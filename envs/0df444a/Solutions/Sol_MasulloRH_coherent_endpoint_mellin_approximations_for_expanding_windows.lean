-- Prove2me | solution 1 for MasulloRH.coherent_endpoint_mellin_approximations_for_expanding_windows
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T04:33:19.465877+00:00
-- url     : https://prove2.me/submissions/2b5ba664-9942-4c58-aa5e-1d56afb233d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_FiniteMellinBands
import Theorems.Thm_MasulloRH_arbitrary_precision_gaussian_approximation_at_each_single_slope
import Theorems.Thm_MasulloRH_window_energy_sandwiched_by_endpoint_mellin_errors
import Theorems.Thm_MasulloRH_fixed_gaussian_energy_lower_at_every_zeta_zero
import Theorems.Thm_MasulloRH_bounded_finite_band_fits_iff_global_window_approximation
import Theorems.Thm_MasulloRH_bounded_total_error_of_simultaneous_finite_band_fits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set MasulloRH MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest
open MasulloRH.RationalThetaGrid MasulloRH.VerticalThetaApproximation MasulloRH.FiniteMellinBands

private lemma edges (k : ℕ) : fullCenter k-fullWidth k=left k ∧ fullCenter k+fullWidth k=upper k := by
  unfold fullCenter fullWidth
  constructor <;> ring

private lemma inside (k : ℕ) : (1/2:ℝ)<left k ∧ left k<upper k ∧ upper k<1 := by
  have hden : (1:ℝ)≤(k:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have h1 := div_le_self (by norm_num : (0:ℝ)≤12287/32768) hden
  have lo : 0<(12287/32768:ℝ)/((k:ℝ)+1) := by positivity
  have hl : left k<right := by unfold left right;linarith
  exact ⟨by unfold left;linarith,hl.trans_le (le_max_left _ _),
    max_lt (by norm_num [right]) (sub_lt_self _ (by positivity))⟩

private theorem cheapAt (c τ : ℝ) (hc : 0<c) (hc' : c<1) (hτ : 0<τ) :
    ∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ), mass c a y < τ := by
  have hp : 0 < 2*Real.pi := by positivity
  obtain ⟨_,m,a,y,δ,hδ,_,_,h⟩ :=
    arbitrary_precision_gaussian_approximation_at_each_single_slope c (τ/(2*Real.pi)) hc hc'
      (div_pos hτ hp)
  have h0 := h c 0 le_rfl (by simpa using hδ.le)
  have h0' := (lt_div_iff₀' hp).mp h0
  refine ⟨m,a,y,?_⟩
  rw [((window_energy_sandwiched_by_endpoint_mellin_errors a y).1 c hc hc').2]
  exact h0'

private theorem feasible (k : ℕ) (τ : ℝ) (hτ : 0<τ) : (feasibleCosts k τ).Nonempty := by
  obtain ⟨l,hl,u⟩ := inside k
  obtain ⟨m,a,y,ha⟩ := cheapAt (left k) τ (by linarith) (by linarith) hτ
  obtain ⟨n,b,z,hb⟩ := cheapAt (upper k) τ (by linarith) u hτ
  let y' := Fin.append y z
  let a' := Fin.append a (fun _ : Fin n => (0,0))
  let b' := Fin.append (fun _ : Fin m => (0,0)) b
  refine ⟨_,m+n,a',b',y',?_,?_,rfl⟩
  · simpa [mass, VerticalThetaApproximation.spectrum,a',y',Fin.sum_univ_add,asComplex] using ha
  · simpa [mass, VerticalThetaApproximation.spectrum,b',y',Fin.sum_univ_add,asComplex] using hb

private theorem otherEndpoint {m : ℕ} (c : ℝ) (hc : 0<c) (hc' : c<1)
    (a b : Fin m → ℚ×ℚ) (y : Fin m → ℚ) :
    mass c a y ≤ 2*mass c b y + 2*coefficientCost c a b y := by
  let D := ∑ i, ‖asComplex (a i)-asComplex (b i)‖ * Real.exp (c*(y i:ℝ))
  let H := fun t => thetaMultiplier (pointAt c t)
  let F := VerticalThetaApproximation.spectrum c a y
  let G := VerticalThetaApproximation.spectrum c b y
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hdif (t : ℝ) : ‖F t - G t‖ ≤ ‖H t‖*D := by
    have e : F t - G t = H t * ∑ i, (asComplex (b i)-asComplex (a i))*
        Complex.exp (pointAt c t*(y i:ℝ)) := by
      simp only [F,G,H,VerticalThetaApproximation.spectrum,sub_mul,Finset.sum_sub_distrib]
      ring
    rw [e,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, norm_sub_rev (asComplex (b i)) (asComplex (a i)), Complex.norm_exp]
    simp [pointAt]
  have hbound (t : ℝ) : ‖F t‖^2 ≤ 2*‖G t‖^2 + (2*D^2)*‖H t‖^2 := by
    have h : ‖F t‖ ≤ ‖G t‖+‖H t‖*D := calc
      ‖F t‖ = ‖(F t-G t)+G t‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (by linarith [hdif t])
    have hs := mul_self_le_mul_self (norm_nonneg _) h
    nlinarith only [hs,sq_nonneg (‖G t‖-‖H t‖*D)]
  have hiF := ((window_energy_sandwiched_by_endpoint_mellin_errors a y).1 c hc hc').1
  have hiG := ((window_energy_sandwiched_by_endpoint_mellin_errors b y).1 c hc hc').1
  have hH := (arbitrary_precision_gaussian_approximation_at_each_single_slope c 1 hc hc' one_pos).1
  have hiH := (memLp_two_iff_integrable_sq_norm hH.1).mp hH
  have r := integral_mono hiF ((hiG.const_mul 2).add (hiH.const_mul (2*D^2))) hbound
  change (∫ t : ℝ, ‖F t‖^2) ≤ ∫ t : ℝ, 2*‖G t‖^2 + (2*D^2)*‖H t‖^2 at r
  rw [integral_add (hiG.const_mul _) (hiH.const_mul _),integral_const_mul,integral_const_mul] at r
  change (∫ t : ℝ, ‖F t‖^2) ≤ 2*(∫ t : ℝ, ‖G t‖^2) + 2*(D^2*(∫ t : ℝ, ‖H t‖^2))
  linarith only [r, mul_assoc 2 (D^2) (∫ t : ℝ, ‖H t‖^2)]

private def physicalTests : Prop :=
  ∀ j : ℕ, 16 ≤ j → ∃ k : ℕ, j+1≤k ∧ ∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ),
    energy (fullCenter k) (fullWidth k) (approximation a y) < 1/((j:ℝ)+1)

private def coefficientTests : Prop :=
  ∀ j : ℕ, 16 ≤ j → ∃ k : ℕ, j+1≤k ∧
    sInf (feasibleCosts k (Real.pi/(4*((j:ℝ)+1)))) < Real.pi/(4*((j:ℝ)+1))

private lemma physicalOfCoefficients : coefficientTests → physicalTests := by
  intro h j hj
  obtain ⟨k,hk,hcost⟩ := h j hj
  let τ := Real.pi/(4*((j:ℝ)+1))
  have hτ : 0<τ := by dsimp [τ]; positivity
  obtain ⟨v,hv,hcheap⟩ := exists_lt_of_csInf_lt (feasible k τ hτ) hcost
  obtain ⟨m,a,b,y,hlo,hhi,rfl⟩ := hv
  have ⟨hl,hm,hu⟩ := inside k
  have hR := otherEndpoint (upper k) (by linarith) hu a b y
  have h := ((window_energy_sandwiched_by_endpoint_mellin_errors a y).2 (fullCenter k) (fullWidth k)
    (by dsimp [fullWidth];linarith) (by rw [(edges k).1];linarith) (by rw [(edges k).2];exact hu)).2.2
  rw [(edges k).1,(edges k).2] at h
  have ht : 8*τ = 2*Real.pi*(1/((j:ℝ)+1)) := by
    dsimp [τ]
    have hd : (j:ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring
  refine ⟨k,hk,m,a,y,?_⟩
  apply (mul_lt_mul_iff_right₀ (by positivity : (0:ℝ)<2*Real.pi)).mp
  rw [← ht]
  change coefficientCost (upper k) a b y < τ at hcheap
  linarith

private theorem ordered_left {j k : ℕ} (h : j≤k) : left k≤left j := by
  unfold left
  apply add_le_add_right
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact_mod_cast Nat.succ_le_succ h


private lemma integrableWindow {m : ℕ} (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ) (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (2*fullCenter k*x+2*fullWidth k*|x|)*‖approximation a y x‖^2) := by
  have ⟨hl,hm,hu⟩ := inside k
  exact ((window_energy_sandwiched_by_endpoint_mellin_errors a y).2 (fullCenter k) (fullWidth k)
    (by dsimp [fullWidth];linarith) (by rw [(edges k).1];linarith) (by rw [(edges k).2];exact hu)).1

private theorem nested {m : ℕ} (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ) {j k : ℕ} (h : j≤k) :
    energy (fullCenter j) (fullWidth j) (approximation a y) ≤ energy (fullCenter k) (fullWidth k) (approximation a y) := by
  apply integral_mono (integrableWindow a y j) (integrableWindow a y k)
  intro x
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    have cmp : upper j≤upper k := by
      apply max_le_max_left
      apply sub_le_sub_left
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ h
    have at_x (i : ℕ) : 2*fullCenter i*x+2*fullWidth i*x=2*(upper i*x) := by
      unfold fullCenter fullWidth
      ring
    rw [at_x,at_x]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cmp hx) (by norm_num)
  · rw [abs_of_nonpos hx]
    have at_x (i : ℕ) : 2*fullCenter i*x+2*fullWidth i*(-x)=2*(left i*x) := by
      unfold fullCenter fullWidth
      ring
    rw [at_x,at_x]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonpos_right (ordered_left h) hx) (by norm_num)

private lemma everyWindowOfCoefficients (h : coefficientTests) (k : ℕ) : FullApprox k := by
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_gt (1/ε)
  let j := max 16 (max k n)
  have hk : k≤j := (le_max_left k n).trans (le_max_right _ _)
  have hn' : (n:ℝ)≤(j:ℝ) := by exact_mod_cast (le_max_right k n).trans (le_max_right 16 (max k n))
  obtain ⟨K,hK,m,a,y,he⟩ := physicalOfCoefficients h j (le_max_left _ _)
  have hbound : 1/((j:ℝ)+1)<ε := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hr := (div_lt_iff₀ hε).mp hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') hε.le]
  exact ⟨m,a,y,(nested a y (hk.trans ((Nat.le_succ j).trans hK))).trans_lt (he.trans hbound)⟩

private theorem mismatchFloor (k : ℕ) {m : ℕ} (a b : Fin m → ℚ×ℚ) (y : Fin m → ℚ)
    (τ : ℝ) (ha : mass (left k) a y < τ) (hb : mass (upper k) b y < τ)
    (s : ℂ) (hs : |s.re-fullCenter k|<fullWidth k) (hz : riemannZeta s=0) :
    2*Real.pi*(Real.exp ((s.re^2-s.im^2)/2)*
      (((fullWidth k)^2-(s.re-fullCenter k)^2)/fullWidth k)) - 3*τ <
        2*coefficientCost (upper k) a b y := by
  obtain ⟨hl,hm,hu⟩ := inside k
  let c := fullCenter k
  let w := fullWidth k
  have hl' : 0<c-w := by rw [(edges k).1];linarith
  have hu' : c+w<1 := (edges k).2.trans_lt hu
  have floor := fixed_gaussian_energy_lower_at_every_zeta_zero c w hl' hu'
    (fun i => asComplex (a i)) (fun i => (y i:ℝ)) s hs hz
  have hwin := ((window_energy_sandwiched_by_endpoint_mellin_errors a y).2 c w
    ((abs_nonneg _).trans hs.le) hl' hu').2.2
  rw [(edges k).1,(edges k).2] at hwin
  have trans := otherEndpoint (upper k) (by linarith) hu a b y
  change _ ≤ energy c w (approximation a y) at floor
  have lhs := (mul_le_mul_of_nonneg_left floor (by positivity : 0≤2*Real.pi)).trans hwin
  dsimp only [c,w] at lhs
  linarith only [ha,hb,trans,lhs]

private theorem boundedCofinalIff : coefficientTests ↔ ∀ k : ℕ, boundedFits (left k) (upper k) := by
  constructor
  · intro h k
    obtain ⟨hl,hm,hu⟩ := inside k
    apply (bounded_finite_band_fits_iff_global_window_approximation (left k) (upper k) (by linarith) hm hu).1.mpr
    intro ε hε
    have hp : 0<4*Real.pi := by positivity
    obtain ⟨m,a,y,he⟩ := everyWindowOfCoefficients h k (ε/(4*Real.pi)) (div_pos hε hp)
    have hw := ((window_energy_sandwiched_by_endpoint_mellin_errors a y).2 (fullCenter k) (fullWidth k)
      (by dsimp [fullWidth];linarith) (by rw [(edges k).1];linarith) (by rw [(edges k).2];exact hu)).2.1
    rw [(edges k).1,(edges k).2,max_le_iff] at hw
    have hsmall := (lt_div_iff₀' hp).mp he
    change 4*Real.pi*energy (fullCenter k) (fullWidth k) (approximation a y)<ε at hsmall
    exact ⟨m,a,y,by unfold total;linarith [hw.1,hw.2]⟩
  · intro h j _
    let k := j+1
    let τ := Real.pi/(4*((j:ℝ)+1))
    have hτ : 0<τ := by dsimp [τ];positivity
    obtain ⟨hl,hm,hu⟩ := inside k
    obtain ⟨m,a,y,small⟩ := (bounded_finite_band_fits_iff_global_window_approximation (left k)
      (upper k) (by linarith) hm hu).1.mp (h k) τ hτ
    have positive (c : ℝ) : 0 ≤ mass c a y := integral_nonneg fun _ => sq_nonneg _
    change mass (left k) a y + mass (upper k) a y<τ at small
    have hz : (0:ℝ) ∈ feasibleCosts k τ := by
      refine ⟨m,a,a,y,by linarith [positive (upper k)],by linarith [positive (left k)],?_⟩
      simp [coefficientCost]
    have lower : BddBelow (feasibleCosts k τ) := by
      refine ⟨0,?_⟩
      rintro _ ⟨n,a,b,y,_,_,rfl⟩
      exact mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    exact ⟨k,le_rfl,(csInf_le lower hz).trans_lt hτ⟩

theorem solution :
    ∀ j : ℕ, 16 ≤ j → ∃ k : ℕ, j+1 ≤ k ∧
      sInf (feasibleCosts k (Real.pi / (4*((j:ℝ)+1)))) < Real.pi / (4*((j:ℝ)+1)) := by
  exact boundedCofinalIff.mpr bounded_total_error_of_simultaneous_finite_band_fits
