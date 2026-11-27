-- Prove2me | solution 2 for MasulloRH.fixed_gaussian_approximation_beyond_first_fifteen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T04:07:04.522612+00:00
-- url     : https://prove2.me/submissions/dc0129e0-e5d7-4d7f-8036-538154627b6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_VerticalThetaApproximation
import Theorems.Thm_MasulloRH_arbitrary_precision_gaussian_approximation_at_each_single_slope
import Theorems.Thm_MasulloRH_window_energy_sandwiched_by_endpoint_mellin_errors
import Theorems.Thm_MasulloRH_coherent_endpoint_mellin_approximations_for_expanding_windows
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set MasulloRH MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest
open MasulloRH.RationalThetaGrid MasulloRH.VerticalThetaApproximation

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

private theorem coherentIff : physicalTests ↔ coefficientTests := by
  constructor
  · intro h j hj
    let n := 8*(j+1)
    have hn : 16≤n := by dsimp [n]; omega
    obtain ⟨k,hk,m,a,y,he⟩ := h n hn
    have ⟨hl,hm,hu⟩ := inside k
    have e := ((window_energy_sandwiched_by_endpoint_mellin_errors a y).2 (fullCenter k) (fullWidth k)
      (by dsimp [fullWidth]; linarith) (by rw [(edges k).1];linarith) (by rw [(edges k).2];exact hu)).2.1
    rw [(edges k).1,(edges k).2] at e
    let τ := Real.pi/(4*((j:ℝ)+1))
    have hτ : 0<τ := by dsimp [τ]; positivity
    have hsmall : 2*Real.pi*(1/((n:ℝ)+1)) < τ := by
      dsimp [n,τ]
      push_cast
      have hd : 0 < 4*((j:ℝ)+1) := by positivity
      have hd' : 0 < 8*((j:ℝ)+1)+1 := by positivity
      rw [mul_one_div,div_lt_div_iff₀ hd' hd]
      nlinarith only [Real.pi_pos]
    have hc := e.trans_lt ((mul_lt_mul_of_pos_left he (by positivity : 0<2*Real.pi)).trans hsmall)
    have hz : (0:ℝ) ∈ feasibleCosts k τ := by
      refine ⟨m,a,a,y,(max_lt_iff.mp hc).1,(max_lt_iff.mp hc).2,?_⟩
      simp [coefficientCost]
    have lower : BddBelow (feasibleCosts k τ) := by
      refine ⟨0,?_⟩
      rintro _ ⟨n,a,b,y,_,_,rfl⟩
      unfold coefficientCost
      exact mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    exact ⟨k,by dsimp [n] at hk; omega,(csInf_le lower hz).trans_lt hτ⟩
  · intro h j hj
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

theorem solution :
    ∀ j : ℕ, 16 ≤ j → ∃ k : ℕ, j+1≤k ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      energy (fullCenter k) (fullWidth k) (residual 0
        (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) < 1/((j:ℝ)+1) := by 
  exact coherentIff.mpr coherent_endpoint_mellin_approximations_for_expanding_windows
