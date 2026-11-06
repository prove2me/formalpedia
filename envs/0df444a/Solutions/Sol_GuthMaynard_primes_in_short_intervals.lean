-- Prove2me | solution 1 for GuthMaynard.primes_in_short_intervals
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:10:15.020251+00:00
-- url     : https://prove2.me/submissions/56c15c6b-7549-4522-8717-965b35d9a597
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_GuthMaynard_norm_sum_vonMangoldt_sub_explicit_formula_le
import Theorems.Thm_GuthMaynard_zeroDensityCount_le_uniform
import Theorems.Thm_GuthMaynard_zeroDensityCount_eq_zero_vinogradov_korobov

open Filter Topology
open scoped ENNReal

namespace GMS1213

noncomputable def Lx (x : ℝ) : ℝ := Real.log x ^ (1 / 4 : ℝ)

/-- ∑_{x ≤ n ≤ x+y} Λ(n) -/
noncomputable def psiWin (x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + y⌋₊, ArithmeticFunction.vonMangoldt n

/-- the set of nontrivial zeros of norm ≤ T -/
def zeroSet (T : ℝ) : Set ℂ := {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T}

/-- ∑_{|ρ| ≤ T} m(ρ) x^{β-1} -/
noncomputable def zeroWeightSum (x T : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zeroSet T, (analyticOrderNatAt riemannZeta ρ : ℝ) * x ^ (ρ.re - 1)

namespace PartAE

theorem term_bound (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) :
    ‖(((x + y : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ≤ y * x ^ (ρ.re - 1) := by
  have hρ : ρ ≠ 0 := by
    intro h; rw [h] at hρ0; simp at hρ0
  set f : ℝ → ℂ := fun t => ((t : ℂ) ^ ρ) / ρ with hf
  have hd : ∀ t ∈ Set.Icc x (x + y), HasDerivWithinAt f ((t : ℂ) ^ (ρ - 1)) (Set.Icc x (x + y)) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
    have h1 : HasDerivAt (fun z : ℂ => z ^ ρ) (ρ * (t : ℂ) ^ (ρ - 1)) (t : ℂ) :=
      (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2 ht0)).hasDerivAt
    have h2 := (h1.comp_ofReal).div_const ρ
    have : ρ * (t : ℂ) ^ (ρ - 1) / ρ = (t : ℂ) ^ (ρ - 1) := by field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
  have hb : ∀ t ∈ Set.Icc x (x + y), ‖(t : ℂ) ^ (ρ - 1)‖ ≤ x ^ (ρ.re - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [Complex.sub_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc x (x + y))
    (Set.left_mem_Icc.2 (by linarith)) (Set.right_mem_Icc.2 (by linarith))
  have e : f (x + y) - f x = (((x + y : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ) := by
    simp only [hf]; push_cast; ring
  rw [e] at this
  have e2 : ‖(x + y) - x‖ = y := by rw [add_sub_cancel_left, Real.norm_of_nonneg hy]
  rw [e2] at this
  linarith

end PartAE

/-- A. Explicit formula, bounded termwise. -/
theorem explicit_bound :
    ∃ C : ℝ, ∀ x T y : ℝ, 2 ≤ T → T ≤ x → 0 ≤ y → y ≤ x → (zeroSet T).Finite →
      |psiWin x y - y| ≤ y * zeroWeightSum x T + C * x * Real.log x ^ 3 / T := by
  obtain ⟨C, hC⟩ := GuthMaynard.norm_sum_vonMangoldt_sub_explicit_formula_le
  refine ⟨C, fun x T y hT hTx hy hyx hfin => ?_⟩
  have hx : 0 < x := by linarith
  have h := hC x T y hT hTx hy hyx
  set S : ℂ := ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T},
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (((x + y : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ) with hS
  have hSb : ‖S‖ ≤ y * zeroWeightSum x T := by
    have hfin' : (zeroSet T).Finite := hfin
    have e : {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ‖ρ‖ ≤ T} = zeroSet T := rfl
    rw [hS, e, finsum_mem_eq_finite_toFinset_sum _ hfin']
    unfold zeroWeightSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin', Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    have hρ' := (Set.Finite.mem_toFinset hfin').1 hρ
    obtain ⟨_, h0, h1, _⟩ := hρ'
    rw [norm_mul]
    have := PartAE.term_bound ρ h0 h1 x y hx hy
    have hm : ‖(analyticOrderNatAt riemannZeta ρ : ℂ)‖ = (analyticOrderNatAt riemannZeta ρ : ℝ) := by
      simp
    rw [hm]
    calc _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (y * x ^ (ρ.re - 1)) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = _ := by ring
  have hcast : ((psiWin x y : ℝ) : ℂ) = ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) := by
    unfold psiWin; push_cast; rfl
  have h2 : |psiWin x y - y| = ‖(((psiWin x y : ℝ) : ℂ) - y)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h2]
  rw [hcast]
  have : ‖(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y‖ ≤
      ‖(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y + S‖ + ‖S‖ := by
    have := norm_sub_le ((∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) - y + S) S
    simpa using this
  linarith

/-- B. The zero set in a bounded region is finite. -/
theorem zeroSet_finite (T : ℝ) : (zeroSet T).Finite := by
  have h := (isCompact_closedBall (0 : ℂ) T).inter_riemannZetaZeros_finite
  refine h.subset ?_
  intro ρ hρ
  exact ⟨by simpa using hρ.2.2.2, hρ.1⟩

namespace PartCD

lemma ord_zeta_eq_ord_completed {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderAt riemannZeta s = analyticOrderAt completedRiemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : s ≠ 1 := fun h => by simp [h] at h1
  have hL : AnalyticAt ℂ completedRiemannZeta s :=
    DifferentiableOn.analyticAt (s := {t : ℂ | t ≠ 0 ∧ t ≠ 1})
      (fun t ht => (differentiableAt_completedZeta ht.1 ht.2).differentiableWithinAt)
      ((isOpen_ne.inter isOpen_ne).mem_nhds ⟨hs0, hs1⟩)
  have hG : AnalyticAt ℂ (fun s => (Complex.Gammaℝ s)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  have heq : riemannZeta =ᶠ[𝓝 s] fun t => completedRiemannZeta t * (Complex.Gammaℝ t)⁻¹ := by
    filter_upwards [isOpen_ne.mem_nhds hs0] with t ht
    rw [riemannZeta_def_of_ne_zero ht, div_eq_mul_inv]
  rw [analyticOrderAt_congr heq]
  have hm := analyticOrderAt_mul hL hG
  simp only [Pi.mul_def] at hm
  rw [hm]
  have : analyticOrderAt (fun s => (Complex.Gammaℝ s)⁻¹) s = 0 := by
    rw [hG.analyticOrderAt_eq_zero]
    exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h0)
  rw [this, add_zero]

lemma ord_zeta_one_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    analyticOrderAt riemannZeta (1 - s) = analyticOrderAt riemannZeta s := by
  have h0' : 0 < (1 - s).re := by simp; linarith
  have h1' : (1 - s).re < 1 := by simp; linarith
  rw [ord_zeta_eq_ord_completed h0' h1', ord_zeta_eq_ord_completed h0 h1]
  have hg : AnalyticAt ℂ (fun t : ℂ => 1 - t) s := by fun_prop
  have hd : deriv (fun t : ℂ => 1 - t) s ≠ 0 := by
    simp
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := completedRiemannZeta) hg hd
  have hc : (completedRiemannZeta ∘ fun t : ℂ => 1 - t) = completedRiemannZeta := by
    funext t; simp [completedRiemannZeta_one_sub]
  rw [hc] at this
  exact this.symm

lemma enat_summable {ι : Type*} (f : ι → ℕ∞) : Summable f :=
  (hasSum_of_isLUB (⨆ s : Finset ι, ∑ i ∈ s, f i) isLUB_iSup).summable

lemma finsum_le_count (σ T : ℝ) (F : Finset ℂ)
    (hF : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) :
    (∑ ρ ∈ F, analyticOrderAt riemannZeta ρ) ≤ LindelofHypothesis.zeroDensityCount σ T := by
  unfold LindelofHypothesis.zeroDensityCount
  set S : Set ℂ := {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T} with hS
  rw [tsum_subtype S (fun s => analyticOrderAt riemannZeta s)]
  calc (∑ ρ ∈ F, analyticOrderAt riemannZeta ρ)
      = ∑ ρ ∈ F, S.indicator (fun s => analyticOrderAt riemannZeta s) ρ := by
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [Set.indicator_of_mem (show ρ ∈ S from hF ρ hρ)]
    _ ≤ _ := (enat_summable _).sum_le_tsum _ (fun _ _ => zero_le)

lemma real_sum_le (σ T B : ℝ) (F : Finset ℂ)
    (hF : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T)
    (hB : (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal B) :
    (∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ max B 0 := by
  have h1 := finsum_le_count σ T F hF
  have h2 : ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℕ∞) ≤
      LindelofHypothesis.zeroDensityCount σ T := by
    refine le_trans ?_ h1
    push_cast
    refine Finset.sum_le_sum fun ρ _ => ?_
    exact ENat.natCast_toNat_le_self _
  have h3 : (((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal B :=
    le_trans (by exact_mod_cast h2) hB
  have h4 : (((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal B := by
    rw [ENat.toENNReal_coe] at h3
    exact h3
  have h5 : (((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ)) ≤ max B 0 := by
    rcases le_or_gt B 0 with hb | hb
    · rw [ENNReal.ofReal_of_nonpos hb] at h4
      have : (∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp h4
      simp [this]
    · rw [← ENNReal.ofReal_natCast] at h4
      exact (ENNReal.ofReal_le_ofReal_iff hb.le).mp h4 |>.trans (le_max_left _ _)
  simpa using h5

/-- the weight of a zero -/
noncomputable def wt (x : ℝ) (ρ : ℂ) : ℝ := (analyticOrderNatAt riemannZeta ρ : ℝ) * x ^ (ρ.re - 1)

lemma wt_nonneg {x : ℝ} (hx : 1 < x) (ρ : ℂ) : 0 ≤ wt x ρ := by
  unfold wt
  have : 0 < x := by linarith
  positivity

lemma analyticAt_zeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := {t : ℂ | t ≠ 1})
    (fun t ht => (differentiableAt_riemannZeta ht).differentiableWithinAt)
    (isOpen_ne.mem_nhds hs)

lemma zero_one_sub {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta (1 - ρ) = 0 := by
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
  have hA : AnalyticAt ℂ riemannZeta ρ := analyticAt_zeta hρ1
  have hA' : AnalyticAt ℂ riemannZeta (1 - ρ) :=
    analyticAt_zeta (fun h => hρ0 (by linear_combination -h))
  have := hA.analyticOrderAt_ne_zero.mpr hz
  rw [← ord_zeta_one_sub h0 h1] at this
  exact hA'.analyticOrderAt_ne_zero.mp this

lemma wt_le_wt_one_sub {x : ℝ} (hx : 1 < x) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1 / 2) :
    wt x ρ ≤ wt x (1 - ρ) := by
  unfold wt analyticOrderNatAt
  rw [ord_zeta_one_sub h0 (by linarith)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.rpow_le_rpow_of_exponent_le hx.le ?_
  simp; linarith

lemma sum_le_two_sum {x T : ℝ} (hx : 1 < x) (S Z : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T)
    (hZ : ∀ ρ, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re < 1 → |ρ.im| ≤ T → ρ ∈ Z) :
    ∑ ρ ∈ S, wt x ρ ≤ 2 * ∑ ρ ∈ Z, wt x ρ := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ => 1 / 2 ≤ ρ.re)]
  have h1 : ∑ ρ ∈ S.filter (fun ρ => 1 / 2 ≤ ρ.re), wt x ρ ≤ ∑ ρ ∈ Z, wt x ρ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ρ _ _ => wt_nonneg hx ρ)
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hz, h0, h1, hT⟩ := hS ρ hρ.1
    exact hZ ρ hz hρ.2 h1 hT
  have h2 : ∑ ρ ∈ S.filter (fun ρ => ¬ 1 / 2 ≤ ρ.re), wt x ρ ≤ ∑ ρ ∈ Z, wt x ρ := by
    calc ∑ ρ ∈ S.filter (fun ρ => ¬ 1 / 2 ≤ ρ.re), wt x ρ
        ≤ ∑ ρ ∈ S.filter (fun ρ => ¬ 1 / 2 ≤ ρ.re), wt x (1 - ρ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [Finset.mem_filter] at hρ
          exact wt_le_wt_one_sub hx (hS ρ hρ.1).2.1 (by have := hρ.2; linarith)
      _ = ∑ ρ ∈ (S.filter (fun ρ => ¬ 1 / 2 ≤ ρ.re)).image (fun ρ => 1 - ρ), wt x ρ := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          simpa using hab
      _ ≤ ∑ ρ ∈ Z, wt x ρ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ρ _ _ => wt_nonneg hx ρ)
          intro ρ hρ
          rw [Finset.mem_image] at hρ
          obtain ⟨σ, hσ, rfl⟩ := hρ
          rw [Finset.mem_filter] at hσ
          obtain ⟨hz, h0, h1, hT⟩ := hS σ hσ.1
          have := hσ.2
          refine hZ _ (zero_one_sub hz h0 h1) (by simp; linarith) (by simp; linarith) ?_
          simpa using hT
  linarith

lemma group_sum {x T M : ℝ} (hx : 1 < x) (hM : 0 ≤ M) (B : ℝ → ℝ)
    (hB : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (B σ))
    (hM' : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1, x ^ (σ - 1) * B σ ≤ M)
    (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) :
    ∑ ρ ∈ Z, wt x ρ ≤ (Real.log x / 2 + 1) * (Real.exp 1 * M) := by
  set ℓ := Real.log x with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  set N := ⌊ℓ / 2⌋₊ + 1 with hN
  let J : ℂ → ℕ := fun ρ => ⌊ℓ * (ρ.re - 1 / 2)⌋₊
  have hJ : ∀ ρ ∈ Z, J ρ ∈ Finset.range N := by
    intro ρ hρ
    obtain ⟨_, h1, h2, _⟩ := hZ ρ hρ
    rw [Finset.mem_range, hN]
    have : ⌊ℓ * (ρ.re - 1 / 2)⌋₊ ≤ ⌊ℓ / 2⌋₊ := Nat.floor_le_floor (by nlinarith)
    show ⌊ℓ * (ρ.re - 1 / 2)⌋₊ < _
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hJ]
  have key : ∀ j ∈ Finset.range N, ∑ ρ ∈ Z with J ρ = j, wt x ρ ≤ Real.exp 1 * M := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjl : (j : ℝ) ≤ ℓ / 2 := by
      have : j ≤ ⌊ℓ / 2⌋₊ := by omega
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by positivity))
    set σ : ℝ := 1 / 2 + j / ℓ with hσ
    have hσ1 : σ ∈ Set.Icc (1 / 2 : ℝ) 1 := by
      constructor
      · have : 0 ≤ (j : ℝ) / ℓ := by positivity
        linarith
      · have : (j : ℝ) / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ0]; linarith
        linarith
    have hfib : ∀ ρ ∈ Z.filter (fun ρ => J ρ = j), σ ≤ ρ.re ∧ ρ.re < σ + 1 / ℓ := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨_, h1, h2, _⟩ := hZ ρ hρ.1
      have hjr : (j : ℝ) = ⌊ℓ * (ρ.re - 1 / 2)⌋₊ := by rw [← hρ.2]
      have a1 : (j : ℝ) ≤ ℓ * (ρ.re - 1 / 2) := by
        rw [hjr]; exact Nat.floor_le (by nlinarith)
      have a2 : ℓ * (ρ.re - 1 / 2) < j + 1 := by
        rw [hjr]; exact Nat.lt_floor_add_one _
      constructor
      · rw [hσ]
        have : (j : ℝ) / ℓ ≤ ρ.re - 1 / 2 := by rw [div_le_iff₀ hℓ0]; linarith
        linarith
      · rw [hσ]
        have : ρ.re - 1 / 2 < ((j : ℝ) + 1) / ℓ := by rw [lt_div_iff₀ hℓ0]; linarith
        have e : ((j : ℝ) + 1) / ℓ = j / ℓ + 1 / ℓ := by ring
        linarith
    have hcount := real_sum_le σ T (B σ) (Z.filter (fun ρ => J ρ = j))
      (fun ρ hρ => by
        have := hfib ρ hρ
        obtain ⟨hz, _, _, hT⟩ := hZ ρ (Finset.mem_filter.mp hρ).1
        exact ⟨hz, this.1, hT⟩) (hB σ hσ1)
    have hMσ : x ^ (σ - 1) * max (B σ) 0 ≤ M := by
      rcases le_total 0 (B σ) with hb | hb
      · rw [max_eq_left hb]; exact hM' σ hσ1
      · rw [max_eq_right hb]; simpa using hM
    calc ∑ ρ ∈ Z with J ρ = j, wt x ρ
        ≤ ∑ ρ ∈ Z with J ρ = j, Real.exp 1 * x ^ (σ - 1) *
            (analyticOrderNatAt riemannZeta ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          obtain ⟨a1, a2⟩ := hfib ρ hρ
          unfold wt
          have hpow : x ^ (ρ.re - 1) ≤ Real.exp 1 * x ^ (σ - 1) := by
            rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx0, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have : ℓ * (ρ.re - σ) ≤ 1 := by
              have := (mul_lt_mul_of_pos_left a2 hℓ0)
              have e : ℓ * (σ + 1 / ℓ) = ℓ * σ + 1 := by field_simp
              nlinarith
            nlinarith
          have hm : (0:ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by positivity
          nlinarith
      _ = Real.exp 1 * x ^ (σ - 1) * ∑ ρ ∈ Z with J ρ = j, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ Real.exp 1 * x ^ (σ - 1) * max (B σ) 0 := by
          refine mul_le_mul_of_nonneg_left hcount (by positivity)
      _ ≤ Real.exp 1 * M := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hMσ (Real.exp_pos 1).le
  calc ∑ j ∈ Finset.range N, ∑ ρ ∈ Z with J ρ = j, wt x ρ
      ≤ ∑ j ∈ Finset.range N, Real.exp 1 * M := Finset.sum_le_sum key
    _ = N * (Real.exp 1 * M) := by simp
    _ ≤ (ℓ / 2 + 1) * (Real.exp 1 * M) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hN]; push_cast
        linarith [Nat.floor_le (show 0 ≤ ℓ / 2 by positivity)]

end PartCD

/-- C. Grouping zeros by real part, with the functional-equation symmetry for β < 1/2. -/
theorem zeroWeightSum_le_of_count_bound (x T M : ℝ) (hx : 1 < x) (hT : 2 ≤ T) (hM : 0 ≤ M)
    (B : ℝ → ℝ)
    (hB : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (B σ))
    (hM' : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1, x ^ (σ - 1) * B σ ≤ M) :
    zeroWeightSum x T ≤ 2 * Real.exp 1 * (Real.log x + 2) * M := by
  have hfin := zeroSet_finite T
  have hZfin : {ρ : ℂ | riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.Finite := by
    refine (zeroSet_finite (T + 1)).subset fun ρ hρ => ?_
    obtain ⟨hz, h1, h2, h3⟩ := hρ
    refine ⟨hz, by linarith, h2, ?_⟩
    calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ T + 1 := by rw [abs_of_pos (by linarith : 0 < ρ.re)]; linarith
  have h1 : zeroWeightSum x T = ∑ ρ ∈ hfin.toFinset, PartCD.wt x ρ := by
    unfold zeroWeightSum PartCD.wt
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  have h2 := PartCD.sum_le_two_sum (T := T) hx hfin.toFinset hZfin.toFinset
    (fun ρ hρ => by
      obtain ⟨a, b, c, d⟩ := hfin.mem_toFinset.mp hρ
      refine ⟨a, b, c, ?_⟩
      exact (Complex.abs_im_le_norm ρ).trans d)
    (fun ρ a b c d => hZfin.mem_toFinset.mpr ⟨a, b, c, d⟩)
  have h3 := PartCD.group_sum hx hM B hB hM' hZfin.toFinset
    (fun ρ hρ => hZfin.mem_toFinset.mp hρ)
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [h1]
  have he := Real.exp_pos 1
  nlinarith [mul_nonneg he.le hM, mul_nonneg (mul_nonneg he.le hM) hl.le]

namespace PartCD

/-- the bound M₀ -/
noncomputable def M0 (C A c ε ℓ : ℝ) : ℝ :=
  |C| * ℓ ^ |A| * Real.exp (-(ε / 2) * (ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ))))

lemma D1 (C A : ℝ) (e : ℝ → ℝ)
    (hunif : ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ ((30 / 13 + e T) * (1 - σ)) * Real.log T ^ A))
    (c : ℝ) (hc : 0 < c) (T₀ : ℝ)
    (hVK : ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
      1 - c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) ≤ σ →
      LindelofHypothesis.zeroDensityCount σ T = 0)
    (ε : ℝ) (hε : 0 < ε) (x T : ℝ) (hx : 1 < x) (hT3 : 3 ≤ T) (hT0 : T₀ ≤ T) (hTx : T ≤ x)
    (hr : T ^ (30 / 13 + e T) ≤ x ^ (1 - ε / 2)) :
    zeroWeightSum x T ≤ 2 * Real.exp 1 * (Real.log x + 2) * M0 C A c ε (Real.log x) := by
  set ℓ := Real.log x with hℓ
  have hx0 : 0 < x := by linarith
  have hT0' : 0 < T := by linarith
  have hlT : 1 < Real.log T := by
    rw [Real.lt_log_iff_exp_lt hT0']
    have := Real.exp_one_lt_d9
    linarith
  have hlTℓ : Real.log T ≤ ℓ := Real.log_le_log hT0' hTx
  have hℓ1 : 1 < ℓ := lt_of_lt_of_le hlT hlTℓ
  have hllT : 0 < Real.log (Real.log T) := Real.log_pos hlT
  have hllTℓ : Real.log (Real.log T) ≤ Real.log ℓ := Real.log_le_log (by linarith) hlTℓ
  have hM0 : 0 ≤ M0 C A c ε ℓ := by unfold M0; positivity
  set σT := 1 - c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) with hσT
  refine zeroWeightSum_le_of_count_bound x T _ hx (by linarith) hM0
    (fun σ => if σ ≤ σT then C * T ^ ((30 / 13 + e T) * (1 - σ)) * Real.log T ^ A else 0) ?_ ?_
  · intro σ hσ
    by_cases h : σ ≤ σT
    · simp only [if_pos h]; exact hunif T (by linarith) σ hσ
    · simp only [if_neg h]
      have := hVK T hT0 σ (by rw [← hσT]; exact (not_le.mp h).le)
      rw [this]; simp
  · intro σ hσ
    by_cases h : σ ≤ σT
    · simp only [if_pos h]
      set a := 30 / 13 + e T with ha
      set δ := c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) with hδ
      have hu : δ ≤ 1 - σ := by rw [hσT] at h; linarith
      have hδpos : 0 ≤ δ := by
        rw [hδ]
        exact mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg (by linarith) _))
          (Real.rpow_nonneg hllT.le _)
      have hP : 0 < T ^ a := Real.rpow_pos_of_pos hT0' a
      -- r = T^a / x
      set r := T ^ a / x with hr_def
      have hrpos : 0 < r := by positivity
      have hrle : r ≤ x ^ (-(ε / 2)) := by
        rw [hr_def, div_le_iff₀ hx0]
        calc T ^ a ≤ x ^ (1 - ε / 2) := hr
          _ = x ^ (-(ε / 2)) * x := by
            rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one, mul_comm]
      have hxle : x ^ (-(ε / 2)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx.le (by linarith)
      have hrle1 : r ≤ 1 := hrle.trans hxle
      have hkey : x ^ (σ - 1) * T ^ (a * (1 - σ)) = r ^ (1 - σ) := by
        rw [hr_def, Real.div_rpow hP.le hx0.le, ← Real.rpow_mul hT0'.le,
          show σ - 1 = -(1 - σ) by ring, Real.rpow_neg hx0.le, div_eq_mul_inv, mul_comm]
      have hrδ : r ^ (1 - σ) ≤ Real.exp (-(ε / 2) * (ℓ * δ)) := by
        calc r ^ (1 - σ) ≤ r ^ δ := Real.rpow_le_rpow_of_exponent_ge hrpos hrle1 hu
          _ ≤ (x ^ (-(ε / 2))) ^ δ := Real.rpow_le_rpow hrpos.le hrle hδpos
          _ = Real.exp (-(ε / 2) * (ℓ * δ)) := by
            rw [← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0]
            congr 1; ring
      have hδ0 : c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ) ≤ δ := by
        rw [hδ]
        have h1 : ℓ ^ (-(2 / 3) : ℝ) ≤ Real.log T ^ (-(2 / 3) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hlTℓ (by norm_num)
        have h2 : Real.log ℓ ^ (-(1 / 3) : ℝ) ≤ Real.log (Real.log T) ^ (-(1 / 3) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hllT hllTℓ (by norm_num)
        have h1' : 0 ≤ ℓ ^ (-(2 / 3) : ℝ) := by positivity
        have h2' : 0 ≤ Real.log ℓ ^ (-(1 / 3) : ℝ) := Real.rpow_nonneg (Real.log_nonneg hℓ1.le) _
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc.le) h2 h2'
          (mul_nonneg hc.le (Real.rpow_nonneg (by linarith) _))
      have hexp : Real.exp (-(ε / 2) * (ℓ * δ)) ≤
          Real.exp (-(ε / 2) * (ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ)))) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ (ε / 2) * ℓ := by positivity
        nlinarith
      have hlogA : Real.log T ^ A ≤ ℓ ^ |A| :=
        calc Real.log T ^ A ≤ Real.log T ^ |A| :=
              Real.rpow_le_rpow_of_exponent_le hlT.le (le_abs_self A)
          _ ≤ ℓ ^ |A| := Real.rpow_le_rpow (by linarith) hlTℓ (abs_nonneg A)
      have hQ : 0 < Real.log T ^ A := Real.rpow_pos_of_pos (by linarith) A
      have hxs : 0 < x ^ (σ - 1) := Real.rpow_pos_of_pos hx0 _
      have hPσ : 0 < T ^ (a * (1 - σ)) := Real.rpow_pos_of_pos hT0' _
      calc x ^ (σ - 1) * (C * T ^ (a * (1 - σ)) * Real.log T ^ A)
          ≤ x ^ (σ - 1) * (|C| * T ^ (a * (1 - σ)) * Real.log T ^ A) := by
            refine mul_le_mul_of_nonneg_left ?_ hxs.le
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hPσ.le) hQ.le
        _ = |C| * Real.log T ^ A * (x ^ (σ - 1) * T ^ (a * (1 - σ))) := by ring
        _ = |C| * Real.log T ^ A * r ^ (1 - σ) := by rw [hkey]
        _ ≤ |C| * ℓ ^ |A| * Real.exp (-(ε / 2) * (ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) *
              Real.log ℓ ^ (-(1 / 3) : ℝ)))) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hlogA (abs_nonneg C)) (hrδ.trans hexp)
              (by positivity) (by positivity)
        _ = M0 C A c ε ℓ := rfl
    · simp only [if_neg h]; simpa using hM0

end PartCD

namespace PartCD

lemma D2 (C A c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ ℓ : ℝ in atTop, 2 * Real.exp 1 * (ℓ + 2) *
      (|C| * ℓ ^ |A| * Real.exp (-(ε / 2) * (ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ)))))
      ≤ Real.exp (-2 * ℓ ^ (1 / 4 : ℝ)) := by
  set κ := ε * c / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  -- (log ℓ)^(1/3) ≤ (κ/3) ℓ^(1/12)
  have h1 : (fun ℓ : ℝ => Real.log ℓ ^ (1 / 3 : ℝ)) =o[atTop] (fun ℓ : ℝ => ℓ ^ (1 / 12 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (1 / 3) (by norm_num)
  have h1' := h1.def (show 0 < κ / 3 by positivity)
  have h2 : (fun w : ℝ => w ^ (4 * (|A| + 1))) =o[atTop] Real.exp := by simpa using isLittleO_rpow_exp_pos_mul_atTop (4 * (|A| + 1)) (b := 1) one_pos
  have h2' := h2.def (show 0 < 1 / (6 * Real.exp 1 * (|C| + 1)) by positivity)
  have h2'' : ∀ᶠ ℓ : ℝ in atTop, ‖(ℓ ^ (1 / 4 : ℝ)) ^ (4 * (|A| + 1))‖ ≤
      1 / (6 * Real.exp 1 * (|C| + 1)) * ‖Real.exp (ℓ ^ (1 / 4 : ℝ))‖ :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 4)).eventually h2'
  filter_upwards [h1', h2'', eventually_gt_atTop (1 : ℝ)] with ℓ ha hb hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hlog : 0 < Real.log ℓ := Real.log_pos hℓ
  set w := ℓ ^ (1 / 4 : ℝ) with hw
  have hw0 : 0 < w := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog.le _), Real.norm_of_nonneg (Real.rpow_nonneg hℓ0.le _)] at ha
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hw0.le _), Real.norm_of_nonneg (Real.exp_pos _).le] at hb
  -- exponent bound: κ ℓ^(1/3) (log ℓ)^(-1/3) ≥ 3 w
  have hℓ13 : ℓ ^ (1 / 3 : ℝ) = w * ℓ ^ (1 / 12 : ℝ) := by
    rw [hw, ← Real.rpow_add hℓ0]; norm_num
  have hexp_eq : ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ)) =
      c * ℓ ^ (1 / 3 : ℝ) / Real.log ℓ ^ (1 / 3 : ℝ) := by
    rw [Real.rpow_neg hℓ0.le, Real.rpow_neg hlog.le]
    have this : ℓ = ℓ ^ (1 / 3 : ℝ) * ℓ ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hℓ0]; norm_num
    have hp : 0 < ℓ ^ (2 / 3 : ℝ) := by positivity
    have h13 : ℓ * (ℓ ^ (2 / 3 : ℝ))⁻¹ = ℓ ^ (1 / 3 : ℝ) := by
      rw [mul_inv_eq_iff_eq_mul₀ hp.ne']; exact this
    calc ℓ * (c * (ℓ ^ (2 / 3 : ℝ))⁻¹ * (Real.log ℓ ^ (1 / 3 : ℝ))⁻¹)
        = c * (ℓ * (ℓ ^ (2 / 3 : ℝ))⁻¹) / Real.log ℓ ^ (1 / 3 : ℝ) := by ring
      _ = _ := by rw [h13]
  have hq : 0 < Real.log ℓ ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hbig : 3 * w ≤ κ * (ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ))) / c := by
    rw [hexp_eq, hℓ13]
    -- κ * (c * (w * s) / q) / c = κ w s / q ≥ 3 w  where q ≤ (κ/3) s
    have : Real.log ℓ ^ (1 / 3 : ℝ) ≤ κ / 3 * ℓ ^ (1 / 12 : ℝ) := ha
    rw [show κ * (c * (w * ℓ ^ (1 / 12 : ℝ)) / Real.log ℓ ^ (1 / 3 : ℝ)) / c =
        κ * (w * ℓ ^ (1 / 12 : ℝ)) / Real.log ℓ ^ (1 / 3 : ℝ) by field_simp]
    rw [le_div_iff₀ hq]
    nlinarith [mul_pos hw0 (show 0 < κ / 3 by positivity)]
  have hX : 3 * w ≤ ε / 2 * (ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ))) := by
    have : κ * (ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ))) / c =
        ε / 2 * (ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ))) := by
      rw [hκ]; field_simp
    linarith
  have hℓw : ℓ = w ^ 4 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]; norm_num
  have hpow : ℓ ^ |A| * ℓ = w ^ (4 * (|A| + 1)) := by
    rw [hw, ← Real.rpow_mul hℓ0.le, show (1 / 4 : ℝ) * (4 * (|A| + 1)) = |A| + 1 by ring,
      Real.rpow_add hℓ0, Real.rpow_one]
  have hexp1 : Real.exp (-(ε / 2) * (ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ)))) ≤
      Real.exp (-(3 * w)) := Real.exp_le_exp.mpr (by linarith)
  have he := Real.exp_pos 1
  have hC1 : 0 < |C| + 1 := by positivity
  have hℓ2 : ℓ + 2 ≤ 3 * ℓ := by linarith
  have hexw : Real.exp (-2 * w) = Real.exp w * Real.exp (-(3 * w)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexpos := Real.exp_pos (-(3 * w))
  calc 2 * Real.exp 1 * (ℓ + 2) * (|C| * ℓ ^ |A| * Real.exp (-(ε / 2) * (ℓ * (c * ℓ ^ (-(2 / 3) : ℝ) * Real.log ℓ ^ (-(1 / 3) : ℝ)))))
      ≤ 2 * Real.exp 1 * (3 * ℓ) * (|C| * ℓ ^ |A| * Real.exp (-(3 * w))) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hℓ2 (by positivity)
        · exact mul_le_mul_of_nonneg_left hexp1 (by positivity)
        · positivity
        · positivity
    _ = 6 * Real.exp 1 * |C| * (ℓ ^ |A| * ℓ) * Real.exp (-(3 * w)) := by ring
    _ = 6 * Real.exp 1 * |C| * w ^ (4 * (|A| + 1)) * Real.exp (-(3 * w)) := by rw [hpow]
    _ ≤ 6 * Real.exp 1 * |C| * (1 / (6 * Real.exp 1 * (|C| + 1)) * Real.exp w) * Real.exp (-(3 * w)) := by
        gcongr
    _ ≤ Real.exp w * Real.exp (-(3 * w)) := by
        have : 6 * Real.exp 1 * |C| * (1 / (6 * Real.exp 1 * (|C| + 1))) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]
          nlinarith [mul_pos (show (0:ℝ) < 6 by norm_num) he]
        calc 6 * Real.exp 1 * |C| * (1 / (6 * Real.exp 1 * (|C| + 1)) * Real.exp w) * Real.exp (-(3 * w))
            = (6 * Real.exp 1 * |C| * (1 / (6 * Real.exp 1 * (|C| + 1)))) * Real.exp w * Real.exp (-(3 * w)) := by ring
          _ ≤ 1 * Real.exp w * Real.exp (-(3 * w)) := by gcongr
          _ = _ := by ring
    _ = Real.exp (-2 * w) := hexw.symm

lemma D3 (e : ℝ → ℝ) (T₀ T₁ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (he : ∀ T : ℝ, T₁ ≤ T → |e T| ≤ ε / 2)
    (x : ℝ) (h1 : 1 < x) (h2 : max 3 (max T₀ T₁) ≤ x ^ (1 / 100 : ℝ))
    (h3 : Real.exp (6 * Lx x) ≤ x ^ (ε / 2))
    (y : ℝ) (hy : y ∈ Set.Icc (x ^ (17 / 30 + ε)) (x ^ (0.99 : ℝ))) :
    3 ≤ x / y * Real.exp (2 * Lx x) ∧ T₀ ≤ x / y * Real.exp (2 * Lx x) ∧
    x / y * Real.exp (2 * Lx x) ≤ x ∧
    (x / y * Real.exp (2 * Lx x)) ^ (30 / 13 + e (x / y * Real.exp (2 * Lx x))) ≤
      x ^ (1 - ε / 2) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Lx x := Real.rpow_nonneg (Real.log_nonneg h1.le) _
  set E := Real.exp (2 * Lx x) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by linarith)
  have hypos : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hy.1
  have hlow : x ^ (1 / 100 : ℝ) ≤ x / y := by
    calc x ^ (1 / 100 : ℝ) = x / x ^ (99 / 100 : ℝ) := by
          have := Real.rpow_sub hx0 1 (99 / 100 : ℝ)
          rw [Real.rpow_one] at this
          rw [← this]; norm_num
      _ ≤ x / y := by
          apply div_le_div_of_nonneg_left hx0.le hypos
          have := hy.2
          norm_num at this
          exact this
  have hup : x / y ≤ x ^ (13 / 30 - ε) := by
    calc x / y ≤ x / x ^ (17 / 30 + ε) :=
          div_le_div_of_nonneg_left hx0.le (Real.rpow_pos_of_pos hx0 _) hy.1
      _ = x ^ (13 / 30 - ε) := by
          have := Real.rpow_sub hx0 1 (17 / 30 + ε)
          rw [Real.rpow_one] at this
          rw [← this]; congr 1; ring
  have hTlow : x ^ (1 / 100 : ℝ) ≤ x / y * E := by nlinarith [div_pos hx0 hypos]
  have hTup : x / y * E ≤ x ^ (13 / 30 - ε) * E :=
    mul_le_mul_of_nonneg_right hup (by linarith)
  have hE3 : E ≤ x ^ (ε / 2) := by
    refine le_trans ?_ h3
    rw [hE]; exact Real.exp_le_exp.mpr (by linarith)
  have hT3 : 3 ≤ x / y * E := le_trans (le_trans (le_max_left _ _) h2) hTlow
  have hT0 : T₀ ≤ x / y * E :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h2) hTlow
  have hT1 : T₁ ≤ x / y * E :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h2) hTlow
  refine ⟨hT3, hT0, ?_, ?_⟩
  · calc x / y * E ≤ x ^ (13 / 30 - ε) * x ^ (ε / 2) := hTup.trans
          (mul_le_mul_of_nonneg_left hE3 (Real.rpow_nonneg hx0.le _))
      _ = x ^ (13 / 30 - ε / 2) := by rw [← Real.rpow_add hx0]; congr 1; ring
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
      _ = x := Real.rpow_one x
  · set T := x / y * E with hT
    have hT1' : 1 ≤ T := by linarith
    have hT0' : 0 < T := by linarith
    have hea := he T hT1
    have ha : 30 / 13 + e T ≤ 30 / 13 + ε / 2 := by have := (abs_le.mp hea).2; linarith
    have hb3 : 30 / 13 + ε / 2 ≤ 3 := by linarith
    calc T ^ (30 / 13 + e T) ≤ T ^ (30 / 13 + ε / 2) :=
          Real.rpow_le_rpow_of_exponent_le hT1' ha
      _ ≤ (x ^ (13 / 30 - ε) * E) ^ (30 / 13 + ε / 2) :=
          Real.rpow_le_rpow hT0'.le hTup (by linarith)
      _ = (x ^ (13 / 30 - ε)) ^ (30 / 13 + ε / 2) * E ^ (30 / 13 + ε / 2) :=
          Real.mul_rpow (Real.rpow_nonneg hx0.le _) (by linarith)
      _ ≤ x ^ (1 - ε) * x ^ (ε / 2) := by
          apply mul_le_mul
          · rw [← Real.rpow_mul hx0.le]
            apply Real.rpow_le_rpow_of_exponent_le h1.le
            nlinarith
          · calc E ^ (30 / 13 + ε / 2) ≤ E ^ (3 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hE1 hb3
              _ = Real.exp (6 * Lx x) := by
                  rw [hE, ← Real.exp_mul]; congr 1; ring
              _ ≤ x ^ (ε / 2) := h3
          · positivity
          · positivity
      _ = x ^ (1 - ε / 2) := by rw [← Real.rpow_add hx0]; congr 1; ring

end PartCD

/-- D. The count/zero-free-region bookkeeping, for the T of the proof. -/
theorem zeroWeightSum_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      y ∈ Set.Icc (x ^ (17 / 30 + ε)) (x ^ (0.99 : ℝ)) →
      zeroWeightSum x (x / y * Real.exp (2 * Lx x)) ≤ C * Real.exp (-2 * Lx x) := by
  obtain ⟨C0, A, e, he, hunif⟩ := GuthMaynard.zeroDensityCount_le_uniform
  obtain ⟨c, hc, T₀, hVK⟩ := GuthMaynard.zeroDensityCount_eq_zero_vinogradov_korobov
  -- T₁ with |e T| ≤ ε/2 for T ≥ T₁
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    ((he.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / 2 by positivity))).mono
      fun T hT => (le_of_lt (by simpa [Real.dist_eq] using hT)))
  have hev1 : ∀ᶠ x : ℝ in atTop, 1 < x := eventually_gt_atTop 1
  have hev2 : ∀ᶠ x : ℝ in atTop, max 3 (max T₀ T₁) ≤ x ^ (1 / 100 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 100)).eventually_ge_atTop _
  have hev3 : ∀ᶠ x : ℝ in atTop, Real.exp (6 * Lx x) ≤ x ^ (ε / 2) := by
    have h34 : ∀ᶠ ℓ : ℝ in atTop, 12 / ε ≤ ℓ ^ (3 / 4 : ℝ) :=
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3 / 4)).eventually_ge_atTop _
    have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    filter_upwards [hlog.eventually h34, hlog.eventually_gt_atTop 1, eventually_gt_atTop (0:ℝ)]
      with x hx hℓ hx0
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    unfold Lx
    set ℓ := Real.log x
    have hℓ0 : 0 < ℓ := by linarith
    have : ℓ ^ (1 / 4 : ℝ) * ℓ ^ (3 / 4 : ℝ) = ℓ := by
      rw [← Real.rpow_add hℓ0]; norm_num
    have hp : 0 < ℓ ^ (1 / 4 : ℝ) := by positivity
    have hε' : 12 / ε ≤ ℓ ^ (3 / 4 : ℝ) := hx
    rw [div_le_iff₀ hε] at hε'
    nlinarith
  have hev4 := (PartCD.D2 C0 A c ε hc hε)
  have hev5 : ∀ᶠ x : ℝ in atTop, 2 * Real.exp 1 * (Real.log x + 2) *
      PartCD.M0 C0 A c ε (Real.log x) ≤ Real.exp (-2 * Lx x) := by
    filter_upwards [Real.tendsto_log_atTop.eventually hev4] with x hx
    unfold PartCD.M0
    exact hx
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hev1.and (hev2.and (hev3.and hev5)))
  refine ⟨1, x₀, fun x hx y hy => ?_⟩
  obtain ⟨hx1, hx2, hx3, hx5⟩ := hx₀ x hx
  obtain ⟨d1, d2, d3, d4⟩ := PartCD.D3 e T₀ T₁ ε hε hε1 (fun T hT => hT₁ T hT) x hx1 hx2 hx3 y hy
  have := PartCD.D1 C0 A e hunif c hc T₀ hVK ε hε x _ hx1 d1 d2 d3 d4
  rw [one_mul]
  exact this.trans hx5


/-- E. The von Mangoldt version of Corollary 1.3. -/
theorem psi_short_interval (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      y ∈ Set.Icc (x ^ (17 / 30 + ε)) (x ^ (0.99 : ℝ)) →
      |psiWin x y - y| ≤ C * y * Real.exp (-Lx x) := by
  obtain ⟨C₁, h₁⟩ := explicit_bound
  obtain ⟨C₂, x₂, h₂⟩ := zeroWeightSum_le ε hε hε1
  refine ⟨|C₂| + |C₁| * (Nat.factorial 12 : ℝ), max x₂ (Real.exp 100), fun x hx y hy => ?_⟩
  have hx2 : x₂ ≤ x := (le_max_left _ _).trans hx
  have hx100 : Real.exp 100 ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx100
  have hlog100 : 100 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx100
    rwa [Real.log_exp] at this
  set L := Lx x with hLdef
  have hL0 : 0 ≤ L := Real.rpow_nonneg (by linarith) _
  have hL4 : L ^ 4 = Real.log x := by
    have : (Real.log x ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = Real.log x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    exact this
  have hL2 : 2 ≤ L := by
    by_contra h
    push Not at h
    have : L ^ 4 < 2 ^ 4 := pow_lt_pow_left₀ h hL0 (by norm_num)
    linarith
  have hL3 : 8 ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hL2 3
    linarith
  -- bounds on y
  have hy_lo : Real.exp (2 * L) ≤ y := by
    have h1 : x ^ (17 / 30 : ℝ) ≤ x ^ (17 / 30 + ε) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.add_one_le_exp (100:ℝ), hx100]) (by linarith)
    have h2 : Real.exp (2 * L) ≤ x ^ (17 / 30 : ℝ) := by
      rw [Real.rpow_def_of_pos hxpos, mul_comm]
      apply Real.exp_le_exp.2
      have : L ^ 4 = L * L ^ 3 := by ring
      nlinarith
    exact h2.trans (h1.trans hy.1)
  have hypos : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy_lo
  have hy_hi : 2 * y ≤ x := by
    have h3 : y ≤ Real.exp (0.99 * Real.log x) := by
      have := hy.2
      rwa [Real.rpow_def_of_pos hxpos, mul_comm] at this
    have h4 : (2:ℝ) ≤ Real.exp (0.01 * Real.log x) := by
      have : (1:ℝ) ≤ 0.01 * Real.log x := by linarith
      have := Real.add_one_le_exp (0.01 * Real.log x)
      linarith
    have h5 : x = Real.exp (0.99 * Real.log x) * Real.exp (0.01 * Real.log x) := by
      rw [← Real.exp_add, show (0.99:ℝ) * Real.log x + 0.01 * Real.log x = Real.log x by ring, Real.exp_log hxpos]
    have h6 := Real.exp_pos (0.99 * Real.log x)
    nlinarith
  set E := Real.exp (2 * L) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (by linarith)
  set T := x / y * E with hT
  have hT2 : 2 ≤ T := by
    have : 2 ≤ x / y := by rw [le_div_iff₀ hypos]; linarith
    nlinarith
  have hTx : T ≤ x := by
    rw [hT, div_mul_eq_mul_div, div_le_iff₀ hypos]
    nlinarith
  have hyx : y ≤ x := by linarith
  have hfin := zeroSet_finite T
  have hA := h₁ x T y hT2 hTx hypos.le hyx hfin
  have hB := h₂ x hx2 y hy
  have hB' : y * zeroWeightSum x T ≤ y * (C₂ * Real.exp (-2 * L)) :=
    mul_le_mul_of_nonneg_left hB hypos.le
  have hxT : C₁ * x * Real.log x ^ 3 / T = C₁ * y * L ^ 12 * Real.exp (-2 * L) := by
    have : Real.exp (-2 * L) = (Real.exp (2 * L))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [this, ← hE, hT, ← hL4]
    field_simp
  rw [hxT] at hA
  -- final estimate
  set a := Real.exp (-L) with ha
  have hapos : 0 < a := Real.exp_pos _
  have hea : Real.exp L * a = 1 := by rw [ha, ← Real.exp_add]; simp
  have he2 : Real.exp (-2 * L) = a * a := by rw [ha, ← Real.exp_add]; ring_nf
  have hfac : (L ^ 12 / (Nat.factorial 12 : ℝ)) ≤ Real.exp L := Real.pow_div_factorial_le_exp L hL0 12
  have hfpos : (0:ℝ) < Nat.factorial 12 := by positivity
  have hL12 : L ^ 12 ≤ (Nat.factorial 12 : ℝ) * Real.exp L := by
    rw [div_le_iff₀ hfpos] at hfac; linarith
  have hL12a : L ^ 12 * (a * a) ≤ (Nat.factorial 12 : ℝ) * a := by
    have h1 : L ^ 12 * (a * a) ≤ ((Nat.factorial 12 : ℝ) * Real.exp L) * (a * a) :=
      mul_le_mul_of_nonneg_right hL12 (by positivity)
    have h2 : ((Nat.factorial 12 : ℝ) * Real.exp L) * (a * a) = (Nat.factorial 12 : ℝ) * a := by
      calc _ = (Nat.factorial 12 : ℝ) * (Real.exp L * a) * a := by ring
        _ = _ := by rw [hea]; ring
    linarith
  have ha1 : a ≤ 1 := by rw [ha]; exact Real.exp_le_one_iff.2 (by linarith)
  have haa : a * a ≤ a := by nlinarith
  rw [he2] at hB' hA
  have hC2 : C₂ * (a * a) ≤ |C₂| * a := by
    calc C₂ * (a * a) ≤ |C₂| * (a * a) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C₂| * a := mul_le_mul_of_nonneg_left haa (abs_nonneg _)
  have hC1 : C₁ * L ^ 12 * (a * a) ≤ |C₁| * (Nat.factorial 12 : ℝ) * a := by
    calc C₁ * L ^ 12 * (a * a) ≤ |C₁| * (L ^ 12 * (a * a)) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C₁| * ((Nat.factorial 12 : ℝ) * a) := mul_le_mul_of_nonneg_left hL12a (abs_nonneg _)
      _ = _ := by ring
  calc |psiWin x y - y| ≤ y * (C₂ * (a * a)) + C₁ * y * L ^ 12 * (a * a) := hA.trans (by linarith)
    _ = y * (C₂ * (a * a) + C₁ * L ^ 12 * (a * a)) := by ring
    _ ≤ y * ((|C₂| + |C₁| * (Nat.factorial 12 : ℝ)) * a) :=
        mul_le_mul_of_nonneg_left (by linarith) hypos.le
    _ = _ := by ring


namespace PartF

lemma pi_sub (a b : ℕ) (h : a ≤ b) :
    ((Nat.primeCounting b : ℝ) - Nat.primeCounting a) =
      (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) := by
  have key : (Finset.range (b + 1)).filter Nat.Prime =
      (Finset.range (a + 1)).filter Nat.Prime ∪ (Finset.Ioc a b).filter Nat.Prime := by
    ext n; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hn : n < a + 1
      · exact Or.inl ⟨hn, h2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, h3⟩
  have hd : Disjoint ((Finset.range (a + 1)).filter Nat.Prime) ((Finset.Ioc a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at h1 h2
    omega
  have : Nat.primeCounting b = Nat.primeCounting a + ((Finset.Ioc a b).filter Nat.Prime).card := by
    simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rw [key, Finset.card_union_of_disjoint hd]
  rw [this]; push_cast; ring


lemma psi_window (x y : ℝ) (hx : 1 ≤ x) (hy : 0 ≤ y) :
    ∃ S T : ℝ, T ≤ S ∧ S ≤ psiWin x y ∧ psiWin x y ≤ S + Real.log x ∧
      S - T ≤ 2 * Real.sqrt (x + y) * Real.log (x + y) ∧
      T = ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime, Real.log n := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hxy : 1 ≤ x + y := by linarith
  set a := ⌊x⌋₊ with ha
  set b := ⌊x + y⌋₊ with hb
  refine ⟨∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n,
    ∑ n ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log n, ?_, ?_, ?_, ?_, rfl⟩
  · rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro n _
    split_ifs with h
    · rw [ArithmeticFunction.vonMangoldt_apply_prime h]
    · exact ArithmeticFunction.vonMangoldt_nonneg
  · unfold psiWin
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
      have := Nat.ceil_le_floor_add_one x
      exact ⟨by omega, hn.2⟩
    · intros; exact ArithmeticFunction.vonMangoldt_nonneg
  · have h1 : psiWin x y ≤ ∑ n ∈ insert a (Finset.Ioc a b), ArithmeticFunction.vonMangoldt n := by
      unfold psiWin
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [Finset.mem_Ioc, Finset.mem_Icc, Finset.mem_insert] at hn ⊢
        have := Nat.floor_le_ceil x
        omega
      · intros; exact ArithmeticFunction.vonMangoldt_nonneg
    rw [Finset.sum_insert (by simp)] at h1
    have h2 : ArithmeticFunction.vonMangoldt a ≤ Real.log x := by
      refine (ArithmeticFunction.vonMangoldt_le_log).trans ?_
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · rw [h0]; simp; exact Real.log_nonneg hx
      · apply Real.log_le_log (by exact_mod_cast h0)
        exact Nat.floor_le hx0
    linarith
  · have e : ∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n -
        ∑ n ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log n =
        ∑ n ∈ (Finset.Ioc a b).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs with h
      · simp [h, ArithmeticFunction.vonMangoldt_apply_prime]
      · simp
    rw [e]
    calc _ ≤ ∑ n ∈ (Finset.Ioc 0 b).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
            exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
          · intros; exact ArithmeticFunction.vonMangoldt_nonneg
      _ = Chebyshev.psi (x + y) - Chebyshev.theta (x + y) :=
          (Chebyshev.psi_sub_theta_eq_sum_not_prime _).symm
      _ ≤ _ := Chebyshev.psi_sub_theta_le hxy

lemma prime_log_bounds (x y : ℝ) (hx : 1 ≤ x) (hy : 0 ≤ y) :
    (((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime).card : ℝ) * Real.log x ≤
      ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime, Real.log n ∧
    ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime, Real.log n ≤
      (((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime).card : ℝ) * (Real.log x + y / x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  constructor
  · rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    have : x < n := (Nat.floor_lt hx0.le).1 hn.1.1
    exact Real.log_le_log hx0 this.le
  · rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    have h1 : (n : ℝ) ≤ x + y := (Nat.le_floor_iff (by linarith)).1 hn.1.2
    have hn0 : (0 : ℝ) < n := by
      have := hn.2.pos; exact_mod_cast this
    calc Real.log n ≤ Real.log (x + y) := Real.log_le_log hn0 h1
      _ = Real.log x + Real.log (1 + y / x) := by
          rw [← Real.log_mul hx0.ne' (by positivity)]; congr 1; field_simp
      _ ≤ _ := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + y / x by positivity)
          linarith

lemma alg (N T y L0 δ : ℝ) (hL : 1 ≤ L0) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (h1 : N * L0 ≤ T) (h2 : T ≤ N * (L0 + δ)) : |N - y / L0| ≤ |T - y| + δ * T := by
  have hL0 : 0 < L0 := by linarith
  have hNT : N ≤ T := by nlinarith
  have hT : 0 ≤ T := by linarith
  have h3 : |N * L0 - y| ≤ |T - y| + δ * T := by
    rw [abs_le]
    constructor
    · have := le_abs_self (T - y)
      have := neg_abs_le (T - y)
      nlinarith [mul_le_mul_of_nonneg_left hNT hδ, abs_nonneg (T - y)]
    · have := le_abs_self (T - y)
      nlinarith [mul_nonneg hδ hT, abs_nonneg (T - y)]
  have e : N - y / L0 = (N * L0 - y) / L0 := by field_simp
  rw [e, abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
  nlinarith [abs_nonneg (N * L0 - y)]

lemma eventually_aux : ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x →
    1 ≤ x ∧ 1 ≤ Real.log x ∧ Lx x ≤ Real.log x / 100 ∧
      300 * x ^ ((13 : ℝ) / 25) ≤ x ^ ((167 : ℝ) / 300) := by
  have h1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have h2 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have h3 : ∀ᶠ x : ℝ in atTop, 100 ≤ Real.log x ^ ((3 : ℝ) / 4) :=
    (((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3 / 4)).comp
      Real.tendsto_log_atTop)).eventually_ge_atTop 100
  have h4 : ∀ᶠ x : ℝ in atTop, 300 ≤ x ^ ((11 : ℝ) / 300) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 11 / 300)).eventually_ge_atTop 300
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 (h1.and (h2.and (h3.and (h4.and (eventually_ge_atTop 1)))))
  refine ⟨x₁, fun x hx => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := hx₁ x hx
  refine ⟨a1, a2, ?_, ?_⟩
  · have hl : 0 < Real.log x := by linarith
    have : Real.log x = Lx x * Real.log x ^ ((3 : ℝ) / 4) := by
      unfold Lx
      rw [← Real.rpow_add hl]; norm_num
    have hLx : 0 ≤ Lx x := Real.rpow_nonneg hl.le _
    nlinarith
  · have : x ^ ((167 : ℝ) / 300) = x ^ ((13 : ℝ) / 25) * x ^ ((11 : ℝ) / 300) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    rw [this]
    have : 0 ≤ x ^ ((13 : ℝ) / 25) := Real.rpow_nonneg (by linarith) _
    nlinarith

lemma err_small (x y : ℝ) (hx : 1 ≤ x) (hy0 : 0 ≤ y) (hyx : y ≤ x)
    (h : 300 * x ^ ((13 : ℝ) / 25) ≤ x ^ ((167 : ℝ) / 300)) :
    Real.log x + 2 * Real.sqrt (x + y) * Real.log (x + y) ≤ x ^ ((167 : ℝ) / 300) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set u := 2 * x with hu
  have hu1 : 1 ≤ u := by linarith
  have hxy : x + y ≤ u := by linarith
  have hlogxy : Real.log (x + y) ≤ Real.log u := Real.log_le_log (by linarith) hxy
  have hlogx : Real.log x ≤ Real.log u := Real.log_le_log hx0 (by linarith)
  have hlu : Real.log u ≤ 50 * u ^ ((1 : ℝ) / 50) := by
    have := Real.log_le_rpow_div (show 0 ≤ u by linarith) (show (0:ℝ) < 1 / 50 by norm_num)
    have e : u ^ ((1 : ℝ) / 50) / (1 / 50) = 50 * u ^ ((1 : ℝ) / 50) := by field_simp
    linarith
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hsq : Real.sqrt (x + y) ≤ u ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt hxy
  have hsq1 : 1 ≤ u ^ ((1 : ℝ) / 2) := Real.one_le_rpow hu1 (by norm_num)
  have hsq0 : 0 ≤ Real.sqrt (x + y) := Real.sqrt_nonneg _
  have hlxy0 : 0 ≤ Real.log (x + y) := Real.log_nonneg (by linarith)
  have step1 : Real.log x + 2 * Real.sqrt (x + y) * Real.log (x + y) ≤
      3 * u ^ ((1 : ℝ) / 2) * Real.log u := by
    nlinarith [mul_le_mul hsq hlogxy hlxy0 (by linarith)]
  have step2 : 3 * u ^ ((1 : ℝ) / 2) * Real.log u ≤ 150 * u ^ ((13 : ℝ) / 25) := by
    have e : u ^ ((13 : ℝ) / 25) = u ^ ((1 : ℝ) / 2) * u ^ ((1 : ℝ) / 50) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hlu (by linarith : (0:ℝ) ≤ 3 * u ^ ((1 : ℝ) / 2))]
  have step3 : u ^ ((13 : ℝ) / 25) ≤ 2 * x ^ ((13 : ℝ) / 25) := by
    rw [hu, Real.mul_rpow (by norm_num) hx0.le]
    have : (2:ℝ) ^ ((13 : ℝ) / 25) ≤ 2 ^ (1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hx0.le _)
  linarith

end PartF

/-- F. From Λ to primes (partial summation). -/
theorem pi_of_psi (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (h : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      y ∈ Set.Icc (x ^ (17 / 30 + ε)) (x ^ (0.99 : ℝ)) →
      |psiWin x y - y| ≤ C * y * Real.exp (-Lx x)) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      y ∈ Set.Icc (x ^ (17 / 30 + ε)) (x ^ (0.99 : ℝ)) →
      |((Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊) - y / Real.log x| ≤
        C * y * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) := by
  obtain ⟨C, x₀, hC⟩ := h
  obtain ⟨x₁, hx₁⟩ := PartF.eventually_aux
  refine ⟨2 * |C| + 2, max x₀ x₁, fun x hx y hy => ?_⟩
  have hxa : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxb : x₁ ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx1, hlog, hL, hbig⟩ := hx₁ x hxb
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := by linarith
  have hLx0 : 0 ≤ Lx x := Real.rpow_nonneg hlogpos.le _
  obtain ⟨hy1, hy2⟩ := hy
  have hpow0 : 0 < x ^ (17 / 30 + ε) := Real.rpow_pos_of_pos hx0 _
  have hy0 : 0 < y := lt_of_lt_of_le hpow0 hy1
  have hyx : y ≤ x := by
    refine hy2.trans ?_
    calc x ^ (0.99 : ℝ) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  set E := Real.exp (-Lx x) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hEdef]; exact Real.exp_le_one_iff.2 (by linarith)
  have hE : x ^ (-(1 : ℝ) / 100) ≤ E := by
    rw [Real.rpow_def_of_pos hx0, hEdef]
    apply Real.exp_le_exp.2
    have : Lx x ≤ Real.log x / 100 := hL
    linarith
  have hyE : x ^ ((167 : ℝ) / 300) ≤ y * E := by
    have e : x ^ ((167 : ℝ) / 300) = x ^ ((17 : ℝ) / 30) * x ^ (-(1 : ℝ) / 100) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [e]
    have h1 : x ^ ((17 : ℝ) / 30) ≤ y :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) hy1
    exact mul_le_mul h1 hE (Real.rpow_nonneg hx0.le _) hy0.le
  have hδ : y / x ≤ E := by
    refine le_trans ?_ hE
    have e : x ^ (-(1 : ℝ) / 100) = x ^ (0.99 : ℝ) / x := by
      have := Real.rpow_sub hx0 (0.99 : ℝ) 1
      rw [Real.rpow_one] at this
      rw [← this]; norm_num
    rw [e]
    exact div_le_div_of_nonneg_right hy2 hx0.le
  have hψ : |psiWin x y - y| ≤ |C| * y * E := by
    refine (hC x hxa y ⟨hy1, hy2⟩).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hy0.le) hE0.le
  obtain ⟨S, T, hTS, hSψ, hψS, hSTR, hT⟩ := PartF.psi_window x y hx1 hy0.le
  obtain ⟨hb1, hb2⟩ := PartF.prime_log_bounds x y hx1 hy0.le
  rw [← hT] at hb1 hb2
  have hpi := PartF.pi_sub ⌊x⌋₊ ⌊x + y⌋₊ (Nat.floor_le_floor (by linarith))
  rw [hpi]
  set N : ℝ := (((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime).card : ℝ) with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hR := PartF.err_small x y hx1 hy0.le hyx hbig
  have hRy : Real.log x + 2 * Real.sqrt (x + y) * Real.log (x + y) ≤ y * E := hR.trans hyE
  have hTy : |T - y| ≤ (|C| + 1) * y * E := by
    have h1 := abs_le.1 hψ
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2]
  have hTle : T ≤ y + |C| * y * E := by
    have := (abs_le.1 hψ).2
    linarith
  have hδT : (y / x) * T ≤ E * (y + |C| * y * E) := by
    have hT0 : 0 ≤ T := le_trans (mul_nonneg hN0 hlogpos.le) hb1
    exact mul_le_mul hδ hTle hT0 hE0.le
  have key := PartF.alg N T y (Real.log x) (y / x) hlog (by positivity) hN0 hb1 hb2
  have hfin : (|T - y| + y / x * T) ≤ (2 * |C| + 2) * y * E := by
    have hc : |C| * y * E * E ≤ |C| * y * E :=
      mul_le_of_le_one_right (mul_nonneg (mul_nonneg (abs_nonneg C) hy0.le) hE0.le) hE1
    have h2 : E * (y + |C| * y * E) = y * E + |C| * y * E * E := by ring
    linarith
  have hLx : Real.log x ^ (1 / 4 : ℝ) = Lx x := rfl
  rw [hLx]
  exact key.trans hfin

end GMS1213


theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      y ∈ Set.Icc (x ^ (17 / 30 + ε)) (x ^ (0.99 : ℝ)) →
      |((Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊) - y / Real.log x| ≤
        C * y * Real.exp (-Real.log x ^ (1 / 4 : ℝ)) := by
  intro ε hε
  set ε' := min ε (1 / 100) with hε'
  have h1 : 0 < ε' := lt_min hε (by norm_num)
  have h2 : ε' ≤ 1 / 100 := min_le_right _ _
  obtain ⟨C, x₀, h⟩ := GMS1213.pi_of_psi ε' h1 h2 (GMS1213.psi_short_interval ε' h1 h2)
  refine ⟨C, max x₀ 2, fun x hx y hy => ?_⟩
  have hx1 : 1 ≤ x := by have := le_max_right x₀ 2; linarith
  refine h x (le_trans (le_max_left _ _) hx) y ⟨?_, hy.2⟩
  calc x ^ (17 / 30 + ε') ≤ x ^ (17 / 30 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by have := min_le_left ε (1 / 100); linarith)
    _ ≤ y := hy.1
