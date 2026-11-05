-- Prove2me | solution 1 for MFGLiquidation.Nash.theorem_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:31:36.028666+00:00
-- url     : https://prove2.me/submissions/d767e403-a598-4f1f-bd1a-57cd490eea6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MFGLiquidation_Nash_Setting
import Definitions.Def_MFGLiquidation_Nash_Game
import Definitions.Def_MFGLiquidation_Nash_Players
import Theorems.Thm_MFGLiquidation_Nash_eq_3_2
import Theorems.Thm_MFGLiquidation_Nash_eq_3_3
import Theorems.Thm_MFGLiquidation_Nash_bounds_I1_I2
import Theorems.Thm_MFGLiquidation_Nash_proposition_2_9

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

/-- Elementary bound: the two error terms are `O(1/√N)` with a constant independent of `N`. -/
lemma err_le (m c K T C n : ℝ) (hm : 0 < m) (hc : 0 ≤ c) (hK : K ≤ c) (hT : 0 ≤ T)
    (hC : 0 ≤ C) (hn : 1 ≤ n) :
    m * K * T / n + 2 * K * T * Real.sqrt m / n
        * (Real.sqrt m + Real.sqrt (2 * (m + (2 * n - 1) * C)))
      + 2 * K * T * Real.sqrt m * Real.sqrt (m + (2 * n - 1) * C) / n
    ≤ (m * c * T + 2 * c * T * Real.sqrt m * (Real.sqrt m + Real.sqrt (2 * (m + 2 * C)))
        + 2 * c * T * Real.sqrt m * Real.sqrt (m + 2 * C)) / Real.sqrt n := by
  have hn0 : 0 < n := by linarith
  set s := Real.sqrt n with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hn
  have hss : s ^ 2 = n := Real.sq_sqrt hn0.le
  have hsm : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  set a := Real.sqrt (2 * (m + (2 * n - 1) * C))
  set a' := Real.sqrt (2 * (m + 2 * C))
  set b := Real.sqrt (m + (2 * n - 1) * C)
  set b' := Real.sqrt (m + 2 * C)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha'0 : 0 ≤ a' := Real.sqrt_nonneg _
  have hb'0 : 0 ≤ b' := Real.sqrt_nonneg _
  have hmn : m ≤ n * m := by nlinarith
  have ha : a ≤ s * a' := by
    have : a = Real.sqrt (2 * (m + (2 * n - 1) * C)) := rfl
    rw [this, hs, ← Real.sqrt_mul hn0.le]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hb : b ≤ s * b' := by
    have : b = Real.sqrt (m + (2 * n - 1) * C) := rfl
    rw [this, hs, ← Real.sqrt_mul hn0.le]
    apply Real.sqrt_le_sqrt
    nlinarith
  -- replace K by c
  have hu : 0 ≤ T * Real.sqrt m := mul_nonneg hT hsm
  have step1 : m * K * T / n + 2 * K * T * Real.sqrt m / n * (Real.sqrt m + a)
      + 2 * K * T * Real.sqrt m * b / n
      ≤ (m * c * T + 2 * c * T * Real.sqrt m * (Real.sqrt m + a)
        + 2 * c * T * Real.sqrt m * b) / n := by
    have e : m * K * T / n + 2 * K * T * Real.sqrt m / n * (Real.sqrt m + a)
      + 2 * K * T * Real.sqrt m * b / n
      = (m * K * T + 2 * K * T * Real.sqrt m * (Real.sqrt m + a)
        + 2 * K * T * Real.sqrt m * b) / n := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hn0.le
    have h1 : 0 ≤ m * T := mul_nonneg hm.le hT
    have h2 : 0 ≤ T * Real.sqrt m * (Real.sqrt m + a) := mul_nonneg hu (by positivity)
    have h3 : 0 ≤ T * Real.sqrt m * b := mul_nonneg hu hb0
    nlinarith [mul_le_mul_of_nonneg_left hK h1, mul_le_mul_of_nonneg_left hK h2,
      mul_le_mul_of_nonneg_left hK h3]
  refine step1.trans ?_
  have hsp : 0 < s := by linarith
  rw [div_le_div_iff₀ hn0 hsp, ← hss]
  have hcT : 0 ≤ c * T * Real.sqrt m := by positivity
  have hmcT : 0 ≤ m * c * T := by positivity
  have k1 : 2 * c * T * Real.sqrt m * a ≤ 2 * c * T * Real.sqrt m * (s * a') :=
    mul_le_mul_of_nonneg_left ha (by positivity)
  have k2 : 2 * c * T * Real.sqrt m * b ≤ 2 * c * T * Real.sqrt m * (s * b') :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have k3 : 0 ≤ 2 * c * T * Real.sqrt m * Real.sqrt m := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hs1 hmcT, mul_le_mul_of_nonneg_left hs1 k3,
    mul_le_mul_of_nonneg_left k1 hsp.le, mul_le_mul_of_nonneg_left k2 hsp.le]


/-- Under Assumption 3.1 every player's `κ_max` is below the uniform bound of `κ`. -/
lemma kappaMax_le {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (Pop : Population Ω k) (hT : 0 < Pop.T) (c : ℝ)
    (hc : ∀ t x w w0, 0 ≤ Pop.κf t x w w0 ∧ Pop.κf t x w w0 ≤ c) (i : ℕ) :
    (Pop.player i).kappaMax P ≤ c := by
  have hne : dtP Pop.T P ≠ 0 := by
    intro h
    have h1 := Measure.prod_prod (μ := volume.restrict (Set.Icc (0 : ℝ) Pop.T)) (ν := P)
      Set.univ Set.univ
    have h2 : (dtP Pop.T P) Set.univ = 0 := by rw [h]; rfl
    unfold dtP at h2
    rw [Set.univ_prod_univ] at h1
    rw [h1, Measure.restrict_apply_univ, Real.volume_Icc, measure_univ, mul_one] at h2
    simp at h2
    exact (ne_of_gt hT) (by exact_mod_cast h2)
  have : (ae (dtP (Pop.player i).T P)).NeBot := ae_neBot.mpr hne
  unfold Data.kappaMax esssupT essSup
  apply Filter.limsup_le_of_le
  · apply Filter.IsBounded.isCobounded_flip
    exact ⟨0, Filter.eventually_map.2 (Filter.Eventually.of_forall fun p => (hc _ _ _ _).1)⟩
  · exact Filter.Eventually.of_forall fun p => (hc _ _ _ _).2

end MFGLiquidation.Nash

open MFGLiquidation.Nash

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (Pop : Population Ω k) (ν : Measure ℝ) (hstd : Pop.Standing P ν)
    (h31 : Pop.Assumption31)
    (h23 : ∀ i, (Pop.player i).Assumption23 P (hstd.player i))
    (Xp Yp : ℕ → ℝ≥0 → Ω → ℝ) (Zp : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hsol : ∀ i, SolvesFBSDE23InClass (hstd.player i) (Xp i) (Yp i) (Zp i))
    (M : ℝ → ℝ) (hM : Measurable M) (hMpos : ∀ x, 0 < M x)
    (hψM : ∀ i, P[fun ω => ∫ t in Set.Icc (0 : ℝ) Pop.T, Pop.xiStar Yp i t.toNNReal ω ^ 2
      | MeasurableSpace.comap (Pop.Xs i) inferInstance] ≤ᵐ[P] fun ω => M (Pop.Xs i ω)) :
    ∃ g : ℝ → ℝ, ∀ N : ℕ, 1 ≤ N → ∀ i < N, ∀ ξ : ℝ≥0 → Ω → ℝ, Pop.AdmN hstd M i ξ →
      Pop.costN P N i (Pop.xiStar Yp)
        ≤ᵐ[P] fun ω => Pop.costN P N i (Function.update (Pop.xiStar Yp) i ξ) ω
          + g (Pop.Xs i ω) / Real.sqrt N := by
  obtain ⟨μ, hμ⟩ := eq_3_2 P Pop ν hstd h31 h23 Xp Yp Zp hsol
  obtain ⟨C0, hC0⟩ := eq_3_3 P Pop ν hstd h31 h23 Xp Yp Zp hsol
  have hC : ∀ j, ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) Pop.T, ‖Pop.xiStar Yp j t.toNNReal ω‖ₑ ^ 2
      ∂volume ∂P ≤ ENNReal.ofReal (max C0 0) :=
    fun j => (hC0 j).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hb := bounds_I1_I2 P Pop ν hstd h31 h23 Xp Yp Zp hsol M hM hMpos hψM μ hμ (max C0 0)
    (le_max_right _ _) hC
  obtain ⟨c, hc⟩ := h31.κf_bdd
  have hc0 : 0 ≤ c := (hc 0 0 0 0).1.trans (hc 0 0 0 0).2
  set C := max C0 0 with hCdef
  have hCnn : 0 ≤ C := le_max_right _ _
  refine ⟨fun x => (M x * c * Pop.T + 2 * c * Pop.T * Real.sqrt (M x)
      * (Real.sqrt (M x) + Real.sqrt (2 * (M x + 2 * C)))
      + 2 * c * Pop.T * Real.sqrt (M x) * Real.sqrt (M x + 2 * C)), ?_⟩
  intro N hN i hi ξ hξ
  obtain ⟨hI1, hI2⟩ := hb N hN i hi ξ hξ
  have hopt : cost (hstd.player i) μ (Pop.xiStar Yp i) ≤ᵐ[P] cost (hstd.player i) μ ξ :=
    (proposition_2_9 P (Pop.player i) (hstd.player i) (h23 i) (Xp i) (Yp i) (Zp i) (hsol i) μ
      (hμ i)).2 ξ hξ.1
  have e1 : Pop.I1 P N i μ Yp ξ
      = Pop.costN P N i (Function.update (Pop.xiStar Yp) i ξ) - cost (hstd.player i) μ ξ := by
    unfold Population.I1 Population.costN cost
    congr 1
    · congr 1
      funext ω
      congr 1
      funext s
      rw [Function.update_self, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hi),
        Function.update_self]
      have hsum : ∑ j ∈ (Finset.range N).erase i, Function.update (Pop.xiStar Yp) i ξ j s.toNNReal ω
          = ∑ j ∈ (Finset.range N).erase i, Pop.xiStar Yp j s.toNNReal ω :=
        Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
      rw [hsum]
      ring
    · congr 1
      funext ω
      congr 1
      funext s
      ring
  have e2 : Pop.I2 P N i μ Yp
      = cost (hstd.player i) μ (Pop.xiStar Yp i) - Pop.costN P N i (Pop.xiStar Yp) := by
    unfold Population.I2 Population.costN cost
    congr 1
    congr 1
    funext ω
    congr 1
    funext s
    ring
  have hTpos : (0 : ℝ) < Pop.T := hstd.T_pos
  have hK := kappaMax_le P Pop hstd.T_pos c hc i
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  filter_upwards [hI1, hI2, hopt] with ω h1 h2 h3
  have key := err_le (M (Pop.Xs i ω)) c ((Pop.player i).kappaMax P) Pop.T C N
    (hMpos _) hc0 hK hTpos.le hCnn hn
  have f1 : Pop.costN P N i (Function.update (Pop.xiStar Yp) i ξ) ω
      = cost (hstd.player i) μ ξ ω + Pop.I1 P N i μ Yp ξ ω := by
    rw [e1]; simp
  have f2 : Pop.costN P N i (Pop.xiStar Yp) ω
      = cost (hstd.player i) μ (Pop.xiStar Yp i) ω - Pop.I2 P N i μ Yp ω := by
    rw [e2]; simp
  rw [f1, f2]
  have a1 := neg_abs_le (Pop.I1 P N i μ Yp ξ ω)
  have a2 := neg_abs_le (Pop.I2 P N i μ Yp ω)
  have a3 := le_abs_self (Pop.I2 P N i μ Yp ω)
  linarith
