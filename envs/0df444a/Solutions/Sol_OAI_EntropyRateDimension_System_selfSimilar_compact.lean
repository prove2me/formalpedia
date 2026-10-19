-- Prove2me | solution 1 for OAI.EntropyRateDimension.System.selfSimilar_compact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:23:34.822504+00:00
-- url     : https://prove2.me/submissions/9299d18b-01e2-4979-a7d5-eeb1dec56f5f

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Basic.lean:L124-L190
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.System.selfSimilar_compact. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic

-- ---- from OAI.MeasureTheory.SelfSimilar.Basic ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem affine_continuous (S : System ι) (i : ι) : Continuous (S.affine i) := by
  unfold affine
  fun_prop

end System

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem selfSimilar_apply (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ)
    {E : Set ℝ} (hE : MeasurableSet E) :
    μ E = ∑ i, ENNReal.ofReal (S.weight i) * μ ((S.affine i) ⁻¹' E) := by
  classical
  conv_lhs => rw [hμ]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (S.affine_continuous _).measurable hE]

theorem selfSimilar_compact (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : ∃ B : ℝ, 0 < B ∧ μ (Set.Icc (-B) B)ᶜ = 0 := by
  classical
  obtain ⟨c,T,hc,hc1,hT,hr,ht⟩ := S.exists_uniform_bounds
  let R := T/(1-c)
  have hR : 0 ≤ R := div_nonneg hT (sub_pos.mpr hc1).le
  have hRc : c*R+T = R := by
    dsimp only [R]
    field_simp [ne_of_gt (sub_pos.mpr hc1)]
    ring
  let a : ℕ → ℝ := fun n => R+(1/c)^n
  let E : ℕ → Set ℝ := fun n => {x | a n < |x|}
  have ha : ∀ n, c*a (n+1)+T = a n := by
    intro n
    dsimp only [a]
    rw [pow_succ]
    field_simp
    nlinarith [hRc]
  have hcInv : 1 < 1/c := (one_lt_div hc).mpr hc1
  have hm : Antitone E := by
    intro n m hnm x hx
    have hp := pow_le_pow_right₀ hcInv.le hnm
    change R+(1/c)^m < |x| at hx
    change R+(1/c)^n < |x|
    linarith
  have hE : ∀ n, MeasurableSet (E n) := fun n => measurableSet_lt measurable_const measurable_abs
  have hpre : ∀ n i, S.affine i ⁻¹' E n ⊆ E (n+1) := by
    intro n i x hx
    have hb : |S.affine i x| ≤ c*|x|+T := calc
      _ ≤ |S.ratio i*x|+|S.offset i| := abs_add_le _ _
      _ ≤ c*|x|+T := by rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_right (hr i) (abs_nonneg x)) (ht i)
    change a n < |S.affine i x| at hx
    change a (n+1) < |x|
    nlinarith [ha n]
  have hinc : ∀ n, μ (E n) ≤ μ (E (n+1)) := by
    intro n
    rw [S.selfSimilar_apply μ hμ (hE n)]
    calc
      _ ≤ ∑ i, ENNReal.ofReal (S.weight i)*μ (E (n+1)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl (measure_mono (hpre n i)))
      _ = μ (E (n+1)) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => S.weight_nonneg i), S.weight_sum,
          ENNReal.ofReal_one, one_mul]
  have hzero : (⋂ n, E n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hpow := (tendsto_pow_atTop_atTop_of_one_lt hcInv).eventually
      (Filter.eventually_gt_atTop (|x|-R))
    obtain ⟨n,hn⟩ := hpow.exists
    have he := Set.mem_iInter.mp hx n
    change R+(1/c)^n < |x| at he
    linarith
  have hlim := tendsto_measure_iInter_atTop (fun n => (hE n).nullMeasurableSet) hm
    ⟨0, measure_ne_top μ (E 0)⟩
  rw [hzero, measure_empty] at hlim
  have hb : ∀ n, μ (E 0) ≤ μ (E n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact ih.trans (hinc n)
  have hz : μ (E 0) = 0 := le_antisymm (ge_of_tendsto' hlim hb) bot_le
  refine ⟨R+1, by linarith, ?_⟩
  have heq : (Set.Icc (-(R+1)) (R+1))ᶜ = E 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, E, a, pow_zero, Set.mem_ofPred_eq,
      ← abs_le, not_le]
  rw [heq, hz]

end System

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.System.selfSimilar_compact.{uι} := @_root_.OAI.EntropyRateDimension.System.selfSimilar_compact.{uι}
