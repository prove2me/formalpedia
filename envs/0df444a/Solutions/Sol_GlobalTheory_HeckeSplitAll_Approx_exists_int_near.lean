-- Prove2me | solution 1 for GlobalTheory.HeckeSplitAll.Approx.exists_int_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:53.849071+00:00
-- url     : https://prove2.me/submissions/623eab7f-a809-4b4e-a349-a6b0575988a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_alg_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology Filter
open GlobalTheory GlobalTheory.HeckeSplitAll GlobalTheory.HeckeSplitAll.Approx
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeSplitAll.Approx
theorem _root_.solution (F : Type) [Field F] [NumberField F] : ∃ C : ℝ, 0 < C ∧ ∀ t : InfiniteAdeleRing F,
    ∃ o : 𝓞 F, ∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o : F) - t w‖ < C := by
  classical
  set b := integralBasis F with hb
  refine ⟨1 + ∑ w : InfinitePlace F, ∑ i, w (b i), by positivity, fun t => ?_⟩
  have hopen : IsOpen {y : InfiniteAdeleRing F | ∀ w, ‖y w - t w‖ < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (((continuous_apply w : Continuous fun y : InfiniteAdeleRing F => y w).sub
        continuous_const).norm) continuous_const
  obtain ⟨f, hf⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hopen
    ⟨t, fun w => by
      show ‖t w - t w‖ < 1
      rw [sub_self, norm_zero]; exact one_pos⟩
  have hf' : ∀ w, ‖algebraMap F w.Completion f - t w‖ < 1 := hf
  refine ⟨∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i, fun w => ?_⟩
  have e : ((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f =
      ∑ i, (((⌊b.repr f i⌋ : ℚ) - b.repr f i : ℚ) : F) * b i := by
    conv_lhs => arg 2; rw [← b.sum_repr f]
    rw [show ((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) =
      algebraMap (𝓞 F) F (∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i) from rfl, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← integralBasis_apply, ← hb, Rat.smul_def, zsmul_eq_mul]
    push_cast
    ring
  have h2 : ‖algebraMap F w.Completion (((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f)‖ ≤
      ∑ i, w (b i) := by
    rw [e, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_alg_inf, map_mul]
    refine mul_le_of_le_one_left (apply_nonneg _ _) ?_
    rw [← InfinitePlace.norm_embedding_eq, map_ratCast, Complex.norm_ratCast, ← Rat.cast_abs, ← Rat.cast_one, Rat.cast_le,
      abs_le]
    constructor <;> linarith [Int.floor_le (b.repr f i), Int.lt_floor_add_one (b.repr f i)]
  have h3 : ∑ i, w (b i) ≤ ∑ w : InfinitePlace F, ∑ i, w (b i) :=
    Finset.single_le_sum (f := fun w : InfinitePlace F => ∑ i, w (b i))
      (fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _) (Finset.mem_univ w)
  have h4 := norm_add_le (algebraMap F w.Completion (((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f))
    (algebraMap F w.Completion f - t w)
  rw [map_sub, sub_add_sub_cancel, ← map_sub] at h4
  linarith [hf' w]
end GlobalTheory.HeckeSplitAll.Approx
