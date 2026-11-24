-- Prove2me | solution 1 for GlobalTheory.UnRep.SmallMat.exists_nsmul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:22:14.591827+00:00
-- url     : https://prove2.me/submissions/436fbf82-cfcb-4533-b115-f0751feef11c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatrices
import Theorems.Thm_GlobalTheory_AdLat_exists_eq_algebraMap_add_nsmul
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SmallMat
open GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.UnRep.SmallMat
theorem _root_.solution (b : FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ v, (m • b) v ∈ v.adicCompletionIntegers F := by
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F 1 one_pos b
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset F)
  have hc : IsIntegral ℤ (y • x) := hy x (by simp)
  have hc' : IsIntegral ℤ (y.natAbs • x) := by
    rcases Int.natAbs_eq y with h | h
    · have : y.natAbs • x = y • x := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hc
    · have : y.natAbs • x = -(y • x) := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hc.neg
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, fun v => ?_⟩
  rw [smul_add, ← map_nsmul]
  refine add_mem ?_ (nsmul_mem (nsmul_mem (ha v) 1) _)
  exact v.coe_mem_adicCompletionIntegers (K := F) (⟨y.natAbs • x, hc'⟩ : 𝓞 F)
end GlobalTheory.UnRep.SmallMat
