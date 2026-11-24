-- Prove2me | solution 1 for GlobalTheory.CNorm.pIdx_range_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:29:32.54398+00:00
-- url     : https://prove2.me/submissions/cea55b21-d582-41cb-9720-9184181decb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexTopOfGroupFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardQuotSpanAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteSpanAlgebraMapOfFreeFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormCoeffMinpolyLeOneOfNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
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
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution (p : ℕ) {A B : Type} [CommGroup A] [CommGroup B] (j : A →* B)
    (hj : Function.Injective j) : pIdx p j.range = pIdx p (⊤ : Subgroup A) := by
  have h : pows p j.range = (pows p (⊤ : Subgroup A)).map j := by
    ext x
    simp only [pows, Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_top,
      true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, map_pow _ _ _⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, (map_pow _ _ _).symm⟩
  unfold pIdx
  rw [h, MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hj]
end GlobalTheory.CNorm
