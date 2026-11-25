-- Prove2me | solution 1 for GlobalTheory.HL.Unimod.comm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:35.896251+00:00
-- url     : https://prove2.me/submissions/e6cb7cf5-f7b7-4a36-a1a3-ee1c601c2a11

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerCommensurableUnramifiedHermitiaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HaarInvVolumeConjModularCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitaryGroupOrthogonalComplementUnimodular
import Theorems.Thm_GlobalTheory_HL_Unimod_inf_stab_smul
import Theorems.Thm_GlobalTheory_T_latticeStabilizer_commensurable_unramified_hermitian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Unimod
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.Unimod
theorem _root_.solution (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) : ∀ h ∈ H,
    (H ⊓ stabL L Λ).relIndex (MulAut.conj h • (H ⊓ stabL L Λ)) ≠ 0 ∧
      (MulAut.conj h • (H ⊓ stabL L Λ)).relIndex (H ⊓ stabL L Λ) ≠ 0 := by
  intro h hh
  have hl := ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ hΛ hΛ H).2 h).1
  rw [← inf_stab_smul L H hΛ hh]
  exact ⟨(GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hl hΛ H).1, (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hΛ hl H).1⟩
end GlobalTheory.HL.Unimod
