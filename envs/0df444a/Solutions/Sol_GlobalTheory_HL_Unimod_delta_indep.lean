-- Prove2me | solution 1 for GlobalTheory.HL.Unimod.delta_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:03.281796+00:00
-- url     : https://prove2.me/submissions/5c07705e-0d74-4372-be49-9e1a4cc8f922

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
import Theorems.Thm_GlobalTheory_HL_Unimod_comm_conj
import Theorems.Thm_GlobalTheory_HL_invVol_mul_pos_le_conj
import Theorems.Thm_GlobalTheory_T_haarInvVolume_conj_modular_character
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
    {Λ0 Λ : Submodule L.O (Fin n → E)} (h0 : IsLat L Λ0) (hΛ : IsLat L Λ) {g} (hg : g ∈ H)
    (h1 : invVol (H ⊓ stabL L Λ) (MulAut.conj g • (H ⊓ stabL L Λ)) = 1) :
    invVol (H ⊓ stabL L Λ0) (MulAut.conj g • (H ⊓ stabL L Λ0)) = 1 := by
  have a := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hΛ h0 H).1
  have b := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ h0 hΛ H).1
  have hl := ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ hΛ hΛ H).2 g).1
  have c := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hl h0 H).1
  have d := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ h0 hl H).1
  rw [inf_stab_smul L H hΛ hg] at c d
  have e1 := ((GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h0)).2.2.2 _ a b g hg).1
  have e2 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ _ _ a b c d).1
  have e3 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ _ _ a b a b).2.1
  rw [e1, h1, mul_one] at e2
  exact mul_right_cancel₀ e3.ne' (by rw [e2, one_mul])
end GlobalTheory.HL.Unimod
