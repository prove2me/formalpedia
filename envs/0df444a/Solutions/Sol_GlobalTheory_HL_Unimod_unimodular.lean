-- Prove2me | solution 1 for GlobalTheory.HL.Unimod.unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:44:51.338844+00:00
-- url     : https://prove2.me/submissions/042b4c82-1712-40ff-9664-87d60c7dfbbd

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
import Theorems.Thm_GlobalTheory_HL_Unimod_qrefl_mem
import Theorems.Thm_GlobalTheory_HL_Unimod_inf_stab_smul
import Theorems.Thm_GlobalTheory_HL_Unimod_comm_conj
import Theorems.Thm_GlobalTheory_HL_Unimod_invVol_self
import Theorems.Thm_GlobalTheory_HL_Unimod_delta_inv
import Theorems.Thm_GlobalTheory_HL_Unimod_delta_indep
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_exists_lattice_and_inverting_automorphism_of_quasi_reflection
import Theorems.Thm_GlobalTheory_T_haarInvVolume_conj_modular_character
import Theorems.Thm_GlobalTheory_T_isometriesFixingSubspace_le_quasiReflection_closure
import Theorems.Thm_GlobalTheory_T_latticeStabilizer_commensurable_unramified_hermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Unimod
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.Unimod
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ Λ0 Λ : Submodule L.O (Fin n → E), IsLat L Λ0 → IsLat L Λ → ∀ h ∈ fixG L Hm (Submodule.span E (Set.range x)), invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (h • Λ)) = invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx Λ0 Λ h0 hΛ h hh
  have hgen := GlobalTheory.T.isometriesFixingSubspace_le_quasiReflection_closure L Hm hH m x hx
  have hq := GlobalTheory.T.exists_lattice_and_inverting_automorphism_of_quasi_reflection L Hm hH m x hx
  have hmem := fun a ha g hg => qrefl_mem L hH.1 (Submodule.span E (Set.range x)) (a := a) ha (g := g) hg
  set H := fixG L Hm (Submodule.span E (Set.range x)) with hHdef
  have key : ∀ g ∈ Subgroup.closure
      {g | ∃ a ∈ perp L Hm (Submodule.span E (Set.range x)), IsQRefl L Hm a g},
      g ∈ H ∧ invVol (H ⊓ stabL L Λ0) (MulAut.conj g • (H ⊓ stabL L Λ0)) = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, hg⟩ := hg
      have hgH := hmem a ha g hg
      refine ⟨hgH, ?_⟩
      obtain ⟨Λ1, h1, α, hα, hαg⟩ := hq a ha g hg
      refine delta_indep L H h0 h1 hgH ?_
      have M := GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h1)
      have e1 := M.2.2.1 α hα g hgH
      have e2 := M.2.1 g hgH
      have e3 := delta_inv L H h1 hgH
      rw [hαg] at e1
      rw [e1] at e3
      nlinarith
    | one => exact ⟨H.one_mem, by simp [invVol_self]⟩
    | mul a b _ _ ha hb =>
      refine ⟨H.mul_mem ha.1 hb.1, ?_⟩
      rw [(GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h0)).1 a ha.1 b hb.1, ha.2, hb.2, one_mul]
    | inv a _ ha =>
      refine ⟨H.inv_mem ha.1, ?_⟩
      have := delta_inv L H h0 ha.1
      rwa [ha.2, one_mul] at this
  have a := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hΛ h0 H).1
  have b := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ h0 hΛ H).1
  rw [inf_stab_smul L H hΛ hh,
    ((GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h0)).2.2.2 _ a b h hh).1, (key h (hgen hh)).2, one_mul]
end GlobalTheory.HL.Unimod
