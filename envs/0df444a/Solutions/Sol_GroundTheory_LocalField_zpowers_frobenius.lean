-- Prove2me | solution 1 for GroundTheory.LocalField.zpowers_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:40.864861+00:00
-- url     : https://prove2.me/submissions/b8aeb51a-8bbd-40b8-b4f9-26de5c536e06

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution (h : ramificationIndex K L = 1) :
    Subgroup.zpowers (frobenius K L h) = ⊤ := by
  let := Fintype.ofFinite 𝓀[K]
  rw [eq_top_iff]
  intro σ _
  obtain ⟨k, hk⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow 𝓀[K] 𝓀[L]).2
    (galoisEquivResidue K L h σ)
  refine ⟨(k : ℕ), ?_⟩
  apply (galoisEquivResidue K L h).injective
  simp only [zpow_natCast, map_pow]
  rw [← hk, frobenius, MulEquiv.apply_symm_apply]
end GroundTheory.LocalField
