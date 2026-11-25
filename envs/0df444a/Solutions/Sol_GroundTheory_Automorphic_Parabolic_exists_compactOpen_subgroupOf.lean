-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_compactOpen_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:49.369202+00:00
-- url     : https://prove2.me/submissions/a34f0f42-2a99-49e2-8e22-3470153af0b7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_unipotentCompactG_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_unipotentCompactG
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_conj_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentCompactG_eq
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {γ : Fin n → ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {H : Subgroup (GL (Fin n) F)}
    (hH : IsClosed (H : Set (GL (Fin n) F))) (hHN : H ≤ unipotentRadical F n γ)
    (s : Finset H) :
    ∃ K : Subgroup H, IsCompact (K : Set H) ∧ IsOpen (K : Set H) ∧ ∀ x ∈ s, x ∈ K := by
  obtain ⟨e, he⟩ := exists_unipotentCompactG_of_isCompact (γ := γ)
    ((s.finite_toSet.image (fun x : H => (x : GL (Fin n) F))).isCompact)
    (by rintro _ ⟨x, -, rfl⟩; exact hHN x.2)
  refine ⟨(unipotentCompactG γ e).subgroupOf H, ?_, ?_, fun x hx => he ⟨x, hx, rfl⟩⟩
  · rw [Subgroup.coe_subgroupOf]
    exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_unipotentCompactG e)
  · have : (unipotentCompactG (F := F) γ e).subgroupOf H =
        ((integralGL F n).comap (MulAut.conj (rankTorus F n γ e)).toMonoidHom).subgroupOf H := by
      ext x
      simp only [Subgroup.mem_subgroupOf, unipotentCompactG_eq, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hHN x.2, h⟩⟩
    rw [this, Subgroup.coe_subgroupOf]
    exact (isOpen_conj_integralGL _).preimage continuous_subtype_val
end GroundTheory.Automorphic.Parabolic
