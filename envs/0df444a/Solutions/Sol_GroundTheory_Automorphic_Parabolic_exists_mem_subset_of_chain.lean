-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_mem_subset_of_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:42.893114+00:00
-- url     : https://prove2.me/submissions/bfd5ca06-d512-4a5b-af08-ea0e303dec3c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
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
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module ℂ U]
  {τ : Representation ℂ G U}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {c : Set (Submodule ℂ U)} (hc : IsChain (· ≤ ·) c)
    {y : Submodule ℂ U} (hy : y ∈ c) (S : Finset U) (hS : ∀ s ∈ S, ∃ Z ∈ c, s ∈ Z) :
    ∃ Z ∈ c, ∀ s ∈ S, s ∈ Z := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨y, hy, by simp⟩
  | insert a S ha ih =>
    obtain ⟨Z₁, hZ₁, haZ₁⟩ := hS a (Finset.mem_insert_self a S)
    obtain ⟨Z₂, hZ₂, hSZ₂⟩ := ih fun s hs => hS s (Finset.mem_insert_of_mem hs)
    rcases hc.total hZ₁ hZ₂ with h | h
    · exact ⟨Z₂, hZ₂, fun s hs => by
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h haZ₁
        · exact hSZ₂ s hs⟩
    · exact ⟨Z₁, hZ₁, fun s hs => by
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact haZ₁
        · exact h (hSZ₂ s hs)⟩
end GroundTheory.Automorphic.Parabolic
