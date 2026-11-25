-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.nontrivial_jacquetModule_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:01.588007+00:00
-- url     : https://prove2.me/submissions/5906622d-9620-4b7c-9f3a-2095d1d00d67

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical
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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution [Nontrivial V] :
    Nontrivial (JacquetModule F n (fun _ : Fin n => (0 : ℕ)) π) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨⟨Representation.Coinvariants.mk _ v, 0, fun h => hv ?_⟩⟩
  have hmem := (Representation.Coinvariants.mk_eq_zero _).1 h
  have hle : Representation.Coinvariants.ker
      (π.comp (unipotentRadical F n (fun _ : Fin n => (0 : ℕ))).subtype) ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, x⟩, rfl⟩
    have hu : (u : GL (Fin n) F) = 1 := by
      apply Units.ext
      ext i j
      exact (mem_unipotentRadical.1 u.2).2 i j rfl
    simp [hu]
  exact (Submodule.mem_bot ℂ).1 (hle hmem)
end GroundTheory.Automorphic.Parabolic
