-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.leviUnipotent_refineFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:37.821366+00:00
-- url     : https://prove2.me/submissions/f5925489-5183-4003-986c-32f2b79160e2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_refineFun_eq_iff
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_refineFun_lt_of_eq
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
variable (F)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (β γ : Fin n → ℕ) :
    leviUnipotent F n β γ = leviUnipotent F n β (refineFun β γ) := by
  ext u
  simp only [leviUnipotent, Subgroup.mem_subgroupOf]
  have hu := mem_levi.1 u.2
  constructor
  · intro h
    obtain ⟨hP, h1⟩ := mem_unipotentRadical.1 h
    refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · by_cases hb : β i = β j
      · exact hP ((refineFun_lt_of_eq hb).1 hij)
      · exact hu i j hb
    · exact h1 i j (refineFun_eq_iff.1 hij).2
  · intro h
    obtain ⟨hP, h1⟩ := mem_unipotentRadical.1 h
    refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · by_cases hb : β i = β j
      · exact hP ((refineFun_lt_of_eq hb).2 hij)
      · exact hu i j hb
    · by_cases hb : β i = β j
      · exact h1 i j (refineFun_eq_iff.2 ⟨hb, hij⟩)
      · rw [hu i j hb, one_apply_ne (fun e => hb (by rw [e]))]
end GroundTheory.Automorphic.Parabolic
