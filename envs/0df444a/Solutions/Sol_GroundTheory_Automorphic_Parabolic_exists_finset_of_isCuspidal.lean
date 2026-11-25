-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_finset_of_isCuspidal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:48:36.157794+00:00
-- url     : https://prove2.me/submissions/5cbb4a03-45c4-4822-84aa-daf2d462df3a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {σ : Representation ℂ (levi F n β) W} (hc : IsCuspidal σ)
    {S : Finset (Fin n)} (hS : ∃ i j, β i = β j ∧ i ∈ S ∧ j ∉ S) (w : W) :
    ∃ U : Finset (levi F n β), (∀ u ∈ U, (u : GL (Fin n) F) ∈ unipotentRadical F n (splitFun S)) ∧
      w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = σ u x - x} := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := hS
  have hsub := hc (splitFun S) ⟨i, j, hij, by simp [splitFun, hi, hj]⟩
  have hw : w ∈ Representation.Coinvariants.ker
      (σ.comp (leviUnipotent F n β (splitFun S)).subtype) :=
    (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
  obtain ⟨T, hT, hwT⟩ := Submodule.mem_span_finite_of_mem_span hw
  have hpre : ∀ y ∈ T, ∃ gv : leviUnipotent F n β (splitFun S) × W,
      σ (gv.1 : levi F n β) gv.2 - gv.2 = y := by
    intro y hy
    obtain ⟨gv, h⟩ := hT hy
    exact ⟨gv, h⟩
  choose! pre hpre using hpre
  refine ⟨T.image fun y => ((pre y).1 : levi F n β), ?_, ?_⟩
  · intro u hu
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hu
    exact Subgroup.mem_subgroupOf.1 (pre y).1.2
  · refine Submodule.span_mono ?_ hwT
    intro y hy
    exact ⟨((pre y).1 : levi F n β), Finset.mem_image_of_mem _ hy, (pre y).2, (hpre y hy).symm⟩
end GroundTheory.Automorphic.Parabolic
