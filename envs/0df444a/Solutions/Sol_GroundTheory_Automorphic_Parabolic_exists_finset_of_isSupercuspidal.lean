-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_finset_of_isSupercuspidal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:55:57.7538+00:00
-- url     : https://prove2.me/submissions/3e276d55-1c3b-4d48-b1bf-a11eb3c08812

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
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
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hsc : IsSupercuspidal π) {S : Finset (Fin n)}
    (hS : ∃ i j, i ∈ S ∧ j ∉ S) (w : V) :
    ∃ U : Finset (GL (Fin n) F), (∀ u ∈ U, u ∈ unipotentRadical F n (splitFun S)) ∧
      w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = π u x - x} := by
  classical
  obtain ⟨i, j, hi, hj⟩ := hS
  have hsub := hsc (splitFun S) ⟨i, j, by simp [splitFun, hi, hj]⟩
  have hw : w ∈ Representation.Coinvariants.ker (π.comp (unipotentRadical F n (splitFun S)).subtype) :=
    (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
  obtain ⟨T, hT, hwT⟩ := Submodule.mem_span_finite_of_mem_span hw
  have hpre : ∀ y ∈ T, ∃ gv : unipotentRadical F n (splitFun S) × V,
      π (gv.1 : GL (Fin n) F) gv.2 - gv.2 = y := by
    intro y hy
    obtain ⟨gv, h⟩ := hT hy
    exact ⟨gv, h⟩
  choose! pre hpre using hpre
  refine ⟨T.image fun y => ((pre y).1 : GL (Fin n) F), ?_, ?_⟩
  · intro u hu
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hu
    exact (pre y).1.2
  · refine Submodule.span_mono ?_ hwT
    intro y hy
    exact ⟨((pre y).1 : GL (Fin n) F), Finset.mem_image_of_mem _ hy, (pre y).2, (hpre y hy).symm⟩
end GroundTheory.Automorphic.Parabolic
