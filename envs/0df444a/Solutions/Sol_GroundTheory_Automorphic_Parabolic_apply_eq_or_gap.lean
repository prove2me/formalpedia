-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.apply_eq_or_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:46:13.473819+00:00
-- url     : https://prove2.me/submissions/3d6cbda4-6f72-43b5-8a91-f23450de1d81

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {θ C : ℤ} {b : α} {μ : Fin n → ℤ}
    (hgap : ∀ k, β k = b → μ k < θ → μ k + C ≤ θ) {u : GL (Fin n) F} (hu : u ∈ levi F n β)
    (hN : u ∈ unipotentRadical F n (splitFun (Finset.univ.filter fun j => β j = b ∧ θ ≤ μ j)))
    (i j : Fin n) : u i j = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i := by
  classical
  obtain ⟨hP, h1⟩ := mem_unipotentRadical.1 hN
  by_cases hb : β i = β j
  swap
  · left
    rw [mem_levi.1 hu i j hb, one_apply_ne (fun e => hb (by rw [e]))]
  rcases lt_trichotomy (splitFun (Finset.univ.filter fun j => β j = b ∧ θ ≤ μ j) i)
    (splitFun (Finset.univ.filter fun j => β j = b ∧ θ ≤ μ j) j) with h | h | h
  · right
    simp only [splitFun, Finset.mem_filter, Finset.mem_univ, true_and] at h
    split_ifs at h with hi hj
    · omega
    · have hjb : β j = b := hb.symm.trans hi.1
      have hjθ : μ j < θ := by
        by_contra h'
        exact hj ⟨hjb, not_lt.1 h'⟩
      have := hgap j hjb hjθ
      linarith [hi.2]
    · omega
    · omega
  · left
    exact h1 i j h
  · left
    have hij : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
    rw [one_apply_ne hij]
    exact hP h
end GroundTheory.Automorphic.Parabolic
