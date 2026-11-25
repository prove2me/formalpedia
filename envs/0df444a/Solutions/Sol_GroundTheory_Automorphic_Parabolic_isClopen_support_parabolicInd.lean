-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isClopen_support_parabolicInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:56.334714+00:00
-- url     : https://prove2.me/submissions/7ef7eaaa-6c28-4c06-9a46-383954e750a9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_parabolicIndSpace
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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (f : parabolicIndSpace F n β σ) :
    IsClopen {g : GL (Fin n) F | (f : GL (Fin n) F → W) g ≠ 0} := by
  obtain ⟨-, K, hKo, hK⟩ := (mem_parabolicIndSpace σ).1 f.2
  have hnhds : ∀ g : GL (Fin n) F, (fun k => g * k) '' (K : Set (GL (Fin n) F)) ∈ 𝓝 g := by
    intro g
    have := (isOpenMap_mul_left g).image_mem_nhds (hKo.mem_nhds K.one_mem)
    simpa using this
  have hval : ∀ g, ∀ x ∈ (fun k => g * k) '' (K : Set (GL (Fin n) F)),
      (f : GL (Fin n) F → W) x = (f : GL (Fin n) F → W) g := by
    rintro g _ ⟨k, hk, rfl⟩
    exact hK k hk g
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro g hg
    refine Filter.mem_of_superset (hnhds g) fun x hx => ?_
    simp only [mem_compl_iff, mem_ofPred_eq, not_not] at hg ⊢
    rw [hval g x hx, hg]
  · rw [isOpen_iff_mem_nhds]
    intro g hg
    refine Filter.mem_of_superset (hnhds g) fun x hx => ?_
    simp only [mem_ofPred_eq] at hg ⊢
    rw [hval g x hx]
    exact hg
end GroundTheory.Automorphic.Parabolic
