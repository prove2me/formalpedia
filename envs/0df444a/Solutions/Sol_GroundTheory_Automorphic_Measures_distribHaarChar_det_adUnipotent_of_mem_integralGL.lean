-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.distribHaarChar_det_adUnipotent_of_mem_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:08.644421+00:00
-- url     : https://prove2.me/submissions/cddb4433-087a-4cfe-b74e-5cb027854cc9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Measures_mul_mul_apply_mem_integer
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotent_symm
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_eq_one_of_mapsTo_box
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_pi_eq
import Theorems.Thm_GroundTheory_Automorphic_Measures_mem_box
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

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ GLnLocal.integralGL F n) :
    distribHaarChar F (LinearEquiv.det (adUnipotent p)) = 1 := by
  obtain ⟨h₁, h₂⟩ := (GLnLocal.mem_integralGL_iff F n).1 hp
  have hint : ∀ (q : blockUpper F n β),
      (∀ i j, ((q : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]) →
      (∀ i j, (((q : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]) →
      ∀ x ∈ box F (UnipotentIndex n β),
        unipotentCoord F n β (adUnipotent q ((unipotentCoord F n β).symm x)) ∈
          box F (UnipotentIndex n β) := by
    intro q hq hq' x hx
    refine mem_box.2 fun s => ?_
    show ((adUnipotent q ((unipotentCoord F n β).symm x) : lieUnipotent F n β) :
      Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 ∈ 𝒪[F]
    rw [coe_adUnipotent]
    refine mul_mul_apply_mem_integer hq (fun i j => ?_) hq' _ _
    show (if h : β i < β j then x ⟨(i, j), h⟩ else 0) ∈ 𝒪[F]
    split_ifs
    · exact mem_box.1 hx _
    · exact Subring.zero_mem _
  rw [← LinearEquiv.det_conj (adUnipotent p) (unipotentCoord F n β), ← distribHaarChar_pi_eq]
  refine distribHaarChar_eq_one_of_mapsTo_box (fun x hx => hint p h₁ h₂ x hx) fun x hx => ?_
  show unipotentCoord F n β ((adUnipotent p).symm ((unipotentCoord F n β).symm x)) ∈ _
  rw [adUnipotent_symm]
  refine hint p⁻¹ (fun i j => ?_) (fun i j => ?_) x hx
  · simpa using h₂ i j
  · simpa using h₁ i j
end GroundTheory.Automorphic.Measures
