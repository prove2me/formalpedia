-- Prove2me | solution 1 for GlobalTheory.mem_identityComponents_of_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:56:07.693816+00:00
-- url     : https://prove2.me/submissions/4c8d68c6-2205-413e-92a5-af895f8fa6d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityComponentsSmoothGroupSchemeMulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvMemConnectedComponentInFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIdentityComponentsOfMulInv
import Theorems.Thm_GlobalTheory_identityComponent_shear_mul
import Theorems.Thm_GlobalTheory_T_identityComponents_smooth_groupScheme_mul_mem
import Theorems.Thm_GlobalTheory_T_inv_mem_identity_component_fibre


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (∀ z ∈ U, G.hom z = G.hom y → z ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G _ hs U y hU hy
  obtain ⟨w, hf, hm, rfl⟩ := hy
  have hbf : G.hom ((fst G G).left w) = G.hom ((snd G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w, Over.w]
  have hbm : G.hom ((μ[G]).left w) = G.hom ((snd G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w, Over.w]
  have zf := hU _ hf hbf
  have zm := hU _ hm hbm
  have zi := GlobalTheory.T.inv_mem_identity_component_fibre S G _ zf
  set φ : G ⊗ G ⟶ G ⊗ G := lift (fst G G ≫ ι[G]) μ[G] with hφ
  have e1 : (fst G G).left (φ.left w) = (ι[G]).left ((fst G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, hφ, lift_fst]
  have e2 : (snd G G).left (φ.left w) = (μ[G]).left w := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφ, lift_snd]
  have key := GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem S G hs (φ.left w) (e1 ▸ zi) (e2 ▸ zm)
  have e3 : (μ[G]).left (φ.left w) = (snd G G).left w := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφ, identityComponent_shear_mul]
  rwa [e3] at key
end GlobalTheory
