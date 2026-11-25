-- Prove2me | solution 1 for GroundTheory.Global.exists_algEquiv_apply_eq_of_minpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:51.2274+00:00
-- url     : https://prove2.me/submissions/7285cb71-2c26-4e20-8ae6-f39b151abfaf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed
import Theorems.Thm_GroundTheory_Global_IsTranscendenceBasis_extendScalars_of_isAlgebraic
import Theorems.Thm_GroundTheory_Global_exists_ringEquiv_extend_of_isTranscendenceBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]
namespace GroundTheory.Global
theorem _root_.solution {x y : Ω} (hx : IsAlgebraic F x)
    (h : minpoly F x = minpoly F y) : ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by
  have hy : IsAlgebraic F y := ⟨minpoly F x, minpoly.ne_zero hx.isIntegral, h ▸ minpoly.aeval _ _⟩
  have := isAlgebraic_adjoin_simple hx.isIntegral
  have := isAlgebraic_adjoin_simple hy.isIntegral
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F Ω
  obtain ⟨σ, hσ, -⟩ := exists_ringEquiv_extend_of_isTranscendenceBasis
    (minpoly.algEquiv hx h).toRingEquiv
    (IsTranscendenceBasis.extendScalars_of_isAlgebraic (E := F⟮x⟯) hs)
    (IsTranscendenceBasis.extendScalars_of_isAlgebraic (E := F⟮y⟯) hs) (Equiv.refl s)
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun a => ?_, ?_⟩
  · have h1 := hσ (algebraMap F F⟮x⟯ a)
    rw [AlgEquiv.coe_ringEquiv, AlgEquiv.commutes] at h1
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
  · have := hσ (AdjoinSimple.gen F x)
    rw [AlgEquiv.coe_ringEquiv, minpoly.algEquiv_apply] at this
    simpa using this
end GroundTheory.Global
