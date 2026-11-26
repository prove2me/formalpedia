-- Prove2me | solution 1 for GlobalTheory.powGr.map_mk
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:14.306574+00:00
-- url     : https://prove2.me/submissions/78dbda59-add3-4013-ae72-be12f6697d5e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R]
open GlobalTheory.powGr
variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ)
variable {I M a}
theorem _root_.solution {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (x : ↥(I ^ a • ⊤ : Submodule R M)) :
    map I a g (mk I M a x) =
      mk I N a ⟨g x, Submodule.smul_top_le_comap_smul_top (I ^ a) g x.2⟩ := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_63_7"

