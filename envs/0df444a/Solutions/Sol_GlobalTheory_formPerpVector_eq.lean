-- Prove2me | solution 1 for GlobalTheory.formPerpVector_eq
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:35:13.01869+00:00
-- url     : https://prove2.me/submissions/e7175d6c-d73d-4ec6-ae4c-824a9f26dec8

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {σ : R →+* R}
theorem _root_.solution (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (g : M) :
    formPerpVector h e e' g = (formPairMatrix h e e').det • g
      - ∑ a, ∑ a', ((formPairMatrix h e e').adjugate a a' * h g (e a)) • e' a' := by
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
  trace "HIT_15_2"

