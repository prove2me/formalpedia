-- Prove2me | solution 1 for GlobalTheory.quasiIsoAt_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:04.400197+00:00
-- url     : https://prove2.me/submissions/b034e405-89d1-498c-bcd3-c27cf028ea2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Theorems.Thm_GlobalTheory_shortComplex_quasiIso_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) (p : ℕ) :
    QuasiIsoAt φ (p + 1) ↔
      (∀ y : C.X (p + 1), (C.d (p + 1) (p + 2)).hom y = 0 →
        ∃ (x : K.X (p + 1)) (z : C.X p), (K.d (p + 1) (p + 2)).hom x = 0 ∧
          (C.d p (p + 1)).hom z + (φ.f (p + 1)).hom x = y) ∧
      (∀ (x : K.X (p + 1)) (z : C.X p), (K.d (p + 1) (p + 2)).hom x = 0 →
        (C.d p (p + 1)).hom z = (φ.f (p + 1)).hom x → ∃ w : K.X p, (K.d p (p + 1)).hom w = x) := by
  rw [quasiIsoAt_iff' φ p (p + 1) (p + 2) (by simp) (by simp), shortComplex_quasiIso_iff]
  rfl
end GlobalTheory
