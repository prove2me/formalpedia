-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.exists_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:32:04.443975+00:00
-- url     : https://prove2.me/submissions/58c9c7b6-b75e-4547-b270-2b54b4ba29ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_QuadraticZeta_eq_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {R : Type*} [CommRing R]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) {t n : ℤ}
    (hw : b 1 ^ 2 = t * b 1 - n) {S : Type*} [CommRing S] {β : S} (hβ : β ^ 2 = t * β - n) :
    ∃ φ : R →+* S, φ (b 1) = β := by
  let f : R →ₗ[ℤ] S := b.constr ℤ ![1, β]
  have hf : ∀ x y : ℤ, f (x + y * b 1) = x + y * β := by
    intro x y
    have : (x + y * b 1 : R) = x • b 0 + y • b 1 := by simp [h0]
    rw [this]
    rw [map_add, map_smul, map_smul]
    simp [f]
  refine ⟨(AlgHom.ofLinearMap f (by simpa using hf 1 0) fun x y => ?_).toRingHom,
    by simpa using hf 0 1⟩
  rw [eq_coord b h0 x, eq_coord b h0 y]
  generalize b.repr x 0 = x0, b.repr x 1 = x1, b.repr y 0 = y0, b.repr y 1 = y1
  rw [show (x0 + x1 * b 1 : R) * (y0 + y1 * b 1) = (x0 * y0 - x1 * y1 * n : ℤ)
      + (x0 * y1 + x1 * y0 + x1 * y1 * t : ℤ) * b 1 by
    push_cast; linear_combination (x1 * y1 : R) * hw, hf, hf, hf]
  push_cast
  linear_combination (-(x1 * y1) : S) * hβ
end GlobalTheory.QuadraticZeta
