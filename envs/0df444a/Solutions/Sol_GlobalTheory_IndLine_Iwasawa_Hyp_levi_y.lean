-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Hyp.levi_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:32.261935+00:00
-- url     : https://prove2.me/submissions/a0f29509-bb16-4875-8394-1f1d277eec93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_prY_mulVec
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_qy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}
open GlobalTheory.IndLine.Iwasawa.Hyp
variable (h : Hyp c J x y ι ι')
include h
namespace GlobalTheory.IndLine.Iwasawa.Hyp
theorem _root_.solution {g : Matrix m m A} (hq : g * prY c J x y = prY c J x y * g)
    (hu : gᵀ * J * g.map c = J) {t : Aˣ} (ht : (t : A) = (g *ᵥ x) ⬝ᵥ J *ᵥ (c ∘ y)) : g *ᵥ y = c (t⁻¹).1 • y := by
  have e : g *ᵥ y = -((g *ᵥ y) ⬝ᵥ J *ᵥ (c ∘ x)) • y := by
    rw [← prY_mulVec (y := y), Matrix.mulVec_mulVec, ← hq, ← Matrix.mulVec_mulVec, h.qy]
  set μ := -((g *ᵥ y) ⬝ᵥ J *ᵥ (c ∘ x))
  have e1 : (g *ᵥ x) ⬝ᵥ J *ᵥ (c ∘ (g *ᵥ y)) = 1 := by
    have : c ∘ (g *ᵥ y) = g.map c *ᵥ (c ∘ y) := by
      funext i; exact RingHom.map_mulVec c g y i
    rw [this, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hu, h.xy]
  have e2 : c ∘ (μ • y) = c μ • (c ∘ y) := by
    funext i; simp
  rw [e, e2, Matrix.mulVec_smul, dotProduct_smul, ← ht, smul_eq_mul, mul_comm] at e1
  rw [Units.inv_eq_of_mul_eq_one_right e1, h.cc]
  exact e
end GlobalTheory.IndLine.Iwasawa.Hyp
