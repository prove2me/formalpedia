-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Vf2.lag_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:47.743828+00:00
-- url     : https://prove2.me/submissions/277289a7-a3f1-4a06-bb0a-0adfef09798c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_SkewTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Vf2
open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] {c : A →ₐ[R] A} [Fintype β] [DecidableEq β] {J : Matrix β β A}
namespace GlobalTheory.ThK.Dbl.Vf2
theorem _root_.solution {b b' x y : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g : UG c (dbl J))
    (hg : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = fromRows x y) :
    (y + b * (y - x))ᵀ * J * (y - x).map c + (y - x)ᵀ * J * (y + b * (y - x)).map c = 0 := by
  have h1 : g.1.1ᵀ * dbl J * g.1.1.map c = dbl J := g.2
  have h2 : (fromRows x y)ᵀ * dbl J * (fromRows x y).map c = 0 := by
    rw [← hg, transpose_mul, mapc_mul]
    calc _ = (diagCols β : Matrix (β ⊕ β) β A)ᵀ * (g.1.1ᵀ * dbl J * g.1.1.map c) * (diagCols β : Matrix (β ⊕ β) β A).map c := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [h1]; simp [diagCols, dbl, fromRows_map, mapc_one, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  have e : b'.map c = -1 - b.map c := by
    rw [← mapc_one (c := c), ← mapc_neg, ← mapc_sub, ← hb]; congr 1; abel
  have b2 : bᵀ * J = -J - J * b.map c := by rw [b1, e]; noncomm_ring
  rw [transpose_fromRows, dbl, fromCols_mul_fromBlocks, fromRows_map, fromCols_mul_fromRows] at h2
  rw [transpose_add, transpose_mul, mapc_add, mapc_mul, mapc_sub, transpose_sub]
  linear_combination (norm := noncomm_ring) (yᵀ - xᵀ) * b2 * (y.map c - x.map c) - h2
end GlobalTheory.ThK.Dbl.Vf2
