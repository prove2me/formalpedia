-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.proj_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:43:10.9836+00:00
-- url     : https://prove2.me/submissions/89c4fb43-c482-4c04-85dc-ecc1c270f737

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution {B' : Type} [CommRing B'] (f : B →+* B') (c : B →+* B) (c' : B' →+* B')
    (hf : ∀ x, f (c x) = c' (f x)) (J K : Matrix n n B) (h : B) (X : Matrix n n B) :
    (proj c J K h X).map f = proj c' (J.map f) (K.map f) (f h) (X.map f) := by
  have hs : ∀ (a : B) (M : Matrix n n B), (a • M).map f = f a • M.map f := by
    intro a M; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
  have hcc : (X.map c).map f = (X.map f).map c' := by ext i j; simp [hf]
  unfold proj tau
  rw [hs, show (X + -(J * X.map c * K)ᵀ).map f = X.map f + (-(J * X.map c * K)ᵀ).map f from
    map_add f.mapMatrix _ _, Matrix.map_neg _ (map_neg f), transpose_map, Matrix.map_mul, Matrix.map_mul, hcc]
end GlobalTheory.EisBL.NilAlg
