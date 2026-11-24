-- Prove2me | solution 1 for GlobalTheory.nsmul_some_map_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:11.885118+00:00
-- url     : https://prove2.me/submissions/b4e9f670-10f2-4681-840c-862343e54f33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TorsionPointTransportEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve
namespace GlobalTheory
theorem _root_.solution {F K : Type} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    (i : F →+* K) (W : WeierstrassCurve F) (x y : F) (N : ℕ)
    (h₀ : W.toAffine.Nonsingular x y) (h : (W.map i).toAffine.Nonsingular (i x) (i y)) :
    N • (Affine.Point.some (i x) (i y) h) = 0 ↔ N • (Affine.Point.some x y h₀) = 0 := by
  letI : Algebra F K := i.toAlgebra
  let φ : W.toAffine.Point →+ (W.map i).toAffine.Point :=
    Affine.Point.map (W' := W.toAffine) (Algebra.ofId F K)
  have hφ : Function.Injective φ := Affine.Point.map_injective (W' := W.toAffine) (Algebra.ofId F K)
  have e : φ (Affine.Point.some x y h₀) = Affine.Point.some (i x) (i y) h := rfl
  rw [← e, ← map_nsmul, map_eq_zero_iff φ hφ]
end GlobalTheory
