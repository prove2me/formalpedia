-- Prove2me | solution 1 for GlobalTheory.torsion_point_transport_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:43:27.561929+00:00
-- url     : https://prove2.me/submissions/0c7a8741-e521-4c20-bca9-9f4c55c0eace

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TorsionPointTransportEmbedding
import Theorems.Thm_GlobalTheory_nsmul_some_map_eq_zero_iff

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
theorem _root_.solution :
    ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [DecidableEq K] [DecidableEq K'] (i : F →+* K) (j : F →+* K') (A B x y : F) (N : ℕ) (h : (⟨0, 0, 0, i A, i B⟩ : WeierstrassCurve K).toAffine.Nonsingular (i x) (i y)), N • (WeierstrassCurve.Affine.Point.some (i x) (i y) h) = 0 → ∃ h' : (⟨0, 0, 0, j A, j B⟩ : WeierstrassCurve K').toAffine.Nonsingular (j x) (j y), N • (WeierstrassCurve.Affine.Point.some (j x) (j y) h') = 0 := by
  intro F K K' _ _ _ _ _ i j A B x y N
  classical
  let W : WeierstrassCurve F := ⟨0, 0, 0, A, B⟩
  have ei : (⟨0, 0, 0, i A, i B⟩ : WeierstrassCurve K) = W.map i := by
    ext <;> simp [W, WeierstrassCurve.map]
  have ej : (⟨0, 0, 0, j A, j B⟩ : WeierstrassCurve K') = W.map j := by
    ext <;> simp [W, WeierstrassCurve.map]
  rw [ei, ej]
  intro h hN
  have h₀ : W.toAffine.Nonsingular x y := (W.toAffine.map_nonsingular i.injective x y).mp h
  have h' : (W.map j).toAffine.Nonsingular (j x) (j y) :=
    (W.toAffine.map_nonsingular j.injective x y).mpr h₀
  exact ⟨h', (nsmul_some_map_eq_zero_iff j W x y N h₀ h').mpr
    ((nsmul_some_map_eq_zero_iff i W x y N h₀ h).mp hN)⟩
end GlobalTheory
