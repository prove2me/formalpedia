-- Prove2me | solution 1 for GlobalTheory.TraceAeval.exists_int_trace_aeval_eq_sum_aroots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:39.281475+00:00
-- url     : https://prove2.me/submissions/159cf80b-f065-42ad-9a87-38e6e15b4a1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq
import Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_map
import Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_int
import Theorems.Thm_GlobalTheory_TraceAeval_powMat_map
import Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_powMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceAeval
open Module
namespace GlobalTheory.TraceAeval
theorem _root_.solution :
    ∀ (χ p : Polynomial ℤ), χ.Monic → ∃ s : ℤ, (s : ℂ) = ((χ.aroots ℂ).map fun z => Polynomial.aeval z p).sum ∧ ∀ (n M : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod M)), B.charpoly = χ.map (Int.castRingHom (ZMod M)) → (Polynomial.aeval B p).trace = (s : ZMod M) := by
  intro χ p hχ
  refine ⟨(aeval (powMat χ.natDegree χ) p).trace, trace_aeval_powMat hχ p, ?_⟩
  intro n M B hB
  rcases subsingleton_or_nontrivial (ZMod M) with hM | hM
  · exact Subsingleton.elim _ _
  have hn : χ.natDegree = n := by
    rw [← hχ.natDegree_map (Int.castRingHom (ZMod M)), ← hB, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  choose B₀ hB₀ using fun i j => ZMod.intCast_surjective (B i j)
  have hBB : (Matrix.of B₀).map (Int.castRingHom (ZMod M)) = B := by
    ext i j; simpa using hB₀ i j
  set A : Matrix (Fin n) (Fin n) ℤ := Matrix.of B₀
  have hA : A.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h1 : (aeval A p).trace = (aeval (powMat n A.charpoly) p).trace := by
    have h2 := trace_aeval_powMat A.charpoly_monic p
    rw [hA] at h2
    apply Int.cast_injective (α := ℂ)
    rw [h2, trace_aeval_int, Matrix.charpoly_map]
    rfl
  rw [← hBB, trace_aeval_map, h1, hn, ← trace_aeval_map, ← trace_aeval_map,
    powMat_map _ _ hχ, powMat_map _ _ A.charpoly_monic, ← Matrix.charpoly_map, hBB, hB]
end GlobalTheory.TraceAeval
