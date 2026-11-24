-- Prove2me | solution 1 for GlobalTheory.SW.exists_nearly_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:27:42.160318+00:00
-- url     : https://prove2.me/submissions/fcdf99cd-00fb-4a1d-8c55-b8fb0d815fe3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_reduce
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_approx
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_den
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_rows
import Theorems.Thm_GlobalTheory_SW_NearPrim_integral_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
open NearPrim
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (m : Type) [Fintype m] (W : Matrix (Fin k) m E), IntM W → LinearIndependent E (fun i => W i) → ∃ a : Matrix (Fin k) (Fin k) E, a.det ≠ 0 ∧ (∀ (τ : E →+* ℂ) i j, ‖τ (a i j)‖ ≤ C) ∧ IntM (a * W) ∧ ∀ t : Fin k → E, (∀ j, IsIntegral ℤ ((t ᵥ* (a * W)) j)) → ∀ i, IsIntegral ℤ ((c : E) * t i) := by
  intro E _ _ _ k
  obtain ⟨C, hC⟩ := exists_reduce E
  obtain ⟨M, hM⟩ := exists_approx E
  refine ⟨M.factorial ^ k, max 1 C, pow_pos M.factorial_pos _, fun m _ W hW hind => ?_⟩
  obtain ⟨d, hd, hden⟩ := exists_den W hind
  let L : AddSubgroup (Fin k → E) :=
    { carrier := {s | ∀ j, IsIntegral ℤ ((s ᵥ* W) j)}
      add_mem' := fun {s t} hs ht j => by rw [add_vecMul]; exact (hs j).add (ht j)
      zero_mem' := fun j => by rw [zero_vecMul]; exact isIntegral_zero
      neg_mem' := fun {s} hs j => by rw [neg_vecMul]; exact (hs j).neg }
  have hO : ∀ s : Fin k → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L := fun s hs j =>
    IsIntegral.sum (s := Finset.univ) (fun i => s i * W i j) fun i _ => (hs i).mul (hW i j)
  have hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L := fun y hy s hs j => by
    rw [smul_vecMul]; exact hy.mul (hs j)
  choose a haL ha0 hai haC hmin using exists_rows L hO d hd hden C hC
  refine ⟨Matrix.of a, ?_, fun τ i j => (canonicalEmbedding.norm_le_iff _ _).1 (haC i j) τ,
    fun i j => haL i j, fun t ht => ?_⟩
  · rw [Matrix.det_of_lowerTriangular (Matrix.of a) (fun i j h => ha0 i j h)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hai i
  · refine integral_coord L hsm M hM (Matrix.of a) haL ha0 hai hmin k le_rfl t
      (fun j hj => absurd j.2 (not_lt.2 hj)) fun j => ?_
    rw [vecMul_vecMul]
    exact ht j
end GlobalTheory.SW
