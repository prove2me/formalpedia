-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.bnd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:16.094541+00:00
-- url     : https://prove2.me/submissions/0eeba87e-f2d1-4d78-9b4e-cfbaeb21dd36

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
variable [Finite ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution {k : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ (l : List ι) (e : Fin m), l.length = k → ‖j (word Z l (y e))‖ ≤ B) :
    bnd j Z y k ≤ B := by
  unfold GlobalTheory.CompanionTheory.AnalyticWord.bnd
  have hs : ((List.finite_length_eq ι k).toFinset ×ˢ (univ : Finset (Fin m))).sup
      (fun p => ‖j (GlobalTheory.CompanionTheory.AnalyticWord.word Z p.1 (y p.2))‖₊) ≤ B.toNNReal := by
    refine Finset.sup_le fun p hp => ?_
    rw [Finset.mem_product, Set.Finite.mem_toFinset] at hp
    show ‖j (GlobalTheory.CompanionTheory.AnalyticWord.word Z p.1 (y p.2))‖₊ ≤ B.toNNReal
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hB]
    exact h p.1 p.2 hp.1
  calc _ ≤ ((B.toNNReal : NNReal) : ℝ) := NNReal.coe_le_coe.2 hs
    _ = B := Real.coe_toNNReal _ hB
end GlobalTheory.CompanionTheory.AnalyticWord
