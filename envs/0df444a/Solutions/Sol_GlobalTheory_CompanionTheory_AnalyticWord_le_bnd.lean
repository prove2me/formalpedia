-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.le_bnd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:42.307829+00:00
-- url     : https://prove2.me/submissions/795adf52-5b6b-4b08-bbaa-b10c02c35b1d

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
theorem _root_.solution {l : List ι} {k : ℕ} (hl : l.length = k) (e : Fin m) :
    ‖j (word Z l (y e))‖ ≤ bnd j Z y k := by
  have hmem : (l, e) ∈ (List.finite_length_eq ι k).toFinset ×ˢ (univ : Finset (Fin m)) := by
    simp [hl]
  have h := Finset.le_sup (f := fun p : List ι × Fin m => ‖j (GlobalTheory.CompanionTheory.AnalyticWord.word Z p.1 (y p.2))‖₊) hmem
  unfold GlobalTheory.CompanionTheory.AnalyticWord.bnd
  exact (coe_nnnorm _).symm.trans_le (NNReal.coe_le_coe.2 h)
end GlobalTheory.CompanionTheory.AnalyticWord
