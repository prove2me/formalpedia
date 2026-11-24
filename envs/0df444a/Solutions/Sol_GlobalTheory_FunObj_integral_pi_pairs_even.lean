-- Prove2me | solution 1 for GlobalTheory.FunObj.integral_pi_pairs_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:10:01.630814+00:00
-- url     : https://prove2.me/submissions/4ba4df5c-e29c-40d0-892e-2b5fe13a9d53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_FunObj_integral_pi_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
namespace GlobalTheory.FunObj
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) (he : Even m) (E : ℕ → Type) [∀ j, MeasurableSpace (E j)]
    (μ : ∀ j, Measure (E j)) [∀ j, SigmaFinite (μ j)] (H : ∀ j : Fin (m - 2), E j → E (j + 1) → ℂ) (L : E (m - 2) → ℂ) :
    ∫ w : ∀ j : Fin (m - 1), E j, (∏ j : Fin (m - 2), if Even j.1 then H j (w ⟨j, by omega⟩) (w ⟨j + 1, by omega⟩) else 1) *
      L (w ⟨m - 2, by omega⟩) ∂(Measure.pi fun j : Fin (m - 1) => μ j) =
    (∏ j : Fin (m - 2), if Even j.1 then ∫ p : E j × E (j + 1), H j p.1 p.2 ∂((μ j).prod (μ (j + 1))) else 1) *
      ∫ u, L u ∂(μ (m - 2)) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = 2 * q + 2 := by
    obtain ⟨r, hr⟩ := he
    exact ⟨r - 1, by omega⟩
  exact integral_pi_pairs q E μ H L
end GlobalTheory.FunObj
