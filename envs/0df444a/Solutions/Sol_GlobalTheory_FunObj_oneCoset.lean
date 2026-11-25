-- Prove2me | solution 1 for GlobalTheory.FunObj.oneCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:31.938977+00:00
-- url     : https://prove2.me/submissions/566f436b-94b2-4307-99fe-ae70d4ecf6a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_oneCoset_of_isTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip
namespace GlobalTheory.FunObj
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {G : Grid k} (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] (J : G.Level) (T : G.Args → ℂ) (ϖ : kˣ) (e : ℕ) :
    Even G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T →
      (∀ j, 0 < j → j < G.m → J (G.m, j) = KO k _) → OneCoset hs ψ ν J T ϖ e := by
  intro _ _ hψ hT hJ
  exact OneCosetProof.oneCoset_of_isTensor hs hψ hT hJ
end GlobalTheory.FunObj
