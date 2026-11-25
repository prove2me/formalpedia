-- Prove2me | solution 1 for GlobalTheory.HeisLine.admitted.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:46:24.498515+00:00
-- url     : https://prove2.me/submissions/1f8d7022-fdfb-4463-b386-586ab23c1631

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AddCharDotProductTrivialOnTsupportNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.HeisLine
open GlobalTheory.SplitWeil.FourierPi
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]
variable [MeasurableSpace k] [BorelSpace k]
variable {χ : AddChar k Circle} {c : kˣ}
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.HeisLine
namespace admitted
theorem _root_.solution {s s' : kˣ} {g : (n → k) → ℂ} (h : admitted χ s g) (hs : box n s' ⊆ box n s) : admitted χ s' g :=
  fun η hη t ht => h η hη t (hs ht)
end admitted
end GlobalTheory.HeisLine
