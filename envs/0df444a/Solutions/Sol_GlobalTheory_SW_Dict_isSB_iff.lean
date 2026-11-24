-- Prove2me | solution 1 for GlobalTheory.SW.Dict.isSB_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:42.238094+00:00
-- url     : https://prove2.me/submissions/79f2dcf8-ac59-4918-b444-81f30472641e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Theorems.Thm_GlobalTheory_SW_Dict_isSB_comp
import Theorems.Thm_GlobalTheory_SW_Dict_exists_den_ofQ
import Theorems.Thm_GlobalTheory_SW_Dict_exists_den_symm

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.Dict
namespace _root_.GlobalTheory.SW.Dict
theorem _root_.solution (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    _root_.GlobalTheory.SW.IsSB φ ↔
      _root_.GlobalTheory.SW.IsSB (fun m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ =>
        φ (_root_.GlobalTheory.SW.ofQ m)) := by
  obtain ⟨D, hD, h1⟩ := _root_.GlobalTheory.SW.Dict.exists_den_ofQ (E := E) (n := n) (N := N)
  obtain ⟨D', hD', h2⟩ := _root_.GlobalTheory.SW.Dict.exists_den_symm (E := E) (n := n) (N := N)
  constructor
  · intro h
    refine _root_.GlobalTheory.SW.Dict.isSB_comp
      (_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).toAddMonoidHom D D' hD hD' h1 (fun m hm => ?_) h
    simpa using h2 _ hm
  · intro h
    have := _root_.GlobalTheory.SW.Dict.isSB_comp
      (_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).symm.toAddMonoidHom D' D hD' hD h2
      (fun x hx => by simpa using h1 _ hx) h
    convert this using 2 with x
    exact congrArg φ ((_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).apply_symm_apply x).symm
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
