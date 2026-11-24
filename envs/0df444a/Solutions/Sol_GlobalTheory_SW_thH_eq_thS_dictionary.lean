-- Prove2me | solution 1 for GlobalTheory.SW.thH_eq_thS_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:57:13.199855+00:00
-- url     : https://prove2.me/submissions/f279d0c9-8d0d-4751-9af3-29dc00eef31c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Theorems.Thm_GlobalTheory_SW_Dict_isSB_iff
import Theorems.Thm_GlobalTheory_SW_Dict_thH_eq
import Theorems.Thm_GlobalTheory_SW_Dict_zetaOf_surj
import Theorems.Thm_GlobalTheory_SW_Dict_tauOf_mem

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
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
namespace _root_.GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ), Function.Bijective (_root_.GlobalTheory.SW.ofQ : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ → Matrix (Fin n) (Fin N) E) ∧ (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, _root_.GlobalTheory.SW.tauOf Ψ Z ∈ _root_.GlobalTheory.SW.Siegel (_root_.GlobalTheory.SW.QI E N)) ∧ (∀ ζ : Fin n → _root_.GlobalTheory.SW.QI E N → ℂ, ∃ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.zetaOf Ψ z z' = ζ) ∧ (∀ (φ : Matrix (Fin n) (Fin N) E → ℂ) Z z z', _root_.GlobalTheory.SW.thH Ψ φ Z z z' = _root_.GlobalTheory.SW.thS (fun m => φ (_root_.GlobalTheory.SW.ofQ m)) (_root_.GlobalTheory.SW.tauOf Ψ Z) (_root_.GlobalTheory.SW.zetaOf Ψ z z')) ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.IsSB φ ↔ _root_.GlobalTheory.SW.IsSB (fun m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ => φ (_root_.GlobalTheory.SW.ofQ m)) := by
  intro E _ _ _ Ψ hΨ n N
  exact ⟨(_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).bijective,
    fun Z hZ => _root_.GlobalTheory.SW.Dict.tauOf_mem hΨ Z hZ,
    fun ζ => _root_.GlobalTheory.SW.Dict.zetaOf_surj hΨ ζ,
    fun φ Z z z' => _root_.GlobalTheory.SW.Dict.thH_eq Ψ φ Z z z',
    fun φ => _root_.GlobalTheory.SW.Dict.isSB_iff φ⟩
end _root_.GlobalTheory.SW
