-- Prove2me | solution 1 for GlobalTheory.Survey.UnimodularStandardLattice.unimod_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:14:10.973407+00:00
-- url     : https://prove2.me/submissions/baceaabb-5cb6-4278-8e51-0ea3af300b08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ThetaSpanAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_UnimodularStandardLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Survey.UnimodularStandardLattice
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma mem_range_algebraMap_iff_isIntegral_int (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩
set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma complexConj_mem_integers_iff (x : E) :
    IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range ↔
      x ∈ (algebraMap (𝓞 E) E).range := by
  rw [mem_range_algebraMap_iff_isIntegral_int, mem_range_algebraMap_iff_isIntegral_int]
  refine ⟨fun h => ?_, fun h => h.map (IsCMField.complexConj E)⟩
  simpa using h.map (IsCMField.complexConj E).symm
variable {H : Host E} {Dw : Datum H} {l : Level H}
end GlobalTheory.Survey.UnimodularStandardLattice
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.UnimodularStandardLattice
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
set_option autoImplicit false
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.Survey.UnimodularStandardLattice
namespace _root_.GlobalTheory.Survey.UnimodularStandardLattice
theorem _root_.solution :
    (⟨_root_.Formalism.L2.Pj.stdLat E n⟩ : _root_.Formalism.L2.Pj.GenLat E n).Unimod := by
  unfold _root_.Formalism.L2.Pj.GenLat.Unimod _root_.Formalism.L2.Pj.stdLat
  intro v
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    ← RingHom.mem_range]
  constructor
  · intro hv w hw
    exact Subring.sum_mem _ fun j _ =>
      Subring.mul_mem _ ((complexConj_mem_integers_iff (v j)).2 (hv j)) (hw j)
  · intro h i
    have hs := h (Pi.single i 1) fun j => by
      rw [Pi.single_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hs
    exact (complexConj_mem_integers_iff (v i)).1 hs
end _root_.GlobalTheory.Survey.UnimodularStandardLattice
end GlobalTheory.Survey.UnimodularStandardLattice
