-- Prove2me | solution 1 for GlobalTheory.ClassSumProbe.finite_conj_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:11.928797+00:00
-- url     : https://prove2.me/submissions/b00519a2-922b-452e-9ec4-b3ba347854e6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_TransformIndicator
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
namespace GlobalTheory.ClassSumProbe
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
set_option autoImplicit false in
open NumberField MvPolynomial in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
private theorem mfr_ne_bot : _root_.Formalism.L2.Pj.Mfr l ≠ ⊥ := by
  intro h
  have hM := l.prod
  have h3 := l.three_le
  unfold _root_.Formalism.L2.Pj.Mfr at h
  rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hM
  exact absurd (Nat.cast_eq_zero.mp hM) (by omega)
end GlobalTheory.ClassSumProbe
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassSumProbe
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
set_option autoImplicit false
open NumberField MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
namespace GlobalTheory.ClassSumProbe
namespace _root_.GlobalTheory.ClassSumProbe
theorem _root_.solution :
    Finite (Dw.La ⧸ (_root_.Formalism.L2.Pj.Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) := by
  haveI := Dw.fin
  haveI : Finite (𝓞 E ⧸ _root_.Formalism.L2.Pj.Mfr l) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ mfr_ne_bot
  exact Module.finite_of_finite (𝓞 E ⧸ _root_.Formalism.L2.Pj.Mfr l)
end _root_.GlobalTheory.ClassSumProbe
end GlobalTheory.ClassSumProbe
