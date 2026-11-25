-- Prove2me | solution 1 for GlobalTheory.ArcInTest.rank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:44.256475+00:00
-- url     : https://prove2.me/submissions/45549717-ce71-449e-8427-2955a4113186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_MemOfPowEqInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArcInTest
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
namespace GlobalTheory.ArcInTest
theorem _root_.solution {D : Datum H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) (r z : O) (hr : ((β r : c.F) : ℂ) = H.rt0)
    (hz : ((β z : c.F) : ℂ) = zeta l.A) (τ : 𝓞 E →+* AlgebraicClosure (FractionRing O')) :
    Module.finrank (𝓞 E) a.D₀.X ≤ max D.p D.q := by
  obtain ⟨h, -⟩ := a.geom (AlgebraicClosure (FractionRing O')) r z hr hz _ rfl
  obtain ⟨n, -, hn⟩ := h τ
  split_ifs at hn <;> omega
end GlobalTheory.ArcInTest
