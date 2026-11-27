-- Prove2me | solution 1 for GlobalTheory.ArcInTest.nonempty_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:44.336689+00:00
-- url     : https://prove2.me/submissions/01f510d1-50a9-41e7-8236-1e26faf34192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_MemOfPowEqInt
import Theorems.Thm_GlobalTheory_ArcInTest_int_ne_rt

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
theorem _root_.solution (D : Datum H) (c : Coeff l) :
    Nonempty (ArcIn D l (Int.castRingHom c.F) c.F (Int.castRingHom c.F)) :=
  let a := GlobalTheory.HostModel.arcIn c c.F (RingHom.id _)
  ⟨{ D₀ := a.D₀, mod := a.mod, oa := a.oa, nontriv := a.nontriv, even := a.even, bimult := a.bimult, gen := a.gen
     w0 := a.w0, be := a.be, be_symm := a.be_symm, be_pos := a.be_pos, be_adj := a.be_adj, be_dvd := a.be_dvd
     eta := fun _ => a.eta 0, etaA := fun _ => a.etaA 0
     geom := fun _ _ _ _ r _ hr => absurd hr (int_ne_rt c r) }⟩
end GlobalTheory.ArcInTest
