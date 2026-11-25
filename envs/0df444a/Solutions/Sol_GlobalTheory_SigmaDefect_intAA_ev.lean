-- Prove2me | solution 1 for GlobalTheory.SigmaDefect.intAA_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:26:29.000976+00:00
-- url     : https://prove2.me/submissions/6e3152bf-f347-46f5-af89-aded17f16e89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Theorems.Thm_GlobalTheory_IntSeries_intAA_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.SigmaDefect
open GlobalTheory.QuadDeriv GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
omit [Algebra ℚ k]
namespace GlobalTheory.SigmaDefect
theorem _root_.solution {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j))
    (hai : ∀ j i, IntAA (R := R) k (a j i)) {f : PS k m d} (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (ev a f) :=
  intAA_subst (fun p => ha p.1 p.2) (fun p => hai p.1 p.2) hf
end GlobalTheory.SigmaDefect
