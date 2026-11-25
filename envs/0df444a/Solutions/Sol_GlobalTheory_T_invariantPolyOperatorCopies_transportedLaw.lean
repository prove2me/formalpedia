-- Prove2me | solution 1 for GlobalTheory.T.invariantPolyOperatorCopies_transportedLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:55.173373+00:00
-- url     : https://prove2.me/submissions/6a20a510-aeb4-4de3-a963-394f631e8edf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantPolyOperatorCopiesTransportedLaw
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantPolyOperatorCopiesTransportedLawStatement
import Theorems.Thm_GlobalTheory_ChartTransN_dpolyN_transF
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [CommRing k] (d n : ℕ) (G : FGLaw k d) (φ φi : Pt k 1 d), IsInvPair φ φi → ∀ (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (g : PS k n d), DpolyN (transF G.F φ φi) cp u P (ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) g) = ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) (DpolyN G.F cp (fun l => (dLin φ).mulVec (u l)) P g) := by
  first | exact @GlobalTheory.ChartTransN.dpolyN_transF | exact GlobalTheory.ChartTransN.dpolyN_transF | (intros; apply GlobalTheory.ChartTransN.dpolyN_transF <;> assumption)
end _root_.GlobalTheory.T
