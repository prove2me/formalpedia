-- Prove2me | solution 1 for GlobalTheory.MultiplicativeSeries.ev_self_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:36.027054+00:00
-- url     : https://prove2.me/submissions/0fa67389-2c2e-45db-8d7c-a15840706f53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvSelfTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.MultiplicativeSeries
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ}
namespace GlobalTheory.MultiplicativeSeries
theorem _root_.solution (f : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] f = f := by
  have e : (fun q : Fin 2 × Fin d => (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) q.1 q.2) = X := by
    funext q
    obtain ⟨j, i⟩ := q
    fin_cases j <;> rfl
  rw [ev, e, subst_self]
  rfl
end GlobalTheory.MultiplicativeSeries
