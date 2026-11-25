-- Prove2me | solution 1 for GlobalTheory.minorHarm_pderiv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:13.340703+00:00
-- url     : https://prove2.me/submissions/6708ba74-89f8-4b23-91ff-7fa5dd0af402

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
open MvPowerSeries
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) {v : σ} (hv : v ∉ S) :
    MvPolynomial.pderiv v p = 0 := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact MvPolynomial.pderiv_X_of_ne (fun h => hv (h ▸ hs))
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [MvPolynomial.pderiv_mul, hx, hy]; simp
end _root_.GlobalTheory
end GlobalTheory
