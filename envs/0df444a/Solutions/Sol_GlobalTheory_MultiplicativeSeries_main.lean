-- Prove2me | solution 1 for GlobalTheory.MultiplicativeSeries.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:19.133642+00:00
-- url     : https://prove2.me/submissions/378a2257-3c64-4765-94bc-444fb0473a34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvSelfTwo
import Theorems.Thm_GlobalTheory_MultiplicativeSeries_partial_eq
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.MultiplicativeSeries
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ}
namespace GlobalTheory.MultiplicativeSeries
theorem _root_.solution :
  (∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (s : PS R 1 d),
    ev (n := 2) ![G.add (pt R d 0) (pt R d 1)] s = ev (n := 2) ![pt R d 0] s * ev (n := 2) ![pt R d 1] s →
    ∀ u : Fin d → R, Dof G.F u s = C (∑ i, u i * coeff (Finsupp.single ((0 : Fin 1), i) 1) s) * s) := by
  intro R _ d G s h u
  rw [Dof, map_sum, Finset.sum_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc, ← partial_eq G s h i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
end GlobalTheory.MultiplicativeSeries
