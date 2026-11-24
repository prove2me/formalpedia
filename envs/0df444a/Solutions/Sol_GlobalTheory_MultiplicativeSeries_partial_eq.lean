-- Prove2me | solution 1 for GlobalTheory.MultiplicativeSeries.partial_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:22:51.235862+00:00
-- url     : https://prove2.me/submissions/bd84f0c9-c0d4-4f13-b037-cf9f518bbedc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvSelfTwo
import Theorems.Thm_GlobalTheory_MultiplicativeSeries_ev_mul
import Theorems.Thm_GlobalTheory_MultiplicativeSeries_ev_sum
import Theorems.Thm_GlobalTheory_MultiplicativeSeries_ev_self_one
import Theorems.Thm_GlobalTheory_MultiplicativeSeries_ev_self_two
import Theorems.Thm_GlobalTheory_MultiplicativeSeries_axis_law
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_pderiv
import Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_pt_zero
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_axis
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_ev_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_ev
import Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_pt
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
theorem _root_.solution (G : FGLaw R d) (s : PS R 1 d)
    (h : ev (n := 2) ![G.add (pt R d 0) (pt R d 1)] s =
      ev (n := 2) ![pt R d 0] s * ev (n := 2) ![pt R d 1] s) (i : Fin d) :
    ∑ j, ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F j)) *
        pderiv R ((0 : Fin 1), j) s =
      C (coeff (Finsupp.single ((0 : Fin 1), i) 1) s) * s := by
  have hadd : G.add (pt R (n := 2) d 0) (pt R d 1) = G.F := funext fun j => ev_self_two _
  rw [hadd] at h
  have h0 : pderiv R ((1 : Fin 2), i) (ev (n := 2) ![pt R d 0] s) = 0 := by
    rw [pderiv_ev (const_one (const_pt 0))]
    simp [pderiv_pt]
  have h1 : pderiv R ((1 : Fin 2), i) (ev (n := 2) ![pt R d 1] s) =
      ev (n := 2) ![pt R d 1] (pderiv R ((0 : Fin 1), i) s) := by
    rw [pderiv_ev (const_one (const_pt 1))]
    simp [pderiv_pt]
  have hd := congrArg (fun f => ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) f)) h
  beta_reduce at hd
  rw [Derivation.leibniz, h0, h1, smul_zero, add_zero, smul_eq_mul, ev_mul const_axis,
    axis_pderiv, ev_ev_one (const_pt 0) const_axis, axis_pt_zero, ev_self_one,
    pderiv_ev (const_one G.const), Fin.sum_univ_one, ev_sum const_axis] at hd
  rw [mul_comm, ← hd]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_mul const_axis, ev_ev_one G.const const_axis, axis_law, ev_self_one, mul_comm]
  rfl
end GlobalTheory.MultiplicativeSeries
