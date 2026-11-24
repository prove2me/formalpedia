-- Prove2me | solution 1 for GlobalTheory.FormalLog.logDerivSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:29:21.916712+00:00
-- url     : https://prove2.me/submissions/81c7a486-d8a3-4431-8061-694c552af1c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Theorems.Thm_GlobalTheory_FormalLog_d_evY
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_second_ev_first_point_eq_zero
import Theorems.Thm_GlobalTheory_FormalLog_addPt
import Theorems.Thm_GlobalTheory_FormalLog_ez_y
import Theorems.Thm_GlobalTheory_FormalLog_CZ_cons
import Theorems.Thm_GlobalTheory_FormalLog_CZ_nil
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_cz1
import Theorems.Thm_GlobalTheory_FormalLog_d_evF
import Theorems.Thm_GlobalTheory_FormalLog_ev_C
import Theorems.Thm_GlobalTheory_FormalLog_ev_mul
import Theorems.Thm_GlobalTheory_FormalLog_ev_sum
import Theorems.Thm_GlobalTheory_FormalLog_ez_F
import Theorems.Thm_GlobalTheory_FormalLog_ez_dy
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_ev


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
variable [Algebra ℚ k]
namespace GlobalTheory.FormalLog
theorem _root_.solution : LogDerivSt := by
  intro k _ _ d G ℓ h0 h1 hadd u g
  have hℓ : CZ (![ℓ] : Fin 1 → Pt k 1 d) := CZ.cons h0 CZ.nil
  have hadd' : ∀ c, ev (n := 2) ![G.F] (ℓ c) = ev (n := 2) ![pt k d 0] (ℓ c) + ev (n := 2) ![pt k d 1] (ℓ c) := by
    intro c
    have := congrFun hadd c
    change ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (ℓ c) = _ at this
    rwa [addPt] at this
  have DJ : ∀ c b, ∑ j, pderiv k ((0 : Fin 1), j) (ℓ c) * Jac G j b = C (if c = b then 1 else 0) := by
    intro c b
    have h := congrArg (fun x => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) x)) (hadd' c)
    beta_reduce at h
    simp only [d_evF, map_add, pderiv_second_ev_first_point_eq_zero, d_evY, zero_add, ev_sum cz1, ev_mul cz1, ez_F, ez_dy, ez_y] at h
    rw [h]
    congr 1
    have hc := congrFun (congrFun h1 c) b
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
    simp only [dLin] at hc
    simp [hc, Matrix.one_apply]
  have hch : ∀ j, pderiv k ((0 : Fin 1), j) (ev (n := 1) ![ℓ] g) =
      ∑ c, ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) * pderiv k ((0 : Fin 1), j) (ℓ c) := by
    intro j
    rw [pderiv_ev hℓ, Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  have step : ∀ c, ∑ i, C (u i) * ∑ j, pderiv k ((0 : Fin 1), j) (ℓ c) * Jac G j i = (C (u c) : PS k 1 d) := by
    intro c
    simp only [DJ, ← map_mul, mul_ite, mul_one, mul_zero]
    rw [← map_sum]
    simp [Finset.sum_ite_eq]
  show ∑ j : Fin d, (∑ i : Fin d, C (u i) * Jac G j i) * pderiv k ((0 : Fin 1), j) (ev (n := 1) ![ℓ] g) = _
  simp only [hch]
  rw [ev_sum hℓ]
  calc ∑ j, (∑ i, C (u i) * Jac G j i) *
        ∑ c, ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) * pderiv k ((0 : Fin 1), j) (ℓ c)
      = ∑ j, ∑ c, ∑ i, C (u i) * Jac G j i *
          (ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) * pderiv k ((0 : Fin 1), j) (ℓ c)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum, Finset.sum_comm]
    _ = ∑ c, ∑ j, ∑ i, C (u i) * Jac G j i *
          (ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) * pderiv k ((0 : Fin 1), j) (ℓ c)) := Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ j, C (u i) * Jac G j i *
          (ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) * pderiv k ((0 : Fin 1), j) (ℓ c)) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) *
          ∑ i, C (u i) * ∑ j, pderiv k ((0 : Fin 1), j) (ℓ c) * Jac G j i := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [step, ev_mul hℓ, ev_C hℓ, mul_comm]
end GlobalTheory.FormalLog
