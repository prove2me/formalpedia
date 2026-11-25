-- Prove2me | solution 1 for GlobalTheory.DerivEndo.dof_comp_endo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:17.173479+00:00
-- url     : https://prove2.me/submissions/b92b7af0-bed1-444b-b9f1-11ce2bb6b069

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
import Theorems.Thm_GlobalTheory_DerivEndo_noConst_one
import Theorems.Thm_GlobalTheory_DerivEndo_ev_mul
import Theorems.Thm_GlobalTheory_DerivEndo_ev_sum
import Theorems.Thm_GlobalTheory_DerivEndo_ev_C
import Theorems.Thm_GlobalTheory_DerivEndo_pderiv_ev
import Theorems.Thm_GlobalTheory_DerivEndo_jac_endo
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.DerivEndo
variable {R : Type} [CommRing R] {d : ℕ}
private theorem dof_eq_sum_C_mul_ev (F : Fin d → PS R 2 d) (u : Fin d → R) (g : PS R 1 d) :
    Dof F u g = ∑ j, (∑ i, C (u i) * ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (F j))) *
      pderiv R ((0 : Fin 1), j) g := by
  rfl
end GlobalTheory.DerivEndo
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.DerivEndo
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.DerivEndo
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (φ : Pt R 1 d),
    (∀ i, constantCoeff (φ i) = 0) →
    comp1 φ (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1)) →
    ∀ (u : Fin d → R) (f : PS R 1 d),
      Dof G.F u (ev (n := 1) ![φ] f) = ev (n := 1) ![φ] (Dof G.F ((dLin φ).mulVec u) f) := by
  intro R _ d G φ hφ hom u f
  have h1 : NoConst (![φ] : Fin 1 → Pt R 1 d) := noConst_one hφ
  rw [dof_eq_sum_C_mul_ev, dof_eq_sum_C_mul_ev, ev_sum h1]
  simp only [pderiv_ev h1, Fin.sum_univ_one, Matrix.cons_val_zero, ev_mul h1, ev_sum h1, ev_C,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have step : ∀ i, ∑ x, C (u i) * ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F x)) *
      (ev (n := 1) ![φ] (pderiv R ((0 : Fin 1), c) f) * pderiv R ((0 : Fin 1), x) (φ c)) =
      C (u i) * ev (n := 1) ![φ] (pderiv R ((0 : Fin 1), c) f) *
        ∑ x, pderiv R ((0 : Fin 1), x) (φ c) *
          ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F x)) := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  conv_lhs => rw [Finset.sum_comm]
  simp only [step, jac_endo G φ hφ hom c, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.DerivEndo
