-- Prove2me | solution 1 for GlobalTheory.DerivEndo.jac_endo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:44:01.84136+00:00
-- url     : https://prove2.me/submissions/48fabb80-083b-4c58-8e34-0e44ccd838fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
import Theorems.Thm_GlobalTheory_DerivEndo_noConst_one
import Theorems.Thm_GlobalTheory_DerivEndo_noConst_two
import Theorems.Thm_GlobalTheory_DerivEndo_cc_pt
import Theorems.Thm_GlobalTheory_DerivEndo_cc_ev
import Theorems.Thm_GlobalTheory_DerivEndo_ev_pt
import Theorems.Thm_GlobalTheory_DerivEndo_ev_zero
import Theorems.Thm_GlobalTheory_DerivEndo_ev_mul
import Theorems.Thm_GlobalTheory_DerivEndo_ev_sum
import Theorems.Thm_GlobalTheory_DerivEndo_ev_ev
import Theorems.Thm_GlobalTheory_DerivEndo_pderiv_ev
import Theorems.Thm_GlobalTheory_DerivEndo_germPointsNoConstantTerm_first_zero
import Theorems.Thm_GlobalTheory_DerivEndo_add_pt
import Theorems.Thm_GlobalTheory_DerivEndo_germ_ev_restrict_axis_first_point
import Theorems.Thm_GlobalTheory_DerivEndo_germ_ev_restrict_axis_second_point
import Theorems.Thm_GlobalTheory_DerivEndo_germ_ev_restrict_axis_groupLaw
import Theorems.Thm_GlobalTheory_DerivEndo_pderiv_second_of_ev_first_point
import Theorems.Thm_GlobalTheory_DerivEndo_dy_y
import Theorems.Thm_GlobalTheory_DerivEndo_cc_pderiv
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
private theorem comp1_apply_eq_ev {n : ℕ} (φ : Pt R 1 d) (ψ : Pt R n d) (b : Fin d) :
    comp1 φ ψ b = ev (n := n) ![ψ] (φ b) := by
  rfl
private theorem ev_swap_of_constantCoeff_eq_zero (φ : Pt R 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0) (g : PS R 2 d) :
    ev (n := 1) ![pt R d 0, 0]
        (ev (n := 2) ![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] g) =
      ev (n := 1) ![φ] (ev (n := 1) ![pt R d 0, 0] g) := by
  have hx : NoConst (![pt R (n := 2) d 0] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 0)
  have hy : NoConst (![pt R (n := 2) d 1] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 1)
  have hxy : NoConst (![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] :
      Fin 2 → Pt R 2 d) :=
    noConst_two (fun b => (cc_ev hx (φ b)).trans (hφ b)) (fun b => (cc_ev hy (φ b)).trans (hφ b))
  rw [ev_ev germPointsNoConstantTerm_first_zero hxy, ev_ev (noConst_one hφ) germPointsNoConstantTerm_first_zero]
  congr 1
  funext j b
  fin_cases j
  · show ev (n := 1) ![pt R d 0, 0] (ev (n := 2) ![pt R (n := 2) d 0] (φ b)) =
      ev (n := 1) ![φ] (pt R d 0 b)
    rw [germ_ev_restrict_axis_first_point, ev_pt (noConst_one hφ)]
    rfl
  · show ev (n := 1) ![pt R d 0, 0] (ev (n := 2) ![pt R (n := 2) d 1] (φ b)) =
      ev (n := 1) ![φ] (0 : PS R 1 d)
    rw [germ_ev_restrict_axis_second_point, hφ b, map_zero, ev_zero (noConst_one hφ)]
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
theorem _root_.solution (G : FGLaw R d) (φ : Pt R 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hom : comp1 φ (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1))) (a i : Fin d) :
    ∑ c, pderiv R ((0 : Fin 1), c) (φ a) *
        ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F c)) =
      ∑ b, ev (n := 1) ![φ] (ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), b) (G.F a))) *
        C (dLin φ b i) := by
  have hF : NoConst (![G.F] : Fin 1 → Pt R 2 d) := noConst_one G.const
  have hx : NoConst (![pt R (n := 2) d 0] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 0)
  have hy : NoConst (![pt R (n := 2) d 1] : Fin 1 → Pt R 2 d) := noConst_one (cc_pt 1)
  have hxy : NoConst (![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] :
      Fin 2 → Pt R 2 d) :=
    noConst_two (fun b => (cc_ev hx (φ b)).trans (hφ b)) (fun b => (cc_ev hy (φ b)).trans (hφ b))
  have key : ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (ev (n := 2) ![G.F] (φ a))) =
      ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i)
        (ev (n := 2) ![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] (G.F a))) := by
    have h2 := congrFun hom a
    rw [add_pt] at h2
    exact congrArg (fun g => ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) g)) h2
  rw [pderiv_ev hF, pderiv_ev hxy, Fin.sum_univ_one, Fin.sum_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, comp1_apply_eq_ev, pderiv_second_of_ev_first_point,
    dy_y, mul_zero, Finset.sum_const_zero, zero_add] at key
  simp only [ev_sum germPointsNoConstantTerm_first_zero, ev_mul germPointsNoConstantTerm_first_zero, germ_ev_restrict_axis_groupLaw, ev_swap_of_constantCoeff_eq_zero φ hφ, germ_ev_restrict_axis_second_point, cc_pderiv] at key
  exact key
end GlobalTheory.DerivEndo
