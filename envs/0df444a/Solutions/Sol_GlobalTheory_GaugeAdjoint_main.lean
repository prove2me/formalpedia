-- Prove2me | solution 1 for GlobalTheory.GaugeAdjoint.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:50.06585+00:00
-- url     : https://prove2.me/submissions/6a16f801-4d50-4532-9b51-3a30c28e790f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_GaugeAdjoint_hasSubst_pts
import Theorems.Thm_GlobalTheory_GaugeAdjoint_constantCoeff_ev
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_zero
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_two
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_comp1
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_axis
import Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_left
import Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_right
import Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_left
import Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_right
import Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_pderiv
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_formalExp
import Theorems.Thm_GlobalTheory_FormalCalc_subst_formalExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one


section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.GaugeAdjoint
open GlobalTheory.FormalCalc GlobalTheory.IntSeries
section Ev
variable {k : Type} [CommRing k] {d m n p : ℕ}
private theorem ev_sub_of_constantCoeff_eq_zero {a : Fin m → Pt k n d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f g : PS k m d) :
    ev a (f - g) = ev a f - ev a g := by
  unfold ev
  exact subst_sub (hasSubst_pts ha) f g
private theorem ev_mul_of_constantCoeff_eq_zero {a : Fin m → Pt k n d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f g : PS k m d) :
    ev a (f * g) = ev a f * ev a g := by
  unfold ev
  exact subst_mul (hasSubst_pts ha) f g
private theorem ev_neg_of_constantCoeff_eq_zero {a : Fin m → Pt k n d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS k m d) :
    ev a (-f) = -ev a f := by
  unfold ev
  rw [← substAlgHom_apply (hasSubst_pts ha), map_neg, substAlgHom_apply]
private theorem ev_finset_sum_of_constantCoeff_eq_zero {a : Fin m → Pt k n d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) {ι : Type} (s : Finset ι) (F : ι → PS k m d) :
    ev a (∑ j ∈ s, F j) = ∑ j ∈ s, ev a (F j) := by
  unfold ev
  rw [← substAlgHom_apply (hasSubst_pts ha), map_sum]
  simp only [substAlgHom_apply]
private theorem pderiv_map_algebraMap' {R : Type} [CommRing R] [Algebra R k] {σ : Type} (s : σ)
    (W : MvPowerSeries σ R) :
    pderiv k s (map (algebraMap R k) W) = map (algebraMap R k) (pderiv R s W) := by
  ext x
  rw [coeff_pderiv, coeff_map, coeff_map, coeff_pderiv, map_mul]
  simp
private theorem ev_formalExp_of_constantCoeff_eq_zero [Algebra ℚ k]
    {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0) {f : PS k m d}
    (hf : constantCoeff f = 0) : ev a (formalExp f) = formalExp (ev a f) := by
  unfold ev
  exact subst_formalExp (hasSubst_pts ha) hf
private theorem ev_axis_map_algebraMap {R : Type} [CommRing R] [Algebra R k]
    (W : PS R 2 d) :
    ev (n := 1) ![pt k d 0, 0] (map (algebraMap R k) W) =
      map (algebraMap R k) (ev (n := 1) ![pt R d 0, 0] W) := by
  unfold ev
  rw [map_subst (hasSubst_pts const_axis)]
  congr 1
  funext q
  obtain ⟨j, l⟩ := q
  fin_cases j <;> simp [pt]
end Ev
end GlobalTheory.GaugeAdjoint
end

set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.GaugeAdjoint
open GlobalTheory.FormalCalc GlobalTheory.IntSeries
namespace GlobalTheory.GaugeAdjoint
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (a : O) (i : Fin d), IntAA (R := R) k (ev (n := 1) ![comp1 (B.actK k a) (pt k d 0)] (sgOf k h i) - ∑ j, sgOf k h j * C (dAct k B (star a) j i)) := by
  intro R _ d O _ _ k _ _ _ B h hh a i
  have hp0 : ∀ l, constantCoeff (pt k d (0 : Fin 2) l) = 0 := fun l => const_pt 0 l
  have hp1 : ∀ l, constantCoeff (pt k d (1 : Fin 2) l) = 0 := fun l => const_pt 1 l
  have hq0 : ∀ l, constantCoeff (pt k d (0 : Fin 1) l) = 0 := fun l => const_pt 0 l
  have hact : ∀ (b : O) (l : Fin d), constantCoeff (B.actK k b l) = 0 := by
    intro b l
    show constantCoeff (map (algebraMap R k) (B.A.act b l)) = 0
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      B.A.const b l, map_zero]
  have hb0 := const_one (const_comp1 (hact a) hq0)
  have hc1 := const_two (const_comp1 (hact a) hp0) hp1
  have hc2 := const_two hp0 (const_comp1 (hact (star a)) hp1)
  have hQ0 : constantCoeff (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := by
    rw [map_sub, constantCoeff_ev hc1, constantCoeff_ev hc2, sub_self]
  have hA : map (algebraMap R k) (B.ad a) =
      formalExp (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
        ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) := hh.ad a
  have hEQ : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := by
    rw [ev_sub_of_constantCoeff_eq_zero const_axis, axis_left (hact a), axis_right (hact (star a)), hh.ax1,
      ev_zero hb0, sub_self]
  have hE : ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (map (algebraMap R k) (B.ad a))) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i)
        (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
          ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)) := by
    rw [hA, pderiv_formalExp hQ0, ev_mul_of_constantCoeff_eq_zero const_axis, ev_formalExp_of_constantCoeff_eq_zero const_axis hQ0, hEQ,
      formalExp_zero, one_mul]
  have hsg : ∀ j, ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) h) = -sgOf k h j := by
    intro j
    simp only [sgOf, neg_neg]
  have key : ev (n := 1) ![comp1 (B.actK k a) (pt k d 0)] (sgOf k h i) -
      ∑ j, sgOf k h j * C (dAct k B (star a) j i) =
      -ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (map (algebraMap R k) (B.ad a))) := by
    rw [hE, map_sub, ev_sub_of_constantCoeff_eq_zero const_axis, pderiv_left (hact a), pderiv_right (hact (star a)),
      axis_left (hact a), ev_finset_sum_of_constantCoeff_eq_zero const_axis]
    simp only [ev_mul_of_constantCoeff_eq_zero const_axis, axis_right (hact (star a)), axis_pderiv, hsg, ev_neg_of_constantCoeff_eq_zero hb0,
      dAct, neg_mul, Finset.sum_neg_distrib]
    ring
  rw [key, pderiv_map_algebraMap', ev_axis_map_algebraMap]
  intro x
  exact RingHom.mem_range.mpr ⟨-coeff x (ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (B.ad a))),
    by simp [coeff_map]⟩
end GlobalTheory.GaugeAdjoint
