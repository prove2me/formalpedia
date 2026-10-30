-- Prove2me | solution 1 for NonconvexCost.Complexity.corollary_5_6
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T11:31:10.253215+00:00
-- url     : https://prove2.me/submissions/3d3cbf84-7f15-4288-8070-e2ec6ef618a8

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting

open Set

theorem _root_.community_slope_drop (h s : ℝ → ℝ) (p q : ℝ) (hs : ConvexOn ℝ (Icc p q) s)
    (hhs : ConvexOn ℝ (Icc p q) (h + s)) (x y : ℝ) (hpx : p ≤ x) (hxy : x < y) (hyq : y ≤ q)
    (c a b : ℝ) (hc : HasDerivWithinAt h c (Icc x q) x) (hc0 : 0 ≤ c)
    (ha : HasDerivWithinAt s a (Icc x q) x) (hb : HasDerivWithinAt s b (Icc p y) y) :
    a - b ≤ (h y - h x) / (y - x) := by
  have hsR : ConvexOn ℝ (Icc x q) s := hs.subset (Icc_subset_Icc hpx le_rfl) (convex_Icc x q)
  have hsL : ConvexOn ℝ (Icc p y) s := hs.subset (Icc_subset_Icc le_rfl hyq) (convex_Icc p y)
  have hhsR : ConvexOn ℝ (Icc x q) (h + s) :=
    hhs.subset (Icc_subset_Icc hpx le_rfl) (convex_Icc x q)
  have hxR : x ∈ Icc x q := ⟨le_rfl, (hxy.trans_le hyq).le⟩
  have hyR : y ∈ Icc x q := ⟨hxy.le, hyq⟩
  have hxL : x ∈ Icc p y := ⟨hpx, hxy.le⟩
  have hyL : y ∈ Icc p y := ⟨hpx.trans hxy.le, le_rfl⟩
  have h1 : a ≤ slope s x y := hsR.le_slope_of_hasDerivWithinAt hxR hyR hxy ha
  have h2 : slope s x y ≤ b := hsL.slope_le_of_hasDerivWithinAt hxL hyL hxy hb
  have h3 : c + a ≤ slope (h + s) x y :=
    hhsR.le_slope_of_hasDerivWithinAt hxR hyR hxy (hc.add ha)
  have e : slope (h + s) x y = slope h x y + slope s x y := by
    simp only [slope_def_field, Pi.add_apply]; ring
  rw [← slope_def_field]
  linarith

namespace Queelius.BisectionComplexity
open NonconvexCost.Complexity Set Filter Topology
lemma midpoint_derivatives (s : ℝ → ℝ) (p m q : ℝ) (hs : ConvexOn ℝ (Icc p q) s)
    (hpm : p < m) (hmq : m < q) :
    ∃ a b : ℝ,HasDerivWithinAt s a (Icc m q) m ∧
      HasDerivWithinAt s b (Icc p m) m ∧ b ≤ a := by
  have hm : m ∈ Icc p q := ⟨hpm.le,hmq.le⟩
  have hr : MonotoneOn (slope s m) (Ioo m q) :=
    (hs.monotoneOn_slope_gt hm).mono (fun x hx => ⟨⟨hpm.le.trans hx.1.le,hx.2.le⟩,hx.1⟩)
  have hl : MonotoneOn (slope s m) (Ioo p m) :=
    (hs.monotoneOn_slope_lt hm).mono (fun x hx => ⟨⟨hx.1.le,hx.2.le.trans hmq.le⟩,hx.2⟩)
  have hbr : BddBelow ((slope s m) '' Ioo m q) := by
    refine ⟨(s m-s p)/(m-p),?_⟩
    rintro _ ⟨y,hy,rfl⟩
    simpa only [slope_def_field] using hs.slope_mono_adjacent ⟨le_rfl,hpm.le.trans hmq.le⟩
      ⟨hpm.le.trans hy.1.le,hy.2.le⟩ hpm hy.1
  have hbl : BddAbove ((slope s m) '' Ioo p m) := by
    refine ⟨(s q-s m)/(q-m),?_⟩
    rintro _ ⟨x,hx,rfl⟩
    rw [slope_comm s m x]
    simpa only [slope_def_field] using hs.slope_mono_adjacent ⟨hx.1.le,hx.2.le.trans hmq.le⟩
      ⟨hpm.le.trans hmq.le,le_rfl⟩ hx.2 hmq
  let a := sInf ((slope s m) '' Ioo m q)
  let b := sSup ((slope s m) '' Ioo p m)
  have htr := MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hmq) hr hbr
  have htl := MonotoneOn.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hpm) hl hbl
  have har : HasDerivWithinAt s a (Ioi m) m :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : m ∉ Ioi m)).mpr htr
  have hbr' : HasDerivWithinAt s b (Iio m) m :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : m ∉ Iio m)).mpr htl
  refine ⟨a,b,har.Ici_of_Ioi.mono Icc_subset_Ici_self,hbr'.Iic_of_Iio.mono Icc_subset_Iic_self,?_⟩
  apply le_csInf ((nonempty_Ioo.mpr hmq).image _)
  rintro _ ⟨y,hy,rfl⟩
  apply csSup_le ((nonempty_Ioo.mpr hpm).image _)
  rintro _ ⟨x,hx,rfl⟩
  rw [slope_comm s m x]
  simpa only [slope_def_field] using hs.slope_mono_adjacent ⟨hx.1.le,hx.2.le.trans hmq.le⟩
    ⟨hpm.le.trans hy.1.le,hy.2.le⟩ hx.2 hy.1
lemma bisect_shift (h : ℝ → ℝ) (p q : ℝ) (n : ℕ) :
    bisect h p q (n+1)=
      if 2*h ((p+q)/2) < h p+h q then bisect h p ((p+q)/2) n
      else bisect h ((p+q)/2) q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bisect,ih]
    split_ifs <;> simp_all [bisect]
lemma eval_shift_left (h : ℝ → ℝ) (p q : ℝ) (hl : 2*h ((p+q)/2) < h p+h q) (n : ℕ) :
    evalPt h p ((p+q)/2) (n+1)=evalPt h p q (n+2) := by
  simp only [evalPt,bisect_shift,if_pos hl]
lemma eval_shift_right (h : ℝ → ℝ) (p q : ℝ) (hl : ¬ 2*h ((p+q)/2) < h p+h q) (n : ℕ) :
    evalPt h ((p+q)/2) q (n+1)=evalPt h p q (n+2) := by
  simp only [evalPt,bisect_shift,if_neg hl]
lemma noStop_left (h h' : ℝ → ℝ) (p q : ℝ) (k : ℕ)
    (hr : NoStopWithin h h' p q (k+1)) (hl : 2*h ((p+q)/2) < h p+h q) :
    NoStopWithin h h' p ((p+q)/2) k := by
  intro j hj
  cases j with
  | zero => simpa [evalPt] using hr 0 (by omega)
  | succ n => rw [eval_shift_left h p q hl n];exact hr (n+2) (by omega)
lemma noStop_right (h h' : ℝ → ℝ) (p q : ℝ) (k : ℕ)
    (hr : NoStopWithin h h' p q (k+1)) (hl : ¬ 2*h ((p+q)/2) < h p+h q) :
    NoStopWithin h h' ((p+q)/2) q k := by
  intro j hj
  cases j with
  | zero => simpa [evalPt,bisect] using hr 1 (by omega)
  | succ n => rw [eval_shift_right h p q hl n];exact hr (n+2) (by omega)
end Queelius.BisectionComplexity

namespace Queelius.BisectionComplexity
open NonconvexCost.Complexity Set
lemma complexity (h h' s : ℝ → ℝ) (p q : ℝ) (hpq : p < q) (hs : ConvexOn ℝ (Icc p q) s)
    (hhs : ConvexOn ℝ (Icc p q) (h+s)) (hder : IsRightDerivOn h h' p q) (sp sq : ℝ)
    (hsp : HasDerivWithinAt s sp (Icc p q) p) (hsq : HasDerivWithinAt s sq (Icc p q) q)
    (k : ℕ) (hk : 1 ≤ k) (hrun : NoStopWithin h h' p q k) :
    (sp-sq)/k ≤ (h q-h p)/(q-p) := by
  induction k generalizing p q sp sq with
  | zero => omega
  | succ k ih =>
    have hdp := hder p ⟨le_rfl,hpq⟩
    have hnp : 0 ≤ h' p := by simpa [evalPt] using hrun 0 (by omega)
    by_cases hk0 : k=0
    · subst k
      have he := community_slope_drop h s p q hs hhs p q le_rfl hpq le_rfl
        (h' p) sp sq hdp hnp hsp hsq
      simpa using he
    have hkpos : 0 < (k:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
    have hkone : (1:ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
    let m := (p+q)/2
    have hpm : p < m := by dsimp [m];linarith
    have hmq : m < q := by dsimp [m];linarith
    obtain ⟨sr,sl,hsr,hsl,horder⟩ := midpoint_derivatives s p m q hs hpm hmq
    have hnm : 0 ≤ h' m := by simpa [evalPt,bisect,m] using hrun 1 (by omega)
    have hdm := hder m ⟨hpm.le,hmq⟩
    let A := (h q-h p)/(q-p)
    let L := (h m-h p)/(m-p)
    let R := (h q-h m)/(q-m)
    have hlen : 0 < q-p := sub_pos.mpr hpq
    have hL : L=(2*(h m-h p))/(q-p) := by
      dsimp only [L]
      rw [show m-p=(q-p)/2 by dsimp [m];ring]
      field_simp [hlen.ne']
      <;> ring
    have hR : R=(2*(h q-h m))/(q-p) := by
      dsimp only [R]
      rw [show q-m=(q-p)/2 by dsimp [m];ring]
      field_simp [hlen.ne']
      <;> ring
    have hsum : L+R=2*A := by rw [hL,hR];dsimp [A];ring
    simp only [Nat.cast_add,Nat.cast_one]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ)+1)).mpr
    by_cases hl : 2*h m < h p+h q
    · have hs' := hs.subset (Icc_subset_Icc le_rfl hmq.le) (convex_Icc p m)
      have hhs' := hhs.subset (Icc_subset_Icc le_rfl hmq.le) (convex_Icc p m)
      have hd' : IsRightDerivOn h h' p m := by
        intro x hx
        exact (hder x ⟨hx.1,hx.2.trans hmq⟩).mono (Icc_subset_Icc le_rfl hmq.le)
      have hi := ih p m hpm hs' hhs' hd' sp sl
        (hsp.mono (Icc_subset_Icc le_rfl hmq.le)) hsl (Nat.one_le_iff_ne_zero.mpr hk0)
        (noStop_left h h' p q k hrun hl)
      have hi' : sp-sl ≤ L*k := (div_le_iff₀ hkpos).mp hi
      have ho := community_slope_drop h s p q hs hhs m q hpm.le hmq le_rfl
        (h' m) sr sq hdm hnm hsr hsq
      have hlo : L ≤ A := by
        rw [hL]
        exact div_le_div_of_nonneg_right (by dsimp [A,m] at *;linarith) hlen.le
      have hm := mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hkone)
      change sp-sq ≤ A*((k:ℝ)+1)
      change sr-sq ≤ R at ho
      nlinarith
    · have hs' := hs.subset (Icc_subset_Icc hpm.le le_rfl) (convex_Icc m q)
      have hhs' := hhs.subset (Icc_subset_Icc hpm.le le_rfl) (convex_Icc m q)
      have hd' : IsRightDerivOn h h' m q := by
        intro x hx
        exact hder x ⟨hpm.le.trans hx.1,hx.2⟩
      have hi := ih m q hmq hs' hhs' hd' sr sq hsr
        (hsq.mono (Icc_subset_Icc hpm.le le_rfl)) (Nat.one_le_iff_ne_zero.mpr hk0)
        (noStop_right h h' p q k hrun hl)
      have hi' : sr-sq ≤ R*k := (div_le_iff₀ hkpos).mp hi
      have ho := community_slope_drop h s p q hs hhs p m le_rfl hpm hmq.le
        (h' p) sp sl hdp hnp hsp hsl
      have hro : R ≤ A := by
        rw [hR]
        exact div_le_div_of_nonneg_right (by dsimp [A,m] at *;linarith) hlen.le
      have hm := mul_le_mul_of_nonneg_left hro (sub_nonneg.mpr hkone)
      change sp-sq ≤ A*((k:ℝ)+1)
      change sp-sl ≤ L at ho
      nlinarith
end Queelius.BisectionComplexity
namespace NonconvexCost.Complexity
 theorem _root_.prior_complexity (h h' s : ℝ → ℝ) (p q : ℝ) (hpq : p < q) (hs : ConvexOn ℝ (Set.Icc p q) s)
    (hhs : ConvexOn ℝ (Set.Icc p q) (h+s)) (hder : IsRightDerivOn h h' p q) (sp sq : ℝ)
    (hsp : HasDerivWithinAt s sp (Set.Icc p q) p) (hsq : HasDerivWithinAt s sq (Set.Icc p q) q)
    (k : ℕ) (hk : 1 ≤ k) (hrun : NoStopWithin h h' p q k) :
    (sp-sq)/k ≤ (h q-h p)/(q-p) := by
  exact Queelius.BisectionComplexity.complexity h h' s p q hpq hs hhs hder sp sq hsp hsq k hk hrun
end NonconvexCost.Complexity

namespace Queelius.BisectionTermination
open NonconvexCost.Complexity Set Filter Topology
open scoped ENNReal NNReal
lemma lipschitz_slope (s : ℝ → ℝ) (p q : ℝ) (K : ℝ≥0)
    (hl : LipschitzOnWith K s (Icc p q)) (x y : ℝ) (hx : x ∈ Icc p q) (hy : y ∈ Icc p q)
    (hxy : x ≠ y) : -(K:ℝ) ≤ slope s x y ∧ slope s x y ≤ K := by
  apply abs_le.mp
  rw [slope_def_field,abs_div]
  apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hxy.symm))).mpr
  simpa only [Real.dist_eq] using hl.dist_le_mul y hy x hx
lemma endpoint_derivatives (s : ℝ → ℝ) (p q : ℝ) (hpq : p < q)
    (hs : ConvexOn ℝ (Icc p q) s) (K : ℝ≥0) (hl : LipschitzOnWith K s (Icc p q)) :
    ∃ a b : ℝ,HasDerivWithinAt s a (Icc p q) p ∧ HasDerivWithinAt s b (Icc p q) q ∧
      -(K:ℝ) ≤ a ∧ b ≤ K := by
  have hp : p ∈ Icc p q := ⟨le_rfl,hpq.le⟩
  have hq : q ∈ Icc p q := ⟨hpq.le,le_rfl⟩
  have hr : MonotoneOn (slope s p) (Ioo p q) :=
    (hs.monotoneOn_slope_gt hp).mono (fun x hx => ⟨⟨hx.1.le,hx.2.le⟩,hx.1⟩)
  have hleft : MonotoneOn (slope s q) (Ioo p q) :=
    (hs.monotoneOn_slope_lt hq).mono (fun x hx => ⟨⟨hx.1.le,hx.2.le⟩,hx.2⟩)
  have hbr : BddBelow ((slope s p) '' Ioo p q) := by
    refine ⟨-(K:ℝ),?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact (lipschitz_slope s p q K hl p x hp ⟨hx.1.le,hx.2.le⟩ hx.1.ne).1
  have hbl : BddAbove ((slope s q) '' Ioo p q) := by
    refine ⟨(K:ℝ),?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact (lipschitz_slope s p q K hl q x hq ⟨hx.1.le,hx.2.le⟩ hx.2.ne').2
  let a := sInf ((slope s p) '' Ioo p q)
  let b := sSup ((slope s q) '' Ioo p q)
  have htr := MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hpq) hr hbr
  have htl := MonotoneOn.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hpq) hleft hbl
  have har : HasDerivWithinAt s a (Ioi p) p :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : p ∉ Ioi p)).mpr htr
  have hbl' : HasDerivWithinAt s b (Iio q) q :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : q ∉ Iio q)).mpr htl
  refine ⟨a,b,har.Ici_of_Ioi.mono Icc_subset_Ici_self,hbl'.Iic_of_Iio.mono Icc_subset_Iic_self,?_,?_⟩
  · apply le_csInf ((nonempty_Ioo.mpr hpq).image _)
    rintro _ ⟨x,hx,rfl⟩
    exact (lipschitz_slope s p q K hl p x hp ⟨hx.1.le,hx.2.le⟩ hx.1.ne).1
  · apply csSup_le ((nonempty_Ioo.mpr hpq).image _)
    rintro _ ⟨x,hx,rfl⟩
    exact (lipschitz_slope s p q K hl q x hq ⟨hx.1.le,hx.2.le⟩ hx.2.ne').2
lemma correction_below (h : ℝ → ℝ) (J : Set ℝ) (R : ℝ)
    (hR : (concaveDeviation h J).toReal < R) (hfinite : concaveDeviation h J ≠ ⊤) :
    ∃ s : ℝ → ℝ,∃ K : ℝ≥0,ConvexOn ℝ J s ∧ ConvexOn ℝ J (h+s) ∧
      LipschitzOnWith K s J ∧ (K:ℝ) < R := by
  have hp : 0 < R := ENNReal.toReal_nonneg.trans_lt hR
  have hi : concaveDeviation h J < ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hp).mpr hR
  unfold concaveDeviation at hi
  obtain ⟨s,hs⟩ := iInf_lt_iff.mp hi
  obtain ⟨K,hK⟩ := iInf_lt_iff.mp hs
  obtain ⟨hvalid,hKR⟩ := iInf_lt_iff.mp hK
  refine ⟨s,K,hvalid.1,hvalid.2.1,hvalid.2.2,?_⟩
  have hr := ENNReal.toReal_lt_toReal ENNReal.coe_ne_top ENNReal.ofReal_ne_top |>.mpr hKR
  simpa only [ENNReal.coe_toReal,ENNReal.toReal_ofReal hp.le] using hr
lemma termination (h h' : ℝ → ℝ) (p q : ℝ) (hpq : p < q) (hder : IsRightDerivOn h h' p q)
    (hM : concaveDeviation h (Icc p q) ≠ ⊤) (hσ : 0 < -((h q-h p)/(q-p))) :
    ¬ NoStopWithin h h' p q
      (1+⌊2*(concaveDeviation h (Icc p q)).toReal/(-((h q-h p)/(q-p)))⌋₊) := by
  let M := (concaveDeviation h (Icc p q)).toReal
  let σ := -((h q-h p)/(q-p))
  let k := 1+⌊2*M/σ⌋₊
  have hk : 1 ≤ k := by dsimp [k];omega
  have hkreal : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hσp : 0 < σ := hσ
  have hfloor : 2*M/σ < (k:ℝ) := by
    have hf := Nat.lt_floor_add_one (2*M/σ)
    simpa only [k,Nat.cast_add,Nat.cast_one,add_comm] using hf
  have hbudget : M < σ*(k:ℝ)/2 := by
    have hh := (div_lt_iff₀ hσp).mp hfloor
    nlinarith
  obtain ⟨s,K,hs,hhs,hl,hK⟩ := correction_below h (Icc p q) (σ*(k:ℝ)/2) hbudget hM
  obtain ⟨a,b,ha,hb,hKa,hbK⟩ := endpoint_derivatives s p q hpq hs K hl
  intro hrun
  have hc := Queelius.BisectionComplexity.complexity h h' s p q hpq hs hhs hder a b ha hb k hk hrun
  have hc' := (div_le_iff₀ hkreal).mp hc
  rw [show (h q-h p)/(q-p) = -σ by dsimp [σ];ring] at hc'
  nlinarith
end Queelius.BisectionTermination

namespace NonconvexCost.Complexity
theorem _root_.solution (h h' : ℝ → ℝ) (p q : ℝ) (hpq : p < q) (hder : IsRightDerivOn h h' p q)
    (hM : concaveDeviation h (Set.Icc p q) ≠ ⊤) (hσ : 0 < -((h q-h p)/(q-p))) :
    ¬ NoStopWithin h h' p q
      (1+⌊2*(concaveDeviation h (Set.Icc p q)).toReal/(-((h q-h p)/(q-p)))⌋₊) := by
  exact Queelius.BisectionTermination.termination h h' p q hpq hder hM hσ
end NonconvexCost.Complexity
