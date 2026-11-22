-- Prove2me | solution 1 for NoHair.Weyl.kerr_radial_primitive_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:48:38.485727+00:00
-- url     : https://prove2.me/submissions/203ef2dd-2a85-41c5-8551-e0972db39c43

import Theorems.Thm_NoHair_Weyl_kerr_radial_rate_identities

noncomputable section
open NoHair NoHair.Weyl

private theorem radius_gt_z (k : ℝ) (p : OrbitPoint) : |p.2| < prolateRadius k p := by
  have side (v : ℝ) : |v| < Real.sqrt (Real.exp (2*p.1)+v^2) := by
    rw [← Real.sqrt_sq_eq_abs v]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith [Real.exp_pos (2*p.1)])
  have h := abs_add_le (p.2-k) (p.2+k)
  rw [show p.2-k+(p.2+k)=2*p.2 by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  unfold prolateRadius
  linarith [side (p.2-k),side (p.2+k)]

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    let k := Real.sqrt (m^2-a^2)
    let x := prolateRadius k
    let r := fun p => m+x p
    let c := fun p : OrbitPoint => p.2/x p
    let B := fun p => 1-c p^2
    let P := fun p => (r p^2+a^2)^2-a^2*kerrDelta m a (r p)*B p
    let D := fun p => x p^2-k^2*c p^2
    let W := fun p => -(2*m*r p*a)/P p
    let L := fun p => B p*P p/D p
    let H := fun p : OrbitPoint => Real.log (L p)/2-p.1
    (∀ p, 0 < L p) ∧ ContDiff ℝ 1 W ∧ ContDiff ℝ 1 H ∧
      ∀ s z : ℝ, HasDerivAt (fun t => W (t,z)) (shiftRate (kerrErnst m a) (s,z)) s ∧
        HasDerivAt (fun t => H (t,z)) (conformalRate (kerrErnst m a) (s,z)) s := by
  let k := Real.sqrt (m^2-a^2)
  let x := prolateRadius k
  let r := fun p => m+x p
  let c := fun p : OrbitPoint => p.2/x p
  let B := fun p => 1-c p^2
  let P := fun p => (r p^2+a^2)^2-a^2*kerrDelta m a (r p)*B p
  let D := fun p => x p^2-k^2*c p^2
  let W := fun p => -(2*m*r p*a)/P p
  let L := fun p => B p*P p/D p
  have hk : k^2 = m^2-a^2 := Real.sq_sqrt (by nlinarith [hm.2])
  have hr (p) : r p-m=x p := by dsimp [r]; ring
  have hp (p) : kerrAxialNumerator m a (r p) (c p)=P p := by
    dsimp only [P,B,kerrAxialNumerator,kerrDelta]; ring
  have hW : W=kerrWeylShift m a := by
    funext p
    change -(2*m*r p*a)/P p=-(2*m*a*r p)/kerrAxialNumerator m a (r p) (c p)
    rw [hp]; ring
  have hL : L=kerrWeylScale m a := by
    funext p
    change B p*P p/(x p^2-k^2*c p^2)=B p*kerrAxialNumerator m a (r p) (c p)/
      ((r p-m)^2-(m^2-a^2)*c p^2)
    rw [hp,hr,hk]
  have hpos (p : OrbitPoint) : 0<L p := by
    rw [hL]; exact (kerr_radial_rate_identities m a hm p.1 p.2).1
  have hP (p) : P p ≠ 0 := by
    intro hz
    have h := hpos p
    change 0 < B p*P p/D p at h
    simp [hz] at h
  have hD (p) : D p ≠ 0 := by
    intro hz
    have h := hpos p
    change 0 < B p*P p/D p at h
    simp [hz] at h
  have hx : ContDiff ℝ 1 x := by
    unfold x prolateRadius
    fun_prop (disch := first | positivity | intro p; positivity)
  have hrs : ContDiff ℝ 1 r := contDiff_const.add hx
  have hcs : ContDiff ℝ 1 c := contDiff_snd.div hx
    (fun p => ((abs_nonneg _).trans_lt (radius_gt_z k p)).ne')
  have hbs : ContDiff ℝ 1 B := contDiff_const.sub (hcs.pow 2)
  have hps : ContDiff ℝ 1 P := by
    dsimp only [P,kerrDelta]
    fun_prop
  have hds : ContDiff ℝ 1 D := (hx.pow 2).sub (contDiff_const.mul (hcs.pow 2))
  have hws : ContDiff ℝ 1 W := by dsimp only [W]; fun_prop (disch := exact hP)
  have hls : ContDiff ℝ 1 L := (hbs.mul hps).div hds hD
  change (∀ p,0<L p) ∧ ContDiff ℝ 1 W ∧ ContDiff ℝ 1 (fun p => Real.log (L p)/2-p.1) ∧
    ∀ s z : ℝ, HasDerivAt (fun t => W (t,z)) _ s ∧ HasDerivAt (fun t => Real.log (L (t,z))/2-t) _ s
  refine ⟨hpos,hws,((hls.log fun p => (hpos p).ne').div_const 2).sub contDiff_fst,?_⟩
  rw [hW,hL]
  exact fun s z => (kerr_radial_rate_identities m a hm s z).2
