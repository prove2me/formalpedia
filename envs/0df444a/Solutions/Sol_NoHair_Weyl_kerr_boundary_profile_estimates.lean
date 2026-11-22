-- Prove2me | solution 1 for NoHair.Weyl.kerr_boundary_profile_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:48:03.130315+00:00
-- url     : https://prove2.me/submissions/460970f0-3245-4cd6-8ba7-66a2fe7a572c

import Definitions.Def_NoHair_weylBoundaryProfile
import Theorems.Thm_NoHair_Weyl_prolate_coordinate_differentials

noncomputable section

open NoHair NoHair.Weyl

private theorem pointwise_bounds (m a r c : ℝ) (hm : 0 < m) (hmr : m ≤ r) (hs : 0 < 1-c^2) :
    let A := (1-c^2)*r^2
    let x := kerrAxialNorm m a r c / A - 1
    let y := (kerrAxialTwist m a r c - 2*(m*a)*(3*c-c^3)) / A
    0 < A ∧ 0 ≤ x ∧ x ≤ 3*a^2/r^2 ∧ |y| ≤ 2*m*|a|^3/r^4 := by
  let S:=1-c^2
  let Q:=r^2+a^2*c^2
  let e:=2*m*r*a^2*S/Q
  have hr := hm.trans_le hmr
  have hr2 := sq_pos_of_pos hr
  have hQ : r^2 ≤ Q := le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hq := hr2.trans_le hQ
  have hS : 0 < S := hs
  have hS1 : S ≤ 1 := sub_le_self _ (sq_nonneg c)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have he' : e ≤ 2*a^2 := by
    apply (div_le_iff₀ hq).2
    have hh : m*r*S ≤ Q := calc
      m*r*S ≤ m*r := by simpa using mul_le_mul_of_nonneg_left hS1 (mul_nonneg hm.le hr.le)
      _ ≤ r^2 := by simpa [sq] using mul_le_mul_of_nonneg_right hmr hr.le
      _ ≤ Q := hQ
    nlinarith only [mul_nonneg (show 0 ≤ 2*a^2 by positivity) (sub_nonneg.mpr hh)]
  have hx : kerrAxialNorm m a r c/(S*r^2)-1=(a^2+e)/r^2 := by
    change S*(r^2+a^2+e)/(S*r^2)-1=_
    field_simp [hS.ne',hr.ne'] <;> ring
  have hy : (kerrAxialTwist m a r c - 2*(m*a)*(3*c-c^3))/(S*r^2)=2*m*a^3*c*S/(Q*r^2) := by
    unfold kerrAxialTwist
    change (2*m*a*(3*c-c^3)+2*m*a^3*c*S^2/Q-2*(m*a)*(3*c-c^3))/(S*r^2)=_
    field_simp [hS.ne',hq.ne',hr.ne'] <;> ring
  have hc : |c| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg (c+1)],by nlinarith [sq_nonneg (c-1)]⟩
  have hfac : |c| *S ≤ 1 := (mul_le_mul hc hS1 hS.le (by norm_num)).trans_eq (one_mul 1)
  have hnum : 0 ≤ 2*m*|a|^3 := by positivity
  change 0 < S*r^2 ∧ 0 ≤ kerrAxialNorm m a r c/(S*r^2)-1 ∧
    kerrAxialNorm m a r c/(S*r^2)-1 ≤ _ ∧ |(kerrAxialTwist m a r c-2*(m*a)*(3*c-c^3))/(S*r^2)| ≤ _
  rw [hx,hy]
  refine ⟨mul_pos hS hr2,by positivity,(div_le_div_iff_of_pos_right hr2).2 (by linarith),?_⟩
  simp only [abs_div,abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ) < 2),abs_of_pos hm,
    abs_of_pos hS,abs_of_pos hq,abs_of_pos hr]
  calc
    2*m*|a|^3*|c| *S/(Q*r^2) ≤ (2*m*|a|^3)/(Q*r^2) := by
      apply (div_le_div_iff_of_pos_right (mul_pos hq hr2)).2
      simpa only [mul_assoc,mul_one] using mul_le_mul_of_nonneg_left hfac hnum
    _ ≤ _ := div_le_div_of_nonneg_left hnum (pow_pos hr 4)
      (by simpa only [show r^4=r^2*r^2 by ring] using mul_le_mul_of_nonneg_right hQ hr2.le)

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    let ℓ := Real.sqrt (m^2-a^2)
    let b := rodBoundaryProfile m ℓ (m*a)
    let K := kerrErnst m a
    HasProfileEstimates K b ∧ ∀ p,
      let r := m+prolateRadius ℓ p
      let x := K.normSq p / b.normSq p - 1
      let y := (K.twist p - b.twist p) / b.normSq p
      0 < b.normSq p ∧ 0 ≤ x ∧ x ≤ 3*a^2/r^2 ∧ |y| ≤ 2*m*|a|^3/r^4 := by
  let k := Real.sqrt (m^2-a^2)
  let b := rodBoundaryProfile m k (m*a)
  let K := kerrErnst m a
  let r := fun p => m+prolateRadius k p
  let x := fun p => K.normSq p/b.normSq p-1
  let y := fun p => (K.twist p-b.twist p)/b.normSq p
  have geom (p : OrbitPoint) : m ≤ r p ∧ Real.exp (2*p.1)+p.2^2 ≤ (r p)^2 := by
    let u:=prolateRadius k p
    let c:=p.2/u
    obtain ⟨hu,hS,_,hw,_⟩ := (prolate_coordinate_differentials k).2.2 p
    change 0 < u at hu
    change 0 < 1-c^2 at hS
    change Real.exp (2*p.1)=(u^2-k^2)*(1-c^2) at hw
    have hz : p.2=u*c := by dsimp [c]; field_simp [hu.ne']
    have hrad : m ≤ r p := by change m ≤ m+u; linarith
    refine ⟨hrad,?_⟩
    change _ ≤ (m+u)^2
    rw [hw,hz]
    nlinarith only [mul_nonneg (sq_nonneg k) hS.le,mul_pos hm.1 hu,sq_nonneg m]
  have h (p : OrbitPoint) : 0 < b.normSq p ∧ 0 ≤ x p ∧ x p ≤ 3*a^2/(r p)^2 ∧
      |y p| ≤ 2*m*|a|^3/(r p)^4 :=
    pointwise_bounds m a (r p) _ hm.1 (geom p).1 ((prolate_coordinate_differentials k).2.2 p).2.1
  refine ⟨?_,h⟩
  let C:=3*a^2+2*m*|a|^3/m^2
  have hm2 := sq_pos_of_pos hm.1
  have hnum : 0 ≤ 2*m*|a|^3 := by have := hm.1; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have errors (p : OrbitPoint) : |x p| ≤ C/(r p)^2 ∧ |y p| ≤ C/(r p)^2 := by
    have hr := hm.1.trans_le (geom p).1
    have hr2 := sq_pos_of_pos hr
    have hmr := pow_le_pow_left₀ hm.1.le (geom p).1 2
    rw [abs_of_nonneg (h p).2.1]
    constructor
    · exact (h p).2.2.1.trans ((div_le_div_iff_of_pos_right hr2).2
        (le_add_of_nonneg_right (div_nonneg hnum hm2.le)))
    · apply (h p).2.2.2.trans
      calc
        2*m*|a|^3/(r p)^4 ≤ (2*m*|a|^3/m^2)/(r p)^2 := by
          rw [div_div]
          apply div_le_div_of_nonneg_left hnum (mul_pos hm2 hr2)
          simpa only [show (r p)^4=(r p)^2*(r p)^2 by ring] using mul_le_mul_of_nonneg_right hmr hr2.le
        _ ≤ _ := (div_le_div_iff_of_pos_right hr2).2 (le_add_of_nonneg_left (by positivity))
  constructor
  · refine ⟨1,C/m^2,zero_lt_one,fun p => ⟨by linarith only [(h p).2.1],?_,?_⟩⟩
    all_goals
      have h' := div_le_div_of_nonneg_left hC hm2 (pow_le_pow_left₀ hm.1.le (geom p).1 2)
      first | exact (errors p).1.trans h' | exact (errors p).2.trans h'
  · intro ε hε
    refine ⟨C/ε,fun p hp => ?_⟩
    have hr := hm.1.trans_le (geom p).1
    have hc := (div_le_iff₀ hε).mp (hp.trans (geom p).2)
    have h' : C/(r p)^2 ≤ ε := (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by linarith only [hc])
    exact ⟨(errors p).1.trans h',(errors p).2.trans h'⟩
