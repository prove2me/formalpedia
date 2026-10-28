-- Prove2me | solution 1 for HeavyTailNV.Tail.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T16:34:30.619991+00:00
-- url     : https://prove2.me/submissions/d7e00ef1-7745-4eb4-a445-da12043aa3ef

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

set_option autoImplicit false

open MeasureTheory Filter Set HeavyTailNV.Tail

namespace HTNV43

/-- expected shortage of a law -/
noncomputable def sh (F : Measure ℝ) (q : ℝ) : ℝ := ∫ w, max (w - q) 0 ∂F

lemma mem_ae_nonneg {m1 ma α : ℝ} {F : Measure ℝ} (hF : F ∈ ambiguitySet m1 ma α) :
    ∀ᵐ w ∂F, 0 ≤ w := by
  obtain ⟨_, h0, -⟩ := hF
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
  rw [this]; exact h0

lemma mem_int_sh {m1 ma α : ℝ} {F : Measure ℝ} (hF : F ∈ ambiguitySet m1 ma α) (q : ℝ) :
    Integrable (fun w : ℝ => max (w - q) 0) F := by
  obtain ⟨hP, -, hi1, -⟩ := hF
  haveI := hP
  exact (hi1.sub (integrable_const q)).pos_part

lemma sh_le {m1 ma α : ℝ} {F : Measure ℝ} (hF : F ∈ ambiguitySet m1 ma α) (q : ℝ) :
    sh F q ≤ m1 + |q| := by
  have hF' := hF
  obtain ⟨hP, -, hi1, -, hm1, -⟩ := hF'
  haveI := hP
  unfold sh
  calc ∫ w, max (w - q) 0 ∂F ≤ ∫ w, (w + |q|) ∂F := by
        refine integral_mono_ae (mem_int_sh hF q) (hi1.add (integrable_const _)) ?_
        filter_upwards [mem_ae_nonneg hF] with w hw
        exact max_le (by linarith [neg_abs_le q]) (by linarith [abs_nonneg q])
    _ = m1 + |q| := by
        rw [integral_add hi1 (integrable_const _), hm1]; simp

lemma sh_nonneg (F : Measure ℝ) (q : ℝ) : 0 ≤ sh F q :=
  integral_nonneg fun _ => le_max_right _ _

lemma sh_of_nonpos {m1 ma α : ℝ} {F : Measure ℝ} (hF : F ∈ ambiguitySet m1 ma α) {q : ℝ}
    (hq : q ≤ 0) : sh F q = m1 - q := by
  have hF' := hF
  obtain ⟨hP, -, hi1, -, hm1, -⟩ := hF'
  haveI := hP
  unfold sh
  rw [integral_congr_ae (g := fun w => w - q)]
  · rw [integral_sub hi1 (integrable_const _), hm1]; simp
  · filter_upwards [mem_ae_nonneg hF] with w hw
    exact max_eq_left (by linarith)

lemma sh_convex {m1 ma α : ℝ} {F : Measure ℝ} (hF : F ∈ ambiguitySet m1 ma α) (x y a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    sh F (a * x + b * y) ≤ a * sh F x + b * sh F y := by
  unfold sh
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((mem_int_sh hF x).const_mul a) ((mem_int_sh hF y).const_mul b)]
  refine integral_mono (mem_int_sh hF _)
    (((mem_int_sh hF x).const_mul a).add ((mem_int_sh hF y).const_mul b)) fun w => ?_
  have h1 := le_max_left (w - x) 0
  have h2 := le_max_right (w - x) 0
  have h3 := le_max_left (w - y) 0
  have h4 := le_max_right (w - y) 0
  refine max_le ?_ (by positivity)
  have e : w - (a * x + b * y) = a * (w - x) + b * (w - y) := by linear_combination (-w) * hab
  rw [e]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h3 hb)

lemma sh_anti {m1 ma α : ℝ} {F : Measure ℝ} (hF : F ∈ ambiguitySet m1 ma α) {x y : ℝ}
    (hxy : x ≤ y) : sh F y ≤ sh F x :=
  integral_mono (mem_int_sh hF y) (mem_int_sh hF x) fun w =>
    max_le_max (by linarith) le_rfl

lemma sh_lip {m1 ma α : ℝ} {F : Measure ℝ} (hF : F ∈ ambiguitySet m1 ma α) {x y : ℝ}
    (hxy : x ≤ y) : sh F x ≤ sh F y + (y - x) := by
  have hF' := hF
  obtain ⟨hP, -⟩ := hF'
  haveI := hP
  unfold sh
  have : ∫ w, max (w - x) 0 ∂F ≤ ∫ w, (max (w - y) 0 + (y - x)) ∂F :=
    integral_mono (mem_int_sh hF x) ((mem_int_sh hF y).add (integrable_const _)) fun w =>
      max_le (by linarith [le_max_left (w - y) 0]) (by linarith [le_max_right (w - y) 0])
  rw [integral_add (mem_int_sh hF y) (integrable_const _)] at this
  simpa using this

lemma bdd {m1 ma α : ℝ} (q : ℝ) :
    BddAbove ((fun F : Measure ℝ => ∫ w, max (w - q) 0 ∂F) '' ambiguitySet m1 ma α) := by
  refine ⟨m1 + |q|, ?_⟩
  rintro _ ⟨F, hF, rfl⟩
  exact sh_le hF q

lemma le_wc {m1 ma α : ℝ} {F : Measure ℝ} (hF : F ∈ ambiguitySet m1 ma α) (q : ℝ) :
    sh F q ≤ worstCase m1 ma α q :=
  le_csSup (bdd q) ⟨F, hF, rfl⟩

lemma wc_le {m1 ma α : ℝ} (hne : (ambiguitySet m1 ma α).Nonempty) (q c : ℝ)
    (h : ∀ F ∈ ambiguitySet m1 ma α, sh F q ≤ c) : worstCase m1 ma α q ≤ c := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨F, hF, rfl⟩
  exact h F hF

lemma wc_convex {m1 ma α : ℝ} (hne : (ambiguitySet m1 ma α).Nonempty) :
    ConvexOn ℝ univ (worstCase m1 ma α) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  refine wc_le hne _ _ fun F hF => ?_
  simp only [smul_eq_mul]
  calc sh F (a * x + b * y) ≤ a * sh F x + b * sh F y := sh_convex hF x y a b ha hb hab
    _ ≤ a * worstCase m1 ma α x + b * worstCase m1 ma α y := by
        gcongr <;> exact le_wc hF _

lemma wc_anti {m1 ma α : ℝ} (hne : (ambiguitySet m1 ma α).Nonempty) :
    Antitone (worstCase m1 ma α) := fun x y hxy =>
  wc_le hne _ _ fun F hF => (sh_anti hF hxy).trans (le_wc hF x)

lemma wc_lip {m1 ma α : ℝ} (hne : (ambiguitySet m1 ma α).Nonempty) {x y : ℝ} (hxy : x ≤ y) :
    worstCase m1 ma α x ≤ worstCase m1 ma α y + (y - x) := by
  exact wc_le hne x _ fun F hF => (sh_lip hF hxy).trans (by linarith [le_wc hF y])

lemma wc_nonneg {m1 ma α : ℝ} (hne : (ambiguitySet m1 ma α).Nonempty) (q : ℝ) :
    0 ≤ worstCase m1 ma α q := by
  obtain ⟨F, hF⟩ := hne
  exact (sh_nonneg F q).trans (le_wc hF q)

lemma wc_of_nonpos {m1 ma α : ℝ} (hne : (ambiguitySet m1 ma α).Nonempty) {q : ℝ}
    (hq : q ≤ 0) : worstCase m1 ma α q = m1 - q := by
  obtain ⟨F, hF⟩ := hne
  refine le_antisymm (wc_le ⟨F, hF⟩ _ _ fun G hG => (sh_of_nonpos hG hq).le) ?_
  rw [← sh_of_nonpos hF hq]; exact le_wc hF q

end HTNV43

namespace HTNV43

/-- three-point law -/
noncomputable def law3 (p x w b : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac x + ENNReal.ofReal w • Measure.dirac b +
    ENNReal.ofReal (1 - p - w) • Measure.dirac 0

lemma law3_int {p x w b : ℝ} (f : ℝ → ℝ) :
    Integrable f (law3 p x w b) := by
  unfold law3
  refine ((Integrable.add_measure ?_ ?_).add_measure ?_) <;>
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma law3_integral {p x w b : ℝ} (hp : 0 ≤ p) (hw : 0 ≤ w) (hpw : p + w ≤ 1) (f : ℝ → ℝ) :
    ∫ t, f t ∂(law3 p x w b) = p * f x + w * f b + (1 - p - w) * f 0 := by
  unfold law3
  have i : ∀ a : ℝ, ∀ c : ℝ, Integrable f (ENNReal.ofReal c • Measure.dirac a) := fun a c =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure ((i x p).add_measure (i b w)) (i 0 _),
    integral_add_measure (i x p) (i b w)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hw,
    ENNReal.toReal_ofReal (by linarith)]

lemma law3_mem {m1 ma α p x w b : ℝ} (hα : 1 < α) (hp : 0 ≤ p) (hw : 0 ≤ w) (hpw : p + w ≤ 1)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (e1 : p * x + w * b = m1) (e2 : p * x ^ α + w * b ^ α = ma) :
    law3 p x w b ∈ ambiguitySet m1 ma α := by
  have hP : IsProbabilityMeasure (law3 p x w b) := by
    constructor
    unfold law3
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp hw, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    simp
  refine ⟨hP, ?_, law3_int _, law3_int _, ?_, ?_⟩
  · unfold law3
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ measurableSet_Iio, Measure.dirac_apply' _ measurableSet_Iio,
      Measure.dirac_apply' _ measurableSet_Iio]
    simp [Set.indicator, not_lt.2 hx, not_lt.2 hb]
  · rw [law3_integral hp hw hpw]; linarith
  · rw [law3_integral hp hw hpw, Real.zero_rpow (by linarith)]; linarith

lemma law3_sh {p x w b q : ℝ} (hp : 0 ≤ p) (hw : 0 ≤ w) (hpw : p + w ≤ 1) :
    p * (x - q) ≤ sh (law3 p x w b) q := by
  unfold sh
  rw [law3_integral hp hw hpw]
  have h1 := le_max_left (x - q) 0
  have h2 := le_max_right (b - q) 0
  have h3 := le_max_right (0 - q) 0
  have : 0 ≤ 1 - p - w := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hp, mul_nonneg hw h2, mul_nonneg this h3]

/-- tangent line inequality for rpow -/
lemma tangent {α x0 x : ℝ} (hα : 1 ≤ α) (hx0 : 0 < x0) (hx : 0 ≤ x) :
    x0 ^ α + α * x0 ^ (α - 1) * (x - x0) ≤ x ^ α := by
  have h := one_add_mul_self_le_rpow_one_add (s := x / x0 - 1)
    (by have : 0 ≤ x / x0 := div_nonneg hx hx0.le; linarith) hα
  have e : 1 + (x / x0 - 1) = x / x0 := by ring
  rw [e, Real.div_rpow hx hx0.le] at h
  have hpos : 0 < x0 ^ α := Real.rpow_pos_of_pos hx0 α
  have e2 : x0 ^ α = x0 ^ (α - 1) * x0 := by
    rw [← Real.rpow_add_one hx0.ne']; ring_nf
  rw [le_div_iff₀ hpos] at h
  have : x0 ^ (α - 1) * (x - x0) = x0 ^ α * (x / x0 - 1) := by
    rw [e2]; field_simp
  nlinarith [this]

end HTNV43

namespace HTNV43

lemma rpow_sub_one_mul {y α : ℝ} (hy : 0 < y) : y ^ (α - 1) * y = y ^ α := by
  rw [Real.rpow_sub_one hy.ne']; field_simp

/-- the asymptotic constant -/
noncomputable def kap (α : ℝ) : ℝ := 1 / (α * (α / (α - 1)) ^ (α - 1))

/-- dual (upper) bound -/
lemma dual_sh {m1 ma α q c lam : ℝ} (hα : 1 < α) (hm1 : 0 < m1) (hq : 0 < q) (hc : 1 ≤ c)
    (hlam : lam = c / (α * (q * (α / ((α - 1) * c))) ^ (α - 1)))
    (hcond : 1 + lam * α * m1 ^ (α - 1) ≤ c)
    {F : Measure ℝ} (hF : F ∈ ambiguitySet m1 ma α) : sh F q ≤ lam * (ma - m1 ^ α) := by
  set s := α / ((α - 1) * c) with hs
  have hspos : 0 < s := div_pos (by linarith) (mul_pos (by linarith) (by linarith))
  set x0 := q * s with hx0
  have hx0pos : 0 < x0 := mul_pos hq hspos
  have hpowpos : 0 < x0 ^ (α - 1) := Real.rpow_pos_of_pos hx0pos _
  have hlampos : 0 < lam := by rw [hlam]; positivity
  have hlx : lam * α * x0 ^ (α - 1) = c := by
    rw [hlam]; field_simp
  have hm1pow : 0 < m1 ^ (α - 1) := Real.rpow_pos_of_pos hm1 _
  have hm1a : m1 ^ (α - 1) * m1 = m1 ^ α := rpow_sub_one_mul hm1
  have hx0a : x0 ^ (α - 1) * x0 = x0 ^ α := rpow_sub_one_mul hx0pos
  have hcs : c * s * (α - 1) = α := by
    have h1 : α - 1 ≠ 0 := by linarith
    have h2 : c ≠ 0 := by linarith
    rw [hs]; field_simp
  -- pointwise bound
  have pw : ∀ x : ℝ, 0 ≤ x → max (x - q) 0 ≤
      lam * x ^ α - (lam * α * m1 ^ (α - 1)) * x + lam * ((α - 1) * m1 ^ α) := by
    intro x hx
    have t1 := tangent hα.le hm1 hx
    have t2 := tangent hα.le hx0pos hx
    have h0 : 0 ≤ x ^ α - m1 ^ α - α * m1 ^ (α - 1) * (x - m1) := by linarith
    have hval : lam * x0 ^ α - c * x0 + q = 0 := by
      have : lam * x0 ^ α = c * x0 / α := by
        rw [← hx0a, ← hlx]; field_simp
      rw [this, hx0]
      have hα0 : α ≠ 0 := by linarith
      field_simp
      linear_combination (-q) * hcs
    have hA : 0 ≤ lam * x ^ α - c * x + q := by
      have := mul_le_mul_of_nonneg_left t2 hlampos.le
      nlinarith [hlx]
    refine max_le ?_ ?_
    · have h2 : (1 + lam * α * m1 ^ (α - 1)) * x ≤ c * x := mul_le_mul_of_nonneg_right hcond hx
      have h3 : 0 ≤ lam * ((α - 1) * m1 ^ α) := by
        have : 0 < m1 ^ α := Real.rpow_pos_of_pos hm1 _
        have : 0 < α - 1 := by linarith
        positivity
      nlinarith
    · have := mul_nonneg hlampos.le h0
      nlinarith [hm1a]
  have hF' := hF
  obtain ⟨hP, -, hi1, hia, hm1e, hmae⟩ := hF'
  haveI := hP
  have hint : Integrable (fun w : ℝ =>
      lam * w ^ α - (lam * α * m1 ^ (α - 1)) * w + lam * ((α - 1) * m1 ^ α)) F :=
    ((hia.const_mul lam).sub (hi1.const_mul _)).add (integrable_const _)
  calc sh F q ≤ ∫ w, (lam * w ^ α - (lam * α * m1 ^ (α - 1)) * w + lam * ((α - 1) * m1 ^ α)) ∂F := by
        refine integral_mono_ae (mem_int_sh hF q) hint ?_
        filter_upwards [mem_ae_nonneg hF] with w hw
        exact pw w hw
    _ = lam * (ma - m1 ^ α) := by
        rw [integral_add (f := fun w : ℝ => lam * w ^ α - (lam * α * m1 ^ (α - 1)) * w)
            (g := fun _ => lam * ((α - 1) * m1 ^ α))
            ((hia.const_mul lam).sub (hi1.const_mul _)) (integrable_const _),
          integral_sub (f := fun w : ℝ => lam * w ^ α)
            (g := fun w : ℝ => (lam * α * m1 ^ (α - 1)) * w) (hia.const_mul lam)
            (hi1.const_mul _), integral_const_mul, integral_const_mul, hm1e, hmae]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        linear_combination (-(lam * α)) * hm1a

/-- upper bound on q^(α-1) * worstCase -/
lemma wc_upper {m1 ma α q c : ℝ} (hα : 1 < α) (hm1 : 0 < m1) (hq : 0 < q) (hc : 1 ≤ c)
    (hne : (ambiguitySet m1 ma α).Nonempty)
    (hcond : 1 + c / (α * (q * (α / ((α - 1) * c))) ^ (α - 1)) * α * m1 ^ (α - 1) ≤ c) :
    q ^ (α - 1) * worstCase m1 ma α q ≤
      c / (α * (α / ((α - 1) * c)) ^ (α - 1)) * (ma - m1 ^ α) := by
  have h := wc_le hne q _ fun F hF => dual_sh hα hm1 hq hc rfl hcond hF
  have hqp : 0 < q ^ (α - 1) := Real.rpow_pos_of_pos hq _
  have hspos : 0 < α / ((α - 1) * c) := div_pos (by linarith) (mul_pos (by linarith) (by linarith))
  rw [Real.mul_rpow hq.le hspos.le] at h
  calc q ^ (α - 1) * worstCase m1 ma α q
      ≤ q ^ (α - 1) * (c / (α * (q ^ (α - 1) * (α / ((α - 1) * c)) ^ (α - 1))) *
          (ma - m1 ^ α)) := mul_le_mul_of_nonneg_left h hqp.le
    _ = _ := by field_simp

/-- lower bound on q^(α-1) * worstCase from the three-point law -/
lemma wc_lower {m1 ma α b q : ℝ} (hα : 1 < α) (hm1 : 0 < m1) (hb : m1 < b)
    (hN : 0 < ma - m1 * b ^ (α - 1)) (hq : 0 < q)
    (hx1 : b < α / (α - 1) * q)
    (hx2 : b ^ (α - 1) + (ma - m1 * b ^ (α - 1)) / m1 ≤ (α / (α - 1) * q) ^ (α - 1)) :
    (ma - m1 * b ^ (α - 1)) * kap α ≤ q ^ (α - 1) * worstCase m1 ma α q := by
  set r := α / (α - 1) with hr
  set x := r * q with hx
  set N := ma - m1 * b ^ (α - 1) with hNdef
  have hα1 : 0 < α - 1 := by linarith
  have hbpos : 0 < b := by linarith
  have hrpos : 1 < r := by rw [hr, lt_div_iff₀ hα1]; linarith
  have hxpos : 0 < x := by linarith
  have hxa : x ^ (α - 1) * x = x ^ α := rpow_sub_one_mul hxpos
  have hba : b ^ (α - 1) * b = b ^ α := rpow_sub_one_mul hbpos
  have hbx : b ^ (α - 1) < x ^ (α - 1) := Real.rpow_lt_rpow hbpos.le hx1 hα1
  have hbp : 0 < b ^ (α - 1) := Real.rpow_pos_of_pos hbpos _
  set dd := x ^ (α - 1) - b ^ (α - 1) with hdd
  have hddpos : 0 < dd := by linarith
  set p := N / (x * dd) with hp
  have hppos : 0 < p := div_pos hN (mul_pos hxpos hddpos)
  have hpx : p * x = N / dd := by rw [hp]; field_simp
  have hpx_le : p * x ≤ m1 := by
    rw [hpx, div_le_iff₀ hddpos]
    have : N / m1 ≤ dd := by linarith
    rw [div_le_iff₀ hm1] at this; linarith
  set w := (m1 - p * x) / b with hw
  have hw0 : 0 ≤ w := div_nonneg (by linarith) hbpos.le
  have hwb : w * b = m1 - p * x := by rw [hw]; field_simp
  have hpw : p + w ≤ 1 := by
    have h1 : p * b ≤ p * x := mul_le_mul_of_nonneg_left hx1.le hppos.le
    have h2 : (p + w) * b ≤ 1 * b := by nlinarith
    exact le_of_mul_le_mul_right h2 hbpos
  have e1 : p * x + w * b = m1 := by rw [hwb]; ring
  have e2 : p * x ^ α + w * b ^ α = ma := by
    rw [← hba, ← hxa]
    have : p * (x * dd) = N := by rw [hp]; field_simp
    have h3 : w * (b ^ (α - 1) * b) = (m1 - p * x) * b ^ (α - 1) := by rw [← hwb]; ring
    rw [h3]; rw [hdd] at this; rw [hNdef] at this; linear_combination this
  have hmem := law3_mem hα hppos.le hw0 hpw hxpos.le hbpos.le e1 e2
  have hlow : p * (x - q) ≤ worstCase m1 ma α q :=
    (law3_sh hppos.le hw0 hpw).trans (le_wc hmem q)
  have hqp : 0 < q ^ (α - 1) := Real.rpow_pos_of_pos hq _
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hlow hqp.le)
  -- algebra: q^(α-1) * p * (x - q) ≥ N * kap α
  have hqa : q ^ (α - 1) * q = q ^ α := rpow_sub_one_mul hq
  have hxr : x ^ (α - 1) = r ^ (α - 1) * q ^ (α - 1) := by
    rw [hx, Real.mul_rpow (by linarith) hq.le]
  have hrp : 0 < r ^ (α - 1) := Real.rpow_pos_of_pos (by linarith) _
  have hdd_le : dd ≤ x ^ (α - 1) := by linarith
  -- p*(x-q) ≥ N*(x-q)/(x * x^(α-1))
  have key : N * (x - q) / (x * x ^ (α - 1)) ≤ p * (x - q) := by
    rw [hp, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_left (mul_nonneg hN.le (by nlinarith)) (mul_pos hxpos hddpos)
    exact mul_le_mul_of_nonneg_left hdd_le hxpos.le
  refine le_trans ?_ (mul_le_mul_of_nonneg_left key hqp.le)
  rw [hxr, kap, ← hr]
  apply le_of_eq
  rw [hx]
  have hrr : r * (α - 1) = α := by rw [hr]; field_simp
  field_simp
  nlinarith [hrr]

end HTNV43

namespace HTNV43

lemma amb_nonempty {m1 ma α : ℝ} (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    (ambiguitySet m1 ma α).Nonempty := by
  have hα1 : 0 < α - 1 := by linarith
  have hmapos : 0 < ma := lt_of_le_of_lt (Real.rpow_nonneg hm1.le _) hma
  set b := (ma / m1) ^ (α - 1)⁻¹ with hb
  have hbpos : 0 < b := Real.rpow_pos_of_pos (div_pos hmapos hm1) _
  have hbb : b ^ (α - 1) = ma / m1 := Real.rpow_inv_rpow (div_pos hmapos hm1).le hα1.ne'
  have hm1a : m1 ^ (α - 1) * m1 = m1 ^ α := rpow_sub_one_mul hm1
  have hba : b ^ (α - 1) * b = b ^ α := rpow_sub_one_mul hbpos
  have hlt : m1 ^ (α - 1) < b ^ (α - 1) := by
    rw [hbb, lt_div_iff₀ hm1]; linarith
  have hmb : m1 < b := (Real.rpow_lt_rpow_iff hm1.le hbpos.le hα1).1 hlt
  refine ⟨law3 0 0 (m1 / b) b, law3_mem hα le_rfl (div_nonneg hm1.le hbpos.le)
    (by rw [zero_add, div_le_one hbpos]; exact hmb.le) le_rfl hbpos.le
    (by field_simp; ring) ?_⟩
  rw [← hba, hbb]; field_simp; ring_nf

lemma wc_tendsto {m1 ma α : ℝ} (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    Tendsto (fun q => q ^ (α - 1) * worstCase m1 ma α q) atTop
      (nhds (kap α * (ma - m1 ^ α))) := by
  have hα1 : 0 < α - 1 := by linarith
  have hne := amb_nonempty hα hm1 hma
  have hD : 0 < ma - m1 ^ α := by linarith
  have hm1a : m1 ^ (α - 1) * m1 = m1 ^ α := rpow_sub_one_mul hm1
  have hr : 0 < α / (α - 1) := div_pos (by linarith) hα1
  have hkap : 0 < kap α := by
    unfold kap; have := Real.rpow_pos_of_pos hr (α - 1); positivity
  rw [tendsto_order]
  constructor
  · intro a ha
    -- choose b slightly above m1
    have hcont : ContinuousAt (fun b : ℝ => (ma - m1 * b ^ (α - 1)) * kap α) m1 := by
      refine ((continuousAt_const.sub (continuousAt_const.mul ?_)).mul continuousAt_const)
      exact Real.continuousAt_rpow_const _ _ (Or.inl hm1.ne')
    have hval : (ma - m1 * m1 ^ (α - 1)) * kap α = kap α * (ma - m1 ^ α) := by
      rw [mul_comm m1, hm1a]; ring
    have ev1 : ∀ᶠ b in nhds m1, a < (ma - m1 * b ^ (α - 1)) * kap α :=
      hcont.eventually (lt_mem_nhds (by show a < (ma - m1 * m1 ^ (α - 1)) * kap α; rw [hval]; exact ha))
    have ev2 : ∀ᶠ b in nhds m1, 0 < ma - m1 * b ^ (α - 1) := by
      have hc2 : ContinuousAt (fun b : ℝ => ma - m1 * b ^ (α - 1)) m1 :=
        continuousAt_const.sub (continuousAt_const.mul
          (Real.continuousAt_rpow_const _ _ (Or.inl hm1.ne')))
      exact hc2.eventually (lt_mem_nhds (by show 0 < ma - m1 * m1 ^ (α - 1); rw [mul_comm m1, hm1a]; exact hD))
    obtain ⟨b, ⟨hb1, hb2⟩, hb3⟩ :=
      ((ev1.and ev2).filter_mono nhdsWithin_le_nhds |>.and
        (self_mem_nhdsWithin : Ioi m1 ∈ nhdsWithin m1 (Ioi m1))).exists
    have hb3' : m1 < b := hb3
    have hT : Tendsto (fun q : ℝ => (α / (α - 1) * q) ^ (α - 1)) atTop atTop :=
      (tendsto_rpow_atTop hα1).comp (tendsto_id.const_mul_atTop hr)
    filter_upwards [hT.eventually_ge_atTop (b ^ (α - 1) + (ma - m1 * b ^ (α - 1)) / m1),
      (tendsto_id.const_mul_atTop hr).eventually_gt_atTop b, eventually_gt_atTop 0]
      with q hq2 hq1 hq0
    exact lt_of_lt_of_le hb1 (wc_lower hα hm1 hb3' hb2 hq0 hq1 hq2)
  · intro a ha
    set U : ℝ → ℝ := fun c => c / (α * (α / ((α - 1) * c)) ^ (α - 1)) with hU
    have hcont : ContinuousAt (fun c => U c * (ma - m1 ^ α)) 1 := by
      refine ContinuousAt.mul ?_ continuousAt_const
      refine continuousAt_id.div (continuousAt_const.mul ?_) ?_
      · refine ContinuousAt.rpow_const ?_ (Or.inl (by simp only [id, mul_one]; exact hr.ne'))
        exact continuousAt_const.div (continuousAt_const.mul continuousAt_id)
          (by simp only [id, mul_one]; exact hα1.ne')
      · rw [mul_one]; have := Real.rpow_pos_of_pos hr (α - 1); have : 0 < α := by linarith
        positivity
    have hval : U 1 * (ma - m1 ^ α) = kap α * (ma - m1 ^ α) := by
      simp [hU, kap]
    have ev1 : ∀ᶠ c in nhds (1 : ℝ), U c * (ma - m1 ^ α) < a :=
      hcont.eventually (gt_mem_nhds (by show U 1 * (ma - m1 ^ α) < a; rw [hval]; exact ha))
    obtain ⟨c, hc1, hc2⟩ := (ev1.filter_mono nhdsWithin_le_nhds |>.and
        (self_mem_nhdsWithin : Ioi (1 : ℝ) ∈ nhdsWithin 1 (Ioi 1))).exists
    have hc2' : 1 < c := hc2
    have hs : 0 < α / ((α - 1) * c) := div_pos (by linarith) (mul_pos hα1 (by linarith))
    -- the condition holds for large q
    have hT : Tendsto (fun q : ℝ => (q * (α / ((α - 1) * c))) ^ (α - 1)) atTop atTop :=
      (tendsto_rpow_atTop hα1).comp (tendsto_id.atTop_mul_const hs)
    have hm1p : 0 < m1 ^ (α - 1) := Real.rpow_pos_of_pos hm1 _
    filter_upwards [hT.eventually_ge_atTop (c * α * m1 ^ (α - 1) / (α * (c - 1))),
      eventually_gt_atTop 0] with q hq1 hq0
    refine lt_of_le_of_lt (wc_upper hα hm1 hq0 hc2'.le hne ?_) hc1
    set X := (q * (α / ((α - 1) * c))) ^ (α - 1) with hX
    have hXpos : 0 < X := Real.rpow_pos_of_pos (mul_pos hq0 hs) _
    have hαpos : 0 < α := by linarith
    have hc1' : 0 < c - 1 := by linarith
    rw [div_le_iff₀ (by positivity)] at hq1
    have : c / (α * X) * α * m1 ^ (α - 1) = c * m1 ^ (α - 1) / X := by
      field_simp
    rw [this]
    have h5 : c * m1 ^ (α - 1) / X ≤ c - 1 := by
      rw [div_le_iff₀ hXpos]; nlinarith
    linarith

/-- regular variation from a power-law limit -/
lemma rv_of_tendsto {u : ℝ → ℝ} {β L : ℝ} (hL : 0 < L)
    (h : Tendsto (fun x => x ^ β * u x) atTop (nhds L)) : IsRegularlyVarying u (-β) := by
  have hpos : ∀ᶠ x in atTop, 0 < u x := by
    filter_upwards [h.eventually (lt_mem_nhds hL), eventually_gt_atTop 0] with x hx hx0
    have := Real.rpow_pos_of_pos hx0 β
    exact pos_of_mul_pos_right hx this.le
  refine ⟨hpos, fun t ht => ?_⟩
  have h2 : Tendsto (fun x => (t * x) ^ β * u (t * x)) atTop (nhds L) :=
    h.comp (tendsto_id.const_mul_atTop ht)
  have h3 := (h2.div h hL.ne').mul_const (t ^ (-β))
  rw [div_self hL.ne', one_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hpos] with x hx0 hux
  have htb : 0 < t ^ β := Real.rpow_pos_of_pos ht β
  have hxb : 0 < x ^ β := Real.rpow_pos_of_pos hx0 β
  show (t * x) ^ β * u (t * x) / (x ^ β * u x) * t ^ (-β) = u (t * x) / u x
  rw [Real.mul_rpow ht.le hx0.le, Real.rpow_neg ht.le]
  field_simp

lemma wc_rv {m1 ma α : ℝ} (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    IsRegularlyVarying (worstCase m1 ma α) (-(α - 1)) := by
  have hD : 0 < ma - m1 ^ α := by linarith
  have hr : 0 < α / (α - 1) := div_pos (by linarith) (by linarith)
  have hkap : 0 < kap α := by
    unfold kap; have := Real.rpow_pos_of_pos hr (α - 1); have : 0 < α := by linarith
    positivity
  exact rv_of_tendsto (mul_pos hkap hD) (wc_tendsto hα hm1 hma)

end HTNV43

namespace HTNV43

/-- hypotheses on the shortage curve used to build the representing law -/
def Good (P : ℝ → ℝ) (m : ℝ) : Prop :=
  ConvexOn ℝ univ P ∧ Antitone P ∧ (∀ x y : ℝ, x ≤ y → P x ≤ P y + (y - x)) ∧
    (∀ q : ℝ, q ≤ 0 → P q = m - q) ∧ Tendsto P atTop (nhds 0)

/-- right derivative -/
noncomputable def rD (P : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin P (Ioi x) x

section good
variable {P : ℝ → ℝ} {m : ℝ}

lemma good_hasD (h : Good P m) (x : ℝ) : HasDerivWithinAt P (rD P x) (Ioi x) x :=
  h.1.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)

lemma rD_le (h : Good P m) {x y : ℝ} (hxy : x < y) : rD P x ≤ (P y - P x) / (y - x) := by
  have := h.1.le_slope_of_hasDerivWithinAt_Ioi (mem_univ x) (mem_univ y) hxy (good_hasD h x)
  rwa [slope_def_field] at this

lemma le_rD (h : Good P m) {x y : ℝ} (hyx : y < x) : (P x - P y) / (x - y) ≤ rD P x := by
  have h1 := h.1.slope_le_leftDeriv (mem_univ y) (mem_univ x) hyx
    (h.1.differentiableWithinAt_Iio_of_mem_interior (by simp))
  have h2 := h.1.leftDeriv_le_rightDeriv_of_mem_interior (x := x) (by simp)
  rw [slope_def_field] at h1
  exact h1.trans h2

lemma rD_mono (h : Good P m) : Monotone (rD P) := fun x y hxy =>
  h.1.monotoneOn_rightDeriv (by simp) (by simp) hxy

lemma rD_nonpos (h : Good P m) (x : ℝ) : rD P x ≤ 0 := by
  have := rD_le h (lt_add_one x)
  have h2 := h.2.1 (le_of_lt (lt_add_one x))
  rw [add_sub_cancel_left, div_one] at this; linarith

lemma rD_ge (h : Good P m) (x : ℝ) : -1 ≤ rD P x := by
  have := le_rD h (sub_one_lt x)
  have h2 := h.2.2.1 (x - 1) x (sub_one_lt x).le
  rw [sub_sub_cancel, div_one] at this; linarith

lemma rD_neg (h : Good P m) {x : ℝ} (hx : x < 0) : rD P x = -1 := by
  refine le_antisymm ?_ (rD_ge h x)
  have := rD_le h (show x < x / 2 by linarith)
  rw [h.2.2.2.1 x hx.le, h.2.2.2.1 (x / 2) (by linarith)] at this
  have e : (m - x / 2 - (m - x)) / (x / 2 - x) = -1 := by
    have : x / 2 - x ≠ 0 := by linarith
    have hx0 : x ≠ 0 := hx.ne
    field_simp; ring
  linarith

lemma rD_tendsto (h : Good P m) : Tendsto (rD P) atTop (nhds 0) := by
  have hl : Tendsto (fun x => P x - P (x + -1)) atTop (nhds 0) := by
    have := h.2.2.2.2.sub (h.2.2.2.2.comp (tendsto_atTop_add_const_right atTop (-1) tendsto_id))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun x => ?_)
    (fun x => rD_nonpos h x)
  have := le_rD h (show x + -1 < x by linarith)
  rwa [show x - (x + -1) = 1 by ring, div_one] at this

lemma good_cont (h : Good P m) : Continuous P := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total x y with hxy | hxy
  · have := h.2.1 hxy; have := h.2.2.1 x y hxy
    rw [abs_le]; constructor <;> [skip; skip] <;> (rw [abs_of_nonpos (by linarith)]) <;> linarith
  · have := h.2.1 hxy; have := h.2.2.1 y x hxy
    rw [abs_le]; constructor <;> (rw [abs_of_nonneg (by linarith)]) <;> linarith

lemma rD_rc (h : Good P m) (x : ℝ) : ContinuousWithinAt (rD P) (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  show Tendsto (rD P) (nhdsWithin x (Ioi x)) (nhds (rD P x))
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact lt_of_lt_of_le ha (rD_mono h (le_of_lt hy))
  · intro a ha
    have hs := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 (good_hasD h x)
    have ev := hs.eventually (gt_mem_nhds (show rD P x < (rD P x + a) / 2 by linarith))
    obtain ⟨z, hz1, hz2⟩ := (ev.and self_mem_nhdsWithin).exists
    have hz2' : x < z := hz2
    rw [slope_def_field] at hz1
    have hφ : ContinuousAt (fun y => (P z - P y) / (z - y)) x :=
      (continuousAt_const.sub (good_cont h).continuousAt).div
        (continuousAt_const.sub continuousAt_id) (by simp; linarith)
    have ev2 : ∀ᶠ y in nhds x, (P z - P y) / (z - y) < a :=
      hφ.eventually (gt_mem_nhds (show (P z - P x) / (z - x) < a by linarith))
    filter_upwards [ev2.filter_mono nhdsWithin_le_nhds, Ioo_mem_nhdsGT hz2'] with y hy1 hy2
    exact lt_of_le_of_lt (rD_le h hy2.2) hy1

/-- the Stieltjes function `1 + rD P` -/
noncomputable def Gs (h : Good P m) : StieltjesFunction ℝ where
  toFun x := 1 + rD P x
  mono' _ _ hxy := by simp only; linarith [rD_mono h hxy]
  right_continuous' x := continuousWithinAt_const.add (rD_rc h x)

lemma Gs_apply (h : Good P m) (x : ℝ) : Gs h x = 1 + rD P x := rfl

lemma Gs_bot (h : Good P m) : Tendsto (Gs h) atBot (nhds 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with x hx
  rw [Gs_apply, rD_neg h hx]; ring

lemma Gs_top (h : Good P m) : Tendsto (Gs h) atTop (nhds 1) := by
  have := (rD_tendsto h).const_add 1
  rw [add_zero] at this
  exact this

lemma Fs_prob (h : Good P m) : IsProbabilityMeasure (Gs h).measure :=
  (Gs h).isProbabilityMeasure (Gs_bot h) (Gs_top h)

lemma Fs_Ioi (h : Good P m) (x : ℝ) : (Gs h).measure (Ioi x) = ENNReal.ofReal (-rD P x) := by
  rw [(Gs h).measure_Ioi (Gs_top h), Gs_apply]; ring_nf

lemma Fs_Iio (h : Good P m) : (Gs h).measure (Iio 0) = 0 := by
  have e : Iio (0 : ℝ) = ⋃ n : ℕ, Iic (-(1 / ((n : ℝ) + 1))) := by
    ext x
    simp only [mem_Iio, mem_iUnion, mem_Iic]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [e]
  refine measure_iUnion_null fun n => ?_
  have hn : -(1 / ((n : ℝ) + 1)) < 0 := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  rw [(Gs h).measure_Iic (Gs_bot h), Gs_apply, rD_neg h hn]
  simp

lemma good_nonneg (h : Good P m) (b : ℝ) : 0 ≤ P b :=
  le_of_tendsto h.2.2.2.2 (by
    filter_upwards [eventually_ge_atTop b] with y hy
    exact h.2.1 hy)

lemma ftc_Ioi (h : Good P m) (q : ℝ) :
    IntegrableOn (fun s => -rD P s) (Ioi q) ∧ ∫ s in Ioi q, -rD P s = P q := by
  have hint : ∀ b, IntervalIntegrable (fun s => -rD P s) volume q b := fun b =>
    ((rD_mono h).intervalIntegrable).neg
  have hftc : ∀ b, q ≤ b → ∫ s in q..b, -rD P s = P q - P b := by
    intro b hb
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb
        (good_cont h).continuousOn (fun x _ => good_hasD h x) ((rD_mono h).intervalIntegrable)]
    ring
  have hIO : IntegrableOn (fun s => -rD P s) (Ioi q) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (P q) q
      (fun i => (hint i).1) tendsto_id ?_
    filter_upwards [eventually_ge_atTop q] with b hb
    have e : ∫ x in q..b, ‖-rD P x‖ = ∫ x in q..b, -rD P x := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [norm_neg, Real.norm_eq_abs]
      rw [abs_of_nonpos (rD_nonpos h x)]
    rw [e, hftc b hb]
    linarith [good_nonneg h b]
  refine ⟨hIO, ?_⟩
  have t1 := intervalIntegral_tendsto_integral_Ioi q hIO tendsto_id
  have t2 : Tendsto (fun b => ∫ s in q..id b, -rD P s) atTop (nhds (P q)) := by
    have : Tendsto (fun b => P q - P b) atTop (nhds (P q)) := by
      simpa using (tendsto_const_nhds (x := P q)).sub h.2.2.2.2
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop q] with b hb
    exact (hftc b hb).symm
  exact tendsto_nhds_unique t1 t2

end good

end HTNV43

namespace HTNV43

section good2
variable {P : ℝ → ℝ} {m : ℝ}

lemma Fs_real_Ioi (h : Good P m) (x : ℝ) : (Gs h).measure.real (Ioi x) = -rD P x := by
  rw [measureReal_def, Fs_Ioi h, ENNReal.toReal_ofReal (by linarith [rD_nonpos h x])]

lemma Fs_ae_nonneg (h : Good P m) : ∀ᵐ w ∂(Gs h).measure, 0 ≤ w := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
  rw [this]; exact Fs_Iio h

lemma shift_lint (g : ℝ → ENNReal) (q : ℝ) :
    ∫⁻ t in Ioi 0, g (t + q) = ∫⁻ s in Ioi q, g s := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  have e : (Ioi (0:ℝ)).indicator (fun t => g (t + q)) = fun t => (Ioi q).indicator g (t + q) := by
    ext t
    simp only [Set.indicator_apply, mem_Ioi, lt_add_iff_pos_left]
  rw [e, lintegral_add_right_eq_self (fun s => (Ioi q).indicator g s) q]

lemma Fs_sh_lint (h : Good P m) (q : ℝ) :
    ∫⁻ w, ENNReal.ofReal (max (w - q) 0) ∂(Gs h).measure = ENNReal.ofReal (P q) := by
  rw [lintegral_eq_lintegral_meas_lt _
    (ae_of_all _ fun w => show (0:ℝ) ≤ max (w - q) 0 from le_max_right _ _)
    ((measurable_id.sub_const q).max measurable_const).aemeasurable]
  have e1 : ∫⁻ t in Ioi 0, (Gs h).measure {a | t < max (a - q) 0} =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (-rD P (t + q)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : 0 < t := ht
    have : {a : ℝ | t < max (a - q) 0} = Ioi (t + q) := by
      ext a; simp only [mem_setOf_eq, mem_Ioi, lt_max_iff]
      constructor
      · rintro (h1 | h1) <;> linarith
      · intro h1; left; linarith
    rw [this, Fs_Ioi h]
  rw [e1, shift_lint (fun s => ENNReal.ofReal (-rD P s)) q]
  obtain ⟨hI, hv⟩ := ftc_Ioi h q
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (ae_of_all _ fun s => show (0:ℝ) ≤ -rD P s by linarith [rD_nonpos h s]), hv]

lemma Fs_sh (h : Good P m) (q : ℝ) :
    Integrable (fun w : ℝ => max (w - q) 0) (Gs h).measure ∧
      (∫ w, max (w - q) 0 ∂(Gs h).measure) = P q := by
  have hm : Measurable (fun w : ℝ => max (w - q) 0) :=
    (measurable_id.sub_const q).max measurable_const
  have hnn : 0 ≤ᵐ[(Gs h).measure] (fun w : ℝ => max (w - q) 0) :=
    ae_of_all _ fun w => show (0:ℝ) ≤ max (w - q) 0 from le_max_right _ _
  refine ⟨⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩, ?_⟩
  · rw [Fs_sh_lint h q]; exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable, Fs_sh_lint h q,
      ENNReal.toReal_ofReal (good_nonneg h q)]

lemma rD_asym (h : Good P m) {β L : ℝ} (hβ : 0 < β)
    (hlim : Tendsto (fun x => x ^ β * P x) atTop (nhds L)) :
    Tendsto (fun x => x ^ (β + 1) * (-rD P x)) atTop (nhds (β * L)) := by
  have hd : HasDerivAt (fun t : ℝ => t ^ (-β)) (-β) 1 := by
    have := Real.hasDerivAt_rpow_const (x := 1) (p := -β) (Or.inl one_ne_zero)
    simpa using this
  have hs : Tendsto (fun t => -L * slope (fun t : ℝ => t ^ (-β)) 1 t) (nhdsWithin 1 {1}ᶜ)
      (nhds (β * L)) := by
    have := (hd.tendsto_slope).const_mul (-L)
    convert this using 2; ring
  have hE : ∀ t : ℝ, 0 < t → Tendsto (fun x => (x ^ β * P x - x ^ β * P (t * x)) / (t - 1))
      atTop (nhds (-L * slope (fun t : ℝ => t ^ (-β)) 1 t)) := by
    intro t ht
    have h1 : Tendsto (fun x => x ^ β * P x - t ^ (-β) * ((t * x) ^ β * P (t * x))) atTop
        (nhds (L - t ^ (-β) * L)) :=
      hlim.sub ((hlim.comp (tendsto_id.const_mul_atTop ht)).const_mul _)
    have h2 := h1.div_const (t - 1)
    rw [slope_def_field, Real.one_rpow,
      show -L * ((t ^ (-β) - 1) / (t - 1)) = (L - t ^ (-β) * L) / (t - 1) by ring]
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have key : t ^ (-β) * (t * x) ^ β = x ^ β := by
      rw [Real.mul_rpow ht.le hx.le, ← mul_assoc, ← Real.rpow_add ht, neg_add_cancel,
        Real.rpow_zero, one_mul]
    linear_combination (-(P (t * x) / (t - 1))) * key
  have hlow : ∀ t : ℝ, 1 < t → ∀ x : ℝ, 0 < x →
      (x ^ β * P x - x ^ β * P (t * x)) / (t - 1) ≤ x ^ (β + 1) * (-rD P x) := by
    intro t ht x hx
    have h1 := rD_le h (show x < t * x by nlinarith)
    have hxb : 0 < x ^ β := Real.rpow_pos_of_pos hx β
    rw [Real.rpow_add hx, Real.rpow_one, div_le_iff₀ (by linarith)]
    rw [le_div_iff₀ (by nlinarith)] at h1
    have := mul_le_mul_of_nonneg_left h1 hxb.le
    nlinarith
  have hup : ∀ t : ℝ, 0 < t → t < 1 → ∀ x : ℝ, 0 < x →
      x ^ (β + 1) * (-rD P x) ≤ (x ^ β * P x - x ^ β * P (t * x)) / (t - 1) := by
    intro t ht0 ht x hx
    have h1 := le_rD h (show t * x < x by nlinarith)
    have hxb : 0 < x ^ β := Real.rpow_pos_of_pos hx β
    rw [Real.rpow_add hx, Real.rpow_one, le_div_iff_of_neg (by linarith)]
    rw [div_le_iff₀ (by nlinarith)] at h1
    have := mul_le_mul_of_nonneg_left h1 hxb.le
    nlinarith
  rw [tendsto_order]
  constructor
  · intro a ha
    have hsub : Ioi (1:ℝ) ⊆ {1}ᶜ := by
      intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt (mem_Ioi.1 ht)
    have hev : ∀ᶠ t in nhdsWithin 1 (Ioi 1), a < -L * slope (fun t : ℝ => t ^ (-β)) 1 t :=
      (hs.mono_left (nhdsWithin_mono _ hsub)).eventually (lt_mem_nhds ha)
    obtain ⟨t, ht1, ht2⟩ := (hev.and self_mem_nhdsWithin).exists
    have ht2' : 1 < t := ht2
    filter_upwards [(hE t (by linarith)).eventually (lt_mem_nhds ht1), eventually_gt_atTop 0]
      with x hx1 hx2
    exact lt_of_lt_of_le hx1 (hlow t ht2' x hx2)
  · intro a ha
    have hsub : Ioo (0:ℝ) 1 ⊆ {1}ᶜ := by
      intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_lt ht.2
    have hmem : Ioo (0:ℝ) 1 ∈ nhdsWithin (1:ℝ) (Ioo 0 1) := self_mem_nhdsWithin
    have hev : ∀ᶠ t in nhdsWithin 1 (Ioo 0 1),
        -L * slope (fun t : ℝ => t ^ (-β)) 1 t < a :=
      (hs.mono_left (nhdsWithin_mono _ hsub)).eventually (gt_mem_nhds ha)
    have hne : (nhdsWithin (1:ℝ) (Ioo 0 1)).NeBot := by
      exact right_nhdsWithin_Ioo_neBot (by norm_num)
    obtain ⟨t, ht1, ht2⟩ := (hev.and hmem).exists
    have ht0 : 0 < t := ht2.1
    have ht2' : t < 1 := ht2.2
    filter_upwards [(hE t ht0).eventually (gt_mem_nhds ht1), eventually_gt_atTop 0]
      with x hx1 hx2
    exact lt_of_le_of_lt (hup t ht0 ht2' x hx2) hx1

end good2

end HTNV43

namespace HTNV43

section good3
variable {P : ℝ → ℝ} {m : ℝ}

lemma Fs_moment (h : Good P m) {a : ℝ} (ha : 0 < a) :
    ∫⁻ w, ENNReal.ofReal (w ^ a) ∂(Gs h).measure =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (-rD P t * (a * t ^ (a - 1))) := by
  have hg : ∀ t > (0:ℝ), IntervalIntegrable (fun s : ℝ => a * s ^ (a - 1)) volume 0 t :=
    fun t _ => (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul a
  have hgnn : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), 0 ≤ a * t ^ (a - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg ha.le (Real.rpow_nonneg (le_of_lt ht) _)
  have hnn : 0 ≤ᵐ[(Gs h).measure] (id : ℝ → ℝ) := by
    filter_upwards [Fs_ae_nonneg h] with w hw
    exact hw
  have key := lintegral_comp_eq_lintegral_meas_lt_mul (Gs h).measure hnn
    measurable_id.aemeasurable hg hgnn
  have e1 : ∀ w : ℝ, 0 ≤ w → ∫ s in (0:ℝ)..w, a * s ^ (a - 1) = w ^ a := by
    intro w _
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
      Real.zero_rpow ha.ne', sub_zero]
    field_simp
  have e2 : ∫⁻ w, ENNReal.ofReal (w ^ a) ∂(Gs h).measure =
      ∫⁻ w, ENNReal.ofReal (∫ s in (0:ℝ)..id w, a * s ^ (a - 1)) ∂(Gs h).measure := by
    refine lintegral_congr_ae ?_
    filter_upwards [Fs_ae_nonneg h] with w hw
    rw [id, e1 w hw]
  rw [e2, key]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [show {x : ℝ | t < id x} = Ioi t from rfl, Fs_Ioi h,
    ← ENNReal.ofReal_mul (by linarith [rD_nonpos h t])]

lemma Fs_moment_fin (h : Good P m) {a α K X : ℝ} (ha : 0 < a) (haα : a < α) (hX : 0 < X)
    (hK : ∀ t, X ≤ t → -rD P t ≤ K * t ^ (-α)) :
    ∫⁻ w, ENNReal.ofReal (w ^ a) ∂(Gs h).measure < ⊤ := by
  rw [Fs_moment h ha]
  have hsub : Ioi (0:ℝ) ⊆ Ioc 0 X ∪ Ioi X := fun t ht => by
    rcases le_or_gt t X with h1 | h1
    · exact Or.inl ⟨ht, h1⟩
    · exact Or.inr h1
  refine lt_of_le_of_lt ((lintegral_mono_set hsub).trans (lintegral_union_le _ _ _))
    (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
  · refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc
      (g := fun t => ENNReal.ofReal (a * t ^ (a - 1))) fun t ht => ?_) ?_
    · apply ENNReal.ofReal_le_ofReal
      have h1 := rD_ge h t
      have h2 := rD_nonpos h t
      have : 0 ≤ a * t ^ (a - 1) := mul_nonneg ha.le (Real.rpow_nonneg ht.1.le _)
      nlinarith
    · have hI : IntegrableOn (fun t : ℝ => a * t ^ (a - 1)) (Ioc 0 X) := by
        have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := X) (r := a - 1)
          (by linarith)).const_mul a
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hX.le).1 this
      exact hI.lintegral_lt_top
  · refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi
      (g := fun t => ENNReal.ofReal (K * a * t ^ (a - 1 - α))) fun t ht => ?_) ?_
    · apply ENNReal.ofReal_le_ofReal
      have ht' : 0 < t := lt_trans hX ht
      have h1 := hK t (le_of_lt ht)
      have e : t ^ (a - 1 - α) = t ^ (-α) * t ^ (a - 1) := by
        rw [← Real.rpow_add ht']; ring_nf
      rw [e]
      have : 0 ≤ a * t ^ (a - 1) := mul_nonneg ha.le (Real.rpow_nonneg ht'.le _)
      nlinarith
    · have hI : IntegrableOn (fun t : ℝ => K * a * t ^ (a - 1 - α)) (Ioi X) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) hX).const_mul (K * a)
      exact hI.lintegral_lt_top

lemma Fs_moment_inf (h : Good P m) {a α c X : ℝ} (ha : 0 < a) (haα : α ≤ a) (hX : 0 < X)
    (hc : 0 < c) (hc' : ∀ t, X ≤ t → c * t ^ (-α) ≤ -rD P t) :
    ∫⁻ w, ENNReal.ofReal (w ^ a) ∂(Gs h).measure = ⊤ := by
  rw [Fs_moment h ha, eq_top_iff]
  have hni : ¬ IntegrableOn (fun t : ℝ => t ^ (a - 1 - α)) (Ioi X) := by
    rw [integrableOn_Ioi_rpow_iff hX]; linarith
  have htop : ∫⁻ t in Ioi X, ENNReal.ofReal (t ^ (a - 1 - α)) = ⊤ := by
    by_contra hne
    apply hni
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi X)] (fun t : ℝ => t ^ (a - 1 - α)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (hX.le.trans (le_of_lt ht)) _
    exact ⟨(measurable_id.pow_const (a - 1 - α)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).2 (lt_top_iff_ne_top.2 hne)⟩
  have hca : ENNReal.ofReal (c * a) ≠ 0 := (ENNReal.ofReal_pos.2 (mul_pos hc ha)).ne'
  calc (⊤ : ENNReal) = ENNReal.ofReal (c * a) * ∫⁻ t in Ioi X, ENNReal.ofReal (t ^ (a - 1 - α)) := by
        rw [htop, ENNReal.mul_top hca]
    _ = ∫⁻ t in Ioi X, ENNReal.ofReal (c * a) * ENNReal.ofReal (t ^ (a - 1 - α)) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ t in Ioi X, ENNReal.ofReal (-rD P t * (a * t ^ (a - 1))) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        have ht' : 0 < t := lt_trans hX ht
        rw [← ENNReal.ofReal_mul (mul_pos hc ha).le]
        apply ENNReal.ofReal_le_ofReal
        have h1 := hc' t (le_of_lt ht)
        have e : t ^ (a - 1 - α) = t ^ (-α) * t ^ (a - 1) := by
          rw [← Real.rpow_add ht']; ring_nf
        rw [e]
        have : 0 ≤ a * t ^ (a - 1) := mul_nonneg ha.le (Real.rpow_nonneg ht'.le _)
        nlinarith
    _ ≤ _ := lintegral_mono_set (Ioi_subset_Ioi hX.le)

lemma Fs_moments (h : Good P m) {α Lt : ℝ} (hα : 0 < α) (hLt : 0 < Lt)
    (hasym : Tendsto (fun x => x ^ α * (-rD P x)) atTop (nhds Lt)) :
    (∀ a : ℝ, 0 ≤ a → a < α → ∫⁻ w, ENNReal.ofReal (w ^ a) ∂(Gs h).measure < ⊤) ∧
    (∀ a : ℝ, α ≤ a → ∫⁻ w, ENNReal.ofReal (w ^ a) ∂(Gs h).measure = ⊤) := by
  haveI := Fs_prob h
  obtain ⟨X1, hX1⟩ := eventually_atTop.1 (hasym.eventually (gt_mem_nhds (lt_add_one Lt)))
  obtain ⟨X2, hX2⟩ := eventually_atTop.1 (hasym.eventually (lt_mem_nhds (half_lt_self hLt)))
  have hpow : ∀ t : ℝ, 0 < t → t ^ (-α) * t ^ α = 1 := fun t ht => by
    rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero]
  have hX : (0:ℝ) < max (max X1 X2) 1 := lt_max_of_lt_right one_pos
  constructor
  · intro a ha0 haα
    rcases ha0.eq_or_lt with rfl | ha
    · simp
    · refine Fs_moment_fin h ha haα hX (K := Lt + 1) fun t ht => ?_
      have ht0 : 0 < t := lt_of_lt_of_le hX ht
      have h1 := hX1 t (((le_max_left _ _).trans (le_max_left _ _)).trans ht)
      have hn : 0 ≤ t ^ (-α) := Real.rpow_nonneg ht0.le _
      calc -rD P t = t ^ (-α) * (t ^ α * (-rD P t)) := by rw [← mul_assoc, hpow t ht0, one_mul]
        _ ≤ t ^ (-α) * (Lt + 1) := mul_le_mul_of_nonneg_left h1.le hn
        _ = (Lt + 1) * t ^ (-α) := mul_comm _ _
  · intro a haα
    refine Fs_moment_inf h (by linarith) haα hX (half_pos hLt) fun t ht => ?_
    have ht0 : 0 < t := lt_of_lt_of_le hX ht
    have h1 := hX2 t (((le_max_right _ _).trans (le_max_left _ _)).trans ht)
    have hn : 0 ≤ t ^ (-α) := Real.rpow_nonneg ht0.le _
    calc Lt / 2 * t ^ (-α) = t ^ (-α) * (Lt / 2) := mul_comm _ _
      _ ≤ t ^ (-α) * (t ^ α * (-rD P t)) := mul_le_mul_of_nonneg_left h1.le hn
      _ = -rD P t := by rw [← mul_assoc, hpow t ht0, one_mul]

end good3

lemma wc_good {m1 ma α : ℝ} (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    Good (worstCase m1 ma α) m1 := by
  have hne := amb_nonempty hα hm1 hma
  refine ⟨wc_convex hne, wc_anti hne, fun x y hxy => wc_lip hne hxy,
    fun q hq => wc_of_nonpos hne hq, ?_⟩
  have h1 := (wc_tendsto hα hm1 hma).div_atTop (tendsto_rpow_atTop (by linarith : 0 < α - 1))
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with q hq
  have : 0 < q ^ (α - 1) := Real.rpow_pos_of_pos hq _
  field_simp

end HTNV43

open MeasureTheory Filter HeavyTailNV.Tail in
theorem solution (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1)
    (hma : m1 ^ α < ma) :
    IsRegularlyVarying (worstCase m1 ma α) (-(α - 1)) ∧
    ∃ Fstar : Measure ℝ, IsProbabilityMeasure Fstar ∧
      Fstar (Set.Iio 0) = 0 ∧ Fstar ∉ ambiguitySet m1 ma α ∧
      (∀ q : ℝ, 0 ≤ q →
        Integrable (fun w : ℝ => max (w - q) 0) Fstar ∧
        (∫ w, max (w - q) 0 ∂Fstar) = worstCase m1 ma α q) ∧
      IsRegularlyVarying (tail Fstar) (-α) ∧
      (∀ a : ℝ, 0 ≤ a → a < α →
        (∫⁻ w, ENNReal.ofReal (w ^ a) ∂Fstar) < ⊤) ∧
      (∀ a : ℝ, α ≤ a →
        (∫⁻ w, ENNReal.ofReal (w ^ a) ∂Fstar) = ⊤) := by
  have h := HTNV43.wc_good hα hm1 hma
  have hD : 0 < ma - m1 ^ α := by linarith
  have hr : 0 < α / (α - 1) := div_pos (by linarith) (by linarith)
  have hkap : 0 < HTNV43.kap α := by
    unfold HTNV43.kap; have := Real.rpow_pos_of_pos hr (α - 1); have : 0 < α := by linarith
    positivity
  have hLt : 0 < (α - 1) * (HTNV43.kap α * (ma - m1 ^ α)) :=
    mul_pos (by linarith) (mul_pos hkap hD)
  have hasym := HTNV43.rD_asym h (by linarith : 0 < α - 1) (HTNV43.wc_tendsto hα hm1 hma)
  rw [sub_add_cancel] at hasym
  have htail : tail (HTNV43.Gs h).measure = fun x => -HTNV43.rD (worstCase m1 ma α) x :=
    funext fun x => HTNV43.Fs_real_Ioi h x
  obtain ⟨hfin, hinf⟩ := HTNV43.Fs_moments h (by linarith) hLt hasym
  refine ⟨HTNV43.wc_rv hα hm1 hma, (HTNV43.Gs h).measure, HTNV43.Fs_prob h, HTNV43.Fs_Iio h, ?_, fun q _ => HTNV43.Fs_sh h q,
    ?_, hfin, hinf⟩
  · intro hmem
    have hI : Integrable (fun w : ℝ => w ^ α) (HTNV43.Gs h).measure := hmem.2.2.2.1
    have := hI.lintegral_lt_top
    rw [hinf α le_rfl] at this
    exact lt_irrefl _ this
  · rw [htail]
    exact HTNV43.rv_of_tendsto hLt hasym
