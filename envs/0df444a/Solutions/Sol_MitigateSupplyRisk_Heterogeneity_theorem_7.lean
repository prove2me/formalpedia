-- Prove2me | solution 1 for MitigateSupplyRisk.Heterogeneity.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:14:32.59846+00:00
-- url     : https://prove2.me/submissions/1c296a90-f33f-4aa6-9f23-5e9d2db4304e

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Heterogeneity_Model

open MeasureTheory ProbabilityTheory Set
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace MSRT7
open MitigateSupplyRisk.Heterogeneity

/-! ## Delivered quantity -/

abbrev Dl (K q ξ : ℝ) : ℝ := MitigateSupplyRisk.LateCommit.delivered K q ξ

lemma Dl_def (K q ξ : ℝ) : Dl K q ξ = min q (max (K - ξ) 0) := rfl

lemma Dl_nonneg {K q ξ : ℝ} (hq : 0 ≤ q) : 0 ≤ Dl K q ξ := le_min hq (le_max_right _ _)

lemma Dl_le (K q ξ : ℝ) : Dl K q ξ ≤ q := min_le_left _ _

lemma Dl_mono_q {K ξ q q' : ℝ} (h : q ≤ q') : Dl K q ξ ≤ Dl K q' ξ := min_le_min_right _ h

lemma Dl_anti (K q : ℝ) : Antitone (fun ξ => Dl K q ξ) :=
  fun _ _ h => min_le_min_left _ (max_le_max_right _ (sub_le_sub_left h K))

lemma Dl_cont (K q : ℝ) : Continuous (fun ξ => Dl K q ξ) := by
  simp only [Dl_def]; fun_prop

lemma Dl_abs_le (K q ξ : ℝ) : |Dl K q ξ| ≤ |q| := by
  rw [Dl_def, abs_le]
  constructor
  · have : min q (max (K - ξ) 0) ≥ min q 0 := min_le_min_left _ (le_max_right _ _)
    have h2 : min q 0 ≥ -|q| := le_min (neg_abs_le q) (by simp)
    linarith
  · exact (min_le_left _ _).trans (le_abs_self q)

lemma Dl_le_K {K q ξ : ℝ} (hK : 0 ≤ K) (hξ : 0 ≤ ξ) : Dl K q ξ ≤ K :=
  (min_le_right _ _).trans (max_le (by linarith) hK)

/-! ## The single-source gain function -/

/-- realized "gain" for delivered quantity `y` and demand `x` at unit cost `C`. -/
noncomputable def hh (S : SymData) (C y x : ℝ) : ℝ :=
  -((1 - S.η) * y * C) + S.r * min x y + S.v * max (y - x) 0 - S.p * max (x - y) 0

noncomputable def φ (S : SymData) (C y : ℝ) : ℝ := ∫ x, hh S C y x ∂S.μ

noncomputable def Lh (S : SymData) (C : ℝ) : NNReal :=
  ‖(1 - S.η) * C‖₊ + ‖S.r‖₊ + ‖S.v‖₊ + ‖S.p‖₊

lemma lip_mul' {α : Type*} [PseudoMetricSpace α] {f : α → ℝ} {K : NNReal}
    (h : LipschitzWith K f) (c : ℝ) : LipschitzWith (‖c‖₊ * K) (fun x => c * f x) := by
  simpa only [smul_eq_mul, Function.comp_def] using (lipschitzWith_smul c).comp h

lemma hh_lip (S : SymData) (C x : ℝ) : LipschitzWith (Lh S C) (fun y => hh S C y x) := by
  have h0 := lip_mul' (LipschitzWith.id) ((1 - S.η) * C)
  have h1 := lip_mul' ((LipschitzWith.id).const_min x) S.r
  have h2 := lip_mul' ((LipschitzWith.id.sub (LipschitzWith.const x)).max_const 0) S.v
  have h3 := lip_mul' (((LipschitzWith.const x).sub LipschitzWith.id).max_const 0) S.p
  have := ((h0.neg.add h1).add h2).sub h3
  have e : (fun y => hh S C y x) = fun y => ((-fun y => (1 - S.η) * C * id y) y
      + S.r * min x (id y) + S.v * max (id y - x) 0 - S.p * max (x - id y) 0) := by
    funext y; simp only [hh, id, Pi.neg_apply]; ring
  rw [e]
  exact this.weaken (le_of_eq (by simp [Lh]))

lemma hh_integrable (S : SymData) (hS : S.Standing) (C y : ℝ) :
    Integrable (fun x => hh S C y x) S.μ := by
  haveI := hS.μ_prob
  have hx : Integrable (fun x : ℝ => x) S.μ := hS.μ_integrable
  have h := (((integrable_const ((1 - S.η) * y * C)).neg.add
      ((hx.inf (integrable_const y)).const_mul S.r)).add
      ((((integrable_const y).sub hx).sup (integrable_const 0)).const_mul S.v)).sub
      (((hx.sub (integrable_const y)).sup (integrable_const 0)).const_mul S.p)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp [hh]

lemma φ_lip (S : SymData) (hS : S.Standing) (C : ℝ) : LipschitzWith (Lh S C) (φ S C) := by
  haveI := hS.μ_prob
  apply LipschitzWith.of_dist_le_mul
  intro y y'
  rw [dist_eq_norm, φ, φ, ← integral_sub (hh_integrable S hS C y) (hh_integrable S hS C y')]
  have h := norm_integral_le_of_norm_le_const (μ := S.μ)
    (ae_of_all _ (fun x => (hh_lip S C x).norm_sub_le y y'))
  simpa [dist_eq_norm] using h

lemma hh_concave (S : SymData) (hS : S.Standing) (C x : ℝ) :
    ConcaveOn ℝ univ (fun y => hh S C y x) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ w _ a b ha hb hab
  simp only [smul_eq_mul]
  have key : ∀ y, hh S C y x = (S.r + S.p - (1 - S.η) * C) * y
      - (S.r + S.p - S.v) * max (y - x) 0 - S.p * x := by
    intro y
    rcases le_total x y with h | h
    · simp only [hh, min_eq_left h, max_eq_left (sub_nonneg.mpr h),
        max_eq_right (sub_nonpos.mpr h)]; ring
    · simp only [hh, min_eq_right h, max_eq_right (sub_nonpos.mpr h),
        max_eq_left (sub_nonneg.mpr h)]; ring
  rw [key, key, key]
  have hmax : max ((a * u + b * w) - x) 0 ≤ a * max (u - x) 0 + b * max (w - x) 0 := by
    apply max_le
    · have h1 := mul_le_mul_of_nonneg_left (le_max_left (u - x) 0) ha
      have h2 := mul_le_mul_of_nonneg_left (le_max_left (w - x) 0) hb
      have he : (a + b) * x = x := by rw [hab, one_mul]
      nlinarith only [h1, h2, he]
    · positivity
  have hh' := mul_le_mul_of_nonneg_left hmax (sub_nonneg.mpr hS.v_lt.le)
  have he : (a + b) * (S.p * x) = S.p * x := by rw [hab, one_mul]
  nlinarith only [hh', he]

lemma φ_concave (S : SymData) (hS : S.Standing) (C : ℝ) : ConcaveOn ℝ univ (φ S C) := by
  haveI := hS.μ_prob
  refine ⟨convex_univ, ?_⟩
  intro u _ w _ a b ha hb hab
  simp only [smul_eq_mul, φ]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((hh_integrable S hS C u).const_mul a) ((hh_integrable S hS C w).const_mul b)]
  exact integral_mono (((hh_integrable S hS C u).const_mul a).add
      ((hh_integrable S hS C w).const_mul b))
    (hh_integrable S hS C (a * u + b * w))
    (fun x => (hh_concave S hS C x).2 (mem_univ u) (mem_univ w) ha hb hab)

lemma φ_shift (S : SymData) (hS : S.Standing) (C C' y : ℝ) :
    φ S C' y = φ S C y - (1 - S.η) * y * (C' - C) := by
  haveI := hS.μ_prob
  have : (fun x => hh S C' y x) = fun x => hh S C y x - (1 - S.η) * y * (C' - C) := by
    funext x; simp [hh]; ring
  rw [φ, this, integral_sub (hh_integrable S hS C y) (integrable_const _)]
  simp [φ]

/-! ## Stochastic-order tools (from the accepted proof of `DualSourcing.lemma_2b`) -/

lemma level_measure_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, cdf μ x ≤ cdf ν x) {f : ℝ → ℝ}
    (hc : Continuous f) (ha : Antitone f) (t : ℝ) :
    μ {x | t ≤ f x} ≤ ν {x | t ≤ f x} := by
  let S : Set ℝ := {x | t ≤ f x}
  change μ S ≤ ν S
  by_cases hn : S.Nonempty
  · by_cases hb : BddAbove S
    · have hm : sSup S ∈ S := (isClosed_le continuous_const hc).csSup_mem hn hb
      have he : S = Iic (sSup S) := by
        ext x
        constructor
        · exact fun hx => le_csSup hb hx
        · exact fun hx => le_trans hm (ha hx)
      rw [he, ← ofReal_cdf, ← ofReal_cdf]
      exact ENNReal.ofReal_le_ofReal (h _)
    · have he : S = univ := by
        apply eq_univ_of_forall
        intro x
        obtain ⟨y,hy,hxy⟩ := not_bddAbove_iff.mp hb x
        exact le_trans hy (ha hxy.le)
      simp [he]
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he]

lemma integral_antitone_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, cdf μ x ≤ cdf ν x) {f : ℝ → ℝ}
    (hc : Continuous f) (ha : Antitone f) (hm : Integrable f μ) (hn : Integrable f ν)
    (c : ℝ) (hb : ∀ x, c ≤ f x) : (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν := by
  let g := fun x => f x-c
  have hgc : Continuous g := hc.sub continuous_const
  have hga : Antitone g := fun x y hxy => sub_le_sub_right (ha hxy) c
  have hgm : Integrable g μ := hm.sub (integrable_const c)
  have hgn : Integrable g ν := hn.sub (integrable_const c)
  have hg0 : ∀ x, 0 ≤ g x := fun x => sub_nonneg.mpr (hb x)
  have hl : (∫ x, g x ∂μ) ≤ ∫ x, g x ∂ν := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgn.aestronglyMeasurable]
    apply ENNReal.toReal_mono hgn.lintegral_lt_top.ne
    rw [lintegral_eq_lintegral_meas_le μ (ae_of_all _ hg0) hgc.measurable.aemeasurable,
      lintegral_eq_lintegral_meas_le ν (ae_of_all _ hg0) hgc.measurable.aemeasurable]
    exact lintegral_mono (fun t => level_measure_le μ ν h hgc hga t)
  dsimp [g] at hl
  rw [integral_sub hm (integrable_const c), integral_sub hn (integrable_const c)] at hl
  simpa using hl

lemma monotone_before_max {f : ℝ → ℝ} {Q z : ℝ}
    (hc : ConcaveOn ℝ (Icc 0 Q) f) (hz : z ∈ Icc 0 Q)
    (hmax : IsMaxOn f (Icc 0 Q) z) : MonotoneOn f (Icc 0 z) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with he | hxy
  · simp [he]
  rcases hy.2.eq_or_lt with he | hyz
  · subst y
    exact hmax ⟨hx.1,hx.2.trans hz.2⟩
  have hs := hc.slope_anti_adjacent ⟨hx.1,hx.2.trans hz.2⟩ hz hxy hyz
  have hm := hmax (show y ∈ Icc 0 Q from ⟨hy.1,hy.2.trans hz.2⟩)
  have hnon : 0 ≤ (f z-f y)/(z-y) := div_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hyz.le)
  have hp : 0 ≤ (f y-f x)/(y-x) := hnon.trans hs
  rcases div_nonneg_iff.mp hp with h | h
  · exact sub_nonneg.mp h.1
  · linarith [h.2]

/-! ## Single sourcing as a one-dimensional problem -/

noncomputable def PS (S : SymData) (C q ξ x : ℝ) : ℝ := -(S.η * q * C) + hh S C (Dl S.K q ξ) x

noncomputable def J (S : SymData) (C q a : ℝ) : ℝ :=
  ∫ ξ, φ S C (Dl S.K q ξ) ∂S.ν a - S.η * q * C

lemma φDl_integrable (S : SymData) (hS : S.Standing) (C q a : ℝ) :
    Integrable (fun ξ => φ S C (Dl S.K q ξ)) (S.ν a) := by
  haveI := hS.ν_prob a
  apply (integrable_const (‖φ S C 0‖ + (Lh S C : ℝ) * |q|)).mono'
  · exact ((φ_lip S hS C).continuous.comp (Dl_cont S.K q)).aestronglyMeasurable
  · refine ae_of_all _ fun ξ => ?_
    have h1 := (φ_lip S hS C).dist_le_mul (Dl S.K q ξ) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at h1
    have h2 := Dl_abs_le S.K q ξ
    have h3 : |φ S C (Dl S.K q ξ)| ≤ |φ S C 0| + |φ S C (Dl S.K q ξ) - φ S C 0| := by
      have := abs_add_le (φ S C 0) (φ S C (Dl S.K q ξ) - φ S C 0)
      simpa using this
    have h4 : (Lh S C : ℝ) * |Dl S.K q ξ| ≤ (Lh S C : ℝ) * |q| :=
      mul_le_mul_of_nonneg_left h2 (Lh S C).2
    simp only [Real.norm_eq_abs]
    linarith

lemma PS_integrable (S : SymData) (hS : S.Standing) (C q a : ℝ) :
    Integrable (fun ω : ℝ × ℝ => PS S C q ω.1 ω.2) ((S.ν a).prod S.μ) := by
  haveI := hS.ν_prob a
  haveI := hS.μ_prob
  have hy : Integrable (fun ω : ℝ × ℝ => Dl S.K q ω.1) ((S.ν a).prod S.μ) := by
    apply (integrable_const |q|).mono'
    · exact ((Dl_cont S.K q).comp continuous_fst).aestronglyMeasurable
    · exact ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using Dl_abs_le S.K q ω.1
  have hx : Integrable (fun ω : ℝ × ℝ => ω.2) ((S.ν a).prod S.μ) :=
    hS.μ_integrable.comp_snd _
  have h := (((integrable_const (S.η * q * C)).neg.add
      ((hy.const_mul (1 - S.η)).mul_const C).neg).add
      ((hx.inf hy).const_mul S.r)).add
      (((hy.sub hx).sup (integrable_const 0)).const_mul S.v) |>.sub
      (((hx.sub hy).sup (integrable_const 0)).const_mul S.p)
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [PS, hh, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.inf_apply, Pi.sup_apply]
  ring

lemma PS_integral (S : SymData) (hS : S.Standing) (C q a : ℝ) :
    ∫ ω, PS S C q ω.1 ω.2 ∂((S.ν a).prod S.μ) = J S C q a := by
  haveI := hS.ν_prob a
  haveI := hS.μ_prob
  rw [integral_prod _ (PS_integrable S hS C q a)]
  have hin : ∀ ξ, ∫ x, PS S C q ξ x ∂S.μ = -(S.η * q * C) + φ S C (Dl S.K q ξ) := by
    intro ξ
    simp only [PS]
    rw [integral_add (integrable_const _) (hh_integrable S hS C _)]
    simp [φ]
  simp_rw [hin]
  rw [integral_add (integrable_const _) (φDl_integrable S hS C q a)]
  simp [J]
  ring

lemma J_lip (S : SymData) (hS : S.Standing) (C a : ℝ) :
    LipschitzWith (Lh S C + ‖S.η * C‖₊) (fun q => J S C q a) := by
  haveI := hS.ν_prob a
  have h1 : LipschitzWith (Lh S C) (fun q => ∫ ξ, φ S C (Dl S.K q ξ) ∂S.ν a) := by
    apply LipschitzWith.of_dist_le_mul
    intro q q'
    rw [dist_eq_norm, ← integral_sub (φDl_integrable S hS C q a) (φDl_integrable S hS C q' a)]
    have hb : ∀ ξ, ‖φ S C (Dl S.K q ξ) - φ S C (Dl S.K q' ξ)‖ ≤ (Lh S C : ℝ) * dist q q' := by
      intro ξ
      have h := (φ_lip S hS C).dist_le_mul (Dl S.K q ξ) (Dl S.K q' ξ)
      have h' := ((LipschitzWith.id.min_const (max (S.K - ξ) 0)) : LipschitzWith 1
        (fun t : ℝ => min t (max (S.K - ξ) 0))).dist_le_mul q q'
      rw [← dist_eq_norm]
      calc dist (φ S C (Dl S.K q ξ)) (φ S C (Dl S.K q' ξ))
          ≤ (Lh S C : ℝ) * dist (Dl S.K q ξ) (Dl S.K q' ξ) := h
        _ ≤ (Lh S C : ℝ) * dist q q' := by
          apply mul_le_mul_of_nonneg_left _ (Lh S C).2
          simpa [Dl_def] using h'
    have h := norm_integral_le_of_norm_le_const (μ := S.ν a) (ae_of_all _ hb)
    simpa using h
  have h2 : LipschitzWith ‖S.η * C‖₊ (fun q : ℝ => S.η * q * C) := by
    have := lip_mul' (LipschitzWith.id) (S.η * C)
    have e : (fun q : ℝ => S.η * q * C) = fun x => S.η * C * id x := by funext q; simp; ring
    rw [e]; exact this.weaken (by simp)
  simpa [J] using h1.sub h2

lemma ae_nonneg_ν (S : SymData) (hS : S.Standing) (a : ℝ) : ∀ᵐ ξ ∂S.ν a, 0 ≤ ξ := by
  rw [ae_iff]
  simpa only [not_le, Set.Iio] using hS.ν_nonneg a

section OneDim
variable (S : SymData) (hS : S.Standing) (C z : ℝ)

include hS in
lemma J_clip (hz : z ∈ Icc 0 S.K) (hzm : IsMaxOn (φ S C) (Icc 0 S.K) z) (hC : 0 ≤ C)
    {q : ℝ} (hq : 0 ≤ q) (a : ℝ) : J S C q a ≤ J S C (min q z) a := by
  haveI := hS.ν_prob a
  have hi : ∫ ξ, φ S C (Dl S.K q ξ) ∂S.ν a ≤ ∫ ξ, φ S C (Dl S.K (min q z) ξ) ∂S.ν a := by
    apply integral_mono_ae (φDl_integrable S hS C q a) (φDl_integrable S hS C _ a)
    filter_upwards [ae_nonneg_ν S hS a] with ξ hξ
    have he : Dl S.K (min q z) ξ = min (Dl S.K q ξ) z := by
      simp only [Dl_def]; exact min_right_comm _ _ _
    rw [he]
    by_cases h : Dl S.K q ξ ≤ z
    · rw [min_eq_left h]
    · rw [min_eq_right (le_of_not_ge h)]
      exact hzm ⟨Dl_nonneg hq, Dl_le_K hS.K_pos.le hξ⟩
  have hc : S.η * min q z * C ≤ S.η * q * C :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_left _ _) hS.η_mem.1) hC
  simp only [J]
  linarith

def Mset (a : ℝ) : Set ℝ := {q | q ∈ Icc 0 z ∧ ∀ q' ∈ Icc 0 z, J S C q' a ≤ J S C q a}

noncomputable def qbar (a : ℝ) : ℝ := sSup (Mset S C z a)

include hS in
lemma qbar_mem (hz : z ∈ Icc 0 S.K) (a : ℝ) : qbar S C z a ∈ Mset S C z a := by
  have hc := (J_lip S hS C a).continuous
  have hne : (Mset S C z a).Nonempty := by
    obtain ⟨q, hq, hmax⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) z)).exists_isMaxOn
      ⟨0, le_rfl, hz.1⟩ hc.continuousOn
    exact ⟨q, hq, fun q' hq' => hmax hq'⟩
  have hcl : IsClosed (Mset S C z a) := by
    have : Mset S C z a = Icc 0 z ∩ ⋂ q' ∈ Icc 0 z, {q | J S C q' a ≤ J S C q a} := by
      ext q; simp [Mset]
    rw [this]
    exact isClosed_Icc.inter (isClosed_biInter fun q' _ => isClosed_le continuous_const hc)
  exact hcl.csSup_mem hne ⟨z, fun q hq => hq.1.2⟩

include hS in
lemma le_qbar (hz : z ∈ Icc 0 S.K) {a q : ℝ} (hq : q ∈ Mset S C z a) : q ≤ qbar S C z a :=
  le_csSup ⟨z, fun q hq => hq.1.2⟩ hq

include hS in
lemma qbar_max (hz : z ∈ Icc 0 S.K) (hzm : IsMaxOn (φ S C) (Icc 0 S.K) z) (hC : 0 ≤ C)
    (a : ℝ) {q : ℝ} (hq : 0 ≤ q) : J S C q a ≤ J S C (qbar S C z a) a :=
  (J_clip S hS C z hz hzm hC hq a).trans
    ((qbar_mem S hS C z hz a).2 _ ⟨le_min hq hz.1, min_le_right _ _⟩)

include hS in
lemma J_incdiff (hz : z ∈ Icc 0 S.K) (hzm : IsMaxOn (φ S C) (Icc 0 S.K) z)
    {q q' a a' : ℝ} (hq' : 0 ≤ q') (hqq : q' ≤ q) (hqz : q ≤ z) (haa : a ≤ a') :
    J S C q a - J S C q' a ≤ J S C q a' - J S C q' a' := by
  haveI := hS.ν_prob a
  haveI := hS.ν_prob a'
  have hmono : MonotoneOn (φ S C) (Icc 0 z) :=
    monotone_before_max (((φ_concave S hS C).subset (subset_univ _) (convex_Icc _ _))) hz hzm
  have hmem : ∀ t ξ, 0 ≤ t → t ≤ z → Dl S.K t ξ ∈ Icc 0 z :=
    fun t ξ h0 h1 => ⟨Dl_nonneg h0, (Dl_le _ _ _).trans h1⟩
  let g := fun ξ => φ S C (Dl S.K q ξ) - φ S C (Dl S.K q' ξ)
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun ξ => sub_nonneg.mpr (hmono (hmem q' ξ hq' (hqq.trans hqz))
    (hmem q ξ (hq'.trans hqq) hqz) (Dl_mono_q hqq))
  have hga : Antitone g := by
    intro ξ1 ξ2 h12
    simp only [g, Dl_def]
    set L1 := max (S.K - ξ1) 0
    set L2 := max (S.K - ξ2) 0
    have hL : L2 ≤ L1 := max_le_max_right _ (sub_le_sub_left h12 _)
    have hL0 : 0 ≤ L2 := le_max_right _ _
    by_cases hc : q' ≤ L2
    · rw [min_eq_left hc, min_eq_left (hc.trans hL)]
      have := hmono ⟨le_min (hq'.trans hqq) hL0, (min_le_left _ _).trans hqz⟩
        ⟨le_min (hq'.trans hqq) (hL0.trans hL), (min_le_left _ _).trans hqz⟩
        (min_le_min_left q hL)
      linarith
    · push_neg at hc
      rw [min_eq_right hc.le, min_eq_right (hc.le.trans hqq)]
      have := hg0 ξ1
      simp only [g, Dl_def] at this
      linarith
  have hgc : Continuous g :=
    ((φ_lip S hS C).continuous.comp (Dl_cont S.K q)).sub
      ((φ_lip S hS C).continuous.comp (Dl_cont S.K q'))
  have hgi : ∀ b, Integrable g (S.ν b) := fun b =>
    (φDl_integrable S hS C q b).sub (φDl_integrable S hS C q' b)
  have hle := integral_antitone_le (S.ν a) (S.ν a') (hS.ν_mono a a' haa) hgc hga
    (hgi a) (hgi a') 0 hg0
  have e : ∀ b, J S C q b - J S C q' b = ∫ ξ, g ξ ∂S.ν b - S.η * (q - q') * C := by
    intro b
    simp only [J, g]
    rw [integral_sub (φDl_integrable S hS C q b) (φDl_integrable S hS C q' b)]
    ring
  rw [e, e]
  linarith

include hS in
lemma qbar_mono (hz : z ∈ Icc 0 S.K) (hzm : IsMaxOn (φ S C) (Icc 0 S.K) z)
    {a a' : ℝ} (haa : a ≤ a') : qbar S C z a ≤ qbar S C z a' := by
  by_contra hlt
  push_neg at hlt
  have h1 := qbar_mem S hS C z hz a
  have h2 := qbar_mem S hS C z hz a'
  have hid := J_incdiff S hS C z hz hzm h2.1.1 hlt.le h1.1.2 haa
  have hge : J S C (qbar S C z a') a ≤ J S C (qbar S C z a) a := h1.2 _ h2.1
  have hmem : qbar S C z a ∈ Mset S C z a' := by
    refine ⟨h1.1, fun q' hq' => ?_⟩
    have := h2.2 q' hq'
    linarith
  have := le_qbar S hS C z hz hmem
  linarith

end OneDim

/-! ## Weights -/

noncomputable def w (S : SymData) (q a : ℝ) : ℝ := S.η * q + (1 - S.η) * ∫ ξ, Dl S.K q ξ ∂S.ν a

lemma Dl_integrable (S : SymData) (hS : S.Standing) (q a : ℝ) :
    Integrable (fun ξ => Dl S.K q ξ) (S.ν a) := by
  haveI := hS.ν_prob a
  apply (integrable_const |q|).mono' (Dl_cont S.K q).aestronglyMeasurable
  exact ae_of_all _ fun ξ => by simpa [Real.norm_eq_abs] using Dl_abs_le S.K q ξ

lemma w_mono (S : SymData) (hS : S.Standing) {q q' a a' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q')
    (haa : a ≤ a') : w S q a ≤ w S q' a' := by
  haveI := hS.ν_prob a
  haveI := hS.ν_prob a'
  have h1 : ∫ ξ, Dl S.K q ξ ∂S.ν a ≤ ∫ ξ, Dl S.K q ξ ∂S.ν a' :=
    integral_antitone_le _ _ (hS.ν_mono a a' haa) (Dl_cont S.K q) (Dl_anti S.K q)
      (Dl_integrable S hS q a) (Dl_integrable S hS q a') 0 (fun ξ => Dl_nonneg hq)
  have h2 : ∫ ξ, Dl S.K q ξ ∂S.ν a' ≤ ∫ ξ, Dl S.K q' ξ ∂S.ν a' :=
    integral_mono (Dl_integrable S hS q a') (Dl_integrable S hS q' a') (fun ξ => Dl_mono_q hqq)
  have hη := hS.η_mem
  have h3 : (1 - S.η) * ∫ ξ, Dl S.K q ξ ∂S.ν a ≤ (1 - S.η) * ∫ ξ, Dl S.K q' ξ ∂S.ν a' :=
    mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith [hη.2])
  have h4 : S.η * q ≤ S.η * q' := mul_le_mul_of_nonneg_left hqq hη.1
  simp only [w]
  linarith

lemma w_nonneg (S : SymData) (hS : S.Standing) {q : ℝ} (hq : 0 ≤ q) (a : ℝ) : 0 ≤ w S q a := by
  haveI := hS.ν_prob a
  have := integral_nonneg (μ := S.ν a) (f := fun ξ => Dl S.K q ξ) (fun ξ => Dl_nonneg hq)
  have hη := hS.η_mem
  simp only [w]
  have : 0 ≤ (1 - S.η) * ∫ ξ, Dl S.K q ξ ∂S.ν a := mul_nonneg (by linarith [hη.2]) this
  nlinarith [hη.1]

lemma w_le (S : SymData) (hS : S.Standing) {q : ℝ} (hq : 0 ≤ q) (a : ℝ) : w S q a ≤ q := by
  haveI := hS.ν_prob a
  have h : ∫ ξ, Dl S.K q ξ ∂S.ν a ≤ q := by
    have := integral_mono (Dl_integrable S hS q a) (integrable_const q) (fun ξ => Dl_le S.K q ξ)
    simpa using this
  have hη := hS.η_mem
  simp only [w]
  nlinarith [hη.1, hη.2]

lemma J_shift (S : SymData) (hS : S.Standing) (C C' q a : ℝ) :
    J S C' q a = J S C q a - (C' - C) * w S q a := by
  haveI := hS.ν_prob a
  simp only [J, w, φ_shift S hS C C']
  rw [integral_sub (φDl_integrable S hS C q a)]
  · have : ∫ ξ, (1 - S.η) * Dl S.K q ξ * (C' - C) ∂S.ν a
        = (1 - S.η) * (C' - C) * ∫ ξ, Dl S.K q ξ ∂S.ν a := by
      rw [← integral_const_mul]; congr 1; funext ξ; ring
    rw [this]; ring
  · exact ((Dl_integrable S hS q a).const_mul (1 - S.η)).mul_const (C' - C)

/-! ## Optimal single-sourcing values -/

noncomputable def star (S : SymData) (C a : ℝ) : ℝ := sSup ((fun q => J S C q a) '' Ici 0)

lemma star_eq (S : SymData) (hS : S.Standing) {C z : ℝ} (hC : 0 ≤ C) (hz : z ∈ Icc 0 S.K)
    (hzm : IsMaxOn (φ S C) (Icc 0 S.K) z) (a : ℝ) :
    star S C a = J S C (qbar S C z a) a := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨qbar S C z a, (qbar_mem S hS C z hz a).1.1, rfl⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact qbar_max S hS C z hz hzm hC a hq

lemma J_le_star (S : SymData) (hS : S.Standing) {C z : ℝ} (hC : 0 ≤ C) (hz : z ∈ Icc 0 S.K)
    (hzm : IsMaxOn (φ S C) (Icc 0 S.K) z) (a : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    J S C q a ≤ star S C a := by
  rw [star_eq S hS hC hz hzm a]; exact qbar_max S hS C z hz hzm hC a hq

lemma star_le (S : SymData) (hS : S.Standing) {C z : ℝ} (hC : 0 ≤ C) (hz : z ∈ Icc 0 S.K)
    (hzm : IsMaxOn (φ S C) (Icc 0 S.K) z) (a : ℝ) : star S C a ≤ φ S C z := by
  haveI := hS.ν_prob a
  rw [star_eq S hS hC hz hzm a]
  have hm := qbar_mem S hS C z hz a
  have h1 : ∫ ξ, φ S C (Dl S.K (qbar S C z a) ξ) ∂S.ν a ≤ ∫ ξ, φ S C z ∂S.ν a :=
    integral_mono (φDl_integrable S hS C _ a) (integrable_const _) (fun ξ =>
      hzm ⟨Dl_nonneg hm.1.1, (Dl_le _ _ _).trans (hm.1.2.trans hz.2)⟩)
  have h2 : 0 ≤ S.η * qbar S C z a * C := mul_nonneg (mul_nonneg hS.η_mem.1 hm.1.1) hC
  simp only [J]
  simp at h1
  linarith

lemma exists_z (S : SymData) (hS : S.Standing) (C : ℝ) :
    ∃ z ∈ Icc 0 S.K, IsMaxOn (φ S C) (Icc 0 S.K) z :=
  (isCompact_Icc : IsCompact (Icc (0:ℝ) S.K)).exists_isMaxOn ⟨0, le_rfl, hS.K_pos.le⟩
    (φ_lip S hS C).continuous.continuousOn

noncomputable def P1 (S : SymData) (C a : ℝ) : ℝ :=
  -(S.m * S.z a) + S.θ * star S C a + (1 - S.θ) * star S C S.a0

noncomputable def SSIv (S : SymData) (C : ℝ) : ℝ := sSup (P1 S C '' Ici S.a0)

lemma z_nonneg (S : SymData) (hS : S.Standing) {a : ℝ} (ha : S.a0 ≤ a) : 0 ≤ S.z a := by
  have := hS.z_mono ((mem_Ici.mpr le_rfl)) ha ha
  rw [hS.z_zero] at this; exact this

lemma P1_bdd (S : SymData) (hS : S.Standing) {C : ℝ} (hC : 0 ≤ C) :
    BddAbove (P1 S C '' Ici S.a0) := by
  obtain ⟨z, hz, hzm⟩ := exists_z S hS C
  refine ⟨φ S C z, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have h1 := star_le S hS hC hz hzm a
  have h2 := star_le S hS hC hz hzm S.a0
  have h3 : 0 ≤ S.m * S.z a := mul_nonneg hS.m_nonneg (z_nonneg S hS ha)
  have hθ := hS.θ_mem
  simp only [P1]
  nlinarith [mul_le_mul_of_nonneg_left h1 hθ.1,
    mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - S.θ by linarith [hθ.2])]

lemma star_anti (S : SymData) (hS : S.Standing) {C C' : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C') (a : ℝ) :
    star S C' a ≤ star S C a := by
  obtain ⟨z', hz', hzm'⟩ := exists_z S hS C'
  obtain ⟨z, hz, hzm⟩ := exists_z S hS C
  rw [star_eq S hS (hC.trans hCC) hz' hzm' a]
  have hq := (qbar_mem S hS C' z' hz' a).1.1
  rw [J_shift S hS C C']
  have := w_nonneg S hS hq a
  have := J_le_star S hS hC hz hzm a hq
  nlinarith

lemma SSIv_anti (S : SymData) (hS : S.Standing) {C C' : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C') :
    SSIv S C' ≤ SSIv S C := by
  show sSup (P1 S C' '' Ici S.a0) ≤ _
  refine csSup_le ⟨P1 S C' S.a0, S.a0, (mem_Ici.mpr le_rfl), rfl⟩ ?_
  rintro _ ⟨a, ha, rfl⟩
  apply le_trans _ (le_csSup (P1_bdd S hS hC) ⟨a, ha, rfl⟩)
  have h1 := star_anti S hS hC hCC a
  have h2 := star_anti S hS hC hCC S.a0
  have hθ := hS.θ_mem
  simp only [P1]
  nlinarith [mul_le_mul_of_nonneg_left h1 hθ.1,
    mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - S.θ by linarith [hθ.2])]

/-- The envelope step for single sourcing with improvement. -/
lemma SSIv_step (S : SymData) (hS : S.Standing) {C C' z : ℝ} (hC' : 0 ≤ C') (hCC : C' ≤ C)
    (hz : z ∈ Icc 0 S.K) (hzm : IsMaxOn (φ S C) (Icc 0 S.K) z) :
    SSIv S C + (C - C') * w S (qbar S C z S.a0) S.a0 ≤ SSIv S C' := by
  obtain ⟨z', hz', hzm'⟩ := exists_z S hS C'
  have hC : 0 ≤ C := hC'.trans hCC
  set W := w S (qbar S C z S.a0) S.a0
  have hstar : ∀ a, S.a0 ≤ a → star S C a + (C - C') * W ≤ star S C' a := by
    intro a ha
    have hq := (qbar_mem S hS C z hz a).1.1
    have h1 := J_le_star S hS hC' hz' hzm' a hq
    rw [J_shift S hS C C'] at h1
    have hw : W ≤ w S (qbar S C z a) a :=
      w_mono S hS (qbar_mem S hS C z hz S.a0).1.1 (qbar_mono S hS C z hz hzm ha) ha
    rw [star_eq S hS hC hz hzm a]
    nlinarith [mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr hCC)]
  have hP : ∀ a, S.a0 ≤ a → P1 S C a + (C - C') * W ≤ P1 S C' a := by
    intro a ha
    have h1 := hstar a ha
    have h2 := hstar S.a0 le_rfl
    have hθ := hS.θ_mem
    simp only [P1]
    nlinarith [mul_le_mul_of_nonneg_left h1 hθ.1,
      mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - S.θ by linarith [hθ.2])]
  have : SSIv S C ≤ SSIv S C' - (C - C') * W := by
    show sSup (P1 S C '' Ici S.a0) ≤ _
    refine csSup_le ⟨P1 S C S.a0, S.a0, (mem_Ici.mpr le_rfl), rfl⟩ ?_
    rintro _ ⟨a, ha, rfl⟩
    have h1 : P1 S C' a ≤ SSIv S C' := le_csSup (P1_bdd S hS hC') ⟨a, ha, rfl⟩
    have := hP a ha
    linarith
  linarith

/-! ## Connection with the model -/

lemma profitSingle0 (S : SymData) (Δ q ξ x : ℝ) :
    (S.costModel Δ).profitSingle 0 q ξ x = PS S (S.c - Δ) q ξ x := by
  simp only [Model.profitSingle, SymData.costModel, PS, hh, Dl]
  simp
  ring

lemma profitSingle1 (S : SymData) (Δ q ξ x : ℝ) :
    (S.costModel Δ).profitSingle 1 q ξ x = PS S (S.c + Δ) q ξ x := by
  simp only [Model.profitSingle, SymData.costModel, PS, hh, Dl]
  simp
  ring

lemma Pi2single0 (S : SymData) (hS : S.Standing) (Δ q a : ℝ) :
    (S.costModel Δ).Pi2single 0 q a = J S (S.c - Δ) q a := by
  rw [← PS_integral S hS]
  simp only [Model.Pi2single, profitSingle0]
  rfl

lemma Pi2single1 (S : SymData) (hS : S.Standing) (Δ q a : ℝ) :
    (S.costModel Δ).Pi2single 1 q a = J S (S.c + Δ) q a := by
  rw [← PS_integral S hS]
  simp only [Model.Pi2single, profitSingle1]
  rfl

lemma PiSSIof0 (S : SymData) (hS : S.Standing) (Δ : ℝ) :
    (S.costModel Δ).PiSSIof 0 = SSIv S (S.c - Δ) := by
  have hst : ∀ a, (S.costModel Δ).Pi2singleStar 0 a = star S (S.c - Δ) a := by
    intro a; simp only [Model.Pi2singleStar, Pi2single0 S hS, star]
  have hP : (S.costModel Δ).Pi1single 0 = P1 S (S.c - Δ) := by
    funext a; simp only [Model.Pi1single, hst, P1]; rfl
  rw [Model.PiSSIof, hP]; rfl

lemma PiSSIof1 (S : SymData) (hS : S.Standing) (Δ : ℝ) :
    (S.costModel Δ).PiSSIof 1 = SSIv S (S.c + Δ) := by
  have hst : ∀ a, (S.costModel Δ).Pi2singleStar 1 a = star S (S.c + Δ) a := by
    intro a; simp only [Model.Pi2singleStar, Pi2single1 S hS, star]
  have hP : (S.costModel Δ).Pi1single 1 = P1 S (S.c + Δ) := by
    funext a; simp only [Model.Pi1single, hst, P1]; rfl
  rw [Model.PiSSIof, hP]; rfl

lemma PiSSI_eq (S : SymData) (hS : S.Standing) {Δ : ℝ} (h0 : 0 ≤ Δ) (hc : Δ < S.c) :
    (S.costModel Δ).PiSSI = SSIv S (S.c - Δ) := by
  rw [Model.PiSSI, PiSSIof0 S hS, PiSSIof1 S hS]
  exact max_eq_left (SSIv_anti S hS (by linarith) (by linarith))

/-! ## Dual sourcing -/

noncomputable def Pm (S : SymData) : Measure ((ℝ × ℝ) × ℝ) :=
  ((S.ν S.a0).prod (S.ν S.a0)).prod S.μ

noncomputable def DS (S : SymData) (Δ : ℝ) (q : Fin 2 → ℝ) : ℝ :=
  (S.costModel Δ).Pi2 q (S.costModel Δ).a0

lemma Pm_prob (S : SymData) (hS : S.Standing) : IsProbabilityMeasure (Pm S) := by
  haveI := hS.ν_prob S.a0
  haveI := hS.μ_prob
  unfold Pm; infer_instance

lemma DS_def (S : SymData) (Δ : ℝ) (q : Fin 2 → ℝ) :
    DS S Δ q = ∫ ω, (S.costModel Δ).profit q ![ω.1.1, ω.1.2] ω.2 ∂Pm S := rfl

noncomputable def wt (S : SymData) (t ξ : ℝ) : ℝ := S.η * t + (1 - S.η) * Dl S.K t ξ

lemma profit_expand (S : SymData) (Δ : ℝ) (q ξ : Fin 2 → ℝ) (x : ℝ) :
    (S.costModel Δ).profit q ξ x =
      -(wt S (q 0) (ξ 0) * (S.c - Δ) + wt S (q 1) (ξ 1) * (S.c + Δ))
      + S.r * min x (Dl S.K (q 0) (ξ 0) + Dl S.K (q 1) (ξ 1))
      + S.v * max ((Dl S.K (q 0) (ξ 0) + Dl S.K (q 1) (ξ 1)) - x) 0
      - S.p * max (x - (Dl S.K (q 0) (ξ 0) + Dl S.K (q 1) (ξ 1))) 0 := by
  simp [Model.profit, SymData.costModel, Fin.sum_univ_two, wt, Dl]

lemma profit_cont (S : SymData) (Δ : ℝ) (q : Fin 2 → ℝ) :
    Continuous (fun ω : (ℝ × ℝ) × ℝ => (S.costModel Δ).profit q ![ω.1.1, ω.1.2] ω.2) := by
  simp only [profit_expand, wt, Dl_def]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  fun_prop

lemma DSprofit_integrable (S : SymData) (hS : S.Standing) (Δ : ℝ) (q : Fin 2 → ℝ) :
    Integrable (fun ω : (ℝ × ℝ) × ℝ => (S.costModel Δ).profit q ![ω.1.1, ω.1.2] ω.2) (Pm S) := by
  haveI := hS.ν_prob S.a0
  haveI := hS.μ_prob
  haveI := Pm_prob S hS
  have hy : ∀ (t : ℝ) (f : (ℝ × ℝ) × ℝ → ℝ), Continuous f →
      Integrable (fun ω => Dl S.K t (f ω)) (Pm S) := by
    intro t f hf
    apply (integrable_const |t|).mono' ((Dl_cont S.K t).comp hf).aestronglyMeasurable
    exact ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using Dl_abs_le S.K t (f ω)
  have h0 := hy (q 0) (fun ω => ω.1.1) (by fun_prop)
  have h1 := hy (q 1) (fun ω => ω.1.2) (by fun_prop)
  have hx : Integrable (fun ω : (ℝ × ℝ) × ℝ => ω.2) (Pm S) := hS.μ_integrable.comp_snd _
  have hY := h0.add h1
  have hw0 := ((integrable_const (S.η * q 0)).add (h0.const_mul (1 - S.η))).mul_const (S.c - Δ)
  have hw1 := ((integrable_const (S.η * q 1)).add (h1.const_mul (1 - S.η))).mul_const (S.c + Δ)
  have h := ((((hw0.add hw1).neg.add ((hx.inf hY).const_mul S.r)).add
    (((hY.sub hx).sup (integrable_const 0)).const_mul S.v)).sub
    (((hx.sub hY).sup (integrable_const 0)).const_mul S.p))
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [profit_expand, wt, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
    Pi.sub_apply, Pi.neg_apply, Pi.inf_apply, Pi.sup_apply]

lemma integral_fst_fst (S : SymData) (hS : S.Standing) (g : ℝ → ℝ) :
    ∫ ω, g ω.1.1 ∂Pm S = ∫ ξ, g ξ ∂S.ν S.a0 := by
  haveI := hS.ν_prob S.a0
  haveI := hS.μ_prob
  have h1 := integral_fun_fst (μ := (S.ν S.a0).prod (S.ν S.a0)) (ν := S.μ) (fun u => g u.1)
  have h2 := integral_fun_fst (μ := S.ν S.a0) (ν := S.ν S.a0) g
  rw [Pm, h1, h2]
  simp

lemma DS_shift_le (S : SymData) (hS : S.Standing) {Δ Δ' : ℝ} (hΔ : Δ ≤ Δ') {q : Fin 2 → ℝ}
    (hq : ∀ i, 0 ≤ q i) : DS S Δ' q ≤ DS S Δ q + (Δ' - Δ) * w S (q 0) S.a0 := by
  haveI := hS.ν_prob S.a0
  haveI := Pm_prob S hS
  have hwi : Integrable (fun ω : (ℝ × ℝ) × ℝ => wt S (q 0) ω.1.1) (Pm S) := by
    haveI := hS.μ_prob
    have : Integrable (fun ω : (ℝ × ℝ) × ℝ => Dl S.K (q 0) ω.1.1) (Pm S) := by
      apply (integrable_const |q 0|).mono' ((Dl_cont S.K (q 0)).comp
        (by fun_prop : Continuous (fun ω : (ℝ × ℝ) × ℝ => ω.1.1))).aestronglyMeasurable
      exact ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using Dl_abs_le S.K (q 0) ω.1.1
    exact (integrable_const _).add (this.const_mul _)
  have hle : DS S Δ' q ≤ ∫ ω, ((S.costModel Δ).profit q ![ω.1.1, ω.1.2] ω.2
      + (Δ' - Δ) * wt S (q 0) ω.1.1) ∂Pm S := by
    rw [DS_def]
    apply integral_mono (DSprofit_integrable S hS Δ' q)
      ((DSprofit_integrable S hS Δ q).add (hwi.const_mul _))
    intro ω
    have hw1 : 0 ≤ wt S (q 1) ω.1.2 :=
      add_nonneg (mul_nonneg hS.η_mem.1 (hq 1))
        (mul_nonneg (by linarith [hS.η_mem.2]) (Dl_nonneg (hq 1)))
    have hd : 0 ≤ Δ' - Δ := sub_nonneg.mpr hΔ
    simp only [profit_expand, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply]
    nlinarith [mul_nonneg hd hw1]
  rw [integral_add (DSprofit_integrable S hS Δ q) (hwi.const_mul _), integral_const_mul,
    integral_fst_fst S hS (fun ξ => wt S (q 0) ξ)] at hle
  have hw : ∫ ξ, wt S (q 0) ξ ∂S.ν S.a0 = w S (q 0) S.a0 := by
    simp only [wt, w]
    rw [integral_add (integrable_const _) ((Dl_integrable S hS (q 0) S.a0).const_mul _)]
    simp [integral_const_mul]
  rw [hw] at hle
  exact hle

lemma profit_single (S : SymData) (Δ t : ℝ) (ξ : Fin 2 → ℝ) (x : ℝ) :
    (S.costModel Δ).profit ![t, 0] ξ x = PS S (S.c - Δ) t (ξ 0) x := by
  have h0 : Dl S.K 0 (ξ 1) = 0 := by simp [Dl_def]
  rw [profit_expand]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, PS, hh, wt, add_zero]
  ring

lemma DS_single (S : SymData) (hS : S.Standing) (Δ t : ℝ) :
    DS S Δ ![t, 0] = J S (S.c - Δ) t S.a0 := by
  haveI := hS.ν_prob S.a0
  haveI := hS.μ_prob
  rw [DS_def, ← PS_integral S hS]
  simp only [profit_single, Matrix.cons_val_zero]
  have hmp : MeasurePreserving (Prod.map Prod.fst id) (Pm S) ((S.ν S.a0).prod S.μ) :=
    (measurePreserving_fst).prod (MeasurePreserving.id _)
  have hc : Continuous (fun ω : ℝ × ℝ => PS S (S.c - Δ) t ω.1 ω.2) := by
    simp only [PS, hh, Dl_def]; fun_prop
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hc.aestronglyMeasurable]
  rfl

/-! Submodularity (as in the accepted proof of `DualSourcing.lemma_1`). -/

lemma pos_part_ineq (a b u l x : ℝ) (ha : a ≤ u) (hb : b ≤ u)
    (he : u + l = a + b) : max (a - x) 0 + max (b - x) 0 ≤ max (u - x) 0 + max (l - x) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

lemma rev_identity (r v p x y : ℝ) :
    r * min x y + v * max (y - x) 0 - p * max (x - y) 0 =
      (r + p) * y - (r + p - v) * max (y - x) 0 - p * x := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

lemma profit_submod (S : SymData) (hS : S.Standing) (Δ : ℝ) (q q' ξ : Fin 2 → ℝ) (x : ℝ) :
    (S.costModel Δ).profit (q ⊔ q') ξ x + (S.costModel Δ).profit (q ⊓ q') ξ x ≤
      (S.costModel Δ).profit q ξ x + (S.costModel Δ).profit q' ξ x := by
  simp only [profit_expand, rev_identity]
  set Y := fun (u : Fin 2 → ℝ) => Dl S.K (u 0) (ξ 0) + Dl S.K (u 1) (ξ 1) with hYdef
  have hbal : ∀ i : Fin 2, Dl S.K ((q ⊔ q') i) (ξ i) + Dl S.K ((q ⊓ q') i) (ξ i) =
      Dl S.K (q i) (ξ i) + Dl S.K (q' i) (ξ i) := by
    intro i
    rcases le_total (q i) (q' i) with h | h
    · simp [Pi.sup_apply, Pi.inf_apply, max_eq_right h, min_eq_left h, add_comm]
    · simp [Pi.sup_apply, Pi.inf_apply, max_eq_left h, min_eq_right h]
  have hwbal : ∀ i : Fin 2, wt S ((q ⊔ q') i) (ξ i) + wt S ((q ⊓ q') i) (ξ i) =
      wt S (q i) (ξ i) + wt S (q' i) (ξ i) := by
    intro i
    have := hbal i
    have hm : (q ⊔ q') i + (q ⊓ q') i = q i + q' i := by
      simp [Pi.sup_apply, Pi.inf_apply, max_add_min]
    simp only [wt]
    linear_combination S.η * hm + (1 - S.η) * this
  have hmono : ∀ u u' : Fin 2 → ℝ, u ≤ u' → Y u ≤ Y u' := by
    intro u u' h
    exact add_le_add (Dl_mono_q (h 0)) (Dl_mono_q (h 1))
  have hp := pos_part_ineq (Y q) (Y q') (Y (q ⊔ q')) (Y (q ⊓ q')) x
    (hmono _ _ le_sup_left) (hmono _ _ le_sup_right)
    (by simp only [hYdef]; linarith [hbal 0, hbal 1])
  have hm := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hS.v_lt.le)
  simp only [hYdef] at hm
  have h0 := congrArg (· * (S.c - Δ)) (hwbal 0)
  have h1 := congrArg (· * (S.c + Δ)) (hwbal 1)
  have hb0 := hbal 0
  have hb1 := hbal 1
  have r1 := rev_identity S.r S.v S.p x (Y q)
  have r2 := rev_identity S.r S.v S.p x (Y q')
  have r3 := rev_identity S.r S.v S.p x (Y (q ⊔ q'))
  have r4 := rev_identity S.r S.v S.p x (Y (q ⊓ q'))
  simp only [hYdef] at r1 r2 r3 r4
  have e1 := congrArg (fun t => (S.r + S.p) * t) (hb0)
  have e2 := congrArg (fun t => (S.r + S.p) * t) (hb1)
  linarith

lemma DS_submod (S : SymData) (hS : S.Standing) (Δ : ℝ) (q q' : Fin 2 → ℝ) :
    DS S Δ (q ⊔ q') + DS S Δ (q ⊓ q') ≤ DS S Δ q + DS S Δ q' := by
  simp only [DS_def]
  rw [← integral_add (DSprofit_integrable S hS Δ _) (DSprofit_integrable S hS Δ _),
    ← integral_add (DSprofit_integrable S hS Δ _) (DSprofit_integrable S hS Δ _)]
  exact integral_mono ((DSprofit_integrable S hS Δ _).add (DSprofit_integrable S hS Δ _))
    ((DSprofit_integrable S hS Δ _).add (DSprofit_integrable S hS Δ _))
    (fun ω => profit_submod S hS Δ q q' _ ω.2)

lemma ae_Pm (S : SymData) (hS : S.Standing) :
    ∀ᵐ ω ∂Pm S, 0 ≤ ω.1.1 ∧ 0 ≤ ω.1.2 ∧ 0 ≤ ω.2 := by
  haveI := hS.ν_prob S.a0
  haveI := hS.μ_prob
  have hν := ae_nonneg_ν S hS S.a0
  have hμ : ∀ᵐ x ∂S.μ, 0 ≤ x := by
    rw [ae_iff]; simpa only [not_le, Set.Iio] using hS.μ_nonneg
  have h1 : ∀ᵐ ω ∂Pm S, 0 ≤ ω.1.1 :=
    ((measurePreserving_fst (μ := S.ν S.a0) (ν := S.ν S.a0)).comp
      (measurePreserving_fst (μ := (S.ν S.a0).prod (S.ν S.a0)) (ν := S.μ))).quasiMeasurePreserving.tendsto_ae.eventually hν
  have h2 : ∀ᵐ ω ∂Pm S, 0 ≤ ω.1.2 :=
    ((measurePreserving_snd (μ := S.ν S.a0) (ν := S.ν S.a0)).comp
      (measurePreserving_fst (μ := (S.ν S.a0).prod (S.ν S.a0)) (ν := S.μ))).quasiMeasurePreserving.tendsto_ae.eventually hν
  have h3 : ∀ᵐ ω ∂Pm S, 0 ≤ ω.2 :=
    (measurePreserving_snd (μ := (S.ν S.a0).prod (S.ν S.a0)) (ν := S.μ)).quasiMeasurePreserving.tendsto_ae.eventually hμ
  filter_upwards [h1, h2, h3] with ω a b c using ⟨a, b, c⟩

lemma DS_bound (S : SymData) (hS : S.Standing) {Δ : ℝ} (h0 : 0 ≤ Δ) (hc : Δ ≤ S.c)
    {q : Fin 2 → ℝ} (hq : ∀ i, 0 ≤ q i) : DS S Δ q ≤ (S.r + |S.v|) * (2 * S.K) := by
  haveI := Pm_prob S hS
  rw [DS_def]
  have := integral_mono_ae (DSprofit_integrable S hS Δ q) (integrable_const ((S.r + |S.v|) * (2 * S.K))) ?_
  · simpa using this
  filter_upwards [ae_Pm S hS] with ω hω
  simp only [profit_expand, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hK := hS.K_pos.le
  have y0 := Dl_nonneg (K := S.K) (ξ := ω.1.1) (hq 0)
  have y1 := Dl_nonneg (K := S.K) (ξ := ω.1.2) (hq 1)
  have y0' := Dl_le_K (q := q 0) hK hω.1
  have y1' := Dl_le_K (q := q 1) hK hω.2.1
  set Y := Dl S.K (q 0) ω.1.1 + Dl S.K (q 1) ω.1.2
  have hw0 : 0 ≤ wt S (q 0) ω.1.1 * (S.c - Δ) :=
    mul_nonneg (add_nonneg (mul_nonneg hS.η_mem.1 (hq 0))
      (mul_nonneg (by linarith [hS.η_mem.2]) y0)) (by linarith)
  have hw1 : 0 ≤ wt S (q 1) ω.1.2 * (S.c + Δ) :=
    mul_nonneg (add_nonneg (mul_nonneg hS.η_mem.1 (hq 1))
      (mul_nonneg (by linarith [hS.η_mem.2]) y1)) (by linarith [hS.c_pos])
  have hmin : S.r * min ω.2 Y ≤ S.r * (2 * S.K) :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (by simp only [Y]; linarith)) hS.r_nonneg
  have hm0 : 0 ≤ max (Y - ω.2) 0 := le_max_right _ _
  have hm1 : max (Y - ω.2) 0 ≤ 2 * S.K := max_le (by simp only [Y]; linarith [hω.2.2]) (by linarith)
  have hv : S.v * max (Y - ω.2) 0 ≤ |S.v| * (2 * S.K) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hm0).trans
      (mul_le_mul_of_nonneg_left hm1 (abs_nonneg _))
  have hp : 0 ≤ S.p * max (ω.2 - Y) 0 := mul_nonneg hS.p_nonneg (le_max_right _ _)
  linarith

lemma PiDS_eq (S : SymData) (Δ : ℝ) :
    (S.costModel Δ).PiDS = sSup ((fun q => DS S Δ q) '' {q : Fin 2 → ℝ | ∀ i, 0 ≤ q i}) := rfl

lemma vec_eq (q : Fin 2 → ℝ) : q = ![q 0, q 1] := by
  funext i; fin_cases i <;> rfl

lemma DS_step (S : SymData) (hS : S.Standing) {Δp Δ z : ℝ} (hp0 : 0 ≤ Δp) (hpΔ : Δp ≤ Δ)
    (hc : Δ < S.c) (hz : z ∈ Icc 0 S.K) (hzm : IsMaxOn (φ S (S.c - Δ)) (Icc 0 S.K) z) :
    (S.costModel Δ).PiDS ≤ (S.costModel Δp).PiDS +
      (Δ - Δp) * w S (qbar S (S.c - Δ) z S.a0) S.a0 := by
  rw [PiDS_eq, PiDS_eq]
  set qb := qbar S (S.c - Δ) z S.a0
  have hqb := (qbar_mem S hS (S.c - Δ) z hz S.a0).1
  have hC : 0 ≤ S.c - Δ := by linarith
  have hbdd : BddAbove ((fun q => DS S Δp q) '' {q : Fin 2 → ℝ | ∀ i, 0 ≤ q i}) := by
    refine ⟨(S.r + |S.v|) * (2 * S.K), ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact DS_bound S hS hp0 (by linarith) hq
  refine csSup_le ⟨DS S Δ 0, 0, fun _ => le_rfl, rfl⟩ ?_
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨qt, hqt, hqt0, hle⟩ : ∃ qt : Fin 2 → ℝ, (∀ i, 0 ≤ qt i) ∧ qt 0 ≤ qb ∧
      DS S Δ q ≤ DS S Δ qt := by
    by_cases h : q 0 ≤ qb
    · exact ⟨q, hq, h, le_rfl⟩
    · push_neg at h
      refine ⟨![qb, q 1], ?_, by simp, ?_⟩
      · intro i; fin_cases i
        · simpa using hqb.1
        · simpa using hq 1
      · have hs := DS_submod S hS Δ ![q 0, 0] ![qb, q 1]
        have e1 : (![q 0, 0] ⊔ ![qb, q 1] : Fin 2 → ℝ) = q := by
          rw [vec_eq q]
          funext i; fin_cases i
          · simp [max_eq_left h.le]
          · simp [max_eq_right (hq 1)]
        have e2 : (![q 0, 0] ⊓ ![qb, q 1] : Fin 2 → ℝ) = ![qb, 0] := by
          funext i; fin_cases i
          · simp [min_eq_right h.le]
          · simp [min_eq_left (hq 1)]
        rw [e1, e2, DS_single S hS, DS_single S hS] at hs
        have := qbar_max S hS (S.c - Δ) z hz hzm hC S.a0 (hq 0)
        linarith
  have h1 := DS_shift_le S hS hpΔ hqt
  have h2 : DS S Δp qt ≤ sSup ((fun q => DS S Δp q) '' {q : Fin 2 → ℝ | ∀ i, 0 ≤ q i}) :=
    le_csSup hbdd ⟨qt, hqt, rfl⟩
  have h3 := w_mono S hS (hqt 0) hqt0 (le_refl S.a0)
  have h4 := mul_le_mul_of_nonneg_left h3 (sub_nonneg.mpr hpΔ)
  linarith

/-! ## Telescoping -/

lemma telescope (F W : ℝ → ℝ) (B t s : ℝ) (hts : t ≤ s)
    (hW : ∀ u ∈ Icc t s, 0 ≤ W u ∧ W u ≤ B)
    (hstep : ∀ u v, t ≤ u → u ≤ v → v ≤ s → (v - u) * (W u - W v) ≤ F v - F u) :
    F t ≤ F s := by
  have hB : 0 ≤ B := (hW t ⟨le_rfl, hts⟩).1.trans (hW t ⟨le_rfl, hts⟩).2
  have key : ∀ n : ℕ, 0 < n → F t - F s ≤ (s - t) * B / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set δ := (s - t) / n with hδ
    have hδ0 : 0 ≤ δ := div_nonneg (by linarith) hn'.le
    have hpt : ∀ m : ℕ, m ≤ n → t ≤ t + m * δ ∧ t + m * δ ≤ s := by
      intro m hm
      refine ⟨by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)], ?_⟩
      have : (m : ℝ) * δ ≤ n * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hδ0
      have e : (n : ℝ) * δ = s - t := by rw [hδ]; field_simp
      linarith
    have ind : ∀ m : ℕ, m ≤ n → δ * (W t - W (t + m * δ)) ≤ F (t + m * δ) - F t := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have ih' := ih (Nat.le_of_succ_le hk)
        have hu := hpt k (Nat.le_of_succ_le hk)
        have hv := hpt (k + 1) hk
        have hst := hstep (t + k * δ) (t + (k + 1 : ℕ) * δ) hu.1
          (by push_cast; nlinarith) hv.2
        have e : t + ((k + 1 : ℕ) : ℝ) * δ - (t + k * δ) = δ := by push_cast; ring
        rw [e] at hst
        nlinarith
    have hn := ind n le_rfl
    have e : t + (n : ℝ) * δ = s := by rw [hδ]; field_simp; ring
    rw [e] at hn
    have hWs := hW s ⟨hts, le_rfl⟩
    have hWt := hW t ⟨le_rfl, hts⟩
    have : δ * (W t - W s) ≥ -(δ * B) := by nlinarith
    have e2 : δ * B = (s - t) * B / n := by rw [hδ]; ring
    linarith
  by_contra hlt
  push_neg at hlt
  set ε := F t - F s
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((s - t) * B / ε)
  have hn0 : 0 < n := by
    have : (0 : ℝ) ≤ (s - t) * B / ε := div_nonneg (mul_nonneg (by linarith) hB) hε.le
    exact_mod_cast this.trans_lt hn
  have h := key n hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [div_lt_iff₀ hε] at hn
  rw [le_div_iff₀ hn'] at h
  nlinarith

/-! ## Main argument -/

lemma key (S : SymData) (hS : S.Standing) (Δ : ℝ) (hΔ : Δ ∈ Ico 0 S.c) :
    ∃ W, 0 ≤ W ∧ W ≤ S.K ∧
      (∀ Δ' ∈ Ico 0 S.c, Δ ≤ Δ' →
        (S.costModel Δ).PiSSI + (Δ' - Δ) * W ≤ (S.costModel Δ').PiSSI) ∧
      (∀ Δp, 0 ≤ Δp → Δp ≤ Δ →
        (S.costModel Δ).PiDS ≤ (S.costModel Δp).PiDS + (Δ - Δp) * W) := by
  obtain ⟨z, hz, hzm⟩ := exists_z S hS (S.c - Δ)
  have hqb := (qbar_mem S hS (S.c - Δ) z hz S.a0).1
  refine ⟨w S (qbar S (S.c - Δ) z S.a0) S.a0, w_nonneg S hS hqb.1 _,
    (w_le S hS hqb.1 _).trans (hqb.2.trans hz.2), ?_, ?_⟩
  · intro Δ' hΔ' hle
    rw [PiSSI_eq S hS hΔ.1 hΔ.2, PiSSI_eq S hS hΔ'.1 hΔ'.2]
    have := SSIv_step S hS (C := S.c - Δ) (C' := S.c - Δ') (by linarith [hΔ'.2]) (by linarith)
      hz hzm
    have e : S.c - Δ - (S.c - Δ') = Δ' - Δ := by ring
    rw [e] at this
    exact this
  · intro Δp hp0 hpΔ
    exact DS_step S hS hp0 hpΔ hΔ.2 hz hzm

end MSRT7

open MSRT7 in
theorem solution (S : MitigateSupplyRisk.Heterogeneity.SymData)
    (hS : S.Standing) :
    MonotoneOn (fun Δ => (S.costModel Δ).PiSSI - (S.costModel Δ).PiDS) (Set.Ico 0 S.c) := by
  have key' : ∀ Δ, ∃ W : ℝ, Δ ∈ Set.Ico 0 S.c → (0 ≤ W ∧ W ≤ S.K ∧
      (∀ Δ' ∈ Set.Ico 0 S.c, Δ ≤ Δ' →
        (S.costModel Δ).PiSSI + (Δ' - Δ) * W ≤ (S.costModel Δ').PiSSI) ∧
      (∀ Δp, 0 ≤ Δp → Δp ≤ Δ →
        (S.costModel Δ).PiDS ≤ (S.costModel Δp).PiDS + (Δ - Δp) * W)) := by
    intro Δ
    by_cases h : Δ ∈ Set.Ico 0 S.c
    · obtain ⟨W, hW⟩ := key S hS Δ h
      exact ⟨W, fun _ => hW⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Wf hWf using key'
  intro t ht s hs hts
  have hsub : ∀ u ∈ Set.Icc t s, u ∈ Set.Ico 0 S.c := fun u hu =>
    ⟨ht.1.trans hu.1, lt_of_le_of_lt hu.2 hs.2⟩
  apply telescope _ Wf S.K t s hts
  · intro u hu
    exact ⟨(hWf u (hsub u hu)).1, (hWf u (hsub u hu)).2.1⟩
  · intro u v htu huv hvs
    have hu := hsub u ⟨htu, huv.trans hvs⟩
    have hv := hsub v ⟨htu.trans huv, hvs⟩
    have h1 := (hWf u hu).2.2.1 v hv huv
    have h2 := (hWf v hv).2.2.2 u hu.1 huv
    nlinarith

#print axioms solution
