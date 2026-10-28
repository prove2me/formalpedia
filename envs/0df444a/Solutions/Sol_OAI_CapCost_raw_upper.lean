-- Prove2me | solution 1 for OAI.CapCost.raw_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:49:53.475994+00:00
-- url     : https://prove2.me/submissions/e71bc038-22a0-4239-a48f-3519d4c31a73

import Mathlib
import Definitions.Def_OAIQ16Cd002
import Theorems.Thm_OAI_CapGeometry_halfcap_ratio

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SphericalLaw
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace SphericalLaw
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

lemma continuous_act {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) : Continuous (act e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _

lemma cone_preimage {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Sphere n)) :
    Ioo (0 : ℝ) 1 • ((↑) '' (act e ⁻¹' S)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' S)) := by
  ext y
  constructor
  · rintro ⟨r, hr, x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨r, hr, e u.val, ⟨act e u, hu, rfl⟩, (e.map_smul r u.val).symm⟩
  · intro hy
    obtain ⟨r, hr, x, hx, he⟩ := hy
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨r, hr, e.symm u.val, ?_, ?_⟩
    · refine ⟨act e.symm u, ?_, rfl⟩
      change act e (act e.symm u) ∈ S
      have hh : act e (act e.symm u) = u := Subtype.ext (e.apply_symm_apply u.val)
      simpa only [hh] using hu
    · apply e.injective
      rw [e.map_smul, e.apply_symm_apply]
      exact he

lemma invariant {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Sphere n))
    (hS : MeasurableSet S) : σ n (act e ⁻¹' S) = σ n S := by
  simp only [σ, Measure.smul_apply]
  congr 1
  rw [Measure.toSphere_apply' _ ((continuous_act e).measurable hS),
    Measure.toSphere_apply' _ hS, cone_preimage]
  congr 1
  change volume (e.toHomeomorph ⁻¹' (Ioo (0:ℝ) 1 • ((↑) '' S))) = _
  rw [← e.toHomeomorph.measurableEmbedding.map_apply]
  exact congrArg (fun μ : Measure (Space n) => μ (Ioo (0:ℝ) 1 • ((↑) '' S)))
    e.measurePreserving.map_eq

lemma cap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (cap x t) :=
  isOpen_lt continuous_const ((continuous_subtype_val.inner continuous_const).abs)

lemma cap_measurable {n : ℕ} (x : Space n) (t : ℝ) : MeasurableSet (cap x t) :=
  (cap_open x t).measurableSet

lemma positive_open {n : ℕ} [NeZero n] (U : Set (Sphere n))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < σ n U := by
  rw [σ, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_pos
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact hU.measure_ne_zero (volume : Measure (Space n)).toSphere hne

lemma cap_equal_norm {n : ℕ} {x y : Space n} (hxy : ‖x‖ = ‖y‖) (t : ℝ) :
    σ n (cap x t) = σ n (cap y t) := by
  let e := (Submodule.span ℝ ({x-y} : Set (Space n)))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  have hp : act e ⁻¹' cap y t = cap x t := by
    ext u
    change (t < |inner ℝ (e u.val) y|) ↔ (t < |inner ℝ u.val x|)
    rw [← he, e.inner_map_map]
  rw [← hp]
  exact invariant e _ (cap_measurable _ _)

end SphericalLaw

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapGeometry
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapGeometry
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
open SphericalLaw

lemma halfcap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (halfcap x t) :=
  isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)

lemma halfcap_measurable {n : ℕ} (x : Space n) (t : ℝ) : MeasurableSet (halfcap x t) :=
  (halfcap_open x t).measurableSet

lemma halfcap_positive {n : ℕ} [NeZero n] (u : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < σ n (halfcap u.val t) := by
  apply positive_open _ (halfcap_open _ _) ⟨u, ?_⟩
  change t < inner ℝ u.val u.val
  simpa only [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp u.property, one_pow] using ht

lemma halfcap_equal_norm {n : ℕ} {x y : Space n} (hxy : ‖x‖ = ‖y‖) (t : ℝ) :
    σ n (halfcap x t) = σ n (halfcap y t) := by
  let e := (Submodule.span ℝ ({x-y} : Set (Space n)))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  have hp : act e ⁻¹' halfcap y t = halfcap x t := by
    ext u
    change (t < inner ℝ (e u.val) y) ↔ (t < inner ℝ u.val x)
    rw [← he, e.inner_map_map]
  rw [← hp]
  exact invariant e _ (halfcap_measurable _ _)

end CapGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapOverlap
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapOverlap
open Set MeasureTheory Metric SphericalLaw CapGeometry CapLens

lemma cap_antimono {n : ℕ} [NeZero n] (e : Sphere n) {t s : ℝ} (hts : t ≤ s) :
    (σ n).real (halfcap e.val s) ≤ (σ n).real (halfcap e.val t) :=
  measureReal_mono (fun _ hw => hts.trans_lt hw) (measure_ne_top _ _)

end CapOverlap

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapAffinity
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapAffinity
open Set MeasureTheory Metric SphericalLaw CapGeometry CapOverlap

lemma halfcap_signed_mass {n : ℕ} (e : Sphere n) (b : Bool) (t : ℝ) :
    σ n (halfcap (signed e b).val t) = σ n (halfcap e.val t) :=
  halfcap_equal_norm ((mem_sphere_zero_iff_norm.mp (signed e b).property).trans
    (mem_sphere_zero_iff_norm.mp e.property).symm) t

lemma cap_eq_union {n : ℕ} (e : Sphere n) (t : ℝ) :
    cap e.val t = ⋃ b : Bool, halfcap (signed e b).val t := by
  ext w
  simp only [cap, halfcap, mem_ofPred_eq, mem_iUnion, Bool.exists_bool,
    signed, Bool.false_eq_true, ↓reduceIte, inner_neg_right]
  exact lt_abs.trans (by tauto)

lemma cap_mass {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : 0 ≤ t) :
    (σ n).real (cap e.val t) = 2*(σ n).real (halfcap e.val t) := by
  rw [cap_eq_union]
  have he : (⋃ b : Bool, halfcap (signed e b).val t) =
      halfcap (signed e false).val t ∪ halfcap (signed e true).val t := by
    ext w; simp only [mem_iUnion, Bool.exists_bool, mem_union]
  rw [he]
  have hd : Disjoint (halfcap (signed e false).val t) (halfcap (signed e true).val t) := by
    apply disjoint_left.mpr
    intro w hw1 hw2
    change t < inner ℝ w.val (-e.val) at hw1
    rw [inner_neg_right] at hw1
    change t < inner ℝ w.val e.val at hw2
    linarith
  rw [measureReal_union hd (halfcap_measurable _ _), measureReal_def, halfcap_signed_mass]
  change (σ n).real (halfcap e.val t) + (σ n).real (halfcap e.val t) = _
  ring

end CapAffinity

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapCost
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapCost
open MeasureTheory SphericalLaw CapGeometry CapAffinity
open scoped ENNReal NNReal

lemma intensity_real {n : ℕ} (e : Sphere n) (t : ℝ) (E : Set (Sphere n)) :
    (intensity e t).real E = (σ n).real E/(σ n).real (cap e.val t) := by
  change (((rate e t : ℝ≥0∞)*(σ n) E).toReal) = _
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  change ((σ n).real (cap e.val t))⁻¹ * (σ n).real E = _
  ring

lemma halfcap_real_pos {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < (σ n).real (halfcap e.val t) :=
  ENNReal.toReal_pos (ne_of_gt (halfcap_positive e ht)) (measure_ne_top _ _)

lemma intensity_cap {n : ℕ} [NeZero n] (e f : Sphere n) {t s : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (hs : 0 ≤ s) :
    (intensity e t).real (cap f.val s) =
      (σ n).real (halfcap f.val s)/(σ n).real (halfcap f.val t) := by
  rw [intensity_real]
  have heq : (σ n).real (cap e.val t) = (σ n).real (cap f.val t) :=
    congrArg ENNReal.toReal (cap_equal_norm ((mem_sphere_zero_iff_norm.mp e.property).trans
      (mem_sphere_zero_iff_norm.mp f.property).symm) t)
  rw [heq,cap_mass f ht,cap_mass f hs]
  field_simp [(halfcap_real_pos f ht1).ne']

lemma log_decrease {n : ℕ} [NeZero n] (e : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (htu : t ≤ u)
    (_hls : l ≤ s) (hsu : s ≤ u) :
    Real.log ((σ n).real (halfcap e.val t))-Real.log ((σ n).real (halfcap e.val s)) ≤
      (n:ℝ)*(1/l+1/(1-u^2))*max (s-t) 0 := by
  have htpos := halfcap_real_pos e (htu.trans_lt hu)
  have hspos := halfcap_real_pos e (hsu.trans_lt hu)
  have hA : 0 ≤ 1/l+1/(1-u^2) := by
    have hu0 := hl.trans_le (hlt.trans htu)
    have hh : 0 < 1-u^2 := by nlinarith
    positivity
  by_cases hts : t ≤ s
  · rw [max_eq_left (sub_nonneg.mpr hts)]
    have hh := (halfcap_ratio e hl hu hlt hts hsu).1
    have hlo := Real.log_le_log (Real.exp_pos _) hh
    rw [Real.log_exp,Real.log_div hspos.ne' htpos.ne'] at hlo
    have hmul := mul_nonneg hA (sub_nonneg.mpr hts)
    nlinarith
  · rw [max_eq_right (by linarith : s-t ≤ 0),mul_zero]
    have hm : (σ n).real (halfcap e.val t) ≤ (σ n).real (halfcap e.val s) :=
      CapOverlap.cap_antimono e (le_of_not_ge hts)
    exact sub_nonpos.mpr (Real.log_le_log htpos hm)

lemma raw_upper_oai {n : ℕ} [NeZero n] (e f : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (htu : t ≤ u)
    (hls : l ≤ s) (hsu : s ≤ u) :
    (intensity e t).real (cap f.val s) ≤
      Real.exp ((n:ℝ)*(1/l+1/(1-u^2))*max (t-s) 0) := by
  rw [intensity_cap e f (hl.trans_le hlt).le (htu.trans_lt hu) (hl.trans_le hls).le]
  apply (Real.log_le_iff_le_exp (div_pos (halfcap_real_pos f (hsu.trans_lt hu))
    (halfcap_real_pos f (htu.trans_lt hu)))).mp
  rw [Real.log_div (halfcap_real_pos f (hsu.trans_lt hu)).ne'
    (halfcap_real_pos f (htu.trans_lt hu)).ne']
  exact log_decrease f hl hu hls hsu hlt htu

end CapCost

end OAI
end

theorem solution : type_of% @OAI.CapCost.raw_upper_oai := @OAI.CapCost.raw_upper_oai
