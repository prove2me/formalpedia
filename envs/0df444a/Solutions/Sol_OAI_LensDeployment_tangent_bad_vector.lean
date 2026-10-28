-- Prove2me | solution 1 for OAI.LensDeployment.tangent_bad_vector
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:49:57.321985+00:00
-- url     : https://prove2.me/submissions/6d5356c8-af73-43b9-b693-2221f8c6a8fa

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

lemma positive_open {n : ℕ} [NeZero n] (U : Set (Sphere n))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < σ n U := by
  rw [σ, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_pos
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact hU.measure_ne_zero (volume : Measure (Space n)).toSphere hne

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
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapLens
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

universe u_1

namespace CapLens
open Set MeasureTheory Metric SphericalLaw CapGeometry
open scoped ENNReal Pointwise

lemma inner_unit {n : ℕ} (x : Space n) (hx : x ≠ 0) (y : Space n) :
    inner ℝ y (unit x hx).val = inner ℝ y x / ‖x‖ := by
  simp [unit, inner_smul_right, div_eq_mul_inv, mul_comm]

lemma tangent_bad_subset {n : ℕ} (e v : Sphere n)
    (hev : inner ℝ e.val v.val = 0) {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    ∃ w : Sphere n, halfcap e.val t ∩ {u : Sphere n | inner ℝ u.val v.val < -h} ⊆
      halfcap w.val (Real.sqrt (t^2+h^2)) := by
  let z := t • e.val - h • v.val
  have hn : ‖z‖^2 = t^2+h^2 := by
    dsimp [z]
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mem_sphere_zero_iff_norm.mp e.property, mem_sphere_zero_iff_norm.mp v.property,
      inner_smul_left, inner_smul_right, hev]
    simp [sq_abs]
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    nlinarith [sq_nonneg h]
  refine ⟨unit z hz, ?_⟩
  intro u hu
  change Real.sqrt (t^2+h^2) < inner ℝ u.val (unit z hz).val
  rw [inner_unit, lt_div_iff₀ (norm_pos_iff.mpr hz)]
  have he : Real.sqrt (t^2+h^2) = ‖z‖ := by rw [← hn, Real.sqrt_sq (norm_nonneg z)]
  rw [he]
  have hu1 : t < inner ℝ u.val e.val := hu.1
  have hu2 : inner ℝ u.val v.val < -h := hu.2
  have hprod := mul_lt_mul_of_pos_left hu1 ht
  have hprod2 := mul_le_mul_of_nonneg_left hu2.le hh
  dsimp [z]
  rw [inner_sub_right, inner_smul_right, inner_smul_right]
  nlinarith [hn]

lemma tangent_bad_measure {n : ℕ} [NeZero n] (e v : Sphere n)
    (hev : inner ℝ e.val v.val = 0) {l u t h : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
    (hqu : Real.sqrt (t^2+h^2) ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l) :
    (σ n).real (halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val v.val < -h}) ≤
      Real.exp (-(n:ℝ)*l*h^2/4) * (σ n).real (halfcap e.val t) := by
  have ht : 0 < t := hl.trans_le hlt
  let q := Real.sqrt (t^2+h^2)
  have hq2 : q^2 = t^2+h^2 := Real.sq_sqrt (by positivity)
  have htq : t ≤ q := by
    dsimp [q]
    apply (Real.le_sqrt ht.le (by positivity)).mpr
    nlinarith [sq_nonneg h]
  have ht1 : t < 1 := (htq.trans hqu).trans_lt hu
  have hq1 : q < 1 := hqu.trans_lt hu
  have hgap : h^2/2 ≤ q-t := by nlinarith [sq_nonneg (q-t), mul_nonneg (sub_nonneg.mpr htq) (by linarith : 0 ≤ 2-q-t)]
  obtain ⟨w, hw⟩ := tangent_bad_subset e v hev ht hh
  have hmono := measureReal_mono hw (measure_ne_top (σ n) _)
  have heq : (σ n).real (halfcap w.val q) = (σ n).real (halfcap e.val q) := by
    exact congrArg ENNReal.toReal (halfcap_equal_norm ((mem_sphere_zero_iff_norm.mp w.property).trans
      (mem_sphere_zero_iff_norm.mp e.property).symm) q)
  rw [heq] at hmono
  have hrat := (halfcap_ratio e hl hu hlt htq hqu).2
  have htpos : 0 < (σ n).real (halfcap e.val t) :=
    ENNReal.toReal_pos (ne_of_gt (halfcap_positive e ht1)) (measure_ne_top _ _)
  have hcoef : ((1/l+1/(1-u^2))-(n:ℝ)*l)*(q-t) ≤ -(n:ℝ)*l*h^2/4 := by
    have hn0 : 0 ≤ (n:ℝ)*l := mul_nonneg (Nat.cast_nonneg n) hl.le
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hgap),
      mul_nonneg (by linarith : 0 ≤ (n:ℝ)*l/2-(1/l+1/(1-u^2))) (sub_nonneg.mpr htq)]
  exact hmono.trans (((div_le_iff₀ htpos).mp hrat).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcoef) htpos.le))

end CapLens

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LensDeployment
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

universe u_1 u_2

namespace LensDeployment
open Set MeasureTheory Metric SphericalLaw CapGeometry CapLens CapCost CapAffinity
open scoped ENNReal NNReal

lemma tangent_bad_vector_oai {n : ℕ} [NeZero n] (e : Sphere n) (v : Space n)
    (hev : inner ℝ e.val v = 0) {l u t h Φ : ℝ}
    (hΦ : ‖v‖ ≤ Φ) (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
    (hqu : Real.sqrt (t^2+h^2) ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l) :
    (σ n).real (halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val v < -Φ*h}) ≤
      Real.exp (-(n:ℝ)*l*h^2/4)*(σ n).real (halfcap e.val t) := by
  by_cases hv : v = 0
  · have hΦ0 : 0 ≤ Φ := (norm_nonneg v).trans hΦ
    have hem : halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val v < -Φ*h} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro w ⟨_,hw⟩
      simp only [mem_ofPred_eq,hv,inner_zero_right] at hw
      nlinarith
    rw [hem,measureReal_empty]
    positivity
  · have hvp := norm_pos_iff.mpr hv
    have hsub : halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val v < -Φ*h} ⊆
        halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val (unit v hv).val < -h} := by
      rintro w ⟨hw1,hw2⟩
      refine ⟨hw1,?_⟩
      change inner ℝ w.val (unit v hv).val < -h
      rw [inner_unit,div_lt_iff₀ hvp]
      have hm := mul_le_mul_of_nonneg_right hΦ hh
      exact hw2.trans_le (by nlinarith)
    exact (measureReal_mono hsub).trans (tangent_bad_measure e (unit v hv)
      (by rw [inner_unit,hev,zero_div]) hl hu hlt hh hqu hdim)

end LensDeployment

end OAI
end

theorem solution : type_of% @OAI.LensDeployment.tangent_bad_vector_oai := @OAI.LensDeployment.tangent_bad_vector_oai
