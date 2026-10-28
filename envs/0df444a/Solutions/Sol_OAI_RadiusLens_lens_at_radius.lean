-- Prove2me | solution 1 for OAI.RadiusLens.lens_at_radius
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:53:00.713051+00:00
-- url     : https://prove2.me/submissions/3e6177a2-6d39-475c-9803-27e3b0529bab

import Mathlib
import Definitions.Def_OAIQ16Cd002
import Theorems.Thm_OAI_CapGeometry_halfcap_ratio
import Theorems.Thm_OAI_LensDeployment_tangent_bad_vector

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

lemma cap_positive {n : ℕ} [NeZero n] (u : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < σ n (cap u.val t) := by
  apply positive_open _ (cap_open _ _) ⟨u, ?_⟩
  change t < |inner ℝ u.val u.val|
  have hnorm : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simpa only [real_inner_self_eq_norm_sq, hnorm, one_pow, abs_one] using ht

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
-- module Solutions.OAIQ16_CD.TranslativeCovering_ProjectiveCaps
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

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace ProjectiveCaps
open InnerProductGeometry Real
variable {V : Type u_1} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma angle_nonneg (x y : V) : 0 ≤ angle x y :=
  le_min (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_nonneg _ _)

end ProjectiveCaps

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
open Set MeasureTheory Metric SphericalLaw CapGeometry

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

lemma cap_real_pos {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < (σ n).real (cap e.val t) :=
  ENNReal.toReal_pos (ne_of_gt (cap_positive e ht)) (measure_ne_top _ _)

lemma halfcap_real_pos {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < (σ n).real (halfcap e.val t) :=
  ENNReal.toReal_pos (ne_of_gt (halfcap_positive e ht)) (measure_ne_top _ _)

end CapCost

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

lemma projected_norm {n : ℕ} (e f : Sphere n) :
    ‖f.val-(inner ℝ e.val f.val) • e.val‖^2 = 1-(inner ℝ e.val f.val)^2 := by
  have he := mem_sphere_zero_iff_norm.mp e.property
  have hf := mem_sphere_zero_iff_norm.mp f.property
  rw [norm_sub_sq_real, norm_smul,Real.norm_eq_abs,he,hf,inner_smul_right,real_inner_comm f.val e.val]
  simp only [mul_one,one_pow,sq_abs]
  ring

lemma projected_bound {n : ℕ} (e f : Sphere n) {Φ : ℝ}
    (hΦ : 0 ≤ Φ) (hangle : InnerProductGeometry.angle e.val f.val ≤ Φ) :
    1-Φ^2/2 ≤ inner ℝ e.val f.val ∧
      ‖f.val-(inner ℝ e.val f.val) • e.val‖ ≤ Φ := by
  have he := mem_sphere_zero_iff_norm.mp e.property
  have hf := mem_sphere_zero_iff_norm.mp f.property
  have ha := InnerProductGeometry.angle_nonneg e.val f.val
  have hsq := pow_le_pow_left₀ ha hangle 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := InnerProductGeometry.angle e.val f.val)
  have hacos := InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one he hf
  have hac : inner ℝ e.val f.val ≤ 1 := by rw [hacos]; exact Real.cos_le_one _
  have ha0 : -1 ≤ inner ℝ e.val f.val := by rw [hacos]; exact Real.neg_one_le_cos _
  have hlow : 1-Φ^2/2 ≤ inner ℝ e.val f.val := by rw [hacos]; linarith
  refine ⟨hlow,?_⟩
  have hn := projected_norm e f
  have hs : 1-(inner ℝ e.val f.val)^2 ≤ Φ^2 := by
    nlinarith [sq_nonneg (inner ℝ e.val f.val-1)]
  nlinarith [norm_nonneg (f.val-(inner ℝ e.val f.val) • e.val)]

lemma ordinary_lens {n : ℕ} [NeZero n] {I : Type u_1} [Fintype I]
    (e : Sphere n) (f : I → Sphere n) (τ : I → ℝ) {l u t h Φ : ℝ}
    (hΦ : 0 ≤ Φ) (hΦsmall : Φ^2 < 2)
    (hangle : ∀ i,InnerProductGeometry.angle e.val (f i).val ≤ Φ)
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
    (hqu : Real.sqrt (t^2+h^2) ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
    (hτ : ∀ i,τ i ≤ t-Φ^2/2-Φ*h) :
    (1-(Fintype.card I:ℝ)*Real.exp (-(n:ℝ)*l*h^2/4))*(σ n).real (halfcap e.val t) ≤
      (σ n).real (⋂ i,halfcap (f i).val (τ i)) := by
  let a := fun i => inner ℝ e.val (f i).val
  let v := fun i => (f i).val-a i • e.val
  have hv (i : I) : inner ℝ e.val (v i) = 0 := by
    dsimp [v,a]
    rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp e.property]
    ring
  have hb (i : I) := projected_bound e (f i) hΦ (hangle i)
  have hap (i : I) : 0 < a i := by dsimp [a]; linarith [(hb i).1]
  have ht0 : 0 < t := hl.trans_le hlt
  have ht1 : t < 1 := by
    have hsq := Real.sq_sqrt (show 0 ≤ t^2+h^2 by positivity)
    have htq : t ≤ Real.sqrt (t^2+h^2) := by nlinarith [Real.sqrt_nonneg (t^2+h^2),sq_nonneg h]
    exact (htq.trans hqu).trans_lt hu
  have hti (i : I) : τ i ≤ a i*t-Φ*h := by
    have hmul := mul_le_mul_of_nonneg_right (hb i).1 ht0.le
    have hh2 := mul_le_mul_of_nonneg_left ht1.le (sq_nonneg Φ)
    dsimp [a]
    nlinarith [hτ i]
  let B : I → Set (Sphere n) := fun i => halfcap e.val t ∩ {w | inner ℝ w.val (v i) < -Φ*h}
  have hBm (i : I) : MeasurableSet (B i) := (halfcap_measurable _ _).inter
    (isOpen_lt (continuous_subtype_val.inner continuous_const) continuous_const).measurableSet
  have hsub : (⋃ i,B i) ⊆ halfcap e.val t := iUnion_subset fun _ => inter_subset_left
  have hlens : halfcap e.val t \ (⋃ i,B i) ⊆ ⋂ i,halfcap (f i).val (τ i) := by
    rintro w ⟨hw,hwB⟩
    apply mem_iInter.mpr
    intro i
    have hwv : -Φ*h ≤ inner ℝ w.val (v i) := by
      by_contra hh
      exact hwB (mem_iUnion.mpr ⟨i,hw,lt_of_not_ge hh⟩)
    change τ i < inner ℝ w.val (f i).val
    have heq : (f i).val = a i • e.val+v i := by dsimp [v]; abel
    rw [heq,inner_add_right,inner_smul_right]
    have hmm := mul_lt_mul_of_pos_left hw (hap i)
    linarith [hti i]
  have hsum : (σ n).real (⋃ i,B i) ≤
      (Fintype.card I:ℝ)*Real.exp (-(n:ℝ)*l*h^2/4)*(σ n).real (halfcap e.val t) := by
    calc
      _ ≤ ∑ i,(σ n).real (B i) := measureReal_iUnion_fintype_le B
      _ ≤ ∑ _i : I,Real.exp (-(n:ℝ)*l*h^2/4)*(σ n).real (halfcap e.val t) :=
        Finset.sum_le_sum fun i _ => tangent_bad_vector e (v i) (hv i) (hb i).2 hl hu hlt hh hqu hdim
      _ = _ := by simp; ring
  have hm := measureReal_mono (μ := σ n) hlens
  rw [measureReal_sdiff hsub (MeasurableSet.iUnion hBm)] at hm
  linarith

lemma orient_axis {n : ℕ} (e f : Sphere n) :
    ∃ g : Sphere n, (∀ t,cap g.val t = cap f.val t) ∧
      InnerProductGeometry.angle e.val g.val = ProjectiveCaps.angle e.val f.val := by
  by_cases h : InnerProductGeometry.angle e.val f.val ≤ InnerProductGeometry.angle e.val (-f.val)
  · exact ⟨f,fun _ => rfl,(min_eq_left h).symm⟩
  · refine ⟨⟨-f.val,by simpa only [mem_sphere_zero_iff_norm,norm_neg] using f.property⟩,?_,?_⟩
    · intro t; ext w; simp [cap,inner_neg_right,abs_neg]
    · exact (min_eq_right (le_of_not_ge h)).symm

lemma projective_lens {n : ℕ} [NeZero n] {I : Type u_2} [Fintype I]
    (e : Sphere n) (f : I → Sphere n) (τ : I → ℝ) {l u t h Φ : ℝ}
    (hΦ : 0 ≤ Φ) (hΦsmall : Φ^2 < 2)
    (hangle : ∀ i,ProjectiveCaps.angle e.val (f i).val ≤ Φ)
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
    (hqu : Real.sqrt (t^2+h^2) ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
    (hτ : ∀ i,τ i ≤ t-Φ^2/2-Φ*h) :
    (1-(Fintype.card I:ℝ)*Real.exp (-(n:ℝ)*l*h^2/4))*(σ n).real (halfcap e.val t) ≤
      (σ n).real (⋂ i,cap (f i).val (τ i)) := by
  choose g hg hang using fun i => orient_axis e (f i)
  apply (ordinary_lens e g τ hΦ hΦsmall (fun i => by rw [hang i]; exact hangle i)
    hl hu hlt hh hqu hdim hτ).trans
  apply measureReal_mono (μ := σ n)
  intro w hw
  apply mem_iInter.mpr
  intro i
  rw [← hg i (τ i)]
  change τ i < |inner ℝ w.val (g i).val|
  exact lt_of_lt_of_le (show τ i < inner ℝ w.val (g i).val from mem_iInter.mp hw i) (le_abs_self _)

end LensDeployment

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LensQuantitative
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

universe u_1

namespace LensQuantitative
open Set MeasureTheory SphericalLaw CapGeometry CapCost LensDeployment
open scoped ENNReal NNReal

lemma cap_eq_mass {n : ℕ} (e f : Sphere n) (t : ℝ) :
    (σ n).real (cap e.val t) = (σ n).real (cap f.val t) := by
  apply congrArg ENNReal.toReal
  exact cap_equal_norm (by rw [mem_sphere_zero_iff_norm.mp e.property,
    mem_sphere_zero_iff_norm.mp f.property]) t

lemma intensity_lens {n : ℕ} [NeZero n] {I : Type u_1} [Fintype I] [Nonempty I]
    (e e₀ : Sphere n) (axes : I → Sphere n) (τ : I → ℝ)
    {l u t t₀ Φ : ℝ}
    (hl : 0 < l) (hu : u < 1) (_ht : 0 ≤ t) (ht1 : t < 1)
    (ht₀ : l ≤ t₀) (hΦ : 0 ≤ Φ) (hΦsmall : Φ^2 < 2)
    (hangle : ∀ i,ProjectiveCaps.angle e₀.val (axes i).val ≤ Φ)
    (hτ : ∀ i,τ i ≤ t₀)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
    (hsmall : let h := Real.sqrt (4*Real.log (2*(Fintype.card I:ℝ))/((n:ℝ)*l))
      Real.sqrt ((t₀+Φ^2/2+Φ*h)^2+h^2) ≤ u) :
    let h := Real.sqrt (4*Real.log (2*(Fintype.card I:ℝ))/((n:ℝ)*l))
    let δ := Φ^2/2+Φ*h
    (intensity e t).real (cap e₀.val t₀)/4 *
      Real.exp (-(n:ℝ)*(1/l+1/(1-u^2))*δ) ≤
        (intensity e t).real (⋂ i,cap (axes i).val (τ i)) := by
  let m : ℝ := Fintype.card I
  have hm : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := I))
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hlog : 0 ≤ Real.log (2*m) := Real.log_nonneg (by linarith)
  let h := Real.sqrt (4*Real.log (2*m)/((n:ℝ)*l))
  let δ := Φ^2/2+Φ*h
  have hsmall' : Real.sqrt ((t₀+δ)^2+h^2) ≤ u := by
    simpa only [δ,h,m,add_assoc] using hsmall
  have hh : 0 ≤ h := Real.sqrt_nonneg _
  have hh2 : h^2 = 4*Real.log (2*m)/((n:ℝ)*l) := Real.sq_sqrt (by positivity)
  have hexp : m*Real.exp (-(n:ℝ)*l*h^2/4) = 1/2 := by
    rw [hh2]
    have he : -(n:ℝ)*l*(4*Real.log (2*m)/((n:ℝ)*l))/4 = -Real.log (2*m) := by
      field_simp
    rw [he,Real.exp_neg,Real.exp_log (by linarith : 0 < 2*m)]
    field_simp
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hsu : t₀+δ ≤ u := by
    have hsq : t₀+δ ≤ Real.sqrt ((t₀+δ)^2+h^2) :=
      le_trans (le_abs_self _) (by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith))
    exact hsq.trans hsmall'
  have hmLens := projective_lens e₀ axes τ hΦ hΦsmall hangle hl hu
    (ht₀.trans (le_add_of_nonneg_right hδ)) hh hsmall' hdim
    (fun i => by dsimp [δ]; linarith [hτ i])
  change (1-m*Real.exp (-(n:ℝ)*l*h^2/4))*(σ n).real (halfcap e₀.val (t₀+δ)) ≤ _ at hmLens
  rw [hexp] at hmLens
  have ht₀pos := halfcap_real_pos e₀ ((le_add_of_nonneg_right hδ).trans_lt (hsu.trans_lt hu))
  have hA : 0 ≤ 1/l+1/(1-u^2) := by
    have hu0 := hl.trans_le (ht₀.trans (le_add_of_nonneg_right hδ) |>.trans hsu)
    have h1 : 0 < 1-u^2 := by nlinarith
    positivity
  have hratio := (halfcap_ratio e₀ hl hu ht₀ (le_add_of_nonneg_right hδ) hsu).1
  have hexple : Real.exp (-(n:ℝ)*(1/l+1/(1-u^2))*δ) ≤
      Real.exp (-((n:ℝ)-1)*(1/l+1/(1-u^2))*(t₀+δ-t₀)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hA hδ]
  have hratio' := (le_div_iff₀ ht₀pos).mp (hexple.trans hratio)
  have hmass := CapAffinity.cap_mass e₀ (hl.trans_le ht₀).le
  simp_rw [intensity_real]
  rw [hmass]
  change (2*(σ n).real (halfcap e₀.val t₀)/(σ n).real (cap e.val t)/4)*
    Real.exp (-(n:ℝ)*(1/l+1/(1-u^2))*δ) ≤ _
  calc
    _ = ((σ n).real (halfcap e₀.val t₀)*
      Real.exp (-(n:ℝ)*(1/l+1/(1-u^2))*δ)/2)/(σ n).real (cap e.val t) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [hratio']) (cap_real_pos e ht1).le

end LensQuantitative

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockGeometry
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

universe u_1

namespace BlockGeometry
open Finset
variable {I : Type u_1}

lemma radius_nonneg (d : I → I → ℝ) (S : Finset I) : 0 ≤ radius d S := by
  classical
  unfold radius
  split_ifs with h
  · apply le_inf'
    intro j _
    obtain ⟨i,hi⟩ := h
    exact (sq_nonneg _).trans (le_sup' (fun i => d j i ^ 2) hi)
  · rfl

lemma exists_center (d : I → I → ℝ) {S : Finset I} (hS : S.Nonempty) :
    ∃ j ∈ S, ∀ i ∈ S, d j i ^ 2 ≤ radius d S := by
  classical
  obtain ⟨j,hj,he⟩ := exists_mem_eq_inf' hS (fun j => S.sup' hS (fun i => d j i ^ 2))
  refine ⟨j,hj,fun i hi => ?_⟩
  rw [radius, dite_eq_left hS, he]
  exact le_sup' (fun i => d j i ^ 2) hi

end BlockGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadiusLens
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
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1

namespace RadiusLens
open Set MeasureTheory CapCost LensQuantitative SphericalLaw CapGeometry BlockGeometry
open scoped BigOperators

lemma lens_at_radius_oai {n : ℕ} [NeZero n] {I : Type u_1} [Fintype I] [DecidableEq I]
    (e : Sphere n) (axes : I → Sphere n) (τ : I → ℝ) (d : I → I → ℝ)
    {l u u₀ t : ℝ} (hl : 0 < l) (hu : u < 1) (_hu₀ : 0 ≤ u₀)
    (ht : 0 ≤ t) (ht1 : t < 1) (hτl : ∀ i,l ≤ τ i) (hτu : ∀ i,τ i ≤ u₀)
    (hmetric : ∀ i j,(n:ℝ)*(ProjectiveCaps.angle (axes i).val (axes j).val)^2 ≤ d i j^2)
    (S : Finset I) (hS : S.Nonempty) (a : I) (ha : a ∈ S)
    (hmin : ∀ i ∈ S,(intensity e t).real (cap (axes a).val (τ a)) ≤
      (intensity e t).real (cap (axes i).val (τ i)))
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
    (hrsmall : radius d S/(n:ℝ) < 2)
    (hsmall : (u₀+radius d S/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l))^2+
      4*Real.log (2*(S.card:ℝ))/((n:ℝ)*l) ≤ u^2) (hu0 : 0 ≤ u) :
    Real.exp (-(3+(1/l+1/(1-u^2))+2*(1/l+1/(1-u^2))/l)*
      (1+radius d S+Real.log S.card))*min ((intensity e t).real (cap (axes a).val (τ a))) (1/2) ≤
      (intensity e t).real (⋂ i ∈ S,cap (axes i).val (τ i)) := by
  let A := 1/l+1/(1-u^2)
  have hA : 0 ≤ A := by
    have hh : 0 < 1-u^2 := by nlinarith
    dsimp [A]; positivity
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  let r := radius d S
  have hr : 0 ≤ r := radius_nonneg d S
  let Φ := Real.sqrt (r/(n:ℝ))
  have hΦ : Φ^2 = r/(n:ℝ) := Real.sq_sqrt (div_nonneg hr hn.le)
  have hm : 1 ≤ (S.card:ℝ) := by exact_mod_cast Finset.one_le_card.mpr hS
  have hmlog : 0 ≤ Real.log S.card := Real.log_nonneg hm
  have hlog : 0 ≤ Real.log (2*(S.card:ℝ)) := Real.log_nonneg (by linarith)
  let h := Real.sqrt (4*Real.log (2*(S.card:ℝ))/((n:ℝ)*l))
  have hh2 : h^2 = 4*Real.log (2*(S.card:ℝ))/((n:ℝ)*l) := Real.sq_sqrt (by positivity)
  let δ := Φ^2/2+Φ*h
  have hδ : 0 ≤ δ := by dsimp [δ,Φ,h]; positivity
  have hδle : δ ≤ r/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l) := by
    calc
      δ ≤ Φ^2+h^2/2 := by dsimp [δ]; nlinarith only [sq_nonneg (Φ-h)]
      _ = _ := by rw [hΦ,hh2]; ring
  obtain ⟨j,hj,hcenter⟩ := exists_center d hS
  obtain ⟨k,hk,hkmax⟩ := Finset.exists_mem_eq_sup' hS τ
  have hτmax (i : S) : τ i ≤ τ k := by
    rw [← hkmax]
    exact Finset.le_sup' τ i.property
  have hang (i : S) : ProjectiveCaps.angle (axes j).val (axes i).val ≤ Φ := by
    apply (Real.le_sqrt (ProjectiveCaps.angle_nonneg _ _) (div_nonneg hr hn.le)).mpr
    exact (le_div_iff₀ hn).mpr (by
      simpa only [mul_comm] using (hmetric j i).trans (hcenter i i.property))
  have hsqrt : Real.sqrt ((τ k+δ)^2+h^2) ≤ u := by
    apply Real.sqrt_le_iff.mpr ⟨hu0,?_⟩
    have h1 : 0 ≤ τ k+δ := add_nonneg (hl.trans_le (hτl k)).le hδ
    have h2 : τ k+δ ≤ u₀+r/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l) := by linarith only [hτu k,hδle]
    have hsquare : (τ k+δ)^2 ≤ (u₀+r/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l))^2 := sq_le_sq₀ h1 (h1.trans h2) |>.mpr h2
    calc
      (τ k+δ)^2+h^2 ≤ (u₀+r/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l))^2+h^2 :=
        by simpa only [add_comm] using add_le_add_right hsquare (h^2)
      _ ≤ u^2 := by simpa only [hh2,r] using hsmall
  have : Nonempty S := ⟨⟨a,ha⟩⟩
  have hbound := intensity_lens e (axes j) (fun i : S => axes i) (fun i : S => τ i)
    hl hu ht ht1 (hτl k) (Real.sqrt_nonneg _) (by change Φ^2 < 2; rw [hΦ]; exact hrsmall)
    hang hτmax hdim (by simpa only [Fintype.card_coe,Φ,h,δ,add_assoc] using hsqrt)
  have heq : (intensity e t).real (cap (axes j).val (τ k)) =
      (intensity e t).real (cap (axes k).val (τ k)) := by
    simp only [intensity_real,cap_eq_mass (axes j) (axes k)]
  rw [heq] at hbound
  have hmass := hmin k hk
  have hminimum : 0 ≤ min ((intensity e t).real (cap (axes a).val (τ a))) (1/2) :=
    le_min measureReal_nonneg (by norm_num)
  have hb : min ((intensity e t).real (cap (axes a).val (τ a))) (1/2)/4 *
      Real.exp (-(n:ℝ)*A*δ) ≤ (intensity e t).real (⋂ i ∈ S,cap (axes i).val (τ i)) := by
    have hle := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right ((min_le_left ((intensity e t).real (cap (axes a).val (τ a))) (1/2)).trans hmass) (by norm_num : (0:ℝ) ≤ 4))
      (Real.exp_pos (-(n:ℝ)*A*δ)).le
    have hbound' : (intensity e t).real (cap (axes k).val (τ k))/4 *
        Real.exp (-(n:ℝ)*A*δ) ≤ (intensity e t).real (⋂ i ∈ S,cap (axes i).val (τ i)) := by
      simpa only [A,δ,h,Φ,Fintype.card_coe,Set.iInter_subtype] using hbound
    exact hle.trans hbound'
  have hexp : Real.exp (-(3+A+2*A/l)*(1+r+Real.log S.card)) ≤ Real.exp (-(n:ℝ)*A*δ)/4 := by
    have hnδ : (n:ℝ)*δ ≤ r+2*Real.log (2*(S.card:ℝ))/l := by
      have hh := mul_le_mul_of_nonneg_left hδle hn.le
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | (field_simp)
    have hnA := mul_le_mul_of_nonneg_left hnδ hA
    have hl2 : Real.log 2 ≤ 1 := by have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    have hl4 : Real.log 4 ≤ 2 := by
      rw [show (4:ℝ) = 2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
      linarith
    have hal : 0 ≤ 2*A/l := by positivity
    have hlmul := mul_le_mul_of_nonneg_left hl2 hal
    rw [Real.log_mul (by norm_num) (by linarith : (S.card:ℝ) ≠ 0)] at hnA
    have hbig : (n:ℝ)*A*δ+Real.log 4 ≤ (3+A+2*A/l)*(1+r+Real.log S.card) := by
      have h1 := mul_nonneg hA hmlog
      have h2 := mul_nonneg hal hr
      simp only [div_eq_mul_inv] at hnA hlmul h2 ⊢
      nlinarith only [hnA,hlmul,hl4,h1,h2,hr,hmlog,hA]
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 4),← Real.exp_sub]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ (Real.exp (-(n:ℝ)*A*δ)/4)*min ((intensity e t).real (cap (axes a).val (τ a))) (1/2) :=
      mul_le_mul_of_nonneg_right hexp hminimum
    _ = _ := by ring
    _ ≤ _ := hb

end RadiusLens

end OAI
end

theorem solution.{u_1} : type_of% @OAI.RadiusLens.lens_at_radius_oai.{u_1} := @OAI.RadiusLens.lens_at_radius_oai.{u_1}
