-- Prove2me | solution 1 for OAI.TargetGeometry.select
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:02:31.52509+00:00
-- url     : https://prove2.me/submissions/0717a46e-a13c-4f7a-900a-46ab3d80caa8

import Mathlib
import Definitions.Def_OAIQ16Cd002

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ConeStretch
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

namespace ConeStretch
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

lemma norm_sq {n : ℕ} (x : Space n) : ‖x‖^2 = ∑ i, (x i)^2 := by
  simpa [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x

lemma coordinate_sq_le {n : ℕ} (i : Fin n) (x : Space n) : (x i)^2 ≤ ‖x‖^2 := by
  rw [norm_sq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

end ConeStretch

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CylinderVolume
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
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CylinderVolume
open Set MeasureTheory Metric Finset ConeStretch
open scoped ENNReal
lemma scale_apply {n : ℕ} (i : Fin n) (a b : ℝ) (x : Space n) (j : Fin n) :
    scale i a b x j = (if j = i then a else b)*x j := by
  simp [scale,Matrix.toLpLin_apply,Matrix.mulVec_diagonal]
lemma scale_det {n : ℕ} (i : Fin n) (a b : ℝ) :
    LinearMap.det (scale i a b) = a*b^(n-1) := by
  classical
  rw [scale,Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin,
    Matrix.det_diagonal,← mul_prod_erase _ _ (mem_univ i)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏ _j ∈ (univ : Finset (Fin n)).erase i,b := by
      apply prod_congr rfl
      intro j hj
      rw [ite_eq_right (mem_erase.mp hj).1]
    _ = _ := by simp
lemma scale_norm_sq {n : ℕ} (i : Fin n) (a b : ℝ) (x : Space n) :
    ‖scale i a b x‖^2 = a^2*(x i)^2+b^2*(‖x‖^2-(x i)^2) := by
  classical
  rw [norm_sq,norm_sq]
  simp only [scale_apply]
  have he : ∀ j : Fin n,((if j = i then a else b)*x j)^2 =
      b^2*(x j)^2+if j = i then (a^2-b^2)*(x i)^2 else 0 := by
    intro j
    by_cases hj : j = i
    · subst j; simp; ring
    · simp [hj]; ring
  simp_rw [he]
  rw [sum_add_distrib,← mul_sum]
  simp
  ring
lemma scale_inverse {n : ℕ} (i : Fin n) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (x : Space n) : scale i a b (scale i a⁻¹ b⁻¹ x) = x := by
  ext j
  simp only [scale_apply]
  split_ifs <;> field_simp

lemma cylinder_closed {n : ℕ} (i : Fin n) (D r : ℝ) : IsClosed (cylinder i D r) := by
  apply IsClosed.inter
  · exact isClosed_le ((EuclideanSpace.proj i).continuous.abs) continuous_const
  · exact isClosed_le (continuous_norm.pow 2 |>.sub ((EuclideanSpace.proj i).continuous.pow 2)) continuous_const

lemma cylinder_subset_image {n : ℕ} (i : Fin n) {D r a b : ℝ}
    (hD : 0 < D) (_hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hscale : D^2/a^2+r^2/b^2 ≤ D^2) :
    cylinder i D r ⊆ scale i a b '' closedBall (0 : Space n) D := by
  intro x hx
  refine ⟨scale i a⁻¹ b⁻¹ x,?_,scale_inverse i ha.ne' hb.ne' x⟩
  rw [mem_closedBall_zero_iff]
  have h1 : (x i)^2 ≤ D^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD.le).mpr hx.1
  have hs := scale_norm_sq i a⁻¹ b⁻¹ x
  have hsq : ‖scale i a⁻¹ b⁻¹ x‖^2 ≤ D^2 := by
    calc
      _ ≤ a⁻¹^2*D^2+b⁻¹^2*r^2 := by
        rw [hs]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hx.2 (sq_nonneg _))
      _ = D^2/a^2+r^2/b^2 := by ring
      _ ≤ _ := hscale
  nlinarith [norm_nonneg (scale i a⁻¹ b⁻¹ x)]

lemma cylinder_volume {n : ℕ} [NeZero n] (i : Fin n) {D r : ℝ}
    (hD : 0 < D) (hr : 0 < r) :
    volume (cylinder i D r) ≤ ENNReal.ofReal (3*((n:ℝ)+1)*(r/D)^(n-1))*
      volume (closedBall (0 : Space n) D) := by
  let a : ℝ := n+1
  let b : ℝ := ((n:ℝ)+1)/(n:ℝ)*(r/D)
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hscale : D^2/a^2+r^2/b^2 ≤ D^2 := by
    dsimp [a,b]
    field_simp
    nlinarith [sq_nonneg D]
  have hsub := cylinder_subset_image i hD hr ha hb hscale
  have hm := measure_mono (μ := volume) hsub
  rw [Measure.addHaar_image_linearMap,scale_det,abs_of_pos (mul_pos ha (pow_pos hb _))] at hm
  apply hm.trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have hpow : (1+(n:ℝ)⁻¹)^(n-1) ≤ 3 :=
    (pow_le_pow_right₀ (show 1 ≤ 1+(n:ℝ)⁻¹ by linarith [inv_nonneg.mpr hn.le]) (Nat.sub_le n 1)).trans
      (Real.one_add_inv_pow_le_exp.trans Real.exp_one_lt_three.le)
  have he : ((n:ℝ)+1)/(n:ℝ) = 1+(n:ℝ)⁻¹ := by field_simp
  dsimp [a,b]
  rw [mul_pow,he]
  nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)+1 by positivity)
    (mul_nonneg (pow_nonneg (div_nonneg hr.le hD.le) (n-1)) (sub_nonneg.mpr hpow))]

lemma perp_sq {n : ℕ} (i : Fin n) (x : Space n) :
    ‖x‖^2-(x i)^2 = ∑ j ∈ (univ : Finset (Fin n)).erase i,(x j)^2 := by
  rw [norm_sq,← sum_erase_add _ _ (mem_univ i)]
  ring

lemma cylinder_translated_volume {n : ℕ} [NeZero n] (i : Fin n) (q : Space n)
    {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    volume {x : Space n | |x i| ≤ D ∧ ‖x-q‖^2-((x-q) i)^2 ≤ r^2} ≤
      ENNReal.ofReal (3*((n:ℝ)+1)*(r/D)^(n-1))*volume (closedBall (0 : Space n) D) := by
  let v := q-EuclideanSpace.single i (q i)
  have he : {x : Space n | |x i| ≤ D ∧ ‖x-q‖^2-((x-q) i)^2 ≤ r^2} =
      (fun x => x-v) ⁻¹' cylinder i D r := by
    ext x
    have hi : (x-v) i = x i := by simp [v]
    have hp : ‖x-v‖^2-((x-v) i)^2 = ‖x-q‖^2-((x-q) i)^2 := by
      rw [perp_sq,perp_sq]
      apply sum_congr rfl
      intro j hj
      simp [v,(mem_erase.mp hj).1]
    change (|x i| ≤ D ∧ ‖x-q‖^2-((x-q) i)^2 ≤ r^2) ↔
      (|(x-v) i| ≤ D ∧ ‖x-v‖^2-((x-v) i)^2 ≤ r^2)
    rw [hp,hi]
  rw [he,(measurePreserving_sub_right volume v).measure_preimage (cylinder_closed i D r).measurableSet.nullMeasurableSet]
  exact cylinder_volume i hD hr

lemma affine_cylinder_volume {n : ℕ} [NeZero n] (u : Space n) (hu : ‖u‖ = 1)
    (q : Space n) {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    volume {x : Space n | ‖x‖ ≤ D ∧ ‖x-q‖^2-(inner ℝ u (x-q))^2 ≤ r^2} ≤
      ENNReal.ofReal (3*((n:ℝ)+1)*(r/D)^(n-1))*volume (closedBall (0 : Space n) D) := by
  let i : Fin n := ⟨0,Nat.pos_of_ne_zero (NeZero.ne n)⟩
  let v : Space n := EuclideanSpace.single i 1
  have hv : ‖v‖ = 1 := by simp [v]
  let e := (Submodule.span ℝ ({u-v} : Set (Space n)))ᗮ.reflection
  have he : e u = v := Submodule.reflection_sub (hu.trans hv.symm)
  let C := {x : Space n | |x i| ≤ D ∧ ‖x-e q‖^2-((x-e q) i)^2 ≤ r^2}
  have hC : MeasurableSet C := by
    apply MeasurableSet.inter
    · exact measurableSet_le (EuclideanSpace.proj i).continuous.abs.measurable measurable_const
    · exact measurableSet_le ((continuous_id.sub continuous_const).norm.pow 2 |>.sub
        (((EuclideanSpace.proj i).continuous.comp (continuous_id.sub continuous_const)).pow 2)).measurable measurable_const
  have hsub : {x : Space n | ‖x‖ ≤ D ∧ ‖x-q‖^2-(inner ℝ u (x-q))^2 ≤ r^2} ⊆ e ⁻¹' C := by
    intro x hx
    have hc : |e x i| ≤ ‖e x‖ := by
      have hh := coordinate_sq_le i (e x)
      nlinarith [sq_abs (e x i),abs_nonneg (e x i),norm_nonneg (e x)]
    have hip : inner ℝ u (x-q) = (e x-e q) i := by
      rw [← e.inner_map_map,he,e.map_sub]
      simp [v,EuclideanSpace.inner_single_left]
    refine ⟨hc.trans (by rw [e.norm_map]; exact hx.1),?_⟩
    rw [← hip,← e.map_sub,e.norm_map]
    exact hx.2
  have hm := measure_mono (μ := volume) hsub
  rw [e.measurePreserving.measure_preimage hC.nullMeasurableSet] at hm
  exact hm.trans (cylinder_translated_volume i (e q) hD hr)

end CylinderVolume

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CylinderAngle
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
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CylinderAngle
open Set MeasureTheory Metric InnerProductGeometry CylinderVolume ConeStretch
open scoped ENNReal

lemma ordinary_perp_bound {n : ℕ} (u x : Space n) (hu : ‖u‖ = 1) (hx : x ≠ 0)
    {L ξ : ℝ} (hL : 0 ≤ L) (hξ : 0 ≤ ξ) (hxL : ‖x‖ ≤ L)
    (hang : InnerProductGeometry.angle u x ≤ ξ) :
    ‖x‖^2-(inner ℝ u x)^2 ≤ (L*ξ)^2 := by
  let A := InnerProductGeometry.angle u x
  have hA0 : 0 ≤ A := angle_nonneg _ _
  have hApi : A ≤ Real.pi := angle_le_pi _ _
  have hs0 : 0 ≤ Real.sin A := Real.sin_nonneg_of_nonneg_of_le_pi hA0 hApi
  have hsξ : Real.sin A ≤ ξ := (Real.sin_le hA0).trans hang
  have hc : Real.cos A*‖x‖ = inner ℝ u x := by
    dsimp [A]
    rw [cos_angle,hu,one_mul,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]
  have hid : ‖x‖^2-(inner ℝ u x)^2 = ‖x‖^2*(Real.sin A)^2 := by
    rw [← hc]
    have hh := congrArg (fun t : ℝ => ‖x‖^2*t) (Real.sin_sq_add_cos_sq A)
    nlinarith [hh]
  rw [hid,mul_pow]
  exact mul_le_mul ((sq_le_sq₀ (norm_nonneg _) hL).mpr hxL)
    ((sq_le_sq₀ hs0 hξ).mpr hsξ) (sq_nonneg _) (sq_nonneg _)

lemma projective_perp_bound {n : ℕ} (u x : Space n) (hu : ‖u‖ = 1) (hx : x ≠ 0)
    {L ξ : ℝ} (hL : 0 ≤ L) (hξ : 0 ≤ ξ) (hxL : ‖x‖ ≤ L)
    (hang : ProjectiveCaps.angle u x ≤ ξ) :
    ‖x‖^2-(inner ℝ u x)^2 ≤ (L*ξ)^2 := by
  rcases (min_le_iff.mp hang) with h | h
  · exact ordinary_perp_bound u x hu hx hL hξ hxL h
  · simpa only [norm_neg,inner_neg_right,neg_sq] using
      ordinary_perp_bound u (-x) hu (neg_ne_zero.mpr hx) hL hξ
        (by simpa only [norm_neg] using hxL) h

lemma angular_section_volume {n : ℕ} [NeZero n] (u : Space n) (hu : ‖u‖ = 1)
    (q : Space n) {D L ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (hξ : 0 < ξ) :
    volume {x : Space n | ‖x‖ ≤ D ∧ x-q ≠ 0 ∧ ‖x-q‖ ≤ L ∧
      ProjectiveCaps.angle u (x-q) ≤ ξ} ≤
    ENNReal.ofReal (3*((n:ℝ)+1)*(L*ξ/D)^(n-1))*
      volume (closedBall (0 : Space n) D) := by
  apply (measure_mono (μ := volume) (show _ ⊆
    {x : Space n | ‖x‖ ≤ D ∧ ‖x-q‖^2-(inner ℝ u (x-q))^2 ≤ (L*ξ)^2} from ?_)).trans
    (affine_cylinder_volume u hu q hD (mul_pos hL hξ))
  intro x hx
  exact ⟨hx.1,projective_perp_bound u (x-q) hu hx.2.1 hL.le hξ.le hx.2.2.1 hx.2.2.2⟩

lemma measurable_angle {n : ℕ} : Measurable (fun p : Space n × Space n => ProjectiveCaps.angle p.1 p.2) := by
  unfold ProjectiveCaps.angle InnerProductGeometry.angle
  fun_prop

end CylinderAngle

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CylinderProbability
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
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CylinderProbability
open Set MeasureTheory Metric CylinderAngle ConeStretch
open scoped ENNReal

lemma uniform_probability {n : ℕ} {G : Set (Space n)} (hG : volume G ≠ 0)
    (hGf : volume G ≠ ∞) : IsProbabilityMeasure (uniform G) := by
  constructor
  simp only [uniform,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hG hGf

lemma uniform_le {n : ℕ} {G S : Set (Space n)} (hG : MeasurableSet G) :
    uniform G S ≤ (volume G)⁻¹*volume (S ∩ G) := by
  rw [uniform,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply' hG]

lemma uniform_section {n : ℕ} [NeZero n] {G : Set (Space n)} (hG : MeasurableSet G)
    {D L ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (hξ : 0 < ξ)
    (hGsub : G ⊆ closedBall (0 : Space n) D)
    (hGlarge : volume (closedBall (0 : Space n) D) ≤ 4*volume G)
    (u q : Space n) (hu : ‖u‖ = 1) :
    uniform G {x | x-q ≠ 0 ∧ ‖x-q‖ ≤ L ∧ ProjectiveCaps.angle u (x-q) ≤ ξ} ≤
      ENNReal.ofReal (12*((n:ℝ)+1)*(L*ξ/D)^(n-1)) := by
  have hGf : volume G ≠ ∞ := ne_top_of_le_ne_top (isCompact_closedBall (0 : Space n) D).measure_ne_top
    (measure_mono hGsub)
  have hG0 : volume G ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hGlarge
    exact (ne_of_gt (measure_closedBall_pos volume (0 : Space n) hD)) (le_zero_iff.mp hGlarge)
  let c : ℝ := 3*((n:ℝ)+1)*(L*ξ/D)^(n-1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsub : {x : Space n | x-q ≠ 0 ∧ ‖x-q‖ ≤ L ∧ ProjectiveCaps.angle u (x-q) ≤ ξ} ∩ G ⊆
      {x : Space n | ‖x‖ ≤ D ∧ x-q ≠ 0 ∧ ‖x-q‖ ≤ L ∧ ProjectiveCaps.angle u (x-q) ≤ ξ} := by
    intro x hx
    exact ⟨mem_closedBall_zero_iff.mp (hGsub hx.2),hx.1⟩
  calc
    _ ≤ (volume G)⁻¹*(ENNReal.ofReal c*volume (closedBall (0 : Space n) D)) :=
      (uniform_le hG).trans (mul_le_mul_right ((measure_mono hsub).trans
        (angular_section_volume u hu q hD hL hξ)) _)
    _ ≤ (volume G)⁻¹*(ENNReal.ofReal c*(4*volume G)) := by gcongr
    _ = 4*ENNReal.ofReal c := by
      rw [show (volume G)⁻¹*(ENNReal.ofReal c*(4*volume G)) =
        (4*ENNReal.ofReal c)*((volume G)⁻¹*volume G) by ring,
        ENNReal.inv_mul_cancel hG0 hGf,mul_one]
    _ = _ := by
      rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      congr 1
      dsimp [c]
      ring

lemma pairEvent_measurable {n : ℕ} (p q : Space n) (L ξ : ℝ) :
    MeasurableSet (pairEvent p q L ξ) := by
  apply MeasurableSet.inter
  · exact (isClosed_eq (continuous_fst.sub continuous_const) continuous_const).measurableSet.compl
  · apply MeasurableSet.inter
    · exact measurableSet_le (continuous_fst.sub continuous_const).norm.measurable measurable_const
    · apply MeasurableSet.inter
      · exact (isClosed_eq (continuous_snd.sub continuous_const) continuous_const).measurableSet.compl
      · exact (measurableSet_le (continuous_snd.sub continuous_const).norm.measurable measurable_const).inter
          (measurableSet_le (measurable_angle.comp ((measurable_fst.sub measurable_const).prodMk
            (measurable_snd.sub measurable_const))) measurable_const)

lemma pair_probability {n : ℕ} [NeZero n] {G : Set (Space n)} (hG : MeasurableSet G)
    {D L ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (hξ : 0 < ξ)
    (hGsub : G ⊆ closedBall (0 : Space n) D)
    (hGlarge : volume (closedBall (0 : Space n) D) ≤ 4*volume G)
    (p q : Space n) :
    ((uniform G).prod (uniform G)) (pairEvent p q L ξ) ≤
      ENNReal.ofReal (12*((n:ℝ)+1)*(L*ξ/D)^(n-1)) := by
  have hGf : volume G ≠ ∞ := ne_top_of_le_ne_top (isCompact_closedBall (0 : Space n) D).measure_ne_top
    (measure_mono hGsub)
  have hG0 : volume G ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hGlarge
    exact (ne_of_gt (measure_closedBall_pos volume (0 : Space n) hD)) (le_zero_iff.mp hGlarge)
  have := uniform_probability hG0 hGf
  rw [Measure.prod_apply (pairEvent_measurable p q L ξ)]
  calc
    _ ≤ ∫⁻ _y : Space n,ENNReal.ofReal (12*((n:ℝ)+1)*(L*ξ/D)^(n-1)) ∂uniform G := by
      apply lintegral_mono
      intro y
      dsimp only
      by_cases hy : y-p = 0
      · have he : Prod.mk y ⁻¹' pairEvent p q L ξ = ∅ := by ext x; simp [pairEvent,hy]
        rw [he,measure_empty]; exact bot_le
      · let u := ‖y-p‖⁻¹ • (y-p)
        have hyn : 0 < ‖y-p‖ := norm_pos_iff.mpr hy
        have hu : ‖u‖ = 1 := by simp [u,norm_smul,hyn.ne']
        have he (x : Space n) : ProjectiveCaps.angle u x = ProjectiveCaps.angle (y-p) x := by
          simp only [u,ProjectiveCaps.angle,InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr hyn)]
        have hsub : Prod.mk y ⁻¹' pairEvent p q L ξ ⊆
            {x | x-q ≠ 0 ∧ ‖x-q‖ ≤ L ∧ ProjectiveCaps.angle u (x-q) ≤ ξ} := by
          intro x hx
          exact ⟨hx.2.2.1,hx.2.2.2.1,by rw [he]; exact hx.2.2.2.2⟩
        exact (measure_mono hsub).trans (uniform_section hG hD hL hξ hGsub hGlarge u q hu)
    _ = _ := by simp

end CylinderProbability

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_TargetSampling
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
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace TargetSampling
open Set MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
variable {Ω : Type u_1} [MeasurableSpace Ω]

lemma pair_preserving (P : Measure Ω) [IsProbabilityMeasure P] {M : ℕ}
    {i j : Fin M} (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin M → Ω => (x i,x j)) (Measure.pi (fun _ => P)) (P.prod P) := by
  have hind : iIndepFun (fun i (x : Fin M → Ω) => x i) (Measure.pi (fun _ => P)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),?_⟩
  have h := IndepFun.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable (hind.indepFun hij)
  rw [(measurePreserving_eval (fun _ : Fin M => P) i).map_eq,
    (measurePreserving_eval (fun _ : Fin M => P) j).map_eq] at h
  exact h

omit [MeasurableSpace Ω] in
lemma score_nonneg {M : ℕ} (A : Set (Ω × Ω)) (x : Fin M → Ω) : 0 ≤ score A x := by
  apply sum_nonneg
  intro p _
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma score_integrable (P : Measure Ω) [IsProbabilityMeasure P] {M : ℕ}
    {A : Set (Ω × Ω)} (hA : MeasurableSet A) :
    Integrable (score (M := M) A) (Measure.pi (fun _ => P)) := by
  apply integrable_finsetSum
  intro p _
  have he : (fun x : Fin M → Ω => A.indicator (fun _ => (1:ℝ)) (x p.1,x p.2)) =
      ((fun x : Fin M → Ω => (x p.1,x p.2)) ⁻¹' A).indicator (fun _ => 1) := by
    ext x; exact (indicator_comp_right _).symm
  rw [he]
  exact (integrable_const _).indicator (hA.preimage ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)))

lemma score_integral (P : Measure Ω) [IsProbabilityMeasure P] {M : ℕ}
    {A : Set (Ω × Ω)} (hA : MeasurableSet A) :
    (∫ x,score (M := M) A x ∂Measure.pi (fun _ => P)) =
      ((pairs M).card:ℝ)*(P.prod P).real A := by
  change (∫ x, ∑ p ∈ pairs M, A.indicator (fun _ => (1:ℝ)) (x p.1,x p.2) ∂Measure.pi (fun _ => P)) = _
  rw [integral_finsetSum]
  · have he (p : Fin M × Fin M) (hp : p ∈ pairs M) :
        (∫ x : Fin M → Ω,A.indicator (fun _ => (1:ℝ)) (x p.1,x p.2) ∂Measure.pi (fun _ => P)) =
          (P.prod P).real A := by
      have hm := pair_preserving P ((mem_filter.mp hp).2)
      have hc := integral_map (μ := Measure.pi (fun _ : Fin M => P)) hm.measurable.aemeasurable
        ((stronglyMeasurable_const (b := (1:ℝ))).indicator hA).aestronglyMeasurable
      rw [hm.map_eq] at hc
      rw [← hc,integral_indicator hA,integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one]
    rw [Finset.sum_congr rfl he]
    simp
  · intro p hp
    have hm := pair_preserving P ((mem_filter.mp hp).2)
    exact hm.integrable_comp ((stronglyMeasurable_const.indicator hA).aestronglyMeasurable) |>.mpr
      ((integrable_const _).indicator hA)

omit [MeasurableSpace Ω] in
lemma score_ge_one {M : ℕ} {A : Set (Ω × Ω)} {x : Fin M → Ω} {i j : Fin M}
    (hij : i ≠ j) (hA : (x i,x j) ∈ A) : 1 ≤ score A x := by
  classical
  have hp : (i,j) ∈ pairs M := by simp [pairs,hij]
  have h := single_le_sum (f := fun p : Fin M × Fin M => A.indicator (fun _ => (1:ℝ)) (x p.1,x p.2)) (fun p (_hp : p ∈ pairs M) =>
    Set.indicator_nonneg (fun _ _ => (zero_le_one : (0:ℝ) ≤ 1)) (x p.1,x p.2)) hp
  simpa [score,indicator_of_mem hA] using h

lemma ae_distinct (P : Measure Ω) [IsProbabilityMeasure P] [NullSingletonClass P]
    {M : ℕ} (hd : MeasurableSet (diagonal Ω)) :
    ∀ᵐ x : Fin M → Ω ∂Measure.pi (fun _ => P), Function.Injective x := by
  have hzero : (P.prod P) (diagonal Ω) = 0 := by
    rw [Measure.prod_apply hd]
    have he (x : Ω) : Prod.mk x ⁻¹' diagonal Ω = {x} := by ext y; simp [diagonal,eq_comm]
    simp_rw [he,measure_singleton]
    simp
  have hp (i j : Fin M) : ∀ᵐ x : Fin M → Ω ∂Measure.pi (fun _ => P), i ≠ j → x i ≠ x j := by
    by_cases hij : i = j
    · simp [hij]
    · have hm := (pair_preserving P hij).measure_preimage hd.nullMeasurableSet
      rw [hzero] at hm
      have hae : ∀ᵐ x : Fin M → Ω ∂Measure.pi (fun _ => P), (x i,x j) ∉ diagonal Ω := by
        apply ae_iff.mpr
        simpa only [not_not,Set.preimage,Set.mem_ofPred_eq] using hm
      filter_upwards [hae] with x hx
      simpa [diagonal] using (fun _ : i ≠ j => hx)
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hp i)] with x hx
  exact fun i j he => by_contra fun hij => hx i j hij he

lemma ae_in_set (P : Measure Ω) [IsProbabilityMeasure P] {M : ℕ} {G : Set Ω}
    (hG : MeasurableSet G) (hlarge : P Gᶜ = 0) :
    ∀ᵐ x : Fin M → Ω ∂Measure.pi (fun _ => P), ∀ i,x i ∈ G := by
  apply ae_all_iff.mpr
  intro i
  apply ae_iff.mpr
  have h := (measurePreserving_eval (fun _ : Fin M => P) i).measure_preimage hG.compl.nullMeasurableSet
  change (Measure.pi fun _ : Fin M => P) ((Function.eval i) ⁻¹' Gᶜ) = 0
  simpa only [hlarge] using h

theorem select (P : Measure Ω) [IsProbabilityMeasure P] [NullSingletonClass P]
    {M : ℕ} (hM : 2 ≤ M) (hd : MeasurableSet (diagonal Ω))
    {G : Set Ω} (hG : MeasurableSet G) (hGfull : P Gᶜ = 0)
    {A B : Set (Ω × Ω)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {p f : ℝ} (hf : 0 < f)
    (hsmall : ((pairs M).card:ℝ)*p < 1/2)
    (hPA : (P.prod P).real A ≤ p) (hPB : (P.prod P).real B ≤ f) :
    ∃ x : Fin M → Ω, (∀ i,x i ∈ G) ∧ Function.Injective x ∧
      (∀ i j,i ≠ j → (x i,x j) ∉ A) ∧
      score B x ≤ 10*((pairs M).card:ℝ)*f := by
  have hK : 0 < ((pairs M).card:ℝ) := by
    have hne : (pairs M).Nonempty := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by simp [pairs,Fin.ext_iff]⟩
    exact_mod_cast card_pos.mpr hne
  let q : ℝ := 10*((pairs M).card:ℝ)*f
  have hq : 0 < q := by dsimp [q]; positivity
  let W := fun x : Fin M → Ω => score A x+score B x/q
  have hWi : Integrable W (Measure.pi (fun _ => P)) :=
    (score_integrable P hA).add ((score_integrable P hB).div_const q)
  have hW : (∫ x,W x ∂Measure.pi (fun _ => P)) < 1 := by
    rw [integral_add (score_integrable P hA) ((score_integrable P hB).div_const q),
      integral_div,score_integral P hA,score_integral P hB]
    have h1 := mul_le_mul_of_nonneg_left hPA hK.le
    have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPB hK.le) hq.le
    have he : ((pairs M).card:ℝ)*f/q = 1/10 := by dsimp [q]; field_simp
    rw [he] at h2
    linarith
  let N := {x : Fin M → Ω | ¬((∀ i,x i ∈ G) ∧ Function.Injective x)}
  have hN : Measure.pi (fun _ : Fin M => P) N = 0 := by
    apply ae_iff.mp
    filter_upwards [ae_in_set P hG hGfull,ae_distinct P hd] with x hx hy
    exact ⟨hx,hy⟩
  obtain ⟨x,hx,hWx⟩ := exists_notMem_null_le_integral hWi hN
  have hWx' : W x < 1 := hWx.trans_lt hW
  have hx' : (∀ i,x i ∈ G) ∧ Function.Injective x := not_not.mp hx
  refine ⟨x,hx'.1,hx'.2,?_,?_⟩
  · intro i j hij ha
    have h1 := score_ge_one hij ha
    have h2 := div_nonneg (score_nonneg B x) hq.le
    dsimp [W] at hWx'
    linarith
  · have h1 := score_nonneg A x
    have h2 : score B x/q < 1 := by dsimp [W] at hWx'; linarith
    have h3 := (div_lt_one hq).mp h2
    exact h3.le

end TargetSampling

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_TargetGeometry
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
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace TargetGeometry
open Set MeasureTheory Metric CylinderProbability ConeStretch
open scoped ENNReal

lemma measurable_bad {n : ℕ} {I : Type u_2} [Fintype I] (p : I → Space n) (L ξ : ℝ) :
    MeasurableSet (bad p L ξ) := MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun j => pairEvent_measurable (p i) (p j) L ξ

lemma bad_probability {n : ℕ} [NeZero n] {I : Type u_3} [Fintype I]
    (p : I → Space n) {G : Set (Space n)} (hG : MeasurableSet G)
    {D L ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (hξ : 0 < ξ)
    (hGsub : G ⊆ closedBall (0 : Space n) D)
    (hGlarge : volume (closedBall (0 : Space n) D) ≤ 4*volume G) :
    (uniform G |>.prod (uniform G)) (bad p L ξ) ≤
      ENNReal.ofReal (12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*ξ/D)^(n-1)) := by
  calc
    _ ≤ ∑ i,∑ j,(uniform G |>.prod (uniform G)) (pairEvent (p i) (p j) L ξ) :=
      (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun i => measure_iUnion_le _) |>.trans_eq (by simp [tsum_fintype])
    _ ≤ ∑ _i : I,∑ _j : I,ENNReal.ofReal (12*((n:ℝ)+1)*(L*ξ/D)^(n-1)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pair_probability hG hD hL hξ hGsub hGlarge (p i) (p j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];
                rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _),
                  ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]; congr 1; ring

theorem select_oai {n : ℕ} [NeZero n] {I : Type u_4} [Fintype I]
    (p : I → Space n) {G : Set (Space n)} (hG : MeasurableSet G)
    {D L t ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (ht : 0 < t) (hξ : 0 < ξ)
    (hGsub : G ⊆ closedBall (0 : Space n) D)
    (hGlarge : volume (closedBall (0 : Space n) D) ≤ 4*volume G)
    {M : ℕ} (hM : 2 ≤ M) (hI : Nonempty I)
    (hsmall : ((TargetSampling.pairs M).card:ℝ)*
      (12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*t/D)^(n-1)) < 1/2) :
    ∃ x : Fin M → Space n, (∀ i,x i ∈ G) ∧ Function.Injective x ∧
      (∀ i j,i ≠ j → (x i,x j) ∉ bad p L t) ∧
      TargetSampling.score (bad p L ξ) x ≤
        10*((TargetSampling.pairs M).card:ℝ)*
          (12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*ξ/D)^(n-1)) := by
  have hGf : volume G ≠ ∞ := ne_top_of_le_ne_top (isCompact_closedBall (0 : Space n) D).measure_ne_top
    (measure_mono hGsub)
  have hG0 : volume G ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hGlarge
    exact (ne_of_gt (measure_closedBall_pos volume (0 : Space n) hD)) (le_antisymm hGlarge bot_le)
  have : IsProbabilityMeasure (uniform G) := uniform_probability hG0 hGf
  have : NullSingletonClass (uniform G) := ⟨fun x => by simp [uniform]⟩
  have : Nonempty I := hI
  have hf : 0 < 12*((n:ℝ)+1)*(Fintype.card I:ℝ)^2*(L*ξ/D)^(n-1) := by
    have hcard : 0 < (Fintype.card I:ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  apply TargetSampling.select (uniform G) hM measurableSet_diagonal hG
    (by simp [uniform,Measure.restrict_apply' hG,Set.compl_inter_self])
    (measurable_bad p L t) (measurable_bad p L ξ) hf hsmall
  · exact ENNReal.toReal_le_of_le_ofReal (by positivity) (bad_probability p hG hD hL ht hGsub hGlarge)
  · exact ENNReal.toReal_le_of_le_ofReal hf.le (bad_probability p hG hD hL hξ hGsub hGlarge)

end TargetGeometry

end OAI
end

theorem solution.{u_4} : type_of% @OAI.TargetGeometry.select_oai.{u_4} := @OAI.TargetGeometry.select_oai.{u_4}
