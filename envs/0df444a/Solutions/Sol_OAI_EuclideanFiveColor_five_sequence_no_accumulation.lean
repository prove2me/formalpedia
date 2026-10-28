-- Prove2me | solution 1 for OAI.EuclideanFiveColor.five_sequence_no_accumulation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:00:58.857143+00:00
-- url     : https://prove2.me/submissions/6d825d3c-12f6-4a06-acf2-0b2a2c3ff0e7

import Mathlib
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_EuclideanFiveColor_fiveState_diag
import Theorems.Thm_OAI_EuclideanFiveColor_five_local_palette

section
-- module Solutions.OAIQ5_T4.Compat
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Expansion
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma line_volume_preimage_bound {F : ℝ → ℝ} {s : Set (ℝ)} {K : ℝ≥0}
    (hF : AntilipschitzWith K (s.domRestrict F)) (A : Set (ℝ)) :
    volume (F ⁻¹' A ∩ s) ≤ (K : ENNReal) * volume A := by
  have he : Subtype.val '' ((s.domRestrict F) ⁻¹' A) = F ⁻¹' A ∩ s := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩; exact ⟨hq,q.2⟩
    · rintro ⟨hp,hs⟩; exact ⟨⟨p,hs⟩,hp,rfl⟩
  have hi := (isometry_subtype_coe : Isometry (Subtype.val : s → ℝ)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ)≤1)) ((s.domRestrict F) ⁻¹' A)
  have ha := hF.hausdorffMeasure_preimage_le (by norm_num : (0 : ℝ)≤1) A
  rw [he,hausdorffMeasure_real] at hi
  rw [← hi,hausdorffMeasure_real,ENNReal.rpow_one] at ha
  exact ha
lemma line_map_restrict_volume_le {F : ℝ → ℝ} (hm : Measurable F)
    {s B : Set (ℝ)} (_hB : MeasurableSet B) {K : ℝ≥0}
    (hF : AntilipschitzWith K (s.domRestrict F)) (himage : MapsTo F s B) :
    (volume.restrict s).map F ≤ (K : ENNReal) • volume.restrict B := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hm hA,Measure.restrict_apply (hm hA),Measure.smul_apply,
    Measure.restrict_apply hA,smul_eq_mul]
  have he : F ⁻¹' A ∩ s = F ⁻¹' (A ∩ B) ∩ s := by
    ext x
    exact ⟨fun hx => ⟨⟨hx.1,himage hx.2⟩,hx.2⟩,fun hx => ⟨hx.1.1,hx.2⟩⟩
  rw [he]
  exact line_volume_preimage_bound hF (A ∩ B)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y] [NormalSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} {ν : Measure Y}
omit [TopologicalSpace Y] [NormalSpace Y] [BorelSpace Y] in
lemma integrable_comp_of_map_le {T : X → Y} (hT : Measurable T) {C : ℝ≥0}
    (hmap : μ.map T ≤ (C : ENNReal) • ν) {f : Y → ℝ} (hf : Integrable f ν) :
    Integrable (fun x => f (T x)) μ := by
  have hh := (hf.smul_measure (by simp : (C : ENNReal) ≠ ⊤)).mono_measure hmap
  exact (integrable_map_measure hh.aestronglyMeasurable hT.aemeasurable).mp hh
omit [TopologicalSpace Y] [NormalSpace Y] [BorelSpace Y] in
lemma integral_norm_comp_le {T : X → Y} (hT : Measurable T) {C : ℝ≥0}
    (hmap : μ.map T ≤ (C : ENNReal) • ν) {f : Y → ℝ} (hf : Integrable f ν) :
    (∫ x, ‖f (T x)‖ ∂μ) ≤ (C : ℝ)*(∫ y, ‖f y‖ ∂ν) := by
  have hh := (hf.smul_measure (by simp : (C : ENNReal) ≠ ⊤)).mono_measure hmap
  rw [← integral_map hT.aemeasurable hh.norm.aestronglyMeasurable]
  calc
    _ ≤ ∫ y, ‖f y‖ ∂((C : ENNReal) • ν) :=
      integral_mono_measure hmap (Eventually.of_forall fun y => norm_nonneg _) (hf.norm.smul_measure (by simp))
    _ = _ := by rw [integral_smul_measure]; simp
/-- L¹ continuity under measurable perturbations with a common bounded pushforward density. -/
lemma tendsto_integral_norm_comp_sub [IsFiniteMeasure μ] [ν.WeaklyRegular]
    {T : ℕ → X → Y} {S : X → Y} {C : ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (hS : Measurable S)
    (hmT : ∀ n, μ.map (T n) ≤ (C : ENNReal) • ν) (hmS : μ.map S ≤ (C : ENNReal) • ν)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => T n x) atTop (𝓝 (S x)))
    {f : Y → ℝ} (hf : Integrable f ν) :
    Tendsto (fun n => ∫ x, ‖f (T n x)-f (S x)‖ ∂μ) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε/(3*((C : ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨g,hg,hgi⟩ := hf.exists_boundedContinuous_integral_sub_le hδ
  have hgT (n : ℕ) : Integrable (fun x => g (T n x)) μ :=
    integrable_comp_of_map_le (hT n) (hmT n) hgi
  have hgS : Integrable (fun x => g (S x)) μ := integrable_comp_of_map_le hS hmS hgi
  have hfT (n : ℕ) := integrable_comp_of_map_le (hT n) (hmT n) hf
  have hfS := integrable_comp_of_map_le hS hmS hf
  have hmid : Tendsto (fun n => ∫ x, ‖g (T n x)-g (S x)‖ ∂μ) atTop (𝓝 0) := by
    have hp := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => 2*‖g‖)
      (fun n => ((hgT n).sub hgS).norm.aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (by linarith [g.norm_coe_le_norm (T n x),g.norm_coe_le_norm (S x)]))
      (ht.mono fun x hx => by
        have hh := (g.continuous.tendsto (S x)).comp hx
        simpa using (hh.sub tendsto_const_nhds).norm)
    simpa using hp
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hmid (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h1 : (∫ x, ‖f (T n x)-g (T n x)‖ ∂μ) ≤ (C : ℝ)*δ :=
    (integral_norm_comp_le (hT n) (hmT n) (hf.sub hgi)).trans (mul_le_mul_of_nonneg_left hg C.2)
  have h2 : (∫ x, ‖f (S x)-g (S x)‖ ∂μ) ≤ (C : ℝ)*δ :=
    (integral_norm_comp_le hS hmS (hf.sub hgi)).trans (mul_le_mul_of_nonneg_left hg C.2)
  have htri : (∫ x, ‖f (T n x)-f (S x)‖ ∂μ) ≤
      (∫ x, ‖f (T n x)-g (T n x)‖ ∂μ) + (∫ x, ‖g (T n x)-g (S x)‖ ∂μ) +
      (∫ x, ‖f (S x)-g (S x)‖ ∂μ) := by
    have ha : Integrable (fun x => ‖f (T n x)-g (T n x)‖) μ := ((hfT n).sub (hgT n)).norm
    have hb : Integrable (fun x => ‖g (T n x)-g (S x)‖) μ := ((hgT n).sub hgS).norm
    have hc : Integrable (fun x => ‖f (S x)-g (S x)‖) μ := (hfS.sub hgS).norm
    have hi := integral_mono ((hfT n).sub hfS).norm ((ha.add hb).add hc) (fun x => by
      simpa only [Pi.add_apply,Pi.sub_apply,← dist_eq_norm,dist_comm (g (S x))] using
        dist_triangle4 (f (T n x)) (g (T n x)) (g (S x)) (f (S x)))
    apply hi.trans_eq
    exact (integral_add (ha.add hb) hc).trans (congrArg (fun t => t + ∫ x, ‖f (S x)-g (S x)‖ ∂μ) (integral_add ha hb))
  have hδv : (C : ℝ)*δ ≤ ε/3 := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<3*((C : ℝ)+1))).mpr
    nlinarith [C.2]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
  have hm := hN n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at hm
  linarith
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
lemma tendsto_integral_norm_comp_sub_eventual {X Y : Type*} [MeasurableSpace X]
    [TopologicalSpace Y] [NormalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [ν.WeaklyRegular]
    {T : ℕ → X → Y} {S : X → Y} {C : ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (hS : Measurable S)
    (hmT : ∀ᶠ n in atTop, μ.map (T n) ≤ (C : ENNReal) • ν) (hmS : μ.map S ≤ (C : ENNReal) • ν)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => T n x) atTop (𝓝 (S x)))
    {f : Y → ℝ} (hf : Integrable f ν) :
    Tendsto (fun n => ∫ x, ‖f (T n x)-f (S x)‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hmT
  apply (tendsto_add_atTop_iff_nat N).mp
  apply tendsto_integral_norm_comp_sub (T := fun n => T (n+N)) (C := C)
    (fun n => hT (n+N)) hS (fun n => hN _ (Nat.le_add_left N n)) hmS
  · exact ht.mono fun x hx => (tendsto_add_atTop_iff_nat N).mpr hx
  · exact hf
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
lemma line_antilipschitz_qmp {S : ℝ → ℝ} (hS : Measurable S) {I : Set ℝ} {K : ℝ≥0}
    (hA : AntilipschitzWith K (I.domRestrict S)) :
    Measure.QuasiMeasurePreserving S (volume.restrict I) volume := by
  refine ⟨hS,?_⟩
  have hle := line_map_restrict_volume_le hS MeasurableSet.univ hA (mapsTo_univ S I)
  rw [Measure.restrict_univ] at hle
  exact Measure.absolutelyContinuous_of_le_smul hle
lemma line_indicator_pullback_L1 {T : ℕ → ℝ → ℝ} {S : ℝ → ℝ} {I B D : Set ℝ} {K : ℝ≥0}
    [IsFiniteMeasure (volume.restrict I)] [IsFiniteMeasure (volume.restrict B)]
    (hT : ∀ n, Measurable (T n)) (hS : Measurable S)
    (hB : IsCompact B) (hD : MeasurableSet D)
    (hAT : ∀ᶠ n in atTop, AntilipschitzWith K (I.domRestrict (T n)))
    (hAS : AntilipschitzWith K (I.domRestrict S))
    (hBT : ∀ᶠ n in atTop, MapsTo (T n) I B) (hBS : MapsTo S I B)
    (ht : ∀ᵐ x ∂volume.restrict I, Tendsto (fun n => T n x) atTop (𝓝 (S x))) :
    Tendsto (fun n => ∫ x in I, ‖D.indicator (fun _ => (1 : ℝ)) (T n x)-
      D.indicator (fun _ => (1 : ℝ)) (S x)‖) atTop (𝓝 0) := by
  have : (volume.restrict B).WeaklyRegular := Measure.WeaklyRegular.restrict_of_measure_ne_top hB.measure_lt_top.ne
  apply tendsto_integral_norm_comp_sub_eventual (ν := volume.restrict B) (C := K) hT hS
  · filter_upwards [hAT,hBT] with n ha hb
    exact line_map_restrict_volume_le (hT n) hB.measurableSet ha hb
  · exact line_map_restrict_volume_le hS hB.measurableSet hAS hBS
  · exact ht
  · exact (integrable_const (1 : ℝ)).indicator hD
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CircleMaps
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma circleSum_continuous (r : ℝ) : Continuous (circleSum r) :=
  continuous_iff_continuousAt.mpr fun p => (circleSum_strict r p).continuousAt
lemma circleSum_local_antilipschitz {r : ℝ} {p : RealPlane} (h : r*Real.sin (p.2-p.1) ≠ 0) :
    ∃ s : Set RealPlane, IsOpen s ∧ p ∈ s ∧ ∃ K : ℝ≥0, AntilipschitzWith K (s.domRestrict (circleSum r)) := by
  let L := circleSumDerivEquiv h
  have hd : HasStrictFDerivAt (circleSum r) (L : RealPlane →L[ℝ] RealPlane) p := circleSum_strict r p
  obtain ⟨s,hp,hs,ha⟩ := hd.approximates_deriv_on_open_nhds
  refine ⟨s,hs,hp,_,ha.antilipschitz ?_⟩
  right
  have hpos := L.subsingleton_or_nnnorm_symm_pos.resolve_left (not_subsingleton RealPlane)
  exact half_lt_self (inv_pos.mpr hpos)
lemma realDirection_lipschitz : LipschitzWith 1 (fun t : ℝ => (Real.cos t,Real.sin t)) := by
  simpa using Real.lipschitzWith_cos.prodMk Real.lipschitzWith_sin
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {t u : ℝ} (h : Real.sin (u-t) ≠ 0)
lemma circleInverse_measurable : Measurable (circleInverse h) := by
  classical
  exact (circleInverseHomeo h).continuousOn_invFun.measurable_piecewise continuous_const.continuousOn
    (circleInverseHomeo h).open_target.measurableSet
lemma circleInverse_eq {q : RealPlane} (hq : q ∈ (circleInverseHomeo h).target) :
    circleInverse h q=(circleInverseHomeo h).symm q := by simp [circleInverse,hq]
lemma circleInverse_at : circleInverse h (circleSum 1 (t,u))=(t,u) := by
  have hd : HasStrictFDerivAt (circleSum 1)
      (circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h) : RealPlane →L[ℝ] RealPlane)
      (t,u) := circleSum_strict 1 (t,u)
  rw [circleInverse_eq h hd.image_mem_toOpenPartialHomeomorph_target]
  exact hd.localInverse_apply_image
lemma circleInverse_continuousAt {q : RealPlane} (hq : q ∈ (circleInverseHomeo h).target) :
    ContinuousAt (circleInverse h) q := by
  apply ((circleInverseHomeo h).continuousAt_symm hq).congr_of_eventuallyEq
  filter_upwards [(circleInverseHomeo h).open_target.mem_nhds hq] with y hy
  exact circleInverse_eq h hy
lemma circleInverse_strict : HasStrictFDerivAt (circleInverse h)
    ((circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h)).symm : RealPlane →L[ℝ] RealPlane)
      (circleSum 1 (t,u)) := by
  have hd : HasStrictFDerivAt (circleSum 1)
      (circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h) : RealPlane →L[ℝ] RealPlane)
      (t,u) := circleSum_strict 1 (t,u)
  apply hd.to_localInverse.congr_of_eventuallyEq
  filter_upwards [(circleInverseHomeo h).open_target.mem_nhds hd.image_mem_toOpenPartialHomeomorph_target] with q hq
  exact (circleInverse_eq h hq).symm
lemma circleInverse_right {q : RealPlane} (hq : q ∈ (circleInverseHomeo h).target) :
    circleSum 1 (circleInverse h q)=q := by
  rw [circleInverse_eq h hq]
  exact (circleInverseHomeo h).right_inv hq
lemma circleInverse_regular :
    ∀ᶠ q in 𝓝 (circleSum 1 (t,u)), Real.sin ((circleInverse h q).2-(circleInverse h q).1) ≠ 0 := by
  have hc := (Real.continuous_sin.continuousAt.comp
    ((circleInverse_strict h).continuousAt.snd.sub (circleInverse_strict h).continuousAt.fst))
  have hh : Real.sin ((circleInverse h (circleSum 1 (t,u))).2-(circleInverse h (circleSum 1 (t,u))).1) ≠ 0 := by
    rwa [circleInverse_at h]
  exact hc.eventually_ne hh
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma triangular_injective (L : E × ℝ →L[ℝ] ℝ) (hc : L (0,1) ≠ 0) :
    Function.Injective ((ContinuousLinearMap.fst ℝ E ℝ).prod L) := by
  intro a b hab
  change (a.1,L a)=(b.1,L b) at hab
  have hab₁ := congrArg (fun q : E × ℝ => q.1) hab
  have hab₂ := congrArg (fun q : E × ℝ => q.2) hab
  dsimp only at hab₁ hab₂
  have he : a-b=(0,a.2-b.2) := Prod.ext (by simp [hab₁]) rfl
  have hz : L (0,a.2-b.2)=0 := by rw [← he,map_sub,hab₂,sub_self]
  have hm : L (0,a.2-b.2)=(a.2-b.2)*L (0,1) := by
    have h : (0,a.2-b.2)=(a.2-b.2) • ((0,1) : E × ℝ) := by ext <;> simp
    rw [h,map_smul,smul_eq_mul]
  rw [hm] at hz
  exact Prod.ext hab₁ (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hc))
omit [CompleteSpace E] in
lemma triangular_surjective (L : E × ℝ →L[ℝ] ℝ) (hc : L (0,1) ≠ 0) :
    Function.Surjective ((ContinuousLinearMap.fst ℝ E ℝ).prod L) := by
  intro b
  refine ⟨(b.1,(b.2-L (b.1,0))/L (0,1)),Prod.ext rfl ?_⟩
  change L (b.1,(b.2-L (b.1,0))/L (0,1))=b.2
  have h (r : ℝ) : L (b.1,r)=L (b.1,0)+r*L (0,1) := by
    have he : (b.1,r)=(b.1,0)+r • ((0,1) : E × ℝ) := by ext <;> simp
    rw [he,map_add,map_smul,smul_eq_mul]
  rw [h,div_mul_cancel₀ _ hc]
  ring
/-- Joint strict differentiability and a nonzero fiber derivative give one inverse
Lipschitz bound simultaneously for every nearby parameter. -/
lemma strict_fiber_uniform_antilipschitz {S : E × ℝ → ℝ} {L : E × ℝ →L[ℝ] ℝ}
    {p : E} {t : ℝ} (hS : HasStrictFDerivAt S L (p,t)) (hc : L (0,1) ≠ 0) :
    ∃ P : Set E, ∃ I : Set ℝ, IsOpen P ∧ p ∈ P ∧ IsOpen I ∧ t ∈ I ∧
      ∃ K : ℝ≥0, ∀ q ∈ P, AntilipschitzWith K (I.domRestrict (fun u => S (q,u))) := by
  let T := (ContinuousLinearMap.fst ℝ E ℝ).prod L
  let H : E × ℝ → E × ℝ := fun q => (q.1,S q)
  let Q : (E × ℝ) ≃L[ℝ] (E × ℝ) := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr (triangular_injective L hc))
    (LinearMap.range_eq_top.mpr (triangular_surjective L hc))
  have hd : HasStrictFDerivAt H (Q : E × ℝ →L[ℝ] E × ℝ) (p,t) :=
    hasStrictFDerivAt_fst.prodMk hS
  obtain ⟨V,hpt,hVo,hA⟩ := hd.approximates_deriv_on_open_nhds
  have hK := hA.antilipschitz (Or.inr (half_lt_self (inv_pos.mpr
    (Q.subsingleton_or_nnnorm_symm_pos.resolve_left (not_subsingleton (E × ℝ))))))
  obtain ⟨P,hP,I,hI,hsub⟩ := mem_nhds_prod_iff.mp (hVo.mem_nhds hpt)
  obtain ⟨P',hP'P,hP'o,hp⟩ := mem_nhds_iff.mp hP
  obtain ⟨I',hI'I,hI'o,ht⟩ := mem_nhds_iff.mp hI
  refine ⟨P',I',hP'o,hp,hI'o,ht,(‖(Q.symm : (E × ℝ) →L[ℝ] (E × ℝ))‖₊⁻¹ - ‖(Q.symm : (E × ℝ) →L[ℝ] (E × ℝ))‖₊⁻¹ / 2)⁻¹,?_⟩
  intro q hq
  apply AntilipschitzWith.of_le_mul_dist
  intro a b
  have ha : (q,a.1) ∈ V := hsub ⟨hP'P hq,hI'I a.2⟩
  have hb : (q,b.1) ∈ V := hsub ⟨hP'P hq,hI'I b.2⟩
  have h := hK.le_mul_dist ⟨(q,a.1),ha⟩ ⟨(q,b.1),hb⟩
  simpa only [Subtype.dist_eq,domRestrict,H,Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)] using h
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma circleTarget_strict (q : CircleJet) : HasStrictFDerivAt circleTarget (circleTargetDeriv q) q := by
  have hc := (Real.hasStrictDerivAt_cos q.2).comp_hasStrictFDerivAt q jetAngle.hasStrictFDerivAt
  have hs := (Real.hasStrictDerivAt_sin q.2).comp_hasStrictFDerivAt q jetAngle.hasStrictFDerivAt
  exact jetCenter.hasStrictFDerivAt.add (jetRadius.hasStrictFDerivAt.smul (hc.prodMk hs))
lemma circleTarget_continuous : Continuous circleTarget :=
  continuous_iff_continuousAt.mpr fun q => (circleTarget_strict q).continuousAt
variable {t u : ℝ} (h : Real.sin (u-t) ≠ 0)
lemma circleEndpoint_measurable : Measurable (circleEndpoint h) :=
  measurable_fst.comp ((circleInverse_measurable h).comp circleTarget_continuous.measurable)
lemma circleEndpoint_strict {q : CircleJet} (he : circleTarget q=circleSum 1 (t,u)) :
    HasStrictFDerivAt (circleEndpoint h) (circleEndpointDeriv h q) q := by
  have hi := circleInverse_strict h
  rw [← he] at hi
  exact hasStrictFDerivAt_fst.comp q (hi.comp q (circleTarget_strict q))
lemma inverse_tangent_first_ne {a : ℝ} (ha : Real.sin (a-u) ≠ 0) :
    ((circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h)).symm
      (-Real.sin a,Real.cos a)).1 ≠ 0 := by
  let L := circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h)
  let q := L.symm (-Real.sin a,Real.cos a)
  intro hq
  have he : circleSumDeriv 1 (t,u) q=(-Real.sin a,Real.cos a) := L.apply_symm_apply _
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  change q.1=0 at hq
  change 1*(-Real.sin t*q.1) + -Real.sin u*q.2 = -Real.sin a at h₁
  change 1*(Real.cos t*q.1) + Real.cos u*q.2 = Real.cos a at h₂
  simp only [hq,mul_zero,zero_add] at h₁ h₂
  apply ha
  rw [Real.sin_sub]
  linear_combination (Real.cos u)*h₁+(Real.sin u)*h₂
lemma circleEndpoint_fiber_ne {q : CircleJet} (hr : q.1.2=1) (ha : Real.sin (q.2-u) ≠ 0) :
    circleEndpointDeriv h q (0,1) ≠ 0 := by
  have he : circleTargetDeriv q (0,1)=(-Real.sin q.2,Real.cos q.2) := by
    simp [circleTargetDeriv,jetCenter,jetRadius,jetAngle,hr]
  change (((circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h)).symm
    (circleTargetDeriv q (0,1))).1) ≠ 0
  rw [he]
  exact inverse_tangent_first_ne h ha
lemma circleEndpoint_uniform {p : CircleParameter} {a : ℝ}
    (he : circleTarget (p,a)=circleSum 1 (t,u)) (hr : p.2=1) (ha : Real.sin (a-u) ≠ 0) :
    ∃ P : Set CircleParameter, ∃ I : Set ℝ, IsOpen P ∧ p ∈ P ∧ IsOpen I ∧ a ∈ I ∧
      ∃ K : ℝ≥0, ∀ q ∈ P, AntilipschitzWith K (I.domRestrict (fun v => circleEndpoint h (q,v))) :=
  strict_fiber_uniform_antilipschitz (circleEndpoint_strict h he) (circleEndpoint_fiber_ne h hr ha)
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
variable {t u : ℝ} (h : Real.sin (u-t) ≠ 0)
lemma circleEndpoint_good_neighborhood {p : CircleParameter} {a : ℝ}
    (he : circleTarget (p,a)=circleSum 1 (t,u)) (hr : p.2=1) (ha : Real.sin (a-u) ≠ 0) :
    ∃ P : Set CircleParameter, ∃ I : Set ℝ, IsOpen P ∧ p ∈ P ∧ IsOpen I ∧ a ∈ I ∧
      I ⊆ Ioc (a-Real.pi) (a-Real.pi+2*Real.pi) ∧
      ∃ K : ℝ≥0, (∀ q ∈ P, AntilipschitzWith K (I.domRestrict (fun v => circleEndpoint h (q,v)))) ∧
        ∀ q ∈ P, ∀ v ∈ I,
          circleTarget (q,v) ∈ (circleInverseHomeo h).target ∧
          Real.sin ((circleInverse h (circleTarget (q,v))).2-(circleInverse h (circleTarget (q,v))).1) ≠ 0 ∧
          circleEndpoint h (q,v) ∈ Metric.closedBall t 1 := by
  obtain ⟨P₀,I₀,hP₀,hp₀,hI₀,ha₀,K,hK⟩ := circleEndpoint_uniform h he hr ha
  have hc : ContinuousAt circleTarget (p,a) := circleTarget_continuous.continuousAt
  have hi := (circleEndpoint_strict h he).continuousAt
  have hs : ∀ᶠ w in 𝓝 (p,a), circleEndpoint h w ∈ Metric.ball t 1 := by
    have hb : Metric.ball t 1 ∈ 𝓝 (circleEndpoint h (p,a)) := by
      have ht : circleEndpoint h (p,a)=t := by simp [circleEndpoint,he,circleInverse_at]
      rw [ht]
      exact Metric.ball_mem_nhds _ (by norm_num)
    exact hi hb
  have ht : ∀ᶠ w in 𝓝 (p,a), circleTarget w ∈ (circleInverseHomeo h).target := by
    apply hc
    rw [he]
    exact (circleInverseHomeo h).open_target.mem_nhds
      ((show HasStrictFDerivAt (circleSum 1)
        (circleSumDerivEquiv (r := 1) (p := (t,u)) (by simpa only [one_mul] using h) : RealPlane →L[ℝ] RealPlane)
        (t,u) from circleSum_strict 1 (t,u)).image_mem_toOpenPartialHomeomorph_target)
  have hn : ∀ᶠ w in 𝓝 (p,a), Real.sin ((circleInverse h (circleTarget w)).2-(circleInverse h (circleTarget w)).1) ≠ 0 := by
    exact hc.eventually (by simpa only [he] using circleInverse_regular h)
  obtain ⟨P₁,hP₁,I₁,hI₁,hsub⟩ := mem_nhds_prod_iff.mp (ht.and (hn.and hs))
  obtain ⟨P₂,hP₂,hP₂o,hp₂⟩ := mem_nhds_iff.mp hP₁
  obtain ⟨I₂,hI₂,hI₂o,ha₂⟩ := mem_nhds_iff.mp hI₁
  let P := P₀ ∩ P₂
  let I := I₀ ∩ I₂ ∩ Ioo (a-Real.pi) (a+Real.pi)
  refine ⟨P,I,hP₀.inter hP₂o,⟨hp₀,hp₂⟩,(hI₀.inter hI₂o).inter isOpen_Ioo,
    ⟨⟨ha₀,ha₂⟩,by constructor <;> linarith [Real.pi_pos]⟩,?_,K,?_,?_⟩
  · intro v hv
    exact ⟨hv.2.1,by linarith [hv.2.2]⟩
  · intro q hq
    apply AntilipschitzWith.of_le_mul_dist
    intro v w
    exact (hK q hq.1).le_mul_dist ⟨v.1,v.2.1.1⟩ ⟨w.1,w.2.1.1⟩
  · intro q hq v hv
    have hh := hsub (show (q,v) ∈ P₁ ×ˢ I₁ from ⟨hP₂ hq.2,hI₂ hv.1.2⟩)
    exact ⟨hh.1,hh.2.1,Metric.ball_subset_closedBall hh.2.2⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma angleChartMeas_le : angleChartMeasure ≤ volume := Measure.restrict_le_self
lemma angleChart_preserving : MeasurePreserving angleChart angleChartMeasure
    ((volume : Measure Angles).prod volume) := by
  have h := (AddCircle.measurePreserving_mk (2*Real.pi) 0).prod
    (AddCircle.measurePreserving_mk (2*Real.pi) 0)
  convert h using 1
  · rfl
  · simp only [angleChartMeasure,zero_add,Measure.prod_restrict,← Measure.volume_eq_prod]
lemma angleChart_measure : (angleChartMeasure.map angleChart) =
    (ENNReal.ofReal (2*Real.pi))^2 • angularMeasure.prod angularMeasure := by
  rw [angleChart_preserving.map_eq,AddCircle.volume_eq_smul_haarAddCircle,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,pow_two]
  rfl
lemma integral_angular_eq_chart {f : Angles × Angles → ℝ} (hf : Measurable f) :
    (∫ p, f p ∂angularMeasure.prod angularMeasure) =
      ((2*Real.pi)^2)⁻¹ * ∫ q, f (angleChart q) ∂angleChartMeasure := by
  have h := integral_map (μ := angleChartMeasure) angleChart_preserving.measurable.aemeasurable hf.aestronglyMeasurable
  rw [angleChart_measure,integral_smul_measure,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.pi),smul_eq_mul] at h
  rw [← h]
  field_simp
lemma direction_realPlane (t : ℝ) : Complex.equivRealProdCLM (direction (t : Angles)) =
    (Real.cos t,Real.sin t) := by
  rw [direction_real,Circle.coe_exp,Complex.exp_mul_I]
  ext <;> simp [Complex.cos_ofReal_re,Complex.sin_ofReal_re]
lemma circleSum_chart (x : ℂ) (r : ℝ) (q : RealPlane) :
    Complex.equivRealProdCLM (x+(r : ℂ)*direction (angleChart q).1+direction (angleChart q).2) =
      Complex.equivRealProdCLM x+circleSum r q := by
  change Complex.equivRealProdCLM (x+(r : ℂ)*direction (q.1 : Angles)+direction (q.2 : Angles)) = _
  rw [map_add,map_add]
  have h : (r : ℂ)*direction (q.1 : Angles) = r • direction (q.1 : Angles) := by simp
  rw [h,map_smul,direction_realPlane,direction_realPlane]
  ext <;> simp [circleSum,add_assoc]
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma volume_preimage_bound {F : ℝ × ℝ → ℝ × ℝ} {s : Set (ℝ × ℝ)} {K : ℝ≥0}
    (hF : AntilipschitzWith K (s.domRestrict F)) (A : Set (ℝ × ℝ)) :
    volume (F ⁻¹' A ∩ s) ≤ (K : ENNReal)^2 * volume A := by
  have he : Subtype.val '' ((s.domRestrict F) ⁻¹' A) = F ⁻¹' A ∩ s := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩; exact ⟨hq,q.2⟩
    · rintro ⟨hp,hs⟩; exact ⟨⟨p,hs⟩,hp,rfl⟩
  have hi := (isometry_subtype_coe : Isometry (Subtype.val : s → ℝ × ℝ)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ)≤2)) ((s.domRestrict F) ⁻¹' A)
  have ha := hF.hausdorffMeasure_preimage_le (by norm_num : (0 : ℝ)≤2) A
  rw [he,hausdorffMeasure_prod_real] at hi
  rw [← hi,hausdorffMeasure_prod_real,ENNReal.rpow_two] at ha
  exact ha
lemma map_restrict_volume_le {F : ℝ × ℝ → ℝ × ℝ} (hm : Measurable F)
    {s B : Set (ℝ × ℝ)} (_hB : MeasurableSet B) {K : ℝ≥0}
    (hF : AntilipschitzWith K (s.domRestrict F)) (himage : MapsTo F s B) :
    (volume.restrict s).map F ≤ ((K^2 : ℝ≥0) : ENNReal) • volume.restrict B := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hm hA,Measure.restrict_apply (hm hA),Measure.smul_apply,
    Measure.restrict_apply hA,smul_eq_mul,ENNReal.coe_pow]
  have he : F ⁻¹' A ∩ s = F ⁻¹' (A ∩ B) ∩ s := by
    ext x
    exact ⟨fun hx => ⟨⟨hx.1,himage hx.2⟩,hx.2⟩,fun hx => ⟨hx.1.1,hx.2⟩⟩
  rw [he]
  exact volume_preimage_bound hF (A ∩ B)
lemma antilipschitz_small_perturbation {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace X] {F G : X → E} {K L : ℝ≥0} (hf : AntilipschitzWith K F)
    (hg : LipschitzWith L G) {a : ℝ} (ha : (K : ℝ)*‖a‖*(L : ℝ) ≤ 1/2) :
    AntilipschitzWith (2*K) (fun x => F x+a • G x) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h1 := hf.le_mul_dist x y
  have h2 := hg.dist_le_mul x y
  have h3 : dist (F x) (F y) ≤ dist (F x+a • G x) (F y+a • G y) + ‖a‖*dist (G x) (G y) := by
    simpa only [add_sub_cancel_right,dist_smul₀] using
      dist_sub_sub_le (F x+a • G x) (a • G x) (F y+a • G y) (a • G y)
  have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg a)
  have h5 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add_right h4 _)) K.2
  have h6 := mul_le_mul_of_nonneg_right ha (dist_nonneg (x := x) (y := y))
  simp only [NNReal.coe_mul,NNReal.coe_ofNat]
  nlinarith
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma realDirection_norm_le (t : ℝ) : ‖(Real.cos t,Real.sin t)‖ ≤ (1 : ℝ) := by
  rw [Prod.norm_def,max_le_iff]
  exact ⟨by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one t,
    by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one t⟩
lemma circleSum_decompose (r : ℝ) (q : RealPlane) :
    circleSum r q = r • (Real.cos q.1,Real.sin q.1) + (Real.cos q.2,Real.sin q.2) := rfl
lemma circleSum_norm_le (r : ℝ) (q : RealPlane) : ‖circleSum r q‖ ≤ |r|+1 := by
  rw [circleSum_decompose]
  calc
    _ ≤ ‖r • (Real.cos q.1,Real.sin q.1)‖+‖(Real.cos q.2,Real.sin q.2)‖ := norm_add_le _ _
    _ ≤ |r| * 1+1 := by rw [norm_smul]; exact add_le_add (mul_le_mul_of_nonneg_left (realDirection_norm_le _) (norm_nonneg r)) (realDirection_norm_le _)
    _ = _ := by ring
lemma circleSum_perturb_identity (r : ℝ) (q : RealPlane) :
    circleSum r q = circleSum 1 q + (r-1) • (Real.cos q.1,Real.sin q.1) := by
  apply Prod.ext
  · change r*Real.cos q.1+Real.cos q.2 = 1*Real.cos q.1+Real.cos q.2+(r-1)*Real.cos q.1
    ring
  · change r*Real.sin q.1+Real.sin q.2 = 1*Real.sin q.1+Real.sin q.2+(r-1)*Real.sin q.1
    ring
lemma circleSum_parameter_tendsto {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (q : RealPlane) :
    Tendsto (fun n => circleSum (r n) q) atTop (𝓝 (circleSum 1 q)) := by
  exact (hr.mul_const (Real.cos q.1) |>.add_const (Real.cos q.2)).prodMk_nhds
    (hr.mul_const (Real.sin q.1) |>.add_const (Real.sin q.2))
lemma circleSum_eventual_image {r : ℕ → ℝ} {y : ℕ → RealPlane} {x : RealPlane}
    (hr : Tendsto r atTop (𝓝 1)) (hy : Tendsto y atTop (𝓝 x)) :
    ∀ᶠ n in atTop, ∀ q, y n+circleSum (r n) q ∈ Metric.closedBall x 4 := by
  filter_upwards [hr.eventually (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ)<1)),
    hy.eventually (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ)<1))] with n hn hyn
  intro q
  have hh := circleSum_norm_le (r n) q
  have hb : |r n| ≤ 2 := by
    have ht := norm_le_norm_sub_add (r n) (1 : ℝ)
    rw [Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,abs_one] at ht
    rw [Real.dist_eq] at hn
    linarith
  rw [Metric.mem_closedBall]
  calc
    _ ≤ dist (y n+circleSum (r n) q) (y n)+dist (y n) x := dist_triangle _ _ _
    _ = ‖circleSum (r n) q‖+dist (y n) x := by rw [dist_eq_norm,add_sub_cancel_left]
    _ ≤ 4 := by linarith
lemma circleSum_limit_image (x q : RealPlane) : x+circleSum 1 q ∈ Metric.closedBall x 4 := by
  rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left]
  have hh := circleSum_norm_le 1 q
  norm_num at hh
  linarith
lemma circleSum_eventual_antilipschitz {V : Set RealPlane} {K : ℝ≥0}
    (hK : AntilipschitzWith K (V.domRestrict (circleSum 1)))
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (y : ℕ → RealPlane) :
    ∀ᶠ n in atTop, AntilipschitzWith (2*K) (V.domRestrict (fun q => y n+circleSum (r n) q)) := by
  have hD : LipschitzWith 1 (fun q : V => (Real.cos q.1.1,Real.sin q.1.1)) := by
    have hf : LipschitzWith 1 (fun q : V => q.1.1) := LipschitzWith.of_dist_le_mul (fun q p => by
      simp only [NNReal.coe_one,one_mul]
      exact le_max_left _ _)
    simpa only [Function.comp_def,one_mul] using realDirection_lipschitz.comp hf
  have ht : Tendsto (fun n => (K : ℝ)*‖r n-1‖) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => r n-1) atTop (𝓝 0) := by simpa using hr.sub_const 1
    simpa using hh.norm.const_mul (K : ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with n hn
  have ha := antilipschitz_small_perturbation hK hD (a := r n-1) (by simpa using le_of_lt hn)
  apply AntilipschitzWith.of_le_mul_dist
  intro q p
  have hh := ha.le_mul_dist q p
  simpa only [Set.domRestrict_apply,dist_add_left,← circleSum_perturb_identity] using hh
lemma circleSum_limit_antilipschitz {V : Set RealPlane} {K : ℝ≥0}
    (hK : AntilipschitzWith K (V.domRestrict (circleSum 1))) (x : RealPlane) :
    AntilipschitzWith (2*K) (V.domRestrict (fun q => x+circleSum 1 q)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro q p
  have hh := hK.le_mul_dist q p
  simpa only [Set.domRestrict_apply,dist_add_left] using hh.trans
    (mul_le_mul_of_nonneg_right (by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; linarith [K.2] : (K : ℝ)≤ ((2*K : ℝ≥0) : ℝ)) dist_nonneg)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma measure_null_of_locally_null_on_conull {X : Type*} [TopologicalSpace X]
    [HereditarilyLindelofSpace X] [MeasurableSpace X] {μ : Measure X} {R A : Set X}
    (hR : μ Rᶜ = 0) (h : ∀ x ∈ R, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ μ (A ∩ V) = 0) :
    μ A = 0 := by
  classical
  choose V hVo hxV hV0 using (fun x : R => h x.1 x.2)
  obtain ⟨t,ht,hcov⟩ := (HereditarilyLindelofSpace.isLindelof R).elim_countable_subcover V hVo
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩)
  have hu : μ (⋃ i ∈ t, A ∩ V i) = 0 := (measure_biUnion_null_iff ht).mpr (fun i _ => hV0 i)
  apply measure_mono_null (t := Rᶜ ∪ ⋃ i ∈ t, A ∩ V i) _ (measure_union_null hR hu)
  intro x hx
  by_cases hr : x ∈ R
  · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcov hr)
    exact Or.inr (mem_iUnion₂.mpr ⟨i,hi,hx,hxi⟩)
  · exact Or.inl hr
lemma circleSum_regular_ae : ∀ᵐ p : RealPlane ∂volume, Real.sin (p.2-p.1) ≠ 0 := by
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · exact Eventually.of_forall fun t => by
      have hs : {s : ℝ | Real.sin (s-t)=0} ⊆ Set.range (fun n : ℤ => t+n*Real.pi) := by
        intro s h
        obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp h
        exact ⟨n,by linarith⟩
      change volume {s : ℝ | ¬ Real.sin (s-t) ≠ 0} = 0
      simpa only [not_not] using measure_mono_null hs ((countable_range _).measure_zero volume)
  · exact (measurableSet_eq_fun (Real.measurable_sin.comp (measurable_snd.sub measurable_fst)) measurable_const).compl
lemma circleSum_preimage_null {r : ℝ} (hr : r ≠ 0) {A : Set RealPlane} (hA : volume A=0) :
    volume (circleSum r ⁻¹' A)=0 := by
  apply measure_null_of_locally_null_on_conull (μ := (volume : Measure RealPlane))
    (R := {p : RealPlane | Real.sin (p.2-p.1) ≠ 0}) (A := circleSum r ⁻¹' A) circleSum_regular_ae
  intro p hp
  obtain ⟨s,hso,hps,K,hK⟩ := circleSum_local_antilipschitz (mul_ne_zero hr hp)
  refine ⟨s,hso,hps,?_⟩
  have hh := volume_preimage_bound hK A
  rw [hA,mul_zero] at hh
  exact nonpos_iff_eq_zero.mp hh
lemma circleSum_quasiMeasurePreserving {r : ℝ} (hr : r ≠ 0) :
    Measure.QuasiMeasurePreserving (circleSum r) volume volume := by
  refine ⟨(circleSum_continuous r).measurable,Measure.AbsolutelyContinuous.mk (fun A hA hz => ?_)⟩
  rw [Measure.map_apply (circleSum_continuous r).measurable hA]
  exact circleSum_preimage_null hr hz
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CircleTransport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter Topology
namespace EuclideanFiveColor
/-- A uniformly bounded nonnegative sequence converging locally in L¹ on a conull open
cover converges globally in L¹ for a finite inner-regular measure. -/
lemma tendsto_integral_of_local_cover {X I : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [Measure.InnerRegularCompactLTTop μ] {F : ℕ → X → ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hb : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (V : I → Set X) (hVo : ∀ i, IsOpen (V i)) (hfull : ∀ᵐ x ∂μ, x ∈ ⋃ i, V i)
    (hlocal : ∀ i, Tendsto (fun n => ∫ x in V i, F n x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hKU,hK,hμK⟩ := (isOpen_iUnion hVo).measurableSet.exists_isCompact_sdiff_lt
    (measure_ne_top μ _) (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (half_pos hε)))
  have hδ : μ Kᶜ < ENNReal.ofReal (ε/2) := by
    have he : (Kᶜ : Set X) =ᵐ[μ] ((⋃ i, V i) \ K : Set X) := by
      filter_upwards [hfull] with x hx
      exact propext ⟨fun h => ⟨hx,h⟩,fun h => h.2⟩
    exact (measure_congr he).trans_lt hμK
  have hδr : μ.real Kᶜ < ε/2 := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (ENNReal.ofReal_ne_top)).mpr hδ
    simpa only [Measure.real,ENNReal.toReal_ofReal (le_of_lt (half_pos hε))] using hh
  obtain ⟨J,hJ⟩ := hK.elim_finite_subcover V hVo hKU
  have hlim : Tendsto (fun n => ∑ i ∈ J, ∫ x in V i, F n x ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum J (fun i _ => hlocal i)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hmaj : (∫ x, F n x ∂μ) ≤ (∑ i ∈ J, ∫ x in V i, F n x ∂μ) + μ.real Kᶜ := by
    have hJJ : Integrable (fun x => ∑ i ∈ J, (V i).indicator (F n) x) μ :=
      integrable_finsetSum J (fun i _ => (hF n).indicator (hVo i).measurableSet)
    have hCC : Integrable (Kᶜ.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const _).indicator hK.measurableSet.compl
    have hi := integral_mono (hF n) (hJJ.add hCC) (fun x => by
      have hs (i : I) : 0 ≤ (V i).indicator (F n) x := indicator_nonneg (fun y _ => (hb n y).1) x
      by_cases hx : x ∈ K
      · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hJ hx)
        have hsum := Finset.single_le_sum (fun j _ => hs j) hi
        simp only [Pi.add_apply,indicator_of_notMem (show x ∉ Kᶜ from not_not.mpr hx),add_zero]
        exact (by simpa only [indicator_of_mem hxi] using hsum)
      · change F n x ≤ (∑ i ∈ J, (V i).indicator (F n) x) + Kᶜ.indicator (fun _ => (1 : ℝ)) x
        rw [indicator_of_mem hx]
        linarith [Finset.sum_nonneg (fun i (_ : i ∈ J) => hs i), (hb n x).2])
    apply hi.trans_eq
    refine (integral_add hJJ hCC).trans ?_
    apply congrArg₂ (·+·)
    · exact (integral_finsetSum J (fun i _ => (hF n).indicator (hVo i).measurableSet)).trans
        (Finset.sum_congr rfl (fun i _ => integral_indicator (hVo i).measurableSet))
    · rw [integral_indicator hK.measurableSet.compl]
      simp only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => (hb n x).1)]
  have hh := hN n hn
  have hs0 : 0 ≤ ∑ i ∈ J, ∫ x in V i, F n x ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg (fun x => (hb n x).1)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hs0] at hh
  linarith
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma bounded_difference_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    Integrable (fun x => ‖f x-g x‖) μ := by
  apply Integrable.of_bound ((hf.sub hg).norm.aestronglyMeasurable) 1
  exact Eventually.of_forall fun x => by
    rw [norm_norm,Real.norm_eq_abs,abs_le]
    change -1 ≤ f x-g x ∧ f x-g x ≤ 1
    constructor <;> linarith [(hfb x).1,(hfb x).2,(hgb x).1,(hgb x).2]
lemma circleSum_tendsto_L1 {μ : Measure RealPlane} [IsFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] (hμ : μ ≤ volume)
    {r : ℕ → ℝ} {y : ℕ → RealPlane} {x : RealPlane}
    (hr : Tendsto r atTop (𝓝 1)) (hy : Tendsto y atTop (𝓝 x))
    {f : RealPlane → ℝ} (hf : Measurable f) (hfb : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    Tendsto (fun n => ∫ q, ‖f (y n+circleSum (r n) q)-f (x+circleSum 1 q)‖ ∂μ) atTop (𝓝 0) := by
  classical
  let T : ℕ → RealPlane → RealPlane := fun n q => y n+circleSum (r n) q
  let S : RealPlane → RealPlane := fun q => x+circleSum 1 q
  have hT (n : ℕ) : Measurable (T n) := (continuous_const.add (circleSum_continuous _)).measurable
  have hS : Measurable S := (continuous_const.add (circleSum_continuous _)).measurable
  let R : Set RealPlane := {p | Real.sin (p.2-p.1) ≠ 0}
  have hex : ∀ p : R, ∃ V : Set RealPlane, IsOpen V ∧ p.1 ∈ V ∧
      ∃ K : ℝ≥0, AntilipschitzWith K (V.domRestrict (circleSum 1)) := by
    intro p
    exact circleSum_local_antilipschitz (by simpa only [one_mul] using (show Real.sin (p.1.2-p.1.1) ≠ 0 from p.2))
  choose V hVo hpV K hK using hex
  have hfull : ∀ᵐ q ∂μ, q ∈ ⋃ p : R, V p := by
    filter_upwards [circleSum_regular_ae.filter_mono (ae_mono hμ)] with q hq
    exact mem_iUnion.mpr ⟨⟨q,hq⟩,hpV ⟨q,hq⟩⟩
  apply tendsto_integral_of_local_cover (μ := μ)
    (fun n => bounded_difference_integrable (hf.comp (hT n)) (hf.comp hS)
      (fun q => hfb (T n q)) (fun q => hfb (S q)))
    (fun n q => ⟨norm_nonneg _,by
      rw [Real.norm_eq_abs,abs_le]
      change -1 ≤ f (T n q)-f (S q) ∧ f (T n q)-f (S q) ≤ 1
      constructor <;> linarith [(hfb (T n q)).1,(hfb (T n q)).2,(hfb (S q)).1,(hfb (S q)).2]⟩)
    V hVo hfull
  intro p
  let B := Metric.closedBall x (4 : ℝ)
  let ν : Measure RealPlane := volume.restrict B
  have hB : MeasurableSet B := measurableSet_closedBall
  let : IsFiniteMeasure ν := ⟨by simpa [ν] using (isCompact_closedBall x 4).measure_lt_top⟩
  have hfi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hfb z).1]; exact (hfb z).2)
  have hmapT : ∀ᶠ n in atTop, ((μ.restrict (V p)).map (T n)) ≤
      (((2*K p)^2 : ℝ≥0) : ENNReal) • ν := by
    filter_upwards [circleSum_eventual_image hr hy,circleSum_eventual_antilipschitz (hK p) hr y] with n hn ha
    apply (Measure.map_mono (Measure.restrict_mono_measure hμ (V p)) (hT n)).trans
    exact map_restrict_volume_le (hT n) hB ha (fun q _ => hn q)
  have hmapS : ((μ.restrict (V p)).map S) ≤ (((2*K p)^2 : ℝ≥0) : ENNReal) • ν := by
    apply (Measure.map_mono (Measure.restrict_mono_measure hμ (V p)) hS).trans
    exact map_restrict_volume_le hS hB (circleSum_limit_antilipschitz (hK p) x)
      (fun q _ => circleSum_limit_image x q)
  apply tendsto_integral_norm_comp_sub_eventual hT hS hmapT hmapS _ hfi
  exact Eventually.of_forall fun q => hy.add (circleSum_parameter_tendsto hr q)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma angularSum_measurable (x : ℂ) (r : ℝ) : Measurable (angularSum x r) :=
  (measurable_const.add (measurable_const.mul (direction_continuous.measurable.comp measurable_fst))).add
    (direction_continuous.measurable.comp measurable_snd)
lemma angularSum_chart (x : ℂ) (r : ℝ) (q : RealPlane) :
    angularSum x r (angleChart q) = Complex.equivRealProdCLM.symm
      (Complex.equivRealProdCLM x+circleSum r q) := by
  apply Complex.equivRealProdCLM.injective
  simpa only [angularSum,ContinuousLinearEquiv.apply_symm_apply] using circleSum_chart x r q
lemma angularSum_quasiMeasurePreserving (x : ℂ) {r : ℝ} (hr : r ≠ 0) :
    Measure.QuasiMeasurePreserving (angularSum x r) (angularMeasure.prod angularMeasure) volume := by
  have hreal : Measure.QuasiMeasurePreserving
      (fun q => Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM x+circleSum r q)) volume volume :=
    (Complex.volume_preserving_equiv_real_prod.symm).quasiMeasurePreserving.comp
      ((measurePreserving_add_left volume (Complex.equivRealProdCLM x)).quasiMeasurePreserving.comp
        (circleSum_quasiMeasurePreserving hr))
  refine ⟨angularSum_measurable x r,Measure.AbsolutelyContinuous.mk (fun A hA hz => ?_)⟩
  rw [Measure.map_apply (angularSum_measurable x r) hA]
  have hpre : angleChartMeasure (angleChart ⁻¹' (angularSum x r ⁻¹' A))=0 := by
    apply le_antisymm _ bot_le
    apply (angleChartMeas_le _).trans
    have hz' := hreal.preimage_null hz
    simpa [preimage_preimage,Function.comp_def,angularSum_chart] using le_of_eq hz'
  have hz' : (ENNReal.ofReal (2*Real.pi))^2 *
      (angularMeasure.prod angularMeasure) (angularSum x r ⁻¹' A)=0 := by
    rw [← smul_eq_mul,← Measure.smul_apply,← angleChart_measure,
      Measure.map_apply angleChart_preserving.measurable ((angularSum_measurable x r) hA)]
    exact hpre
  exact (mul_eq_zero.mp hz').resolve_left (by positivity)
lemma angularSum_tendsto_L1 {r : ℕ → ℝ} {y : ℕ → ℂ} {x : ℂ}
    (hr : Tendsto r atTop (𝓝 1)) (hy : Tendsto y atTop (𝓝 x))
    {f : ℂ → ℝ} (hf : Measurable f) (hfb : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    Tendsto (fun n => ∫ p, ‖f (angularSum (y n) (r n) p)-f (angularSum x 1 p)‖
      ∂angularMeasure.prod angularMeasure) atTop (𝓝 0) := by
  have h := circleSum_tendsto_L1 (μ := angleChartMeasure) angleChartMeas_le hr
    (Complex.equivRealProdCLM.continuous.tendsto x |>.comp hy)
    (hf.comp Complex.equivRealProdCLM.symm.continuous.measurable)
    (fun z => hfb (Complex.equivRealProdCLM.symm z))
  have he := h.const_mul (((2*Real.pi)^2)⁻¹)
  simp only [mul_zero] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  simpa only [Function.comp_def,Pi.sub_apply,angularSum_chart] using
    (integral_angular_eq_chart (f := fun p => ‖f (angularSum (y n) (r n) p)-f (angularSum x 1 p)‖)
      (((hf.comp (angularSum_measurable _ _)).sub (hf.comp (angularSum_measurable _ _))).norm))
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
namespace EuclideanFiveColor
lemma samplingParameter_tendsto {x z : ℂ} {y : ℕ → ℂ} {r : ℕ → ℝ}
    (hy : Tendsto y atTop (𝓝 z)) (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => samplingParameter x (y n) (r n)) atTop (𝓝 (samplingParameter x z 1)) :=
  (Complex.equivRealProdCLM.continuous.continuousAt.tendsto.comp (hy.sub_const x)).prodMk_nhds hr
lemma circleTarget_sampling (x y : ℂ) (r f : ℝ) :
    Complex.equivRealProdCLM x + circleTarget (samplingParameter x y r,f) =
      Complex.equivRealProdCLM (y+(r : ℂ)*direction (f : Angles)) := by
  have he : (r : ℂ)*direction (f : Angles)=r • direction (f : Angles) := by simp
  rw [he,map_add,map_smul,direction_realPlane]
  simp only [circleTarget,samplingParameter,map_sub]
  abel
lemma circleInverse_sampling {t u : ℝ} (h : Real.sin (u-t) ≠ 0) {x y : ℂ} {r f : ℝ}
    (ht : circleTarget (samplingParameter x y r,f) ∈ (circleInverseHomeo h).target) :
    y+(r : ℂ)*direction (f : Angles) =
      angularSum x 1 (angleChart (circleInverse h (circleTarget (samplingParameter x y r,f)))) := by
  rw [angularSum_chart,circleInverse_right h ht]
  apply Complex.equivRealProdCLM.injective
  exact (circleTarget_sampling x y r f).symm
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_WeakColoring
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma shiftL2_ae (z : ℂ) (f : PlaneL2) : shiftL2 z f =ᵐ[volume] fun x => f (x+z) :=
  Lp.coeFn_compMeasurePreserving f _
lemma shiftL2_continuous (f : PlaneL2) : Continuous (fun z => shiftL2 z f) := by
  let g : C(ℂ,C(ℂ,ℂ)) := (ContinuousMap.mk (fun p : ℂ × ℂ => p.2+p.1) (by fun_prop)).curry
  exact continuous_const.compMeasurePreservingLp g.continuous (fun z => measurePreserving_add_right volume z) (by simp)
lemma product_zero_of_inner_zero (f g : PlaneL2) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hg : ∀ᵐ x ∂volume, 0 ≤ g x) (h : ⟪f,g⟫ = 0) :
    ∀ᵐ x ∂volume, f x*g x=0 := by
  have hi : Integrable (fun x : ℂ => f x*g x) volume := by
    simpa [RCLike.inner_apply,mul_comm] using (L2.integrable_inner (𝕜 := ℝ) f g)
  have hn : ∀ᵐ x ∂volume, 0 ≤ f x*g x := by
    filter_upwards [hf,hg] with x hx hy
    exact mul_nonneg hx hy
  rw [L2.inner_def] at h
  apply (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
  simpa [RCLike.inner_apply,mul_comm] using h
/-- AE exclusions over any full-support parameter measure upgrade to every parameter. -/
lemma all_parameters_product_zero {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    (μ : Measure T) [μ.IsOpenPosMeasure] (d : T → ℂ) (hd : Continuous d)
    (f : PlaneL2) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (ho : ∀ᵐ t ∂μ, ∀ᵐ x ∂(volume : Measure ℂ), f x*f (x+d t)=0) :
    ∀ t : T, ∀ᵐ x ∂(volume : Measure ℂ), f x*f (x+d t)=0 := by
  have hc : Continuous (fun t : T => ⟪f,shiftL2 (d t) f⟫) :=
    continuous_const.inner ((shiftL2_continuous f).comp hd)
  have hz : (fun t : T => ⟪f,shiftL2 (d t) f⟫) =ᵐ[μ] fun _ => 0 := by
    filter_upwards [ho] with t ht
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [shiftL2_ae (d t) f,ht] with x hx hh
    simpa [RCLike.inner_apply,mul_comm,hx] using hh
  have he := (hc.ae_eq_iff_eq μ continuous_const).mp hz
  intro t
  have hg : ∀ᵐ x ∂volume, 0 ≤ shiftL2 (d t) f x := by
    filter_upwards [shiftL2_ae (d t) f,
      (measurePreserving_add_right volume (d t)).quasiMeasurePreserving.ae hf] with x hx hh
    simpa only [hx] using hh
  have h0 := product_zero_of_inner_zero f (shiftL2 (d t) f) hf hg (congrFun he t)
  filter_upwards [h0,shiftL2_ae (d t) f] with x hx hh
  simpa only [hh] using hx
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
include hc
lemma truncatedVector_ae (i : Fin k) (n : ℕ) :
    truncatedVector c hc i n =ᵐ[volume] (truncatedClass c i n).indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _
lemma weak_all_directions (hweak : WeakColoring k c) :
    ∀ t : Angles, ∀ᵐ z ∂(volume : Measure ℂ), c z ≠ c (z+direction t) := by
  have ho : ∀ᵐ t ∂angularMeasure, ∀ᵐ z ∂(volume : Measure ℂ), c z ≠ c (z+direction t) := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod hweak.2)
    exact (measurableSet_eq_fun (hc.comp measurable_fst)
      (hc.comp (measurable_fst.add (direction_continuous.measurable.comp measurable_snd)))).compl
  have hz (i : Fin k) (n : ℕ) : ∀ t : Angles, ∀ᵐ z ∂(volume : Measure ℂ),
      truncatedVector c hc i n z*truncatedVector c hc i n (z+direction t)=0 := by
    apply all_parameters_product_zero angularMeasure direction direction_continuous
    · filter_upwards [truncatedVector_ae c hc i n] with z hz
      rw [hz]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · filter_upwards [ho] with t ht
      filter_upwards [ht,truncatedVector_ae c hc i n,
        (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving.ae (truncatedVector_ae c hc i n)] with z hne h1 h2
      rw [h1,h2]
      by_cases h : z ∈ truncatedClass c i n
      · have hh : z+direction t ∉ truncatedClass c i n := fun hh => hne (h.1.trans hh.1.symm)
        simp [Set.indicator_of_notMem hh]
      · simp [Set.indicator_of_notMem h]
  intro t
  have hi : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin k, ∀ n : ℕ,
      ((truncatedClass c i n).indicator (fun _ => (1 : ℝ)) z)*
      ((truncatedClass c i n).indicator (fun _ => (1 : ℝ)) (z+direction t))=0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    filter_upwards [hz i n t,truncatedVector_ae c hc i n,
      (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving.ae (truncatedVector_ae c hc i n)] with z h0 h1 h2
    simpa only [h1,h2] using h0
  filter_upwards [hi] with z hz
  intro he
  obtain ⟨n,hn⟩ := exists_nat_gt (max ‖z‖ ‖z+direction t‖)
  have h1 : z ∈ truncatedClass c (c z) n := ⟨rfl,by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (lt_of_le_of_lt (le_max_left _ _) hn).le⟩
  have h2 : z+direction t ∈ truncatedClass c (c z) n := ⟨he.symm,by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (lt_of_le_of_lt (le_max_right _ _) hn).le⟩
  have h0 := hz (c z) n
  simp [Set.indicator_of_mem h1,Set.indicator_of_mem h2] at h0
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma densityOne_disjoint {A B : Set ℂ} (hB : MeasurableSet B)
    (hd : AEDisjoint volume A B) {x : ℂ} (hA : DensityOne A x) : ¬ DensityOne B x := by
  intro hb
  have hh := hA.add hb
  have hle : (1 : ENNReal)+1 ≤ 1 := le_of_tendsto hh (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [← ENNReal.add_div,← measure_union₀ (hB.inter measurableSet_closedBall).nullMeasurableSet
      (hd.mono inter_subset_left inter_subset_left)]
    apply (ENNReal.div_le_iff (Metric.measure_closedBall_pos volume x hr).ne'
      ((isCompact_closedBall x r).measure_ne_top)).mpr
    simpa only [one_mul] using measure_mono (union_subset inter_subset_right inter_subset_right))
  norm_num at hle
lemma densityOne_translate {A : Set ℂ} {x u : ℂ} :
    DensityOne ((fun z : ℂ => z+u) ⁻¹' A) x ↔ DensityOne A (x+u) := by
  have he (r : ℝ) : (fun z : ℂ => z+u) ⁻¹' (Metric.closedBall (x+u) r) = Metric.closedBall x r := by
    ext z
    simp only [Set.mem_preimage,Metric.mem_closedBall,dist_eq_norm,add_sub_add_right_eq_sub]
  have h1 (r : ℝ) : volume (((fun z : ℂ => z+u) ⁻¹' A) ∩ Metric.closedBall x r) =
      volume (A ∩ Metric.closedBall (x+u) r) := by
    rw [← he,← Set.preimage_inter,measure_preimage_add_right]
  have h2 (r : ℝ) : volume (Metric.closedBall x r) = volume (Metric.closedBall (x+u) r) := by
    rw [← he,measure_preimage_add_right]
  simp only [DensityOne,h1,h2]
lemma direction_exists {u : ℂ} (hu : ‖u‖=1) : ∃ t, direction t=u := by
  let v : Circle := ⟨u,mem_sphere_zero_iff_norm.mpr hu⟩
  obtain ⟨t,ht⟩ := Circle.exp_surjective v
  exact ⟨(t : Angles),by simpa only [direction_real] using congrArg Subtype.val ht⟩
lemma weak_density_proper {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    (i : Fin k) {x y : ℂ} (hxy : ‖x-y‖=1) (hx : DensityOne {z | c z=i} x) :
    ¬ DensityOne {z | c z=i} y := by
  let u := y-x
  obtain ⟨t,ht⟩ := direction_exists (u := u) (by simpa only [u,norm_sub_rev] using hxy)
  have hd : AEDisjoint volume {z | c z=i} ((fun z : ℂ => z+u) ⁻¹' {z | c z=i}) := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [weak_all_directions c hc hw t] with z hz
    rintro ⟨h1,h2⟩
    exact hz (by simpa only [ht] using h1.trans h2.symm)
  have hh := densityOne_disjoint ((measurableSet_eq_fun hc measurable_const).preimage
    (measurable_id.add_const u)) hd hx
  simp only [id_eq] at hh
  rw [densityOne_translate] at hh
  simpa only [u,add_sub_cancel] using hh
lemma ae_density_actual {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) :
    ∀ᵐ x ∂(volume : Measure ℂ), DensityOne {z | c z=c x} x := by
  have hh : ∀ᵐ x ∂(volume : Measure ℂ), ∀ i : Fin k,
      Tendsto (fun r : ℝ => volume ({z | c z=i} ∩ Metric.closedBall x r) / volume (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 (({z | c z=i} : Set ℂ).indicator (1 : ℂ → ENNReal) x)) :=
    ae_all_iff.mpr fun i => Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume
      (measurableSet_eq_fun hc measurable_const)
  filter_upwards [hh] with x hx
  simpa only [DensityOne,Set.indicator_of_mem (show x ∈ {z | c z=c x} from rfl),Pi.one_apply] using hx (c x)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Compactness
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
lemma oneL2_ae : oneL2 μ =ᵐ[μ] (fun _ => (1 : ℝ)) := by
  simpa only [oneL2,Set.indicator_univ] using (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
    (hμs := measure_ne_top μ Set.univ) (c := (1 : ℝ)))
lemma weak_limit_nonneg {f : ℕ → RealL2 μ} {b : RealL2 μ}
    (ht : ∀ v, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hf : ∀ n, 0 ≤ᵐ[μ] f n) : 0 ≤ᵐ[μ] b := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (MemLp.integrable (by norm_num) (Lp.memLp b))
  intro s hs hμs
  have h := ht (indicatorConstLp 2 hs hμs.ne 1)
  have he (v : RealL2 μ) : ⟪v,indicatorConstLp 2 hs hμs.ne 1⟫ = ∫ x in s, v x ∂μ := by
    rw [real_inner_comm,L2.inner_indicatorConstLp_one]
  simp_rw [he] at h
  exact ge_of_tendsto h (Eventually.of_forall fun n => integral_nonneg_of_ae (ae_restrict_of_ae (hf n)))
lemma weak_limit_le_one {f : ℕ → RealL2 μ} {b : RealL2 μ}
    (ht : ∀ v, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hf : ∀ n, f n ≤ᵐ[μ] (fun _ => (1 : ℝ))) : b ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
  have hh : 0 ≤ᵐ[μ] (oneL2 μ-b) := weak_limit_nonneg μ
    (f := fun n => oneL2 μ-f n) (fun v => by simpa only [inner_sub_left] using tendsto_const_nhds.sub (ht v)) (fun n => by
      filter_upwards [Lp.coeFn_sub (oneL2 μ) (f n),oneL2_ae μ,hf n] with x hx h1 hn
      simpa only [hx,Pi.sub_apply,Pi.zero_apply,h1,sub_nonneg] using hn)
  filter_upwards [hh,Lp.coeFn_sub (oneL2 μ) b,oneL2_ae μ] with x hx he h1
  simpa only [he,Pi.sub_apply,Pi.zero_apply,h1,sub_nonneg] using hx
lemma weak_limit_sum {ι : Type*} [Fintype ι] {f : ℕ → ι → RealL2 μ} {b : ι → RealL2 μ}
    (ht : ∀ i v, Tendsto (fun n => ⟪f n i,v⟫) atTop (𝓝 ⟪b i,v⟫))
    (hf : ∀ n, ∑ i, f n i = oneL2 μ) : ∑ i, b i = oneL2 μ := by
  apply ext_inner_right ℝ
  intro v
  have hh := tendsto_finsetSum Finset.univ (fun i _ => ht i v)
  simp_rw [← sum_inner,hf] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma sample_sum (hc : Measurable c) (y : ℂ) (r : ℝ) :
    ∑ i, sample c hc y r i = oneL2 angularMeasure := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => sample c hc y r i),
    ae_all_iff.mpr (sample_ae c hc y r),oneL2_ae angularMeasure] with t ht ha h1
  rw [ht,h1]
  simp only [ha,sampleFn]
  simp
end EuclideanFiveColor
end

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor.WeakBall
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
omit [TopologicalSpace.SeparableSpace E] in
lemma value_eval (a : Space E) (v : E) : ⟪value E a,v⟫ = a.1 v := by
  simp only [value,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply]
omit [TopologicalSpace.SeparableSpace E] in
lemma tendsto_iff {I : Type*} {l : Filter I} {f : I → Space E} {b : Space E} :
    Tendsto f l (𝓝 b) ↔ ∀ v : E, Tendsto (fun n => ⟪value E (f n),v⟫) l (𝓝 ⟪value E b,v⟫) := by
  simp only [value_eval]
  rw [tendsto_subtype_rng, tendsto_iff_forall_eval_tendsto_topDualPairing]
  rfl
end EuclideanFiveColor.WeakBall
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
lemma bounded_test_error {f v g : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1) (hv : Integrable v μ) (hg : Integrable g μ) :
    dist (∫ x, f x*v x ∂μ) (∫ x, f x*g x ∂μ) ≤ ∫ x, ‖v x-g x‖ ∂μ := by
  have hft : MemLp f ⊤ μ := MemLp.of_bound hf 1 hfb
  have hiv : Integrable (fun x => f x*v x) μ := hv.mul_of_top_right hft
  have hig : Integrable (fun x => f x*g x) μ := hg.mul_of_top_right hft
  rw [dist_eq_norm,← integral_sub hiv hig]
  calc
    _ ≤ ∫ x, ‖f x*v x-f x*g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖v x-g x‖ ∂μ := by
      apply integral_mono_ae ((hv.mul_of_top_right hft).sub (hg.mul_of_top_right hft)).norm (hv.sub hg).norm
      filter_upwards [hfb] with x hx
      change ‖f x * v x - f x * g x‖ ≤ ‖v x - g x‖
      rw [← mul_sub,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
lemma weak_L2_to_weakStar {f : ℕ → Lp ℝ 2 μ} {b : Lp ℝ 2 μ}
    (hf : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ 1) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ 1)
    (ht : ∀ v : Lp ℝ 2 μ, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    {v : X → ℝ} (hv : Integrable v μ) :
    Tendsto (fun n => ∫ x, f n x*v x ∂μ) atTop (𝓝 (∫ x, b x*v x ∂μ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g,hg,hgm⟩ := (memLp_one_iff_integrable.mpr hv).exists_simpleFunc_eLpNorm_sub_lt (by simp : (1 : ENNReal) ≠ ⊤)
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < ε/3))
  obtain ⟨C,hC⟩ := g.exists_forall_norm_le
  have hg2 : MemLp g 2 μ := MemLp.of_bound g.measurable.aestronglyMeasurable C (Eventually.of_forall hC)
  have hgi : Integrable (fun x => g x) μ := memLp_one_iff_integrable.mp hgm
  have herr : (∫ x, ‖v x-g x‖ ∂μ) < ε/3 := by
    change (∫ x, ‖(v - (fun x => g x)) x‖ ∂μ) < ε/3
    rw [integral_norm_eq_lintegral_enorm (hv.sub hgi).aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm]
    exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hg) ENNReal.ofReal_ne_top).mpr hg |>.trans_eq (ENNReal.toReal_ofReal (by positivity))
  have he (w : Lp ℝ 2 μ) : ⟪w,hg2.toLp g⟫ = ∫ x, w x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with x hx
    simp [hx, mul_comm]
  have htt := ht (hg2.toLp g)
  simp_rw [he] at htt
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp htt (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h1 := bounded_test_error (Lp.aestronglyMeasurable (f n)) (hf n) hv hgi
  have h2 := bounded_test_error (Lp.aestronglyMeasurable b) hb hv hgi
  calc
    _ ≤ dist (∫ x, f n x*v x ∂μ) (∫ x, f n x*g x ∂μ) +
        dist (∫ x, f n x*g x ∂μ) (∫ x, b x*g x ∂μ) +
        dist (∫ x, b x*g x ∂μ) (∫ x, b x*v x ∂μ) := by
      exact dist_triangle4 _ _ _ _
    _ < ε := by rw [dist_comm (∫ x, b x*g x ∂μ)]; linarith [hN n hn]
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma trace_realization {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    ∃ y : ℕ → ℂ, ∃ r : ℕ → ℝ, (∀ n, TypicalSampling c (y n) (r n)) ∧
      Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 1) ∧
      Tendsto (fun n => sampleCode c hc (y n) (r n)) atTop (𝓝 b) := by
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp hb
  simp only [nhds_prod_eq] at ht
  refine ⟨fun n => (p n).1,fun n => (p n).2.1,fun n => (hp n).1,ht.fst,ht.snd.fst,?_⟩
  simpa only [show (fun n => (p n).2.2) = (fun n => sampleCode c hc (p n).1 (p n).2.1) from
    funext fun n => (hp n).2] using ht.snd.snd
lemma trace_of_realization {x : ℂ} {b : TraceVector k} {y : ℕ → ℂ} {r : ℕ → ℝ}
    (htr : ∀ n, TypicalSampling c (y n) (r n)) (hy : Tendsto y atTop (𝓝 x))
    (hr : Tendsto r atTop (𝓝 1))
    (hb : Tendsto (fun n => sampleCode c hc (y n) (r n)) atTop (𝓝 b)) : IsTrace c hc x b := by
  exact mem_closure_of_tendsto (hy.prodMk_nhds (hr.prodMk_nhds hb))
    (Eventually.of_forall fun n => show (y n,r n,sampleCode c hc (y n) (r n)) ∈ sampleSet c hc from ⟨htr n,rfl⟩)
lemma traceCode_tendsto_iff {I : Type*} {l : Filter I} {f : I → TraceVector k} {b : TraceVector k} :
    Tendsto f l (𝓝 b) ↔ ∀ i v, Tendsto (fun n => ⟪traceValue (f n) i,v⟫) l (𝓝 ⟪traceValue b i,v⟫) := by
  rw [tendsto_pi_nhds]
  exact forall_congr' fun i => WeakBall.tendsto_iff _
lemma trace_bounds {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    (∀ i, 0 ≤ᵐ[angularMeasure] traceValue b i) ∧
    (∀ i, traceValue b i ≤ᵐ[angularMeasure] (fun _ => (1 : ℝ))) ∧
    ∑ i, traceValue b i = oneL2 angularMeasure := by
  obtain ⟨y,r,_,_,_,ht⟩ := trace_realization c hc hb
  have hw := traceCode_tendsto_iff.mp ht
  simp only [traceValue_sampleCode] at hw
  refine ⟨?_,?_,?_⟩
  · intro i
    apply weak_limit_nonneg angularMeasure (hw i)
    intro n
    filter_upwards [sample_ae c hc (y n) (r n) i] with t he
    simpa only [he,Pi.zero_apply] using sampleFn_nonneg c (y n) (r n) i t
  · intro i
    apply weak_limit_le_one angularMeasure (hw i)
    intro n
    filter_upwards [sample_ae c hc (y n) (r n) i] with t he
    simpa only [he] using sampleFn_le_one c (y n) (r n) i t
  · exact weak_limit_sum angularMeasure hw (fun n => sample_sum c hc (y n) (r n))
lemma trace_realization_weakStar {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    ∃ y : ℕ → ℂ, ∃ r : ℕ → ℝ, (∀ n, TypicalSampling c (y n) (r n)) ∧
      Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 1) ∧
      ∀ i (v : Angles → ℝ), Integrable v angularMeasure →
        Tendsto (fun n => ∫ t, sampleFn c (y n) (r n) i t*v t ∂angularMeasure) atTop
          (𝓝 (∫ t, traceValue b i t*v t ∂angularMeasure)) := by
  obtain ⟨y,r,hy,hyt,hrt,hbt⟩ := trace_realization c hc hb
  refine ⟨y,r,hy,hyt,hrt,fun i v hv => ?_⟩
  have hbounds := trace_bounds c hc hb
  have hbn : ∀ᵐ t ∂angularMeasure, ‖traceValue b i t‖ ≤ 1 := by
    filter_upwards [hbounds.1 i,hbounds.2.1 i] with t ht1 ht2
    rwa [Real.norm_eq_abs,abs_of_nonneg ht1]
  have hsn (n : ℕ) : ∀ᵐ t ∂angularMeasure, ‖sample c hc (y n) (r n) i t‖ ≤ 1 := by
    filter_upwards [sample_ae c hc (y n) (r n) i] with t ht
    rw [ht,Real.norm_eq_abs,abs_of_nonneg (sampleFn_nonneg c _ _ _ t)]
    exact sampleFn_le_one c _ _ _ t
  have hw := weak_L2_to_weakStar hsn hbn
    (by simpa only [traceValue_sampleCode] using (traceCode_tendsto_iff.mp hbt) i) hv
  convert hw using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  exact (integral_congr_ae ((sample_ae c hc (y n) (r n) i).mono fun t ht => congrArg (fun a => a*v t) ht)).symm
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Palettes
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma tracePositive_le_palette (x : ℂ) (i : Fin k) (b : Traces c hc x) :
    tracePositive c hc x i b ≤ᵐ[angularMeasure] paletteSet c hc x i :=
  (exists_countable_essential_union angularMeasure (tracePositive c hc x i) (tracePositive_measurable c hc x i)).choose_spec.2 b
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PaletteDensity
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
lemma weak_strong_disjoint {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : ℕ → X → ℝ} {b : X → ℝ} {G : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hF : ∀ n, Measurable (F n)) (hb : Measurable b)
    (hG : ∀ n, Measurable (G n)) (hg : Measurable g)
    (hFb : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (hbb : ∀ᵐ x ∂μ, 0 ≤ b x ∧ b x ≤ 1)
    (hGb : ∀ n p, 0 ≤ G n p ∧ G n p ≤ 1)
    (hgb : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (hw : ∀ v : X → ℝ, Integrable v μ →
      Tendsto (fun n => ∫ x, F n x*v x ∂μ) atTop (𝓝 (∫ x, b x*v x ∂μ)))
    (hs : Tendsto (fun n => ∫ p, ‖G n p-g p‖ ∂μ.prod ν) atTop (𝓝 0))
    (hz : ∀ n, ∀ᵐ p ∂μ.prod ν, F n p.1*G n p=0) :
    ∀ᵐ p ∂μ.prod ν, b p.1*g p=0 := by
  have hgi : Integrable g (μ.prod ν) := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs,abs_of_nonneg (hgb p).1]; exact (hgb p).2)
  have hFi (n : ℕ) : Integrable (fun p : X × Y => F n p.1*g p) (μ.prod ν) := by
    apply Integrable.of_bound (((hF n).comp measurable_fst).mul hg).aestronglyMeasurable 1
    exact Eventually.of_forall fun p => by
      change ‖F n p.1*g p‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hFb n p.1).1 (hgb p).1)]
      exact (mul_le_of_le_one_left (hgb p).1 (hFb n p.1).2).trans (hgb p).2
  have hbi : Integrable (fun p : X × Y => b p.1*g p) (μ.prod ν) := by
    apply Integrable.of_bound ((hb.comp measurable_fst).mul hg).aestronglyMeasurable 1
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbb] with p hp
    change ‖b p.1*g p‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp.1 (hgb p).1)]
    exact (mul_le_of_le_one_left (hgb p).1 hp.2).trans (hgb p).2
  have herr (n : ℕ) : Integrable (fun p => ‖G n p-g p‖) (μ.prod ν) := by
    apply Integrable.of_bound ((hG n).sub hg).norm.aestronglyMeasurable 1
    exact Eventually.of_forall fun p => by
      rw [norm_norm,Real.norm_eq_abs,abs_le]
      change -1 ≤ G n p-g p ∧ G n p-g p ≤ 1
      constructor <;> linarith [(hGb n p).1,(hGb n p).2,(hgb p).1,(hgb p).2]
  have hi0 : Tendsto (fun n => ∫ p, F n p.1*g p ∂μ.prod ν) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun p => mul_nonneg (hFb n p.1).1 (hgb p).1) _ hs
    intro n
    apply integral_mono_ae (hFi n) (herr n)
    filter_upwards [hz n] with p hp
    rw [Real.norm_eq_abs]
    calc
      F n p.1*g p = F n p.1*(g p-G n p) := by rw [mul_sub,hp,sub_zero]
      _ ≤ |g p-G n p| := by
        calc
          _ ≤ F n p.1*|g p-G n p| := mul_le_mul_of_nonneg_left (le_abs_self _) (hFb n p.1).1
          _ ≤ 1*|g p-G n p| := mul_le_mul_of_nonneg_right (hFb n p.1).2 (abs_nonneg _)
          _ = _ := one_mul _
      _ = |G n p-g p| := abs_sub_comm _ _
  let v : X → ℝ := fun x => ∫ y, g (x,y) ∂ν
  have hvi : Integrable v μ := hgi.integral_prod_left
  have hlim := hw v hvi
  have hconvert (f : X → ℝ) (hi : Integrable (fun p : X × Y => f p.1*g p) (μ.prod ν)) :
      (∫ p, f p.1*g p ∂μ.prod ν) = ∫ x, f x*v x ∂μ := by
    rw [integral_prod _ hi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      exact integral_const_mul (f x) (fun y => g (x,y))
  have he0 : (∫ p, b p.1*g p ∂μ.prod ν)=0 := by
    have ht : Tendsto (fun n => ∫ p, F n p.1*g p ∂μ.prod ν) atTop
        (𝓝 (∫ p, b p.1*g p ∂μ.prod ν)) := by
      simpa only [hconvert b hbi,hconvert (F _) (hFi _)] using hlim
    exact tendsto_nhds_unique ht hi0
  exact (integral_eq_zero_iff_of_nonneg_ae
    ((Measure.quasiMeasurePreserving_fst.ae hbb).mono fun p hp => mul_nonneg hp.1 (hgb p).1) hbi).mp he0
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
include hc in
lemma colorIndicator_measurable (i : Fin k) : Measurable (colorIndicator c i) :=
  measurable_one.piecewise (measurableSet_eq_fun hc measurable_const) measurable_zero
lemma colorIndicator_bounds (i : Fin k) (z : ℂ) : 0 ≤ colorIndicator c i z ∧ colorIndicator c i z ≤ 1 := by
  simp only [colorIndicator]; split_ifs <;> norm_num
include hc in
lemma sample_pair_disjoint (hw : WeakColoring k c) {y : ℂ} {r : ℝ}
    (hy : TypicalSampling c y r) (i : Fin k) :
    ∀ᵐ p ∂angularMeasure.prod angularMeasure,
      sampleFn c y r i p.1*colorIndicator c i (angularSum y r p)=0 := by
  have h1 : ∀ᵐ p ∂angularMeasure.prod angularMeasure, Typical c (y+(r : ℂ)*direction p.1) :=
    Measure.quasiMeasurePreserving_fst.ae hy.2
  have h2 := (angularSum_quasiMeasurePreserving y hy.1.ne').ae (ae_density_actual c hc)
  filter_upwards [h1,h2] with p hp1 hp2
  by_cases ha : c (y+(r : ℂ)*direction p.1)=i
  · have hb : c (angularSum y r p) ≠ i := by
      intro hb
      have hdist : ‖(y+(r : ℂ)*direction p.1)-angularSum y r p‖=1 := by
        simp [angularSum]
      apply weak_density_proper c hc hw i hdist
      · simpa only [Typical,ha] using hp1
      · simpa only [hb] using hp2
    simp [sampleFn,colorIndicator,ha,hb]
  · simp [sampleFn,ha]
lemma trace_pair_disjoint (hw : WeakColoring k c) {x : ℂ} {b : TraceVector k}
    (hb : IsTrace c hc x b) (i : Fin k) :
    ∀ᵐ p ∂angularMeasure.prod angularMeasure,
      traceValue b i p.1*colorIndicator c i (angularSum x 1 p)=0 := by
  obtain ⟨y,r,ht,hy,hr,hweak⟩ := trace_realization_weakStar c hc hb
  have hbnd := trace_bounds c hc hb
  apply weak_strong_disjoint (F := fun n => sampleFn c (y n) (r n) i)
    (G := fun n p => colorIndicator c i (angularSum (y n) (r n) p))
    (fun n => sampleFn_measurable c hc (y n) (r n) i) (Lp.stronglyMeasurable _).measurable
    (fun n => (colorIndicator_measurable c hc i).comp (angularSum_measurable _ _))
    ((colorIndicator_measurable c hc i).comp (angularSum_measurable _ _))
    (fun n t => ⟨sampleFn_nonneg c _ _ _ t,sampleFn_le_one c _ _ _ t⟩)
    (Eventually.and (hbnd.1 i) (hbnd.2.1 i))
    (fun n p => colorIndicator_bounds c i _) (fun p => colorIndicator_bounds c i _)
    (hweak i) (angularSum_tendsto_L1 hr hy (colorIndicator_measurable c hc i) (colorIndicator_bounds c i))
    (fun n => sample_pair_disjoint c hc hw (ht n) i)
lemma palette_first_exclusion (hw : WeakColoring k c) (x : ℂ) (i : Fin k) :
    ∀ᵐ p ∂angularMeasure.prod angularMeasure,
      p.1 ∈ paletteSet c hc x i → c (angularSum x 1 p) ≠ i := by
  have hall : ∀ᵐ p ∂angularMeasure.prod angularMeasure, ∀ b ∈ paletteGenerators c hc x i,
      traceValue b.1 i p.1*colorIndicator c i (angularSum x 1 p)=0 :=
    (ae_ball_iff (paletteGenerators_countable c hc x i)).mpr
      (fun b _ => trace_pair_disjoint c hc hw b.2 i)
  filter_upwards [hall] with p hp
  intro hm he
  obtain ⟨b,hb,hpos⟩ := Set.mem_iUnion₂.mp hm
  have hzero := hp b hb
  have hval : colorIndicator c i (angularSum x 1 p)=1 := by simp [colorIndicator,he]
  rw [hval,mul_one] at hzero
  exact (show 0 < traceValue b.1 i p.1 from hpos).ne' hzero
end EuclideanFiveColor

end

noncomputable section
open MeasureTheory Set
namespace EuclideanFiveColor
lemma angleMk_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving ((↑) : ℝ → Angles) volume angularMeasure := by
  have hm : Measurable ((↑) : ℝ → Angles) := (AddCircle.measurePreserving_mk (2*Real.pi) 0).measurable
  refine ⟨hm,Measure.AbsolutelyContinuous.mk (fun A hA hz => ?_)⟩
  rw [Measure.map_apply hm hA]
  have hzv : (volume : Measure Angles) A=0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,Measure.smul_apply]
    change ENNReal.ofReal (2*Real.pi) * angularMeasure A=0
    rw [hz,mul_zero]
  have hh (n : ℤ) : volume (((↑) : ℝ → Angles) ⁻¹' A ∩
      Ioc (n • (2*Real.pi)) ((n+1) • (2*Real.pi)))=0 := by
    have h := (AddCircle.measurePreserving_mk (2*Real.pi) (n • (2*Real.pi))).quasiMeasurePreserving.preimage_null hzv
    rw [Measure.restrict_apply' measurableSet_Ioc] at h
    simpa only [add_zsmul,one_zsmul] using h
  have hcov := iUnion_Ioc_zsmul (by positivity : 0 < 2*Real.pi)
  have he : ((↑) : ℝ → Angles) ⁻¹' A = ⋃ n : ℤ,
      ((↑) : ℝ → Angles) ⁻¹' A ∩ Ioc (n • (2*Real.pi)) ((n+1) • (2*Real.pi)) := by
    rw [← inter_iUnion,hcov,inter_univ]
  rw [he]
  exact measure_iUnion_null hh
lemma anglePair_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ => ((p.1 : Angles),(p.2 : Angles)))
      volume (angularMeasure.prod angularMeasure) := by
  exact QuasiMeasurePreserving.prodMap angleMk_quasiMeasurePreserving
    angleMk_quasiMeasurePreserving
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma volume_image_bound {F : ℝ × ℝ → ℝ × ℝ} {s : Set (ℝ × ℝ)} {K : ℝ≥0}
    (hF : LipschitzWith K (s.domRestrict F)) (A : Set (ℝ × ℝ)) (hA : A ⊆ s) :
    volume (F '' A) ≤ (K : ENNReal)^2 * volume A := by
  let B : Set s := Subtype.val ⁻¹' A
  have he1 : (s.domRestrict F) '' B = F '' A := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩; exact ⟨z.1,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩; exact ⟨⟨z,hA hz⟩,hz,rfl⟩
  have he2 : Subtype.val '' B = A := by
    ext z
    exact ⟨fun ⟨q,hq,he⟩ => he ▸ hq,fun hz => ⟨⟨z,hA hz⟩,hz,rfl⟩⟩
  have hi := (isometry_subtype_coe : Isometry (Subtype.val : s → ℝ × ℝ)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ)≤2)) B
  have ha := hF.hausdorffMeasure_image_le (by norm_num : (0 : ℝ)≤2) B
  rw [he1,hausdorffMeasure_prod_real,ENNReal.rpow_two] at ha
  rw [he2,hausdorffMeasure_prod_real] at hi
  rwa [← hi] at ha
lemma flatDensityZero_prod {D : Set ℝ} {t u : ℝ} (hD : LineDensityZero D t) :
    FlatDensityZero (D ×ˢ univ) (t,u) := by
  have h := hD.const_mul 2
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp : 0 < r := hr
  rw [← closedBall_prod_same,prod_inter_prod,univ_inter,Measure.volume_eq_prod]
  simp only [Measure.real,Measure.prod_prod,ENNReal.toReal_mul,Real.volume_closedBall,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*r)]
  change 2*(volume.real (D ∩ Metric.closedBall t r)/r) =
    volume.real (D ∩ Metric.closedBall t r)*(2*r)/r^2
  field_simp [hp.ne']
lemma tendsto_pos_mul_nhdsWithin {a : ℝ} (ha : 0<a) :
    Tendsto (fun r : ℝ => a*r) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0)))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos ha hr
lemma FlatDensityZero.image {D s : Set (ℝ × ℝ)} {p : ℝ × ℝ} {F : ℝ × ℝ → ℝ × ℝ}
    {K L : ℝ≥0} (hD : FlatDensityZero D p) (hps : p ∈ s)
    (hF : LipschitzWith K (s.domRestrict F)) (hA : AntilipschitzWith L (s.domRestrict F))
    (hL : 0 < L) : FlatDensityZero (F '' (D ∩ s)) (F p) := by
  have h := (hD.comp (tendsto_pos_mul_nhdsWithin (show 0 < (L : ℝ) from hL))).const_mul
    ((K : ℝ)^2*(L : ℝ)^2)
  simp only [mul_zero] at h
  apply squeeze_zero' (Eventually.of_forall fun r => div_nonneg measureReal_nonneg (sq_nonneg r)) _ h
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp : 0 < r := hr
  let E : Set (ℝ × ℝ) := D ∩ s ∩ Metric.closedBall p ((L : ℝ)*r)
  have he : F '' (D ∩ s) ∩ Metric.closedBall (F p) r ⊆ F '' E := by
    rintro z ⟨⟨q,hq,rfl⟩,hz⟩
    refine ⟨q,⟨hq,?_⟩,rfl⟩
    exact (hA.le_mul_dist ⟨q,hq.2⟩ ⟨p,hps⟩).trans
      (mul_le_mul_of_nonneg_left hz L.2)
  have hm := (measure_mono he).trans (volume_image_bound hF E (fun q hq => hq.1.2))
  have hsub : E ⊆ D ∩ Metric.closedBall p ((L : ℝ)*r) := fun q hq => ⟨hq.1.1,hq.2⟩
  have hfin : volume (D ∩ Metric.closedBall p ((L : ℝ)*r)) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall _ _).measure_ne_top (measure_mono inter_subset_right)
  have hm' := hm.trans (mul_le_mul (le_refl _) (measure_mono hsub) bot_le bot_le)
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by finiteness) hfin) hm'
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.coe_toReal] at hreal
  calc
    _ ≤ (K : ℝ)^2*volume.real (D ∩ Metric.closedBall p ((L : ℝ)*r))/r^2 :=
      div_le_div_of_nonneg_right hreal (sq_nonneg r)
    _ = _ := by
      change _ = ((K : ℝ)^2*(L : ℝ)^2)*
        (volume.real (D ∩ Metric.closedBall p ((L : ℝ)*r))/((L : ℝ)*r)^2)
      have hLr : (L : ℝ) ≠ 0 := ne_of_gt hL
      field_simp [hp.ne',hLr]
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma FlatDensityZero.of_locally_le {A B s : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hb : FlatDensityZero B p) (hs : s ∈ 𝓝 p) (hAB : (A ∩ s : Set (ℝ × ℝ)) ≤ᵐ[volume] B) :
    FlatDensityZero A p := by
  obtain ⟨δ,hδ,hsδ⟩ := Metric.mem_nhds_iff.mp hs
  apply squeeze_zero' (Eventually.of_forall fun r => div_nonneg measureReal_nonneg (sq_nonneg r)) _ hb
  filter_upwards [(eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hr
  apply div_le_div_of_nonneg_right _ (sq_nonneg r)
  apply ENNReal.toReal_mono
  · exact ne_top_of_le_ne_top (isCompact_closedBall p r).measure_ne_top (measure_mono inter_subset_right)
  · apply measure_mono_ae
    filter_upwards [hAB] with q hq
    intro hqa
    exact ⟨hq ⟨hqa.1,hsδ (Metric.closedBall_subset_ball hr hqa.2)⟩,hqa.2⟩
lemma FlatDensityZero.transport {A D s : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    {F : ℝ × ℝ → ℝ × ℝ} {K L : ℝ≥0} (hD : FlatDensityZero D p)
    (hps : p ∈ s) (hs : F '' s ∈ 𝓝 (F p))
    (hF : LipschitzWith K (s.domRestrict F)) (hA : AntilipschitzWith L (s.domRestrict F))
    (hL : 0 < L) (hAD : (F ⁻¹' A ∩ s : Set (ℝ × ℝ)) ≤ᵐ[volume] D) : FlatDensityZero A (F p) := by
  let N := (F ⁻¹' A ∩ s) \ D
  have hN : volume N=0 := measure_eq_zero_iff_ae_notMem.mpr (hAD.mono fun q hq h => h.2 (hq h.1))
  have himg : volume (F '' N)=0 := by
    apply le_antisymm _ (zero_le : (0 : ENNReal) ≤ volume (F '' N))
    simpa only [hN,mul_zero] using volume_image_bound hF N (fun q hq => hq.1.2)
  apply (hD.image hps hF hA hL).of_locally_le hs
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp himg] with q hq
  rintro ⟨hqa,⟨t,ht,rfl⟩⟩
  by_cases hd : t ∈ D
  · exact ⟨t,⟨hd,ht⟩,rfl⟩
  · exact (hq ⟨t,⟨⟨hqa,ht⟩,hd⟩,rfl⟩).elim
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma circleSum_one_lipschitz : LipschitzWith 2 (circleSum 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have h₁ := realDirection_lipschitz.dist_le_mul a.1 b.1
  have h₂ := realDirection_lipschitz.dist_le_mul a.2 b.2
  have h := dist_add_add_le (Real.cos a.1,Real.sin a.1) (Real.cos a.2,Real.sin a.2)
    (Real.cos b.1,Real.sin b.1) (Real.cos b.2,Real.sin b.2)
  have he (p : RealPlane) : circleSum 1 p =
      (Real.cos p.1,Real.sin p.1)+(Real.cos p.2,Real.sin p.2) := by simp [circleSum]
  rw [he a,he b]
  norm_num only [NNReal.coe_ofNat,NNReal.coe_one,one_mul] at *
  have ha : dist a.1 b.1 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hb : dist a.2 b.2 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_right _ _
  linarith
lemma circleSum_densityZero {D : Set ℝ} {A : Set RealPlane} {t u : ℝ} (x : RealPlane)
    (hD : LineDensityZero D t) (hu : Real.sin (u-t) ≠ 0)
    (hAD : ∀ᵐ q : RealPlane ∂volume, x+circleSum 1 q ∈ A → q.1 ∈ D) :
    FlatDensityZero A (x+circleSum 1 (t,u)) := by
  let F : RealPlane → RealPlane := fun q => x+circleSum 1 q
  have hreg : (1 : ℝ)*Real.sin (u-t) ≠ 0 := by simpa only [one_mul] using hu
  obtain ⟨s,hso,hps,K,hK⟩ := circleSum_local_antilipschitz (r := 1) (p := (t,u)) hreg
  have ha : AntilipschitzWith (K+1) (s.domRestrict F) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro a b
    have h := hK.le_mul_dist a b
    simp only [domRestrict] at h
    simp only [domRestrict,F,dist_add_left,NNReal.coe_add,NNReal.coe_one]
    nlinarith [dist_nonneg (x := circleSum 1 a.1) (y := circleSum 1 b.1)]
  let L := circleSumDerivEquiv (r := 1) (p := (t,u)) hreg
  have hd : HasStrictFDerivAt F (L : RealPlane →L[ℝ] RealPlane) (t,u) :=
    (circleSum_strict 1 (t,u)).const_add x
  have him : F '' s ∈ 𝓝 (F (t,u)) := by
    rw [← hd.map_nhds_eq_of_equiv]
    exact image_mem_map (hso.mem_nhds hps)
  have hl : LipschitzWith 2 F := LipschitzWith.of_dist_le_mul fun a b => by
    simpa only [F,dist_add_left] using circleSum_one_lipschitz.dist_le_mul a b
  apply (flatDensityZero_prod hD).transport hps him
    (show LipschitzWith 2 (s.domRestrict F) from fun a b => hl a.1 b.1) ha (by positivity)
  filter_upwards [hAD] with q hq
  rintro ⟨hm,_⟩
  exact ⟨hq hm,mem_univ _⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma complex_ball_flat_ball {z w : ℂ} {r : ℝ} (h : w ∈ Metric.closedBall z r) :
    Complex.equivRealProdCLM w ∈ Metric.closedBall (Complex.equivRealProdCLM z) r := by
  rw [Metric.mem_closedBall,dist_eq_norm] at h ⊢
  change max ‖w.re-z.re‖ ‖w.im-z.im‖ ≤ r
  simpa only [Real.norm_eq_abs,Complex.sub_re,Complex.sub_im] using
    max_le ((Complex.abs_re_le_norm (w-z)).trans h) ((Complex.abs_im_le_norm (w-z)).trans h)
lemma flat_to_complex_densityZero {A : Set ℂ} {z : ℂ}
    (h : FlatDensityZero (Complex.equivRealProdCLM.symm ⁻¹' A) (Complex.equivRealProdCLM z)) :
    Tendsto (fun r : ℝ => volume (A ∩ Metric.closedBall z r)/volume (Metric.closedBall z r))
      (𝓝[>] 0) (𝓝 (0 : ENNReal)) := by
  have ht := h.const_mul (Real.pi)⁻¹
  simp only [mul_zero] at ht
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  simp only [ENNReal.ofReal_zero] at he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp : 0 < r := hr
  let B := Complex.equivRealProdCLM.symm ⁻¹' A ∩ Metric.closedBall (Complex.equivRealProdCLM z) r
  have hm : volume (A ∩ Metric.closedBall z r) ≤ (volume : Measure (ℝ × ℝ)) B := by
    apply (measure_mono (t := Complex.equivRealProdCLM ⁻¹' B) ?_).trans
      (Complex.volume_preserving_equiv_real_prod.measure_preimage_le B)
    intro w hw
    exact ⟨by simpa only [Set.mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hw.1,complex_ball_flat_ball hw.2⟩
  have hfin : (volume : Measure (ℝ × ℝ)) B ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall _ _).measure_ne_top (measure_mono inter_subset_right)
  have hfinA : volume (A ∩ Metric.closedBall z r) ≠ ⊤ := ne_top_of_le_ne_top (isCompact_closedBall z r).measure_ne_top
    (measure_mono (s := A ∩ Metric.closedBall z r) inter_subset_right)
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top hfinA
    (Metric.measure_closedBall_pos volume z hp).ne') ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_div,Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hp.le,ENNReal.coe_toReal,NNReal.coe_real_pi,
    ENNReal.toReal_ofReal (by positivity)]
  calc
    _ ≤ volume.real B/(r^2*Real.pi) := div_le_div_of_nonneg_right (ENNReal.toReal_mono hfin hm) (by positivity)
    _ = _ := by dsimp [B]; ring
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma ae_lineDensityZero_compl {D : Set ℝ} (hD : MeasurableSet D) :
    ∀ᵐ t : ℝ ∂volume, t ∈ D → LineDensityZero Dᶜ t := by
  have hh := Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hD.compl
  filter_upwards [hh] with t ht htd
  rw [Set.indicator_of_notMem (show t ∉ Dᶜ from by simpa only [mem_compl_iff,not_not] using htd)] at ht
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp ht
  simp only [ENNReal.toReal_zero,Function.comp_def,ENNReal.toReal_div] at hreal
  have h := hreal.const_mul 2
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp : 0 < r := hr
  rw [Real.volume_closedBall,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*r)]
  change 2*(volume.real (Dᶜ ∩ Metric.closedBall t r)/(2*r)) = _
  field_simp
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma liftPalette_measurable (x : ℂ) (i : Fin k) : MeasurableSet (liftPalette c hc x i) :=
  (paletteSet_measurable c hc x i).preimage angleMk_quasiMeasurePreserving.measurable
lemma palette_spatial_densityZero (hw : WeakColoring k c) {x : ℂ} {i : Fin k} {t u : ℝ}
    (ht : LineDensityZero (liftPalette c hc x i)ᶜ t) (hu : Real.sin (u-t) ≠ 0) :
    Tendsto (fun r : ℝ => volume ({z | c z=i} ∩ Metric.closedBall (angularSum x 1 (angleChart (t,u))) r)/
      volume (Metric.closedBall (angularSum x 1 (angleChart (t,u))) r))
        (𝓝[>] 0) (𝓝 (0 : ENNReal)) := by
  apply flat_to_complex_densityZero
  have he := anglePair_quasiMeasurePreserving.ae (palette_first_exclusion c hc hw x i)
  have hAD : ∀ᵐ q : RealPlane ∂volume, Complex.equivRealProdCLM x+circleSum 1 q ∈
      Complex.equivRealProdCLM.symm ⁻¹' {z | c z=i} → q.1 ∈ (liftPalette c hc x i)ᶜ := by
    filter_upwards [he] with q hq hm hd
    apply hq hd
    change c (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM x+circleSum 1 q))=i at hm
    change c (angularSum x 1 (angleChart q))=i
    rwa [angularSum_chart]
  have hb := circleSum_densityZero (Complex.equivRealProdCLM x) ht hu hAD
  rwa [← circleSum_chart x 1 (t,u)] at hb
lemma palette_spatial_not_densityOne (hw : WeakColoring k c) {x : ℂ} {i : Fin k} {t u : ℝ}
    (ht : LineDensityZero (liftPalette c hc x i)ᶜ t) (hu : Real.sin (u-t) ≠ 0) :
    ¬ DensityOne {z | c z=i} (angularSum x 1 (angleChart (t,u))) := by
  intro hd
  exact zero_ne_one (tendsto_nhds_unique (palette_spatial_densityZero c hc hw ht hu) hd)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_sample_branch_exclusion (hw : WeakColoring k c) {x y : ℂ} {r : ℝ}
    (hy : TypicalSampling c y r) (i : Fin k) {I : Set ℝ} (hI : MeasurableSet I) {s t : ℝ → ℝ}
    (hq : Measure.QuasiMeasurePreserving s (volume.restrict I) volume)
    (hn : ∀ f ∈ I, Real.sin (t f-s f) ≠ 0)
    (he : ∀ f ∈ I, y+(r : ℂ)*direction (f : Angles)=angularSum x 1 (angleChart (s f,t f))) :
    ∀ᵐ f : ℝ ∂volume.restrict I,
      sampleFn c y r i (f : Angles)*(liftPalette c hc x i).indicator (fun _ => (1 : ℝ)) (s f)=0 := by
  have hd := hq.ae (ae_lineDensityZero_compl (liftPalette_measurable c hc x i))
  have ht := ae_restrict_of_ae (s := I) (angleMk_quasiMeasurePreserving.ae hy.2)
  filter_upwards [hd,ht,ae_restrict_mem hI] with f hfd hft hf
  by_cases hs : s f ∈ liftPalette c hc x i
  · have hzero := palette_spatial_not_densityOne c hc hw (hfd hs) (hn f hf)
    have hi : c (y+(r : ℂ)*direction (f : Angles)) ≠ i := by
      intro hi
      apply hzero
      rw [← he f hf]
      simpa only [Typical,hi] using hft
    simp only [sampleFn,ite_eq_right hi,zero_mul]
  · rw [indicator_of_notMem hs,mul_zero]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PaletteTransport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma angleRep_preserving (a : ℝ) :
    MeasurePreserving (fun t : Angles => (AddCircle.equivIoc (2*Real.pi) a t : ℝ))
      volume (volume.restrict (Ioc a (a+2*Real.pi))) :=
  (measurePreserving_subtype_coe measurableSet_Ioc).comp (AddCircle.measurePreserving_equivIoc _)
lemma weak_lift_Ioc {F : ℕ → Angles → ℝ} {b : Angles → ℝ}
    (hw : ∀ v : Angles → ℝ, Integrable v angularMeasure →
      Tendsto (fun n => ∫ t, F n t*v t ∂angularMeasure) atTop (𝓝 (∫ t, b t*v t ∂angularMeasure)))
    (a : ℝ) (v : ℝ → ℝ) (hv : Integrable v (volume.restrict (Ioc a (a+2*Real.pi)))) :
    Tendsto (fun n => ∫ t in Ioc a (a+2*Real.pi), F n (t : Angles)*v t) atTop
      (𝓝 (∫ t in Ioc a (a+2*Real.pi), b (t : Angles)*v t)) := by
  let V : Angles → ℝ := AddCircle.liftIoc (2*Real.pi) a v
  have hvi : Integrable V (volume : Measure Angles) := (angleRep_preserving a).integrable_comp_of_integrable hv
  have hva : Integrable V angularMeasure := by
    rw [AddCircle.volume_eq_smul_haarAddCircle] at hvi
    exact (integrable_smul_measure (by positivity : ENNReal.ofReal (2*Real.pi) ≠ 0) (ENNReal.ofReal_ne_top)).mp hvi
  have h := (hw V hva).const_mul (2*Real.pi)
  have he (f : Angles → ℝ) : (∫ t in Ioc a (a+2*Real.pi), f (t : Angles)*v t) =
      (2*Real.pi)*(∫ t, f t*V t ∂angularMeasure) := by
    have hpre := AddCircle.integral_preimage (2*Real.pi) a (fun t => f t*V t)
    have hi : (∫ t in Ioc a (a+2*Real.pi), f (t : Angles)*v t) =
        ∫ t in Ioc a (a+2*Real.pi), f (t : Angles)*V (t : Angles) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change f (t : Angles)*v t=f (t : Angles)*V (t : Angles)
      rw [show V (t : Angles)=v t from AddCircle.liftIoc_coe_apply ht]
    rw [hi,hpre,AddCircle.volume_eq_smul_haarAddCircle,integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.pi),smul_eq_mul]
    rfl
  simpa only [← he] using h
lemma weak_restrict {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ} {b : X → ℝ}
    (hw : ∀ v : X → ℝ, Integrable v μ →
      Tendsto (fun n => ∫ t, F n t*v t ∂μ) atTop (𝓝 (∫ t, b t*v t ∂μ)))
    {I : Set X} (hI : MeasurableSet I) :
    ∀ v : X → ℝ, Integrable v (μ.restrict I) →
      Tendsto (fun n => ∫ t, F n t*v t ∂μ.restrict I) atTop
        (𝓝 (∫ t, b t*v t ∂μ.restrict I)) := by
  intro v hv
  have hvi : Integrable (I.indicator v) μ := (integrable_indicator_iff hI).mpr hv
  have h := hw (I.indicator v) hvi
  have he (f : X → ℝ) : (fun t => f t*I.indicator v t)=I.indicator (fun t => f t*v t) := by
    funext t
    by_cases ht : t ∈ I <;> simp [ht]
  simpa only [he,integral_indicator hI] using h
lemma weak_lift_set {F : ℕ → Angles → ℝ} {b : Angles → ℝ}
    (hw : ∀ v : Angles → ℝ, Integrable v angularMeasure →
      Tendsto (fun n => ∫ t, F n t*v t ∂angularMeasure) atTop (𝓝 (∫ t, b t*v t ∂angularMeasure)))
    {I : Set ℝ} (hI : MeasurableSet I) {a : ℝ} (hIa : I ⊆ Ioc a (a+2*Real.pi)) :
    ∀ v : ℝ → ℝ, Integrable v (volume.restrict I) →
      Tendsto (fun n => ∫ t in I, F n (t : Angles)*v t) atTop
        (𝓝 (∫ t in I, b (t : Angles)*v t)) := by
  have h := weak_restrict (weak_lift_Ioc hw a) hI
  simpa only [Measure.restrict_restrict hI,inter_eq_left.mpr hIa] using h
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
lemma weak_strong_disjoint_single {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {F : ℕ → X → ℝ} {b : X → ℝ} {G : ℕ → X → ℝ} {g : X → ℝ}
    (hF : ∀ n, Measurable (F n)) (hb : Measurable b)
    (hG : ∀ n, Measurable (G n)) (hg : Measurable g)
    (hFb : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (hbb : ∀ᵐ x ∂μ, 0 ≤ b x ∧ b x ≤ 1)
    (hGb : ∀ n p, 0 ≤ G n p ∧ G n p ≤ 1)
    (hgb : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (hw : ∀ v : X → ℝ, Integrable v μ →
      Tendsto (fun n => ∫ x, F n x*v x ∂μ) atTop (𝓝 (∫ x, b x*v x ∂μ)))
    (hs : Tendsto (fun n => ∫ p, ‖G n p-g p‖ ∂μ) atTop (𝓝 0))
    (hz : ∀ n, ∀ᵐ p ∂μ, F n p*G n p=0) :
    ∀ᵐ p ∂μ, b p*g p=0 := by
  have hgi : Integrable g (μ) := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs,abs_of_nonneg (hgb p).1]; exact (hgb p).2)
  have hFi (n : ℕ) : Integrable (fun p : X => F n p*g p) (μ) := by
    apply Integrable.of_bound ((hF n).mul hg).aestronglyMeasurable 1
    exact Eventually.of_forall fun p => by
      change ‖F n p*g p‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hFb n p).1 (hgb p).1)]
      exact (mul_le_of_le_one_left (hgb p).1 (hFb n p).2).trans (hgb p).2
  have hbi : Integrable (fun p : X => b p*g p) (μ) := by
    apply Integrable.of_bound (hb.mul hg).aestronglyMeasurable 1
    filter_upwards [hbb] with p hp
    change ‖b p*g p‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp.1 (hgb p).1)]
    exact (mul_le_of_le_one_left (hgb p).1 hp.2).trans (hgb p).2
  have herr (n : ℕ) : Integrable (fun p => ‖G n p-g p‖) (μ) := by
    apply Integrable.of_bound ((hG n).sub hg).norm.aestronglyMeasurable 1
    exact Eventually.of_forall fun p => by
      rw [norm_norm,Real.norm_eq_abs,abs_le]
      change -1 ≤ G n p-g p ∧ G n p-g p ≤ 1
      constructor <;> linarith [(hGb n p).1,(hGb n p).2,(hgb p).1,(hgb p).2]
  have hi0 : Tendsto (fun n => ∫ p, F n p*g p ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun p => mul_nonneg (hFb n p).1 (hgb p).1) _ hs
    intro n
    apply integral_mono_ae (hFi n) (herr n)
    filter_upwards [hz n] with p hp
    rw [Real.norm_eq_abs]
    calc
      F n p*g p = F n p*(g p-G n p) := by rw [mul_sub,hp,sub_zero]
      _ ≤ |g p-G n p| := by
        calc
          _ ≤ F n p*|g p-G n p| := mul_le_mul_of_nonneg_left (le_abs_self _) (hFb n p).1
          _ ≤ 1*|g p-G n p| := mul_le_mul_of_nonneg_right (hFb n p).2 (abs_nonneg _)
          _ = _ := one_mul _
      _ = |G n p-g p| := abs_sub_comm _ _
  have he0 : (∫ p, b p*g p ∂μ)=0 := tendsto_nhds_unique (hw g hgi) hi0
  exact (integral_eq_zero_iff_of_nonneg_ae
    (hbb.mono fun p hp => mul_nonneg hp.1 (hgb p).1) hbi).mp he0
lemma weak_strong_disjoint_single_eventual {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {F : ℕ → X → ℝ} {b : X → ℝ} {G : ℕ → X → ℝ} {g : X → ℝ}
    (hF : ∀ n, Measurable (F n)) (hb : Measurable b)
    (hG : ∀ n, Measurable (G n)) (hg : Measurable g)
    (hFb : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (hbb : ∀ᵐ x ∂μ, 0 ≤ b x ∧ b x ≤ 1)
    (hGb : ∀ n p, 0 ≤ G n p ∧ G n p ≤ 1)
    (hgb : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (hw : ∀ v : X → ℝ, Integrable v μ →
      Tendsto (fun n => ∫ x, F n x*v x ∂μ) atTop (𝓝 (∫ x, b x*v x ∂μ)))
    (hs : Tendsto (fun n => ∫ p, ‖G n p-g p‖ ∂μ) atTop (𝓝 0))
    (hz : ∀ᶠ n in atTop, ∀ᵐ p ∂μ, F n p*G n p=0) :
    ∀ᵐ p ∂μ, b p*g p=0 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hz
  exact weak_strong_disjoint_single (fun n => hF (n+N)) hb (fun n => hG (n+N)) hg
    (fun n => hFb (n+N)) hbb (fun n => hGb (n+N)) hgb
    (fun v hv => (tendsto_add_atTop_iff_nat N).mpr (hw v hv))
    ((tendsto_add_atTop_iff_nat N).mpr hs) (fun n => hN _ (Nat.le_add_left N n))
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_trace_branch (hw : WeakColoring k c) {x z : ℂ} {t u a : ℝ}
    (h : Real.sin (u-t) ≠ 0) {P : Set CircleParameter} {I : Set ℝ} {K : ℝ≥0}
    (hP : P ∈ 𝓝 (samplingParameter x z 1))
    (hI : MeasurableSet I) (hIa : I ⊆ Ioc a (a+2*Real.pi))
    (hA : ∀ q ∈ P, AntilipschitzWith K (I.domRestrict (fun v => circleEndpoint h (q,v))))
    (hB : ∀ q ∈ P, ∀ v ∈ I, circleTarget (q,v) ∈ (circleInverseHomeo h).target ∧
      Real.sin ((circleInverse h (circleTarget (q,v))).2-(circleInverse h (circleTarget (q,v))).1) ≠ 0 ∧
      circleEndpoint h (q,v) ∈ Metric.closedBall t 1)
    {b : TraceVector k} (hb : IsTrace c hc z b) (i : Fin k) :
    ∀ᵐ f : ℝ ∂volume.restrict I, traceValue b i (f : Angles)*
      (liftPalette c hc x i).indicator (fun _ => (1 : ℝ)) (circleEndpoint h (samplingParameter x z 1,f))=0 := by
  have : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono (hIa.trans Ioc_subset_Icc_self)).trans_lt isCompact_Icc.measure_lt_top))
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall t 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall t 1).measure_lt_top.ne
  have hp : samplingParameter x z 1 ∈ P := mem_of_mem_nhds hP
  obtain ⟨y,r,hy,hyt,hrt,hwt⟩ := trace_realization_weakStar c hc hb
  let p : ℕ → CircleParameter := fun n => samplingParameter x (y n) (r n)
  let p₀ := samplingParameter x z 1
  let T : ℕ → ℝ → ℝ := fun n f => circleEndpoint h (p n,f)
  let S : ℝ → ℝ := fun f => circleEndpoint h (p₀,f)
  have hpt : Tendsto p atTop (𝓝 p₀) := samplingParameter_tendsto hyt hrt
  have hpn : ∀ᶠ n in atTop, p n ∈ P := hpt hP
  have hTm (n : ℕ) : Measurable (T n) :=
    (circleEndpoint_measurable h).comp (measurable_const.prodMk measurable_id)
  have hSm : Measurable S := (circleEndpoint_measurable h).comp (measurable_const.prodMk measurable_id)
  let D := liftPalette c hc x i
  have hDm : MeasurableSet D := liftPalette_measurable c hc x i
  have hDind : Measurable (D.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hDm
  have hs : Tendsto (fun n => ∫ f in I, ‖D.indicator (fun _ => (1 : ℝ)) (T n f)-
      D.indicator (fun _ => (1 : ℝ)) (S f)‖) atTop (𝓝 0) := by
    apply line_indicator_pullback_L1 hTm hSm (isCompact_closedBall t 1) hDm
    · exact hpn.mono fun n hn => hA (p n) hn
    · exact hA p₀ hp
    · exact hpn.mono fun n hn f hf => (hB (p n) hn f hf).2.2
    · exact fun f hf => (hB p₀ hp f hf).2.2
    · filter_upwards [ae_restrict_mem hI] with f hf
      exact ((circleInverse_continuousAt h (hB p₀ hp f hf).1).fst.comp
        circleTarget_continuous.continuousAt).tendsto.comp (hpt.prodMk_nhds tendsto_const_nhds)
  have hz : ∀ᶠ n in atTop, ∀ᵐ f : ℝ ∂volume.restrict I,
      sampleFn c (y n) (r n) i (f : Angles)*D.indicator (fun _ => (1 : ℝ)) (T n f)=0 := by
    filter_upwards [hpn] with n hn
    exact palette_sample_branch_exclusion c hc hw (hy n) i hI
      (line_antilipschitz_qmp (hTm n) (hA (p n) hn))
      (fun f hf => (hB (p n) hn f hf).2.1)
      (fun f hf => circleInverse_sampling h (hB (p n) hn f hf).1)
  have hbb : ∀ᵐ f : ℝ ∂volume.restrict I, 0 ≤ traceValue b i (f : Angles) ∧ traceValue b i (f : Angles) ≤ 1 :=
    ae_restrict_of_ae (angleMk_quasiMeasurePreserving.ae
      (((trace_bounds c hc hb).1 i).and ((trace_bounds c hc hb).2.1 i)))
  have hgi (f : ℝ) : 0 ≤ D.indicator (fun _ => (1 : ℝ)) f ∧ D.indicator (fun _ => (1 : ℝ)) f ≤ 1 := by
    by_cases hf : f ∈ D <;> simp [hf]
  exact weak_strong_disjoint_single_eventual
    (fun n => (sampleFn_measurable c hc (y n) (r n) i).comp angleMk_quasiMeasurePreserving.measurable)
    ((Lp.stronglyMeasurable (traceValue b i)).measurable.comp angleMk_quasiMeasurePreserving.measurable)
    (fun n => hDind.comp (hTm n)) (hDind.comp hSm)
    (fun n f => ⟨sampleFn_nonneg c _ _ _ _,sampleFn_le_one c _ _ _ _⟩) hbb
    (fun n f => hgi (T n f)) (fun f => hgi (S f))
    (weak_lift_set (hwt i) hI hIa) hs hz
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_branch_local (hw : WeakColoring k c) {x z : ℂ} {t u a : ℝ}
    (h : Real.sin (u-t) ≠ 0)
    (he : circleTarget (samplingParameter x z 1,a)=circleSum 1 (t,u))
    (ha : Real.sin (a-u) ≠ 0) :
    ∃ I : Set ℝ, IsOpen I ∧ a ∈ I ∧ ∀ i : Fin k,
      ∀ᵐ f : ℝ ∂volume.restrict I,
        f ∈ liftPalette c hc z i → circleEndpoint h (samplingParameter x z 1,f) ∉ liftPalette c hc x i := by
  obtain ⟨P,I,hP,hp,hI,haI,hIa,K,hA,hB⟩ := circleEndpoint_good_neighborhood h he rfl ha
  refine ⟨I,hI,haI,fun i => ?_⟩
  have ht : ∀ᵐ f : ℝ ∂volume.restrict I, ∀ b ∈ paletteGenerators c hc z i,
      traceValue b.1 i (f : Angles)*(liftPalette c hc x i).indicator (fun _ => (1 : ℝ))
        (circleEndpoint h (samplingParameter x z 1,f))=0 := by
    apply (ae_ball_iff (paletteGenerators_countable c hc z i)).mpr
    intro b _
    exact palette_trace_branch c hc hw h (hP.mem_nhds hp) hI.measurableSet hIa hA hB b.2 i
  filter_upwards [ht] with f hf hfm hxs
  obtain ⟨b,hb,hbf⟩ := mem_iUnion₂.mp (show (f : Angles) ∈ paletteSet c hc z i from hfm)
  have hz := hf b hb
  rw [indicator_of_mem hxs,mul_one] at hz
  exact (ne_of_gt hbf) hz
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma circleInverse_left {t u : ℝ} (h : Real.sin (u-t) ≠ 0) {q : RealPlane}
    (hq : q ∈ (circleInverseHomeo h).source) : circleInverse h (circleSum 1 q)=q := by
  have ht : circleSum 1 q ∈ (circleInverseHomeo h).target := (circleInverseHomeo h).map_source hq
  rw [circleInverse_eq h ht]
  exact (circleInverseHomeo h).left_inv hq
lemma circleEndpoint_eventuallyEq {x z : ℂ} {a : ℝ} {s t : ℝ → ℝ}
    (hs : ContinuousAt s a) (ht : ContinuousAt t a) (h : Real.sin (t a-s a) ≠ 0)
    (he : ∀ᶠ f in 𝓝 a, circleTarget (samplingParameter x z 1,f)=circleSum 1 (s f,t f)) :
    ∀ᶠ f in 𝓝 a, circleEndpoint h (samplingParameter x z 1,f)=s f := by
  have hp : (s a,t a) ∈ (circleInverseHomeo h).source :=
    (show HasStrictFDerivAt (circleSum 1)
      (circleSumDerivEquiv (r := 1) (p := (s a,t a)) (by simpa only [one_mul] using h) : RealPlane →L[ℝ] RealPlane)
      (s a,t a) from circleSum_strict 1 (s a,t a)).mem_toOpenPartialHomeomorph_source
  have hf := (hs.prodMk ht) ((circleInverseHomeo h).open_source.mem_nhds hp)
  filter_upwards [hf,he] with f hf he
  simp only [circleEndpoint,he,circleInverse_left h hf]
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma ae_of_locally_ae {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) {S : Set X} {P : X → Prop}
    (h : ∀x∈S,∃U : Set X,IsOpen U ∧ x∈U ∧ ∀ᵐy∂μ,y∈U → P y) :
    ∀ᵐx∂μ,x∈S → P x := by
  choose U ho hm ha using fun x : S => h x x.2
  obtain ⟨T,hT,hcov⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover U ho
    (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩,hm ⟨x,hx⟩⟩)
  have hh : ∀ᵐy∂μ,∀x∈T,y∈U x → P y := (ae_ball_iff hT).mpr (fun x _ => ha x)
  filter_upwards [hh] with y hy hs
  obtain ⟨x,hx,hyU⟩ := mem_iUnion₂.mp (hcov hs)
  exact hy x hx hyU
lemma ae_restrict_of_locally_ae {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} {S : Set X} {P : X → Prop}
    (hS : MeasurableSet S)
    (h : ∀x∈S,∃U : Set X,IsOpen U ∧ x∈U ∧ ∀ᵐy∂μ.restrict U,P y) :
    ∀ᵐx∂μ.restrict S,P x := by
  apply (ae_restrict_iff' hS).mpr
  apply ae_of_locally_ae μ
  intro x hx
  obtain ⟨U,hU,hxU,ha⟩ := h x hx
  exact ⟨U,hU,hxU,(ae_restrict_iff' hU.measurableSet).mp ha⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_transport_real (hw : WeakColoring k c) {x z : ℂ} {U : Set ℝ} (hU : IsOpen U)
    {s t : ℝ → ℝ} (hs : ContinuousOn s U) (ht : ContinuousOn t U)
    (hnp : ∀ a ∈ U, Real.sin (t a-s a) ≠ 0)
    (hss : ∀ a ∈ U, Real.sin (a-t a) ≠ 0)
    (he : ∀ a ∈ U, circleTarget (samplingParameter x z 1,a)=circleSum 1 (s a,t a)) (i : Fin k) :
    ∀ᵐ f : ℝ ∂volume.restrict U, f ∈ liftPalette c hc z i → s f ∉ liftPalette c hc x i := by
  apply ae_restrict_of_locally_ae hU.measurableSet
  intro a ha
  obtain ⟨I,hI,haI,hb⟩ := palette_branch_local c hc hw (hnp a ha) (he a ha) (hss a ha)
  have heq := circleEndpoint_eventuallyEq (hs.continuousAt (hU.mem_nhds ha))
    (ht.continuousAt (hU.mem_nhds ha)) (hnp a ha)
    ((show ∀ᶠ f in 𝓝 a, f ∈ U from hU.mem_nhds ha).mono fun f hf => he f hf)
  obtain ⟨V,hV,hVo,haV⟩ := mem_nhds_iff.mp heq
  refine ⟨I ∩ V,hI.inter hVo,⟨haI,haV⟩,?_⟩
  have hb' := ae_restrict_of_ae_restrict_of_subset (s := I ∩ V) (t := I) inter_subset_left (hb i)
  filter_upwards [hb',ae_restrict_mem (hI.inter hVo).measurableSet] with f hf hfI
  rw [hV hfI.2] at hf
  exact hf
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
namespace EuclideanFiveColor
lemma endpoint_fiber_nonzero {x z : ℂ} {a ds dt : ℝ} {s t : ℝ → ℝ}
    (hs : HasDerivAt s ds a) (ht : HasDerivAt t dt a) (hds : ds ≠ 0)
    (hn : Real.sin (t a-s a) ≠ 0)
    (he : ∀ᶠ f in 𝓝 a, circleTarget (samplingParameter x z 1,f)=circleSum 1 (s f,t f)) :
    Real.sin (a-t a) ≠ 0 := by
  have hv : HasDerivAt (fun f => circleTarget (samplingParameter x z 1,f))
      (-Real.sin a,Real.cos a) a := by
    simpa only [circleTarget,samplingParameter,one_smul] using
      ((Real.hasDerivAt_cos a).prodMk (Real.hasDerivAt_sin a)).const_add (Complex.equivRealProdCLM (z-x))
  have hc₁ := (Real.hasDerivAt_cos (s a)).comp a hs
  have hc₂ := (Real.hasDerivAt_cos (t a)).comp a ht
  have hs₁ := (Real.hasDerivAt_sin (s a)).comp a hs
  have hs₂ := (Real.hasDerivAt_sin (t a)).comp a ht
  have hw : HasDerivAt (fun f => circleSum 1 (s f,t f))
      (-Real.sin (s a)*ds+-Real.sin (t a)*dt,Real.cos (s a)*ds+Real.cos (t a)*dt) a := by
    have h := (hc₁.add hc₂).prodMk (hs₁.add hs₂)
    convert h using 1; simp [circleSum,Function.comp_def]
  have hd := (hv.congr_of_eventuallyEq (Filter.EventuallyEq.symm he)).unique hw
  have h₁ := congrArg Prod.fst hd
  have h₂ := congrArg Prod.snd hd
  dsimp only at h₁ h₂
  have hid : Real.sin (a-t a)=ds*Real.sin (s a-t a) := by
    rw [Real.sin_sub,Real.sin_sub]
    linear_combination -(Real.cos (t a))*h₁-(Real.sin (t a))*h₂
  rw [hid]
  apply mul_ne_zero hds
  rw [show s a-t a=-(t a-s a) by ring,Real.sin_neg,neg_ne_zero]
  exact hn
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_smooth_transport (hw : WeakColoring k c) {x z : ℂ} {U : Set ℝ} (hU : IsOpen U)
    {s t ds dt : ℝ → ℝ} (hs : ∀ a ∈ U, HasDerivAt s (ds a) a)
    (ht : ∀ a ∈ U, HasDerivAt t (dt a) a) (hds : ∀ a ∈ U, ds a ≠ 0)
    (hnp : ∀ a ∈ U, Real.sin (t a-s a) ≠ 0)
    (he : ∀ a ∈ U, circleTarget (samplingParameter x z 1,a)=circleSum 1 (s a,t a)) (i : Fin k) :
    ∀ᵐ f : ℝ ∂volume.restrict U, f ∈ liftPalette c hc z i → s f ∉ liftPalette c hc x i := by
  apply palette_transport_real c hc hw hU (fun a ha => (hs a ha).continuousAt.continuousWithinAt)
    (fun a ha => (ht a ha).continuousAt.continuousWithinAt) hnp ?_ he i
  intro a ha
  exact endpoint_fiber_nonzero (hs a ha) (ht a ha) (hds a ha) (hnp a ha)
    ((show ∀ᶠ f in 𝓝 a, f ∈ U from hU.mem_nhds ha).mono fun f hf => he f hf)
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
namespace EuclideanFiveColor
lemma sin_sixty_ne : Real.sin sixty ≠ 0 := by
  rw [sixty,Real.sin_pi_div_three]
  positivity
lemma sin_twice_sixty_ne : Real.sin (2*sixty) ≠ 0 := by
  rw [Real.sin_two_mul,sixty,Real.sin_pi_div_three,Real.cos_pi_div_three]
  positivity
lemma sixty_sum (x : ℂ) (a : ℝ) :
    circleTarget (samplingParameter x x 1,a)=circleSum 1 (a+sixty,a-sixty) := by
  simp only [circleTarget,samplingParameter,sub_self,map_zero,one_smul,zero_add]
  ext <;> simp only [circleSum,one_mul,Real.cos_add,Real.cos_sub,Real.sin_add,Real.sin_sub]
  · rw [sixty,Real.cos_pi_div_three]
    ring
  · rw [sixty,Real.cos_pi_div_three]
    ring
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
namespace EuclideanFiveColor
lemma ae_angular_of_ae_line {p : Angles → Prop} (hp : MeasurableSet {t | p t})
    (h : ∀ᵐ t : ℝ ∂volume, p (t : Angles)) : ∀ᵐ t ∂angularMeasure, p t := by
  have hh : ∀ᵐ t ∂(volume : Measure Angles), p t := by
    rw [← (AddCircle.measurePreserving_mk (2*Real.pi) 0).map_eq]
    exact (ae_map_iff (AddCircle.measurePreserving_mk (2*Real.pi) 0).measurable.aemeasurable hp).mpr
      (ae_restrict_of_ae h)
  rw [AddCircle.volume_eq_smul_haarAddCircle] at hh
  exact (Measure.ae_ennreal_smul_measure_iff (by positivity : ENNReal.ofReal (2*Real.pi) ≠ 0)).mp hh
lemma ae_sin_sub_ne_zero (t : ℝ) : ∀ᵐ a : ℝ ∂volume, Real.sin (a-t) ≠ 0 := by
  have hs : {a : ℝ | Real.sin (a-t)=0} ⊆ range (fun n : ℤ => t+n*Real.pi) := by
    intro a ha
    obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp ha
    exact ⟨n,by linarith⟩
  change volume {a : ℝ | ¬Real.sin (a-t) ≠ 0}=0
  simpa only [not_not] using measure_mono_null hs ((countable_range _).measure_zero volume)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_sixty_real (hw : WeakColoring k c) (x : ℂ) (i : Fin k) :
    ∀ᵐ f : ℝ ∂volume, f ∈ liftPalette c hc x i → f+sixty ∉ liftPalette c hc x i := by
  have h := palette_transport_real c hc hw (x := x) (z := x) isOpen_univ
    (s := fun a => a+sixty) (t := fun a => a-sixty)
    (continuous_id.add continuous_const).continuousOn (continuous_id.sub continuous_const).continuousOn
    (fun a _ => by
      rw [show (a-sixty)-(a+sixty)=-(2*sixty) by ring,Real.sin_neg,neg_ne_zero]
      exact sin_twice_sixty_ne)
    (fun a _ => by simpa only [sub_sub_cancel] using sin_sixty_ne)
    (fun a _ => sixty_sum x a) i
  simpa only [Measure.restrict_univ] using h
lemma palette_sixty (hw : WeakColoring k c) (x : ℂ) (i : Fin k) :
    ∀ᵐ f ∂angularMeasure, f ∈ paletteSet c hc x i → f+(sixty : Angles) ∉ paletteSet c hc x i := by
  apply ae_angular_of_ae_line
  · simpa only [imp_iff_not_or,Set.compl_def,Set.union_def,Set.preimage,Function.id_def,Set.mem_ofPred_eq] using (paletteSet_measurable c hc x i).compl.union
      (((paletteSet_measurable c hc x i).preimage (measurable_id.add_const (sixty : Angles))).compl)
  · simpa only [liftPalette,mem_preimage,AddCircle.coe_add] using palette_sixty_real c hc hw x i
lemma palette_sixty_disjoint (hw : WeakColoring k c) (x : ℂ) :
    ∀ᵐ f ∂angularMeasure, Disjoint (palette c hc x f) (palette c hc x (f+(sixty : Angles))) := by
  filter_upwards [ae_all_iff.mpr (fun i => palette_sixty c hc hw x i)] with f hf
  exact Finset.disjoint_left.mpr fun i hi hj => hf i ((mem_palette c hc x f i).mp hi)
    ((mem_palette c hc x (f+(sixty : Angles)) i).mp hj)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BinaryPalettes
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma ae_circle_palette_exclusion {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
    (hw : WeakColoring k c) (x : ℂ) :
    ∀ᵐ t ∂angularMeasure, ∀ᵐ v ∂angularMeasure,
      c (x+direction t+direction v) ∉ palette c hc x t := by
  have hh := Measure.ae_ae_of_ae_prod (ae_all_iff.mpr (fun i => palette_first_exclusion c hc hw x i))
  apply hh.mono
  intro t ht
  apply ht.mono
  intro v hv hmem
  apply hv (c (x+direction t+direction v)) ((mem_palette c hc x t _).mp hmem)
  simp only [angularSum,Complex.ofReal_one,one_mul]
lemma ae_circle_typicalSampling {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (x : ℂ) :
    ∀ᵐ t ∂angularMeasure, TypicalSampling c (x+direction t) 1 := by
  have htyp := Measure.ae_ae_of_ae_prod ((angularSum_quasiMeasurePreserving x (by norm_num : (1:ℝ)≠0)).ae (ae_density_actual c hc))
  apply htyp.mono
  intro t ht
  refine ⟨by norm_num,?_⟩
  simpa only [Typical,angularSum,Complex.ofReal_one,one_mul] using ht
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_States
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma LineDensityZero.mono_ae {A B : Set ℝ} {t : ℝ}
    (hB : LineDensityZero B t) (hAB : A≤ᵐ[volume] B) : LineDensityZero A t := by
  apply squeeze_zero' ?_ ?_ hB
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonneg measureReal_nonneg (le_of_lt hr)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    apply div_le_div_of_nonneg_right _ (le_of_lt hr)
    apply ENNReal.toReal_mono
    · exact ne_top_of_le_ne_top (isCompact_closedBall t r).measure_ne_top (measure_mono inter_subset_right)
    · exact measure_mono_ae (hAB.mono fun _ hz h => ⟨hz h.1,h.2⟩)
lemma DensityZero.union {A B : Set ℂ} {x : ℂ} (hA : DensityZero A x) (hB : DensityZero B x) :
    DensityZero (A∪B) x := by
  have hh := hA.add hB
  rw [add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => zero_le)
  intro r
  dsimp only
  rw [← ENNReal.add_div,union_inter_distrib_right]
  exact ENNReal.div_le_div_right (measure_union_le _ _) _
lemma densityZero_empty (x : ℂ) : DensityZero ∅ x := by
  simp only [DensityZero,empty_inter,measure_empty,ENNReal.zero_div]
  exact tendsto_const_nhds
lemma DensityZero.biUnion_finset {ι : Type*} (J : Finset ι) {A : ι → Set ℂ} {x : ℂ}
    (hA : ∀ i∈J,DensityZero (A i) x) : DensityZero (⋃ i∈J,A i) x := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa using densityZero_empty x
  | @insert i J hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (hA i (Finset.mem_insert_self _ _)).union
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))
lemma DensityZero.compl {A : Set ℂ} {x : ℂ} (hA : MeasurableSet A) (hz : DensityZero A x) :
    DensityOne Aᶜ x := by
  have ht := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1:ENNReal))) hz (Or.inl (by finiteness))
  rw [tsub_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hfin : volume (A∩Metric.closedBall x r)≠⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall x r).measure_ne_top (measure_mono inter_subset_right)
  have hp := (Metric.measure_closedBall_pos volume x hr).ne'
  have he : Aᶜ∩Metric.closedBall x r=Metric.closedBall x r\(A∩Metric.closedBall x r) := by
    ext z; simp; tauto
  rw [he,measure_sdiff inter_subset_right (hA.inter measurableSet_closedBall).nullMeasurableSet hfin,
    ENNReal.sub_div (fun _ _ => hp),ENNReal.div_self hp (isCompact_closedBall x r).measure_ne_top]
variable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
lemma state_densityZero (hw : WeakColoring k c) {x : ℂ} {A : Set ℝ} {J : Finset (Fin k)}
    (hA : RealState hc x A J) {t u : ℝ} (ht : LineDensityZero Aᶜ t)
    (hu : Real.sin (u-t)≠0) {i : Fin k} (hi : i∈J) :
    DensityZero {z | c z=i} (angularSum x 1 (angleChart (t,u))) := by
  apply palette_spatial_densityZero c hc hw _ hu
  apply ht.mono_ae
  filter_upwards [hA.2 i hi] with v hv
  exact mt hv
lemma angularSum_swap (x : ℂ) (t u : ℝ) :
    angularSum x 1 (angleChart (u,t))=angularSum x 1 (angleChart (t,u)) := by
  simp only [angularSum,angleChart,Complex.ofReal_one,one_mul]
  ring
lemma states_densityOne (hw : WeakColoring k c) {x : ℂ} {A B : Set ℝ} {J K : Finset (Fin k)}
    (hA : RealState hc x A J) (hB : RealState hc x B K) {t u : ℝ}
    (ht : LineDensityZero Aᶜ t) (hu : LineDensityZero Bᶜ u) (hne : Real.sin (u-t)≠0) :
    DensityOne {z | c z∉J∪K} (angularSum x 1 (angleChart (t,u))) := by
  have hz : DensityZero (⋃ i∈J∪K, {z | c z=i}) (angularSum x 1 (angleChart (t,u))) := by
    apply DensityZero.biUnion_finset
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact state_densityZero hc hw hA ht hne hi
    · rw [← angularSum_swap x t u]
      apply state_densityZero hc hw hB hu _ hi
      rwa [← neg_sub u t,Real.sin_neg,neg_ne_zero]
  have hm : MeasurableSet (⋃ i∈J∪K, {z | c z=i}) :=
    (J∪K).measurableSet_biUnion fun _ _ => measurableSet_eq_fun hc measurable_const
  convert hz.compl hm using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_compl_iff,mem_iUnion,mem_ofPred_eq]
  aesop
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma varying_pullback_L1 {X Y : Type*} [MeasurableSpace X]
    [TopologicalSpace Y] [NormalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [ν.WeaklyRegular]
    {T : ℕ → X → Y} {S : X → Y} {C : ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (hS : Measurable S)
    (hmT : ∀ᶠ n in atTop, μ.map (T n) ≤ (C : ENNReal) • ν) (hmS : μ.map S ≤ (C : ENNReal) • ν)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => T n x) atTop (𝓝 (S x)))
    {f : Y → ℝ} {g : ℕ → Y → ℝ} (hf : Integrable f ν) (hg : ∀ n, Integrable (g n) ν)
    (hgf : Tendsto (fun n => ∫ y, ‖g n y-f y‖ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖g n (T n x)-f (S x)‖ ∂μ) atTop (𝓝 0) := by
  have hfixed := tendsto_integral_norm_comp_sub_eventual hT hS hmT hmS ht hf
  have hbound : Tendsto (fun n => (C : ℝ)*(∫ y, ‖g n y-f y‖ ∂ν)+
      ∫ x, ‖f (T n x)-f (S x)‖ ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (hgf.const_mul (C : ℝ)).add hfixed
  apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [hmT] with n hn
  have hgT := integrable_comp_of_map_le (hT n) hn (hg n)
  have hfT := integrable_comp_of_map_le (hT n) hn hf
  have hfS := integrable_comp_of_map_le hS hmS hf
  calc
    _ ≤ ∫ x, ‖g n (T n x)-f (T n x)‖+‖f (T n x)-f (S x)‖ ∂μ :=
      integral_mono (hgT.sub hfS).norm ((hgT.sub hfT).norm.add (hfT.sub hfS).norm)
        (fun x => norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ = (∫ x, ‖g n (T n x)-f (T n x)‖ ∂μ)+(∫ x, ‖f (T n x)-f (S x)‖ ∂μ) :=
      integral_add (hgT.sub hfT).norm (hfT.sub hfS).norm
    _ ≤ _ := add_le_add (integral_norm_comp_le (hT n) hn ((hg n).sub hf)) le_rfl
lemma indicator_inter_positive {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {A : Set X} {B D : ℕ → Set X} (hA : MeasurableSet A)
    (hB : ∀ n,MeasurableSet (B n)) (hD : ∀ n,MeasurableSet (D n)) (hp : 0<μ A)
    (hBA : Tendsto (fun n => ∫ x, ‖(B n).indicator (fun _ => (1:ℝ)) x-A.indicator (fun _ => (1:ℝ)) x‖ ∂μ) atTop (𝓝 0))
    (hDA : Tendsto (fun n => ∫ x, ‖(D n).indicator (fun _ => (1:ℝ)) x-A.indicator (fun _ => (1:ℝ)) x‖ ∂μ) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 0<μ (B n∩D n) := by
  have hpos : 0<(μ A).toReal := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  have ht := hBA.add hDA
  rw [add_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hpos)] with n hn
  by_contra hh
  have hz : μ (B n∩D n)=0 := nonpos_iff_eq_zero.mp (le_of_not_gt hh)
  have hiA : Integrable (A.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator hA
  have hiB : Integrable ((B n).indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator (hB n)
  have hiD : Integrable ((D n).indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator (hD n)
  have hi := integral_mono_ae hiA ((hiB.sub hiA).norm.add (hiD.sub hiA).norm) ?_
  · simp only [Pi.add_apply] at hi
    rw [integral_add (hiB.sub hiA).norm (hiD.sub hiA).norm,integral_indicator_const (1:ℝ) hA,smul_eq_mul,mul_one] at hi
    exact (not_lt_of_ge hi) hn
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx
    by_cases ha : x∈A
    · by_cases hb : x∈B n
      · have hd : x∉D n := fun hd => hx ⟨hb,hd⟩
        simp [ha,hb,hd]
      · by_cases hd : x∈D n <;> simp [ha,hb,hd]
    · simp only [Pi.add_apply,Set.indicator_of_notMem ha]
      positivity
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma circleEndpoint_identity_neighborhood {a u : ℝ} (h : Real.sin (u-a)≠0) :
    ∃ I : Set ℝ, IsOpen I ∧ a∈I ∧
      ∀ v∈I, circleTarget (samplingParameter 0 (direction (u : Angles)) 1,v)∈(circleInverseHomeo h).target ∧
        circleEndpoint h (samplingParameter 0 (direction (u : Angles)) 1,v)=v := by
  let V := (circleInverseHomeo h).source
  have ha : (a,u)∈V := (circleSum_strict 1 (a,u)).mem_toOpenPartialHomeomorph_source
  let I := (fun v : ℝ => (v,u)) ⁻¹' V
  refine ⟨I,(circleInverseHomeo h).open_source.preimage (continuous_id.prodMk continuous_const),ha,?_⟩
  intro v hv
  have he : circleTarget (samplingParameter 0 (direction (u : Angles)) 1,v)=circleSum 1 (v,u) := by
    simp [circleTarget,samplingParameter,circleSum,add_comm]
  have hv' : (v,u)∈(circleInverseHomeo h).source := hv
  have ht : circleSum 1 (v,u)∈(circleInverseHomeo h).target := (circleInverseHomeo h).map_source hv'
  refine ⟨he ▸ ht,?_⟩
  rw [circleEndpoint,he,circleInverse_eq h ht]
  exact congrArg Prod.fst ((circleInverseHomeo h).left_inv hv')
lemma near_identity_circle_in {a u : ℝ} (h : Real.sin (u-a)≠0)
    {w : ℕ → ℂ} (hw : Tendsto w atTop (𝓝 (direction (u : Angles))))
    {V : Set ℝ} (hV : IsOpen V) (haV : a∈V) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ ∃ C : ℝ≥0, 1≤C ∧ ∃ T : ℕ → ℝ → ℝ,
      (∀ n,Measurable (T n)) ∧
      (∀ v∈Metric.ball a δ,Tendsto (fun n => T n v) atTop (𝓝 v)) ∧
      (∀ᶠ n in atTop, AntilipschitzWith C ((Metric.ball a δ).domRestrict (T n)) ∧
        MapsTo (T n) (Metric.ball a δ) (Metric.closedBall a 1) ∧
        MapsTo (T n) (Metric.ball a δ) V ∧
        ∀ v∈Metric.ball a δ, ‖w n+direction (v : Angles)-direction (T n v : Angles)‖=1) := by
  let p := samplingParameter 0 (direction (u : Angles)) 1
  have he : circleTarget (p,a)=circleSum 1 (a,u) := by
    simp [p,circleTarget,samplingParameter,circleSum,add_comm]
  have ha : Real.sin (a-u)≠0 := by rwa [← neg_sub u a,Real.sin_neg,neg_ne_zero]
  obtain ⟨P,I,hP,hp,hI,hai,hIp,K,hK,hctrl⟩ := circleEndpoint_good_neighborhood h he rfl ha
  obtain ⟨J,hJ,haj,hid⟩ := circleEndpoint_identity_neighborhood h
  have hcv : ∀ᶠ q in 𝓝 (p,a),circleEndpoint h q∈V := by
    apply (circleEndpoint_strict h he).continuousAt
    simpa only [circleEndpoint,he,circleInverse_at] using hV.mem_nhds haV
  obtain ⟨P₁,hP₁,I₁,hI₁,hsubV⟩ := mem_nhds_prod_iff.mp hcv
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((hI.inter hJ).mem_nhds ⟨hai,haj⟩) hI₁)
  let ε := min δ 1
  have hε : 0<ε := lt_min hδ (by norm_num)
  let T : ℕ → ℝ → ℝ := fun n v => circleEndpoint h (samplingParameter 0 (w n) 1,v)
  have hparam := samplingParameter_tendsto (x := 0) hw tendsto_const_nhds
  have hT (n : ℕ) : Measurable (T n) :=
    (circleEndpoint_measurable h).comp (measurable_const.prodMk measurable_id)
  refine ⟨ε,hε,min_le_right _ _,max K 1,le_max_right _ _,T,hT,?_,?_⟩
  · intro v hv
    have hvI := (hsub ((Metric.ball_subset_ball (min_le_left δ 1)) hv)).1
    have hh := (circleInverse_continuousAt h (hid v hvI.2).1).fst.tendsto.comp
      (circleTarget_continuous.continuousAt.tendsto.comp (hparam.prodMk_nhds tendsto_const_nhds))
    have hid' := (hid v hvI.2).2
    change Tendsto (fun n => T n v) atTop (𝓝 (circleEndpoint h (p,v))) at hh
    simpa only [p,hid'] using hh
  · filter_upwards [hparam.eventually (hP.mem_nhds hp),hparam.eventually hP₁] with n hn hnV
    refine ⟨?_,?_,?_,?_⟩
    · apply AntilipschitzWith.of_le_mul_dist
      intro v z
      have hv := (hsub ((Metric.ball_subset_ball (min_le_left δ 1)) v.2)).1.1
      have hz := (hsub ((Metric.ball_subset_ball (min_le_left δ 1)) z.2)).1.1
      exact ((hK _ hn).le_mul_dist ⟨v,hv⟩ ⟨z,hz⟩).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K 1) dist_nonneg)
    · intro v hv
      exact (hctrl _ hn v (hsub ((Metric.ball_subset_ball (min_le_left δ 1)) hv)).1.1).2.2
    · intro v hv
      exact hsubV ⟨hnV,(hsub ((Metric.ball_subset_ball (min_le_left δ 1)) hv)).2⟩
    · intro v hv
      have ht := (hctrl _ hn v (hsub ((Metric.ball_subset_ball (min_le_left δ 1)) hv)).1.1).1
      have hh := circleInverse_sampling h ht
      simp only [Complex.ofReal_one,one_mul,angularSum,zero_add,angleChart] at hh
      change w n+direction (v : Angles)=direction (T n v : Angles)+
        direction (((circleInverse h (circleTarget (samplingParameter 0 (w n) 1,v))).2) : Angles) at hh
      rw [hh,add_sub_cancel_left]
      exact Circle.norm_coe _
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma nonparallel_neighborhood {a b : ℝ} (h : Real.sin (b-a)≠0)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 b)) :
    ∃ V : Set ℝ, IsOpen V ∧ a∈V ∧ ∀ᶠ n in atTop, ∀ v∈V, Real.sin (s n-v)≠0 := by
  have hf : Continuous (fun q : ℝ×ℝ => Real.sin (q.2-q.1)) :=
    Real.continuous_sin.comp (continuous_snd.sub continuous_fst)
  have ho : IsOpen {q : ℝ×ℝ | Real.sin (q.2-q.1)≠0} :=
    isOpen_compl_singleton.preimage hf
  have hh : {q : ℝ×ℝ | Real.sin (q.2-q.1)≠0}∈𝓝 (a,b) := ho.mem_nhds h
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨Metric.ball a ε,Metric.isOpen_ball,Metric.mem_ball_self hε,?_⟩
  filter_upwards [hs.eventually (Metric.ball_mem_nhds b hε)] with n hn
  intro v hv
  exact @hsub (v,s n) (show max (dist v a) (dist (s n) b)<ε from max_lt hv hn)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma strict_state_sequence_local_false {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c)
    (x : ℕ → ℂ) (J K : Finset (Fin k)) (X : Fin k)
    (hlabels : ∀i, i∉J∪K ↔ i=X)
    (A B : ℕ → Set ℝ) (D : Set ℝ) (hD : MeasurableSet D)
    (hA : ∀n,RealState hc (x n) (A n) J) (hB : ∀n,RealState hc (x n) (B n) K)
    (b d : ℕ → ℝ) (b₀ d₀ a u : ℝ)
    (hb : Tendsto b atTop (𝓝 b₀)) (hd : Tendsto d atTop (𝓝 d₀))
    (hbden : ∀n,LineDensityZero (B n)ᶜ (b n)) (hdden : ∀n,LineDensityZero (B n)ᶜ (d n))
    (hu : direction (u : Angles)=direction (b₀ : Angles)-direction (d₀ : Angles))
    (hab : Real.sin (b₀-a)≠0) (had : Real.sin (d₀-a)≠0) (hau : Real.sin (u-a)≠0)
    (hpos : ∀ε>0,0<volume (D∩Metric.ball a ε))
    (hL1 : ∀ E : Set ℝ, IsCompact E →
      Tendsto (fun n => ∫ v in E, ‖(A n).indicator (fun _ => (1:ℝ)) v-D.indicator (fun _ => (1:ℝ)) v‖)
        atTop (𝓝 0)) : False := by
  let w : ℕ → ℂ := fun n => direction (b n : Angles)-direction (d n : Angles)
  have hdir : Continuous (fun v : ℝ => direction (v : Angles)) := direction_continuous.comp (AddCircle.continuous_mk' (2*Real.pi))
  have hwt : Tendsto w atTop (𝓝 (direction (u : Angles))) := by
    rw [hu]
    exact (hdir.tendsto b₀ |>.comp hb).sub (hdir.tendsto d₀ |>.comp hd)
  obtain ⟨V,hV,haV,hparb⟩ := nonparallel_neighborhood hab hb
  obtain ⟨W,hW,haW,hpard⟩ := nonparallel_neighborhood had hd
  obtain ⟨δ,hδ,hδ1,C,hC,T,hT,hTlim,hctrl⟩ := near_identity_circle_in hau hwt hW haW
  obtain ⟨η,hη,hηV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds haV)
  let ε := min δ η
  have hε : 0<ε := lt_min hδ hη
  let I := Metric.ball a ε
  let E := Metric.closedBall a 1
  have hIE : I⊆E := (Metric.ball_subset_ball ((min_le_left δ η).trans hδ1)).trans Metric.ball_subset_closedBall
  have hIδ : I⊆Metric.ball a δ := Metric.ball_subset_ball (min_le_left δ η)
  have hIV : I⊆V := (Metric.ball_subset_ball (min_le_right δ η)).trans hηV
  let μ := volume.restrict I
  let ν := volume.restrict E
  have hEc : IsCompact E := isCompact_closedBall a 1
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hEc.measure_ne_top
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top hEc.measure_ne_top (measure_mono hIE))
  have : ν.WeaklyRegular := Measure.WeaklyRegular.restrict_of_measure_ne_top hEc.measure_lt_top.ne
  have hS : AntilipschitzWith C (I.domRestrict id) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro v z
    change dist v.1 z.1≤(C:ℝ)*dist v.1 z.1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1:ℝ)≤C by exact_mod_cast hC) (dist_nonneg (x := v.1) (y := z.1))
  have hmS : μ.map id≤(C:ENNReal) •ν := line_map_restrict_volume_le measurable_id hEc.measurableSet hS hIE
  have hmT : ∀ᶠ n in atTop, μ.map (T n)≤(C:ENNReal) •ν := by
    filter_upwards [hctrl] with n hn
    apply line_map_restrict_volume_le (hT n) hEc.measurableSet
      (AntilipschitzWith.of_le_mul_dist fun v z => hn.1.le_mul_dist ⟨v,hIδ v.2⟩ ⟨z,hIδ z.2⟩)
    exact hn.2.1.mono_left hIδ
  have hiD : Integrable (D.indicator (fun _ => (1:ℝ))) ν := (integrable_const _).indicator hD
  have hiA (n : ℕ) : Integrable ((A n).indicator (fun _ => (1:ℝ))) ν := (integrable_const _).indicator (hA n).1
  have hlimT : ∀ᵐ v ∂μ,Tendsto (fun n => T n v) atTop (𝓝 (id v)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with v hv
    exact hTlim v (hIδ hv)
  have hcomp := varying_pullback_L1 hT measurable_id hmT hmS hlimT hiD hiA (hL1 E hEc)
  have hdirect : Tendsto (fun n => ∫ v, ‖(A n).indicator (fun _ => (1:ℝ)) v-D.indicator (fun _ => (1:ℝ)) v‖ ∂μ)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun v => norm_nonneg _) _
      (by simpa only [mul_zero] using (hL1 E hEc).const_mul (C:ℝ))
    exact Eventually.of_forall fun n => integral_norm_comp_le measurable_id hmS ((hiA n).sub hiD)
  have hpre (n : ℕ) : MeasurableSet (T n ⁻¹' A n) := (hA n).1.preimage (hT n)
  have hcompeq (n : ℕ) (v : ℝ) : (T n ⁻¹' A n).indicator (fun _ => (1:ℝ)) v =
      (A n).indicator (fun _ => (1:ℝ)) (T n v) := by
    by_cases hv : T n v∈A n <;> simp [hv]
  have hpositive : ∀ᶠ n in atTop,0<μ (A n∩T n ⁻¹' A n) := by
    apply indicator_inter_positive hD (fun n => (hA n).1) hpre ?_ hdirect
    · simpa only [hcompeq,id_eq] using hcomp
    · simpa only [μ,Measure.restrict_apply hD,I] using hpos ε hε
  obtain ⟨n,hn,hbp,hdp,hp⟩ := (hctrl.and (hparb.and (hpard.and hpositive))).exists
  have hqmp : Measure.QuasiMeasurePreserving (T n) μ volume :=
    line_antilipschitz_qmp (hT n)
      (AntilipschitzWith.of_le_mul_dist fun v z => hn.1.le_mul_dist ⟨v,hIδ v.2⟩ ⟨z,hIδ z.2⟩)
  have hden := ae_lineDensityZero_compl (hA n).1
  have hgood : ∀ᵐ v ∂μ,v∈I ∧ (v∈A n → LineDensityZero (A n)ᶜ v) ∧
      (T n v∈A n → LineDensityZero (A n)ᶜ (T n v)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae hden,hqmp.ae hden] with v hv hd₁ hd₂
    exact ⟨hv,hd₁,hd₂⟩
  obtain ⟨v,hvA,hvI,hvden,hTvden⟩ := ((frequently_ae_mem_iff.mpr hp.ne').and_eventually hgood).exists
  have h₁ := states_densityOne hc hw (hA n) (hB n) (hvden hvA.1) (hbden n) (hbp v (hIV hvI))
  have h₂ := states_densityOne hc hw (hA n) (hB n) (hTvden hvA.2) (hdden n)
    (hdp (T n v) (hn.2.2.1 (hIδ hvI)))
  have he : {z | c z∉J∪K}={z | c z=X} := by ext z; exact hlabels (c z)
  rw [he] at h₁ h₂
  apply weak_density_proper c hc hw X _ h₁ h₂
  have hdist := hn.2.2.2 v (hIδ hvI)
  convert hdist using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp only [angularSum,angleChart,Complex.ofReal_one,one_mul,w]
  ring
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma positive_state_support_point {D : Set ℝ} (_hD : MeasurableSet D) (hp : 0<volume D)
    (b d u : ℝ) : ∃ a : ℝ, Real.sin (b-a)≠0 ∧ Real.sin (d-a)≠0 ∧ Real.sin (u-a)≠0 ∧
      ∀ ε>0,0<volume (D∩Metric.ball a ε) := by
  have hs : ∀ᵐ a ∂volume.restrict D, a∈(volume.restrict D).support ∧
      Real.sin (a-b)≠0 ∧ Real.sin (a-d)≠0 ∧ Real.sin (a-u)≠0 := by
    filter_upwards [(volume.restrict D).support_mem_ae,
      ae_restrict_of_ae (ae_sin_sub_ne_zero b),ae_restrict_of_ae (ae_sin_sub_ne_zero d),
      ae_restrict_of_ae (ae_sin_sub_ne_zero u)] with a ha hb hd hu
    exact ⟨ha,hb,hd,hu⟩
  obtain ⟨a,_,ha,hb,hd,hu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp.ne' hs
  have hneg (v : ℝ) (hv : Real.sin (a-v)≠0) : Real.sin (v-a)≠0 := by
    rwa [← neg_sub a v,Real.sin_neg,neg_ne_zero]
  refine ⟨a,hneg b hb,hneg d hd,hneg u hu,?_⟩
  intro ε hε
  have hh := (Measure.mem_support_iff_forall a).mp ha (Metric.ball a ε) (Metric.ball_mem_nhds a hε)
  simpa only [Measure.restrict_apply measurableSet_ball,inter_comm] using hh
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma support_density_direction {B : Set ℝ} (hB : MeasurableSet B) {b : ℝ}
    (hb : b∈(volume.restrict B).support) {ε : ℝ} (hε : 0<ε) :
    ∃ t∈B, dist t b<ε ∧ LineDensityZero Bᶜ t := by
  have hp : 0<volume (B∩Metric.ball b ε) := by
    have hh := (Measure.mem_support_iff_forall b).mp hb (Metric.ball b ε) (Metric.ball_mem_nhds b hε)
    simpa only [Measure.restrict_apply measurableSet_ball,inter_comm] using hh
  obtain ⟨t,ht,hd⟩ := ((frequently_ae_mem_iff.mpr hp.ne').and_eventually (ae_lineDensityZero_compl hB)).exists
  exact ⟨t,ht.1,ht.2,hd ht.1⟩
lemma support_density_sequence {B : ℕ → Set ℝ} (hB : ∀n,MeasurableSet (B n))
    {b : ℕ → ℝ} {b₀ : ℝ} (hb : Tendsto b atTop (𝓝 b₀))
    (hs : ∀n,b n∈(volume.restrict (B n)).support) :
    ∃ d : ℕ → ℝ, Tendsto d atTop (𝓝 b₀) ∧ ∀n,LineDensityZero (B n)ᶜ (d n) := by
  have hp (n : ℕ) : 0<(1:ℝ)/(n+1) := by positivity
  choose d _hmem hdist hden using fun n => support_density_direction (hB n) (hs n) (hp n)
  refine ⟨d,?_,hden⟩
  apply hb.congr_dist
  simp only [dist_comm (b _) (d _)]
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
  exact tendsto_one_div_add_atTop_nhds_zero_nat
lemma strict_state_sequence_false {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c)
    (x : ℕ → ℂ) (J K : Finset (Fin k)) (X : Fin k)
    (hlabels : ∀i, i∉J∪K ↔ i=X)
    (A B : ℕ → Set ℝ) (D : Set ℝ) (hD : MeasurableSet D) (hp : 0<volume D)
    (hA : ∀n,RealState hc (x n) (A n) J) (hB : ∀n,RealState hc (x n) (B n) K)
    (b d : ℕ → ℝ) (b₀ d₀ : ℝ)
    (hb : Tendsto b atTop (𝓝 b₀)) (hd : Tendsto d atTop (𝓝 d₀))
    (hbs : ∀n,b n∈(volume.restrict (B n)).support)
    (hds : ∀n,d n∈(volume.restrict (B n)).support)
    (hu : ‖direction (b₀ : Angles)-direction (d₀ : Angles)‖=1)
    (hL1 : ∀ E : Set ℝ, IsCompact E →
      Tendsto (fun n => ∫ v in E, ‖(A n).indicator (fun _ => (1:ℝ)) v-D.indicator (fun _ => (1:ℝ)) v‖)
        atTop (𝓝 0)) : False := by
  obtain ⟨b',hb',hbden⟩ := support_density_sequence (fun n => (hB n).1) hb hbs
  obtain ⟨d',hd',hdden⟩ := support_density_sequence (fun n => (hB n).1) hd hds
  obtain ⟨u,hu⟩ := direction_exists hu
  obtain ⟨u,rfl⟩ := QuotientAddGroup.mk_surjective u
  obtain ⟨a,hab,had,hau,hpos⟩ := positive_state_support_point hD hp b₀ d₀ u
  exact strict_state_sequence_local_false hc hw x J K X hlabels A B D hD hA hB
    b' d' b₀ d₀ a u hb' hd' hbden hdden hu hab had hau hpos hL1
lemma strict_state_no_unit_support {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c)
    {x : ℂ} {J K : Finset (Fin k)} {X : Fin k}
    (hlabels : ∀i, i∉J∪K ↔ i=X)
    {A B : Set ℝ} (hA : RealState hc x A J) (hB : RealState hc x B K)
    (hp : 0<volume A) {b d : ℝ}
    (hb : b∈(volume.restrict B).support) (hd : d∈(volume.restrict B).support) :
    ‖direction (b : Angles)-direction (d : Angles)‖≠1 := by
  intro hu
  apply strict_state_sequence_false hc hw (fun _ => x) J K X hlabels (fun _ => A) (fun _ => B)
    A hA.1 hp (fun _ => hA) (fun _ => hB) (fun _ => b) (fun _ => d) b d tendsto_const_nhds
    tendsto_const_nhds (fun _ => hb) (fun _ => hd) hu
  intro E _
  simp only [sub_self,norm_zero,integral_zero]
  exact tendsto_const_nhds
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BoundaryTrace
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma support_good_sequence {A : Set ℝ} {P : ℝ → Prop} {a : ℝ}
    (ha : a∈(volume.restrict A).support) (hP : ∀ᵐt∂volume,t∈A → P t) :
    ∃t : ℕ → ℝ, Tendsto t atTop (𝓝 a) ∧ ∀n,P (t n) := by
  have hex (n : ℕ) : ∃t,dist t a<1/((n:ℝ)+1) ∧ P t := by
    have hp : 0<volume (Metric.ball a (1/((n:ℝ)+1))∩A) := by
      simpa only [Measure.restrict_apply measurableSet_ball] using
        (Measure.mem_support_iff_forall a).mp ha _ (Metric.ball_mem_nhds a (by positivity))
    obtain ⟨t,ht,hpt⟩ := ((frequently_ae_mem_iff.mpr hp.ne').and_eventually hP).exists
    exact ⟨t,ht.1,hpt ht.2⟩
  choose t hd hpt using hex
  refine ⟨t,?_,hpt⟩
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hd n).le) tendsto_one_div_add_atTop_nhds_zero_nat
lemma state_support_avoiding_trace (hw : WeakColoring k c) {x : ℂ} {A : Set ℝ} {J : Finset (Fin k)}
    (hA : RealState hc x A J) {a : ℝ} (ha : a∈(volume.restrict A).support) :
    ∃b : TraceVector k,IsTrace c hc (x+direction (a : Angles)) b ∧ ∀i∈J,traceValue b i=0 := by
  have he := angleMk_quasiMeasurePreserving.ae (ae_circle_palette_exclusion c hc hw x)
  have ht := angleMk_quasiMeasurePreserving.ae (ae_circle_typicalSampling c hc x)
  have hp : ∀ᵐt : ℝ∂volume,t∈A → TypicalSampling c (x+direction (t : Angles)) 1 ∧
      ∀i∈J,sample c hc (x+direction (t : Angles)) 1 i=0 := by
    filter_upwards [he,ht,ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun hi : i∈J => hA.2 i hi))] with t he ht hJ hta
    refine ⟨ht,?_⟩
    intro i hi
    apply Lp.ext
    filter_upwards [sample_ae c hc (x+direction (t : Angles)) 1 i,he,Lp.coeFn_zero ℝ 2 angularMeasure] with v hv he hz
    rw [hz,hv]
    have hne : c (x+direction (t : Angles)+direction v)≠i := by
      intro hh
      apply he
      rw [hh]
      exact (mem_palette c hc x (t : Angles) i).mpr (hJ i hi hta)
    simp only [sampleFn,Complex.ofReal_one,one_mul,ite_eq_right hne,Pi.zero_apply]
  obtain ⟨t,ht,hp⟩ := support_good_sequence ha hp
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (TraceVector k))).isSeqCompact.subseq_of_frequently_in
    (Eventually.frequently (Eventually.of_forall fun n => Set.mem_univ (sampleCode c hc (x+direction (t n : Angles)) 1)))
  have hlim : Tendsto (fun n => x+direction (t n : Angles)) atTop (𝓝 (x+direction (a : Angles))) :=
    tendsto_const_nhds.add (direction_continuous.continuousAt.tendsto.comp ((AddCircle.continuous_mk' (2*Real.pi)).continuousAt.tendsto.comp ht))
  refine ⟨b,trace_of_realization c hc (fun n => (hp (φ n)).1) (hlim.comp hφ.tendsto_atTop) tendsto_const_nhds hb,?_⟩
  intro i hi
  have hh := traceCode_tendsto_iff.mp hb i (traceValue b i)
  simp only [Function.comp_apply,traceValue_sampleCode,(hp _).2 i hi,inner_zero_left] at hh
  exact inner_self_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hh).symm
lemma avoiding_trace_palette {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b)
    {J : Finset (Fin k)} (hJ : ∀i∈J,traceValue b i=0) :
    ∀ᵐt∂angularMeasure,¬palette c hc x t⊆J := by
  have hs : (fun t => ∑i,traceValue b i t)=ᵐ[angularMeasure](fun _ => (1:ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (traceValue b)
    rw [(trace_bounds c hc hb).2.2] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  have hz (i : Fin k) : ∀ᵐt∂angularMeasure,i∈J → traceValue b i t=0 := by
    by_cases hi : i∈J
    · rw [hJ i hi]
      exact (Lp.coeFn_zero ℝ 2 angularMeasure).mono fun _ hh _ => hh
    · exact Eventually.of_forall fun _ hh => (hi hh).elim
  filter_upwards [hs,ae_all_iff.mpr hz,ae_all_iff.mpr (fun i => tracePositive_le_palette c hc x i ⟨b,hb⟩)] with t hs hz hp hsub
  have hn : ∀i : Fin k,traceValue b i t≤0 := by
    intro i
    by_contra! hpos
    have hm := hsub ((mem_palette c hc x t i).mpr (hp i hpos))
    linarith [hz i hm]
  have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hn i)
  linarith
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Exclusion
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
lemma five_diag_disjoint : ∀i j : Fin 5, Disjoint (fiveDiag i) (fiveDiag j) ↔ fiveAdj i j := by decide
lemma five_adj_four : ∀i j : Fin 5, fiveAdj i j → ∃ X : Fin 5, ∀k, k∉fiveDiag i∪fiveDiag j ↔ k=X := by decide
lemma five_no_common_adj : ∀I : Finset (Fin 5), I.Nonempty → (∀k,∃i∈I,k∉fiveDiag i) →
    ∃i∈I,∃j∈I,fiveAdj i j := by decide
lemma five_forced_label : ∀i j X : Fin 5, fiveAdj i j →
    (∀k,k∉fiveDiag i∪fiveDiag j ↔ k=X) → ∀p : Finset (Fin 5),
    Disjoint p (fiveDiag i) → ¬p⊆fiveDiag j → X∈p := by decide
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FourTransport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma circleSum_one_lipschitz_sumTransport : LipschitzWith 2 (circleSum 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hh (g : ℝ → ℝ) (hg : LipschitzWith 1 g) :
      dist (g p.1+g p.2) (g q.1+g q.2)≤2*max (dist p.1 q.1) (dist p.2 q.2) := by
    have h1 := hg.dist_le_mul p.1 q.1
    have h2 := hg.dist_le_mul p.2 q.2
    norm_num only [NNReal.coe_one,one_mul] at h1 h2
    have h3 := dist_add_add_le (g p.1) (g p.2) (g q.1) (g q.2)
    have h4 := le_max_left (dist p.1 q.1) (dist p.2 q.2)
    have h5 := le_max_right (dist p.1 q.1) (dist p.2 q.2)
    linarith
  simpa only [circleSum,one_mul,Prod.dist_eq,NNReal.coe_ofNat] using
    max_le (hh _ Real.lipschitzWith_cos) (hh _ Real.lipschitzWith_sin)

end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma direction_sixty_unit_real (a : ℝ) :
    ‖direction (a : Angles)-direction ((a+sixty : ℝ) : Angles)‖=1 := by
  have he : direction (a : Angles)=direction ((a+sixty : ℝ) : Angles)+direction ((a-sixty : ℝ) : Angles) := by
    apply Complex.equivRealProdCLM.injective
    simpa only [map_add,direction_realPlane,circleTarget,samplingParameter,sub_self,map_zero,one_smul,zero_add,circleSum,one_mul,Prod.mk_add_mk] using sixty_sum (0:ℂ) a
  rw [he,add_sub_cancel_left,direction_norm]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Accumulation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma palette_eq_measurable (x : ℂ) (p : Finset (Fin 5)) :
    MeasurableSet {t | palette c hc x t=p} := by
  simp only [Finset.ext_iff,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i∈p
  · simpa only [hi,iff_true,mem_palette,Set.ofPred_mem_eq] using paletteSet_measurable c hc x i
  · simpa only [hi,iff_false,mem_palette,← Set.mem_compl_iff,Set.ofPred_mem_eq] using (paletteSet_measurable c hc x i).compl
lemma fiveState_measurable (x : ℂ) : Measurable (fiveState c hc x) := by
  exact Measurable.ite (palette_eq_measurable c hc x _) measurable_const
    (Measurable.ite (palette_eq_measurable c hc x _) measurable_const
      (Measurable.ite (palette_eq_measurable c hc x _) measurable_const
        (Measurable.ite (palette_eq_measurable c hc x _) measurable_const measurable_const)))
lemma fiveState_represents (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) (i : Fin 5) :
    RealState hc x {t : ℝ | fiveState c hc x (t : Angles)=i} (fiveDiag i) := by
  refine ⟨measurableSet_eq_fun ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) measurable_const,?_⟩
  intro j hj
  filter_upwards [angleMk_quasiMeasurePreserving.ae (fiveState_diag c hc hw hx)] with t ht hti
  change fiveState c hc x (t : Angles)=i at hti
  apply (mem_palette c hc x (t : Angles) j).mp
  rw [ht,hti]
  exact hj
lemma fiveState_adj (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) :
    ∀ᵐt∂angularMeasure,fiveAdj (fiveState c hc x t) (fiveState c hc x (t+(sixty : Angles))) := by
  have hs := fiveState_diag c hc hw hx
  filter_upwards [hs,(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae hs,
    palette_sixty_disjoint c hc hw x] with t ht hu hd
  apply (five_diag_disjoint _ _).mp
  change Disjoint (palette c hc x t) (palette c hc x (t+(sixty : Angles))) at hd
  rwa [ht,hu] at hd
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FiveSupport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_neighbor_real (hw : WeakColoring k c) (x : ℂ) (a : ℝ) (i : Fin k) :
    ∀ᵐt : ℝ∂volume,t∈liftPalette c hc (x+direction (a : Angles)) i → t∉liftPalette c hc x i := by
  let U : Set ℝ := {t | Real.sin (a-t)≠0}
  have hU : IsOpen U := isOpen_ne_fun (Real.continuous_sin.comp (continuous_const.sub continuous_id)) continuous_const
  have hu : ∀ᵐt : ℝ∂volume,t∈U := by
    filter_upwards [ae_sin_sub_ne_zero a] with t ht
    change Real.sin (a-t)≠0
    rwa [← neg_sub t a,Real.sin_neg,neg_ne_zero]
  have hh := palette_smooth_transport c hc hw (x := x) (z := x+direction (a : Angles)) hU (s := id) (t := fun _ => a)
    (ds := fun _ => 1) (dt := fun _ => 0) (fun t _ => hasDerivAt_id t)
    (fun t _ => hasDerivAt_const t a) (fun _ _ => one_ne_zero) (fun _ ht => ht) (fun t _ => ?_) i
  · exact (ae_restrict_iff' hU.measurableSet).mp hh |>.mp (hu.mono fun t ht hi => hi ht)
  · simp only [circleTarget,samplingParameter,add_sub_cancel_left,direction_realPlane,circleSum,one_smul,one_mul,id_eq]
    exact Prod.ext (add_comm _ _) (add_comm _ _)
lemma palette_neighbor_disjoint (hw : WeakColoring k c) (x : ℂ) (a : ℝ) :
    ∀ᵐt∂angularMeasure,Disjoint (palette c hc (x+direction (a : Angles)) t) (palette c hc x t) := by
  have hp (i : Fin k) : ∀ᵐt∂angularMeasure,t∈paletteSet c hc (x+direction (a : Angles)) i → t∉paletteSet c hc x i := by
    apply ae_angular_of_ae_line
    · simpa only [imp_iff_not_or,Set.compl_def,Set.union_def,Set.mem_ofPred_eq] using
        (paletteSet_measurable c hc (x+direction (a : Angles)) i).compl.union (paletteSet_measurable c hc x i).compl
    · exact palette_neighbor_real c hc hw x a i
  filter_upwards [ae_all_iff.mpr hp] with t ht
  exact Finset.disjoint_left.mpr fun i hi hj => ht i ((mem_palette c hc _ t i).mp hi) ((mem_palette c hc _ t i).mp hj)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
lemma ae_mem_stateSupport {f : ℝ → ι} (hf : Measurable f) (i : ι) :
    ∀ᵐt : ℝ∂volume,f t=i → t∈stateSupport f i :=
  (ae_restrict_iff' (measurableSet_eq_fun hf measurable_const)).mp
    (volume.restrict {t | f t=i}).support_mem_ae
lemma ae_state_support {f : ℝ → ι} (hf : Measurable f) :
    ∀ᵐt : ℝ∂volume,t∈stateSupport f (f t) := by
  have h : ∀ᵐt : ℝ∂volume,∀i : ι,f t=i → t∈stateSupport f i :=
    ae_all_iff.mpr (fun i => ae_mem_stateSupport hf i)
  exact h.mono fun t ht => ht (f t) rfl
lemma stateSupport_cover {f : ℝ → ι} (hf : Measurable f) (a : ℝ) : ∃i,a∈stateSupport f i := by
  have hclosed : IsClosed (⋃i,stateSupport f i)  := isClosed_iUnion_of_finite fun _ => Measure.isClosed_support
  have hae : ∀ᵐt : ℝ∂volume,t∈⋃i,stateSupport f i :=
    (ae_state_support hf).mono fun t ht => mem_iUnion.mpr ⟨f t,ht⟩
  have hd := Measure.dense_of_ae hae
  exact mem_iUnion.mp ((hclosed.closure_eq ▸ hd a) : a∈⋃i,stateSupport f i)
lemma stateSupport_shift_relation {f : ℝ → ι} (hf : Measurable f) {R : ι → ι → Prop}
    {d : ℝ} (hR : ∀ᵐt : ℝ∂volume,R (f t) (f (t+d))) {i : ι} {a : ℝ}
    (ha : a∈stateSupport f i) : ∃j,R i j ∧ a+d∈stateSupport f j := by
  classical
  let K : Set ℝ := ⋃j∈({j | R i j} : Set ι),(fun t => t+d)⁻¹'stateSupport f j
  have hK : IsClosed K := (Set.toFinite _).isClosed_biUnion (fun j _ =>
    Measure.isClosed_support.preimage (continuous_id.add continuous_const))
  have hm : ∀ᵐt : ℝ∂volume,f t=i → t∈K := by
    filter_upwards [hR,(measurePreserving_add_right (volume : Measure ℝ) d).quasiMeasurePreserving.ae (ae_state_support hf)] with t hR ht hti
    exact mem_iUnion.mpr ⟨f (t+d),mem_iUnion.mpr ⟨hti ▸ hR,ht⟩⟩
  have hk : a∈K := Measure.support_subset_of_isClosed hK
    ((ae_restrict_iff' (hf (measurableSet_singleton i))).mpr hm) ha
  rcases mem_iUnion.mp hk with ⟨j,hj⟩
  obtain ⟨hr,hs⟩ := mem_iUnion.mp hj
  exact ⟨j,hr,hs⟩
omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma stateSupport_nonempty_measure {f : ℝ → ι} {i : ι} {a : ℝ}
    (ha : a∈stateSupport f i) : 0<volume {t | f t=i} := by
  have h := (Measure.mem_support_iff_forall a).mp ha univ (univ_mem)
  simpa only [Measure.restrict_apply_univ] using h
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma five_support_trace (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (ha : a∈fiveSupport c hc x i) :
    ∃b : TraceVector 5,IsTrace c hc (x+direction (a : Angles)) b ∧ ∀j∈fiveDiag i,traceValue b j=0 :=
  state_support_avoiding_trace c hc hw (fiveState_represents c hc hw hx i) ha
lemma five_support_step_ban (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i j : Fin 5}
    (hi : a∈fiveSupport c hc x i) (hj : a∈fiveSupport c hc x j) (hij : fiveAdj i j) :
    ∀ᵐt∂angularMeasure,¬(fiveState c hc x t=i ∧ fiveState c hc x (t+(sixty : Angles))=j) ∧
      ¬(fiveState c hc x t=j ∧ fiveState c hc x (t+(sixty : Angles))=i) := by
  obtain ⟨bi,hbi,hzi⟩ := five_support_trace c hc hw hx hi
  obtain ⟨bj,hbj,hzj⟩ := five_support_trace c hc hw hx hj
  obtain ⟨X,hX⟩ := five_adj_four i j hij
  have hji : fiveAdj j i := hij.symm
  have hv : ∀ᵐt∂angularMeasure,fiveState c hc x t=i ∨ fiveState c hc x t=j →
      X∈palette c hc (x+direction (a : Angles)) t := by
    filter_upwards [avoiding_trace_palette c hc hbi hzi,avoiding_trace_palette c hc hbj hzj,
      palette_neighbor_disjoint c hc hw x a,fiveState_diag c hc hw hx] with t hni hnj hd he hs
    rw [he] at hd
    rcases hs with hi|hj
    · rw [hi] at hd
      exact five_forced_label i j X hij hX _ hd hnj
    · rw [hj] at hd
      exact five_forced_label j i X hji (by simpa only [Finset.union_comm] using hX) _ hd hni
  filter_upwards [hv,(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae hv,
    palette_sixty_disjoint c hc hw (x+direction (a : Angles))] with t ht hu hd
  constructor
  · rintro ⟨hi,hj⟩
    exact Finset.disjoint_left.mp hd (ht (Or.inl hi)) (hu (Or.inr hj))
  · rintro ⟨hj,hi⟩
    exact Finset.disjoint_left.mp hd (ht (Or.inr hj)) (hu (Or.inl hi))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma five_support_cover (x : ℂ) (a : ℝ) : ∃i,a∈fiveSupport c hc x i :=
  stateSupport_cover ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) a
lemma five_support_next (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (hi : a∈fiveSupport c hc x i) : ∃j,fiveAdj i j ∧ a+sixty∈fiveSupport c hc x j := by
  apply stateSupport_shift_relation ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) _ hi
  simpa only [Function.comp_def,AddCircle.coe_add] using angleMk_quasiMeasurePreserving.ae (fiveState_adj c hc hw hx)
lemma five_support_prev (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (hi : a∈fiveSupport c hc x i) : ∃j,fiveAdj i j ∧ a-sixty∈fiveSupport c hc x j := by
  apply stateSupport_shift_relation ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) (d := -sixty) _ hi
  have hh := angleMk_quasiMeasurePreserving.ae (fiveState_adj c hc hw hx)
  have hh' := (measurePreserving_add_right (volume : Measure ℝ) (-sixty)).quasiMeasurePreserving.ae hh
  filter_upwards [hh'] with t ht
  have he : ((t+-sixty : ℝ) : Angles)+(sixty : Angles)=(t : Angles) := by
    rw [← AddCircle.coe_add,neg_add_cancel_right]
  rw [he] at ht
  exact ht.symm
lemma five_support_no_sixty (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (hi : a∈fiveSupport c hc x i) : a+sixty∉fiveSupport c hc x i := by
  obtain ⟨j,hj,hsj⟩ := five_support_next c hc hw hx hi
  obtain ⟨X,hX⟩ := five_adj_four j i hj.symm
  have hp : 0<volume (fiveRealState c hc x j) := stateSupport_nonempty_measure hsj
  intro hs
  exact strict_state_no_unit_support hc hw hX (fiveState_represents c hc hw hx j)
    (fiveState_represents c hc hw hx i) hp hi hs (direction_sixty_unit_real a)
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor.FiveComb
lemma contact_neighbors : ∀i : Fin 5,∀L : Finset (Fin 5), i∉L → i+1∉L →
    (∃j∈L,Adj i j) → (∃j∈L,Adj (i+1) j) → i-1∈L ∧ i+2∈L := by decide
lemma opposite_contacts : ∀i j : Fin 5, Disjoint ({i-1,i+2} : Finset (Fin 5)) {j-1,j+2} →
    j=i+1 ∨ j+1=i := by decide
lemma adjacent_oriented : ∀I : Finset (Fin 5), (∃i∈I,∃j∈I,Adj i j) → ∃i,i∈I ∧ i+1∈I := by decide
lemma two_bans : ∀i j : Fin 5, j=i+1 ∨ j+1=i → ∃s,
    (s=i ∨ s=i+1) ∧ (s=j ∨ s=j+1) ∧
    ∀t,Adj s t → ((s=i ∧ t=i+1) ∨ (s=i+1 ∧ t=i)) ∨ ((s=j ∧ t=j+1) ∨ (s=j+1 ∧ t=j)) := by decide
end EuclideanFiveColor.FiveComb
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma five_contact_next (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (hi : a∈fiveSupport c hc x i) (hi' : a∈fiveSupport c hc x (i+1)) :
    i-1∈fiveSupportList c hc x (a+sixty) ∧ i+2∈fiveSupportList c hc x (a+sixty) := by
  apply FiveComb.contact_neighbors
  · exact fun h => five_support_no_sixty c hc hw hx hi ((mem_fiveSupportList _ _ _ _ _).mp h)
  · exact fun h => five_support_no_sixty c hc hw hx hi' ((mem_fiveSupportList _ _ _ _ _).mp h)
  · obtain ⟨j,hj,hs⟩ := five_support_next c hc hw hx hi
    exact ⟨j,(mem_fiveSupportList _ _ _ _ _).mpr hs,hj⟩
  · obtain ⟨j,hj,hs⟩ := five_support_next c hc hw hx hi'
    exact ⟨j,(mem_fiveSupportList _ _ _ _ _).mpr hs,hj⟩
lemma five_contact_prev (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (hi : a∈fiveSupport c hc x i) (hi' : a∈fiveSupport c hc x (i+1)) :
    i-1∈fiveSupportList c hc x (a-sixty) ∧ i+2∈fiveSupportList c hc x (a-sixty) := by
  apply FiveComb.contact_neighbors
  · intro h
    have hh := five_support_no_sixty c hc hw hx ((mem_fiveSupportList _ _ _ _ _).mp h)
    exact hh (by simpa only [sub_add_cancel] using hi)
  · intro h
    have hh := five_support_no_sixty c hc hw hx ((mem_fiveSupportList _ _ _ _ _).mp h)
    exact hh (by simpa only [sub_add_cancel] using hi')
  · obtain ⟨j,hj,hs⟩ := five_support_prev c hc hw hx hi
    exact ⟨j,(mem_fiveSupportList _ _ _ _ _).mpr hs,hj⟩
  · obtain ⟨j,hj,hs⟩ := five_support_prev c hc hw hx hi'
    exact ⟨j,(mem_fiveSupportList _ _ _ _ _).mpr hs,hj⟩
lemma five_opposite_contacts_false (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x)
    {a b : ℝ} (hab : b=a+3*sixty) {i j : Fin 5}
    (hi : a∈fiveSupport c hc x i) (hi' : a∈fiveSupport c hc x (i+1))
    (hj : b∈fiveSupport c hc x j) (hj' : b∈fiveSupport c hc x (j+1)) : False := by
  have hn := five_contact_next c hc hw hx hi hi'
  have hp := five_contact_prev c hc hw hx hj hj'
  have hdis : Disjoint ({i-1,i+2} : Finset (Fin 5)) {j-1,j+2} := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    have hiK : a+sixty∈fiveSupport c hc x k := by
      apply (mem_fiveSupportList _ _ _ _ _).mp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl|rfl <;> tauto
    have hjK : b-sixty∈fiveSupport c hc x k := by
      apply (mem_fiveSupportList _ _ _ _ _).mp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hl
      rcases hl with rfl|rfl <;> tauto
    exact five_support_no_sixty c hc hw hx hiK (by convert hjK using 1; rw [hab]; ring)
  have hji := FiveComb.opposite_contacts i j hdis
  obtain ⟨s,hs,_hst,hban⟩ := FiveComb.two_bans i j hji
  have hss : a∈fiveSupport c hc x s := by rcases hs with rfl|rfl <;> assumption
  have hbanI := five_support_step_ban c hc hw hx hi hi' (Or.inl rfl)
  have hbanJ := five_support_step_ban c hc hw hx hj hj' (Or.inl rfl)
  have hnot : ∀ᵐt∂angularMeasure,fiveState c hc x t≠s := by
    filter_upwards [hbanI,hbanJ,fiveState_adj c hc hw hx] with t hbI hbJ ha he
    rw [he] at ha
    rcases hban _ ha with h|h
    · rcases h with ⟨rfl,ht⟩|⟨rfl,ht⟩
      · exact hbI.1 ⟨he,ht⟩
      · exact hbI.2 ⟨he,ht⟩
    · rcases h with ⟨rfl,ht⟩|⟨rfl,ht⟩
      · exact hbJ.1 ⟨he,ht⟩
      · exact hbJ.2 ⟨he,ht⟩
  have hz : volume (fiveRealState c hc x s)=0 := measure_eq_zero_iff_ae_notMem.mpr (angleMk_quasiMeasurePreserving.ae hnot)
  exact (stateSupport_nonempty_measure hss).ne' hz
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
open scoped NNReal ENNReal
lemma plane_lipschitz_image_null {F : RealPlane → RealPlane} {K : ℝ≥0}
    (hf : LipschitzWith K F) {A : Set RealPlane} (ha : volume A=0) : volume (F '' A)=0 := by
  have h := hf.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤2) A
  rw [hausdorffMeasure_prod_real,ha,mul_zero] at h
  exact bot_unique h
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_open_exclusion (hw : WeakColoring k c) {x : ℂ} {i : Fin k} {a b : ℝ}
    (hab : Real.sin (b-a)≠0) {V : Set ℝ} (hV : IsOpen V) (ha : a∈V)
    (hpal : ∀ᵐt : ℝ∂volume,t∈V → (t : Angles)∈paletteSet c hc x i) :
    ∃U : Set ℂ, IsOpen U ∧ x+direction (a : Angles)+direction (b : Angles)∈U ∧
      volume (U∩{z | c z=i})=0 := by
  let e := circleInverseHomeo hab
  let W : Set RealPlane := e.source ∩ Prod.fst ⁻¹' V
  have hW : IsOpen W := e.open_source.inter (hV.preimage continuous_fst)
  have haW : (a,b)∈W := by
    refine ⟨?_,ha⟩
    exact (show HasStrictFDerivAt (circleSum 1)
      (circleSumDerivEquiv (r := 1) (p := (a,b)) (by simpa using hab) : RealPlane →L[ℝ] RealPlane)
      (a,b) from circleSum_strict 1 (a,b)).mem_toOpenPartialHomeomorph_source
  have hO : IsOpen (circleSum 1 '' W) := e.isOpen_image_of_subset_source hW inter_subset_left
  let g : RealPlane → ℂ := fun q => x+Complex.equivRealProdCLM.symm q
  have hgs (q : RealPlane) : g (circleSum 1 q)=angularSum x 1 (angleChart q) := by
    rw [angularSum_chart]
    simp only [g,map_add,ContinuousLinearEquiv.symm_apply_apply]
  have hgc : IsOpenMap g := (Homeomorph.addLeft x).isOpenMap.comp Complex.equivRealProdCLM.symm.toHomeomorph.isOpenMap
  have hex := anglePair_quasiMeasurePreserving.ae (palette_first_exclusion c hc hw x i)
  have hp : ∀ᵐq : RealPlane∂volume,q.1∈V → (q.1 : Angles)∈paletteSet c hc x i :=
    Measure.quasiMeasurePreserving_fst.ae hpal
  have hnull : volume (W∩{q | c (g (circleSum 1 q))=i})=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hex,hp] with q hq hp hmem
    apply hq (hp hmem.1.2)
    change c (angularSum x 1 (angleChart q))=i
    rw [← hgs]
    exact hmem.2
  have himage := plane_lipschitz_image_null circleSum_one_lipschitz_sumTransport hnull
  have hnullg : volume (g '' (circleSum 1 '' (W∩{q | c (g (circleSum 1 q))=i})))=0 := by
    rw [show g '' (circleSum 1 '' (W∩{q | c (g (circleSum 1 q))=i}))=
      (fun z => Complex.equivRealProdCLM (z-x)) ⁻¹' (circleSum 1 '' (W∩{q | c (g (circleSum 1 q))=i})) by
        ext z
        constructor
        · rintro ⟨p,hp,rfl⟩
          simpa only [Set.mem_preimage,g,add_sub_cancel_left,ContinuousLinearEquiv.apply_symm_apply] using hp
        · intro hz
          refine ⟨Complex.equivRealProdCLM (z-x),hz,?_⟩
          change x+Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (z-x))=z
          rw [ContinuousLinearEquiv.symm_apply_apply]
          abel]
    exact ((Complex.volume_preserving_equiv_real_prod.comp (measurePreserving_sub_right volume x)).quasiMeasurePreserving.preimage_null himage)
  refine ⟨g '' (circleSum 1 '' W),hgc _ hO,?_,?_⟩
  · refine ⟨circleSum 1 (a,b),⟨(a,b),haW,rfl⟩,?_⟩
    simpa only [angularSum,Complex.ofReal_one,one_mul,angleChart] using hgs (a,b)
  · exact measure_mono_null (by rintro z ⟨⟨q,⟨p,hp,rfl⟩,rfl⟩,hz⟩; exact ⟨_,⟨p,⟨hp,hz⟩,rfl⟩,rfl⟩) hnullg
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma transitionEdge_no_open_exclusion {i j : Fin k} {x : ℂ} (he : TransitionEdge c i j x)
    {U : Set ℂ} (hU : IsOpen U) (hx : x∈U) (hz : volume (U∩{z | c z=i})=0) : False := by
  obtain ⟨r,hr,hB⟩ := Metric.isOpen_iff.mp hU x hx
  have hae : ∀ᵐz : ℂ∂volume,z∈U → c z≠i := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with z hz hu he
    exact hz ⟨hu,he⟩
  have hratio : ∀ᶠh : ℂ in 𝓝[≠] 0, transitionRatio c i j x (r/2) h=0 := by
    have hh : ∀ᶠh : ℂ in 𝓝[≠] 0,‖h‖ < r/2 := by
      have hb : ∀ᶠh : ℂ in 𝓝[≠] 0,h∈Metric.ball 0 (r/2) :=
        nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (show 0 < r/2 by linarith))
      filter_upwards [hb] with h hh
      simpa only [Metric.mem_ball,dist_zero_right] using hh
    filter_upwards [hh] with h hh
    have hap := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hae
    have hzT : volume (transitionSet c i j x (r/2) h)=0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hae,hap] with q hq hqh ht
      have hqU : q∈U := hB (Metric.ball_subset_ball (show r/2 ≤ r by linarith) ht.1)
      have hqhU : q+h∈U := by
        apply hB
        have hd := dist_triangle (q+h) q x
        have hdist : dist (q+h) q=‖h‖ := by simp [dist_eq_norm]
        rw [hdist] at hd
        exact hd.trans_lt (by have hqx : dist q x < r/2 := ht.1; linarith)
      rcases ht.2 with ht|ht
      · exact hq hqU ht.1
      · exact hqh hqhU ht.2
    simp only [transitionRatio,hzT,ENNReal.zero_div]
  have hh : limsup (transitionRatio c i j x (r/2)) (𝓝[≠] (0:ℂ))=0 := by
    rw [limsup_congr hratio]
    exact limsup_const 0
  have hp := he.2 (r/2) (by linarith)
  rw [hh] at hp
  exact lt_irrefl _ hp
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
variable {ι X : Type*} [Finite ι] [TopologicalSpace X]
lemma finite_closed_family_locally_subset {S : ι → Set X} (hS : ∀i,IsClosed (S i)) (a : X) :
    ∃V,IsOpen V ∧ a∈V ∧ ∀v∈V,∀i,v∈S i → a∈S i := by
  let V := ⋂i∈({i | a∉S i} : Set ι),(S i)ᶜ
  have hop : IsOpen V := (Set.toFinite _).isOpen_biInter (fun i _ => (hS i).isOpen_compl)
  refine ⟨V,hop,?_,?_⟩
  · exact mem_iInter₂.mpr (fun _ hi => hi)
  · intro v hv i hi
    by_contra hn
    exact mem_iInter₂.mp hv i hn hi
lemma finite_closed_family_no_common_limit {S : ι → Set X} (hS : ∀i,IsClosed (S i))
    {P : ι → Prop} {a : X} {an : ℕ → X} (ha : Tendsto an atTop (𝓝 a))
    (hn : ∀n,∃i,an n∈S i ∧ P i) : ∃i,a∈S i ∧ P i := by
  obtain ⟨V,hV,haV,hsub⟩ := finite_closed_family_locally_subset hS a
  have hev : ∀ᶠn in atTop,an n∈V := ha (hV.mem_nhds haV)
  obtain ⟨n,hnV⟩ := hev.exists
  obtain ⟨i,hi,hP⟩ := hn n
  exact ⟨i,hsub _ hnV i hi,hP⟩
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CyclicCore
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma five_endpoint_no_common (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a b : ℝ}
    (hab : Real.sin (b-a)≠0) (hy : FiveCenter c (x+direction (a : Angles)+direction (b : Angles))) :
    ∀k : Fin 5,∃i,a∈fiveSupport c hc x i ∧ k∉fiveDiag i := by
  intro k
  by_contra! h
  obtain ⟨V,hV,ha,hpal⟩ := five_local_palette c hc hw hx h
  obtain ⟨U,hU,hyU,hnull⟩ := palette_open_exclusion c hc hw hab hV ha hpal
  exact transitionEdge_no_open_exclusion c (hy k) hU hyU hnull
lemma five_limit_contact {x : ℂ} {an : ℕ → ℝ} {a : ℝ} (ha : Tendsto an atTop (𝓝 a))
    (hn : ∀n,∀k : Fin 5,∃i,an n∈fiveSupport c hc x i ∧ k∉fiveDiag i) :
    ∃i,a∈fiveSupport c hc x i ∧ a∈fiveSupport c hc x (i+1) := by
  have hall : ∀k : Fin 5,∃i,a∈fiveSupport c hc x i ∧ k∉fiveDiag i := fun k =>
    finite_closed_family_no_common_limit (fun _ => Measure.isClosed_support) ha (fun n => hn n k)
  have hnList : (fiveSupportList c hc x a).Nonempty := by
    obtain ⟨i,hi⟩ := five_support_cover c hc x a
    exact ⟨i,(mem_fiveSupportList _ _ _ _ _).mpr hi⟩
  have hp : ∀k,∃i∈fiveSupportList c hc x a,k∉fiveDiag i := by
    intro k; obtain ⟨i,hi,hk⟩ := hall k
    exact ⟨i,(mem_fiveSupportList _ _ _ _ _).mpr hi,hk⟩
  obtain ⟨i,hi,hi'⟩ := FiveComb.adjacent_oriented _ (five_no_common_adj _ hnList hp)
  exact ⟨i,(mem_fiveSupportList _ _ _ _ _).mp hi,(mem_fiveSupportList _ _ _ _ _).mp hi'⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma chord_angles_sum {z : ℂ} (hz : ‖z‖≤2) :
    Complex.exp (((z.arg-Real.arccos (‖z‖/2) : ℝ) : ℂ)*Complex.I)+
      Complex.exp (((z.arg+Real.arccos (‖z‖/2) : ℝ) : ℂ)*Complex.I)=z := by
  have hc := Real.cos_arccos (x := ‖z‖/2) (by have := norm_nonneg z; linarith) (by linarith)
  have hre := Complex.norm_mul_cos_arg z
  have him := Complex.norm_mul_sin_arg z
  rw [Complex.exp_mul_I,Complex.exp_mul_I]
  apply Complex.ext
  · simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.cos_ofReal_re,Complex.sin_ofReal_re,Complex.sin_ofReal_im,mul_zero,
      sub_zero,mul_one]
    rw [Real.cos_sub,Real.cos_add,hc]
    nlinarith
  · simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.cos_ofReal_im,Complex.sin_ofReal_re,Complex.sin_ofReal_im,mul_zero,
      zero_add,add_zero,mul_one]
    rw [Real.sin_sub,Real.sin_add,hc]
    nlinarith
lemma chord_angles_nonparallel {r t : ℝ} (hr : 0 < r) (hr2 : r<2) :
    Real.sin ((t+Real.arccos (r/2))-(t-Real.arccos (r/2)))≠0 := by
  have ha := Real.arccos_pos.mpr (show r/2<1 by linarith)
  have hb := Real.arccos_lt_pi_div_two.mpr (show 0 < r/2 by linarith)
  exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
lemma chord_sequence_lifts {z : ℕ → ℂ} (hz : Tendsto z atTop (𝓝 0))
    (hne : ∀n,z n≠0) (hsmall : ∀n,‖z n‖<2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ t : ℝ,∃ a b : ℕ → ℝ,
      Tendsto a atTop (𝓝 (t-Real.pi/2)) ∧ Tendsto b atTop (𝓝 (t+Real.pi/2)) ∧
      (∀n,Complex.exp ((a n : ℂ)*Complex.I)+Complex.exp ((b n : ℂ)*Complex.I)=z (φ n)) ∧
      ∀n,Real.sin (b n-a n)≠0 := by
  obtain ⟨t,_ht,φ,hφ,harg⟩ := (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)).tendsto_subseq
    (fun n => ⟨(Complex.neg_pi_lt_arg (z n)).le,Complex.arg_le_pi (z n)⟩)
  have hn : Tendsto (fun n => ‖z (φ n)‖/2) atTop (𝓝 0) := by
    simpa only [Function.comp_def,norm_zero,zero_div] using ((hz.comp hφ.tendsto_atTop).norm.div_const 2)
  have hac : Tendsto (fun n => Real.arccos (‖z (φ n)‖/2)) atTop (𝓝 (Real.pi/2)) := by
    simpa only [Function.comp_def,Real.arccos_zero] using Real.continuous_arccos.continuousAt.tendsto.comp hn
  refine ⟨φ,hφ,t,(fun n => (z (φ n)).arg-Real.arccos (‖z (φ n)‖/2)),
    (fun n => (z (φ n)).arg+Real.arccos (‖z (φ n)‖/2)),harg.sub hac,harg.add hac,?_,?_⟩
  · exact fun n => chord_angles_sum (hsmall (φ n)).le
  · exact fun n => chord_angles_nonparallel (norm_pos_iff.mpr (hne (φ n))) (hsmall (φ n))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
include hc in
lemma five_sequence_small_no_accumulation (hw : WeakColoring 5 c)
    {yn : ℕ → ℂ} {x : ℂ} (hyn : ∀n,FiveCenter c (yn n)) (hx : FiveCenter c x)
    (hy : Tendsto yn atTop (𝓝 x)) (hne : ∀n,yn n≠x) (hsmall : ∀n,‖yn n-x‖<2) : False := by
  obtain ⟨φ,hφ,t,a,b,ha,hb,hs,hab⟩ := chord_sequence_lifts
    (by simpa only [sub_self] using hy.sub_const x) (fun n => sub_ne_zero.mpr (hne n)) hsmall
  have hcSum (n : ℕ) : x+direction (a n : Angles)+direction (b n : Angles)=yn (φ n) := by
    rw [direction_real,direction_real,Circle.coe_exp,Circle.coe_exp,add_assoc,hs]
    abel
  have haC : ∀n,∀k : Fin 5,∃i,a n∈fiveSupport c hc x i ∧ k∉fiveDiag i := by
    intro n
    apply five_endpoint_no_common c hc hw hx (hab n)
    rw [hcSum]; exact hyn _
  have hbC : ∀n,∀k : Fin 5,∃i,b n∈fiveSupport c hc x i ∧ k∉fiveDiag i := by
    intro n
    apply five_endpoint_no_common c hc hw hx
    · rw [show a n-b n=-(b n-a n) by ring,Real.sin_neg]
      exact neg_ne_zero.mpr (hab n)
    · rw [add_right_comm,hcSum]; exact hyn _
  obtain ⟨i,hi,hi'⟩ := five_limit_contact c hc ha haC
  obtain ⟨j,hj,hj'⟩ := five_limit_contact c hc hb hbC
  exact five_opposite_contacts_false c hc hw hx (by dsimp [sixty]; ring) hi hi' hj hj'
include hc in
lemma five_sequence_no_accumulation_oai (hw : WeakColoring 5 c)
    {yn : ℕ → ℂ} {x : ℂ} (hyn : ∀n,FiveCenter c (yn n)) (hx : FiveCenter c x)
    (hy : Tendsto yn atTop (𝓝 x)) (hne : ∀n,yn n≠x) : False := by
  have hsmall : ∀ᶠn in atTop,‖yn n-x‖<2 := by
    have hn : Tendsto (fun n => ‖yn n-x‖) atTop (𝓝 0) := by
      simpa only [sub_self,norm_zero] using (hy.sub_const x).norm
    exact hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<2))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hsmall
  exact five_sequence_small_no_accumulation c hc hw (fun n => hyn (n+N)) hx
    (hy.comp (tendsto_add_atTop_nat N)) (fun n => hne (n+N)) (fun n => hN (n+N) (Nat.le_add_left _ _))
end EuclideanFiveColor
end

end OAI
end

theorem solution : type_of% @OAI.EuclideanFiveColor.five_sequence_no_accumulation_oai := @OAI.EuclideanFiveColor.five_sequence_no_accumulation_oai
