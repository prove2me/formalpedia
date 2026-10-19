-- Prove2me | solution 1 for OAI.UniversalCoverSplitting.exists_holomorphic_local_flow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:50:06.721246+00:00
-- url     : https://prove2.me/submissions/f3fa98df-a331-4bfe-9315-082df3c2c99e

import Mathlib
import Definitions.Def_OAIQWUCS003

section
-- module Solutions.OAIQW_UniversalCover.PathDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set
open scoped Manifold

open Set Metric Filter Topology Asymptotics

namespace UniversalCoverSplitting
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem uniform_strict_derivative_on_compact {f : E → F} {D : E → E →L[𝕜] F}
    {K : Set E} (hK : IsCompact K)
    (hder : ∀ x ∈ K, HasStrictFDerivAt f (D x) x)
    (hD : ∀ x ∈ K, ContinuousAt D x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ K, ∀ x ∈ ball a δ, ∀ y ∈ ball a δ,
      ‖f x - f y - D a (x-y)‖ ≤ ε * ‖x-y‖ := by
  classical
  have hlocal (a : K) : ∃ d > 0,
      (∀ b ∈ ball a.val d, ‖D b-D a.val‖ ≤ ε/2) ∧
      ∀ x ∈ ball a.val (2*d), ∀ y ∈ ball a.val (2*d),
        ‖f x-f y-D a.val (x-y)‖ ≤ (ε/2)*‖x-y‖ := by
    have he := (hasStrictFDerivAt_iff_isLittleO.mp (hder a.val a.property)).bound (half_pos hε)
    obtain ⟨r,hr,hrb⟩ := Metric.eventually_nhds_iff_ball.mp he
    obtain ⟨s,hs,hsb⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hD a.val a.property) (ball_mem_nhds (D a.val) (half_pos hε)))
    let d := min (r/3) s
    have hd : 0 < d := lt_min (by linarith) hs
    refine ⟨d,hd,?_,?_⟩
    · intro b hb
      have : b ∈ ball a.val s := ball_subset_ball (min_le_right _ _) hb
      exact le_of_lt (by simpa only [mem_ball,dist_eq_norm] using hsb b this)
    · intro x hx y hy
      apply hrb (x,y)
      rw [← ball_prod_same]
      have hcmp : 2*d ≤ r := by have := min_le_left (r/3) s; dsimp [d]; linarith
      exact ⟨ball_subset_ball hcmp hx,ball_subset_ball hcmp hy⟩
  choose d hd hDb hstrict using hlocal
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun a : K ↦ ball a.val (d a))
    (fun _ ↦ isOpen_ball) (fun a ha ↦ mem_iUnion.mpr ⟨⟨a,ha⟩,mem_ball_self (hd ⟨a,ha⟩)⟩)
  by_cases hsn : s.Nonempty
  · refine ⟨s.inf' hsn d, (Finset.lt_inf'_iff hsn).mpr (fun a _ ↦ hd a),?_⟩
    intro a ha x hx y hy
    obtain ⟨b,hb⟩ := mem_iUnion.mp (hs ha)
    obtain ⟨hbs,hab⟩ := mem_iUnion.mp hb
    have hdle : s.inf' hsn d ≤ d b := s.inf'_le d hbs
    have hxb : x ∈ ball b.val (2*d b) := by
      have : dist x b.val ≤ dist x a + dist a b.val := dist_triangle _ _ _
      change dist x a < _ at hx
      change dist a b.val < _ at hab
      change dist x b.val < _
      linarith
    have hyb : y ∈ ball b.val (2*d b) := by
      have : dist y b.val ≤ dist y a + dist a b.val := dist_triangle _ _ _
      change dist y a < _ at hy
      change dist a b.val < _ at hab
      change dist y b.val < _
      linarith
    have herr := hstrict b x hxb y hyb
    have hop : ‖D b.val-D a‖ ≤ ε/2 := by
      rw [norm_sub_rev]
      exact hDb b a hab
    calc
      ‖f x-f y-D a (x-y)‖ =
          ‖(f x-f y-D b.val (x-y)) + (D b.val-D a) (x-y)‖ := by
        congr 1; simp only [sub_apply]; abel
      _ ≤ ‖f x-f y-D b.val (x-y)‖ + ‖(D b.val-D a) (x-y)‖ := norm_add_le _ _
      _ ≤ (ε/2)*‖x-y‖ + (ε/2)*‖x-y‖ :=
        add_le_add herr (((D b.val-D a).le_opNorm _).trans (by gcongr))
      _ = ε*‖x-y‖ := by ring
  · refine ⟨1,zero_lt_one,?_⟩
    intro a ha
    have := hs ha
    simp only [Finset.not_nonempty_iff_eq_empty.mp hsn,Finset.notMem_empty, iUnion_of_empty,
      iUnion_empty,mem_empty_iff_false] at this

end UniversalCoverSplitting
open Set Metric Filter Topology Asymptotics

namespace UniversalCoverSplitting
variable {𝕜 E F T : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace T] [CompactSpace T]

theorem hasStrictFDerivAt_pathCompose (f : C(E,F)) (D : E → E →L[𝕜] F)
    (γ : C(T,E)) (hder : ∀ t, HasStrictFDerivAt f (D (γ t)) (γ t))
    (hD : ∀ t, ContinuousAt D (γ t)) :
    HasStrictFDerivAt (fun η : C(T,E) ↦ f.comp η)
      (pathLinearApply (pathDerivative D γ hD)) γ := by
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hb⟩ := uniform_strict_derivative_on_compact
    (isCompact_range γ.continuous)
    (by rintro x ⟨t,rfl⟩; exact hder t)
    (by rintro x ⟨t,rfl⟩; exact hD t) hε
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨δ,hδ,?_⟩
  intro p hp
  rw [← ball_prod_same] at hp
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro t
  have hx : p.1 t ∈ ball (γ t) δ := by
    have ht := (p.1-γ).norm_coe_le_norm t
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt ht (by simpa only [mem_ball,dist_eq_norm] using hp.1)
  have hy : p.2 t ∈ ball (γ t) δ := by
    have ht := (p.2-γ).norm_coe_le_norm t
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt ht (by simpa only [mem_ball,dist_eq_norm] using hp.2)
  exact (hb (γ t) (mem_range_self t) _ hx _ hy).trans
    (mul_le_mul_of_nonneg_left ((p.1-p.2).norm_coe_le_norm t) hε.le)

end UniversalCoverSplitting
open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {𝕜 E F T : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace T] [CompactSpace T]

theorem contDiffAt_pathCompose_one (f : C(E,F)) (D : C(E,E →L[𝕜] F))
    {U : Set E} (hU : IsOpen U)
    (hder : ∀ x ∈ U, HasFDerivAt f (D x) x)
    (γ : C(T,E)) (hγ : range γ ⊆ U) :
    ContDiffAt 𝕜 1 (fun η : C(T,E) ↦ f.comp η) γ := by
  let O : Set C(T,E) := {η | range η ⊆ U}
  have hO : IsOpen O := ContinuousMap.isOpen_setOfPred_range_subset hU
  have hcoef : Continuous (fun η : C(T,E) ↦ pathLinearApply (D.comp η)) :=
    pathLinearApplyL.continuous.comp D.continuous_postcomp
  apply contDiffAt_one_iff.mpr
  refine ⟨fun η ↦ pathLinearApply (D.comp η), O, hO.mem_nhds hγ,
    hcoef.continuousOn, ?_⟩
  intro η hη
  have hs (t : T) : HasStrictFDerivAt f (D (η t)) (η t) := by
    apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    · filter_upwards [hU.mem_nhds (hη (mem_range_self t))] with x hx
      exact hder x hx
    · exact D.continuous.continuousAt
  have hD (t : T) : ContinuousAt D (η t) := D.continuous.continuousAt
  convert! (hasStrictFDerivAt_pathCompose f D η hs hD).hasFDerivAt using 1

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Picard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set Metric Filter Topology
open Set MeasureTheory
open scoped Interval

open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

 theorem contDiffAt_picardEquation_one (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ContDiffAt ℂ 1 (picardEquation V) (picardBase p) := by
  have hpath : range (ContinuousMap.const FlowTime p) ⊆ U := by
    rintro _ ⟨t,rfl⟩; exact hp
  have hs := contDiffAt_pathCompose_one V D hU hder (ContinuousMap.const FlowTime p) hpath
  have hi : ContDiffAt ℂ 1 (picardIntegral V) (ContinuousMap.const FlowTime p) :=
    (pathPrimitiveL : FlowPath E →L[ℂ] FlowPath E).contDiff.contDiffAt.comp _ hs
  have hiq : ContDiffAt ℂ 1 (fun q : FlowParameter E × FlowPath E ↦ picardIntegral V q.2)
      (picardBase p) := hi.comp (f := fun q : FlowParameter E × FlowPath E ↦ q.2) (picardBase p) contDiffAt_id.snd
  have hc : ContDiffAt ℂ 1 (fun q : FlowParameter E × FlowPath E ↦
      ContinuousMap.const FlowTime q.1.1) (picardBase p) :=
    (ContinuousLinearMap.const ℂ FlowTime : E →L[ℂ] FlowPath E).contDiff.contDiffAt.comp _
      contDiffAt_id.fst.fst
  exact contDiffAt_id.fst.prodMk
    ((contDiffAt_id.snd.sub hc).sub (contDiffAt_id.fst.snd.smul hiq))

 theorem hasFDerivAt_picardEquation_base (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    HasFDerivAt (picardEquation V) (pathShear (picardLinearTerm V p)).toContinuousLinearMap
      (picardBase p) := by
  have hpath : range (ContinuousMap.const FlowTime p) ⊆ U := by
    rintro _ ⟨t,rfl⟩; exact hp
  have hs := contDiffAt_pathCompose_one V D hU hder (ContinuousMap.const FlowTime p) hpath
  have hi : DifferentiableAt ℂ (picardIntegral V) (ContinuousMap.const FlowTime p) :=
    (pathPrimitiveL : FlowPath E →L[ℂ] FlowPath E).differentiableAt.comp _
      (hs.differentiableAt (by norm_num))
  let q₀ := picardBase p
  have hid : HasFDerivAt (fun q : FlowParameter E × FlowPath E ↦ q)
      (ContinuousLinearMap.id ℂ _) q₀ := hasFDerivAt_id q₀
  have hiq := hi.hasFDerivAt.comp q₀ hid.snd
  have hc := (ContinuousLinearMap.const ℂ FlowTime : E →L[ℂ] FlowPath E).hasFDerivAt.comp q₀
    hid.fst.fst
  have he := hid.fst.prodMk ((hid.snd.sub hc).sub (hid.fst.snd.smul hiq))
  convert! he using 1
  ext q t <;> simp [pathShear,picardLinearTerm,picardBase,q₀]

end UniversalCoverSplitting
open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem exists_holomorphic_picard_family (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ∃ W : Set (FlowParameter E), IsOpen W ∧ (p,0) ∈ W ∧
      ∃ φ : FlowParameter E → FlowPath E,
        ContDiffOn ℂ 1 φ W ∧ φ (p,0) = ContinuousMap.const FlowTime p ∧
        ∀ q ∈ W, range (φ q) ⊆ U ∧
          φ q = ContinuousMap.const FlowTime q.1 + q.2 • picardIntegral V (φ q) := by
  let q₀ := picardBase p
  have hc := contDiffAt_picardEquation_one V D hU hder hp
  have hd := hasFDerivAt_picardEquation_base V D hU hder hp
  have hn : (1 : ℕ∞ω) ≠ 0 := by norm_num
  let H := hc.localInverse hd hn
  have hHbase : H ((p,0),0) = q₀ := by
    simpa only [picardEquation_base] using hc.localInverse_apply_image hd hn
  have hH : ContDiffAt ℂ 1 H ((p,0),0) := by
    simpa only [picardEquation_base] using hc.to_localInverse hd hn
  let φ : FlowParameter E → FlowPath E := fun q ↦ (H (q,0)).2
  have hφbase : φ (p,0) = ContinuousMap.const FlowTime p := by
    change (H ((p,0),0)).2 = _
    rw [hHbase]; rfl
  have hφ : ContDiffAt ℂ 1 φ (p,0) :=
    hH.snd.comp (f := fun q : FlowParameter E ↦ (q,(0 : FlowPath E))) (p,0)
      (contDiffAt_id.prodMk contDiffAt_const)
  have hemb : ContinuousAt (fun q : FlowParameter E ↦ (q,(0 : FlowPath E))) (p,0) := by
    fun_prop
  have hi : ∀ᶠ q : FlowParameter E × FlowPath E in 𝓝 ((p,0),0),
      picardEquation V (H q) = q := by
    convert! (hc.hasStrictFDerivAt' hd hn).eventually_right_inverse using 1
    simp only [picardEquation_base]
  have hir := hemb.tendsto.eventually hi
  have hprange : range (ContinuousMap.const FlowTime p) ⊆ U := by
    rintro _ ⟨t,rfl⟩; exact hp
  have hr : ∀ᶠ q in 𝓝 (p,0), range (φ q) ⊆ U := by
    have hh : ∀ᶠ γ : FlowPath E in 𝓝 (φ (p,0)), range γ ⊆ U := by
      rw [hφbase]
      convert! ContinuousMap.eventually_range_subset hU hprange
    exact hφ.continuousAt.tendsto.eventually hh
  obtain ⟨S,hS,hCS⟩ := hφ.contDiffOn le_rfl (by norm_num)
  have hall : {q | q ∈ S ∧ picardEquation V (H (q,0)) = (q,0) ∧ range (φ q) ⊆ U}
      ∈ 𝓝 (p,0) := by
    filter_upwards [hS,hir,hr] with q hq hiq hrq
    exact ⟨hq,hiq,hrq⟩
  obtain ⟨W,hW,hWo,hWp⟩ := _root_.mem_nhds_iff.mp hall
  refine ⟨W,hWo,hWp,φ,hCS.mono (fun q hq ↦ (hW hq).1),hφbase,?_⟩
  intro q hq
  obtain ⟨_,heq,hrange⟩ := hW hq
  refine ⟨hrange,?_⟩
  have hparam := congrArg Prod.fst heq
  have hres := congrArg Prod.snd heq
  change (H (q,0)).1 = q at hparam
  change (H (q,0)).2 - ContinuousMap.const FlowTime (H (q,0)).1.1 -
    (H (q,0)).1.2 • picardIntegral V (H (q,0)).2 = 0 at hres
  rw [hparam] at hres
  apply sub_eq_zero.mp
  simpa only [sub_add_eq_sub_sub,φ] using hres

end UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Interval

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem hasFDerivAt_picardIntegral (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {γ : FlowPath E} (hγ : range γ ⊆ U) :
    HasFDerivAt (picardIntegral V)
      (pathPrimitiveL.comp (pathLinearApply (D.comp γ))) γ := by
  have hs (t : FlowTime) : HasStrictFDerivAt V (D (γ t)) (γ t) := by
    apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    · filter_upwards [hU.mem_nhds (hγ (mem_range_self t))] with x hx
      exact hder x hx
    · exact D.continuous.continuousAt
  have hD (t : FlowTime) : ContinuousAt D (γ t) := D.continuous.continuousAt
  have hsc : HasFDerivAt (fun η : FlowPath E ↦ V.comp η)
      (pathLinearApply (D.comp γ)) γ := by
    convert! (hasStrictFDerivAt_pathCompose V D γ hs hD).hasFDerivAt using 1
  exact pathPrimitiveL.hasFDerivAt.comp γ hsc

omit [CompleteSpace E] in

theorem picard_variation_equation (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} {z : ℂ} {ψ : ℂ → FlowPath E} {Z : FlowPath E}
    (hψ : HasDerivAt ψ Z z) (hr : range (ψ z) ⊆ U)
    (heq : ∀ᶠ w in 𝓝 z, ψ w = ContinuousMap.const FlowTime p + w • picardIntegral V (ψ w)) :
    Z = picardIntegral V (ψ z) + z • pathPrimitiveL (pathLinearApply (D.comp (ψ z)) Z) := by
  have hi := (hasFDerivAt_picardIntegral V D hU hder hr).comp_hasDerivAt z hψ
  have hh := ((hasDerivAt_id z).smul hi).const_add (ContinuousMap.const FlowTime p)
  have he : HasDerivAt ψ
      (picardIntegral V (ψ z) + z • pathPrimitiveL (pathLinearApply (D.comp (ψ z)) Z)) z := by
    convert! hh.congr_of_eventuallyEq heq using 1
    simp [add_comm]
  exact hψ.unique he

omit [CompleteSpace E] in

theorem picard_linear_unique (A : C(FlowTime,E →L[ℂ] E)) {z : ℂ}
    (hz : ‖z‖ * ‖A‖ < 1) {B Z Y : FlowPath E}
    (hZ : Z = B + z • pathPrimitiveL (pathLinearApply A Z))
    (hY : Y = B + z • pathPrimitiveL (pathLinearApply A Y)) : Z = Y := by
  have he : Z-Y = z • pathPrimitiveL (pathLinearApply A (Z-Y)) := by
    calc
      Z-Y = (B + z • pathPrimitiveL (pathLinearApply A Z)) -
          (B + z • pathPrimitiveL (pathLinearApply A Y)) := congrArg₂ (· - ·) hZ hY
      _ = z • pathPrimitiveL (pathLinearApply A (Z-Y)) := by
        rw [map_sub,map_sub,smul_sub]; abel
  have hn : ‖Z-Y‖ ≤ (‖z‖ * ‖A‖) * ‖Z-Y‖ := by
    calc
      ‖Z-Y‖ = ‖z‖ * ‖pathPrimitiveL (pathLinearApply A (Z-Y))‖ := (congrArg norm he).trans (norm_smul _ _)
      _ ≤ ‖z‖ * ‖pathLinearApply A (Z-Y)‖ :=
        mul_le_mul_of_nonneg_left (pathPrimitive_norm_le _) (norm_nonneg z)
      _ ≤ ‖z‖ * (‖A‖ * ‖Z-Y‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
        exact ((pathLinearApply A).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (pathLinearApply_norm_le A) (norm_nonneg _))
      _ = (‖z‖ * ‖A‖) * ‖Z-Y‖ := by ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (Z-Y)]))

theorem picardRealExtension_hasDerivAt (V : C(E,E)) (p : E) (z : ℂ)
    (γ : FlowPath E) (t : ℝ) :
    HasDerivAt (picardRealExtension V p z γ) (z • V (pathExtend γ t)) t := by
  have hc : Continuous (fun u ↦ V (pathExtend γ u)) := V.continuous.comp (pathExtend γ).continuous
  exact ((intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt).const_smul z).const_add p

omit [CompleteSpace E] in
theorem picardRealExtension_eq (V : C(E,E)) {p : E} {z : ℂ} {γ : FlowPath E}
    (heq : γ = ContinuousMap.const FlowTime p + z • picardIntegral V γ)
    (t : FlowTime) : picardRealExtension V p z γ t = γ t := by
  exact (congrArg (fun η : FlowPath E ↦ η t) heq).symm

end UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Interval

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem picardTimeVariation_equation (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} {z : ℂ} {γ : FlowPath E} (hr : range γ ⊆ U)
    (heq : γ = ContinuousMap.const FlowTime p + z • picardIntegral V γ) :
    picardTimeVariation V γ = picardIntegral V γ +
      z • pathPrimitiveL (pathLinearApply (D.comp γ) (picardTimeVariation V γ)) := by
  let η := picardRealExtension V p z γ
  let β := V.comp γ
  let A := D.comp γ
  let Y := picardTimeVariation V γ
  let g : ℝ → E := fun u ↦ pathExtend β u + z • pathExtend (pathLinearApply A Y) u
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hη (u : FlowTime) : η u = γ u := picardRealExtension_eq V heq u
  have hd (u : FlowTime) : HasDerivAt (fun v : ℝ ↦ v • V (η v)) (g u) u := by
    have ht := picardRealExtension_hasDerivAt V p z γ u.val
    have hv := ((hder (γ u) (hr (mem_range_self u))).restrictScalars ℝ)
    rw [← hη u] at hv
    have hc := hv.comp_hasDerivAt u.val ht
    have hh := (hasDerivAt_id u.val).smul hc
    convert! hh using 1
    dsimp [g,β,A,Y,picardTimeVariation]
    rw [pathExtend_apply,pathExtend_apply,pathLinearApply_apply,hη u,pathExtend_apply]
    simp only [one_smul,ContinuousMap.comp_apply]
    change V (γ u) + z • (D (γ u)) (u.val • V (γ u)) =
      u.val • (D (γ u)) (z • V (γ u)) + V (γ u)
    simp only [ContinuousLinearMap.map_smul_of_tower]
    rw [smul_comm,add_comm]
  ext t
  have hderiv (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) t.val) :
      HasDerivAt (fun v : ℝ ↦ v • V (η v)) (g u) u := by
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      rw [uIcc_of_le t.property.1] at hu
      exact ⟨hu.1,hu.2.trans t.property.2⟩
    exact hd ⟨u,hu'⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hg.intervalIntegrable 0 t.val)
  have heval : (∫ u in (0 : ℝ)..t.val, g u) =
      picardIntegral V γ t + z • pathPrimitiveL (pathLinearApply A Y) t := by
    dsimp [g,picardIntegral]
    rw [intervalIntegral.integral_add,intervalIntegral.integral_smul]
    · exact (pathExtend β).continuous.intervalIntegrable _ _
    · exact ((pathExtend (pathLinearApply A Y)).continuous.const_smul z).intervalIntegrable _ _
  rw [heval] at hi
  simp only [zero_smul,sub_zero] at hi
  change t.val • V (γ t) = _
  rw [← hη t]
  exact hi.symm

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.FlowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology
open scoped ContDiff
open Set Metric Filter Topology MeasureTheory
open scoped Interval

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem picard_initial_variation (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p v : E} {z : ℂ} {ψ : ℂ → FlowPath E} {Z : FlowPath E}
    (hψ : HasDerivAt ψ Z 0) (hr : range (ψ 0) ⊆ U)
    (heq : ∀ᶠ w in 𝓝 (0 : ℂ),
      ψ w = ContinuousMap.const FlowTime (p+w•v) + z • picardIntegral V (ψ w)) :
    Z = ContinuousMap.const FlowTime v +
      z • pathPrimitiveL (pathLinearApply (D.comp (ψ 0)) Z) := by
  have hi := (hasFDerivAt_picardIntegral V D hU hder hr).comp_hasDerivAt 0 hψ
  have hp := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  have hc := (ContinuousLinearMap.const ℂ FlowTime : E →L[ℂ] FlowPath E).hasFDerivAt.comp_hasDerivAt 0 hp
  have hh := hc.add (hi.const_smul z)
  have he : HasDerivAt ψ (ContinuousMap.const FlowTime v +
      z • pathPrimitiveL (pathLinearApply (D.comp (ψ 0)) Z)) 0 := by
    convert! hh.congr_of_eventuallyEq heq using 1
    simp
    rfl
  exact hψ.unique he

theorem commuting_field_picard_equation (V W : C(E,E)) (D : C(E,E →L[ℂ] E))
    (DW : E → E →L[ℂ] E) {U : Set E}
    (hW : ∀ x ∈ U, HasFDerivAt W (DW x) x)
    (hcomm : ∀ x ∈ U, DW x (V x) = D x (W x))
    {p : E} {z : ℂ} {γ : FlowPath E} (hr : range γ ⊆ U)
    (heq : γ = ContinuousMap.const FlowTime p + z • picardIntegral V γ) :
    W.comp γ = ContinuousMap.const FlowTime (W p) +
      z • pathPrimitiveL (pathLinearApply (D.comp γ) (W.comp γ)) := by
  let η := picardRealExtension V p z γ
  let B := pathLinearApply (D.comp γ) (W.comp γ)
  have hη (u : FlowTime) : η u = γ u := picardRealExtension_eq V heq u
  have hd (u : FlowTime) : HasDerivAt (fun v : ℝ ↦ W (η v))
      (z • pathExtend B u) u := by
    have ht := picardRealExtension_hasDerivAt V p z γ u.val
    have hv := ((hW (γ u) (hr (mem_range_self u))).restrictScalars ℝ)
    rw [← hη u] at hv
    have hc := hv.comp_hasDerivAt u.val ht
    convert! hc using 1
    rw [pathExtend_apply,hη u,pathExtend_apply]
    change z • D (γ u) (W (γ u)) = DW (γ u) (z • V (γ u))
    rw [map_smul,hcomm _ (hr (mem_range_self u))]
  ext t
  have hderiv (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) t.val) :
      HasDerivAt (fun v : ℝ ↦ W (η v)) (z • pathExtend B u) u := by
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      rw [uIcc_of_le t.property.1] at hu
      exact ⟨hu.1,hu.2.trans t.property.2⟩
    exact hd ⟨u,hu'⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (((pathExtend B).continuous.const_smul z).intervalIntegrable 0 t.val)
  rw [intervalIntegral.integral_smul,hη t] at hi
  have hη0 : η 0 = p := by simp [η,picardRealExtension]
  rw [hη0] at hi
  change W (γ t) = W p + z • ∫ u in (0 : ℝ)..t.val, pathExtend B u
  exact (sub_eq_iff_eq_add.mp hi.symm).trans (add_comm _ _)

theorem picard_endpoint_preserves_commuting_field (V W : C(E,E))
    (D : C(E,E →L[ℂ] E)) (DW : E → E →L[ℂ] E)
    {U : Set E} (hU : IsOpen U) (hV : ∀ x ∈ U, HasFDerivAt V (D x) x)
    (hW : ∀ x ∈ U, HasFDerivAt W (DW x) x)
    (hcomm : ∀ x ∈ U, DW x (V x) = D x (W x))
    {p : E} {z : ℂ} {ψ : ℂ → FlowPath E} {Z : FlowPath E}
    (hψ : HasDerivAt ψ Z 0) (hr : range (ψ 0) ⊆ U)
    (heq : ∀ᶠ w in 𝓝 (0 : ℂ), ψ w =
      ContinuousMap.const FlowTime (p+w•W p) + z • picardIntegral V (ψ w))
    (hz : ‖z‖ * ‖D.comp (ψ 0)‖ < 1) :
    HasDerivAt (fun w ↦ ψ w ⟨1,zero_le_one,le_rfl⟩)
      (W (ψ 0 ⟨1,zero_le_one,le_rfl⟩)) 0 := by
  have hZ := picard_initial_variation V D hU hV hψ hr heq
  have heq0 : ψ 0 = ContinuousMap.const FlowTime p + z • picardIntegral V (ψ 0) := by
    simpa using heq.self_of_nhds
  have hY := commuting_field_picard_equation V W D DW hW hcomm hr heq0
  have hZY := picard_linear_unique (D.comp (ψ 0)) hz hZ hY
  have hEval := (ContinuousMap.evalCLM (R := ℂ) (M := E)
    (⟨1,zero_le_one,le_rfl⟩ : FlowTime)).hasFDerivAt.comp_hasDerivAt 0 hψ
  convert! hEval using 1
  rw [hZY]; rfl

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem exists_small_holomorphic_picard_family (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ∃ W : Set (FlowParameter E), IsOpen W ∧ (p,0) ∈ W ∧
      ∃ φ : FlowParameter E → FlowPath E,
        ContDiffOn ℂ 1 φ W ∧ φ (p,0) = ContinuousMap.const FlowTime p ∧
        ∀ q ∈ W, range (φ q) ⊆ U ∧
          φ q = ContinuousMap.const FlowTime q.1 + q.2 • picardIntegral V (φ q) ∧
          ‖q.2‖ * ‖D.comp (φ q)‖ < 1 := by
  obtain ⟨O,hOo,hOp,φ,hφ,hφbase,heq⟩ := exists_holomorphic_picard_family V D hU hder hp
  have hcφ : ContinuousAt φ (p,0) := hφ.continuousOn.continuousAt (hOo.mem_nhds hOp)
  have hcD : ContinuousAt (fun q : E × ℂ ↦ D.comp (φ q)) (p,0) := by
    convert! D.continuous_postcomp.continuousAt.comp hcφ
  have hn : Continuous (fun A : C(FlowTime,E →L[ℂ] E) ↦ ‖A‖) := by
    convert! @continuous_norm C(FlowTime,E →L[ℂ] E) inferInstance
  have hcNorm : ContinuousAt (fun q : E × ℂ ↦ ‖q.2‖ * ‖D.comp (φ q)‖) (p,0) :=
    continuous_snd.continuousAt.norm.mul (hn.continuousAt.comp hcD)
  have hsmall : ∀ᶠ q : E × ℂ in 𝓝 (p,0), ‖q.2‖ * ‖D.comp (φ q)‖ < 1 := by
    apply hcNorm.eventually_lt continuousAt_const
    simp
  have hboth : O ∩ {q | ‖q.2‖ * ‖D.comp (φ q)‖ < 1} ∈ 𝓝 (p,0) :=
    inter_mem (hOo.mem_nhds hOp) hsmall
  obtain ⟨W,hWO,hWo,hWp⟩ := _root_.mem_nhds_iff.mp hboth
  refine ⟨W,hWo,hWp,φ,hφ.mono (fun q hq ↦ (hWO hq).1),hφbase,?_⟩
  intro q hq
  exact ⟨(heq q (hWO hq).1).1,(heq q (hWO hq).1).2,(hWO hq).2⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem picard_endpoint_hasDerivAt (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} {z : ℂ} {ψ : ℂ → FlowPath E} {Z : FlowPath E}
    (hψ : HasDerivAt ψ Z z) (hr : range (ψ z) ⊆ U)
    (heq : ∀ᶠ w in 𝓝 z, ψ w = ContinuousMap.const FlowTime p + w • picardIntegral V (ψ w))
    (hz : ‖z‖ * ‖D.comp (ψ z)‖ < 1) :
    HasDerivAt (fun w ↦ ψ w ⟨1,zero_le_one,le_rfl⟩)
      (V (ψ z ⟨1,zero_le_one,le_rfl⟩)) z := by
  have hZ := picard_variation_equation V D hU hder hψ hr heq
  have hY := picardTimeVariation_equation V D hder hr heq.self_of_nhds
  have hZY := picard_linear_unique (D.comp (ψ z)) hz hZ hY
  have he := (ContinuousMap.evalCLM (R := ℂ) (M := E)
    (⟨1,zero_le_one,le_rfl⟩ : FlowTime)).hasFDerivAt.comp_hasDerivAt z hψ
  convert! he using 1
  rw [hZY]
  simp [picardTimeVariation]

end UniversalCoverSplitting
open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem picard_family_fderiv_preserves (V W : C(E,E))
    (D : C(E,E →L[ℂ] E)) (DW : E → E →L[ℂ] E)
    {U : Set E} (hU : IsOpen U) (hV : ∀ x ∈ U, HasFDerivAt V (D x) x)
    (hW : ∀ x ∈ U, HasFDerivAt W (DW x) x)
    (hcomm : ∀ x ∈ U, DW x (V x) = D x (W x))
    {O : Set (E × ℂ)} (hO : IsOpen O) {φ : E × ℂ → FlowPath E}
    (hφ : ContDiffOn ℂ 1 φ O)
    (heq : ∀ q ∈ O, range (φ q) ⊆ U ∧
      φ q = ContinuousMap.const FlowTime q.1 + q.2 • picardIntegral V (φ q) ∧
      ‖q.2‖ * ‖D.comp (φ q)‖ < 1)
    {q : E × ℂ} (hq : q ∈ O) :
    fderiv ℂ (fun r ↦ φ r ⟨1,zero_le_one,le_rfl⟩) q (W q.1,0) =
      W (φ q ⟨1,zero_le_one,le_rfl⟩) := by
  let c : ℂ → E × ℂ := fun w ↦ (q.1 + w • W q.1,q.2)
  have hc : HasDerivAt c (W q.1,0) 0 := by
    convert! (((hasDerivAt_id (0 : ℂ)).smul_const (W q.1)).const_add q.1).prodMk
      (hasDerivAt_const (0 : ℂ) q.2) using 1; simp
  have hc0 : c 0 = q := by simp [c]
  have hφq := (hφ.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hφc : DifferentiableAt ℂ φ (c 0) := by simpa only [hc0] using hφq
  have hψ := hφc.hasFDerivAt.comp_hasDerivAt 0 hc
  have hr : range (φ (c 0)) ⊆ U := by simpa [hc0] using (heq q hq).1
  have hi : ∀ᶠ w in 𝓝 (0 : ℂ), φ (c w) =
      ContinuousMap.const FlowTime (q.1+w•W q.1) + q.2 • picardIntegral V (φ (c w)) := by
    have hnc : O ∈ 𝓝 (c 0) := by simpa only [hc0] using hO.mem_nhds hq
    have hn := hc.continuousAt.tendsto.eventually hnc
    filter_upwards [hn] with w hw
    exact (heq _ hw).2.1
  have hz : ‖q.2‖ * ‖D.comp (φ (c 0))‖ < 1 := by
    simpa [hc0] using (heq q hq).2.2
  have hP := picard_endpoint_preserves_commuting_field V W D DW hU hV hW hcomm hψ hr hi hz
  let F : E × ℂ → E := fun r ↦ φ r ⟨1,zero_le_one,le_rfl⟩
  have hF : DifferentiableAt ℂ F q :=
    (ContinuousMap.evalCLM (R := ℂ) (M := E) (⟨1,zero_le_one,le_rfl⟩ : FlowTime)).differentiableAt.comp q hφq
  have hFc : DifferentiableAt ℂ F (c 0) := by simpa only [hc0] using hF
  have hF' := hFc.hasFDerivAt.comp_hasDerivAt 0 hc
  simpa [hc0,F] using hF'.unique hP

theorem exists_holomorphic_flow_preserving_representatives (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ∃ W : Set (E × ℂ), IsOpen W ∧ (p,0) ∈ W ∧
      ∃ F : E × ℂ → E,
        ContDiffOn ℂ 1 F W ∧ MapsTo F W U ∧
        (∀ x, (x,0) ∈ W → F (x,0) = x) ∧
        (∀ q ∈ W, HasDerivAt (fun z ↦ F (q.1,z)) (V (F q)) q.2) ∧
        (∀ (A : C(E,E)) (DA : E → E →L[ℂ] E),
          (∀ x ∈ U, HasFDerivAt A (DA x) x) →
          (∀ x ∈ U, DA x (V x) = D x (A x)) →
          ∀ q ∈ W, fderiv ℂ F q (A q.1,0) = A (F q)) := by
  obtain ⟨W,hWo,hWp,φ,hφ,hφbase,heq⟩ :=
    exists_small_holomorphic_picard_family V D hU hder hp
  let e₁ : FlowTime := ⟨1,zero_le_one,le_rfl⟩
  let F : E × ℂ → E := fun q ↦ φ q e₁
  refine ⟨W,hWo,hWp,F,?_,?_,?_,?_,?_⟩
  · exact (ContinuousMap.evalCLM (R := ℂ) (M := E) e₁).contDiff.comp_contDiffOn
      hφ
  · intro q hq
    exact (heq q hq).1 (mem_range_self e₁)
  · intro x hx
    have h := congrArg (fun γ : FlowPath E ↦ γ e₁) (heq (x,0) hx).2.1
    simpa [F] using h
  · intro q hq
    have hφq : DifferentiableAt ℂ φ q :=
      (hφ.contDiffAt (hWo.mem_nhds hq)).differentiableAt (by norm_num)
    have hem : DifferentiableAt ℂ (fun z : ℂ ↦ (q.1,z)) q.2 :=
      (differentiableAt_const q.1).prodMk differentiableAt_id
    have hψ := (hφq.comp q.2 hem).hasDerivAt
    have heq' : ∀ᶠ z in 𝓝 q.2,
        φ (q.1,z) = ContinuousMap.const FlowTime q.1 + z • picardIntegral V (φ (q.1,z)) := by
      have hn := hem.continuousAt.tendsto.eventually (hWo.mem_nhds hq)
      filter_upwards [hn] with z hz
      exact (heq _ hz).2.1
    exact picard_endpoint_hasDerivAt V D hU hder hψ (heq q hq).1 heq' (heq q hq).2.2

  · intro A DA hA hcomm q hq
    exact picard_family_fderiv_preserves V A D DA hU hder hA hcomm hWo hφ heq hq

end UniversalCoverSplitting
open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem exists_holomorphicFlowData_proof (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hV : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) : Nonempty (HolomorphicFlowData V D U p) := by
  obtain ⟨O,hO,hpO,F,hF,hFU,hF0,hFt,hFA⟩ :=
    exists_holomorphic_flow_preserving_representatives V D hU hV hp
  refine ⟨⟨O,hO,hpO,F,hF,hFU,hF0,?_,hFA⟩⟩
  intro q hq
  have hFq := (hF.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)
  have hc : HasDerivAt (fun z : ℂ ↦ (q.1,z)) (0,1) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  exact (hFq.hasFDerivAt.comp_hasDerivAt q.2 hc).unique (hFt q hq)

theorem exists_holomorphic_local_flow_oai (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hV : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ∃ (O : Set (E × ℂ)) (F : E × ℂ → E), IsOpen O ∧ (p,0) ∈ O ∧
      ContDiffOn ℂ 1 F O ∧ Set.MapsTo F O U ∧
      (∀ x, (x,0) ∈ O → F (x,0) = x) ∧
      (∀ q ∈ O, fderiv ℂ F q (0,1) = V (F q)) ∧
      (∀ (A : C(E,E)) (DA : E → E →L[ℂ] E),
        (∀ x ∈ U, HasFDerivAt A (DA x) x) →
        (∀ x ∈ U, DA x (V x) = D x (A x)) →
        ∀ q ∈ O, fderiv ℂ F q (A q.1,0) = A (F q)) := by
  obtain ⟨H⟩ := exists_holomorphicFlowData_proof V D hU hV hp
  exact ⟨H.domain, H.map, H.isOpen_domain, H.base_mem, H.contDiff, H.mapsTo, H.zero, H.time,
    H.preserves⟩

end UniversalCoverSplitting

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.UniversalCoverSplitting.exists_holomorphic_local_flow_oai.{u_1} := @OAI.UniversalCoverSplitting.exists_holomorphic_local_flow_oai.{u_1}
