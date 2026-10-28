-- Prove2me | solution 1 for OAI.SmoothObstruction.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:25:04.097433+00:00
-- url     : https://prove2.me/submissions/7e42be85-757b-4e00-b522-b8c161a2b640

import Mathlib
import Definitions.Def_SmoothObstruction
import Definitions.Def_OAIQ5T3000
import Theorems.Thm_OAI_SmoothObstruction_ManifoldCoordinates_grid_switches
import Theorems.Thm_OAI_SmoothObstruction_WordHierarchy_no_switching

section
-- module Solutions.OAIQ5_T3.Compat
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Models
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped ENNReal Topology Manifold ContDiff

namespace SmoothObstruction.ConullTransport
open MeasureTheory Set
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma inverse_coe (A : Set X) (B : Set Y) (e : A ≃ᵐ B) (x₀ : X) (y : B) :
    inverse A B e x₀ y=(e.symm y : X) :=
  Subtype.val_injective.extend_apply _ _ y

lemma measurable_inverse (A : Set X) (B : Set Y) (e : A ≃ᵐ B) (x₀ : X)
    (hB : MeasurableSet B) : Measurable (inverse A B e x₀) :=
  (MeasurableEmbedding.subtype_coe hB).measurable_extend
    (measurable_subtype_coe.comp e.symm.measurable) measurable_const

/-- The arbitrary extension still pushes the full original probability
measure to exactly μ. No normalization or exceptional-set approximation. -/
theorem preserving_inverse (μ : Measure X) (ν : Measure Y)
    (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAc : μ Aᶜ=0) (hBc : ν Bᶜ=0) (e : A ≃ᵐ B)
    (he : MeasurePreserving e (μ.comap (Subtype.val : A → X))
      (ν.comap (Subtype.val : B → Y))) (x₀ : X) :
    MeasurePreserving (inverse A B e x₀) ν μ := by
  have hAr : μ.restrict A=μ := Measure.restrict_eq_self_of_ae_mem hAc
  have hBr : ν.restrict B=ν := Measure.restrict_eq_self_of_ae_mem hBc
  have hincA : MeasurePreserving (Subtype.val : A → X) (μ.comap Subtype.val) μ :=
    ⟨measurable_subtype_coe,(map_comap_subtype_coe hA μ).trans hAr⟩
  have hpre := hincA.comp (he.symm e)
  refine ⟨measurable_inverse A B e x₀ hB,?_⟩
  rw [←hBr,←map_comap_subtype_coe hB ν,
    Measure.map_map (measurable_inverse A B e x₀ hB) measurable_subtype_coe]
  have hh : inverse A B e x₀ ∘ (Subtype.val : B → Y)=
      (Subtype.val : A → X) ∘ e.symm := by
    funext y
    exact inverse_coe A B e x₀ y
  rw [hh]
  exact hpre.map_eq

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma invariant_iterates (T : X → X) (A : Set X) (hA : T ⁻¹' A=A) :
    ∀ n, ∀ x∈A,(T^[n]) x∈A := by
  intro n x hx
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact show (T^[n]) x∈T ⁻¹' A from by rw [hA]; exact ih

/-- The total representative intertwines every nonnegative iterate on the
original invariant conull set, not merely as unrelated a.e. identities. -/
theorem inverse_iterates (A : Set X) (B : Set Y) (e : A ≃ᵐ B) (x₀ : X)
    (T : X → X) (S : Y → Y) (hA : T ⁻¹' A=A) (hB : S ⁻¹' B=B)
    (heq : ∀ (x y : A),T x=y → (e y : Y)=S (e x)) :
    ∀ n,∀ y∈B,inverse A B e x₀ ((S^[n]) y)=(T^[n]) (inverse A B e x₀ y) := by
  have hstep (y : B) : inverse A B e x₀ (S y)=T (e.symm y) := by
    let x := e.symm y
    let x' : A := ⟨T x,show (x:X)∈T ⁻¹' A from by rw [hA]; exact x.property⟩
    have hey : (e x' : Y)=S y := by
      have hh := heq x x' rfl
      simpa [x] using hh
    rw [←hey,inverse_coe]
    simp [x',x]
  intro n y hy
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    let y' : B := ⟨(S^[n]) y,invariant_iterates S B hB n y hy⟩
    have ht := hstep y'
    rw [←inverse_coe A B e x₀ y'] at ht
    exact ht.trans (congrArg T ih)

/-- Faithful observation transport supplied by the literal conull conjugacy.
In particular ALL finite name distributions can be pushed through r. -/
theorem from_conjugate (μ : Measure X) (ν : Measure Y) (T : X → X) (S : Y → Y)
    (h : SmoothObstruction.ConullConjugate μ T ν S) (x₀ : X) :
    ∃ r : Y → X,MeasurePreserving r ν μ ∧
      ∃ B : Set Y,MeasurableSet B ∧ ν Bᶜ=0 ∧ S ⁻¹' B=B ∧
        ∀ n,∀ y∈B,r ((S^[n]) y)=(T^[n]) (r y) := by
  obtain ⟨A,B,hA,hB,hAc,hBc,hTA,hSB,e,he,heq⟩ := h
  exact ⟨inverse A B e x₀,preserving_inverse μ ν A B hA hB hAc hBc e he x₀,
    B,hB,hBc,hSB,inverse_iterates A B e x₀ T S hTA hSB heq⟩
end SmoothObstruction.ConullTransport

namespace SmoothObstruction.ConullTransport
open MeasureTheory Set
variable {X Y : Type*}

lemma invariant_inverse (S : Y ≃ Y) (B : Set Y) (hB : S ⁻¹' B=B) :
    S.symm ⁻¹' B=B := by
  ext y
  have hh := congrArg (fun A : Set Y => S.symm y∈A) hB
  simpa only [Set.mem_preimage,S.apply_symm_apply] using hh.symm.to_iff

/-- The same original invariant conull set supports both time directions.
No countable collection of unrelated a.e. conjugacies is substituted. -/
theorem inverse_time (r : Y → X) (T : X ≃ X) (S : Y ≃ Y)
    (B : Set Y) (hB : S ⁻¹' B=B)
    (h : ∀ n,∀ y∈B,r ((S^[n]) y)=(T^[n]) (r y)) :
    ∀ n,∀ y∈B,r ((S.symm^[n]) y)=(T.symm^[n]) (r y) := by
  have hBinv := invariant_inverse S B hB
  have hstep (y : Y) (hy : y∈B) : r (S.symm y)=T.symm (r y) := by
    have hy' : S.symm y∈B := by
      change y∈S.symm ⁻¹' B
      rwa [hBinv]
    have hh := h 1 (S.symm y) hy'
    simp only [Function.iterate_one,S.apply_symm_apply] at hh
    simpa only [T.symm_apply_apply] using (congrArg T.symm hh).symm
  intro n y hy
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',
      hstep _ (invariant_iterates S.symm B hBinv n y hy),ih]

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- Faithful bilateral observation transport from the literal main's
conjugacy, including the invariant-conull and exact law clauses. -/
theorem from_conjugate_bilateral (μ : Measure X) (ν : Measure Y)
    (T : X ≃ X) (S : Y ≃ Y) (h : SmoothObstruction.ConullConjugate μ T ν S) (x₀ : X) :
    ∃ r : Y → X,MeasurePreserving r ν μ ∧
      ∃ B : Set Y,MeasurableSet B ∧ ν Bᶜ=0 ∧ S ⁻¹' B=B ∧ S.symm ⁻¹' B=B ∧
        (∀ n,∀ y∈B,r ((S^[n]) y)=(T^[n]) (r y)) ∧
        (∀ n,∀ y∈B,r ((S.symm^[n]) y)=(T.symm^[n]) (r y)) := by
  obtain ⟨r,hr,B,hB,hBc,hSB,he⟩ := from_conjugate μ ν T S h x₀
  exact ⟨r,hr,B,hB,hBc,hSB,invariant_inverse S B hSB,he,inverse_time r T S B hSB he⟩
end SmoothObstruction.ConullTransport

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_DensityBounds
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ChartDomination
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma measurable_coordinateSet (e : X → E) (r : E → X)
    (he : Measurable e) (hr : Measurable r) (G : Set X) (hG : MeasurableSet G) :
    MeasurableSet (coordinateSet e r G) :=
  (hG.preimage hr).inter (measurableSet_eq_fun (he.comp hr) measurable_id)

omit [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma coordinateSet_eq_image (e : X → E) (r : E → X) (G : Set X)
    (hleft : ∀ x ∈ G, r (e x) = x) : coordinateSet e r G = e '' G := by
  ext u
  constructor
  · rintro ⟨hu,heq⟩
    exact ⟨r u,hu,heq⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨by rwa [hleft x hx],congrArg e (hleft x hx)⟩

/-- Restricting an ORIGINAL measure before taking chart coordinates is
exactly restriction to the coordinate image, not conditioning on it. The
chart inverse is required only on the full original carrier Q. -/
theorem map_restrict_coordinateSet (μ : Measure X)
    (Q G : Set X) (hQ : μ Qᶜ = 0)
    (e : X → E) (r : E → X) (he : Measurable e) (hr : Measurable r)
    (hG : MeasurableSet G) (hleft : ∀ x ∈ Q, r (e x) = x) :
    (μ.restrict G).map e = (μ.map e).restrict (coordinateSet e r G) := by
  have hs := measurable_coordinateSet e r he hr G hG
  have hsets : G =ᵐ[μ] e ⁻¹' coordinateSet e r G := by
    filter_upwards [show ∀ᵐ x ∂μ,x∈Q from hQ] with x hx
    apply propext
    change (x∈G ↔ r (e x)∈G ∧ e (r (e x))=e x)
    rw [hleft x hx]
    simp
  rw [Measure.restrict_congr_set hsets]
  exact (Measure.restrict_map he hs).symm

end SmoothObstruction.ChartDomination

namespace SmoothObstruction.ChartDensity
open Set MeasureTheory Filter Topology
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma measurable_target (hclosed : IsClosed (range I)) (a : M) :
    MeasurableSet (extChartAt I a).target := by
  rw [extChartAt_target]
  exact ((chartAt H a).open_target.preimage I.continuous_symm).measurableSet.inter
    hclosed.measurableSet

lemma measurable_coordinates (a : M) : Measurable (coordinates I a) := by
  classical
  exact (continuousOn_extChartAt a).measurable_piecewise continuous_const.continuousOn
    (by rw [extChartAt_source]; exact (chartAt H a).open_source.measurableSet)

lemma measurable_inverse (hclosed : IsClosed (range I)) (a : M) :
    Measurable (inverse I a) := by
  classical
  exact (continuousOn_extChartAt_symm a).measurable_piecewise
    continuous_const.continuousOn (measurable_target I hclosed a)

omit [MeasurableSpace M] [BorelSpace M] in
lemma coordinates_eq (a x : M) (hx : x∈(extChartAt I a).source) :
    coordinates I a x=extChartAt I a x := by
  classical
  exact ite_eq_left hx

omit [MeasurableSpace M] [BorelSpace M] in
lemma inverse_eq (a : M) (u : EuclideanSpace ℝ (Fin d))
    (hu : u∈(extChartAt I a).target) : inverse I a u=(extChartAt I a).symm u := by
  classical
  exact ite_eq_left hu

omit [MeasurableSpace M] [BorelSpace M] in
lemma inverse_coordinates (a x : M) (hx : x∈(extChartAt I a).source) :
    inverse I a (coordinates I a x)=x := by
  rw [coordinates_eq I a x hx,inverse_eq I a _ ((extChartAt I a).map_source hx)]
  exact (extChartAt I a).left_inv hx

/-- Coordinates for each ORIGINAL measurable subcell carry precisely its chart
Lebesgue density, without conditioning on the cell or on a good set. All maps
have measurable total extensions; their arbitrary values off the chart are
irrelevant to the equality. -/
theorem cell_density (hclosed : IsClosed (range I)) (μ : Measure M)
    (hμ : SmoothPositiveDensity I μ) (a : M) :
    ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiffOn ℝ ∞ f (extChartAt I a).target ∧
      (∀ u∈(extChartAt I a).target,0<f u) ∧
      ∀ Q : Set M,MeasurableSet Q → Q⊆(extChartAt I a).source →
        let W := ChartDomination.coordinateSet (coordinates I a) (inverse I a) Q
        Measurable (W.indicator (fun u => ENNReal.ofReal (f u))) ∧
        (μ.restrict Q).map (coordinates I a)=
          volume.withDensity (W.indicator (fun u => ENNReal.ofReal (f u))) := by
  classical
  obtain ⟨f,hf,hpos,hmap⟩ := hμ a
  refine ⟨f,hf,hpos,fun Q hQ hQsrc => ?_⟩
  let e := coordinates I a
  let r := inverse I a
  let V := (extChartAt I a).target
  let U := (extChartAt I a).source
  let W := ChartDomination.coordinateSet e r Q
  have he : Measurable e := measurable_coordinates I a
  have hr : Measurable r := measurable_inverse I hclosed a
  have hV : MeasurableSet V := measurable_target I hclosed a
  have hU : MeasurableSet U := by
    rw [show U=(chartAt H a).source from extChartAt_source I a]
    exact (chartAt H a).open_source.measurableSet
  have hW : MeasurableSet W := ChartDomination.measurable_coordinateSet e r he hr Q hQ
  have himage : W=e '' Q := ChartDomination.coordinateSet_eq_image e r Q
    (fun x hx => inverse_coordinates I a x (hQsrc hx))
  have hWV : W⊆V := by
    rw [himage]
    rintro u ⟨x,hx,rfl⟩
    rw [show e x=extChartAt I a x from coordinates_eq I a x (hQsrc hx)]
    exact (extChartAt I a).map_source (hQsrc hx)
  have hd : Measurable (W.indicator (fun u => ENNReal.ofReal (f u))) := by
    have hh : Measurable (W.piecewise f (fun _ => (0:ℝ))) :=
      (hf.continuousOn.mono hWV).measurable_piecewise
        continuous_const.continuousOn hW
    have hh' := hh.ennreal_ofReal
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    by_cases hu : u∈W <;> simp [Set.indicator,Set.piecewise,hu]
  refine ⟨hd,?_⟩
  have hemap : (μ.restrict U).map e=(volume.withDensity (fun u => ENNReal.ofReal (f u))).restrict V := by
    rw [←hmap]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hU] with x hx
    exact coordinates_eq I a x hx
  have hfull : (μ.restrict U) Uᶜ=0 := by
    rw [Measure.restrict_apply hU.compl,compl_inter_self,measure_empty]
  have hm := ChartDomination.map_restrict_coordinateSet (μ.restrict U) U Q hfull
    e r he hr hQ (fun x hx => inverse_coordinates I a x hx)
  rw [Measure.restrict_restrict hQ,inter_eq_left.mpr hQsrc,hemap,
    Measure.restrict_restrict hW,inter_eq_left.mpr hWV] at hm
  rw [hm,restrict_withDensity hW,←withDensity_indicator hW]
end SmoothObstruction.ChartDensity

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_BoundaryDensity
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.HalfspaceCollar
open Set MeasureTheory Metric
open scoped ENNReal Manifold

/-- Positive normal coordinate margin keeps the entire nonlinear tube in
 the original half-space. No extension across the boundary is used. -/
theorem closedBall_interior {d : ℕ} [NeZero d] (x : EuclideanSpace ℝ (Fin d))
    {δ : ℝ} (hx : δ<x 0) : closedBall x δ⊆interior (Set.range (𝓡∂ d)) := by
  intro y hy
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  have hh := PiLp.norm_apply_le (y-x) 0
  have hd : ‖y-x‖≤δ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  change 0<y 0
  simp only [PiLp.sub_apply,Real.norm_eq_abs] at hh
  have h := (abs_le.mp (hh.trans hd)).1
  linarith

/-- The elementary quantitative codimension-one collar bound. Merely
knowing that the boundary is null would not imply the simultaneous
`[-n,n]` retained-mass estimate required in smooth switching. -/
theorem slab_volume_le {d : ℕ} (j : Fin d) (R ε : ℝ) :
    volume {x : EuclideanSpace ℝ (Fin d) | ‖x‖≤R ∧ 0≤x j ∧ x j≤ε}≤
      ENNReal.ofReal ε*(ENNReal.ofReal (2*R))^(d-1) := by
  classical
  let a : Fin d → ℝ := fun i => if i=j then 0 else -R
  let b : Fin d → ℝ := fun i => if i=j then ε else R
  have hsub : {x : EuclideanSpace ℝ (Fin d) | ‖x‖≤R ∧ 0≤x j ∧ x j≤ε}⊆
      WithLp.ofLp ⁻¹' Icc a b := by
    intro x hx
    constructor <;> intro i
    · by_cases hi : i=j
      · simpa [a,hi] using hx.2.1
      · have hh := (abs_le.mp ((PiLp.norm_apply_le x i).trans hx.1)).1
        simpa only [a,ite_eq_right hi] using hh
    · by_cases hi : i=j
      · simpa [b,hi] using hx.2.2
      · have hh := (abs_le.mp ((PiLp.norm_apply_le x i).trans hx.1)).2
        simpa only [b,ite_eq_right hi] using hh
  calc
    _ ≤ volume (WithLp.ofLp ⁻¹' Icc a b) := measure_mono hsub
    _ = ∏ i,ENNReal.ofReal (b i-a i) := by
      rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage measurableSet_Icc.nullMeasurableSet,
        Real.volume_Icc_pi]
    _ = ENNReal.ofReal ε*(ENNReal.ofReal (2*R))^(d-1) := by
      rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      have he : ∀ i∈Finset.univ.erase j,ENNReal.ofReal (b i-a i)=ENNReal.ofReal (2*R) := by
        intro i hi
        have hj : i≠j := (Finset.mem_erase.mp hi).1
        simp only [a,b,ite_eq_right hj,sub_neg_eq_add,←two_mul]
      rw [Finset.prod_congr rfl he]
      simp [a,b,Finset.card_erase_of_mem]

end SmoothObstruction.HalfspaceCollar

namespace SmoothObstruction.HalfspaceCollar
open Set MeasureTheory Metric
open scoped ENNReal

/-- A bounded ORIGINAL chart density supported in a bounded patch retains
 the linear collar bound; the density is neither renormalized nor replaced
 by a uniform conditional law. -/
theorem supported_density_slab {d : ℕ} (j : Fin d) (R ε : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (A : ℝ≥0∞)
    (hf : ∀ x,f x≤A) (hzero : ∀ x,R<‖x‖ → f x=0) :
    (volume.withDensity f) {x | 0≤x j ∧ x j≤ε}≤
      A*(ENNReal.ofReal ε*(ENNReal.ofReal (2*R))^(d-1)) := by
  classical
  have hdom : volume.withDensity f≤
      volume.withDensity ((closedBall (0 : EuclideanSpace ℝ (Fin d)) R).indicator (fun _ => A)) := by
    apply withDensity_mono
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x∈closedBall (0 : EuclideanSpace ℝ (Fin d)) R
    · simpa only [indicator_of_mem hx] using hf x
    · rw [indicator_of_notMem hx,hzero x (by simpa only [mem_closedBall_zero_iff,not_le] using hx)]
  rw [withDensity_indicator isClosed_closedBall.measurableSet,withDensity_const] at hdom
  have hs : MeasurableSet {x : EuclideanSpace ℝ (Fin d) | 0≤x j ∧ x j≤ε} := by
    exact (measurableSet_le measurable_const (show Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) by fun_prop)).inter
      (measurableSet_le (show Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) by fun_prop) measurable_const)
  calc
    _ ≤ (A • volume.restrict (closedBall (0 : EuclideanSpace ℝ (Fin d)) R)) {x | 0≤x j ∧ x j≤ε} :=
      hdom _
    _ = A*volume {x : EuclideanSpace ℝ (Fin d) | ‖x‖≤R ∧ 0≤x j ∧ x j≤ε} := by
      rw [Measure.smul_apply,Measure.restrict_apply hs]
      change A * volume (_ ∩ _) = A * volume _
      congr 1
      congr 1
      ext x
      simp only [mem_inter_iff,mem_ofPred_eq,mem_closedBall_zero_iff]
      tauto
    _ ≤ _ := by gcongr; exact slab_volume_le j R ε
end SmoothObstruction.HalfspaceCollar

namespace SmoothObstruction.ChartDensity
open Set MeasureTheory Metric
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]

/-- Quantitative collar estimate in an authentic compact coordinate patch.
The measure is the original smooth measure restricted to that patch. -/
theorem compact_chart_slab (hclosed : IsClosed (range I)) (μ : Measure M)
    (hμ : SmoothPositiveDensity I μ) (a : M) (K : Set M) (hK : IsCompact K)
    (hKU : K⊆(extChartAt I a).source) (j : Fin d) :
    ∃ R A : ℝ,0<R ∧ 0<A ∧ ∀ ε : ℝ,
      μ {x | x∈K ∧ 0 ≤ coordinates I a x j ∧ coordinates I a x j≤ε}≤
        ENNReal.ofReal A*(ENNReal.ofReal ε*(ENNReal.ofReal (2*R))^(d-1)) := by
  classical
  obtain ⟨f,hf,_,hcell⟩ := cell_density I hclosed μ hμ a
  have hKm : MeasurableSet K := hK.measurableSet
  obtain ⟨_,hmap⟩ := hcell K hKm hKU
  let e := coordinates I a
  let W := ChartDomination.coordinateSet e (inverse I a) K
  have him : W=(extChartAt I a) '' K := by
    change ChartDomination.coordinateSet e (inverse I a) K=_
    rw [ChartDomination.coordinateSet_eq_image e (inverse I a) K
      (fun x hx => inverse_coordinates I a x (hKU hx))]
    apply image_congr
    intro x hx
    exact coordinates_eq I a x (hKU hx)
  have hW : IsCompact W := by
    rw [him]
    exact hK.image_of_continuousOn ((continuousOn_extChartAt a).mono hKU)
  have hWV : W⊆(extChartAt I a).target := by
    rw [him]
    rintro u ⟨x,hx,rfl⟩
    exact (extChartAt I a).map_source (hKU hx)
  obtain ⟨R₀,hR₀⟩ := hW.bddAbove_image continuous_norm.continuousOn
  obtain ⟨A₀,hA₀⟩ := hW.bddAbove_image (hf.continuousOn.mono hWV)
  let R := max R₀ 0+1
  let A := max A₀ 0+1
  have hR : 0<R := by dsimp [R]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  have hnorm (u) (hu : u∈W) : ‖u‖≤R := by
    have hh := hR₀ (mem_image_of_mem (fun u => ‖u‖) hu)
    exact hh.trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  have hbound (u) (hu : u∈W) : f u≤A := by
    have hh := hA₀ (mem_image_of_mem f hu)
    exact hh.trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  refine ⟨R,A,hR,hA,fun ε => ?_⟩
  let V : Set (EuclideanSpace ℝ (Fin d)) := {u | 0≤u j ∧ u j≤ε}
  have hV : MeasurableSet V :=
    (measurableSet_le measurable_const (show Measurable (fun u : EuclideanSpace ℝ (Fin d) => u j) by fun_prop)).inter
      (measurableSet_le (show Measurable (fun u : EuclideanSpace ℝ (Fin d) => u j) by fun_prop) measurable_const)
  have he : Measurable e := measurable_coordinates I a
  have hid : μ {x | x∈K ∧ 0≤e x j ∧ e x j≤ε} =
      ((μ.restrict K).map e) V := by
    rw [Measure.map_apply he hV,Measure.restrict_apply (hV.preimage he)]
    congr 1
    ext x
    simp only [mem_ofPred_eq,mem_inter_iff,mem_preimage,V]
    tauto
  rw [hid,hmap]
  apply HalfspaceCollar.supported_density_slab j R ε
  · intro u
    change W.indicator (fun u => ENNReal.ofReal (f u)) u≤ENNReal.ofReal A
    by_cases hu : u∈W
    · simpa only [indicator_of_mem hu] using ENNReal.ofReal_le_ofReal (hbound u hu)
    · simp only [indicator_of_notMem hu,zero_le]
  · intro u hu
    exact indicator_of_notMem (fun hw => (not_lt_of_ge (hnorm u hw)) hu) _
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.ChartDensity
open Set MeasureTheory Metric
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} [NeZero d]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanHalfSpace d) M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]

/-- A GLOBAL quantitative boundary exclusion from the given original
positive smooth density and authentic finite compact atlas. The same set
works for every selected chart containing the point; its mass is O(δ), not
merely o(1), so all 2n+1 tests can be charged to invariant volume. -/
theorem global_halfspace_collar (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : SmoothPositiveDensity (𝓡∂ d) μ) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt (EuclideanHalfSpace d) (a i)).source) :
    ∃ C : ℝ,0<C ∧ ∀ δ : ℝ,0≤δ →
      ∃ W : Set M,MeasurableSet W ∧ μ.real W≤C*δ ∧
        ∀ i x,x∈K i → x∉W →
          closedBall ((extChartAt (𝓡∂ d) (a i)) x) δ⊆interior (range (𝓡∂ d)) := by
  classical
  have hclosed : IsClosed (range (𝓡∂ d)) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact isClosed_le continuous_const (by fun_prop)
  have hs (i : ι) := compact_chart_slab (𝓡∂ d) hclosed μ hμ (a i) (K i) (hK i)
    (by simpa only [extChartAt_source] using hKU i) (0 : Fin d)
  choose R A hR hA hm using hs
  let D (i : ι) := A i*(2*R i)^(d-1)
  let C := (∑ i,D i)+1
  have hD (i : ι) : 0≤D i := by exact mul_nonneg (hA i).le (pow_nonneg (by linarith [hR i]) _)
  have hC : 0<C := by have := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => hD i); dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro δ hδ
  let V (i : ι) : Set M := {x | x∈K i ∧ 0 ≤ coordinates (𝓡∂ d) (a i) x 0 ∧
    coordinates (𝓡∂ d) (a i) x 0≤δ}
  let W := ⋃ i,V i
  have hV (i : ι) : MeasurableSet (V i) := by
    have hf : Measurable (fun x => coordinates (𝓡∂ d) (a i) x 0) := by
      exact (show Measurable (fun u : EuclideanSpace ℝ (Fin d) => u 0) by fun_prop).comp (measurable_coordinates (𝓡∂ d) (a i))
    exact (hK i).measurableSet.inter ((measurableSet_le measurable_const hf).inter
      (measurableSet_le hf measurable_const))
  have hVm (i : ι) : μ (V i)≤ENNReal.ofReal (D i*δ) := by
    have hh := hm i δ
    have he : ENNReal.ofReal (A i)*(ENNReal.ofReal δ*(ENNReal.ofReal (2*R i))^(d-1))=
        ENNReal.ofReal (D i*δ) := by
      rw [ENNReal.ofReal_mul (hD i),ENNReal.ofReal_mul (hA i).le,ENNReal.ofReal_pow (by linarith [hR i])]
      ring
    exact hh.trans_eq he
  have hWm : μ W≤ENNReal.ofReal (C*δ) := by
    calc
      μ W ≤ ∑ i,μ (V i) := by simpa only [tsum_fintype] using measure_iUnion_le (μ:=μ) V
      _ ≤ ∑ i,ENNReal.ofReal (D i*δ) := Finset.sum_le_sum (fun i _ => hVm i)
      _ = ENNReal.ofReal ((∑ i,D i)*δ) := by
        rw [Finset.sum_mul,ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hD i) hδ)]
      _ ≤ ENNReal.ofReal (C*δ) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hδ)
  refine ⟨W,MeasurableSet.iUnion hV,?_,?_⟩
  · exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hWm).trans_eq (ENNReal.toReal_ofReal (mul_nonneg hC.le hδ))
  · intro i x hx hxW
    have hxs : x∈(extChartAt (𝓡∂ d) (a i)).source := by simpa only [extChartAt_source] using hKU i hx
    have hxrange := (extChartAt (𝓡∂ d) (a i)).map_source hxs
    rw [extChartAt,OpenPartialHomeomorph.extend_target] at hxrange
    have hxnonneg : 0≤(extChartAt (𝓡∂ d) (a i) x) 0 := by
      have hh := hxrange.2
      rw [range_modelWithCornersEuclideanHalfSpace] at hh
      exact hh
    have hxnot : x∉V i := fun hh => hxW (mem_iUnion.mpr ⟨i,hh⟩)
    apply HalfspaceCollar.closedBall_interior
    by_contra hle
    apply hxnot
    refine ⟨hx,?_,?_⟩ <;> rw [coordinates_eq (𝓡∂ d) _ _ hxs]
    · exact hxnonneg
    · exact le_of_not_gt hle
end SmoothObstruction.ChartDensity

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ShearGauge
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix

namespace SmoothObstruction.FiniteShears

lemma forward_succ (q : ℝ) (f : ℕ → ℝ) (t : ℕ) :
    forward q f (t + 1) = q * forward q f t + f t := by
  simp only [forward, sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjt : j < t := mem_range.mp hj
  rw [show t - j = (t - 1 - j) + 1 by omega, pow_succ]
  ring

lemma forward_bound {q M : ℝ} (hq : 0 ≤ q) (hq₁ : q ≤ 1)
    (f : ℕ → ℝ) (t : ℕ) (hf : ∀ j < t, |f j| ≤ M) :
    |forward q f t| ≤ t * M := by
  calc
    _ ≤ ∑ j ∈ range t, |q ^ (t - 1 - j) * f j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range t, M := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (pow_nonneg hq _)]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hq hq₁) (abs_nonneg _)).trans
        (by simpa using hf j (mem_range.mp hj))
    _ = _ := by simp

lemma backward_succ (N : ℕ) {q : ℝ} (hq : q ≠ 0) (f : ℕ → ℝ)
    (t : ℕ) (ht : t < N) :
    backward N q f (t + 1) = q * backward N q f t + f t := by
  have hn : N - t = (N - (t + 1)) + 1 := by omega
  have ht' : N - 1 - (N - (t + 1)) = t := by omega
  unfold backward
  rw [hn, forward_succ, ht']
  field_simp
  ring

lemma backward_bound (N : ℕ) {q M : ℝ} (hq : 1 ≤ q) (hM : 0 ≤ M)
    (f : ℕ → ℝ) (t : ℕ) (hf : ∀ j < N, |f j| ≤ M) :
    |backward N q f t| ≤ N * M := by
  have hq₀ : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqi : 0 ≤ q⁻¹ := inv_nonneg.mpr hq₀.le
  have hqi₁ : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  by_cases ht : t ≤ N
  · have hbound := forward_bound hqi hqi₁ (fun j => f (N - 1 - j)) (N - t)
      (fun j hj => hf _ (by omega))
    calc
      _ = q⁻¹ * |forward q⁻¹ (fun j => f (N - 1 - j)) (N - t)| := by
        rw [backward, abs_mul, abs_neg, abs_of_nonneg hqi]
      _ ≤ (1 : ℝ) * ((N - t : ℕ) * M) := mul_le_mul hqi₁ hbound (abs_nonneg _) (by positivity)
      _ ≤ N * M := by
        simp only [one_mul]
        apply mul_le_mul_of_nonneg_right _ hM
        exact_mod_cast Nat.sub_le N t
  · simp only [backward, Nat.sub_eq_zero_of_le (by omega : N ≤ t), forward_zero, mul_zero, abs_zero]
    positivity

/-- The scalar input needed by every elementary shear in the finite
triangular cocycle reduction. This includes q=1; it never divides by q−1. -/
theorem exists_bounded_recurrence (N : ℕ) {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M)
    (f : ℕ → ℝ) (hf : ∀ t < N, |f t| ≤ M) :
    ∃ u : ℕ → ℝ, (∀ t < N, u (t + 1) = q * u t + f t) ∧
      (∀ t ≤ N, |u t| ≤ N * M) := by
  by_cases hq₁ : q ≤ 1
  · refine ⟨forward q f, fun t _ => forward_succ q f t, ?_⟩
    intro t ht
    exact (forward_bound hq.le hq₁ f t (fun j hj => hf j (hj.trans_le ht))).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) hM)
  · exact ⟨backward N q f, fun t ht => backward_succ N hq.ne' f t ht,
      fun t _ => backward_bound N (le_of_lt (lt_of_not_ge hq₁)) hM f t hf⟩

end SmoothObstruction.FiniteShears

namespace SmoothObstruction.TriangularGauge
open SmoothObstruction.FiniteShears

variable {d : ℕ}

lemma mul_rowReplace_same {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsUpperTriangular)
    (U : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) (v : Fin d → ℝ) :
    (A * rowReplace U i v) i j =
      A i i * v j + ∑ k, if i < k then A i k * U k j else 0 := by
  rw [Matrix.mul_apply]
  have hterm (k : Fin d) : A i k * rowReplace U i v k j =
      (if k = i then A i i * v j else 0) + (if i < k then A i k * U k j else 0) := by
    rcases lt_trichotomy k i with hki | rfl | hik
    · simp [rowReplace, ne_of_lt hki, not_lt_of_ge hki.le, hA hki]
    · simp [rowReplace]
    · simp [rowReplace, ne_of_gt hik, hik]
  simp_rw [hterm]
  rw [sum_add_distrib]
  simp

lemma mul_rowReplace_later {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsUpperTriangular)
    (U : Matrix (Fin d) (Fin d) ℝ) (i k j : Fin d) (v : Fin d → ℝ) (hik : i < k) :
    (A * rowReplace U i v) k j = (A * U) k j := by
  simp only [Matrix.mul_apply]
  apply sum_congr rfl
  intro l _
  by_cases hli : l = i
  · subst l
    simp [hA hik]
  · simp [rowReplace, hli]

lemma forcing_zero {U : Matrix (Fin d) (Fin d) ℝ} (hU : U.IsUpperTriangular)
    (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) (hji : j ≤ i) :
    (∑ k, if i < k then A i k * U k j else 0) = 0 := by
  apply sum_eq_zero
  intro k _
  by_cases hik : i < k
  · simp [hik, hU (hji.trans_lt hik)]
  · simp [hik]

lemma forcing_bound (A U : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d)
    {H M : ℝ} (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hA : ∀ k l, |A k l| ≤ H) (hU : ∀ k l, |U k l| ≤ M) :
    |∑ k, if i < k then A i k * U k j else 0| ≤ d * H * M := by
  calc
    _ ≤ ∑ k, |if i < k then A i k * U k j else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, H * M := by
      apply sum_le_sum
      intro k _
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul (hA i k) (hU k j) (abs_nonneg _) hH
      · simp only [abs_zero]
        positivity
    _ = _ := by simp; ring


/-- A full finite-time unitriangular diagonalizing gauge. In contrast to
infinite-time reducibility, this assertion needs no separation of rates.
All losses are fixed-degree polynomials in the length and entry bound. -/
theorem exists_diagonal_gauge (N : ℕ) (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (a : Fin d → ℝ) {H : ℝ} (hH : 1 ≤ H)
    (ha : ∀ j, 0 < a j) (hai : ∀ j, |(a j)⁻¹| ≤ H)
    (htri : ∀ t < N, (A t).IsUpperTriangular)
    (hdiag : ∀ t < N, ∀ j, A t j j = a j)
    (hbound : ∀ t < N, ∀ i j, |A t i j| ≤ H) :
    ∃ U : ℕ → Matrix (Fin d) (Fin d) ℝ,
      (∀ t, (U t).IsUpperTriangular ∧ ∀ j, U t j j = 1) ∧
      (∀ t ≤ N, ∀ i j, |U t i j| ≤ (1 + N * d * H ^ 2) ^ d) ∧
      (∀ t < N, A t * U t = U (t + 1) * Matrix.diagonal a) := by
  classical
  let K : ℝ := 1 + N * d * H ^ 2
  have hK : 1 ≤ K := by
    dsimp [K]
    exact le_add_of_nonneg_right (by positivity)
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hind (r : ℕ) (hr : r ≤ d) :
      ∃ U : ℕ → Matrix (Fin d) (Fin d) ℝ,
        (∀ t, (U t).IsUpperTriangular ∧ ∀ j, U t j j = 1) ∧
        (∀ t ≤ N, ∀ i j, |U t i j| ≤ K ^ r) ∧
        (∀ t < N, ∀ i, d - r ≤ i.val → ∀ j,
          (A t * U t) i j = a j * U (t + 1) i j) := by
    induction r with
    | zero =>
      refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · intro t
        refine ⟨?_, fun j => by simp⟩
        intro i j hji
        change j < i at hji
        simp [ne_of_gt hji]
      · intro t ht i j
        simp only [Matrix.one_apply, pow_zero]
        split_ifs <;> norm_num
      · intro t ht i hi
        simp only [Nat.sub_zero] at hi
        exact (not_le_of_gt i.isLt hi).elim
    | succ r ih =>
      obtain ⟨U, hUtri, hUb, hUeq⟩ := ih (by omega)
      let i : Fin d := ⟨d - (r + 1), by omega⟩
      let M : ℝ := K ^ r
      have hM : 0 ≤ M := pow_nonneg hK₀ r
      let R (j : Fin d) (t : ℕ) : ℝ :=
        ∑ k, if i < k then A t i k * U t k j else 0
      let f (j : Fin d) (t : ℕ) : ℝ := (a j)⁻¹ * R j t
      have hf (j : Fin d) (t : ℕ) (ht : t < N) :
          |f j t| ≤ H * (d * H * M) := by
        change |(a j)⁻¹ * R j t| ≤ _
        rw [abs_mul]
        exact mul_le_mul (hai j)
          (forcing_bound (A t) (U t) i j hH₀ hM (hbound t ht) (hUb t ht.le))
          (abs_nonneg _) hH₀
      have hforce : 0 ≤ H * (d * H * M) := by positivity
      have hrex (j : Fin d) := exists_bounded_recurrence N
        (div_pos (ha i) (ha j)) hforce (f j) (hf j)
      choose u hurec hub using hrex
      let v (t : ℕ) (j : Fin d) : ℝ :=
        if i < j then u j t else if j = i then 1 else 0
      let V (t : ℕ) := rowReplace (U t) i (v t)
      have hKM : K * M = K ^ (r + 1) := by dsimp [M]; rw [pow_succ]; ring
      have hMB : M ≤ K ^ (r + 1) := by
        rw [← hKM]
        exact le_mul_of_one_le_left hM hK
      have hNB : (N : ℝ) * (H * (d * H * M)) ≤ K ^ (r + 1) := by
        rw [← hKM]
        dsimp [K]
        nlinarith
      have hv (t : ℕ) (ht : t ≤ N) (j : Fin d) : |v t j| ≤ K ^ (r + 1) := by
        dsimp [v]
        split_ifs with hij hji
        · exact (hub j t ht).trans hNB
        · simpa using one_le_pow₀ hK
        · simpa using pow_nonneg hK₀ (r + 1)
      refine ⟨V, ?_, ?_, ?_⟩
      · intro t
        constructor
        · intro k j hjk
          change j < k at hjk
          dsimp [V, rowReplace]
          split_ifs with hki
          · subst k
            simp [v, not_lt_of_ge hjk.le, ne_of_lt hjk]
          · exact (hUtri t).1 hjk
        · intro j
          dsimp [V, rowReplace]
          split_ifs with hji
          · subst j
            simp [v]
          · exact (hUtri t).2 j
      · intro t ht k j
        dsimp [V, rowReplace]
        split_ifs
        · exact hv t ht j
        · exact (hUb t ht k j).trans hMB
      · intro t ht k hk j
        by_cases hki : k = i
        · subst k
          rw [show V t = rowReplace (U t) i (v t) from rfl,
            mul_rowReplace_same (htri t ht), hdiag t ht]
          rw [show V (t + 1) i j = v (t + 1) j by simp [V, rowReplace]]
          change a i * v t j + R j t = a j * v (t + 1) j
          by_cases hij : i < j
          · simp only [v, ite_eq_left hij]
            rw [hurec j t ht]
            dsimp [f]
            field_simp [(ha j).ne']
          · have hR : R j t = 0 := forcing_zero (hUtri t).1 (A t) i j (le_of_not_gt hij)
            rw [hR]
            by_cases hji : j = i
            · subst j
              simp [v]
            · simp [v, hij, hji]
        · have hik : i < k := lt_of_le_of_ne hk (Ne.symm hki)
          have hk' : d - r ≤ k.val := by
            have hval : i.val < k.val := hik
            dsimp [i] at hval
            omega
          rw [show V t = rowReplace (U t) i (v t) from rfl,
            mul_rowReplace_later (htri t ht) (U t) i k j (v t) hik,
            hUeq t ht k hk']
          simp [V, rowReplace, hki]
  obtain ⟨U, hUt, hUb, hUeq⟩ := hind d le_rfl
  refine ⟨U, hUt, hUb, ?_⟩
  intro t ht
  ext i j
  rw [Matrix.mul_diagonal]
  exact (hUeq t ht i (by omega) j).trans (mul_comm _ _)

/-- A deliberately coarse finite-dimensional determinant estimate. -/
lemma abs_det_le_entry_bound (A : Matrix (Fin d) (Fin d) ℝ) {B : ℝ}
    (hA : ∀ i j, |A i j| ≤ B) :
    |A.det| ≤ (Nat.factorial d : ℝ) * B ^ d := by
  classical
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin d), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin d), ∏ i, |A (σ i) i| := by
      apply sum_congr rfl
      intro σ _
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        simp [h, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), B ^ d := by
      apply sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _i : Fin d, B := prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _ = _ := by simp
    _ = _ := by simp [Fintype.card_perm]

lemma unitriangular_det {U : Matrix (Fin d) (Fin d) ℝ}
    (ht : U.IsUpperTriangular) (hd : ∀ i, U i i = 1) : U.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [hd]

lemma unitriangular_inverse_bound {U : Matrix (Fin d) (Fin d) ℝ} {B : ℝ}
    (ht : U.IsUpperTriangular) (hd : ∀ i, U i i = 1) (hB : 1 ≤ B)
    (hb : ∀ i j, |U i j| ≤ B) (i j : Fin d) :
    |U⁻¹ i j| ≤ (Nat.factorial d : ℝ) * B ^ d := by
  have hdet := unitriangular_det ht hd
  rw [Matrix.inv_def, hdet]
  simp only [Ring.inverse_one, one_smul, Matrix.adjugate_apply]
  apply abs_det_le_entry_bound _
  intro k l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self, Pi.single_apply]
    split_ifs
    · simpa using hB
    · simpa using (zero_le_one.trans hB)
  · simpa [Matrix.updateRow_ne hk] using hb k l

end SmoothObstruction.TriangularGauge

namespace SmoothObstruction.NormalizedGauge
open SmoothObstruction.TriangularGauge
variable {d : ℕ}

lemma error_succ (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) (j : Fin d) :
    error A lam (t + 1) j = error A lam t j + Real.log (A t j j) - lam j := by
  simp only [error, sum_range_succ]
  ring

lemma normalized_tri (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) (ht : (A t).IsUpperTriangular) :
    (normalized A lam t).IsUpperTriangular := by
  intro i j hji
  simp [normalized, ht hji]

lemma normalized_diag (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) (j : Fin d) (hpos : 0 < A t j j) :
    normalized A lam t j j = Real.exp (lam j) := by
  unfold normalized
  rw [← Real.exp_log hpos, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [error_succ]
  ring

lemma normalized_bound (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) {R E : ℝ}
    (hA : ∀ i j, |A t i j| ≤ Real.exp R)
    (hprev : ∀ j, |error A lam t j| ≤ E)
    (hnext : ∀ j, |error A lam (t + 1) j| ≤ E) (i j : Fin d) :
    |normalized A lam t i j| ≤ Real.exp (R + 2 * E) := by
  have hi : -error A lam (t + 1) i ≤ E := by
    have := (abs_le.mp (hnext i)).1
    linarith
  have hj : error A lam t j ≤ E := le_trans (le_abs_self _) (hprev j)
  calc
    _ = Real.exp (-error A lam (t + 1) i) * |A t i j| * Real.exp (error A lam t j) := by
      simp [normalized, abs_mul]
    _ ≤ Real.exp E * Real.exp R * Real.exp E := by
      gcongr
      exact hA i j
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Diagonal chord normalization followed by a finite bounded shear gauge. -/
theorem exists_normalized_gauge (N : ℕ) (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) {R E : ℝ} (hR : 0 ≤ R) (hE : 0 ≤ E)
    (htri : ∀ t < N, (A t).IsUpperTriangular)
    (hpos : ∀ t < N, ∀ j, 0 < A t j j)
    (hA : ∀ t < N, ∀ i j, |A t i j| ≤ Real.exp R)
    (hlam : ∀ j, |lam j| ≤ R)
    (he : ∀ t ≤ N, ∀ j, |error A lam t j| ≤ E) :
    ∃ C V : ℕ → Matrix (Fin d) (Fin d) ℝ,
      (∀ t, C t * V t = 1 ∧ V t * C t = 1) ∧
      (∀ t ≤ N, ∀ i j, |C t i j| ≤ Real.exp E *
        (1 + N * d * (Real.exp (R + 2 * E)) ^ 2) ^ d) ∧
      (∀ t ≤ N, ∀ i j, |V t i j| ≤ (Nat.factorial d : ℝ) *
        ((1 + N * d * (Real.exp (R + 2 * E)) ^ 2) ^ d) ^ d * Real.exp E) ∧
      (∀ t < N, A t * C t = C (t + 1) * Matrix.diagonal (fun j => Real.exp (lam j))) := by
  let H := Real.exp (R + 2 * E)
  let a := fun j => Real.exp (lam j)
  have hH : 1 ≤ H := Real.one_le_exp_iff.mpr (by positivity)
  have hai (j : Fin d) : |(a j)⁻¹| ≤ H := by
    dsimp [a, H]
    rw [← Real.exp_neg, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hlam j)).1
    linarith
  obtain ⟨U, hUt, hUb, hUeq⟩ := exists_diagonal_gauge N (normalized A lam) a hH
    (fun j => Real.exp_pos _) hai
    (fun t ht => normalized_tri A lam t (htri t ht))
    (fun t ht j => normalized_diag A lam t j (hpos t ht j))
    (fun t ht i j => normalized_bound A lam t (hA t ht)
      (he t ht.le) (he (t + 1) (by omega)) i j)
  let D (t : ℕ) := Matrix.diagonal (fun j => Real.exp (error A lam t j))
  let E' (t : ℕ) := Matrix.diagonal (fun j => Real.exp (-error A lam t j))
  have hDE (t : ℕ) : D t * E' t = 1 := by
    dsimp only [D, E']
    rw [Matrix.diagonal_mul_diagonal]
    simp [← Real.exp_add]
  have hED (t : ℕ) : E' t * D t = 1 := by
    dsimp only [D, E']
    rw [Matrix.diagonal_mul_diagonal]
    simp [← Real.exp_add]
  have hdet (t : ℕ) : IsUnit (U t).det := by
    rw [unitriangular_det (hUt t).1 (hUt t).2]
    exact isUnit_one
  have hnorm (t : ℕ) : A t * D t = D (t + 1) * normalized A lam t := by
    ext i j
    simp only [D, Matrix.mul_diagonal, Matrix.diagonal_mul, normalized]
    rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  refine ⟨fun t => D t * U t, fun t => (U t)⁻¹ * E' t, ?_, ?_, ?_, ?_⟩
  · intro t
    constructor
    · calc
        _ = D t * (U t * (U t)⁻¹) * E' t := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [Matrix.mul_nonsing_inv _ (hdet t), Matrix.mul_one, hDE]
    · calc
        _ = (U t)⁻¹ * (E' t * D t) * U t := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hED, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hdet t)]
  · intro t ht i j
    dsimp only [D]
    rw [Matrix.diagonal_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hUb t ht i j) (abs_nonneg _) (Real.exp_nonneg _)
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (he t ht i))
  · intro t ht i j
    dsimp only [E']
    rw [Matrix.mul_diagonal, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul
      (unitriangular_inverse_bound (hUt t).1 (hUt t).2
        (one_le_pow₀ (le_add_of_nonneg_right (by positivity))) (hUb t ht) i j)
      _ (Real.exp_nonneg _) (by positivity)
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (he t ht j)).1
    linarith
  · intro t ht
    rw [← Matrix.mul_assoc, hnorm, Matrix.mul_assoc, hUeq t ht, ← Matrix.mul_assoc]

lemma gauge_polynomial_le_exp (d N : ℕ) {R E : ℝ} (hR : 0 ≤ R)
    (hE : 1 ≤ E) (hN : (N : ℝ) ≤ Real.exp E) :
    1 + N * d * (Real.exp (R + 2 * E)) ^ 2 ≤
      Real.exp ((2 * R + d + 6) * E) := by
  have hE₀ : 0 ≤ E := zero_le_one.trans hE
  have hd : (d : ℝ) ≤ Real.exp ((d : ℝ) * E) := by
    calc
      (d : ℝ) ≤ Real.exp (d : ℝ) := by linarith [Real.add_one_le_exp (d : ℝ)]
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (by positivity) hE)
  have hH : (Real.exp (R + 2 * E)) ^ 2 ≤ Real.exp ((2 * R + 4) * E) := by
    rw [sq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hT : (0 : ℝ) ≤ (2 * R + d + 5) * E := by positivity
  have hsum : 1 + Real.exp ((2 * R + d + 5) * E) ≤
      Real.exp E * Real.exp ((2 * R + d + 5) * E) := by
    have hone := Real.one_le_exp_iff.mpr hT
    have htwo : (2 : ℝ) ≤ Real.exp E := calc
      2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ _ := Real.exp_le_exp.mpr hE
    nlinarith
  calc
    _ ≤ 1 + Real.exp E * Real.exp ((d : ℝ) * E) * Real.exp ((2 * R + 4) * E) := by
      gcongr
    _ = 1 + Real.exp ((2 * R + d + 5) * E) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := hsum
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Uniform exponential estimates with a constant depending only on d and R.
This is the finite gauge estimate `eq:finite-gauge` before conversion of the
entry norm to the Euclidean operator norm. -/
theorem exists_exponential_gauge (d : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (E : ℝ) (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
      (lam : Fin d → ℝ), 1 ≤ E → Real.log (N + 1) ≤ E →
      (∀ t < N, (A t).IsUpperTriangular) →
      (∀ t < N, ∀ j, 0 < A t j j) →
      (∀ t < N, ∀ i j, |A t i j| ≤ Real.exp R) →
      (∀ j, |lam j| ≤ R) →
      (∀ t ≤ N, ∀ j, |error A lam t j| ≤ E) →
      ∃ U V : ℕ → Matrix (Fin d) (Fin d) ℝ,
        (∀ t, U t * V t = 1 ∧ V t * U t = 1) ∧
        (∀ t ≤ N, ∀ i j, |U t i j| ≤ Real.exp (C * E)) ∧
        (∀ t ≤ N, ∀ i j, |V t i j| ≤ Real.exp (C * E)) ∧
        (∀ t < N, A t * U t = U (t + 1) * Matrix.diagonal (fun j => Real.exp (lam j))) := by
  let c : ℝ := 2 * R + d + 6
  let C : ℝ := 1 + Nat.factorial d + (d + d * d) * c
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N E A lam hE hlog htri hpos hA hlam he
  have hE₀ : 0 ≤ E := zero_le_one.trans hE
  have hN : (N : ℝ) ≤ Real.exp E := by
    calc
      (N : ℝ) ≤ N + 1 := by linarith
      _ = Real.exp (Real.log (N + 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  obtain ⟨U, V, hUV, hUb, hVb, hEq⟩ := exists_normalized_gauge N A lam hR hE₀
    htri hpos hA hlam he
  have hK := gauge_polynomial_le_exp d N hR hE hN
  have hb : 0 ≤ 1 + (N : ℝ) * d * (Real.exp (R + 2 * E)) ^ 2 := by positivity
  have hpow : (1 + (N : ℝ) * d * (Real.exp (R + 2 * E)) ^ 2) ^ d ≤
      Real.exp ((d : ℝ) * c * E) := by
    calc
      _ ≤ (Real.exp (c * E)) ^ d := pow_le_pow_left₀ hb hK d
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hfac : (Nat.factorial d : ℝ) ≤ Real.exp ((Nat.factorial d : ℝ) * E) := by
    calc
      _ ≤ Real.exp (Nat.factorial d : ℝ) := by linarith [Real.add_one_le_exp (Nat.factorial d : ℝ)]
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (by positivity) hE)
  refine ⟨U, V, hUV, ?_, ?_, hEq⟩
  · intro t ht i j
    calc
      _ ≤ _ := hUb t ht i j
      _ ≤ Real.exp E * Real.exp ((d : ℝ) * c * E) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
      _ = Real.exp ((1 + d * c) * E) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        dsimp [C]
        nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) * d by positivity) hc,
          show 0 ≤ (Nat.factorial d : ℝ) by positivity]
  · intro t ht i j
    calc
      _ ≤ _ := hVb t ht i j
      _ ≤ Real.exp ((Nat.factorial d : ℝ) * E) *
          (Real.exp ((d : ℝ) * c * E)) ^ d * Real.exp E := by
        gcongr
      _ = Real.exp (((Nat.factorial d : ℝ) + d * d * c + 1) * E) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        dsimp [C]
        nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) by positivity) hc]

end SmoothObstruction.NormalizedGauge

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_DyadicChord
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators

namespace SmoothObstruction.DyadicChord

lemma prefixSum_add (f : ℕ → ℝ) (n m : ℕ) :
    prefixSum f (n + m) = prefixSum f n + prefixSum (fun j => f (n + j)) m := by
  simp only [prefixSum, sum_range_add]

lemma deviation_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ deviation f n := by
  have h := Finset.le_sup' (fun u => |chord f n u| / n)
    (show 0 ∈ range (n + 1) by simp)
  calc
    0 = |chord f n 0| / n := by simp [chord, prefixSum]
    _ ≤ deviation f n := h

lemma abs_chord_le (f : ℕ → ℝ) {n u : ℕ} (hn : 0 < n) (hu : u ≤ n) :
    |chord f n u| ≤ n * deviation f n := by
  have h := Finset.le_sup' (fun u => |chord f n u| / n)
    (show u ∈ range (n + 1) by simpa using Nat.lt_succ_of_le hu)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have := (div_le_iff₀ hn').mp h
  simpa [deviation, mul_comm] using this

lemma deviation_le (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) {D : ℝ}
    (hD : ∀ u ≤ n, |chord f n u| ≤ n * D) : deviation f n ≤ D := by
  apply Finset.sup'_le
  intro u hu
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
  simpa [mul_comm] using hD u (Nat.le_of_lt_succ (Finset.mem_range.mp hu))

@[simp] lemma deviation_one (f : ℕ → ℝ) : deviation f 1 = 0 := by
  apply le_antisymm _ (deviation_nonneg f 1)
  apply deviation_le f (by omega)
  intro u hu
  interval_cases u <;> simp [chord, average, prefixSum]

lemma average_double (f : ℕ → ℝ) {n : ℕ} (_hn : 0 < n) :
    average f (2 * n) = (average f n + average (fun j => f (n + j)) n) / 2 := by
  rw [show 2 * n = n + n by omega, average, prefixSum_add]
  simp only [Nat.cast_add, average]
  ring

lemma prefixSum_eq (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    prefixSum f n = n * average f n := by
  unfold average
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp

lemma chord_left (f : ℕ → ℝ) (n u : ℕ) :
    chord f (2 * n) u = chord f n u + u * (average f n - average f (2 * n)) := by
  unfold chord
  ring

lemma chord_right (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (u : ℕ) :
    chord f (2 * n) (n + u) = chord (fun j => f (n + j)) n u +
      ((n : ℝ) - u) * (average f n - average f (2 * n)) := by
  simp only [chord, prefixSum_add, Nat.cast_add]
  rw [prefixSum_eq f hn, average_double f hn]
  ring

/-- A deterministic midpoint recurrence for maximal deviation from the
block's own chord. No independence or average mixing hypothesis is used. -/
lemma deviation_double_le (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    deviation f (2 * n) ≤
      (|average f n - average f (2 * n)| +
        max (deviation f n) (deviation (fun j => f (n + j)) n)) / 2 := by
  apply deviation_le f (by omega)
  intro u hu
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  let D := max (deviation f n) (deviation (fun j => f (n + j)) n)
  have hbound_left : ∀ u ≤ n, |chord f (2 * n) u| ≤
      n * (|average f n - average f (2 * n)| + D) := by
    intro v hv
    rw [chord_left]
    calc
      _ ≤ |chord f n v| + |(v : ℝ) * (average f n - average f (2 * n))| := abs_add_le _ _
      _ = |chord f n v| + v * |average f n - average f (2 * n)| := by
        rw [abs_mul, show |(v : ℝ)| = v from abs_of_nonneg (Nat.cast_nonneg v)]
      _ ≤ n * deviation f n + n * |average f n - average f (2 * n)| :=
        add_le_add (abs_chord_le f hn hv)
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hv) (abs_nonneg _))
      _ ≤ n * (|average f n - average f (2 * n)| + D) := by
        have h := mul_le_mul_of_nonneg_left (le_max_left (deviation f n)
          (deviation (fun j => f (n + j)) n)) hn0
        dsimp [D]
        linarith
  have hbound_right : ∀ v ≤ n, |chord f (2 * n) (n + v)| ≤
      n * (|average f n - average f (2 * n)| + D) := by
    intro v hv
    rw [chord_right f hn]
    calc
      _ ≤ |chord (fun j => f (n + j)) n v| +
          |((n : ℝ) - v) * (average f n - average f (2 * n))| := abs_add_le _ _
      _ = |chord (fun j => f (n + j)) n v| +
          ((n : ℝ) - v) * |average f n - average f (2 * n)| := by
        rw [abs_mul, show |(n : ℝ) - v| = (n : ℝ) - v from
          abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hv))]
      _ ≤ n * deviation (fun j => f (n + j)) n + n * |average f n - average f (2 * n)| :=
        add_le_add (abs_chord_le _ hn hv)
          (mul_le_mul_of_nonneg_right (by simp) (abs_nonneg _))
      _ ≤ n * (|average f n - average f (2 * n)| + D) := by
        have h := mul_le_mul_of_nonneg_left (le_max_right (deviation f n)
          (deviation (fun j => f (n + j)) n)) hn0
        dsimp [D]
        linarith
  have h : |chord f (2 * n) u| ≤ n * (|average f n - average f (2 * n)| + D) := by
    by_cases hun : u ≤ n
    · exact hbound_left u hun
    · simpa only [Nat.add_sub_of_le (by omega : n ≤ u)] using
        hbound_right (u - n) (by omega)
  calc
    _ ≤ n * (|average f n - average f (2 * n)| + D) := h
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_ofNat, D]; ring

/-- A rational square version, more convenient for summing the L² energies. -/
lemma deviation_double_sq (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (deviation f (2 * n))^2 ≤
      (3 / 4 : ℝ) * (average f n - average f (2 * n))^2 +
      (3 / 8 : ℝ) * ((deviation f n)^2 + (deviation (fun j => f (n + j)) n)^2) := by
  have h := deviation_double_le f hn
  have h0 := deviation_nonneg f (2 * n)
  have hl := deviation_nonneg f n
  have hr := deviation_nonneg (fun j => f (n + j)) n
  have hd0 : 0 ≤ |average f n - average f (2 * n)| := abs_nonneg _
  have hsq := sq_abs (average f n - average f (2 * n))
  rcases le_total (deviation f n) (deviation (fun j => f (n + j)) n) with hh | hh
  · rw [max_eq_right hh] at h
    nlinarith [sq_nonneg (|average f n - average f (2 * n)| - deviation (fun j => f (n + j)) n / 2),
      sq_nonneg (deviation f n)]
  · rw [max_eq_left hh] at h
    nlinarith [sq_nonneg (|average f n - average f (2 * n)| - deviation f n / 2),
      sq_nonneg (deviation (fun j => f (n + j)) n)]

end SmoothObstruction.DyadicChord

namespace SmoothObstruction.DyadicChord

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma prefixSum_memLp {Y : ℕ → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) (n : ℕ) :
    MemLp (fun x => prefixSum (fun j => Y j x) n) 2 μ := by
  exact memLp_finsetSum _ (fun j _ => hY j)

lemma average_memLp {Y : ℕ → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) (n : ℕ) :
    MemLp (fun x => average (fun j => Y j x) n) 2 μ := by
  simpa only [average, div_eq_mul_inv] using (prefixSum_memLp hY n).mul_const (n : ℝ)⁻¹

lemma chord_memLp {Y : ℕ → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) (n u : ℕ) :
    MemLp (fun x => chord (fun j => Y j x) n u) 2 μ := by
  exact (prefixSum_memLp hY u).sub ((average_memLp hY n).const_mul u)

lemma deviation_memLp {Y : ℕ → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) (n : ℕ) :
    MemLp (fun x => deviation (fun j => Y j x) n) 2 μ := by
  have h : MemLp ((range (n + 1)).sup' (by simp)
      (fun u x => |chord (fun j => Y j x) n u| / n)) 2 μ := by
    apply Finset.sup'_induction (p := fun g : Ω → ℝ => MemLp g 2 μ) (by simp)
      (fun u x => |chord (fun j => Y j x) n u| / n)
    · intro f hf g hg
      exact hf.sup hg
    · intro u _
      simpa only [Real.norm_eq_abs, div_eq_mul_inv] using
        (chord_memLp hY n u).norm.mul_const (n : ℝ)⁻¹
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact (Finset.sup'_apply (s := range (n + 1)) (by simp)
    (fun u x => |chord (fun j => Y j x) n u| / n) x).symm

omit [MeasurableSpace Ω] in
lemma orbit_shift (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) (n : ℕ) :
    (fun j => orbit T f x (n + j)) = orbit T f (T^[n] x) := by
  funext j
  simp only [orbit, Nat.add_comm n j, Function.iterate_add_apply]

lemma integral_comp_preserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg : Integrable g μ) :
    (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have hgm : AEStronglyMeasurable g (Measure.map T μ) := by
    rw [hT.map_eq]
    exact hg.aestronglyMeasurable
  have h := integral_map hT.measurable.aemeasurable hgm
  rw [hT.map_eq] at h
  exact h.symm

lemma orbit_memLp {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (j : ℕ) : MemLp (fun x => orbit T f x j) 2 μ :=
  hf.comp_measurePreserving (hT.iterate j)

lemma averageEnergy_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) :
    0 ≤ averageEnergy T f μ n := integral_nonneg (fun _ => sq_nonneg _)

lemma deviationEnergy_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) :
    0 ≤ deviationEnergy T f μ n := integral_nonneg (fun _ => sq_nonneg _)

@[simp] lemma deviationEnergy_one (T : Ω → Ω) (f : Ω → ℝ) :
    deviationEnergy T f μ 1 = 0 := by simp [deviationEnergy]

lemma averageEnergy_shift {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (n m : ℕ) :
    (∫ x, (average (fun j => orbit T f x (n + j)) m)^2 ∂μ) = averageEnergy T f μ m := by
  simp only [orbit_shift]
  exact integral_comp_preserving (hT.iterate n) ((average_memLp (orbit_memLp hT hf) m).integrable_sq)

lemma deviationEnergy_shift {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (n m : ℕ) :
    (∫ x, (deviation (fun j => orbit T f x (n + j)) m)^2 ∂μ) = deviationEnergy T f μ m := by
  simp only [orbit_shift]
  exact integral_comp_preserving (hT.iterate n) ((deviation_memLp (orbit_memLp hT hf) m).integrable_sq)

/-- The midpoint square is exactly the drop in the average's second moment.
This identity uses only stationarity of the right half. -/
lemma midpoint_energy {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) {n : ℕ} (hn : 0 < n) :
    (∫ x, (average (orbit T f x) n - average (orbit T f x) (2 * n))^2 ∂μ) =
      averageEnergy T f μ n - averageEnergy T f μ (2 * n) := by
  have hL : Integrable (fun x => (average (orbit T f x) n)^2) μ :=
    (average_memLp (orbit_memLp hT hf) n).integrable_sq
  have hR : Integrable (fun x => (average (fun j => orbit T f x (n + j)) n)^2) μ :=
    (average_memLp (fun j => orbit_memLp hT hf (n + j)) n).integrable_sq
  have hW : Integrable (fun x => (average (orbit T f x) (2 * n))^2) μ :=
    (average_memLp (orbit_memLp hT hf) (2 * n)).integrable_sq
  calc
    _ = ∫ x, (((average (orbit T f x) n)^2 +
        (average (fun j => orbit T f x (n + j)) n)^2) / 2 -
        (average (orbit T f x) (2 * n))^2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [average_double _ hn]
      ring
    _ = (averageEnergy T f μ n + averageEnergy T f μ n) / 2 -
        averageEnergy T f μ (2 * n) := by
      have hadd : Integrable (fun x => ((average (orbit T f x) n)^2 +
          (average (fun j => orbit T f x (n + j)) n)^2) / 2) μ := (hL.add hR).div_const 2
      rw [integral_sub hadd hW, integral_div,
        integral_add hL hR, averageEnergy_shift hT hf]
      rfl
    _ = _ := by ring

lemma deviationEnergy_double {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) {n : ℕ} (hn : 0 < n) :
    deviationEnergy T f μ (2 * n) ≤
      (3 / 4 : ℝ) * (averageEnergy T f μ n - averageEnergy T f μ (2 * n)) +
      (3 / 4 : ℝ) * deviationEnergy T f μ n := by
  have hL : Integrable (fun x => (deviation (orbit T f x) n)^2) μ :=
    (deviation_memLp (orbit_memLp hT hf) n).integrable_sq
  have hR : Integrable (fun x => (deviation (fun j => orbit T f x (n + j)) n)^2) μ :=
    (deviation_memLp (fun j => orbit_memLp hT hf (n + j)) n).integrable_sq
  have hM : Integrable (fun x => (average (orbit T f x) n -
      average (orbit T f x) (2 * n))^2) μ :=
    ((average_memLp (orbit_memLp hT hf) n).sub
      (average_memLp (orbit_memLp hT hf) (2 * n))).integrable_sq
  have hW : Integrable (fun x => (deviation (orbit T f x) (2 * n))^2) μ :=
    (deviation_memLp (orbit_memLp hT hf) (2 * n)).integrable_sq
  calc
    _ ≤ ∫ x, (3 / 4 : ℝ) * (average (orbit T f x) n -
          average (orbit T f x) (2 * n))^2 +
        (3 / 8 : ℝ) * ((deviation (orbit T f x) n)^2 +
          (deviation (fun j => orbit T f x (n + j)) n)^2) ∂μ :=
      integral_mono hW ((hM.const_mul _).add ((hL.add hR).const_mul _))
        (fun x => deviation_double_sq (orbit T f x) hn)
    _ = _ := by
      have hadd : Integrable (fun x => (3 / 8 : ℝ) * ((deviation (orbit T f x) n)^2 +
          (deviation (fun j => orbit T f x (n + j)) n)^2)) μ := (hL.add hR).const_mul _
      rw [integral_add (hM.const_mul (3 / 4)) hadd, integral_const_mul,
        integral_const_mul, integral_add hL hR, midpoint_energy hT hf hn,
        deviationEnergy_shift hT hf]
      change (3 / 4 : ℝ) * _ + (3 / 8 : ℝ) * (deviationEnergy T f μ n + _) = _
      ring

end SmoothObstruction.DyadicChord

namespace SmoothObstruction.DyadicChord

/-- A telescoping potential turns the midpoint recurrence into an absolute
summability bound. These constants do not depend on a process or dimension. -/
lemma energy_sum_bound (A Z : ℕ → ℝ) (hA : ∀ h, 0 ≤ A h) (hZ : ∀ h, 0 ≤ Z h)
    (hZ₀ : Z 0 = 0)
    (hrec : ∀ h, Z (h + 1) ≤ (3 / 4 : ℝ) * (A h - A (h + 1)) + (3 / 4 : ℝ) * Z h)
    (N : ℕ) : ∑ h ∈ range N, Z h ≤ 3 * A 0 := by
  have hpot : ∀ n, (∑ h ∈ range n, Z h) + 4 * Z n + 3 * A n ≤ 3 * A 0 := by
    intro n
    induction n with
    | zero => simp [hZ₀]
    | succ n ih =>
      rw [sum_range_succ]
      linarith [hrec n]
  linarith [hpot N, hZ N, hA N]

lemma energy_summable (A Z : ℕ → ℝ) (hA : ∀ h, 0 ≤ A h) (hZ : ∀ h, 0 ≤ Z h)
    (hZ₀ : Z 0 = 0)
    (hrec : ∀ h, Z (h + 1) ≤ (3 / 4 : ℝ) * (A h - A (h + 1)) + (3 / 4 : ℝ) * Z h) :
    Summable Z ∧ ∑' h, Z h ≤ 3 * A 0 := by
  exact ⟨summable_of_sum_range_le hZ (energy_sum_bound A Z hA hZ hZ₀ hrec),
    Real.tsum_le_of_sum_range_le hZ (energy_sum_bound A Z hA hZ hZ₀ hrec)⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The square-summability conclusion of the source dyadic chord lemma, with
an explicit absolute constant 3. The process is recorded as an observable of
a measure-preserving transformation; in particular it covers the compact
orthogonal-frame process required by the smooth switching construction. -/
theorem dyadic_square_summable {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Summable (fun h => deviationEnergy T f μ (2^h)) ∧
      (∑' h, deviationEnergy T f μ (2^h)) ≤ 3 * ∫ x, (f x)^2 ∂μ := by
  have h := energy_summable (fun h => averageEnergy T f μ (2^h))
    (fun h => deviationEnergy T f μ (2^h))
    (fun h => averageEnergy_nonneg T f _) (fun h => deviationEnergy_nonneg T f _)
    (by simp) (fun h => by
      simpa only [pow_succ', Nat.ofNat_pos] using
        deviationEnergy_double hT hf (pow_pos (by omega : 0 < 2) h))
  simpa only [pow_zero, averageEnergy_one] using h

end SmoothObstruction.DyadicChord

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Coordinates
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The genuine derivative in any independently fixed pair of regular
charts, including half-space charts. -/
theorem continuousOn_coord (S : Diffeomorph I I M M ∞) (a b : M) :
    ContinuousOn (coord I S a b) (domain I S a b) := by
  apply continuousOn_clm_apply.mpr
  intro v
  let e := trivializationAt (E (d:=d)) (TangentSpace I) a
  let e' := trivializationAt (E (d:=d)) (TangentSpace I) b
  have hin : ContinuousOn (fun x => TotalSpace.mk' (E (d:=d)) x (e.symm x v)) e.baseSet := by
    exact e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => ⟨hx,mem_univ _⟩)
  have htan := S.contMDiff.continuous_tangentMap (show (1 : ℕ∞ω)≤∞ by simp)
  have hmid := htan.comp_continuousOn hin
  have hout : ContinuousOn (fun x => (e' (tangentMap I I S
      (TotalSpace.mk' (E (d:=d)) x (e.symm x v)))).2) (domain I S a b) := by
    apply (e'.continuousOn.comp (hmid.mono (fun x hx => ?_)) (fun x hx => ?_)).snd
    · simpa only [e,TangentBundle.trivializationAt_baseSet] using hx.1
    · apply e'.mem_source.mpr
      change S x∈(chartAt H b).source
      exact hx.2
  apply hout.congr
  intro x hx
  have h₁ : x∈e.baseSet := by simpa only [e,TangentBundle.trivializationAt_baseSet] using hx.1
  have h₂ : S x∈e'.baseSet := by exact hx.2
  change e'.continuousLinearMapAt ℝ (S x)
    ((mfderiv I I S x) ((e.symmL ℝ x) v))=_
  rw [e.symmL_apply h₁,Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e' h₂]
  rfl


/-- Uniform two-sided derivative bounds on any compact chart-pair patch. -/
theorem bound_on_compact (S : Diffeomorph I I M M ∞) (a b : M)
    {K : Set M} (hK : IsCompact K) (hsub : K⊆domain I S a b) :
    ∃ C : ℝ, 0<C ∧ ∀ x∈K, ‖coord I S a b x‖≤C ∧
      ∀ v, ‖v‖≤C*‖coord I S a b x v‖ := by
  have hc := (continuousOn_coord I S a b).mono hsub
  have hi : ContinuousOn (fun x => Ring.inverse (coord I S a b x)) K := by
    intro x hx
    let : CompleteSpace (E (d:=d) →L[ℝ] E (d:=d)) :=
      ContinuousLinearMap.instCompleteSpace
    have h := NormedRing.inverse_continuousAt (coordEquiv I S a b x (hsub hx)).toUnit
    rw [show ((coordEquiv I S a b x (hsub hx)).toUnit : E (d:=d) →L[ℝ] E (d:=d)) =
      coord I S a b x from coordEquiv_coe I S a b x (hsub hx)] at h
    exact h.comp_continuousWithinAt (hc x hx)
  obtain ⟨C₁,hC₁⟩ := hK.exists_bound_of_continuousOn hc
  obtain ⟨C₂,hC₂⟩ := hK.exists_bound_of_continuousOn hi
  refine ⟨max C₁ (max C₂ 1), lt_of_lt_of_le zero_lt_one (le_max_right C₂ 1 |>.trans (le_max_right _ _)),?_⟩
  intro x hx
  refine ⟨(hC₁ x hx).trans (le_max_left _ _),?_⟩
  intro v
  let e := coordEquiv I S a b x (hsub hx)
  have he : (e.toContinuousLinearMap)=coord I S a b x := coordEquiv_coe I S a b x (hsub hx)
  have hi' : Ring.inverse (coord I S a b x)=e.symm.toContinuousLinearMap := by
    rw [←he]
    exact Ring.inverse_unit e.toUnit
  have hnv := e.symm.toContinuousLinearMap.le_opNorm (e v)
  simp only [ContinuousLinearEquiv.coe_coe,e.symm_apply_apply] at hnv
  rw [←hi'] at hnv
  calc
    ‖v‖≤‖Ring.inverse (coord I S a b x)‖*‖e v‖ := hnv
    _ ≤ max C₁ (max C₂ 1)*‖e v‖ := mul_le_mul_of_nonneg_right
      ((hC₂ x hx).trans ((le_max_left C₂ 1).trans (le_max_right _ _))) (norm_nonneg _)
    _ = max C₁ (max C₂ 1)*‖coord I S a b x v‖ := by rw [←he]; rfl

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.FiniteAtlas
open Set Filter Topology MeasureTheory
universe u
variable {M : Type u} [TopologicalSpace M] [CompactSpace M] [T2Space M]

/-- Compact inner patches covering the whole compact space. This applies to
half-space and nonorientable atlas charts without a global frame. -/
theorem compact_inner_cover (U : M → Set M) (hU : ∀ x,IsOpen (U x))
    (hxU : ∀ x,x∈U x) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → M) (K : ι → Set M),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆U (a i)) ∧ ∀ x,∃ i,x∈K i := by
  choose K hK hKi hKU using fun x => exists_compact_subset (hU x) (hxU x)
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (K x))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.mpr ⟨x,hKi x⟩)
  refine ⟨{x // x∈s},inferInstance,Subtype.val,fun i => K i,fun i => hK i,
    fun i => hKU i,?_⟩
  intro x
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact ⟨⟨i,hi⟩,interior_subset hxi⟩

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace ι]
    

/-- Deterministic measurable choice of the first containing compact patch.
No measurable selection theorem is postulated. -/
theorem measurable_selector (K : ι → Set Ω) (hK : ∀ i,MeasurableSet (K i))
    (hcover : ∀ x,∃ i,x∈K i) :
    ∃ a : Ω → ι,Measurable a ∧ ∀ x,x∈K (a x) := by
  classical
  by_cases hΩ : IsEmpty Ω
  · let := hΩ
    exact ⟨isEmptyElim,measurable_of_empty _,fun x => isEmptyElim x⟩
  have : Nonempty Ω := not_isEmpty_iff.mp hΩ
  have : Nonempty ι := let ⟨i,_⟩ := hcover (Classical.choice inferInstance); ⟨i⟩
  let N := Fintype.card ι
  let e := Fintype.equivFin ι
  let p : Ω → ℕ → Prop := fun x n => ∃ h:n<N,x∈K (e.symm ⟨n,h⟩)
  have hp (x : Ω) : ∃ n,p x n := by
    obtain ⟨i,hi⟩ := hcover x
    exact ⟨(e i).val,⟨(e i).isLt,by simpa using hi⟩⟩
  let k : Ω → ℕ := fun x => Nat.find (hp x)
  have hk : Measurable k := measurable_find hp (fun n => by
    by_cases hn : n<N
    · have he : {x | p x n}=K (e.symm ⟨n,hn⟩) := by
        ext x
        simp only [mem_ofPred_eq,p]
        exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨hn,h⟩⟩
      rw [he]; exact hK _
    · have he : {x | p x n}=∅ := by ext x; simp [p,hn]
      rw [he]; exact MeasurableSet.empty)
  have hkN (x : Ω) : k x<N := (Nat.find_spec (hp x)).choose
  let f : Ω → Fin N := fun x => ⟨k x,hkN x⟩
  have hf : Measurable f := by
    apply measurable_to_countable'
    intro i
    have he : f ⁻¹' {i}={x | k x=i.val} := by
      ext x
      simp [f,Fin.ext_iff]
    rw [he]
    exact measurableSet_eq_fun hk measurable_const
  refine ⟨e.symm ∘ f, (measurable_of_finite e.symm).comp hf,?_⟩
  intro x
  exact (Nat.find_spec (hp x)).choose_spec
end SmoothObstruction.FiniteAtlas

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology MeasureTheory
open scoped Manifold ContDiff
universe u
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- A bounded measurable cocycle of the genuine derivative, in a finite
system of measurable chart regions with compact inner patches. -/
theorem actual_coordinate_cocycle_discrete (S : Diffeomorph I I M M ∞) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : MeasurableSpace ι) (_ : MeasurableSingletonClass ι)
      (a : ι → M) (K : ι → Set M) (c : M → ι) (C : ℝ)
      (A : M → CompactMatrix.Alphabet d C),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆(chartAt H (a i)).source) ∧
      Measurable c ∧ (∀ x,x∈K (c x)) ∧ 0<C ∧ Measurable A ∧
      ∀ x,(A x).val=coord I S (a (c x)) (a (c (S x))) x := by
  classical
  obtain ⟨ι,hfin,a,K,hK,hKU,hcover⟩ := FiniteAtlas.compact_inner_cover
    (fun x : M => (chartAt H x).source) (fun x => (chartAt H x).open_source)
    (fun x => mem_chart_source H x)
  let : Fintype ι := hfin
  let : MeasurableSpace ι := ⊤
  obtain ⟨c,hc,hcK⟩ := FiniteAtlas.measurable_selector K
    (fun i => (hK i).isClosed.measurableSet) hcover
  let L : ι × ι → Set M := fun ij => K ij.1 ∩ S ⁻¹' K ij.2
  have hL (ij : ι × ι) : IsCompact (L ij) :=
    (hK ij.1).inter_right ((hK ij.2).isClosed.preimage S.continuous)
  have hLd (ij : ι × ι) : L ij⊆domain I S (a ij.1) (a ij.2) :=
    fun _ hx => ⟨hKU _ hx.1,hKU _ hx.2⟩
  choose D hDp hD using fun ij => bound_on_compact I S (a ij.1) (a ij.2) (hL ij) (hLd ij)
  let C : ℝ := 1+∑ ij,D ij
  have hDC (ij : ι × ι) : D ij≤C := by
    have hh : D ij≤∑ p,D p := Finset.single_le_sum (fun p _ => (hDp p).le) (Finset.mem_univ ij)
    dsimp only [C]; linarith
  have hCp : 0<C := by
    have hh : 0≤∑ ij,D ij := Finset.sum_nonneg (fun p _ => (hDp p).le)
    dsimp only [C]; linarith
  let f : ι × ι → M → (E (d:=d) →L[ℝ] E (d:=d)) := fun ij =>
    (L ij).piecewise (coord I S (a ij.1) (a ij.2)) 0
  have hf (ij : ι × ι) : Measurable (f ij) :=
    ((continuousOn_coord I S (a ij.1) (a ij.2)).mono (hLd ij)).measurable_piecewise
      continuous_const.continuousOn (hL ij).isClosed.measurableSet
  have hf' : Measurable (fun p : M × (ι × ι) => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  have heval : Measurable (fun x => f (c x,c (S x)) x) :=
    hf'.comp (measurable_id.prodMk (hc.prodMk (hc.comp S.continuous.measurable)))
  have hxe (x : M) : x∈L (c x,c (S x)) := ⟨hcK x,hcK (S x)⟩
  have heq (x : M) : f (c x,c (S x)) x=coord I S (a (c x)) (a (c (S x))) x := by
    exact Set.piecewise_eq_of_mem _ _ _ (hxe x)
  have hb (x : M) : ‖f (c x,c (S x)) x‖≤C ∧ ∀ v,‖v‖≤C*‖f (c x,c (S x)) x v‖ := by
    rw [heq]
    exact ⟨((hD _ x (hxe x)).1).trans (hDC _),fun v =>
      ((hD _ x (hxe x)).2 v).trans (mul_le_mul_of_nonneg_right (hDC _) (norm_nonneg _))⟩
  let A : M → CompactMatrix.Alphabet d C := fun x => ⟨f (c x,c (S x)) x,hb x⟩
  exact ⟨ι,hfin,⊤,inferInstance,a,K,c,C,A,hK,hKU,hc,hcK,hCp,heval.subtype_mk,heq⟩

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_InvariantMeasure
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SmoothObstruction.CompactInvariant

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

lemma integral_iterateLaw (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (j : ℕ) (f : X →ᵇ ℝ) :
    ∫ x, f x ∂(iterateLaw T hT μ j : Measure X) = ∫ x, f ((T^[j]) x) ∂(μ : Measure X) := by
  exact integral_map (hT.iterate j).measurable.aemeasurable f.continuous.aestronglyMeasurable

lemma integral_cesaro (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (n : ℕ) (f : X →ᵇ ℝ) :
    ∫ x, f x ∂(cesaro T hT μ n : Measure X) =
      (∑ j ∈ range (n + 1), ∫ x, f ((T^[j]) x) ∂(μ : Measure X)) / (n + 1) := by
  change (∫ x, f x ∂(((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • _)) = _
  rw [integral_smul_measure, integral_finsetSum_measure (fun j _ => f.integrable _)]
  simp [integral_iterateLaw, ENNReal.toReal_add, div_eq_mul_inv, mul_comm]

lemma cesaro_integral_defect (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (n : ℕ) (f : X →ᵇ ℝ) :
    (∫ x, f (T x) ∂(cesaro T hT μ n : Measure X)) -
      (∫ x, f x ∂(cesaro T hT μ n : Measure X)) =
      ((∫ x, f ((T^[n + 1]) x) ∂(μ : Measure X)) - ∫ x, f x ∂(μ : Measure X)) / (n + 1) := by
  let g : X →ᵇ ℝ := f.compContinuous ⟨T, hT⟩
  change (∫ x, g x ∂(cesaro T hT μ n : Measure X)) - _ = _
  rw [integral_cesaro, integral_cesaro, ← sub_div, ← sum_sub_distrib]
  have heq (j : ℕ) : (∫ x, g ((T^[j]) x) ∂(μ : Measure X)) =
      ∫ x, f ((T^[j + 1]) x) ∂(μ : Measure X) := by
    simp only [g, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
      Function.iterate_succ_apply']
  simp only [heq]
  rw [sum_range_sub (fun j => ∫ x, f ((T^[j]) x) ∂(μ : Measure X))]
  simp

omit [BorelSpace X] in
lemma integral_iterate_bound (μ : ProbabilityMeasure X) (T : X → X)
    (j : ℕ) (f : X →ᵇ ℝ) :
    |∫ x, f ((T^[j]) x) ∂(μ : Measure X)| ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure X))
    (f := fun x => f ((T^[j]) x)) (C := ‖f‖)
    (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm ((T^[j]) x)))
  simpa [Real.norm_eq_abs, measureReal_def] using h

lemma cesaro_integral_defect_bound (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (n : ℕ) (f : X →ᵇ ℝ) :
    |(∫ x, f (T x) ∂(cesaro T hT μ n : Measure X)) -
      (∫ x, f x ∂(cesaro T hT μ n : Measure X))| ≤ 2 * ‖f‖ / (n + 1) := by
  rw [cesaro_integral_defect, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ |∫ x, f ((T^[n + 1]) x) ∂(μ : Measure X)| + |∫ x, f x ∂(μ : Measure X)| := abs_sub _ _
    _ ≤ _ := by
      have h₀ := integral_iterate_bound μ T 0 f
      simp only [Function.iterate_zero, id_eq] at h₀
      linarith [integral_iterate_bound μ T (n + 1) f]

lemma cesaro_integral_defect_tendsto (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (f : X →ᵇ ℝ) :
    Tendsto (fun n => (∫ x, f (T x) ∂(cesaro T hT μ n : Measure X)) -
      (∫ x, f x ∂(cesaro T hT μ n : Measure X))) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun (n : ℕ) => by
    simpa only [Real.norm_eq_abs] using (cesaro_integral_defect_bound T hT μ n f))
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * ‖f‖)
  simpa only [mul_zero, mul_one_div] using h

variable [MetrizableSpace X] [CompactSpace X]

omit [CompactSpace X] in
/-- Any weak limit of the Cesaro orbit averages is invariant. -/
theorem cesaro_limit_invariant (T : X → X) (hT : Continuous T)
    (μ ν : ProbabilityMeasure X) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hlim : Tendsto ((cesaro T hT μ) ∘ φ) atTop (𝓝 ν)) :
    MeasurePreserving T (ν : Measure X) (ν : Measure X) := by
  refine ⟨hT.measurable, ?_⟩
  let ν' := ν.map hT.measurable.aemeasurable
  change (ν' : Measure X) = (ν : Measure X)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [show (ν' : Measure X) = (ν : Measure X).map T from rfl,
    integral_map hT.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  let g : X →ᵇ ℝ := f.compContinuous ⟨T, hT⟩
  have hg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim g)
  have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim f)
  have hzero := (cesaro_integral_defect_tendsto T hT μ f).comp hφ
  have heq : (∫ x, f (T x) ∂(ν : Measure X)) - (∫ x, f x ∂(ν : Measure X)) = 0 :=
    tendsto_nhds_unique (hg.sub hf) hzero
  exact sub_eq_zero.mp heq

/-- Compactness of probability measures provides a genuine invariant law.
This is the Krylov--Bogoliubov argument used twice in the manuscript. -/
theorem exists_invariant_probability [Nonempty X] (T : X → X) (hT : Continuous T) :
    ∃ μ : ProbabilityMeasure X, MeasurePreserving T (μ : Measure X) (μ : Measure X) := by
  let μ₀ : ProbabilityMeasure X := ⟨Measure.dirac (Classical.choice ‹Nonempty X›), by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  obtain ⟨ν, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq (cesaro T hT μ₀)
  exact ⟨ν, cesaro_limit_invariant T hT μ₀ ν hφ.tendsto_atTop hlim⟩


omit [MetrizableSpace X] [CompactSpace X] in
lemma continuous_testEmbedding : Continuous (testEmbedding (X := X)) := by
  apply continuous_pi
  intro f
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

omit [CompactSpace X] in
lemma testEmbedding_injective : Function.Injective (testEmbedding (X := X)) := by
  intro μ ν h
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact congrFun h f

omit [CompactSpace X] in
lemma invariant_probabilities_closed (T : X → X) (hT : Continuous T) :
    IsClosed {μ : ProbabilityMeasure X | MeasurePreserving T (μ : Measure X) (μ : Measure X)} := by
  have h := isClosed_eq (ProbabilityMeasure.continuous_map hT) continuous_id
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext μ
  exact ⟨fun hm => ProbabilityMeasure.toMeasure_injective hm.map_eq,
    fun hm => ⟨hT.measurable, congrArg ProbabilityMeasure.toMeasure hm⟩⟩

/-- Every continuous self-map of a nonempty compact metrizable Borel space
has an ergodic invariant probability law, obtained as an extreme point. -/
theorem exists_ergodic_probability [Nonempty X] (T : X → X) (hT : Continuous T) :
    ∃ μ : ProbabilityMeasure X, Ergodic T (μ : Measure X) := by
  let K : Set (ProbabilityMeasure X) :=
    {μ | MeasurePreserving T (μ : Measure X) (μ : Measure X)}
  have hK : IsCompact K := (invariant_probabilities_closed T hT).isCompact
  have hKn : K.Nonempty := exists_invariant_probability T hT
  obtain ⟨v, hv⟩ := (hK.image continuous_testEmbedding).extremePoints_nonempty
    (hKn.image testEmbedding)
  obtain ⟨μ, hμ, rfl⟩ := hv.1
  refine ⟨μ, Ergodic.of_mem_extremePoints ⟨⟨hμ, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩, ?_⟩⟩
  intro ν₁ hν₁ ν₂ hν₂ hseg
  let : IsProbabilityMeasure ν₁ := hν₁.2
  let : IsProbabilityMeasure ν₂ := hν₂.2
  let p₁ : ProbabilityMeasure X := ⟨ν₁, hν₁.2⟩
  let p₂ : ProbabilityMeasure X := ⟨ν₂, hν₂.2⟩
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have ha₁ : a ≤ 1 := by rw [← hab]; exact le_add_right le_rfl
  have hb₁ : b ≤ 1 := by rw [← hab]; exact le_add_left le_rfl
  have hat : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha₁
  have hbt : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hb₁
  have hreal : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add hat hbt, hab, ENNReal.toReal_one]
  have hseg' : testEmbedding μ ∈ openSegment ℝ (testEmbedding p₁) (testEmbedding p₂) := by
    refine ⟨a.toReal, b.toReal, ENNReal.toReal_pos ha.ne' hat,
      ENNReal.toReal_pos hb.ne' hbt, hreal, ?_⟩
    funext f
    change a.toReal * (∫ x, f x ∂ν₁) + b.toReal * (∫ x, f x ∂ν₂) = _
    rw [testEmbedding, ← heq,
      integral_add_measure ((f.integrable ν₁).smul_measure hat)
        ((f.integrable ν₂).smul_measure hbt), integral_smul_measure, integral_smul_measure]
    rfl
  have hemb := hv.2 ⟨p₁, hν₁.1, rfl⟩ ⟨p₂, hν₂.1, rfl⟩ hseg'
  exact congrArg ProbabilityMeasure.toMeasure (testEmbedding_injective hemb)

end SmoothObstruction.CompactInvariant

namespace SmoothObstruction.CompactInvariant
open MeasureTheory Filter Topology TopologicalSpace Set
open scoped BoundedContinuousFunction

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Probability measures lift through continuous surjections from a compact
metric space. Finite simple approximants avoid any selection assumption. -/
theorem exists_probability_lift (π : X → Y) (hπ : Continuous π)
    (hsur : Function.Surjective π) (μ : ProbabilityMeasure Y) :
    ∃ ν : ProbabilityMeasure X, (ν : Measure X).map π=(μ : Measure Y) := by
  classical
  have : Nonempty Y := nonempty_of_isProbabilityMeasure (μ : Measure Y)
  let y₀ : Y := Classical.choice inferInstance
  let a (n : ℕ) : SimpleFunc Y Y := SimpleFunc.approxOn id measurable_id Set.univ y₀ (Set.mem_univ _) n
  let s : Y → X := fun y => Classical.choose (hsur y)
  have hs (y : Y) : π (s y)=y := Classical.choose_spec (hsur y)
  let b (n : ℕ) : SimpleFunc Y X := (a n).map s
  let v (n : ℕ) : ProbabilityMeasure X := μ.map (b n).measurable.aemeasurable
  obtain ⟨ν,φ,hφ,hlim⟩ := CompactSpace.tendsto_subseq v
  refine ⟨ν,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hπ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  let g : X →ᵇ ℝ := f.compContinuous ⟨π,hπ⟩
  have hν := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim g
  have hμ : Tendsto (fun n => ∫ y, f (a n y) ∂(μ : Measure Y)) atTop
      (𝓝 (∫ y, f y ∂(μ : Measure Y))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (f.continuous.measurable.comp (a n).measurable).aestronglyMeasurable)
      (integrable_const _)
      (fun n => Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm (a n y)))
    exact Filter.Eventually.of_forall (fun y => f.continuous.continuousAt.tendsto.comp
      (SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ y₀) (by simp)))
  have he (n : ℕ) : (∫ x,g x ∂(v n : Measure X))=∫ y,f (a n y) ∂(μ : Measure Y) := by
    change (∫ x,g x ∂((μ : Measure Y).map (b n)))=_
    rw [integral_map (b n).measurable.aemeasurable g.continuous.aestronglyMeasurable]
    simp only [g,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,
      b,SimpleFunc.map_apply,hs]
  simp only [Function.comp_apply,he] at hν
  exact tendsto_nhds_unique hν (hμ.comp hφ.tendsto_atTop)


end SmoothObstruction.CompactInvariant

namespace SmoothObstruction.CompactInvariant
open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped BoundedContinuousFunction
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The required stationary lift with exactly the prescribed marginal. This
uses compactness and actual finite probability approximants, not a chosen
stationary lift as an additional hypothesis. -/
theorem exists_invariant_lift (π : X → Y) (hπ : Continuous π)
    (hsur : Function.Surjective π) (T : X → X) (hT : Continuous T) (S : Y → Y)
    (hsem : Function.Semiconj π T S) (μ : ProbabilityMeasure Y)
    (hS : MeasurePreserving S (μ : Measure Y) (μ : Measure Y)) :
    ∃ ν : ProbabilityMeasure X, MeasurePreserving T (ν : Measure X) (ν : Measure X) ∧
      (ν : Measure X).map π=(μ : Measure Y) := by
  obtain ⟨ν₀,hν₀⟩ := exists_probability_lift π hπ hsur μ
  have hproj (j : ℕ) : (iterateLaw T hT ν₀ j : Measure X).map π=(μ : Measure Y) := by
    change ((ν₀ : Measure X).map (T^[j])).map π=_
    rw [Measure.map_map hπ.measurable (hT.iterate j).measurable]
    have he : π∘(T^[j])=(S^[j])∘π := funext (hsem.iterate_right j)
    rw [he,←Measure.map_map (hS.iterate j).measurable hπ.measurable,hν₀]
    exact (hS.iterate j).map_eq
  obtain ⟨ν,φ,hφ,hlim⟩ := CompactSpace.tendsto_subseq (cesaro T hT ν₀)
  refine ⟨ν,cesaro_limit_invariant T hT ν₀ ν hφ.tendsto_atTop hlim,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hπ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  let g : X →ᵇ ℝ := f.compContinuous ⟨π,hπ⟩
  have he (j : ℕ) : (∫ x,g ((T^[j]) x) ∂(ν₀ : Measure X))=∫ y,f y ∂(μ : Measure Y) := by
    rw [←integral_iterateLaw T hT ν₀ j g,←hproj j,
      integral_map hπ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
    rfl
  have hc (n : ℕ) : (∫ x,g x ∂(cesaro T hT ν₀ n : Measure X))=∫ y,f y ∂(μ : Measure Y) := by
    rw [integral_cesaro]
    simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    field_simp
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim g
  simp only [Function.comp_apply,hc] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds


end SmoothObstruction.CompactInvariant

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_OrthogonalCocycle
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SmoothObstruction.QR
open InnerProductSpace Finset
variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ}

/-- Continuity of the actual Gram--Schmidt algorithm on independent lists. -/
theorem continuous_gramSchmidt (f : X → Fin d → E) (hf : Continuous f)
    (hind : ∀ x,LinearIndependent ℝ (f x)) (j : Fin d) :
    Continuous (fun x => gramSchmidt ℝ (f x) j) := by
  apply wellFounded_lt.induction j
  intro j ih
  have he : (fun x => gramSchmidt ℝ (f x) j)=
      (fun x => f x j-∑ i∈Iio j,
        (inner ℝ (gramSchmidt ℝ (f x) i) (f x j)/‖gramSchmidt ℝ (f x) i‖^2) •
          gramSchmidt ℝ (f x) i) := by
    funext x
    rw [gramSchmidt_def]
    simp [Submodule.starProjection_singleton]
  rw [he]
  apply ((continuous_apply j).comp hf).sub
  apply continuous_finsetSum
  intro i hi
  have hlt := Finset.mem_Iio.mp hi
  exact (((ih i hlt).inner ((continuous_apply j).comp hf)).div
    ((ih i hlt).norm.pow 2) (fun x => pow_ne_zero 2
      (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i (hind x))))).smul (ih i hlt)

theorem continuous_gramSchmidtNormed (f : X → Fin d → E) (hf : Continuous f)
    (hind : ∀ x,LinearIndependent ℝ (f x)) :
    Continuous (fun x => gramSchmidtNormed ℝ (f x)) := by
  apply continuous_pi
  intro j
  exact ((continuous_gramSchmidt f hf hind j).norm.inv₀
    (fun x => norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j (hind x)))).smul
      (continuous_gramSchmidt f hf hind j)


end SmoothObstruction.QR

namespace SmoothObstruction.QR
open InnerProductSpace Finset Set

variable {d : ℕ}

lemma continuous_step {X : Type*} [TopologicalSpace X]
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (e : X → Frame d) (he : Continuous e) : Continuous (fun x => step (A x) (e x)) := by
  apply Continuous.subtype_mk
  apply continuous_gramSchmidtNormed
  · apply continuous_pi
    intro i
    exact hA.clm_apply ((continuous_apply i).comp (continuous_subtype_val.comp he))
  · intro x
    exact (e x).property.linearIndependent.map' (A x).toLinearMap (LinearMap.ker_eq_bot.mpr (A x).injective)

end SmoothObstruction.QR

namespace SmoothObstruction.QR
open InnerProductSpace Finset
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

lemma inner_gramSchmidt_self (f : Fin d → E) (i : Fin d) :
    inner ℝ (gramSchmidt ℝ f i) (f i)=‖gramSchmidt ℝ f i‖^2 := by
  have h := congrArg (fun z => inner ℝ (gramSchmidt ℝ f i) z) (gramSchmidt_def' ℝ f i)
  rw [inner_add_right,inner_sum] at h
  have hz : (∑ j∈Iio i,inner ℝ (gramSchmidt ℝ f i)
      ((ℝ ∙ gramSchmidt ℝ f j).starProjection (f i)))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Submodule.starProjection_singleton,inner_smul_right,
      gramSchmidt_orthogonal ℝ f (ne_of_gt (Finset.mem_Iio.mp hj)),mul_zero]
  simpa only [hz,add_zero,real_inner_self_eq_norm_sq] using h

lemma positive_diagonal (f : Fin d → E) (hf : LinearIndependent ℝ f) (i : Fin d) :
    0 < inner ℝ (gramSchmidtNormed ℝ f i) (f i) := by
  rw [gramSchmidtNormed,inner_smul_left,inner_gramSchmidt_self]
  simp only [RCLike.conj_to_real]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (gramSchmidt_ne_zero i hf)))
    (sq_pos_of_pos (norm_pos_iff.mpr (gramSchmidt_ne_zero i hf)))

variable {d : ℕ}

lemma diagonal_pos (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) (i : Fin d) : 0<triangular A e i i :=
  positive_diagonal _ (e.property.linearIndependent.map' A.toLinearMap
    (LinearMap.ker_eq_bot.mpr A.injective)) i

lemma triangular_upper (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) : (triangular A e).IsUpperTriangular := by
  have hf := e.property.linearIndependent.map' A.toLinearMap (LinearMap.ker_eq_bot.mpr A.injective)
  have hn (i : Fin d) : gramSchmidtNormed ℝ (fun j => A (e.val j)) i ≠ 0 := by
    have hh := gramSchmidtNormed_unit_length i hf
    change ‖gramSchmidtNormed ℝ (fun j => A (e.val j)) i‖=1 at hh
    intro hz
    rw [hz,norm_zero] at hh
    exact zero_ne_one hh
  intro i j hj
  change inner ℝ (gramSchmidtNormed ℝ (fun j => A (e.val j)) i) (A (e.val j))=0
  rw [←gramSchmidtOrthonormalBasis_apply
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin d))=Fintype.card (Fin d)) (hn i)]
  exact gramSchmidtOrthonormalBasis_inv_triangular
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin d))=Fintype.card (Fin d))
    (fun j => A (e.val j)) hj


end SmoothObstruction.QR

namespace SmoothObstruction.QR
open MeasureTheory Filter Topology InnerProductSpace
variable {d : ℕ}

lemma basis_apply (e : Frame d) (i : Fin d) : basis e i=e.val i := by
  rw [basis,gramSchmidtOrthonormalBasis_apply_of_orthogonal]
  · simp [e.property.norm_eq_one]
  · exact e.property.2
  · exact e.property.ne_zero i

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_skew (T : X → X) (hT : Continuous T)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))) :
    Continuous (skew T A) :=
  (hT.comp continuous_fst).prodMk (continuous_step _ (hA.comp continuous_fst) _ continuous_snd)

/-- The QR frame process carries a stationary law whose base marginal is
exactly the given measure. The lift is constructed, not hypothesized. -/
theorem exists_stationary_qr (T : X → X) (hT : Continuous T)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (μ : ProbabilityMeasure X) (hμ : MeasurePreserving T (μ : Measure X) (μ : Measure X)) :
    ∃ ν : ProbabilityMeasure (X × Frame d),
      MeasurePreserving (skew T A) (ν : Measure (X × Frame d)) (ν : Measure (X × Frame d)) ∧
      (ν : Measure (X × Frame d)).map Prod.fst=(μ : Measure X) := by
  have hsur : Function.Surjective (Prod.fst : X × Frame d → X) :=
    fun x => ⟨(x,Classical.choice inferInstance),rfl⟩
  exact CompactInvariant.exists_invariant_lift Prod.fst continuous_fst hsur
    (skew T A) (continuous_skew T hT A hA) T (fun _ => rfl) μ hμ

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_diagonal (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (i : Fin d) : Continuous (fun z : X × Frame d => triangular (A z.1) z.2 i i) := by
  exact ((continuous_apply i).comp (continuous_subtype_val.comp
    (continuous_step _ (hA.comp continuous_fst) _ continuous_snd))).inner
      ((hA.comp continuous_fst).clm_apply
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_log_diagonal (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (i : Fin d) : Continuous (fun z : X × Frame d => Real.log (triangular (A z.1) z.2 i i)) :=
  (continuous_diagonal A hA i).log (fun z => (diagonal_pos (A z.1) z.2 i).ne')

end SmoothObstruction.QR

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_shift : Continuous (shift (X:=X) (d:=d) (K:=K)) := by
  apply continuous_pi
  intro j
  exact continuous_apply (j+1)

omit [CompactSpace X] in
lemma measurable_code (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) : Measurable (code S A) := by
  apply Measurable.of_eval
  intro j
  exact (S^j).continuous.measurable.prodMk (hA.comp (S^j).continuous.measurable)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma code_shift (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K) (x : X) :
    code S A (S x)=shift (code S A x) := by
  funext j
  dsimp only [code,shift]
  rw [zpow_add_one,Homeomorph.mul_apply]

/-- Coding even a merely measurable bounded cocycle produces a genuine
stationary law on a compact path space. -/
theorem stationary_code (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) (μ : ProbabilityMeasure X)
    (hS : MeasurePreserving S (μ : Measure X) (μ : Measure X)) :
    MeasurePreserving shift ((μ : Measure X).map (code S A))
      ((μ : Measure X).map (code S A)) := by
  have hc := measurable_code S A hA
  refine ⟨continuous_shift.measurable,?_⟩
  rw [Measure.map_map continuous_shift.measurable hc]
  have he : shift ∘ code S A=code S A ∘ S := by
    funext x
    exact (code_shift S A x).symm
  rw [he,←Measure.map_map hc hS.measurable,hS.map_eq]

end SmoothObstruction.OrbitCocycle

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

lemma actual_measurable (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) : MeasurableSet (Actual S A) := by
  let : SecondCountableTopology X := inferInstance
  let : SecondCountableTopology (CompactMatrix.Alphabet d K) := inferInstance
  let : SecondCountableTopology (Path (X:=X) (d:=d) (K:=K)) := inferInstance
  let : BorelSpace (Path (X:=X) (d:=d) (K:=K)) := inferInstance
  let : MeasurableEq (Path (X:=X) (d:=d) (K:=K)) :=
    ⟨isClosed_diagonal.measurableSet⟩
  exact measurableSet_eq_fun measurable_id ((measurable_code S A hA).comp
    (measurable_fst.comp (measurable_pi_apply 0)))

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma code_actual (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K) (x : X) :
    code S A x ∈ Actual S A := by simp [Actual,code]

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_matrix : Continuous (fun p : Path (X:=X) (d:=d) (K:=K) =>
    (matrix p).toContinuousLinearMap) :=
  continuous_subtype_val.comp (continuous_snd.comp (continuous_apply 0))

/-- A stationary QR process for the genuine measurable cocycle. The path
law, its original marginal, and concentration on actual orbits are proved. -/
theorem stationary_qr_code (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) (μ : ProbabilityMeasure X)
    (hS : MeasurePreserving S (μ : Measure X) (μ : Measure X)) :
    ∃ ν : ProbabilityMeasure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d),
      MeasurePreserving (QR.skew shift matrix) (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)) (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)) ∧
      (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).map Prod.fst=(μ : Measure X).map (code S A) ∧
      ∀ᵐ z ∂(ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)), z.1∈Actual S A := by
  let := TopologicalSpace.metrizableSpaceMetric (Path (X:=X) (d:=d) (K:=K))
  let μc := μ.map (measurable_code S A hA).aemeasurable
  obtain ⟨ν,hν,hπ⟩ := QR.exists_stationary_qr shift continuous_shift matrix continuous_matrix μc
    (stationary_code S A hA μ hS)
  refine ⟨ν,hν,hπ,?_⟩
  have hμa : ∀ᵐ p ∂((μ : Measure X).map (code S A)), p∈Actual S A := by
    apply (ae_map_iff (measurable_code S A hA).aemeasurable (actual_measurable S A hA)).mpr
    exact Filter.Eventually.of_forall (code_actual S A)
  change (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).map Prod.fst=
    (μ : Measure X).map (code S A) at hπ
  rw [←hπ] at hμa
  exact ae_of_ae_map measurable_fst.aemeasurable hμa

omit [CompactSpace X] [BorelSpace X] in
lemma preserving_pow (S : X ≃ₜ X) {μ : Measure X} (hS : MeasurePreserving S μ μ) (n : ℕ) :
    MeasurePreserving (S^n) μ μ := by
  induction n with
  | zero => exact MeasurePreserving.id μ
  | succ n ih =>
      rw [pow_succ]
      exact ih.comp hS

omit [CompactSpace X] in
/-- Every deterministic-time observation has exactly the original base law. -/
lemma marginal_at (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) (μ : ProbabilityMeasure X)
    (hS : MeasurePreserving S (μ : Measure X) (μ : Measure X))
    (ν : ProbabilityMeasure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d))
    (hπ : (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).map Prod.fst=(μ : Measure X).map (code S A)) (n : ℕ) :
    (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).map (fun z => (z.1 (n : ℤ)).1)=(μ : Measure X) := by
  let p : Path (X:=X) (d:=d) (K:=K) → X := fun q => (q (n : ℤ)).1
  have hp : Measurable p := measurable_fst.comp (measurable_pi_apply _)
  change (ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).map (p ∘ Prod.fst)=_
  rw [←Measure.map_map hp measurable_fst,hπ,
    Measure.map_map hp (measurable_code S A hA)]
  have he : p ∘ code S A=(S^n : X ≃ₜ X) := by
    funext x; simp [p,code]
  rw [he]
  exact (preserving_pow S hS n).map_eq

end SmoothObstruction.OrbitCocycle

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_StationaryGauge
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators

namespace SmoothObstruction.GoodStationary
open MeasureTheory Finset Filter Topology
open SmoothObstruction.DyadicChord
open scoped ENNReal NNReal

lemma floorAt_pos (k : ℕ) : 0 < floorAt k := Real.rpow_pos_of_pos (by norm_num) _

lemma floorAt_sq (k : ℕ) : (floorAt k)^2 = ((2 : ℝ)^(-1/5 : ℝ))^k := by
  rw [floorAt, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

lemma floorAt_square_summable : Summable (fun k => (floorAt k)^2) := by
  simp_rw [floorAt_sq]
  exact summable_geometric_of_norm_lt_one (by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

lemma bAt_floor {η : ℝ} (hη : 0 < η) (a : ℕ → ℝ) (k : ℕ) :
    floorAt k ≤ bAt η a k := by
  dsimp [bAt]
  exact le_add_of_nonneg_left (by positivity)

lemma bAt_pos {η : ℝ} (hη : 0 < η) (a : ℕ → ℝ) (k : ℕ) :
    0 < bAt η a k := (floorAt_pos k).trans_le (bAt_floor hη a k)

lemma bAt_square_summable {η : ℝ} {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) (hsum : Summable a) :
    Summable (fun k => (bAt η a k)^2) := by
  have hs : Summable (fun k => a (k + 1)) := (summable_nat_add_iff 1).2 hsum
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
    ((hs.mul_left (2 * (40 / Real.sqrt η)^2)).add
      (floorAt_square_summable.mul_left 2))
  intro k
  dsimp [bAt]
  have := Real.sq_sqrt (ha (k + 1))
  nlinarith [sq_nonneg ((40 / Real.sqrt η) * Real.sqrt (a (k + 1)) - floorAt k)]

lemma error_ratio {η : ℝ} (hη : 0 < η) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) (k : ℕ) :
    4 * a (k + 1) / (bAt η a k)^2 ≤ η / 400 := by
  have hr : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hb := bAt_pos hη a k
  have hbase : (40 / Real.sqrt η) * Real.sqrt (a (k + 1)) ≤ bAt η a k := by
    dsimp [bAt]
    linarith [floorAt_pos k]
  have hs : ((40 / Real.sqrt η) * Real.sqrt (a (k + 1)))^2 ≤ (bAt η a k)^2 :=
    pow_le_pow_left₀ (by positivity) hbase 2
  have hsq : ((40 / Real.sqrt η) * Real.sqrt (a (k + 1)))^2 =
      1600 * a (k + 1) / η := by
    rw [mul_pow, div_pow, Real.sq_sqrt (ha _), Real.sq_sqrt hη.le]
    ring
  rw [hsq] at hs
  have := (div_le_iff₀ hη).mp hs
  apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma jointEnergy_nonneg {d : ℕ} (T : Ω → Ω) (f : Fin d → Ω → ℝ) (h : ℕ) :
    0 ≤ jointEnergy T f μ h := sum_nonneg (fun j _ => deviationEnergy_nonneg T (f j) _)

lemma jointEnergy_summable {d : ℕ} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Fin d → Ω → ℝ} (hf : ∀ j, MemLp (f j) 2 μ) :
    Summable (jointEnergy T f μ) := by
  exact summable_sum (fun j _ => (dyadic_square_summable hT (hf j)).1)

omit [MeasurableSpace Ω] in
lemma good_iff_deviation {d : ℕ} (T : Ω → Ω) (f : Fin d → Ω → ℝ)
    (k : ℕ) (b : ℝ) (x : Ω) :
    x ∈ Good T f k b ↔ ∀ j, deviation (orbit T (f j) x) (2^(k + 1)) ≤ b / 2 := by
  have hn : 0 < 2^(k + 1) := pow_pos (by omega : 0 < 2) _
  have hn' : (2 : ℝ)^(k + 1) = 2 * 2^k := pow_succ' _ _
  constructor
  · intro hx j
    apply deviation_le _ hn
    intro u hu
    have := hx j u hu
    simp only [Nat.cast_pow, Nat.cast_ofNat, hn']
    nlinarith
  · intro hx j u hu
    have hh := abs_chord_le (orbit T (f j) x) hn hu
    have hh' := mul_le_mul_of_nonneg_left (hx j) (Nat.cast_nonneg (2^(k + 1)))
    simp only [Nat.cast_pow, Nat.cast_ofNat, hn'] at hh hh'
    nlinarith

/-- Quantitative squared Markov bound for all coordinate chords together.
The measure is UNNORMALIZED; no conditioning of the original law occurs. -/
theorem bad_measure {d : ℕ} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Fin d → Ω → ℝ} (hf : ∀ j, MemLp (f j) 2 μ)
    {b : ℝ} (hb : 0 < b) (k : ℕ) :
    μ (Good T f k b)ᶜ ≤ ENNReal.ofReal (4 * jointEnergy T f μ (k + 1) / b^2) := by
  let F : Ω → ℝ := fun x => (4 / b^2) * ∑ j, (deviation (orbit T (f j) x) (2^(k + 1)))^2
  have hF : Integrable F μ :=
    (integrable_finsetSum _ (fun j _ =>
      (deviation_memLp (orbit_memLp hT (hf j)) _).integrable_sq)).const_mul _
  have hnonneg : ∀ x, 0 ≤ F x := by
    intro x
    dsimp [F]
    positivity
  have hbad : ∀ x ∈ (Good T f k b)ᶜ, 1 ≤ F x := by
    intro x hx
    have hnot : ¬ ∀ j, deviation (orbit T (f j) x) (2^(k + 1)) ≤ b / 2 := by
      simpa only [Set.mem_compl_iff, good_iff_deviation] using hx
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have hsmall : (deviation (orbit T (f j) x) (2^(k + 1)))^2 ≤
        ∑ i, (deviation (orbit T (f i) x) (2^(k + 1)))^2 :=
      single_le_sum (f := fun i : Fin d => (deviation (orbit T (f i) x) (2^(k + 1)))^2)
        (fun _ _ => sq_nonneg _) (mem_univ j)
    have hsum : b^2 / 4 ≤ ∑ i, (deviation (orbit T (f i) x) (2^(k + 1)))^2 := by
      nlinarith [deviation_nonneg (orbit T (f j) x) (2^(k + 1))]
    dsimp [F]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
    nlinarith
  convert hF.measure_le_integral (Filter.Eventually.of_forall hnonneg) hbad using 2
  all_goals try with_reducible_and_instances rfl
  dsimp [F, jointEnergy, deviationEnergy]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
    (deviation_memLp (orbit_memLp hT (hf j)) _).integrable_sq)]
  ring

/-- The actual simultaneous good-segment sequence, not an assumed rate of
convergence. No ergodicity or rate assumption is used. -/
theorem good_segments {d : ℕ} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Fin d → Ω → ℝ} (hf : ∀ j, MemLp (f j) 2 μ) {η : ℝ} (hη : 0 < η) :
    ∃ b : ℕ → ℝ, (∀ k, 0 < b k) ∧ (∀ k, floorAt k ≤ b k) ∧
      Summable (fun k => (b k)^2) ∧
      ∀ k, μ (Good T f k (b k))ᶜ ≤ ENNReal.ofReal (η / 400) := by
  let a := jointEnergy T f μ
  refine ⟨bAt η a, bAt_pos hη a, bAt_floor hη a,
    bAt_square_summable (jointEnergy_nonneg T f) (jointEnergy_summable hT hf), ?_⟩
  intro k
  exact (bad_measure hT hf (bAt_pos hη a k) k).trans
    (ENNReal.ofReal_le_ofReal (error_ratio hη (jointEnergy_nonneg T f) k))

section Compact
variable [TopologicalSpace Ω]

omit [MeasurableSpace Ω] in
lemma chord_continuous {T : Ω → Ω} (hT : Continuous T) {f : Ω → ℝ}
    (hf : Continuous f) (n u : ℕ) : Continuous (fun x => chord (orbit T f x) n u) := by
  have hs (m : ℕ) : Continuous (fun x => prefixSum (orbit T f x) m) :=
    continuous_finsetSum _ (fun j _ => hf.comp (hT.iterate j))
  exact (hs u).sub (continuous_const.mul ((hs n).div_const _))

omit [MeasurableSpace Ω] in
lemma good_isClosed {d : ℕ} {T : Ω → Ω} (hT : Continuous T)
    {f : Fin d → Ω → ℝ} (hf : ∀ j, Continuous (f j)) (k : ℕ) (b : ℝ) :
    IsClosed (Good T f k b) := by
  have heq : Good T f k b = ⋂ j, ⋂ u, ⋂ (_ : u ≤ 2^(k + 1)),
      {x | |chord (orbit T (f j) x) (2^(k + 1)) u| ≤ b * (2 : ℝ)^k} := by
    ext x
    simp only [Good, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter (fun j => isClosed_iInter (fun u => isClosed_iInter
    (fun _ => isClosed_le (chord_continuous hT (hf j) _ u).abs continuous_const)))

variable [CompactSpace Ω] [BorelSpace Ω] [IsProbabilityMeasure μ]

/-- Compact good sets, with the source's 1−η/100 lower bound. The proof
actually gives 1−η/400. The displayed natural-coordinate block has length
2^(k+1), corresponding to the source's centered block [-2^k,2^k). -/
theorem compact_good_segments {d : ℕ} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hTc : Continuous T) {f : Fin d → Ω → ℝ} (hf : ∀ j, Continuous (f j))
    {η : ℝ} (hη : 0 < η) :
    ∃ b : ℕ → ℝ, (∀ k, 0 < b k) ∧ (∀ k, floorAt k ≤ b k) ∧
      Summable (fun k => (b k)^2) ∧ ∀ k,
      IsCompact (Good T f k (b k)) ∧ 1 - η / 100 ≤ μ.real (Good T f k (b k)) := by
  obtain ⟨b, hbpos, hbfloor, hbsum, hbad⟩ := good_segments hT
    (fun j => (hf j).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hη
  refine ⟨b, hbpos, hbfloor, hbsum, fun k => ⟨(good_isClosed hTc hf k (b k)).isCompact, ?_⟩⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbad k)
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  change μ.real (Good T f k (b k))ᶜ ≤ η / 400 at hreal
  rw [measureReal_compl (good_isClosed hTc hf k (b k)).measurableSet] at hreal
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at hreal
  change _ ≤ (μ (Good T f k (b k))).toReal
  linarith

end Compact

/-- Projection of a compact good set needs no measurable frame selection.
The sole measure input is the genuine pushforward identity. -/
theorem compact_projection_good {Γ : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    [BorelSpace Ω] [IsProbabilityMeasure μ] [TopologicalSpace Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] {ν : Measure Γ} [IsProbabilityMeasure ν]
    {π : Ω → Γ} (hπ : Continuous π) (hpush : MeasurePreserving π μ ν)
    {G : Set Ω} (hG : IsCompact G) {a : ℝ} (ha : a ≤ μ.real G) :
    IsCompact (π '' G) ∧ a ≤ ν.real (π '' G) := by
  have himage := hG.image hπ
  refine ⟨himage, ha.trans ?_⟩
  calc
    μ.real G ≤ μ.real (π ⁻¹' (π '' G)) := measureReal_mono (Set.subset_preimage_image π G)
    _ = ν.real (π '' G) := hpush.measureReal_preimage himage.isClosed.measurableSet.nullMeasurableSet

end SmoothObstruction.GoodStationary

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology Set
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_logDiagonal (j : Fin d) :
    Continuous (logDiagonal (X:=X) (K:=K) j) := by
  let := TopologicalSpace.metrizableSpaceMetric (Path (X:=X) (d:=d) (K:=K))
  exact QR.continuous_log_diagonal (matrix (X:=X) (d:=d) (K:=K)) continuous_matrix j

/-- The actual good-frame burden for a bounded coordinate cocycle is
constructed from stationarity, with compactness restored inside the Borel
full-measure genuine-code locus rather than asserted for a measurable graph.
The projection uses the middle of each length-2n block. -/
theorem compact_actual_good (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) (μ : ProbabilityMeasure X)
    (hS : MeasurePreserving S (μ : Measure X) (μ : Measure X))
    {η : ℝ} (hη : 0<η) :
    ∃ (ν : ProbabilityMeasure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d))
      (b : ℕ → ℝ) (G : ℕ → Set (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)),
      (∀ k, 0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
      Summable (fun k => (b k)^2) ∧ ∀ k,
      IsCompact (G k) ∧
      (∀ z∈G k,z.1∈Actual S A ∧
        z∈GoodStationary.Good (QR.skew shift matrix) logDiagonal k (b k)) ∧
      1-η/100≤(ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).real (G k) ∧
      IsCompact ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k) ∧
      1-η/100≤(μ : Measure X).real ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k) := by
  let := TopologicalSpace.metrizableSpaceMetric (Path (X:=X) (d:=d) (K:=K))
  obtain ⟨ν,hν,hπ,hact⟩ := stationary_qr_code S A hA μ hS
  have hTc : Continuous (QR.skew (shift (X:=X) (d:=d) (K:=K)) matrix) :=
    QR.continuous_skew _ continuous_shift _ continuous_matrix
  obtain ⟨b,hbp,hbf,hbs,hG⟩ := GoodStationary.compact_good_segments hν hTc
    (fun j => continuous_logDiagonal j) (show 0<η/2 by linarith)
  have hco : MeasurableSet (Prod.fst ⁻¹' Actual S A :
      Set (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)) :=
    (actual_measurable S A hA).preimage measurable_fst
  have hchoose (k : ℕ) : ∃ F : Set (Path (X:=X) (d:=d) (K:=K) × QR.Frame d),
      F ⊆ GoodStationary.Good (QR.skew shift matrix) logDiagonal k (b k) ∩
        Prod.fst ⁻¹' Actual S A ∧ IsCompact F ∧
        1-η/100≤(ν : Measure _).real F := by
    let H : Set (Path (X:=X) (d:=d) (K:=K) × QR.Frame d) :=
      GoodStationary.Good (QR.skew shift matrix) logDiagonal k (b k)
    have hh : MeasurableSet H := (hG k).1.isClosed.measurableSet
    have he : (ν : Measure _) (H∩Prod.fst ⁻¹' Actual S A)=(ν : Measure _) H := by
      apply measure_congr
      filter_upwards [hact] with z hz
      change (z ∈ H ∧ z.1 ∈ Actual S A) = (z ∈ H)
      exact propext (and_iff_left hz)
    obtain ⟨F,hF,hFc,hFm⟩ := (hh.inter hco).exists_isCompact_lt_add
      (measure_ne_top (ν : Measure _) _) (show ENNReal.ofReal (η/400)≠0 by positivity)
    refine ⟨F,hF,hFc,?_⟩
    rw [he] at hFm
    have hr := (ENNReal.toReal_lt_toReal (measure_ne_top (ν : Measure _) H)
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top (ν : Measure _) F,ENNReal.ofReal_ne_top⟩)).mpr hFm
    rw [ENNReal.toReal_add (measure_ne_top (ν : Measure _) F) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at hr
    have hg := (hG k).2
    change 1-(η/2)/100≤((ν : Measure _) H).toReal at hg
    change 1-η/100≤((ν : Measure _) F).toReal
    linarith
  choose G hsub hGc hGm using hchoose
  refine ⟨ν,b,G,hbp,hbf,hbs,?_⟩
  intro k
  have hp : Continuous (fun z : Path (X:=X) (d:=d) (K:=K) × QR.Frame d =>
      (z.1 ((2^k : ℕ) : ℤ)).1) :=
    continuous_fst.comp ((continuous_apply _).comp continuous_fst)
  have hmp : MeasurePreserving (fun z : Path (X:=X) (d:=d) (K:=K) × QR.Frame d =>
      (z.1 ((2^k : ℕ) : ℤ)).1) (ν : Measure _) (μ : Measure X) :=
    ⟨hp.measurable,marginal_at S A hA μ hS ν hπ (2^k)⟩
  have hproj := GoodStationary.compact_projection_good hp hmp (hGc k) (hGm k)
  exact ⟨hGc k,fun z hz => ⟨(hsub k hz).2,(hsub k hz).1⟩,hGm k,hproj⟩

end SmoothObstruction.OrbitCocycle

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Splitting
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.EuclideanSplitting
variable {d : ℕ}

lemma norm_le_sum_coordinates (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

/-- Entry bounds produce Euclidean operator bounds. The dimension factor is
paid only at endpoints, never once per step. -/
lemma opNorm_le_entry (A : Matrix (Fin d) (Fin d) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i j, |A i j| ≤ B) : ‖A‖ ≤ (d : ℝ)^2 * B := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM]
  refine (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) A).opNorm_le_bound (mul_nonneg (sq_nonneg _) hB) ?_
  intro x
  calc
    _ ≤ ∑ i, ‖(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) A x) i‖ := norm_le_sum_coordinates _
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, B*‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      change ‖(A *ᵥ x) i‖ ≤ _
      rw [Matrix.mulVec, dotProduct]
      calc
        _ ≤ ∑ j, ‖A i j*x j‖ := norm_sum_le _ _
        _ ≤ _ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul,Real.norm_eq_abs]
          exact mul_le_mul (hA i j) (PiLp.norm_apply_le x j) (norm_nonneg _) hB
    _ = _ := by simp; ring

lemma opNorm_le_exp (A : Matrix (Fin d) (Fin d) ℝ) {C E : ℝ}
    (hE : 1 ≤ E) (hA : ∀ i j, |A i j| ≤ Real.exp (C*E)) :
    ‖A‖ ≤ Real.exp ((C+(d:ℝ)^2)*E) := by
  have hd : (d:ℝ)^2 ≤ Real.exp ((d:ℝ)^2*E) := by
    calc
      _ ≤ Real.exp ((d:ℝ)^2) := by linarith [Real.add_one_le_exp ((d:ℝ)^2)]
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (sq_nonneg _) hE)
  calc
    _ ≤ (d:ℝ)^2*Real.exp (C*E) := opNorm_le_entry A (Real.exp_nonneg _) hA
    _ ≤ Real.exp ((d:ℝ)^2*E)*Real.exp (C*E) :=
      mul_le_mul_of_nonneg_right hd (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

/-- Conversion of the constructed finite triangular gauge to genuine
Euclidean operator bounds. The constant is independent of the interval. -/
theorem exists_operator_gauge (d : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (E : ℝ) (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
      (lam : Fin d → ℝ), 1 ≤ E → Real.log (N+1) ≤ E →
      (∀ t < N, (A t).IsUpperTriangular) →
      (∀ t < N, ∀ j, 0 < A t j j) →
      (∀ t < N, ∀ i j, |A t i j| ≤ Real.exp R) →
      (∀ j, |lam j| ≤ R) →
      (∀ t ≤ N, ∀ j, |NormalizedGauge.error A lam t j| ≤ E) →
      ∃ U V : ℕ → Matrix (Fin d) (Fin d) ℝ,
        (∀ t, U t*V t=1 ∧ V t*U t=1) ∧
        (∀ t ≤ N, ‖U t‖ ≤ Real.exp (C*E)) ∧
        (∀ t ≤ N, ‖V t‖ ≤ Real.exp (C*E)) ∧
        (∀ t < N, A t*U t=U (t+1)*rate lam 1) := by
  obtain ⟨C,hC,h⟩ := NormalizedGauge.exists_exponential_gauge d R hR
  refine ⟨C+(d:ℝ)^2,add_nonneg hC (sq_nonneg _),?_⟩
  intro N E A lam hE hlog htri hpos hA hlam he
  obtain ⟨U,V,hUV,hU,hV,hEq⟩ := h N E A lam hE hlog htri hpos hA hlam he
  refine ⟨U,V,hUV,fun t ht => opNorm_le_exp _ hE (hU t ht),
    fun t ht => opNorm_le_exp _ hE (hV t ht),?_⟩
  intro t ht
  simpa only [rate,one_mul] using hEq t ht

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.QR
open Matrix
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma frameMatrix_inverse (e : Frame d) : frameMatrix e*frameInverse e=1 ∧ frameInverse e*frameMatrix e=1 := by
  constructor <;> apply EquivLike.injective (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)) <;>
    simp only [map_mul,map_one,frameMatrix,frameInverse,StarAlgEquiv.apply_symm_apply]
  · apply ContinuousLinearMap.ext
    intro x
    exact (basis e).repr.symm_apply_apply x
  · apply ContinuousLinearMap.ext
    intro x
    exact (basis e).repr.apply_symm_apply x

lemma norm_frameMatrix (e : Frame d) : ‖frameMatrix e‖≤1 := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM,frameMatrix,StarAlgEquiv.apply_symm_apply]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.norm_map,one_mul,le_refl]

lemma norm_frameInverse (e : Frame d) : ‖frameInverse e‖≤1 := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM,frameInverse,StarAlgEquiv.apply_symm_apply]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.norm_map,one_mul,le_refl]

lemma triangular_bound (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) (i j : Fin d) : |triangular A e i j|≤‖A.toContinuousLinearMap‖ := by
  have h := norm_inner_le_norm (𝕜:=ℝ) ((step A e).val i) (A (e.val j))
  rw [(step A e).property.norm_eq_one,one_mul] at h
  apply h.trans
  change ‖A.toContinuousLinearMap (e.val j)‖≤‖A.toContinuousLinearMap‖
  simpa only [e.property.norm_eq_one,mul_one] using A.toContinuousLinearMap.le_opNorm (e.val j)

lemma matrix_qr (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) :
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm A.toContinuousLinearMap*frameMatrix e=
      frameMatrix (step A e)*triangular A e := by
  apply EquivLike.injective (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ))
  simp only [map_mul,StarAlgEquiv.apply_symm_apply,frameMatrix]
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
  intro j
  change A ((basis e).repr.symm (EuclideanSpace.basisFun (Fin d) ℝ j))=
    (basis (step A e)).repr.symm (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (triangular A e) (EuclideanSpace.basisFun (Fin d) ℝ j))
  have hcol : Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (triangular A e) (EuclideanSpace.basisFun (Fin d) ℝ j)=
      (basis (step A e)).repr (A (e.val j)) := by
    ext i
    simp only [Matrix.ofLp_toEuclideanCLM,EuclideanSpace.basisFun_apply,PiLp.ofLp_single,
      Matrix.mulVec_single,MulOpposite.op_one,one_smul,Matrix.col_apply,
      OrthonormalBasis.repr_apply_apply,basis_apply,triangular]
  rw [hcol,LinearIsometryEquiv.symm_apply_apply]
  congr 1
  apply (basis e).repr.injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  simpa only [basis_apply,EuclideanSpace.basisFun_apply] using ((basis e).repr_self j).symm

/-- The actual QR frame change transfers a triangular finite gauge to the
original derivative matrices, at no loss in operator norm. -/
theorem transfer_gauge
    (A : ℕ → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : ℕ → Frame d) (he : ∀ t,e (t+1)=step (A t) (e t))
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (N : ℕ) (K : ℝ)
    (hUV : ∀ t,U t*V t=1 ∧ V t*U t=1)
    (hU : ∀ t≤N,‖U t‖≤Real.exp K) (hV : ∀ t≤N,‖V t‖≤Real.exp K)
    (hEq : ∀ t<N,triangular (A t) (e t)*U t=U (t+1)*EuclideanSplitting.rate lam 1) :
    ∃ P Q : ℕ → Matrix (Fin d) (Fin d) ℝ,
      (∀ t,P t*Q t=1 ∧ Q t*P t=1) ∧
      (∀ t≤N,‖P t‖≤Real.exp K) ∧ (∀ t≤N,‖Q t‖≤Real.exp K) ∧
      (∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (A t).toContinuousLinearMap*P t=
        P (t+1)*EuclideanSplitting.rate lam 1) := by
  let P := fun t => frameMatrix (e t)*U t
  let Q := fun t => V t*frameInverse (e t)
  refine ⟨P,Q,fun t => ?_,fun t ht => ?_,fun t ht => ?_,fun t ht => ?_⟩
  · constructor
    · dsimp [P,Q]
      calc
        _=frameMatrix (e t)*(U t*V t)*frameInverse (e t) := by noncomm_ring
        _=1 := by rw [(hUV t).1,mul_one,(frameMatrix_inverse _).1]
    · dsimp [P,Q]
      calc
        _=V t*(frameInverse (e t)*frameMatrix (e t))*U t := by noncomm_ring
        _=1 := by rw [(frameMatrix_inverse _).2,mul_one,(hUV t).2]
  · exact (norm_mul_le _ _).trans (by
      simpa only [one_mul] using mul_le_mul (norm_frameMatrix _) (hU t ht) (norm_nonneg _) zero_le_one)
  · exact (norm_mul_le _ _).trans (by
      simpa only [mul_one] using mul_le_mul (hV t ht) (norm_frameInverse _) (norm_nonneg _) (Real.exp_nonneg _))
  · dsimp [P]
    rw [←mul_assoc,matrix_qr,mul_assoc,hEq t ht,←mul_assoc,he t]
end SmoothObstruction.QR

namespace SmoothObstruction.QR
open MeasureTheory Filter Topology Finset
open scoped Matrix.Norms.L2Operator
variable {d : ℕ} {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Compactness bounds both the actual derivative and every positive QR
log-diagonal. The frame is arbitrary, so no measurable choice is hidden. -/
lemma exists_uniform_qr_bound
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x).toContinuousLinearMap)) :
    ∃ R : ℝ, 0≤R ∧ (∀ x,‖(A x).toContinuousLinearMap‖≤Real.exp R) ∧
      ∀ (x : X) (e : Frame d) j, |Real.log (triangular (A x) e j j)|≤R := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hA.continuousOn
  have hb : ∀ j : Fin d,∃ B : ℝ,∀ z : X × Frame d,
      |Real.log (triangular (A z.1) z.2 j j)|≤B := by
    intro j
    obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_log_diagonal A hA j).continuousOn
    exact ⟨B,fun z => hB z (Set.mem_univ _)⟩
  choose B hB using hb
  let R := |C|+∑ j,|B j|+1
  have hR : 0≤R := by dsimp [R]; positivity
  have hCR : C≤R := by
    have hs : 0≤∑ j,|B j| := sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [R]; linarith [le_abs_self C]
  refine ⟨R,hR,fun x => (hC x (Set.mem_univ _)).trans (hCR.trans ?_),?_⟩
  · linarith [Real.add_one_le_exp R]
  · intro x e j
    have hj := single_le_sum (f:=fun j : Fin d => |B j|) (fun _ _ => abs_nonneg _) (mem_univ j)
    have hh := (hB j (x,e)).trans (le_abs_self (B j))
    dsimp [R]
    linarith [abs_nonneg C]

omit [MetricSpace X] [CompactSpace X] in
lemma skew_iterate_fst (T : X → X)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (z : X × Frame d) (t : ℕ) : ((skew T A)^[t] z).1=T^[t] z.1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [Function.iterate_succ_apply',skew,ih]

omit [MetricSpace X] [CompactSpace X] in
lemma log_error_is_chord (T : X → X)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (z : X × Frame d) (N t : ℕ) (j : Fin d) :
    NormalizedGauge.error
      (fun a => triangular (A ((skew T A)^[a] z).1) ((skew T A)^[a] z).2)
      (fun i => DyadicChord.average
        (DyadicChord.orbit (skew T A) (fun w => Real.log (triangular (A w.1) w.2 i i)) z) N) t j=
    DyadicChord.chord
      (DyadicChord.orbit (skew T A) (fun w => Real.log (triangular (A w.1) w.2 j j)) z) N t := by
  simp only [NormalizedGauge.error,DyadicChord.chord,DyadicChord.prefixSum,
    DyadicChord.orbit,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]

lemma average_abs_le {f : ℕ → ℝ} {R : ℝ} {N : ℕ} (hN : 0<N)
    (hf : ∀ t<N,|f t|≤R) : |DyadicChord.average f N|≤R := by
  rw [DyadicChord.average,abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  calc
    |DyadicChord.prefixSum f N|≤∑ t∈range N,|f t| := by
      exact abs_sum_le_sum_abs _ _
    _≤∑ t∈range N,R := sum_le_sum (fun t ht => hf t (mem_range.mp ht))
    _=R*N := by simp only [sum_const,card_range,nsmul_eq_mul]; ring

/-- Finite gauges for genuine good QR orbit segments. Positivity and
triangularity come from the actual Gram--Schmidt process, and the chord
errors are identified with the stationary quantities, not assumed anew. -/
theorem compact_good_gauge (T : X → X)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x).toContinuousLinearMap)) :
    ∃ R C : ℝ,0≤R ∧ 0≤C ∧ ∀ k b (z : X × Frame d),
      z∈GoodStationary.Good (skew T A)
        (fun j w => Real.log (triangular (A w.1) w.2 j j)) k b →
      1≤b*(2:ℝ)^k → Real.log ((2^(k+1):ℕ)+1)≤b*(2:ℝ)^k →
      ∃ (lam : Fin d → ℝ) (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ),
        (∀ j,|lam j|≤R) ∧ (∀ t,P t*Q t=1 ∧ Q t*P t=1) ∧
        (∀ t≤2^(k+1),‖P t‖≤Real.exp (C*(b*2^k))) ∧
        (∀ t≤2^(k+1),‖Q t‖≤Real.exp (C*(b*2^k))) ∧
        (∀ t<2^(k+1),
          (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (A (T^[t] z.1)).toContinuousLinearMap*P t=
            P (t+1)*EuclideanSplitting.rate lam 1) := by
  obtain ⟨R,hR,hAR,hlogR⟩ := exists_uniform_qr_bound A hA
  obtain ⟨C,hC,hg⟩ := EuclideanSplitting.exists_operator_gauge d R hR
  refine ⟨R,C,hR,hC,?_⟩
  intro k b z hz hb hn
  let w := fun t => (skew T A)^[t] z
  let L := fun t => A (w t).1
  let e := fun t => (w t).2
  let B := fun t => triangular (L t) (e t)
  let lam := fun j => DyadicChord.average
    (DyadicChord.orbit (skew T A) (fun w => Real.log (triangular (A w.1) w.2 j j)) z) (2^(k+1))
  have hlam : ∀ j,|lam j|≤R := by
    intro j
    exact average_abs_le (pow_pos (by omega : 0<2) _) (fun t _ => hlogR _ _ j)
  have he : ∀ t,e (t+1)=step (L t) (e t) := by
    intro t
    simp only [e,L,w,Function.iterate_succ_apply',skew]
  have herr : ∀ t≤2^(k+1),∀ j,|NormalizedGauge.error B lam t j|≤b*2^k := by
    intro t ht j
    rw [show NormalizedGauge.error B lam t j=
      DyadicChord.chord
        (DyadicChord.orbit (skew T A) (fun w => Real.log (triangular (A w.1) w.2 j j)) z)
        (2^(k+1)) t from log_error_is_chord T A z _ _ _]
    exact hz j t ht
  obtain ⟨U,V,hUV,hU,hV,hEq⟩ := hg (2^(k+1)) (b*2^k) B lam hb hn
    (fun t _ => triangular_upper _ _) (fun t _ => diagonal_pos _ _)
    (fun t _ i j => (triangular_bound _ _ i j).trans (hAR _)) hlam herr
  obtain ⟨P,Q,hPQ,hP,hQ,hStep⟩ := transfer_gauge L e he U V lam (2^(k+1)) (C*(b*2^k))
    hUV hU hV hEq
  refine ⟨lam,P,Q,hlam,hPQ,hP,hQ,?_⟩
  intro t ht
  simpa only [L,w,skew_iterate_fst] using hStep t ht
end SmoothObstruction.QR

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Charts
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.GoodStationary
open Filter Topology

lemma floor_burden_eq (k : ℕ) :
    floorAt k*(2:ℝ)^k=Real.exp ((9*Real.log 2/10)*(k:ℝ)) := by
  have hp : (2:ℝ)^k=Real.exp (Real.log 2*(k:ℝ)) := by
    rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [floorAt,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),hp,←Real.exp_add]
  congr 1
  ring

lemma burden_ge_one (b : ℕ → ℝ) (hb : ∀ k,floorAt k≤b k) (k : ℕ) :
    1≤b k*(2:ℝ)^k := by
  have hc : 0≤9*Real.log 2/10 := by positivity
  have he := Real.one_le_exp_iff.mpr (mul_nonneg hc (Nat.cast_nonneg k))
  rw [←floor_burden_eq] at he
  exact he.trans (mul_le_mul_of_nonneg_right (hb k) (pow_nonneg (by norm_num) _))

lemma eventual_log_le_burden (b : ℕ → ℝ) (hb : ∀ k,floorAt k≤b k) :
    ∀ᶠ k in atTop,Real.log ((2^(k+1):ℕ)+1)≤b k*(2:ℝ)^k := by
  have hc : 0<9*Real.log 2/10 := by positivity
  have ho := (isLittleO_pow_exp_pos_mul_atTop 1 hc).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)
  filter_upwards [ho.bound (show (0:ℝ)<1/3 by norm_num),Filter.eventually_ge_atTop 1] with k hk hk1
  simp only [Function.comp_apply,pow_one,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k),
    abs_of_pos (Real.exp_pos _)] at hk
  have hpow : ((2^(k+1):ℕ):ℝ)+1≤(2:ℝ)^(k+2) := by
    have hh : (1:ℝ)≤2^(k+1) := one_le_pow₀ (by norm_num)
    calc
      _ = (2:ℝ)^(k+1)+1 := by norm_cast
      _ ≤ (2:ℝ)^(k+1)*2 := by linarith
      _ = (2:ℝ)^(k+2) := by simp only [show k+2=(k+1)+1 by omega,pow_succ]
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<((2^(k+1):ℕ):ℝ)+1) hpow
  rw [Real.log_pow] at hlog
  have h2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hkk : (k:ℝ)+2≤3*k := by exact_mod_cast (show k+2≤3*k by omega)
  have hlog' : Real.log (((2^(k+1):ℕ):ℝ)+1)≤3*k := by
    exact hlog.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (by simpa using hkk))
  have he : 3*(k:ℝ)≤floorAt k*2^k := by rw [floor_burden_eq]; linarith
  exact hlog'.trans (he.trans (mul_le_mul_of_nonneg_right (hb k) (by positivity)))
end SmoothObstruction.GoodStationary

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma code_iterate (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K) (x : X) (t : ℕ) :
    shift^[t] (code S A x)=code S A (S^[t] x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,←code_shift,Function.iterate_succ_apply']

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma matrix_at_actual (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (p : Path (X:=X) (d:=d) (K:=K)) (hp : p∈Actual S A) (t : ℕ) :
    (matrix (shift^[t] p)).toContinuousLinearMap=(A (S^[t] (p 0).1)).val := by
  have he : shift^[t] p=code S A (S^[t] (p 0).1) := by
    conv_lhs => rw [show p=code S A (p 0).1 from hp]
    exact code_iterate S A (p 0).1 t
  rw [he]
  simp only [matrix,code,zpow_zero,Homeomorph.one_apply]
  rfl

/-- Quantitative finite gauges for the genuine bounded measurable cocycle.
The compact stationary QR lift, square-summable burdens, compact good
sets, and their original base masses are all constructed. On every good
witness the operator identity uses the ACTUAL original cocycle, not a
free triangular surrogate or a separately assumed frame process. -/
theorem actual_good_gauges (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) (μ : ProbabilityMeasure X)
    (hS : MeasurePreserving S (μ : Measure X) (μ : Measure X))
    {η : ℝ} (hη : 0<η) :
    ∃ (ν : ProbabilityMeasure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d))
      (b : ℕ → ℝ) (G : ℕ → Set (Path (X:=X) (d:=d) (K:=K) × QR.Frame d))
      (R C : ℝ),
      0≤R ∧ 0≤C ∧ (∀ k,0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
      Summable (fun k => (b k)^2) ∧
      (∀ k,IsCompact (G k) ∧
        (∀ z∈G k,z.1∈Actual S A) ∧
        1-η/100≤(ν : Measure _).real (G k) ∧
        IsCompact ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k) ∧
        1-η/100≤(μ : Measure X).real ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k)) ∧
      ∀ᶠ k in atTop,∀ z∈G k,
        ∃ (lam : Fin d → ℝ) (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ),
          (∀ j,|lam j|≤R) ∧ (∀ t,P t*Q t=1 ∧ Q t*P t=1) ∧
          (∀ t≤2^(k+1),‖P t‖≤Real.exp (C*(b k*2^k))) ∧
          (∀ t≤2^(k+1),‖Q t‖≤Real.exp (C*(b k*2^k))) ∧
          (∀ t<2^(k+1),
            (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (A (S^[t] (z.1 0).1)).val*P t=
              P (t+1)*EuclideanSplitting.rate lam 1) := by
  let := TopologicalSpace.metrizableSpaceMetric (Path (X:=X) (d:=d) (K:=K))
  obtain ⟨ν,b,G,hbp,hbf,hbs,hG⟩ := compact_actual_good S A hA μ hS hη
  obtain ⟨R,C,hR,hC,hg⟩ := QR.compact_good_gauge
    (shift (X:=X) (d:=d) (K:=K)) matrix continuous_matrix
  refine ⟨ν,b,G,R,C,hR,hC,hbp,hbf,hbs,fun k => ?_,?_⟩
  · exact ⟨(hG k).1,fun z hz => ((hG k).2.1 z hz).1,(hG k).2.2⟩
  · filter_upwards [GoodStationary.eventual_log_le_burden b hbf] with k hk
    intro z hz
    obtain ⟨lam,P,Q,hlam,hPQ,hP,hQ,hEq⟩ := hg k (b k) z ((hG k).2.1 z hz).2
      (GoodStationary.burden_ge_one b hbf k) hk
    refine ⟨lam,P,Q,hlam,hPQ,hP,hQ,fun t ht => ?_⟩
    have ha := ((hG k).2.1 z hz).1
    simpa only [matrix_at_actual S A z.1 ha] using hEq t ht
end SmoothObstruction.OrbitCocycle

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
universe u
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Actual compact-manifold derivative gauges, constructed uniformly from
smoothness, compactness and the invariant original probability. The finite
chart selector, stationary frame lift, summable error sequence, large
compact middle-point sets and two-sided invertible gauges are all produced.
This is the linear input to the nonlinear switching proof, not that proof. -/
theorem manifold_good_gauges_discrete (S : Diffeomorph I I M M ∞)
    (μ : ProbabilityMeasure M) (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M))
    {η : ℝ} (hη : 0<η) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : MeasurableSpace ι) (_ : MeasurableSingletonClass ι)
      (a : ι → M) (K : ι → Set M) (c : M → ι) (D : ℝ)
      (A : M → CompactMatrix.Alphabet d D),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆(chartAt H (a i)).source) ∧
      Measurable c ∧ (∀ x,x∈K (c x)) ∧ 0<D ∧ Measurable A ∧
      (∀ x,(A x).val=coord I S (a (c x)) (a (c (S x))) x) ∧
      ∃ (ν : ProbabilityMeasure (OrbitCocycle.Path (X:=M) (d:=d) (K:=D) × QR.Frame d))
        (b : ℕ → ℝ) (G : ℕ → Set (OrbitCocycle.Path (X:=M) (d:=d) (K:=D) × QR.Frame d))
        (R C : ℝ),
        0≤R ∧ 0≤C ∧ (∀ k,0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
        Summable (fun k => (b k)^2) ∧
        (∀ k,IsCompact (G k) ∧
          (∀ z∈G k,z.1∈OrbitCocycle.Actual S.toHomeomorph A) ∧
          1-η/100≤(ν : Measure _).real (G k) ∧
          IsCompact ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k) ∧
          1-η/100≤(μ : Measure M).real ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k)) ∧
        ∀ᶠ k in atTop,∀ z∈G k,
          ∃ (lam : Fin d → ℝ) (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ),
            (∀ j,|lam j|≤R) ∧ (∀ t,P t*Q t=1 ∧ Q t*P t=1) ∧
            (∀ t≤2^(k+1),‖P t‖≤Real.exp (C*(b k*2^k))) ∧
            (∀ t≤2^(k+1),‖Q t‖≤Real.exp (C*(b k*2^k))) ∧
            (∀ t<2^(k+1),let x := S^[t] (z.1 0).1
              (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
                (coord I S (a (c x)) (a (c (S x))) x)*P t=
                P (t+1)*EuclideanSplitting.rate lam 1) := by
  obtain ⟨ι,hfin,hmeas,hsc,a,K,c,D,A,hK,hKU,hc,hcK,hD,hA,heq⟩ := actual_coordinate_cocycle_discrete I S
  let : Fintype ι := hfin
  let : MeasurableSpace ι := hmeas
  obtain ⟨ν,b,G,R,C,hR,hC,hbp,hbf,hbs,hG,hg⟩ :=
    OrbitCocycle.actual_good_gauges S.toHomeomorph A hA μ hS hη
  refine ⟨ι,hfin,hmeas,hsc,a,K,c,D,A,hK,hKU,hc,hcK,hD,hA,heq,
    ν,b,G,R,C,hR,hC,hbp,hbf,hbs,hG,?_⟩
  filter_upwards [hg] with k hk
  intro z hz
  obtain ⟨lam,P,Q,hlam,hPQ,hP,hQ,hEq⟩ := hk z hz
  refine ⟨lam,P,Q,hlam,hPQ,hP,hQ,fun t ht => ?_⟩
  simpa only [heq,Diffeomorph.coe_toHomeomorph] using hEq t ht
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Actual reverse derivative in a pair of fixed charts, also at boundary points. -/
lemma coord_inverse_step (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈(chartAt H a).source) (hy : S x∈(chartAt H b).source) :
    coord I S.symm b a (S x)*coord I S a b x=1 := by
  have hi : (mfderiv I I S.symm (S x)).comp (mfderiv I I S x)=
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    rw [←mfderiv_comp x (S.symm.mdifferentiable (by simp) _) (S.mdifferentiable (by simp) _)]
    have he : ((S.symm : M → M) ∘ (S : M → M))=id := by
      funext y
      exact S.symm_apply_apply y
    rw [he,mfderiv_id]
  rw [coord,coord]
  rw [ContinuousLinearMap.inCoordinates_eq hy (by simpa using hx),
    ContinuousLinearMap.inCoordinates_eq hx hy]
  ext v : 1
  simp only [mul_apply_eq_comp,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  have hv := congrArg (fun f => f (((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x hx).symm v)) hi
  change (mfderiv I I S.symm (S x)) ((mfderiv I I S x)
    (((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x hx).symm v))=
    ((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x hx).symm v at hv
  have hh := congrArg (fun w => ((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x hx) w) hv
  rw [ContinuousLinearEquiv.apply_symm_apply] at hh
  convert hh using 1
  · change ((trivializationAt (E (d:=d)) (TangentSpace I) a)
      (⟨S.symm (S x),_⟩ : TotalSpace (E (d:=d)) (TangentSpace I))).2=
      ((trivializationAt (E (d:=d)) (TangentSpace I) a)
      (⟨x,_⟩ : TotalSpace (E (d:=d)) (TangentSpace I))).2
    congr 2
    exact Bundle.TotalSpace.ext (S.symm_apply_apply x) HEq.rfl
  · rfl
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.OrbitCocycle
open Set
variable {X : Type*} [MetricSpace X] {d : ℕ} {K : ℝ}

lemma homeomorph_pow_iterate (S : X ≃ₜ X) (x : X) (n : ℕ) :
    (S^n) x=S^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Homeomorph.mul_apply,Function.iterate_succ_apply',ih]

lemma actual_middle (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (p : Path (X:=X) (d:=d) (K:=K)) (hp : p∈Actual S A) (n : ℕ) :
    (p (n:ℤ)).1=S^[n] (p 0).1 := by
  conv_lhs => rw [show p=code S A (p 0).1 from hp]
  simp only [code,zpow_natCast]
  exact homeomorph_pow_iterate S _ n

lemma backward_center (S : X ≃ₜ X) (x : X) {n t : ℕ} (ht : t≤n) :
    S.symm^[t] (S^[n] x)=S^[n-t] x := by
  have he : n=t+(n-t) := by omega
  conv_lhs => rw [he,Function.iterate_add_apply]
  exact (show Function.LeftInverse S.symm S from S.symm_apply_apply).iterate t _
end SmoothObstruction.OrbitCocycle

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Reversing a genuine finite derivative gauge is exact; the backward
rates are the negatives of the forward rates, and the same center basis
is used. No second derivative of a long iterate is introduced. -/
lemma reverse_gauge_step (S : Diffeomorph I I M M ∞)
    (c : ℕ → M) (x : ℕ → M) (P : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (j : ℕ)
    (hx : S (x j)=x (j+1))
    (hsrc : x j∈(chartAt H (c j)).source)
    (htar : x (j+1)∈(chartAt H (c (j+1))).source)
    (hstep : (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S (c j) (c (j+1)) (x j))*P j=
        P (j+1)*EuclideanSplitting.rate lam 1) :
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S.symm (c (j+1)) (c j) (x (j+1)))*P (j+1)=
        P j*EuclideanSplitting.rate (fun i => -lam i) 1 := by
  let F := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
  let A := F.symm (coord I S (c j) (c (j+1)) (x j))
  let Z := F.symm (coord I S.symm (c (j+1)) (c j) (x (j+1)))
  have hZA : Z*A=1 := by
    rw [←map_mul,←hx,coord_inverse_step I S _ _ _ hsrc (by rwa [hx]),map_one]
  have hrate : EuclideanSplitting.rate lam 1*
      EuclideanSplitting.rate (fun i => -lam i) 1=1 := by
    have he : EuclideanSplitting.rate (fun i => -lam i) 1=
        EuclideanSplitting.rate lam (-1) := by simp [EuclideanSplitting.rate]
    rw [he,←EuclideanSplitting.rate_add]
    norm_num
  change Z*P (j+1)=_
  calc
    Z*P (j+1)=(Z*P (j+1))*
        (EuclideanSplitting.rate lam 1*EuclideanSplitting.rate (fun i => -lam i) 1) := by
      rw [hrate,mul_one]
    _=Z*(P (j+1)*EuclideanSplitting.rate lam 1)*
        EuclideanSplitting.rate (fun i => -lam i) 1 := by noncomm_ring
    _=Z*(A*P j)*EuclideanSplitting.rate (fun i => -lam i) 1 := by rw [←hstep]
    _=P j*EuclideanSplitting.rate (fun i => -lam i) 1 := by
      rw [←mul_assoc Z A,hZA,one_mul]
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
universe u
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma center_from_gauge (S : Diffeomorph I I M M ∞) {ι : Type*}
    (a : ι → M) (c : M → ι) (hc : ∀ x,x∈(chartAt H (a (c x))).source)
    (x₀ : M) (n : ℕ) (B R : ℝ)
    (lam : Fin d → ℝ) (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hlam : ∀ i,|lam i|≤R) (hPQ : ∀ t,P t*Q t=1 ∧ Q t*P t=1)
    (hb : ∀ t≤n+n,‖P t‖≤Real.exp B ∧ ‖Q t‖≤Real.exp B)
    (hstep : ∀ t<n+n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S (a (c (S^[t] x₀))) (a (c (S^[t+1] x₀))) (S^[t] x₀))*P t=
        P (t+1)*EuclideanSplitting.rate lam 1) :
    Nonempty (BilateralGauge I S a c n B R (S^[n] x₀)) := by
  have hf (t : ℕ) : S^[t] (S^[n] x₀)=S^[n+t] x₀ := by
    rw [Nat.add_comm n t,Function.iterate_add_apply]
  have hr (t : ℕ) (ht : t≤n) : S.symm^[t] (S^[n] x₀)=S^[n-t] x₀ :=
    OrbitCocycle.backward_center S.toHomeomorph x₀ ht
  refine ⟨{
    lam := lam
    rate_bound := hlam
    UF := fun t => P (n+t)
    VF := fun t => Q (n+t)
    UB := fun t => P (n-t)
    VB := fun t => Q (n-t)
    invF := fun t => hPQ (n+t)
    invB := fun t => hPQ (n-t)
    centerU := by simp
    centerV := by simp
    normF := fun t ht => hb (n+t) (by omega)
    normB := fun t ht => hb (n-t) (by omega)
    stepF := ?_
    stepB := ?_
  }⟩
  · intro t ht
    simp only [hf,←Nat.add_assoc]
    exact hstep (n+t) (by omega)
  · intro t ht
    rw [hr t ht.le,hr (t+1) (by omega)]
    have he : n-(t+1)+1=n-t := by omega
    have hh := reverse_gauge_step I S (fun j => a (c (S^[j] x₀)))
      (fun j => S^[j] x₀) P lam (n-(t+1))
      (by simp only [Function.iterate_succ_apply']) (hc _) (hc _)
      (hstep _ (by omega))
    simpa only [he] using hh

/-- The compact, large original-measure good base sets now carry actual
forward AND backward gauges about their own time-zero point. The QR path
witness is eliminated existentially; no measurable frame selection is used. -/
theorem good_bilateral_gauges [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : Diffeomorph I I M M ∞) (μ : ProbabilityMeasure M)
    (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M)) {η : ℝ} (hη : 0<η) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : MeasurableSpace ι) (_ : MeasurableSingletonClass ι)
      (a : ι → M) (K : ι → Set M) (c : M → ι),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆(chartAt H (a i)).source) ∧
      Measurable c ∧ (∀ x,x∈K (c x)) ∧
      ∃ (b : ℕ → ℝ) (R C : ℝ) (G : ℕ → Set M),
        0≤R ∧ 0≤C ∧ (∀ k,0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
        Summable (fun k => (b k)^2) ∧
        (∀ k,IsCompact (G k) ∧ 1-η/100≤(μ : Measure M).real (G k)) ∧
        ∀ᶠ k in atTop,∀ x∈G k,
          Nonempty (BilateralGauge I S a c (2^k) (C*(b k*2^k)) R x) := by
  obtain ⟨ι,hfin,hmeas,hsc,a,K,c,D,A,hK,hKU,hc,hcK,hD,hA,heq,
    ν,b,F,R,C,hR,hC,hbp,hbf,hbs,hF,hg⟩ := manifold_good_gauges_discrete I S μ hS hη
  let : Fintype ι := hfin
  let : MeasurableSpace ι := hmeas
  let G (k : ℕ) := (fun z : OrbitCocycle.Path (X:=M) (d:=d) (K:=D) × QR.Frame d =>
    (z.1 ((2^k:ℕ):ℤ)).1) '' F k
  refine ⟨ι,hfin,hmeas,hsc,a,K,c,hK,hKU,hc,hcK,b,R,C,G,hR,hC,hbp,hbf,hbs,
    fun k => ⟨(hF k).2.2.2.1,(hF k).2.2.2.2⟩,?_⟩
  filter_upwards [hg] with k hk
  rintro x ⟨z,hz,rfl⟩
  obtain ⟨lam,P,Q,hlam,hPQ,hP,hQ,hstep⟩ := hk z hz
  have he := OrbitCocycle.actual_middle S.toHomeomorph A z.1 ((hF k).2.1 z hz) (2^k)
  change (z.1 ((2^k:ℕ):ℤ)).1=S^[2^k] (z.1 0).1 at he
  dsimp only
  rw [he]
  have hn : (2^k:ℕ)+2^k=2^(k+1) := by rw [pow_succ]; omega
  apply center_from_gauge I S a c (fun x => hKU _ (hcK x)) (z.1 0).1 (2^k)
    (C*(b k*2^k)) R lam P Q hlam hPQ
  · intro t ht
    exact ⟨hP t (by rwa [←hn]),hQ t (by rwa [←hn])⟩
  · intro t ht
    have hh := hstep t (by rwa [←hn])
    simpa only [Function.iterate_succ_apply'] using hh
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma chartChange_coe (a b x : M) (ha : x∈(chartAt H a).source)
    (hb : x∈(chartAt H b).source) :
    (chartChange I a b x ha hb : E (d:=d) →L[ℝ] E (d:=d))=
      coord I (Diffeomorph.refl I M ∞) a b x := by
  rw [coord,ContinuousLinearMap.inCoordinates_eq ha hb]
  simp only [Diffeomorph.coe_refl,mfderiv_id]
  rfl

/-- Exact cocycle conjugation for independently fixed carried charts.
This is a relation between actual manifold derivatives, not a formal
similarity hypothesis supplied in place of them. -/
theorem coord_chart_change (S : Diffeomorph I I M M ∞) (a b a' b' x : M)
    (hx : x∈domain I S a b) (hx' : x∈domain I S a' b') :
    coord I S a' b' x=
      (chartChange I b b' (S x) hx.2 hx'.2 : E (d:=d) →L[ℝ] E (d:=d)) *
      coord I S a b x *
      (chartChange I a' a x hx'.1 hx.1 : E (d:=d) →L[ℝ] E (d:=d)) := by
  rw [←coordEquiv_coe I S a b x hx,←coordEquiv_coe I S a' b' x hx']
  ext v
  simp only [mul_apply_eq_comp,ContinuousLinearEquiv.coe_coe,
    coordEquiv,chartChange,ContinuousLinearEquiv.trans_apply]
  simp

lemma chartChange_inverse (a b x : M) (ha : x∈(chartAt H a).source)
    (hb : x∈(chartAt H b).source) :
    (chartChange I a b x ha hb).symm=chartChange I b a x hb ha := by
  ext v
  simp [chartChange]

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.CarriedCharts
open Set Metric
variable {M : Type*} [MetricSpace M] {ι : Type*} [Fintype ι]

lemma finite_positive_lower (r : ι → ℝ) (hr : ∀ i,0 < r i) :
    ∃ a : ℝ,0 < a ∧ ∀ i,a ≤ r i := by
  classical
  have hh (s : Finset ι) : ∃ a : ℝ,0 < a ∧ ∀ i∈s,a ≤ r i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a,ha,has⟩ := ih
      refine ⟨min a (r i),lt_min ha (hr i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hj|hj
      · subst j; exact min_le_right _ _
      · exact (min_le_left _ _).trans (has j hj)
  obtain ⟨a,ha,hh⟩ := hh Finset.univ
  exact ⟨a,ha,fun i => hh i (Finset.mem_univ i)⟩

end SmoothObstruction.CarriedCharts

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Uniform bounds on actual chart conversions throughout fixed enlarged
compact patches. Thus gauges may be transported from a discontinuously
selected atlas to a carried atlas without adding point/scale-dependent
constants. These are derivatives of the identity on M, also at its boundary. -/
theorem uniform_chart_changes (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r D : ℝ,0 < r ∧ 1 ≤ D ∧ ∀ i j x,
      x∈cthickening r (K i) → x∈cthickening r (K j) →
      x∈(chartAt H (a i)).source ∧ x∈(chartAt H (a j)).source ∧
      ‖coord I (Diffeomorph.refl I M ∞) (a i) (a j) x‖ ≤ D ∧
      ‖coord I (Diffeomorph.refl I M ∞) (a j) (a i) x‖ ≤ D := by
  have hex (i : ι) : ∃ r : ℝ,0 < r ∧ cthickening r (K i)⊆(chartAt H (a i)).source :=
    (hK i).exists_cthickening_subset_open (chartAt H (a i)).open_source (hKU i)
  choose r hr hrU using hex
  obtain ⟨r₀,hr₀,hr₀r⟩ := CarriedCharts.finite_positive_lower r hr
  let N (i : ι) := cthickening (r i) (K i)
  have hNC (i : ι) : IsCompact (N i) := (hK i).cthickening
  have hb (ij : ι×ι) : ∃ D : ℝ,∀ x∈N ij.1∩N ij.2,
      ‖coord I (Diffeomorph.refl I M ∞) (a ij.1) (a ij.2) x‖ ≤ D :=
    ((hNC ij.1).inter (hNC ij.2)).exists_bound_of_continuousOn
      ((continuousOn_coord I (Diffeomorph.refl I M ∞) (a ij.1) (a ij.2)).mono
        (fun x hx => ⟨hrU _ hx.1,hrU _ hx.2⟩))
  choose C hC using hb
  let D : ℝ := 1+∑ ij,|C ij|
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hCD (ij : ι×ι) : C ij ≤ D := by
    have hh := Finset.single_le_sum (fun z _ => abs_nonneg (C z)) (Finset.mem_univ ij)
    dsimp [D]
    linarith [le_abs_self (C ij)]
  refine ⟨r₀,D,hr₀,hD,fun i j x hxi hxj => ?_⟩
  have hi : x∈N i := cthickening_mono (hr₀r i) (K i) hxi
  have hj : x∈N j := cthickening_mono (hr₀r j) (K j) hxj
  exact ⟨hrU i hi,hrU j hj,(hC (i,j) x ⟨hi,hj⟩).trans (hCD (i,j)),
    (hC (j,i) x ⟨hj,hi⟩).trans (hCD (j,i))⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Uniformly transport genuine finite gauges between any selected and
carried chart sequences lying in the enlarged finite atlas. All norm losses
are the same fixed D; the actual manifold-derivative conjugation identity
is proved above, and is not an extra cocycle assumption. -/
theorem uniform_carried_gauge_explicit (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r D : ℝ,0 < r ∧ 1 ≤ D ∧
      ∀ (S : Diffeomorph I I M M ∞) (x : ℕ → M) (c e : ℕ → ι)
        (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (N : ℕ) (B : ℝ),
        (∀ t≤N,x t∈cthickening r (K (c t))) →
        (∀ t≤N,x t∈cthickening r (K (e t))) →
        (∀ t<N,S (x t)=x (t+1)) →
        (∀ t,P t*Q t=1 ∧ Q t*P t=1) →
        (∀ t≤N,‖P t‖≤Real.exp B ∧ ‖Q t‖≤Real.exp B) →
        (∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (c t)) (a (c (t+1))) (x t))*P t=
            P (t+1)*EuclideanSplitting.rate lam 1) →
        ∃ P' Q' : ℕ → Matrix (Fin d) (Fin d) ℝ,
          (∀ t≤N,P' t*Q' t=1 ∧ Q' t*P' t=1) ∧
          (∀ t≤N,‖P' t‖≤D*Real.exp B ∧ ‖Q' t‖≤D*Real.exp B) ∧
          (∀ t,P' t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t))*P t ∧
            Q' t=Q t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t))) ∧
          ∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S (a (e t)) (a (e (t+1))) (x t))*P' t=
              P' (t+1)*EuclideanSplitting.rate lam 1 := by
  classical
  obtain ⟨r,D,hr,hD,hh⟩ := uniform_chart_changes I a K hK hKU
  refine ⟨r,D,hr,hD,fun S x c e P Q lam N B hc he hx hPQ hb hEq => ?_⟩
  let F := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
  have hmem t (ht : t≤N) := hh (c t) (e t) (x t) (hc t ht) (he t ht)
  let R (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
    F.symm (coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t))
  let V (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
    F.symm (coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t))
  have hRV (t : ℕ) (ht : t≤N) : R t*V t=1 ∧ V t*R t=1 := by
    have hm := hmem t ht
    have hR := chartChange_coe I (a (c t)) (a (e t)) (x t) hm.1 hm.2.1
    have hV := chartChange_coe I (a (e t)) (a (c t)) (x t) hm.2.1 hm.1
    have hid : coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t) *
        coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t) = 1 := by
      have h := (chartChange I (a (c t)) (a (e t)) (x t) hm.1 hm.2.1).coe_comp_coe_symm
      rw [chartChange_inverse I _ _ _ hm.1 hm.2.1] at h
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, hR, hV] using h
    have hdi : coord I (Diffeomorph.refl I M ∞) (a (e t)) (a (c t)) (x t) *
        coord I (Diffeomorph.refl I M ∞) (a (c t)) (a (e t)) (x t) = 1 := by
      have h := (chartChange I (a (c t)) (a (e t)) (x t) hm.1 hm.2.1).coe_symm_comp_coe
      rw [chartChange_inverse I _ _ _ hm.1 hm.2.1] at h
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def, hR, hV] using h
    constructor
    · simpa only [map_mul,map_one,R,V] using congrArg F.symm hid
    · simpa only [map_mul,map_one,R,V] using congrArg F.symm hdi
  have hnorm (t : ℕ) (ht : t≤N) : ‖R t‖≤D ∧ ‖V t‖≤D := by
    have hh' := (hmem t ht).2.2
    simpa only [R,V,←Matrix.l2_opNorm_toEuclideanCLM,
      F,StarAlgEquiv.apply_symm_apply] using hh'
  have hconj (t : ℕ) (ht : t<N) : F.symm (coord I S (a (e t)) (a (e (t+1))) (x t))=
      R (t+1)*F.symm (coord I S (a (c t)) (a (c (t+1))) (x t))*V t := by
    have h₀ := hmem t ht.le
    have h₁ := hmem (t+1) (by omega)
    have hd₀ : x t∈domain I S (a (c t)) (a (c (t+1))) :=
      ⟨h₀.1,by simpa only [Set.mem_preimage, hx t ht] using h₁.1⟩
    have hd₁ : x t∈domain I S (a (e t)) (a (e (t+1))) :=
      ⟨h₀.2.1,by simpa only [Set.mem_preimage, hx t ht] using h₁.2.1⟩
    rw [coord_chart_change I S _ _ _ _ _ hd₀ hd₁]
    simp only [map_mul,chartChange_coe,hx t ht,R,V]
  refine ⟨fun t => R t*P t,fun t => Q t*V t,fun t ht => ?_,fun t ht => ?_,fun t => ⟨rfl,rfl⟩,fun t ht => ?_⟩
  · constructor
    · calc
        _=R t*(P t*Q t)*V t := by noncomm_ring
        _=1 := by rw [(hPQ t).1,mul_one,(hRV t ht).1]
    · calc
        _=Q t*(V t*R t)*P t := by noncomm_ring
        _=1 := by rw [(hRV t ht).2,mul_one,(hPQ t).2]
  · constructor
    · exact (norm_mul_le _ _).trans (mul_le_mul (hnorm t ht).1 (hb t ht).1
        (norm_nonneg _) (by linarith))
    · exact (norm_mul_le _ _).trans (by
        calc
          ‖Q t‖*‖V t‖ ≤ Real.exp B*D := mul_le_mul (hb t ht).2 (hnorm t ht).2
            (norm_nonneg _) (Real.exp_pos B).le
          _=D*Real.exp B := mul_comm _ _)
  · rw [hconj t ht]
    calc
      _=R (t+1)*F.symm (coord I S (a (c t)) (a (c (t+1))) (x t))*(V t*R t)*P t := by noncomm_ring
      _=R (t+1)*(F.symm (coord I S (a (c t)) (a (c (t+1))) (x t))*P t) := by
        rw [(hRV t ht.le).2,mul_one,mul_assoc]
      _=(R (t+1)*P (t+1))*EuclideanSplitting.rate lam 1 := by rw [hEq t ht,mul_assoc]
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

theorem uniform_carried_bilateral_explicit (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r D : ℝ,0 < r ∧ 1≤D ∧
      ∀ (S : Diffeomorph I I M M ∞) (c : M → ι) (x : M) (n : ℕ) (B R : ℝ)
        (A : BilateralGauge I S a c n B R x) (eF eB : ℕ → ι),
        (∀ y,y∈K (c y)) → eB 0=eF 0 →
        (∀ t≤n,S^[t] x∈cthickening r (K (eF t))) →
        (∀ t≤n,S.symm^[t] x∈cthickening r (K (eB t))) →
        ∃ F Z : ShortBin.Gauge d n (B+Real.log D),
          (∀ i,F.lam i=A.lam i) ∧ (∀ i,Z.lam i= -A.lam i) ∧
          Z.U 0=F.U 0 ∧ Z.V 0=F.V 0 ∧
          (∀ t<n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S (a (eF t)) (a (eF (t+1))) (S^[t] x))*F.U t=
              F.U (t+1)*EuclideanSplitting.rate F.lam 1) ∧
          (∀ t<n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S.symm (a (eB t)) (a (eB (t+1))) (S.symm^[t] x))*Z.U t=
              Z.U (t+1)*EuclideanSplitting.rate Z.lam 1) ∧
          ∀ t≤n,
            F.U t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (c (S^[t] x))) (a (eF t)) (S^[t] x))*A.UF t ∧
            F.V t=A.VF t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (eF t)) (a (c (S^[t] x))) (S^[t] x)) ∧
            Z.U t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (c (S.symm^[t] x))) (a (eB t)) (S.symm^[t] x))*A.UB t ∧
            Z.V t=A.VB t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (eB t)) (a (c (S.symm^[t] x))) (S.symm^[t] x)) := by
  obtain ⟨r,D,hr,hD,hcarry⟩ := uniform_carried_gauge_explicit I a K hK hKU
  refine ⟨r,D,hr,hD,fun S c x n B R A eF eB hc h0 heF heB => ?_⟩
  have hDpos : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hbound : D*Real.exp B=Real.exp (B+Real.log D) := by
    rw [Real.exp_add,Real.exp_log hDpos,mul_comm]
  have hmF t (_ht : t≤n) : S^[t] x∈cthickening r (K (c (S^[t] x))) :=
    self_subset_cthickening _ (hc _)
  have hmB t (_ht : t≤n) : S.symm^[t] x∈cthickening r (K (c (S.symm^[t] x))) :=
    self_subset_cthickening _ (hc _)
  obtain ⟨PF,QF,hiF,hbF,formF,stepF⟩ := hcarry S (fun t => S^[t] x)
    (fun t => c (S^[t] x)) eF A.UF A.VF A.lam n B hmF heF
    (fun t _ => (Function.iterate_succ_apply' _ _ _).symm) A.invF A.normF A.stepF
  obtain ⟨PB,QB,hiB,hbB,formB,stepB⟩ := hcarry S.symm (fun t => S.symm^[t] x)
    (fun t => c (S.symm^[t] x)) eB A.UB A.VB (fun i => -A.lam i) n B hmB heB
    (fun t _ => (Function.iterate_succ_apply' _ _ _).symm) A.invB A.normB A.stepB
  have hbF' t (ht : t≤n) : ‖PF t‖≤Real.exp (B+Real.log D) ∧ ‖QF t‖≤Real.exp (B+Real.log D) := by
    simpa only [hbound] using hbF t ht
  have hbB' t (ht : t≤n) : ‖PB t‖≤Real.exp (B+Real.log D) ∧ ‖QB t‖≤Real.exp (B+Real.log D) := by
    simpa only [hbound] using hbB t ht
  refine ⟨ShortBin.Gauge.ofFinite PF QF A.lam hiF hbF',
    ShortBin.Gauge.ofFinite PB QB (fun i => -A.lam i) hiB hbB',
    fun _ => rfl,fun _ => rfl,?_,?_,?_,?_,?_⟩
  · change PB (min 0 n)=PF (min 0 n)
    rw [Nat.zero_min,(formB 0).1,(formF 0).1]
    simp only [Function.iterate_zero_apply,h0,A.centerU]
  · change QB (min 0 n)=QF (min 0 n)
    rw [Nat.zero_min,(formB 0).2,(formF 0).2]
    simp only [Function.iterate_zero_apply,h0,A.centerV]
  · intro t ht
    simpa only [ShortBin.Gauge.ofFinite,Nat.min_eq_left ht.le,
      Nat.min_eq_left (show t+1≤n by omega)] using stepF t ht
  · intro t ht
    simpa only [ShortBin.Gauge.ofFinite,Nat.min_eq_left ht.le,
      Nat.min_eq_left (show t+1≤n by omega)] using stepB t ht
  · intro t ht
    simpa only [ShortBin.Gauge.ofFinite,Nat.min_eq_left ht] using
      And.intro (formF t).1 (And.intro (formF t).2 (formB t))

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_CoordinateTubes
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.CoordinateTubes
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

lemma isOpen_carrier (a : M) {U : Set M} (hU : IsOpen U) : IsOpen (carrier I a U) :=
  ((chartAt H a).isOpen_inter_preimage_symm hU).preimage I.continuous_symm

lemma coord_mem_carrier (a x : M) {U : Set M}
    (hx : x∈(chartAt H a).source) (hU : x∈U) :
    (extChartAt I a) x∈carrier I a U := by
  have ht := (extChartAt I a).map_source (by simpa only [extChartAt_source] using hx)
  have htar : I.symm ((extChartAt I a) x)∈(chartAt H a).target := by
    rw [extChartAt,OpenPartialHomeomorph.extend_target] at ht
    exact ht.1
  refine ⟨htar,?_⟩
  change (extChartAt I a).symm ((extChartAt I a) x)∈U
  rwa [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx)]

end SmoothObstruction.CoordinateTubes

namespace SmoothObstruction.CoordinateTubes
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]

/-- Uniform inverse-chart modulus on finitely many compact patches. This
works with a closed model range, so includes the closed half-space without
postulating an ambient extension of an inverse chart. -/
theorem uniform_inverse_modulus {ι : Type*} [Fintype ι]
    (hclosed : IsClosed (range I)) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKs : ∀ i,K i⊆(chartAt H (a i)).source)
    {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ i x,x∈K i → ∀ y,y∈(chartAt H (a i)).source →
      ‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖≤δ → dist y x<ε := by
  let L (i : ι) := (extChartAt I (a i)) '' K i
  have hL (i : ι) : IsCompact (L i) :=
    (hK i).image_of_continuousOn ((continuousOn_extChartAt (I:=I) (a i)).mono
      (fun _ hx => by simpa only [extChartAt_source] using hKs i hx))
  have hex (i : ι) : ∃ r : ℝ,0 < r ∧ cthickening r (L i)⊆carrier I (a i) univ := by
    apply (hL i).exists_cthickening_subset_open (isOpen_carrier I _ isOpen_univ)
    rintro z ⟨x,hx,rfl⟩
    exact coord_mem_carrier I _ _ (hKs i hx) (mem_univ _)
  choose r hr hu using hex
  let Q (i : ι) := cthickening (r i) (L i)∩range I
  have hQt (i : ι) : Q i⊆(extChartAt I (a i)).target := by
    intro z hz
    rw [extChartAt,OpenPartialHomeomorph.extend_target]
    exact ⟨(hu i hz.1).1,hz.2⟩
  have hQ (i : ι) : IsCompact (Q i) := (hL i).cthickening.inter_right hclosed
  have hm (i : ι) : ∃ s : ℝ,0 < s ∧ ∀ u∈Q i,∀ v∈Q i,dist u v < s →
      dist ((extChartAt I (a i)).symm u) ((extChartAt I (a i)).symm v)<ε :=
    Metric.uniformContinuousOn_iff.mp ((hQ i).uniformContinuousOn_of_continuous
      ((continuousOn_extChartAt_symm (I:=I) (a i)).mono (hQt i))) ε hε
  choose s hs hm using hm
  obtain ⟨δ,hδ,hδi⟩ := CarriedCharts.finite_positive_lower
    (fun i => min (r i) (s i/2)) (fun i => lt_min (hr i) (div_pos (hs i) (by norm_num)))
  refine ⟨δ,hδ,fun i x hx y hy hxy => ?_⟩
  have hxt : x∈(extChartAt I (a i)).source := by simpa only [extChartAt_source] using hKs i hx
  have hyt : y∈(extChartAt I (a i)).source := by simpa only [extChartAt_source] using hy
  have hxQ : (extChartAt I (a i)) x∈Q i := ⟨self_subset_cthickening (L i) ⟨x,hx,rfl⟩,
    by exact ⟨(chartAt H (a i)) x,rfl⟩⟩
  have hyQ : (extChartAt I (a i)) y∈Q i := ⟨
    mem_cthickening_of_dist_le _ _ _ _ ⟨x,hx,rfl⟩
      (by simpa only [dist_eq_norm] using hxy.trans ((hδi i).trans (min_le_left _ _))),
    ⟨(chartAt H (a i)) y,rfl⟩⟩
  have hh := hm i _ hyQ _ hxQ (show dist ((extChartAt I (a i)) y) ((extChartAt I (a i)) x) < s i from
    (by rw [dist_eq_norm]; exact lt_of_le_of_lt (hxy.trans ((hδi i).trans (min_le_right _ _))) (by linarith [hs i])))
  simpa only [(extChartAt I (a i)).left_inv hyt,(extChartAt I (a i)).left_inv hxt] using hh
end SmoothObstruction.CoordinateTubes

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SmoothScales
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.SmoothScales

lemma positive {b : ℝ} (hb : 0 < b) : 0 < B b := Real.rpow_pos_of_pos hb _

lemma root_sixteen {b : ℝ} (hb : 0 ≤ b) : (B b)^16 = b^2 := by
  rw [B, ← Real.rpow_natCast, ← Real.rpow_mul hb]
  norm_num

end SmoothObstruction.SmoothScales

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ProductCoordinates
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.AtlasCores
open Set MeasureTheory Metric
open scoped ENNReal NNReal
variable {M ι : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [Fintype ι]

/-- Compact cores of a finite measurable cover cost arbitrarily little of the
original measure. No relative distribution inside a selector fiber is used. -/
theorem finite_cores (μ : Measure M) [IsFiniteMeasure μ]
    [Measure.InnerRegularCompactLTTop μ] (A : ι → Set M)
    (hA : ∀ i,MeasurableSet (A i)) (hcover : ∀ x,∃ i,x∈A i)
    (ε : ℝ≥0) (hε : 0<ε) :
    ∃ K : ι → Set M,(∀ i,K i⊆A i) ∧ (∀ i,IsCompact (K i)) ∧
      μ (⋃ i,K i)ᶜ≤ε := by
  classical
  let δ : ℝ≥0 := ε/(Fintype.card ι+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  choose K hKA hK hμK using fun i =>
    (hA i).exists_isCompact_sdiff_lt (measure_ne_top μ (A i))
      (show (δ : ℝ≥0∞)≠0 by exact_mod_cast ne_of_gt hδ)
  refine ⟨K,hKA,hK,?_⟩
  have hsub : (⋃ i,K i)ᶜ⊆⋃ i,A i\K i := by
    intro x hx
    obtain ⟨i,hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i,hi,fun hk => hx (mem_iUnion.mpr ⟨i,hk⟩)⟩
  calc
    μ (⋃ i,K i)ᶜ≤μ (⋃ i,A i\K i) := measure_mono hsub
    _ ≤ ∑ i,μ (A i\K i) := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : ι,(δ : ℝ≥0∞) := Finset.sum_le_sum (fun i _ => (hμK i).le)
    _ = ((Fintype.card ι : ℝ≥0)*δ : ℝ≥0) := by simp
    _ ≤ (ε : ℝ≥0∞) := by
      exact_mod_cast (show (Fintype.card ι : ℝ≥0)*δ≤ε from by
        dsimp [δ]
        rw [←mul_div_assoc,div_le_iff₀ (show (0 : ℝ≥0)<Fintype.card ι+1 by positivity)]
        nlinarith)

/-- Positive finitely many scales have a positive common lower bound, including
an empty index type. This avoids a nonempty-atlas convention. -/
lemma finite_positive_min (a : ι → ℝ) (ha : ∀ i,0<a i) :
    ∃ r : ℝ,0 < r ∧ ∀ i,r≤a i := by
  classical
  have h : ∀ s : Finset ι,∃ r : ℝ,0 < r ∧ ∀ i∈s,r≤a i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨r,hr,hra⟩ := ih
      refine ⟨min r (a i),lt_min hr (ha i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hra j hj)
  obtain ⟨r,hr,hra⟩ := h Finset.univ
  exact ⟨r,hr,fun i => hra i (Finset.mem_univ i)⟩

omit [MeasurableSpace M] [BorelSpace M] in
/-- Disjoint compact chart cores admit one radius whose closed thickenings
remain pairwise disjoint and inside the designated open charts. -/
theorem separated_neighborhoods (K U : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i))
    (hKU : ∀ i,K i⊆U i) (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ r : ℝ,0 < r ∧ (∀ i,cthickening r (K i)⊆U i) ∧
      Pairwise (fun i j => Disjoint (cthickening r (K i)) (cthickening r (K j))) := by
  classical
  choose a ha hsub using fun i => (hK i).exists_cthickening_subset_open (hU i) (hKU i)
  obtain ⟨r,hr,hra⟩ := finite_positive_min a ha
  have hp (ij : ι×ι) : ∃ δ : ℝ,0<δ ∧
      (ij.1≠ij.2 → Disjoint (cthickening δ (K ij.1)) (cthickening δ (K ij.2))) := by
    by_cases h : ij.1=ij.2
    · exact ⟨1,by norm_num,fun hn => (hn h).elim⟩
    · obtain ⟨δ,hδ,hd⟩ := (hdisj h).exists_cthickenings (hK ij.1) (hK ij.2).isClosed
      exact ⟨δ,hδ,fun _ => hd⟩
  choose b hb hbd using hp
  obtain ⟨s,hs,hsb⟩ := finite_positive_min b hb
  refine ⟨min r s,lt_min hr hs,?_,?_⟩
  · intro i
    exact (cthickening_mono (le_trans (min_le_left _ _) (hra i)) _).trans (hsub i)
  · intro i j hij
    apply (hbd (i,j) hij).mono
    · exact cthickening_mono (le_trans (min_le_right _ _) (hsb (i,j))) _
    · exact cthickening_mono (le_trans (min_le_right _ _) (hsb (i,j))) _
/-- The finite atlas selector now yields coherent disjoint retained chart cores
and a single positive safety radius, with error measured in the ORIGINAL law. -/
theorem selector_cores [CompactSpace M] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (μ : Measure M) [IsFiniteMeasure μ]
    (c : M → ι) (hc : Measurable c) (U : ι → Set M)
    (hU : ∀ i,IsOpen (U i)) (hcU : ∀ x,x∈U (c x))
    (ε : ℝ≥0) (hε : 0<ε) :
    ∃ (K : ι → Set M) (r : ℝ),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆c ⁻¹' {i}) ∧
      μ (⋃ i,K i)ᶜ≤ε ∧ 0 < r ∧
      (∀ i,cthickening r (K i)⊆U i) ∧
      Pairwise (fun i j => Disjoint (cthickening r (K i)) (cthickening r (K j))) := by
  obtain ⟨K,hKA,hK,hμK⟩ := finite_cores μ (fun i => c ⁻¹' {i})
    (fun i => hc (measurableSet_singleton i)) (fun x => ⟨c x,rfl⟩) ε hε
  have hKU : ∀ i,K i⊆U i := by
    intro i x hx
    have he : c x=i := hKA i hx
    simpa only [he] using hcU x
  have hd : Pairwise (fun i j => Disjoint (K i) (K j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hij ((hKA i hx).symm.trans (hKA j hy))
  obtain ⟨r,hr,hsub,hsep⟩ := separated_neighborhoods K U hK hU hKU hd
  exact ⟨K,r,hK,hKA,hμK,hr,hsub,hsep⟩
end SmoothObstruction.AtlasCores

namespace SmoothObstruction.AtlasCores
open Set MeasureTheory Metric
open scoped ENNReal NNReal
variable {M ι : Type*} [MeasurableSpace M]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Modify a chart selector only in disjoint protected neighborhoods. On the
retained compact cores the new selector is genuinely locally constant, so
nearby switched endpoints recover the same chart label. -/
theorem protected_selector (c : M → ι) (hc : Measurable c)
    (U V : ι → Set M) (hV : ∀ i,MeasurableSet (V i))
    (hVU : ∀ i,V i⊆U i) (hcU : ∀ x,x∈U (c x))
    (hd : Pairwise (fun i j => Disjoint (V i) (V j))) :
    ∃ q : M → ι,Measurable q ∧ (∀ x,x∈U (q x)) ∧
      (∀ i,∀ x∈V i,q x=i) ∧
      ∀ x,x∉⋃ i,V i → q x=c x := by
  let W : ι → Set M := fun i => V i ∪ ((⋃ j,V j)ᶜ ∩ c ⁻¹' {i})
  have hW : ∀ i,MeasurableSet (W i) := fun i => (hV i).union
    ((MeasurableSet.iUnion hV).compl.inter (hc (measurableSet_singleton i)))
  have hcover : ∀ x,∃ i,x∈W i := by
    intro x
    by_cases hx : x∈⋃ i,V i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact ⟨i,Or.inl hi⟩
    · exact ⟨c x,Or.inr ⟨hx,rfl⟩⟩
  obtain ⟨q,hq,hqW⟩ := FiniteAtlas.measurable_selector W hW hcover
  have hqV : ∀ i,∀ x∈V i,q x=i := by
    intro i x hx
    rcases hqW x with h|h
    · by_contra hi
      exact Set.disjoint_left.mp (hd hi) h hx
    · exact (h.1 (mem_iUnion.mpr ⟨i,hx⟩)).elim
  refine ⟨q,hq,?_,hqV,?_⟩
  · intro x
    rcases hqW x with h|h
    · exact hVU _ h
    · have he : c x=q x := h.2
      rw [←he]
      exact hcU x
  · intro x hx
    rcases hqW x with h|h
    · exact (hx (mem_iUnion.mpr ⟨q x,h⟩)).elim
    · exact (show c x=q x from h.2).symm

end SmoothObstruction.AtlasCores

namespace SmoothObstruction.AtlasCores
open Set MeasureTheory Metric
open scoped ENNReal NNReal
variable {M ι : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Fintype ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A stable selector can be chosen in any prescribed positive enlargement
of the original compact patches. This preserves uniform chart bounds while
charging only one fixed compact-core error in the original measure. -/
theorem compact_stable_selector (μ : Measure M) [IsFiniteMeasure μ]
    (c : M → ι) (hc : Measurable c) (K : ι → Set M)
    (hcK : ∀ x,x∈K (c x))
    {r : ℝ} (hr : 0 < r) (ε : ℝ≥0) (hε : 0<ε) :
    ∃ (q : M → ι) (L : ι → Set M) (s : ℝ),
      Measurable q ∧ (∀ x,x∈cthickening r (K (q x))) ∧
      (∀ i,IsCompact (L i)) ∧ μ (⋃ i,L i)ᶜ≤ε ∧ 0 < s ∧
      (∀ i,L i⊆K i) ∧ (∀ i,∀ x∈L i,q x=i) ∧
      ∀ x∈⋃ i,L i,∀ y,dist y x ≤ s → q y=q x := by
  obtain ⟨L,s,hL,hLc,hm,hs,hLU,hd⟩ := selector_cores μ c hc
    (fun i => thickening r (K i)) (fun _ => isOpen_thickening)
    (fun x => self_subset_thickening hr _ (hcK x)) ε hε
  have hLK (i : ι) : L i⊆K i := by
    intro x hx
    have he : c x=i := hLc i hx
    simpa only [he] using hcK x
  obtain ⟨q,hq,hqU,hqL,_⟩ := protected_selector c hc
    (fun i => thickening r (K i)) (fun i => cthickening s (L i))
    (fun _ => isClosed_cthickening.measurableSet) hLU
    (fun x => self_subset_thickening hr _ (hcK x)) hd
  have hLq (i : ι) (x : M) (hx : x∈L i) : q x=i :=
    hqL i x (self_subset_cthickening _ hx)
  refine ⟨q,L,s,hq,fun x => thickening_subset_cthickening r _ (hqU x),hL,hm,hs,hLK,hLq,?_⟩
  intro x hx y hy
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  rw [hLq i x hi]
  exact hqL i y (mem_cthickening_of_dist_le y x s (L i) hi hy)
end SmoothObstruction.AtlasCores

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator NNReal ENNReal
universe u
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type u} [MetricSpace M] [CompactSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- Stable endpoint chart labels and actual good gauges are compatible.
The chart-core error is fixed before the dyadic sequence is constructed;
no orbit code or endpoint label is added to the future cell partition. -/
theorem good_stable_gauges (S : Diffeomorph I I M M ∞)
    (μ : ProbabilityMeasure M) (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M))
    {η : ℝ} (hη : 0<η) (ε : ℝ≥0) (hε : 0<ε) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : MeasurableSpace ι) (_ : MeasurableSingletonClass ι)
      (a : ι → M) (K L : ι → Set M) (q : M → ι) (s : ℝ),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆(chartAt H (a i)).source) ∧
      Measurable q ∧ (∀ x,x∈K (q x)) ∧
      (∀ i,IsCompact (L i)) ∧ (μ : Measure M) (⋃ i,L i)ᶜ≤ε ∧ 0 < s ∧
      (∀ i,L i⊆K i) ∧ (∀ i,∀ x∈L i,q x=i) ∧
      (∀ x∈⋃ i,L i,∀ y,dist y x ≤ s → q y=q x) ∧
      ∃ (b : ℕ → ℝ) (R C : ℝ) (G : ℕ → Set M),
        0≤R ∧ 0≤C ∧ (∀ k,0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
        Summable (fun k => (b k)^2) ∧
        (∀ k,IsCompact (G k) ∧ 1-η/100≤(μ : Measure M).real (G k)) ∧
        ∀ᶠ k in atTop,∀ x∈G k,
          Nonempty (BilateralGauge I S a q (2^k) (C*(b k*2^k)) R x) := by
  obtain ⟨ι,hfin,hmeas,hsc,a,K,c,hK,hKU,hc,hcK,b,R,C,G,hR,hC,hbp,hbf,hbs,hG,hg⟩ :=
    good_bilateral_gauges I S μ hS hη
  let : Fintype ι := hfin
  let : MeasurableSpace ι := hmeas
  let : MeasurableSingletonClass ι := hsc
  obtain ⟨r,D,hr,hD,hcarry⟩ := uniform_carried_bilateral_explicit I a K hK hKU
  choose r₀ hr₀ hr₀U using fun i =>
    (hK i).exists_cthickening_subset_open (chartAt H (a i)).open_source (hKU i)
  obtain ⟨t,ht,htr⟩ := CarriedCharts.finite_positive_lower r₀ hr₀
  let v := min r t
  have hv : 0<v := lt_min hr ht
  let K' (i : ι) := cthickening v (K i)
  have hK' (i : ι) : IsCompact (K' i) := (hK i).cthickening
  have hK'U (i : ι) : K' i⊆(chartAt H (a i)).source :=
    (cthickening_mono ((min_le_right r t).trans (htr i)) _).trans (hr₀U i)
  obtain ⟨q,L,s,hq,hqK,hL,hm,hs,hLK,hLq,hstable⟩ :=
    AtlasCores.compact_stable_selector (μ : Measure M) c hc K hcK hv ε hε
  let C' := C+Real.log D
  have hlog : 0≤Real.log D := Real.log_nonneg hD
  have hC' : 0≤C' := add_nonneg hC hlog
  refine ⟨ι,hfin,hmeas,hsc,a,K',L,q,s,hK',hK'U,hq,hqK,hL,hm,hs,
    fun i => (hLK i).trans (self_subset_cthickening _),hLq,hstable,
    b,R,C',G,hR,hC',hbp,hbf,hbs,hG,?_⟩
  filter_upwards [hg] with k hk
  intro x hx
  obtain ⟨A⟩ := hk x hx
  have hqK' y : y∈cthickening r (K (q y)) :=
    cthickening_mono (min_le_left r t) _ (hqK y)
  obtain ⟨F,Z,hFl,hZl,hU,hV,hFs,hZs,_⟩ := hcarry S c x (2^k) (C*(b k*2^k)) R A
    (fun t => q (S^[t] x)) (fun t => q (S.symm^[t] x)) hcK rfl
    (fun t _ => hqK' _) (fun t _ => hqK' _)
  have hbound : C*(b k*2^k)+Real.log D≤C'*(b k*2^k) := by
    have hn := GoodStationary.burden_ge_one b hbf k
    dsimp only [C']
    nlinarith
  have hexp := Real.exp_le_exp.mpr hbound
  refine ⟨{
    lam := A.lam
    rate_bound := A.rate_bound
    UF := F.U
    VF := F.V
    UB := Z.U
    VB := Z.V
    invF := fun t => ⟨F.UV t,F.VU t⟩
    invB := fun t => ⟨Z.UV t,Z.VU t⟩
    centerU := hU
    centerV := hV
    normF := fun t ht => ⟨(F.normU t ht).trans hexp,(F.normV t ht).trans hexp⟩
    normB := fun t ht => ⟨(Z.normU t ht).trans hexp,(Z.normV t ht).trans hexp⟩
    stepF := ?_
    stepB := ?_
  }⟩
  · intro t ht
    have hl : F.lam=A.lam := funext hFl
    simpa only [hl] using hFs t ht
  · intro t ht
    have hl : Z.lam=(fun i => -A.lam i) := funext hZl
    simpa only [hl] using hZs t ht
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SwitchRecovery
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric MeasureTheory Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    {ι : Type*} [Fintype ι]

/-- Uniform old-chart tubes give metric shadowing, with constants chosen
before the time length, orbit, chart selector, or frame witness. -/
theorem uniform_original_shadow (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {ε : ℝ} (hε : 0<ε) :
    ∃ σ : ℝ,0<σ ∧ ∀ (S : Diffeomorph I I M M ∞) (c : M → ι)
      (n : ℕ) (ρ : ℝ) (x z : M), (∀ u,u∈K (c u)) → ρ≤σ →
      originalTube I S a c (n:=n) ρ x z →
      ∀ t : Fin (n+1),dist (S^[t.val] z) (S^[t.val] x)<ε := by
  obtain ⟨σ,hσ,hm⟩ := CoordinateTubes.uniform_inverse_modulus I hclosed a K hK hKU hε
  refine ⟨σ,hσ,?_⟩
  intro S c n ρ x z hc hρ ht t
  exact hm _ _ (hc _) _ (ht t).1 ((ht t).2.trans hρ)

/-- The qualitative uniform shadowing assertion follows from the actual
sharp tube radii tending to zero. This does not assume a rate for an arbitrary
compatible metric on the compact manifold. -/
theorem original_shadow_tendsto (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (S : Diffeomorph I I M M ∞) (c : M → ι) (hc : ∀ u,u∈K (c u))
    (n : ℕ → ℕ) (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0))
    (G : ℕ → Set (M×M)) (Φ : ℕ → M×M → M×M)
    (ht : ∀ᶠ k in atTop,∀ u∈G k,
      originalTube I S a c (n:=n k) (ρ k) u.1 (Φ k u).1 ∧
      originalTube I S.symm a c (n:=n k) (ρ k) u.2 (Φ k u).1) :
    ∀ ε : ℝ,0<ε → ∀ᶠ k in atTop,∀ u∈G k,∀ t v : Fin (n k+1),
      dist (S^[t.val] (Φ k u).1) (S^[t.val] u.1)+
      dist (S.symm^[v.val] (Φ k u).1) (S.symm^[v.val] u.2)<ε := by
  intro ε hε
  obtain ⟨σ,hσ,hm⟩ := uniform_original_shadow I hclosed a K hK hKU (half_pos hε)
  filter_upwards [ht,hρ.eventually (gt_mem_nhds hσ)] with k hk hkρ u hu t v
  have h₁ := hm S c (n k) (ρ k) u.1 (Φ k u).1 hc hkρ.le (hk u hu).1 t
  have h₂ := hm S.symm c (n k) (ρ k) u.2 (Φ k u).1 hc hkρ.le (hk u hu).2 v
  linarith

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Counting
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.GridCount
open Filter Topology
lemma ceil_grid_bound {A t : ℝ} (hA : 0≤A) (ht : 0≤t) :
    ((2*⌈A*Real.exp t+1⌉₊+1:ℕ):ℝ)≤(2*A+5)*Real.exp t := by
  have hh := Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤A*Real.exp t+1)
  have he := Real.one_le_exp_iff.mpr ht
  push_cast
  nlinarith

/-- A uniform exponential count for the two original starting grids.
The strip-thinning denominator N cancels from the actual grid period. -/
theorem original_grid_count (d j : ℕ) (Dc Dp Dg : ℝ) (hDc : 1≤Dc) (hDp : 1≤Dp) (hDg : 0≤Dg) :
    ∃ C : ℝ,0≤C ∧ ∀ (b : ℝ) (n N : ℕ),0<b → b≤1 → 1≤b*n → 0<N →
      let B := Dg*(b*n)
      let t := b^(1/8:ℝ)*n
      let dc := Real.exp (-t)/(((d:ℝ)+1)*N)
      let dp := Real.exp (-2*t)/(Real.sqrt 2*((d:ℝ)+1)*N)
      let mc := ⌈Dc/(dc*N)+1⌉₊
      let mp := ⌈(Real.sqrt 2*Real.exp (2*B))*Dp/(dp*N)+1⌉₊
      ((j*(2*mc+1)^d*(2*mp+1)^d:ℕ):ℝ)≤Real.exp (C*t) := by
  let A₁ := Dc*((d:ℝ)+1)
  let A₂ := 2*Dp*((d:ℝ)+1)
  let K := (j:ℝ)*(2*A₁+5)^d*(2*A₂+5)^d
  have hA₁ : 0≤A₁ := by dsimp only [A₁]; positivity
  have hA₂ : 0≤A₂ := by dsimp only [A₂]; positivity
  have hK : 0≤K := by dsimp only [K]; positivity
  refine ⟨K+(3+2*Dg)*d,by positivity,?_⟩
  intro b n N hb hb1 hbn hN B t dc dp mc mp
  have hbroot : b≤b^(1/8:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hb hb1 (by norm_num : (1/8:ℝ)≤1)
  have htn : b*n≤t := mul_le_mul_of_nonneg_right hbroot (Nat.cast_nonneg _)
  have ht : 1≤t := hbn.trans htn
  have hB : B≤Dg*t := mul_le_mul_of_nonneg_left htn hDg
  have hB0 : 0≤B := by dsimp only [B]; positivity
  have hcs : Dc/(dc*N)=A₁*Real.exp t := by
    dsimp only [dc,A₁]
    rw [Real.exp_neg]
    field_simp
  have hps : (Real.sqrt 2*Real.exp (2*B))*Dp/(dp*N)=A₂*Real.exp (2*B+2*t) := by
    dsimp only [dp,A₂]
    rw [show -2*t= -(2*t) by ring,Real.exp_neg,Real.exp_add]
    have hs : Real.sqrt 2*Real.sqrt 2=2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    nlinarith only [hs]
  have hc := ceil_grid_bound hA₁ (by linarith : 0≤t)
  have hp := ceil_grid_bound hA₂ (by linarith : 0≤2*B+2*t)
  rw [←hcs] at hc
  rw [←hps] at hp
  have hcp := pow_le_pow_left₀ (Nat.cast_nonneg _) hc d
  have hpp := pow_le_pow_left₀ (Nat.cast_nonneg _) hp d
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hcp (Nat.cast_nonneg j)) hpp
    (by positivity) (by positivity)
  have hmain : ((j*(2*mc+1)^d*(2*mp+1)^d:ℕ):ℝ)≤K*Real.exp ((d:ℝ)*t+(d:ℝ)*(2*B+2*t)) := by
    calc
      _ ≤ (j:ℝ)*((2*A₁+5)*Real.exp t)^d*((2*A₂+5)*Real.exp (2*B+2*t))^d := by
        simpa only [Nat.cast_mul,Nat.cast_pow] using hm
      _ = K*Real.exp ((d:ℝ)*t+(d:ℝ)*(2*B+2*t)) := by
        dsimp only [K]
        rw [mul_pow,mul_pow,←Real.exp_nat_mul,←Real.exp_nat_mul,Real.exp_add]
        ring
  have hKexp : K≤Real.exp K := by linarith [Real.add_one_le_exp K]
  have hKt : K≤K*t := le_mul_of_one_le_right hK ht
  have hBd := mul_le_mul_of_nonneg_left hB (show 0≤2*(d:ℝ) by positivity)
  calc
    _ ≤ K*Real.exp ((d:ℝ)*t+(d:ℝ)*(2*B+2*t)) := hmain
    _ ≤ Real.exp K*Real.exp ((d:ℝ)*t+(d:ℝ)*(2*B+2*t)) := mul_le_mul_of_nonneg_right hKexp (Real.exp_pos _).le
    _ = Real.exp (K+((d:ℝ)*t+(d:ℝ)*(2*B+2*t))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((K+(3+2*Dg)*d)*t) := by apply Real.exp_le_exp.mpr; nlinarith only [hKt,hBd]
end SmoothObstruction.GridCount

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
variable {d : ℕ} {H : Type} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type} [MetricSpace M] [CompactSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]

/-- Smooth switching from a good gauge and a quantitative geometric
boundary collar, for Euclidean and half-space manifold models. -/
theorem switching_from_gauges (hclosed : IsClosed (range I))
    (μ : ProbabilityMeasure M) (hμ : SmoothPositiveDensity I (μ : Measure M))
    (S : Diffeomorph I I M M ∞) (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M))
    (hcollar : ∀ (ι : Type) [Fintype ι] (a : ι → M) (K : ι → Set M),
      (∀ i,IsCompact (K i)) → (∀ i,K i⊆(chartAt H (a i)).source) →
      ∃ Cb : ℝ,0≤Cb ∧ ∀ r : ℝ,0 ≤ r → ∃ W : Set M,MeasurableSet W ∧
        (μ : Measure M).real W≤Cb*r ∧
        ∀ i x,x∈K i → x∉W → closedBall ((extChartAt I (a i)) x) r⊆interior (range I)) :
    SmoothSwitching (μ : Measure M) S S.symm := by
  classical
  intro η hη
  let ε : ℝ≥0 := ⟨η/100,by positivity⟩
  obtain ⟨ι,hfin,hmeas,hsc,a,K,L,c,s,hK,hKU,hc,hcover,hL,hLm,hs,hLK,hLc,hcore,
    b,R₀,Dg,G,hR₀,hDg,hbpos,hfloor,hbs,hG,hA⟩ := good_stable_gauges I S μ hS hη ε (by change (0:ℝ)<η/100; positivity)
  let : Fintype ι := hfin
  let : MeasurableSpace ι := hmeas
  let : MeasurableSingletonClass ι := hsc
  let V := ⋃ i,L i
  have hV : MeasurableSet V := (isCompact_iUnion hL).measurableSet
  have hVm : (μ : Measure M).real Vᶜ≤η/100 := by
    exact (ENNReal.toReal_mono (by simp) hLm).trans_eq (by rfl)
  have hGm : ∀ k,(μ : Measure M).real (G k)ᶜ≤η/100 := by
    intro k
    rw [measureReal_compl (hG k).1.measurableSet,probReal_univ]
    have hh := (hG k).2
    linarith
  have hb : Tendsto b atTop (𝓝 0) := by
    have hh := hbs.tendsto_atTop_zero.sqrt
    simpa only [Real.sqrt_sq (hbpos _).le,Real.sqrt_zero] using hh
  have hn : Tendsto (fun k => ((2^k:ℕ):ℝ)) atTop atTop := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have hfloor' : ∀ k,((2^k:ℕ):ℝ)^(-1/10:ℝ)≤b k := by
    intro k
    have he : ((2^k:ℕ):ℝ)^(-1/10:ℝ)=GoodStationary.floorAt k := by
      rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
      dsimp only [GoodStationary.floorAt]
      congr 1
      ring
    rw [he]
    exact hfloor k
  obtain ⟨Cb,hCb,hcol⟩ := hcollar ι a K hK hKU
  obtain ⟨Dc,Dp,N,ρ,hDc,hDp,hN,hρ,hsw⟩ := grid_switches I hclosed (μ : Measure M) hμ S hS
    a K hK hKU c hc hcover V hV s hs hcore η hη hVm b (fun k => 2^k) hbpos hb hn hfloor'
    Dg R₀ hDg hR₀ G (fun k => (hG k).1.measurableSet) hGm (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hA)
    Cb hCb hcol
  obtain ⟨C,hC,hcount⟩ := GridCount.original_grid_count d (Fintype.card ι) Dc Dp Dg hDc hDp hDg
  let B := fun k => SmoothScales.B (b k)
  have hBs : Summable (fun k => (B k)^16) := by
    simpa only [B,SmoothScales.root_sixteen (hbpos _).le] using hbs
  have hex : ∀ᶠ k in atTop,∃ D : SwitchData (μ : Measure M),D.Good η C (B k) (2^k) ∧
      ∀ u∈D.carrier,originalTube I S a c (n:=2^k) (ρ k) u.1 (D.point u) ∧
        originalTube I S.symm a c (n:=2^k) (ρ k) u.2 (D.point u) := by
    filter_upwards [hsw,hb.eventually_le_const (by norm_num : (0:ℝ)<1)] with k hk hb1
    obtain ⟨J,hjfin,hjmeas,hjsc,P,Gp,Φ,hcard,hP,hGp,hΦ,hm,hmarg,ht⟩ := hk
    let : Fintype J := hjfin
    let : MeasurableSpace J := hjmeas
    let : MeasurableSingletonClass J := hjsc
    let D : SwitchData (μ : Measure M) := ⟨J,hjfin,hjmeas,hjsc,P,Gp,(fun u => (Φ u).1),hP,hGp,measurable_fst.comp hΦ⟩
    have hbn := GoodStationary.burden_ge_one b hfloor k
    have hcnt := hcount (b k) (2^k) N (hbpos k) hb1 (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hbn) hN
    refine ⟨D,⟨?_,hm,hmarg⟩,ht⟩
    change (Fintype.card J:ℝ)≤_
    rw [hcard]
    simpa only [B,SmoothScales.B,mul_assoc,neg_mul] using hcnt
  let D₀ : SwitchData (μ : Measure M) := ⟨Unit,inferInstance,inferInstance,inferInstance,
    (fun _ => ()),∅,Prod.fst,measurable_const,MeasurableSet.empty,measurable_fst⟩
  let D (k : ℕ) : SwitchData (μ : Measure M) :=
    if hk : ∃ D : SwitchData (μ : Measure M),D.Good η C (B k) (2^k) ∧
      ∀ u∈D.carrier,originalTube I S a c (n:=2^k) (ρ k) u.1 (D.point u) ∧
        originalTube I S.symm a c (n:=2^k) (ρ k) u.2 (D.point u)
    then hk.choose else D₀
  have hD : ∀ᶠ k in atTop,(D k).Good η C (B k) (2^k) ∧
      ∀ u∈(D k).carrier,originalTube I S a c (n:=2^k) (ρ k) u.1 ((D k).point u) ∧
        originalTube I S.symm a c (n:=2^k) (ρ k) u.2 ((D k).point u) := by
    filter_upwards [hex] with k hk
    dsimp only [D]; rw [dite_eq_left hk]; exact hk.choose_spec
  refine ⟨B,C,D,fun k => SmoothScales.positive (hbpos k),hBs,hD.mono (fun _ hk => hk.1),?_⟩
  have hout := original_shadow_tendsto I hclosed a K hK hKU S c hcover (fun k => 2^k) ρ hρ
    (fun k => (D k).carrier) (fun k u => ((D k).point u,u.2)) (hD.mono (fun _ hk => hk.2))
  exact hout
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_FiniteEntropy
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SmoothObstruction

namespace FiniteEntropy

variable {α β γ : Type*}

/-- The pointwise log-sum bound, including the zero convention. -/
lemma negMulLog_le_cross {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.negMulLog p ≤ -p * Real.log q + q - p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · subst p
    simp only [Real.negMulLog_zero, neg_zero, zero_mul, zero_add, sub_zero]
    exact hq.le
  · have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at h
    have h' := mul_le_mul_of_nonneg_left h hp.le
    simp only [mul_sub, mul_one, mul_div_cancel₀ _ hp.ne'] at h'
    simp only [Real.negMulLog_def]
    nlinarith

/-- Entropy of a nonnegative vector of total mass `θ` on a finite set. -/
lemma sum_negMulLog_le_mass (s : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i ∈ s, Real.negMulLog (p i) ≤
      Real.negMulLog (∑ i ∈ s, p i) + (∑ i ∈ s, p i) * Real.log s.card := by
  classical
  let θ := ∑ i ∈ s, p i
  have hθ : 0 ≤ θ := sum_nonneg hp
  by_cases hzero : θ = 0
  · have hz (i : α) (hi : i ∈ s) : p i = 0 :=
      (sum_eq_zero_iff_of_nonneg hp).mp hzero i hi
    simp [show ∑ i ∈ s, p i = 0 from hzero, sum_congr rfl (fun i hi => congrArg Real.negMulLog (hz i hi))]
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hs : s.Nonempty := by
      by_contra h
      have hempty := not_nonempty_iff_eq_empty.mp h
      simp [θ, hempty] at hzero
    have hc : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
    have hq : 0 < θ / s.card := div_pos hθpos hc
    calc
      _ ≤ ∑ i ∈ s, (-p i * Real.log (θ / s.card) + θ / s.card - p i) :=
        sum_le_sum (fun i hi => negMulLog_le_cross (hp i hi) hq)
      _ = -θ * Real.log (θ / s.card) := by
        simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
        rw [← sum_mul, sum_neg_distrib]
        change -θ * Real.log (θ / s.card) + s.card * (θ / s.card) - θ = _
        rw [mul_div_cancel₀ _ hc.ne']
        ring
      _ = _ := by
        rw [Real.log_div hθpos.ne' hc.ne']
        simp only [Real.negMulLog_def]
        change -θ * (Real.log θ - Real.log s.card) = -θ * Real.log θ + θ * Real.log s.card
        ring

lemma entropy_nonneg [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) : 0 ≤ natEntropy p := by
  apply sum_nonneg
  intro a _
  apply Real.negMulLog_nonneg (hp a)
  calc
    p a ≤ ∑ a, p a := single_le_sum (fun a _ => hp a) (mem_univ a)
    _ = 1 := hpsum

lemma entropy_le_log_card [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) : natEntropy p ≤ Real.log (Fintype.card α) := by
  simpa [natEntropy, hpsum] using sum_negMulLog_le_mass univ p (fun a _ => hp a)

end FiniteEntropy
end SmoothObstruction

namespace SmoothObstruction.FiniteEntropy

open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

omit [Fintype α] in
lemma leftMass_nonneg {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (a : α) :
    0 ≤ leftMass p a := sum_nonneg (fun _ _ => hp _)
omit [Fintype β] in
lemma rightMass_nonneg {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (b : β) :
    0 ≤ rightMass p b := sum_nonneg (fun _ _ => hp _)
omit [Fintype α] in
lemma le_leftMass {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (a : α) (b : β) :
    p (a,b) ≤ leftMass p a := single_le_sum (fun _ _ => hp _) (mem_univ b)
omit [Fintype β] in
lemma le_rightMass {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (a : α) (b : β) :
    p (a,b) ≤ rightMass p b := single_le_sum (fun a _ => hp (a,b)) (mem_univ a)
lemma sum_leftMass (p : α × β → ℝ) : ∑ a, leftMass p a = ∑ x, p x := by
  simp only [leftMass, Fintype.sum_prod_type]
lemma sum_rightMass (p : α × β → ℝ) : ∑ b, rightMass p b = ∑ x, p x := by
  simp only [rightMass, Fintype.sum_prod_type]
  exact sum_comm

/-- Finite joint entropy subadditivity, including zero marginal masses.
This is the unconditional entropy input for block-rate existence. -/
theorem entropy_subadd {p : α × β → ℝ} (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) :
    natEntropy p ≤ natEntropy (leftMass p) + natEntropy (rightMass p) := by
  have hpoint (a : α) (b : β) : Real.negMulLog (p (a,b)) ≤
      -p (a,b) * Real.log (leftMass p a) - p (a,b) * Real.log (rightMass p b) +
        leftMass p a * rightMass p b - p (a,b) := by
    rcases eq_or_lt_of_le (hp (a,b)) with he | he
    · rw [← he]
      simp only [Real.negMulLog_zero, neg_zero, zero_mul, sub_zero, zero_add]
      exact mul_nonneg (leftMass_nonneg hp a) (rightMass_nonneg hp b)
    · have ha := he.trans_le (le_leftMass hp a b)
      have hb := he.trans_le (le_rightMass hp a b)
      have h := negMulLog_le_cross (hp (a,b)) (mul_pos ha hb)
      rw [Real.log_mul ha.ne' hb.ne'] at h
      nlinarith
  have hA : (∑ a, ∑ b, -p (a,b) * Real.log (leftMass p a)) = natEntropy (leftMass p) := by
    simp only [← sum_mul, sum_neg_distrib, leftMass, natEntropy, Real.negMulLog_def]
  have hB : (∑ a, ∑ b, -p (a,b) * Real.log (rightMass p b)) = natEntropy (rightMass p) := by
    rw [sum_comm]
    simp only [← sum_mul, sum_neg_distrib, rightMass, natEntropy, Real.negMulLog_def]
  have hAB : (∑ a, ∑ b, leftMass p a * rightMass p b) = 1 := by
    simp only [← mul_sum, sum_rightMass, sum_leftMass, hs, mul_one]
  calc
    _ ≤ ∑ a, ∑ b, (-p (a,b) * Real.log (leftMass p a) -
        p (a,b) * Real.log (rightMass p b) + leftMass p a * rightMass p b - p (a,b)) := by
      simp only [natEntropy, Fintype.sum_prod_type]
      exact sum_le_sum (fun a _ => sum_le_sum (fun b _ => hpoint a b))
    _ = _ := by
      simp only [sub_eq_add_neg, neg_mul, sum_add_distrib, sum_neg_distrib] at hA hB ⊢
      have hpSum : (∑ a, ∑ b, p (a,b)) = 1 := by simpa only [Fintype.sum_prod_type] using hs
      rw [hA, hB, hAB, hpSum]
      ring

lemma entropy_push_le {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (f : α → β) :
    natEntropy (pushMass p f) ≤ natEntropy p := by
  classical
  have hupper (a : α) : p a ≤ pushMass p f (f a) := by
    have h := single_le_sum (s := univ) (a := a)
      (f := fun x => if f x = f a then p x else 0)
      (by intro x _; split_ifs; exact hp x; exact le_rfl) (mem_univ a)
    simpa [pushMass] using h
  have hpoint (a : α) : -p a * Real.log (pushMass p f (f a)) ≤ Real.negMulLog (p a) := by
    rcases eq_or_lt_of_le (hp a) with ha | ha
    · rw [← ha]; simp
    · have hm := Real.log_le_log ha (hupper a)
      simpa only [Real.negMulLog_def] using mul_le_mul_of_nonpos_left hm (by linarith : -p a ≤ 0)
  have heq : natEntropy (pushMass p f) = ∑ a, -p a * Real.log (pushMass p f (f a)) := by
    unfold natEntropy
    simp only [Real.negMulLog_def]
    calc
      _ = ∑ b, ∑ a, -(if f a = b then p a else 0) * Real.log (pushMass p f b) := by
        apply sum_congr rfl
        intro b _
        rw [← sum_mul, sum_neg_distrib]
        rfl
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a _
        simp [ite_mul]
  rw [heq]
  exact sum_le_sum (fun a _ => hpoint a)

end SmoothObstruction.FiniteEntropy

namespace SmoothObstruction.FiniteEntropy
open Finset
variable {α : Type*} [Fintype α]

/-- Entropy of a symbol emitted only on an event of total mass δ. The marker
cost is exactly one natural-log bit; zeros are included. -/
lemma entropy_option {p : Option α → ℝ} (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    natEntropy p ≤ Real.log 2 + (∑ a, p (some a)) * Real.log (Fintype.card α) := by
  let δ := ∑ a, p (some a)
  have hδ : 0 ≤ δ := sum_nonneg (fun a _ => hp (some a))
  have htotal : p none + δ = 1 := by simpa only [Fintype.sum_option] using hs
  have hbin := entropy_le_log_card (p := fun b : Bool => if b then δ else p none)
    (by intro b; cases b; exact hp none; exact hδ)
    (by simpa [add_comm] using htotal)
  simp only [natEntropy, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    Fintype.card_bool, Nat.cast_ofNat] at hbin
  have htail := sum_negMulLog_le_mass (univ : Finset α) (fun a => p (some a))
    (fun a _ => hp (some a))
  simp only [card_univ] at htail
  change _ ≤ Real.negMulLog δ + δ * _ at htail
  unfold natEntropy
  rw [Fintype.sum_option]
  nlinarith

end SmoothObstruction.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PartitionEntropy
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SmoothObstruction.PartitionEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.FiniteEntropy
open scoped Topology
variable {X α β : Type*} [MeasurableSpace X] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
lemma mass_nonneg (f : X → α) (a : α) : 0 ≤ mass μ f a := ENNReal.toReal_nonneg

lemma sum_mass {f : X → α} (hf : Measurable f) : ∑ a, mass μ f a = 1 := by
  have h := sum_measureReal_preimage_singleton (μ := μ) univ
    (fun a _ => (measurableSet_singleton a).preimage hf)
  simpa [mass] using h

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma push_mass {f : X → α} (hf : Measurable f) (g : α → β) :
    pushMass (mass μ f) g = mass μ (g ∘ f) := by
  classical
  funext b
  unfold pushMass
  rw [← sum_filter]
  have h := sum_measureReal_preimage_singleton (μ := μ) (univ.filter (fun a => g a = b))
    (fun a _ => (measurableSet_singleton a).preimage hf)
  rw [show f ⁻¹' ↑(univ.filter (fun a => g a = b)) = (g ∘ f) ⁻¹' {b} by
    ext x; simp] at h
  exact h

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma entropy_comp_le {f : X → α} (hf : Measurable f) (g : α → β) :
    entropy μ (g ∘ f) ≤ entropy μ f := by
  unfold entropy
  rw [← push_mass μ hf g]
  exact entropy_push_le (mass_nonneg μ f) g

lemma entropy_nonnegative {f : X → α} (hf : Measurable f) : 0 ≤ entropy μ f :=
  entropy_nonneg (mass_nonneg μ f) (sum_mass μ hf)

lemma entropy_card_bound {f : X → α} (hf : Measurable f) :
    entropy μ f ≤ Real.log (Fintype.card α) :=
  entropy_le_log_card (mass_nonneg μ f) (sum_mass μ hf)

lemma leftMass_pair {f : X → α} {g : X → β} (hf : Measurable f) (hg : Measurable g) :
    leftMass (mass μ (fun x => (f x,g x))) = mass μ f := by
  have h := push_mass μ (hf.prodMk hg) Prod.fst
  rw [show (Prod.fst ∘ fun x => (f x,g x)) = f by rfl] at h
  rw [← h]
  funext a
  classical
  simp only [leftMass, pushMass, Fintype.sum_prod_type]
  rw [sum_comm]
  simp

lemma rightMass_pair {f : X → α} {g : X → β} (hf : Measurable f) (hg : Measurable g) :
    rightMass (mass μ (fun x => (f x,g x))) = mass μ g := by
  have h := push_mass μ (hf.prodMk hg) Prod.snd
  rw [show (Prod.snd ∘ fun x => (f x,g x)) = g by rfl] at h
  rw [← h]
  funext b
  classical
  simp [rightMass, pushMass, Fintype.sum_prod_type]

lemma entropy_pair_le {f : X → α} {g : X → β} (hf : Measurable f) (hg : Measurable g) :
    entropy μ (fun x => (f x,g x)) ≤ entropy μ f + entropy μ g := by
  have h := entropy_subadd (mass_nonneg μ (fun x => (f x,g x)))
    (sum_mass μ (hf.prodMk hg))
  rw [leftMass_pair μ hf hg, rightMass_pair μ hf hg] at h
  exact h

omit [IsProbabilityMeasure μ] in
lemma entropy_preserving {T : X → X} (hT : MeasurePreserving T μ μ)
    {f : X → α} (hf : Measurable f) : entropy μ (f ∘ T) = entropy μ f := by
  unfold entropy mass
  congr 1
  funext a
  exact hT.measureReal_preimage ((measurableSet_singleton a).preimage hf).nullMeasurableSet

omit [Fintype α] [MeasurableSingletonClass α] in
lemma measurable_name {T : X → X} (hT : Measurable T) {P : X → α} (hP : Measurable P)
    (n : ℕ) : Measurable (name T P n) :=
  Measurable.of_eval (fun j => hP.comp (hT.iterate j.val))

omit [MeasurableSpace X] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma name_add (T : X → X) (P : X → α) (m n : ℕ) :
    name T P (m+n) = (fun w => Fin.append w.1 w.2) ∘
      (fun x => (name T P m x, name T P n ((T^[m]) x))) := by
  funext x j
  change P ((T^[j.val]) x) = Fin.append _ _ j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [name, Fin.append]
  · simp [name, Fin.append, Function.iterate_add_apply, Nat.add_comm m]

/-- Exact subadditivity for finite partition names of a stationary system. -/
theorem block_subadditive {T : X → X} (hT : MeasurePreserving T μ μ)
    {P : X → α} (hP : Measurable P) :
    Subadditive (fun n => entropy μ (name T P n)) := by
  intro m n
  change entropy μ (name T P (m+n)) ≤ entropy μ (name T P m) + entropy μ (name T P n)
  rw [name_add]
  have hm := measurable_name hT.measurable hP m
  have hn := measurable_name hT.measurable hP n
  calc
    _ ≤ entropy μ (fun x => (name T P m x, name T P n ((T^[m]) x))) :=
      entropy_comp_le μ (hm.prodMk (hn.comp (hT.measurable.iterate m))) _
    _ ≤ entropy μ (name T P m) + entropy μ ((name T P n) ∘ T^[m]) :=
      entropy_pair_le μ hm (hn.comp (hT.measurable.iterate m))
    _ = _ := by rw [entropy_preserving μ (hT.iterate m) hn]

/-- Every individual finite partition has an entropy rate, by Fekete's lemma.
The main theorem still needs a *uniform* bound over arbitrary partitions. -/
theorem exists_block_rate {T : X → X} (hT : MeasurePreserving T μ μ)
    {P : X → α} (hP : Measurable P) :
    ∃ h : ℝ, 0 ≤ h ∧ h ≤ Real.log (Fintype.card α) ∧
      Tendsto (fun n : ℕ => entropy μ (name T P n) / n) atTop (𝓝 h) := by
  have hs := block_subadditive μ hT hP
  have hb : BddBelow (Set.range (fun n : ℕ => entropy μ (name T P n) / n)) :=
    ⟨0, by rintro _ ⟨n,rfl⟩; exact div_nonneg (entropy_nonnegative μ
      (measurable_name hT.measurable hP n)) (Nat.cast_nonneg n)⟩
  refine ⟨hs.lim, ?_, ?_, hs.tendsto_lim hb⟩
  · exact ge_of_tendsto (hs.tendsto_lim hb) (Filter.Eventually.of_forall
      (fun n => div_nonneg (entropy_nonnegative μ (measurable_name hT.measurable hP n))
        (Nat.cast_nonneg n)))
  · have h1 := hs.lim_le_div hb (n := 1) (by decide)
    have hc := entropy_card_bound μ (measurable_name hT.measurable hP 1)
    simp only [Nat.cast_one, div_one] at h1
    simpa using h1.trans hc

end SmoothObstruction.PartitionEntropy

namespace SmoothObstruction.PartitionEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.FiniteEntropy
open scoped Topology
variable {X α : Type*} [MeasurableSpace X] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] (μ : Measure X) [IsProbabilityMeasure μ]

attribute [local instance] OAI.SmoothObstruction.PartitionEntropy.instMeasurableSpaceOption_solutions
local instance instMeasurableSingletonClassOption_solutions : MeasurableSingletonClass (Option α) := ⟨fun _ => trivial⟩

omit [MeasurableSpace X] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma recover_error (P Q : X → α) (x : X) : recover (Q x) (errorCode P Q x) = P x := by
  classical
  unfold errorCode
  split_ifs with h
  · exact h.symm
  · rfl

lemma measurable_error {P Q : X → α} (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (errorCode P Q) := by
  classical
  unfold errorCode
  exact Measurable.ite (measurableSet_eq_fun hP hQ) measurable_const
    ((measurable_of_finite Option.some).comp hP)

lemma error_mass {P Q : X → α} (hP : Measurable P) (hQ : Measurable Q) :
    (∑ a, mass μ (errorCode P Q) (some a)) = μ.real {x | P x ≠ Q x} := by
  classical
  have ht := sum_mass μ (measurable_error hP hQ)
  rw [Fintype.sum_option] at ht
  have hm : (errorCode P Q) ⁻¹' {none} = {x | P x = Q x} := by
    ext x
    simp [errorCode]
  have hc := measureReal_compl (μ := μ) (measurableSet_eq_fun hP hQ)
  simp only [mass, hm] at ht
  have hcompl : {x | P x ≠ Q x} = {x | P x = Q x}ᶜ := rfl
  rw [hcompl, hc]
  simp only [probReal_univ, mass]
  linarith

lemma error_entropy_bound {P Q : X → α} (hP : Measurable P) (hQ : Measurable Q) :
    entropy μ (errorCode P Q) ≤ Real.log 2 + μ.real {x | P x ≠ Q x} *
      Real.log (Fintype.card α) := by
  have h := entropy_option (mass_nonneg μ (errorCode P Q))
    (sum_mass μ (measurable_error hP hQ))
  rw [error_mass μ hP hQ] at h
  exact h

/-- Compare genuine orbit names through pointwise error coding. -/
lemma names_error_le {T : X → X} (hT : Measurable T) {P Q : X → α}
    (hP : Measurable P) (hQ : Measurable Q) (n : ℕ) :
    entropy μ (name T P n) ≤ entropy μ (name T Q n) +
      entropy μ (name T (errorCode P Q) n) := by
  have hfor := entropy_comp_le μ
    ((measurable_name hT hQ n).prodMk (measurable_name hT (measurable_error hP hQ) n))
    (fun z : (Fin n → α) × (Fin n → Option α) => fun j => recover (z.1 j) (z.2 j))
  have he : ((fun z : (Fin n → α) × (Fin n → Option α) => fun j => recover (z.1 j) (z.2 j)) ∘
      (fun x => (name T Q n x,name T (errorCode P Q) n x))) = name T P n := by
    funext x j
    exact recover_error P Q ((T^[j.val]) x)
  rw [he] at hfor
  exact hfor.trans (entropy_pair_le μ (measurable_name hT hQ n)
    (measurable_name hT (measurable_error hP hQ) n))

end SmoothObstruction.PartitionEntropy

namespace SmoothObstruction.PartitionEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.FiniteEntropy
open scoped Topology
variable {X α : Type*} [MeasurableSpace X] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] (μ : Measure X) [IsProbabilityMeasure μ]

lemma entropy_name_one {T : X → X} {P : X → α} (hP : Measurable P) :
    entropy μ (name T P 1) = entropy μ P := by
  have he : name T P 1 = (fun a => fun _ : Fin 1 => a) ∘ P := by
    funext x j
    simp [name, Fin.eq_zero j]
  rw [he]
  apply le_antisymm (entropy_comp_le μ hP _)
  have h := entropy_comp_le μ ((measurable_of_finite (fun a : α => fun _ : Fin 1 => a)).comp hP)
    (fun w : Fin 1 → α => w 0)
  exact h

/-- If the genuine name entropy has a limit, its rate is at most the entropy
of the one-time partition. No independence is assumed. -/
lemma block_rate_le_entropy {T : X → X} (hT : MeasurePreserving T μ μ)
    {P : X → α} (hP : Measurable P) {h : ℝ}
    (hh : Tendsto (fun n : ℕ => entropy μ (name T P n) / n) atTop (𝓝 h)) :
    h ≤ entropy μ P := by
  have hs := block_subadditive μ hT hP
  have hb : BddBelow (Set.range (fun n : ℕ => entropy μ (name T P n) / n)) :=
    ⟨0, by rintro _ ⟨n,rfl⟩; exact div_nonneg (entropy_nonnegative μ
      (measurable_name hT.measurable hP n)) (Nat.cast_nonneg n)⟩
  have hid : hs.lim = h := tendsto_nhds_unique (hs.tendsto_lim hb) hh
  have hone := hs.lim_le_div hb (n := 1) (by decide)
  simpa only [hid, Nat.cast_one, div_one, entropy_name_one μ hP] using hone

attribute [local instance] OAI.SmoothObstruction.PartitionEntropy.instMeasurableSpaceOption_solutions_1
local instance instMeasurableSingletonClassOption_solutions_1 : MeasurableSingletonClass (Option α) := ⟨fun _ => trivial⟩

/-- Quantitative approximation of rates by a finite observation. This is a
real stationary-process entropy argument, not an assertion of a generator. -/
lemma rate_approximation {T : X → X} (hT : MeasurePreserving T μ μ)
    {P Q : X → α} (hP : Measurable P) (hQ : Measurable Q) {h k : ℝ}
    (hh : Tendsto (fun n : ℕ => entropy μ (name T P n) / n) atTop (𝓝 h))
    (hk : Tendsto (fun n : ℕ => entropy μ (name T Q n) / n) atTop (𝓝 k)) :
    h ≤ k + Real.log 2 + μ.real {x | P x ≠ Q x} * Real.log (Fintype.card α) := by
  obtain ⟨e, he0, heCard, he⟩ := exists_block_rate μ hT (measurable_error hP hQ)
  have hlim : h ≤ k + e := le_of_tendsto_of_tendsto hh (hk.add he)
    (Filter.Eventually.of_forall (fun n => by
      dsimp only
      rw [← add_div]
      exact div_le_div_of_nonneg_right (names_error_le μ hT.measurable hP hQ n)
        (Nat.cast_nonneg n)))
  have hbound := (block_rate_le_entropy μ hT (measurable_error hP hQ) he).trans
    (error_entropy_bound μ hP hQ)
  linarith

/-- Sufficient approximation criterion for a uniform finite KS bound.
The criterion requires actual measurable approximants with small error and
uniform rate bound; it does not postulate the KS conclusion. -/
theorem finite_rate_of_approximants {T : X → X} (hT : MeasurePreserving T μ μ)
    {C : ℝ} {P : X → α} (hP : Measurable P)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ Q : X → α, Measurable Q ∧
      μ.real {x | P x ≠ Q x} ≤ δ ∧ ∃ k : ℝ, k ≤ C ∧
        Tendsto (fun n : ℕ => entropy μ (name T Q n) / n) atTop (𝓝 k)) :
    ∃ h : ℝ, 0 ≤ h ∧ h ≤ C + Real.log 2 + 1 ∧
      Tendsto (fun n : ℕ => entropy μ (name T P n) / n) atTop (𝓝 h) := by
  obtain ⟨h, hh0, _, hh⟩ := exists_block_rate μ hT hP
  let L := max (Real.log (Fintype.card α)) 0
  have hL : 0 ≤ L := le_max_right _ _
  let δ := (1 + L)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (by linarith)
  obtain ⟨Q,hQ,herr,k,hk,hklim⟩ := happrox δ hδ
  refine ⟨h,hh0,?_,hh⟩
  have hrare : μ.real {x | P x ≠ Q x} * Real.log (Fintype.card α) ≤ 1 := calc
    _ ≤ μ.real {x | P x ≠ Q x} * L :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) measureReal_nonneg
    _ ≤ δ * L := mul_le_mul_of_nonneg_right herr hL
    _ ≤ δ * (1 + L) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    _ = 1 := inv_mul_cancel₀ (by linarith : 1 + L ≠ 0)
  linarith [rate_approximation μ hT hP hQ hh hklim]

end SmoothObstruction.PartitionEntropy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PhaseEntropy
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset
open MeasureTheory Set MeasurableSpace
open scoped ENNReal symmDiff

namespace SmoothObstruction.CylinderApproximation

variable {X ι : Type*} {A : ι → Type*} [MeasurableSpace X]
  [∀ i, MeasurableSpace (A i)] (π : X → ∀ i, A i)

omit [MeasurableSpace X] in
lemma algebra : IsSetAlgebra (cylinders π) where
  empty_mem := ⟨∅,empty_mem_measurableCylinders A,preimage_empty⟩
  compl_mem := by
    rintro s ⟨t,ht,rfl⟩
    exact ⟨tᶜ,compl_mem_measurableCylinders ht,rfl⟩
  union_mem := by
    rintro s t ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩
    exact ⟨u ∪ v,union_mem_measurableCylinders hu hv,rfl⟩

lemma generates (hπ : ‹MeasurableSpace X› = MeasurableSpace.comap π MeasurableSpace.pi) :
    ‹MeasurableSpace X› = generateFrom (cylinders π) := by
  rw [hπ, ← generateFrom_measurableCylinders, comap_generateFrom]
  rfl

/-- Genuine approximation of arbitrary measurable sets by finite-coordinate
sets, in an arbitrary finite measure on a coordinate subspace. -/
lemma approximate_set (μ : Measure X) [IsFiniteMeasure μ]
    (hπ : ‹MeasurableSpace X› = MeasurableSpace.comap π MeasurableSpace.pi)
    {s : Set X} (hs : MeasurableSet s) {ε : ℝ} (hε : 0 < ε) :
    ∃ (I : Finset ι) (S : Set (∀ i : I, A i)), MeasurableSet S ∧
      μ.real ((π ⁻¹' cylinder I S) ∆ s) < ε := by
  have hcover : ∃ D : Set (Set X), D.Countable ∧ D ⊆ cylinders π ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, Set.countable_singleton _, ?_, ?_⟩
    · simpa using (algebra π).univ_mem
    · simp
  obtain ⟨t,ht,herr⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := μ) (algebra π).isSetRing hcover (generates π hπ) hs
    (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨u,hu,rfl⟩ := ht
  obtain ⟨I,S,hS,rfl⟩ := (mem_measurableCylinders u).mp hu
  refine ⟨I,S,hS,?_⟩
  simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr herr

/-- Every finite measurable observation admits a finite-coordinate
approximation in measure. The output labels and their measurable meaning
are preserved; overlaps of the approximating atoms cause only the stated
symmetric-difference error. -/
theorem approximate_partition [∀ i, Fintype (A i)] [∀ i, MeasurableSingletonClass (A i)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hπ : ‹MeasurableSpace X› = MeasurableSpace.comap π MeasurableSpace.pi)
    {q : ℕ} {P : X → Fin (q+1)} (hP : Measurable P) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (J : Finset ι) (f : (∀ i : J, A i) → Fin (q+1)),
      Measurable (fun x => f (J.restrict (π x))) ∧
      μ.real {x | P x ≠ f (J.restrict (π x))} ≤ δ := by
  classical
  have hε : 0 < δ / (q+1) := div_pos hδ (by positivity)
  have ha (a : Fin (q+1)) := approximate_set π μ hπ
    ((measurableSet_singleton a).preimage hP) hε
  choose I S hS herr using ha
  let J := Finset.univ.biUnion I
  have hIJ (a : Fin (q+1)) : I a ⊆ J := fun i hi =>
    Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ a,hi⟩
  let R (a : Fin (q+1)) (z : ∀ i : J, A i) : Prop :=
    Finset.restrict₂ (hIJ a) z ∈ S a
  let f (z : ∀ i : J, A i) : Fin (q+1) :=
    if h : ∃ a, R a z then h.choose else 0
  have hmeasπ : Measurable π := by
    rw [Measurable, hπ]
    intro t ht
    exact ⟨t,ht,rfl⟩
  refine ⟨J,f,(measurable_of_finite f).comp (Finset.measurable_restrict J |>.comp hmeasπ),?_⟩
  let E (a : Fin (q+1)) := (π ⁻¹' cylinder (I a) (S a)) ∆ (P ⁻¹' {a})
  have hsub : {x | P x ≠ f (J.restrict (π x))} ⊆ ⋃ a, E a := by
    intro x hx
    by_contra hn
    have hnone (a : Fin (q+1)) : x ∉ E a := fun hm => hn (mem_iUnion.mpr ⟨a,hm⟩)
    have hiff (a : Fin (q+1)) : R a (J.restrict (π x)) ↔ P x = a := by
      have hh := hnone a
      simp only [E, mem_symmDiff, Set.mem_preimage, mem_singleton_iff,
        mem_cylinder, Finset.restrict_def] at hh
      change (fun i : I a => π x i) ∈ S a ↔ P x = a
      tauto
    have hex : ∃ a, R a (J.restrict (π x)) := ⟨P x,(hiff (P x)).mpr rfl⟩
    have hf : f (J.restrict (π x)) = P x := by
      dsimp only [f]
      rw [dite_eq_left hex]
      exact ((hiff hex.choose).mp hex.choose_spec).symm
    exact hx hf.symm
  calc
    _ ≤ μ.real (⋃ a, E a) := measureReal_mono hsub
    _ ≤ ∑ a, μ.real (E a) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _a : Fin (q+1), δ / (q+1) := Finset.sum_le_sum (fun a _ => (herr a).le)
    _ = δ := by simp; field_simp

end SmoothObstruction.CylinderApproximation

namespace SmoothObstruction.PhaseEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.PartitionEntropy
open scoped Topology

variable (A : Type) (m : ℕ → ℕ)

variable {A m} {X : Type*} [MeasurableSpace X]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [∀ i, NeZero (m i)]
  (s : X → ℤ → A) (p : X → ∀ i, ZMod (m i))

omit [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [∀ i, NeZero (m i)] [MeasurableSpace X] in
lemma symbol_iterate {T : X → X} (hs : ∀ x t, s (T x) t = s x (t+1)) (n : ℕ) (x : X) (t : ℤ) :
    s ((T^[n]) x) t = s x (t+n) := by
  induction n generalizing x t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', hs, ih]
    congr 1
    push_cast
    ring

omit [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [∀ i, NeZero (m i)] [MeasurableSpace X] in
lemma phase_iterate {T : X → X} (hp : ∀ x i, p (T x) i = p x i + 1)
    (n : ℕ) (x : X) (i : ℕ) : p ((T^[n]) x) i = p x i + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', hp, ih]; push_cast; ring

/-- Every genuine cylinder observation on symbols and phases has rate at most
log(card A). Initial phase data have finite cost and add zero entropy rate. -/
theorem cylinder_rate_bound (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ)
    (hcoord : Measurable (coordinates s p))
    (hs : ∀ x t, s (T x) t = s x (t+1)) (hp : ∀ x i, p (T x) i = p x i + 1)
    {q : ℕ} (J : Finset (ℤ ⊕ ℕ)) (f : (∀ i : J, Coordinate A m i) → Fin (q+1)) :
    ∃ h : ℝ, h ≤ Real.log (Fintype.card A) ∧
      Tendsto (fun n : ℕ => entropy μ (name T (fun x => f (J.restrict (coordinates s p x))) n) / n)
        atTop (𝓝 h) := by
  classical
  let Q := fun x => f (J.restrict (coordinates s p x))
  have hQ : Measurable Q := (measurable_of_finite f).comp ((Finset.measurable_restrict J).comp hcoord)
  obtain ⟨h,_,_,hh⟩ := exists_block_rate μ hT hQ
  let k := J.sup (Sum.elim Int.natAbs (fun _ => 0))
  have hbound (t : ℤ) (ht : Sum.inl t ∈ J) : -(k : ℤ) ≤ t ∧ t ≤ k := by
    have hk : t.natAbs ≤ k := Finset.le_sup (f := Sum.elim Int.natAbs (fun _ => 0)) ht
    have h₁ := Int.le_natAbs (a := t)
    have h₂ := Int.le_natAbs (a := -t)
    simp only [Int.natAbs_neg] at h₂
    omega
  let D := ∀ i : J, Coordinate A m i
  let O (n : ℕ) (x : X) : (Fin (n+2*k+1) → A) × D :=
    (fun a => s x ((a.val : ℤ)-k), J.restrict (coordinates s p x))
  have hO (n : ℕ) : Measurable (O n) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro a
      exact (measurable_pi_apply (Sum.inl ((a.val : ℤ)-k))).comp hcoord
    · exact (Finset.measurable_restrict J).comp hcoord
  have hindex (n : ℕ) (j : Fin n) (t : ℤ) (ht : Sum.inl t ∈ J) :
      (t+j.val+k).toNat < n+2*k+1 := by
    have hb := hbound t ht
    omega
  let decoder (n : ℕ) (d : (Fin (n+2*k+1) → A) × D) (j : Fin n) : D := fun i =>
    match i with
    | ⟨Sum.inl t, ht⟩ => d.1 ⟨(t+j.val+k).toNat, hindex n j t ht⟩
    | ⟨Sum.inr r, hr⟩ => (fun z : ZMod (m r) => z + (j.val : ZMod (m r))) (d.2 ⟨Sum.inr r,hr⟩)
  have hdecode (n : ℕ) (x : X) (j : Fin n) :
      decoder n (O n x) j = J.restrict (coordinates s p ((T^[j.val]) x)) := by
    funext ⟨i,hi⟩
    cases i with
    | inl t =>
      change s x (((t+j.val+k).toNat : ℤ)-k) = s ((T^[j.val]) x) t
      rw [symbol_iterate s hs]
      congr 1
      have hb := hbound t hi
      omega
    | inr r =>
      exact (phase_iterate p hp j.val x r).symm
  have hfactor (n : ℕ) : name T Q n = (fun d => fun j => f (decoder n d j)) ∘ O n := by
    funext x j
    rw [Function.comp_apply, hdecode]
    rfl
  have hcard (n : ℕ) : entropy μ (name T Q n) ≤
      ((n+2*k+1 : ℕ) : ℝ) * Real.log (Fintype.card A) + Real.log (Fintype.card D) := by
    rw [hfactor]
    have he := (entropy_comp_le μ (hO n) (fun d => fun j => f (decoder n d j))).trans
      (entropy_card_bound μ (hO n))
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_pow, Real.log_mul (by positivity : (Fintype.card A : ℝ) ^ (n+2*k+1) ≠ 0)
        (by positivity : (Fintype.card D : ℝ) ≠ 0), Real.log_pow] using he
  have hlim : Tendsto (fun n : ℕ => Real.log (Fintype.card A) +
      (((2*k+1 : ℕ) : ℝ) * Real.log (Fintype.card A) + Real.log (Fintype.card D)) / n)
      atTop (𝓝 (Real.log (Fintype.card A))) := by
    have ht : Tendsto (fun n : ℕ =>
        (((2*k+1 : ℕ) : ℝ) * Real.log (Fintype.card A) + Real.log (Fintype.card D)) / n)
        atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [add_zero] using
      (show Tendsto (fun _ : ℕ => Real.log (Fintype.card A)) atTop
        (𝓝 (Real.log (Fintype.card A))) from tendsto_const_nhds).add ht
  refine ⟨h,le_of_tendsto_of_tendsto hh hlim ?_,hh⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hb := div_le_div_of_nonneg_right (hcard n) (Nat.cast_nonneg n)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  field_simp
  ring

/-- All finite measurable partitions on the actual coordinate subspace have
one finite entropy bound; the cylinder approximation is constructed in measure. -/
theorem all_partition_rates (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ)
    (hspace : ‹MeasurableSpace X› = MeasurableSpace.comap (coordinates s p) MeasurableSpace.pi)
    (hs : ∀ x t, s (T x) t = s x (t+1)) (hp : ∀ x i, p (T x) i = p x i + 1)
    {q : ℕ} {P : X → Fin (q+1)} (hP : Measurable P) :
    ∃ h : ℝ, 0 ≤ h ∧ h ≤ Real.log (Fintype.card A) + Real.log 2 + 1 ∧
      Tendsto (fun n : ℕ => entropy μ (name T P n) / n) atTop (𝓝 h) := by
  have hcoord : Measurable (coordinates s p) := by
    rw [Measurable, hspace]
    intro t ht
    exact ⟨t,ht,rfl⟩
  apply finite_rate_of_approximants μ hT hP
  intro δ hδ
  obtain ⟨J,f,hQ,herr⟩ := CylinderApproximation.approximate_partition
    (coordinates s p) μ hspace hP hδ
  exact ⟨_,hQ,herr,cylinder_rate_bound s p μ hT hcoord hs hp J f⟩

end SmoothObstruction.PhaseEntropy

namespace SmoothObstruction
open MeasureTheory Set Filter
open scoped Topology


lemma blockEntropy_eq_nats {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X → X) {q : ℕ} (P : X → Fin q) (n : ℕ) :
    blockEntropy μ T P n =
      PartitionEntropy.entropy μ (PartitionEntropy.name T P n) / Real.log 2 := by
  unfold blockEntropy PartitionEntropy.entropy FiniteEntropy.natEntropy
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  have he : {x | ∀ j : Fin n, P ((T^[j.val]) x) = w j} =
      PartitionEntropy.name T P n ⁻¹' {w} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      funext_iff, PartitionEntropy.name]
  rw [he]
  simp only [entropyTerm, PartitionEntropy.mass, Measure.real, Real.negMulLog_def, neg_mul]

/-- The exact frozen finite-KS predicate for any finite-symbol cyclic phase
subspace with its genuine coordinate sigma field. -/
theorem PhaseEntropy.finiteKS {A : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    {m : ℕ → ℕ} [∀ i, NeZero (m i)] {X : Type*} [MeasurableSpace X]
    (s : X → ℤ → A) (p : X → ∀ i, ZMod (m i))
    (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ)
    (hspace : ‹MeasurableSpace X› = MeasurableSpace.comap (coordinates s p) MeasurableSpace.pi)
    (hs : ∀ x t, s (T x) t = s x (t+1)) (hp : ∀ x i, p (T x) i = p x i + 1) :
    FiniteKSEntropy μ T := by
  refine ⟨(Real.log (Fintype.card A) + Real.log 2 + 1) / Real.log 2, ?_⟩
  intro q P hP
  obtain ⟨h,_,hb,hl⟩ := all_partition_rates s p μ hT hspace hs hp hP
  refine ⟨h / Real.log 2,div_le_div_of_nonneg_right hb (Real.log_nonneg (by norm_num)),?_⟩
  have ht := hl.div_const (Real.log 2)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [blockEntropy_eq_nats]
  ring
end SmoothObstruction

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_StandardProbability
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set ENNReal unitInterval Filter Topology Function

namespace SmoothObstruction

/- The quantile construction gives a measurable map from the unit interval
with the prescribed probability law. Injectivity yields a measurable
isomorphism on conull subsets for nonatomic laws. -/

lemma monotone_unitQuantile (μ : Measure I) : Monotone (unitQuantile μ) := by
  intro u v huv
  apply sSup_le_sSup
  intro x hx
  exact lt_of_lt_of_le hx (show (u : ℝ) ≤ v from huv)

lemma measurable_unitQuantile (μ : Measure I) : Measurable (unitQuantile μ) :=
  (monotone_unitQuantile μ).measurable

lemma map_unitQuantile (μ : Measure I) [IsProbabilityMeasure μ] :
    volume.map (unitQuantile μ) = μ := by
  apply (volume.map (unitQuantile μ)).ext_of_Iic μ
  intro x
  have Iic_to_Icc : Iic x = Icc 0 x := by ext; simp
  have μ_in_I : μ.real (Icc 0 x) ∈ I := ⟨measureReal_nonneg, measureReal_le_one⟩
  simp_rw [Measure.map_apply (measurable_unitQuantile μ) measurableSet_Iic, preimage,
    mem_Iic, Iic_to_Icc, ← ofReal_measureReal (measure_ne_top μ _),
    ← unitInterval.volume_Iic ⟨_, μ_in_I⟩]
  congr with ξ
  constructor
  · intro (hξ : unitQuantile μ ξ ≤ x)
    change ξ ≤ μ.real (Icc 0 x)
    by_cases hx : x = 1
    · simp [hx, ← univ_eq_Icc, ξ.2.2]
    let g := fun y ↦ μ.real (Icc 0 y)
    let nebot : NeBot (𝓝[>] x) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      exact ⟨1, lt_of_le_of_ne x.2.2 hx⟩
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) (g := g) continuousWithinAt_const ?_ ?_
    · let h := cdf (μ.map Subtype.val)
      have h_continuousWithinAt := continuousWithinAt_Ioi_iff_Ici.mpr (h.right_continuous x)
      simp_rw [g, ← unitInterval.cdf_eq_real μ]
      exact h_continuousWithinAt.comp (Continuous.continuousWithinAt (by fun_prop)) (fun y hy ↦ hy)
    · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      by_contra! h
      simp only [sSup_le_iff, unitQuantile] at hξ
      specialize hξ y h
      grind
  · intro (hξ : ξ ≤ μ.real (Icc 0 x))
    simp only [sSup_le_iff, unitQuantile]
    intro c hc
    by_contra! h
    have h_lt : ¬ μ.real (Icc 0 x) ≤ μ.real (Icc 0 c) := not_le.mpr (lt_of_le_of_lt' hξ hc)
    refine h_lt ?_
    gcongr
    simp

lemma strictMono_unitQuantile (μ : Measure I) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : StrictMono (unitQuantile μ) := by
  intro u v huv
  refine lt_of_le_of_ne (monotone_unitQuantile μ huv.le) ?_
  intro heq
  have hnull : (volume : Measure I) ((unitQuantile μ) ⁻¹' {unitQuantile μ u}) = 0 := by
    rw [← Measure.map_apply (measurable_unitQuantile μ) (measurableSet_singleton _),
      map_unitQuantile, measure_singleton]
  have hsub : Icc u v ⊆ (unitQuantile μ) ⁻¹' {unitQuantile μ u} := by
    intro t ht
    exact le_antisymm ((monotone_unitQuantile μ ht.2).trans_eq heq.symm)
      (monotone_unitQuantile μ ht.1)
  have hzero := measure_mono_null hsub hnull
  rw [unitInterval.volume_Icc, ENNReal.ofReal_eq_zero] at hzero
  exact not_le_of_gt (sub_pos.mpr (show (u : ℝ) < v from huv)) hzero

lemma embedding_unitQuantile (μ : Measure I) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : MeasurableEmbedding (unitQuantile μ) :=
  (measurable_unitQuantile μ).measurableEmbedding (strictMono_unitQuantile μ).injective


lemma equivImage_preserving {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    {f : X → Z} (hf : MeasurableEmbedding f) (μ : Measure X)
    {A : Set X} (hA : MeasurableSet A) :
    MeasurePreserving (hf.equivImage A) (μ.comap (Subtype.val : A → X))
      ((μ.map f).comap (Subtype.val : f '' A → Z)) := by
  refine ⟨(hf.equivImage A).measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe (hf.measurableSet_image' hA)).map_injective
  rw [Measure.map_map measurable_subtype_coe (hf.equivImage A).measurable,
    map_comap_subtype_coe (hf.measurableSet_image' hA)]
  change (μ.comap (Subtype.val : A → X)).map (f ∘ Subtype.val) = _
  rw [← Measure.map_map hf.measurable measurable_subtype_coe,
    map_comap_subtype_coe hA, hf.restrict_map, hf.injective.preimage_image]

private lemma setEqEquiv_preserving {Z : Type*} [MeasurableSpace Z] {A B : Set Z}
    (h : A = B) (μ : Measure Z) :
    MeasurePreserving (setEqEquiv h) (μ.comap (Subtype.val : A → Z))
      (μ.comap (Subtype.val : B → Z)) := by
  subst B
  exact MeasurePreserving.id _

/-- Two measurable embeddings having the same image law give an actual
measurable isomorphism on conull sets, not merely two factors. -/
lemma conullIsomorphic_of_common_embedding {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {f : X → Z} {g : Y → Z} (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (μ : Measure X) (ν : Measure Y) (heq : μ.map f = ν.map g) :
    ConullIsomorphic μ ν := by
  let A := f ⁻¹' range g
  let B := g ⁻¹' range f
  have hA : MeasurableSet A := hf.measurable hg.measurableSet_range
  have hB : MeasurableSet B := hg.measurable hf.measurableSet_range
  have hAnull : μ Aᶜ = 0 := by
    change μ (f ⁻¹' (range g)ᶜ) = 0
    rw [← hf.map_apply, heq, hg.map_apply]
    simp
  have hBnull : ν Bᶜ = 0 := by
    change ν (g ⁻¹' (range f)ᶜ) = 0
    rw [← hg.map_apply, ← heq, hf.map_apply]
    simp
  have hAB : f '' A = g '' B := by
    simp only [A, B, image_preimage_eq_inter_range, inter_comm]
  let eA := hf.equivImage A
  let eB := hg.equivImage B
  let eC := setEqEquiv hAB
  have hC : MeasurePreserving eC ((μ.map f).comap (Subtype.val : f '' A → Z))
      ((ν.map g).comap (Subtype.val : g '' B → Z)) := by
    rw [heq]
    exact setEqEquiv_preserving hAB _
  refine ⟨A, B, hA, hB, hAnull, hBnull, eA.trans (eC.trans eB.symm), ?_⟩
  exact (MeasurePreserving.symm eB (equivImage_preserving hg ν hB)).comp
    (hC.comp (equivImage_preserving hf μ hA))

lemma nullSingleton_map_embedding {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {f : X → Y} (hf : MeasurableEmbedding f)
    (μ : Measure X) [NullSingletonClass μ] : NullSingletonClass (μ.map f) := by
  constructor
  intro y
  rw [hf.map_apply]
  exact (Set.subsingleton_singleton.preimage hf.injective).measure_zero μ

/-- The nonatomic standard-Borel classification needed by prop:system,
with the same closed-unit-interval reference as the frozen main target. -/
theorem standardNonatomic_of_standardBorel {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : StandardNonatomic μ := by
  let f := sigmoid ∘ embeddingReal X
  have hf : MeasurableEmbedding f := measurableEmbedding_sigmoid_comp_embeddingReal X
  let ρ := μ.map f
  have : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hf.measurable.aemeasurable
  have : NullSingletonClass ρ := nullSingleton_map_embedding hf μ
  have hq := embedding_unitQuantile ρ
  have h := conullIsomorphic_of_common_embedding hf hq μ volume (map_unitQuantile ρ).symm
  exact h

end SmoothObstruction

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PhaseDynamics
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter Topology

namespace SmoothObstruction.PhaseDynamics

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
lemma iterate_phase {m : ℕ} (T : X → X) (a : X → ZMod m)
    (ha : ∀ x, a (T x) = a x + 1) (x : X) (n : ℕ) :
    a ((T^[n]) x) = a x + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ha, ih, Nat.cast_add, Nat.cast_one, add_assoc]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- Uniform infinite cyclic factors rule out every periodic point. This
uses only the exact phase evolution, not recognition or word frequencies. -/
theorem no_periodic_points (T : X → X) (m : ℕ → ℕ) (a : ∀ i, X → ZMod (m i))
    (ha : ∀ i x, a i (T x) = a i x + 1) (hm : ∀ n, ∃ i, n < m i) :
    ∀ x n, 0 < n → (T^[n]) x ≠ x := by
  intro x n hn hx
  obtain ⟨i, hi⟩ := hm n
  have h := iterate_phase T (a i) (ha i) x n
  rw [hx] at h
  have hn0 : (n : ZMod (m i)) = 0 := by
    apply add_left_cancel (a := a i x)
    simpa using h.symm
  have hdiv := (ZMod.natCast_eq_zero_iff n (m i)).mp hn0
  exact (not_le.mpr hi) (Nat.le_of_dvd hn hdiv)

/-- The phase extension's nonatomicity: a positive singleton would return by
Poincare recurrence, contradicting its arbitrarily large cyclic factors. -/
theorem noAtoms_of_phases (μ : Measure X) [IsFiniteMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (m : ℕ → ℕ) (a : ∀ i, X → ZMod (m i))
    (ha : ∀ i x, a i (T x) = a i x + 1) (hm : ∀ n, ∃ i, n < m i) : NullSingletonClass μ := by
  refine ⟨fun x => ?_⟩
  by_contra hx
  obtain ⟨y, hy, n, hn, hny⟩ := hT.conservative.exists_mem_iterate_mem'
    (measurableSet_singleton x) hx
  have hyx : y = x := mem_singleton_iff.mp hy
  subst y
  exact no_periodic_points T m a ha hm x n (Nat.pos_of_ne_zero hn) (mem_singleton_iff.mp hny)

section Words
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  (m : ℕ → ℕ) (hm : ∀ i, m i ∣ m (i + 1))
  (W : ∀ i, Set (Fin (m i) → A))

omit [DiscreteTopology A] in
lemma continuous_wordAt (i : ℕ) (t : ℤ) : Continuous (fun x : Space A m => wordAt m x i t) :=
  continuous_pi (fun j => (continuous_apply (t + j.val)).comp continuous_fst)

omit [DiscreteTopology A] in
lemma compatible_closed (i : ℕ) : IsClosed {x : Space A m | Compatible m hm x i} := by
  apply isClosed_eq _ ((continuous_apply i).comp continuous_snd)
  exact (continuous_of_discreteTopology : Continuous (ZMod.castHom (hm i) (ZMod (m i)))).comp
    ((continuous_apply (i + 1)).comp continuous_snd)

lemma legal_closed (i : ℕ) : IsClosed {x : Space A m | Legal m W x i} := by
  have heq : {x : Space A m | Legal m W x i} =
      ⋂ t : ℤ, ({x : Space A m | (t : ZMod (m i)) ≠ -x.2 i} ∪
        (fun x : Space A m => wordAt m x i t) ⁻¹' W i) := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_preimage, Legal]
    simp only [imp_iff_not_or]
  rw [heq]
  apply isClosed_iInter
  intro t
  apply IsClosed.union _ ((isClosed_discrete (W i)).preimage (continuous_wordAt m i t))
  have hc : IsClosed {a : ZMod (m i) | (t : ZMod (m i)) ≠ -a} := isClosed_discrete _
  exact hc.preimage (show Continuous (fun x : Space A m => x.2 i) from
    (continuous_apply i).comp continuous_snd)

lemma extension_closed : IsClosed (extension m hm W) := by
  have heq : extension m hm W =
      ⋂ i, {x : Space A m | Compatible m hm x i} ∩ {x : Space A m | Legal m W x i} := by
    ext x; simp [extension]
  rw [heq]
  exact isClosed_iInter (fun i => (compatible_closed m hm i).inter (legal_closed m W i))

/-- Compactness needs only finite-level admissible configurations. The actual
word hierarchy supplies these by periodically repeating a word at the largest
requested level; no invariant measure or frequency hypothesis enters. -/
theorem extension_nonempty [CompactSpace A] [∀ i, NeZero (m i)]
    (hfinite : ∀ n, ∃ x : Space A m, ∀ i ≤ n, Compatible m hm x i ∧ Legal m W x i) :
    (extension m hm W).Nonempty := by
  let E : ℕ → Set (Space A m) := fun n =>
    {x | ∀ i ≤ n, Compatible m hm x i ∧ Legal m W x i}
  have hcl (n : ℕ) : IsClosed (E n) := by
    have heq : E n = ⋂ i ∈ Set.Iic n,
        {x : Space A m | Compatible m hm x i} ∩ {x : Space A m | Legal m W x i} := by
      ext x; simp [E]
    rw [heq]
    exact isClosed_biInter (fun i _ => (compatible_closed m hm i).inter (legal_closed m W i))
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed E
    (fun n x hx i hi => hx i (by omega)) hfinite (hcl 0).isCompact hcl
  refine ⟨x, fun i => ?_⟩
  exact (mem_iInter.mp hx i) i le_rfl

end Words
end SmoothObstruction.PhaseDynamics

end

section

namespace SmoothObstruction.PhaseDynamics
open MeasureTheory Set Filter
open scoped Topology
variable {A : Type} [Fintype A] [Nonempty A] [TopologicalSpace A]
  [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
  (m : ℕ → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, m i ∣ m (i+1))
  (W : ∀ i, Set (Fin (m i) → A))

omit [Fintype A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [∀ i, NeZero (m i)] in
lemma extension_coordinate_space :
    (inferInstance : MeasurableSpace (extension m hm W)) = MeasurableSpace.comap
      (PhaseEntropy.coordinates (fun x : extension m hm W => x.val.1)
        (fun x : extension m hm W => x.val.2)) MeasurableSpace.pi := by
  let e := MeasurableEquiv.sumPiEquivProdPi (PhaseEntropy.Coordinate A m)
  have he := e.symm.measurableEmbedding.comap_eq
  have hc : PhaseEntropy.coordinates (fun x : extension m hm W => x.val.1)
      (fun x : extension m hm W => x.val.2) = e.symm ∘ Subtype.val := by
    funext x i
    cases i <;> rfl
  change MeasurableSpace.comap (Subtype.val : extension m hm W → Space A m)
    inferInstance = _
  exact (congrArg (MeasurableSpace.comap (Subtype.val : extension m hm W → Space A m)) he).symm.trans
    (MeasurableSpace.comap_comp.trans (congrArg (fun f => MeasurableSpace.comap f MeasurableSpace.pi) hc.symm))

/-- A genuine ergodic invertible standard nonatomic finite-KS system from
any nonempty finite admissible word hierarchy with unbounded lengths.
This is the measure-theoretic construction, not its graph obstruction. -/
theorem exists_system
    (hunbounded : ∀ n, ∃ i, n < m i)
    (hfinite : ∀ n, ∃ x : Space A m, ∀ i ≤ n, Compatible m hm x i ∧ Legal m W x i) :
    ∃ μ : ProbabilityMeasure (extension m hm W),
      StandardNonatomic (μ : Measure (extension m hm W)) ∧
      Ergodic (extensionShift m hm W) (μ : Measure (extension m hm W)) ∧
      FiniteKSEntropy (μ : Measure (extension m hm W)) (extensionShift m hm W) := by
  let : CompactSpace A := Finite.compactSpace
  let : Fact (IsClosed (extension m hm W)) := ⟨extension_closed m hm W⟩
  let : CompactSpace (extension m hm W) := isCompact_iff_compactSpace.mp (extension_closed m hm W).isCompact
  have hn := extension_nonempty m hm W hfinite
  let : Nonempty (extension m hm W) := hn.to_subtype
  let : StandardBorelSpace (extension m hm W) := (extension_closed m hm W).measurableSet.standardBorel
  obtain ⟨μ,hμ⟩ := CompactInvariant.exists_ergodic_probability
    (extensionShift m hm W) (extensionShift m hm W).continuous
  let : NullSingletonClass (μ : Measure (extension m hm W)) :=
    noAtoms_of_phases μ (extensionShift m hm W) hμ.toMeasurePreserving m
      (fun i x => x.val.2 i) (fun _ _ => rfl) hunbounded
  refine ⟨μ,standardNonatomic_of_standardBorel (μ : Measure (extension m hm W)),hμ,?_⟩
  exact PhaseEntropy.finiteKS (fun x : extension m hm W => x.val.1)
    (fun x : extension m hm W => x.val.2) μ hμ.toMeasurePreserving
    (extension_coordinate_space m hm W) (fun _ _ => rfl) (fun _ _ => rfl)
end SmoothObstruction.PhaseDynamics

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordParameters
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty _root_.OAI.SmoothObstruction.WordHierarchy.lengthNeZero _root_.OAI.SmoothObstruction.WordHierarchy.recognitionLengthNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology

namespace SmoothObstruction.WordParameters

lemma length_ge_two_pow {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    2 ^ i ≤ length s₀ i := by
  induction i with
  | zero => simp [length]
  | succ i ih =>
    have hk := (sequence_growth h₀ i).1
    rw [length, pow_succ]
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 1 ≤ K (sequence s₀ i) by omega)
    exact Nat.mul_le_mul ih (by simpa using hpow)

lemma length_unbounded {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (n : ℕ) :
    ∃ i, n < length s₀ i := by
  refine ⟨n, (Nat.lt_two_pow_self (n := n)).trans_le (length_ge_two_pow h₀ n)⟩

end SmoothObstruction.WordParameters

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordHierarchy
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty _root_.OAI.SmoothObstruction.WordHierarchy.levelNonempty _root_.OAI.SmoothObstruction.WordHierarchy.recognitionLengthNeZero _root_.OAI.SmoothObstruction.WordHierarchy.recognitionNNeZero _root_.OAI.SmoothObstruction.WordHierarchy.stageLengthNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.WordConcatenation
variable {A B : Type*} {m N : ℕ}

lemma pack_val (b : Fin N) (r : Fin m) : (pack (b,r)).val = b.val*m+r.val := by
  change r.val + m*b.val = b.val*m+r.val
  ac_rfl

/-- Every aligned lower word in a concatenation is an actual constituent,
including near the last endpoint. -/
lemma slice_is_constituent (hm : 0 < m) (u : B → Fin m → A) (w : Fin N → B)
    (a : ℕ) (ha : m ∣ a) (hlen : a+m ≤ m*N) :
    ∃ b : Fin N, (fun r : Fin m => concat u w
      ⟨a+r.val,lt_of_lt_of_le (Nat.add_lt_add_left r.isLt a) hlen⟩) = u (w b) := by
  have hb : a/m < N := by
    apply (Nat.div_lt_iff_lt_mul hm).mpr
    rw [Nat.mul_comm N m]
    omega
  let b : Fin N := ⟨a/m,hb⟩
  have hab : b.val*m = a := Nat.div_mul_cancel ha
  refine ⟨b,?_⟩
  funext r
  have hi : (⟨a+r.val,lt_of_lt_of_le (Nat.add_lt_add_left r.isLt a) hlen⟩ : Fin (m*N)) =
      pack (b,r) := by
    apply Fin.ext
    simp only [pack_val,hab]
  rw [hi,concat_pack]
end SmoothObstruction.WordConcatenation

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation

lemma words_nonempty (i : ℕ) : (words i).Nonempty := by
  let : Nonempty (A i) := alphabet_nonempty i
  exact Set.range_nonempty _

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.PhaseDynamics
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  (m : ℕ → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, m i ∣ m (i+1))
  (W : ∀ i, Set (Fin (m i) → A))

omit [TopologicalSpace A] [DiscreteTopology A] in
include hm in
lemma legal_of_succ (hW : SubwordClosed m W) (x : Space A m)
    (hx : ∀ i, x.2 i = 0) (i : ℕ) (hi : Legal m W x (i+1)) : Legal m W x i := by
  intro t ht
  have ht0 : (t : ZMod (m i)) = 0 := by simpa only [hx,neg_zero] using ht
  let r := (t : ZMod (m (i+1))).val
  have hr : r < m (i+1) := ZMod.val_lt _
  have hrmod : (r : ZMod (m (i+1))) = (t : ZMod (m (i+1))) := by
    exact ZMod.natCast_zmod_val _
  have hr0 : (r : ZMod (m i)) = 0 := by
    have hh := congrArg (ZMod.castHom (hm i) (ZMod (m i))) hrmod
    simpa only [map_natCast,map_intCast,ht0] using hh
  have hrdvd : m i ∣ r := (ZMod.natCast_eq_zero_iff r (m i)).mp hr0
  have hlen : r+m i ≤ m (i+1) := by
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt hr) (Nat.dvd_sub (hm i) hrdvd)
    omega
  have hstart : ((t-(r:ℤ) : ℤ) : ZMod (m (i+1))) = -x.2 (i+1) := by
    simp only [Int.cast_sub,Int.cast_natCast,hx,neg_zero,hrmod,sub_self]
  have hw := hW i (wordAt m x (i+1) (t-r)) (hi (t-r) hstart) r hrdvd hlen
  have heq : wordAt m x i t = fun j : Fin (m i) =>
      wordAt m x (i+1) (t-r) ⟨r+j.val,lt_of_lt_of_le (Nat.add_lt_add_left j.isLt r) hlen⟩ := by
    funext j
    change x.1 (t+(j.val:ℤ)) = x.1 (t-(r:ℤ)+((r+j.val:ℕ):ℤ))
    apply congrArg x.1
    push_cast
    ring
  simpa only [heq] using hw

omit [TopologicalSpace A] [DiscreteTopology A] in
lemma repeatWord_legal (n : ℕ) (w : Fin (m n) → A) (hw : w ∈ W n) :
    Legal m W (repeatWord m n w) n := by
  intro t ht
  have ht0 : (t : ZMod (m n)) = 0 := by simpa [repeatWord] using ht
  have heq : wordAt m (repeatWord m n w) n t = w := by
    funext j
    change w ⟨((t+j.val : ℤ) : ZMod (m n)).val,ZMod.val_lt _⟩ = w j
    congr 1
    apply Fin.ext
    simp only [Int.cast_add,Int.cast_natCast,ht0,zero_add,ZMod.val_natCast_of_lt j.isLt]
  simpa only [heq] using hw

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Every nonempty concatenated word hierarchy has all the finite-level
configurations required by the compact phase construction. -/
theorem finite_configs (hW : SubwordClosed m W) (hne : ∀ i, (W i).Nonempty) :
    ∀ n, ∃ x : Space A m, ∀ i ≤ n, Compatible m hm x i ∧ Legal m W x i := by
  intro n
  obtain ⟨w,hw⟩ := hne n
  refine ⟨repeatWord m n w,fun i hi => ⟨?_,?_⟩⟩
  · simp [Compatible,repeatWord]
  · have htop := repeatWord_legal m W n w hw
    induction hi using Nat.decreasingInduction with
    | self => exact htop
    | of_succ i hi ih => exact legal_of_succ m hm W hW _ (fun _ => rfl) i ih
end SmoothObstruction.PhaseDynamics

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory

lemma words_subwordClosed : PhaseDynamics.SubwordClosed (length 40000) words := by
  intro i w hw r hr hlen
  obtain ⟨a,rfl⟩ := hw
  obtain ⟨b,hb⟩ := slice_is_constituent (length_pos 40000 i) (word i) (children i a) r hr hlen
  change (fun j => concat (word i) (children i a) _) ∈ Set.range (word i)
  exact ⟨children i a b,hb.symm⟩

/-- Here the finite-admissibility producers are discharged by the actual
words. The remaining main obstruction is not part of this theorem. -/
theorem actual_system : ∃ μ : ProbabilityMeasure Extension,
    StandardNonatomic (μ : Measure Extension) ∧
    Ergodic (PhaseDynamics.extensionShift (length 40000) (length_dvd 40000) words)
      (μ : Measure Extension) ∧
    FiniteKSEntropy (μ : Measure Extension)
      (PhaseDynamics.extensionShift (length 40000) (length_dvd 40000) words) := by
  exact PhaseDynamics.exists_system (length 40000) (length_dvd 40000) words
    (length_unbounded initial_threshold)
    (PhaseDynamics.finite_configs (length 40000) (length_dvd 40000) words
      words_subwordClosed words_nonempty)

end SmoothObstruction.WordHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {d : ℕ} {M : Type} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]

theorem euclidean_switching [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
    [IsManifold (𝓡 d) ∞ M]
    (μ : ProbabilityMeasure M) (hμ : SmoothPositiveDensity (𝓡 d) (μ : Measure M))
    (S : Diffeomorph (𝓡 d) (𝓡 d) M M ∞)
    (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M)) :
    SmoothSwitching (μ : Measure M) S S.symm := by
  have hr : range (𝓡 d)=univ := by ext x; simp
  apply ManifoldCoordinates.switching_from_gauges (𝓡 d) (by rw [hr]; exact isClosed_univ) μ hμ S hS
  intro ι inst a K hK hKU
  refine ⟨0,le_rfl,?_⟩
  intro r hr₀
  refine ⟨∅,MeasurableSet.empty,by simp,?_⟩
  intro i x hx hxW
  rw [hr,interior_univ]
  exact subset_univ _

theorem halfspace_switching [NeZero d] [ChartedSpace (EuclideanHalfSpace d) M]
    [IsManifold (𝓡∂ d) ∞ M]
    (μ : ProbabilityMeasure M) (hμ : SmoothPositiveDensity (𝓡∂ d) (μ : Measure M))
    (S : Diffeomorph (𝓡∂ d) (𝓡∂ d) M M ∞)
    (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M)) :
    SmoothSwitching (μ : Measure M) S S.symm := by
  have hr : IsClosed (range (𝓡∂ d)) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact isClosed_le continuous_const (by fun_prop)
  apply ManifoldCoordinates.switching_from_gauges (𝓡∂ d) hr μ hμ S hS
  intro ι inst a K hK hKU
  obtain ⟨C,hC,hcol⟩ := ChartDensity.global_halfspace_collar (μ : Measure M) hμ a K hK hKU
  exact ⟨C,hC.le,hcol⟩
end SmoothObstruction

namespace SmoothObstruction
open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff
open WordHierarchy

/-- No closed smooth positive-density model in any finite dimension. The
compatible metric used in the switching proof is chosen from the given topology;
no metric or orientability hypothesis is imposed on the model. -/
theorem no_euclidean_model (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (d : ℕ) :
    ¬ HasModelWith μ T (𝓡 d) := by
  classical
  rintro ⟨M,top,meas,borel,t2,ct,compact,chart,manifold,ν,prob,S,hν,hS,hc⟩
  let : TopologicalSpace M := top
  let : MeasurableSpace M := meas
  let : BorelSpace M := borel
  let : T2Space M := t2
  let : SecondCountableTopology M := ct
  let : CompactSpace M := compact
  let : ChartedSpace (EuclideanSpace ℝ (Fin d)) M := chart
  let : IsManifold (𝓡 d) ∞ M := manifold
  let : IsProbabilityMeasure ν := prob
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  let : Nonempty M := nonempty_of_isProbabilityMeasure ν
  have hswitch := euclidean_switching (⟨ν,prob⟩ : ProbabilityMeasure M) hν S hS
  have hSi : MeasurePreserving S.symm ν ν :=
    MeasurePreserving.symm S.toHomeomorph.toMeasurableEquiv hS
  obtain ⟨r,hr,B,hB,hBc,hBf,hBi,hforward,hinverse⟩ :=
    ConullTransport.from_conjugate_bilateral μ ν T.toEquiv S.toEquiv hc
      (Classical.choice (nonempty_of_isProbabilityMeasure μ))
  exact no_switching μ hT ν S.toEquiv hS hSi r hr B hB hBc hBi hforward hswitch

/-- The same obstruction for smooth boundary manifolds, with their genuine
half-space chart densities. No orientability assumption is introduced. -/
theorem no_halfspace_model (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (d : ℕ) [NeZero d] :
    ¬ HasModelWith μ T (𝓡∂ d) := by
  classical
  rintro ⟨M,top,meas,borel,t2,ct,compact,chart,manifold,ν,prob,S,hν,hS,hc⟩
  let : TopologicalSpace M := top
  let : MeasurableSpace M := meas
  let : BorelSpace M := borel
  let : T2Space M := t2
  let : SecondCountableTopology M := ct
  let : CompactSpace M := compact
  let : ChartedSpace (EuclideanHalfSpace d) M := chart
  let : IsManifold (𝓡∂ d) ∞ M := manifold
  let : IsProbabilityMeasure ν := prob
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  let : Nonempty M := nonempty_of_isProbabilityMeasure ν
  have hswitch := halfspace_switching (⟨ν,prob⟩ : ProbabilityMeasure M) hν S hS
  have hSi : MeasurePreserving S.symm ν ν :=
    MeasurePreserving.symm S.toHomeomorph.toMeasurableEquiv hS
  obtain ⟨r,hr,B,hB,hBc,hBf,hBi,hforward,hinverse⟩ :=
    ConullTransport.from_conjugate_bilateral μ ν T.toEquiv S.toEquiv hc
      (Classical.choice (nonempty_of_isProbabilityMeasure μ))
  exact no_switching μ hT ν S.toEquiv hS hSi r hr B hB hBc hBi hforward hswitch

/-- An ergodic invertible finite-KS-entropy transformation of a standard
nonatomic probability space, with no compact finite-dimensional smooth
strictly-positive-density model even modulo invariant null sets. -/
theorem main_oai :
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (_ : IsProbabilityMeasure μ) (T : X ≃ᵐ X),
      StandardNonatomic μ ∧ Ergodic T μ ∧ FiniteKSEntropy μ T ∧
        ¬ HasSmoothPositiveVolumeModel μ T := by
  classical
  obtain ⟨μ,hstd,herg,hent⟩ := actual_system
  refine ⟨Extension,inferInstance,(μ : Measure Extension),inferInstance,
    wordMeasurableEquiv,hstd,herg,hent,?_⟩
  rintro (⟨d,hmodel⟩ | ⟨d,hd,hmodel⟩)
  · exact no_euclidean_model (μ : Measure Extension) herg.toMeasurePreserving d hmodel
  · let : NeZero d := hd
    exact no_halfspace_model (μ : Measure Extension) herg.toMeasurePreserving d hmodel
end SmoothObstruction

end

end OAI
end

theorem solution : type_of% @OAI.SmoothObstruction.main_oai := @OAI.SmoothObstruction.main_oai
