-- Prove2me | solution 1 for OAI.SmoothObstruction.ManifoldCoordinates.family_original_germ_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:17:01.897329+00:00
-- url     : https://prove2.me/submissions/0899601f-13b4-4e52-be04-97f9c656a7b4

import Mathlib
import Definitions.Def_OAIQ5T3000

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

namespace SmoothObstruction.CarriedCharts
open Set Metric Filter Topology
open scoped ContDiff
variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- Uniform C2 bounds up to a closed model boundary, WITHOUT an extension
assumption. Ordinary derivatives are taken only in the original interior;
the bound is independent of distance to the boundary. -/
theorem uniform_c2_boundary (f : ι → E → F) (K U : ι → Set E) (H : Set E)
    (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i)) (hH : IsClosed H)
    (hKU : ∀ i,K i⊆U i) (huniq : ∀ i,UniqueDiffOn ℝ (U i∩H))
    (hf : ∀ i,ContDiffOn ℝ ∞ (f i) (U i∩H)) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ i x,x∈K i →
      closedBall x r⊆U i ∧ ∀ y∈closedBall x r,y∈interior H →
        ContDiffAt ℝ ∞ (f i) y ∧
        ‖fderiv ℝ (f i) y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (f i)) y‖ ≤ C := by
  have hex (i : ι) : ∃ r : ℝ,0 < r ∧ cthickening r (K i)⊆U i :=
    (hK i).exists_cthickening_subset_open (hU i) (hKU i)
  choose r hr hrU using hex
  obtain ⟨a,ha,har⟩ := finite_positive_lower r hr
  let s (i : ι) := U i∩H
  let f₁ (i : ι) := fderivWithin ℝ (f i) (s i)
  let f₂ (i : ι) := fderivWithin ℝ (f₁ i) (s i)
  have hf₁ (i : ι) : ContDiffOn ℝ ∞ (f₁ i) (s i) :=
    (hf i).fderivWithin (huniq i) (by simp)
  have hf₂ (i : ι) : ContDiffOn ℝ ∞ (f₂ i) (s i) :=
    (hf₁ i).fderivWithin (huniq i) (by simp)
  have hb (i : ι) : ∃ C : ℝ,∀ y∈cthickening (r i) (K i)∩H,
      ‖f₁ i y‖ ≤ C ∧ ‖f₂ i y‖ ≤ C := by
    have hcomp : IsCompact (cthickening (r i) (K i)∩H) := (hK i).cthickening.inter_right hH
    have hsub : cthickening (r i) (K i)∩H⊆s i := fun y hy => ⟨hrU i hy.1,hy.2⟩
    obtain ⟨A,hA⟩ := hcomp.exists_bound_of_continuousOn (f := f₁ i)
      ((hf₁ i).continuousOn.mono hsub)
    obtain ⟨B,hB⟩ := hcomp.exists_bound_of_continuousOn (f := f₂ i)
      ((hf₂ i).continuousOn.mono hsub)
    exact ⟨max A B,fun y hy => ⟨(hA y hy).trans (le_max_left _ _),
      (hB y hy).trans (le_max_right _ _)⟩⟩
  choose C hC using hb
  let D : ℝ := 1+∑ i,|C i|
  have hD : 1 ≤ D := by
    dsimp [D]
    have hh : 0≤∑ i,|C i| := Finset.sum_nonneg (fun i _ => abs_nonneg (C i))
    linarith
  have hCD (i : ι) : C i ≤ D := by
    have hh : |C i| ≤ ∑ j,|C j| := Finset.single_le_sum (fun j _ => abs_nonneg (C j))
      (Finset.mem_univ i)
    dsimp [D]
    linarith [le_abs_self (C i)]
  refine ⟨a,D,ha,hD,fun i x hx => ?_⟩
  have hball : closedBall x a⊆cthickening (r i) (K i) :=
    (closedBall_subset_closedBall (har i)).trans (closedBall_subset_cthickening hx (r i))
  refine ⟨hball.trans (hrU i),fun y hy hyH => ?_⟩
  have hyU := hrU i (hball hy)
  have hys : s i∈𝓝 y := inter_mem ((hU i).mem_nhds hyU) (mem_interior_iff_mem_nhds.mp hyH)
  have heq : f₁ i =ᶠ[𝓝 y] fderiv ℝ (f i) := by
    filter_upwards [((hU i).inter isOpen_interior).mem_nhds ⟨hyU,hyH⟩] with z hz
    exact fderivWithin_of_mem_nhds (inter_mem ((hU i).mem_nhds hz.1)
      (mem_interior_iff_mem_nhds.mp hz.2))
  have hfirst : f₁ i y=fderiv ℝ (f i) y := heq.eq_of_nhds
  have hsecond : f₂ i y=fderiv ℝ (fderiv ℝ (f i)) y :=
    (fderivWithin_of_mem_nhds hys).trans heq.fderiv_eq
  have hb' := hC i y ⟨hball hy,interior_subset hyH⟩
  rw [hfirst,hsecond] at hb'
  exact ⟨(hf i y ⟨hyU,interior_subset hyH⟩).contDiffAt hys,
    hb'.1.trans (hCD i),hb'.2.trans (hCD i)⟩
end SmoothObstruction.CarriedCharts

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
lemma isOpen_domainU (S : Diffeomorph I I M M ∞) (a b : M) : IsOpen (domainU I S a b) :=
  ((chartAt H a).isOpen_inter_preimage_symm
    ((chartAt H b).open_source.preimage S.continuous)).preimage I.continuous_symm

omit [IsManifold I ∞ M] in
lemma map_mem_domainU (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) : (extChartAt I a) x∈domainU I S a b := by
  have ht := (extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1)
  have htar : I.symm ((extChartAt I a) x)∈(chartAt H a).target := by
    rw [extChartAt,OpenPartialHomeomorph.extend_target] at ht
    exact ht.1
  refine ⟨htar,?_⟩
  change S ((extChartAt I a).symm ((extChartAt I a) x))∈(chartAt H b).source
  rw [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1)]
  exact hx.2

theorem contDiffOn_localMap (S : Diffeomorph I I M M ∞) (a b : M) :
    ContDiffOn ℝ ∞ (localMap I S a b) (domainU I S a b∩range I) := by
  intro y hy
  have hyt : y∈(extChartAt I a).target := by
    rw [extChartAt,OpenPartialHomeomorph.extend_target]
    exact ⟨hy.1.1,hy.2⟩
  have hby : S ((extChartAt I a).symm y)∈(chartAt H b).source := hy.1.2
  have hf : ContMDiffAt I (𝓘(ℝ,E (d:=d))) ∞ (extChartAt I b ∘ S)
      ((extChartAt I a).symm y) :=
    (contMDiffAt_extChartAt' (I:=I) hby).comp _ (S.contMDiff _)
  have hh := hf.comp_contMDiffWithinAt y
    (contMDiffWithinAt_extChartAt_symm_range (I:=I) (n:=∞) a hyt)
  have hd : ContDiffWithinAt ℝ ∞ (localMap I S a b) (range I) y :=
    contMDiffWithinAt_iff_contDiffWithinAt.mp hh
  exact hd.mono inter_subset_right

/-- Genuine uniform first and second derivative bounds for all actually
used local chart pairs. Valid for the closed half-space model, uniformly
as the reference point approaches the boundary. No extension theorem or
long-iterate C2 bound has been assumed. -/
theorem actual_uniform_c2 [T2Space M] {ι : Type*} [Fintype ι]
    (hclosed : IsClosed (range I)) (S : Diffeomorph I I M M ∞)
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ i j x,x∈K i → S x∈K j →
      closedBall ((extChartAt I (a i)) x) r⊆domainU I S (a i) (a j) ∧
      ∀ y∈closedBall ((extChartAt I (a i)) x) r,y∈interior (range I) →
        ContDiffAt ℝ ∞ (localMap I S (a i) (a j)) y ∧
        ‖fderiv ℝ (localMap I S (a i) (a j)) y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (localMap I S (a i) (a j))) y‖ ≤ C := by
  let L (ij : ι×ι) := (extChartAt I (a ij.1)) '' (K ij.1∩S ⁻¹' K ij.2)
  have hcomp (ij : ι×ι) : IsCompact (L ij) :=
    ((hK ij.1).inter_right ((hK ij.2).isClosed.preimage S.continuous)).image_of_continuousOn
      ((continuousOn_extChartAt (I:=I) (a ij.1)).mono (fun x hx => by simpa only [extChartAt_source] using hKU _ hx.1))
  have hsub (ij : ι×ι) : L ij⊆domainU I S (a ij.1) (a ij.2) := by
    rintro z ⟨x,hx,rfl⟩
    exact map_mem_domainU I S (a ij.1) (a ij.2) x ⟨hKU _ hx.1,hKU _ hx.2⟩
  obtain ⟨r,C,hr,hC,hh⟩ := CarriedCharts.uniform_c2_boundary
    (fun ij : ι×ι => localMap I S (a ij.1) (a ij.2)) L
    (fun ij => domainU I S (a ij.1) (a ij.2)) (range I) hcomp
    (fun ij => isOpen_domainU I S (a ij.1) (a ij.2)) hclosed hsub
    (fun ij => by simpa only [inter_comm] using
      I.uniqueDiffOn.inter (isOpen_domainU I S (a ij.1) (a ij.2)))
    (fun ij => contDiffOn_localMap I S (a ij.1) (a ij.2))
  exact ⟨r,C,hr,hC,fun i j x hx hSx => hh (i,j) ((extChartAt I (a i)) x) ⟨x,⟨hx,hSx⟩,rfl⟩⟩
end SmoothObstruction.ManifoldCoordinates

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

namespace SmoothObstruction.ChartDensity
open Set MeasureTheory Filter Topology
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]

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

end SmoothObstruction.ChartDensity

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_MinorTransfer
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.MinorGraph
open Matrix Set Metric
open scoped Matrix.Norms.Elementwise
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma block_factorization (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n m ℝ) (D : Matrix n n ℝ) (hA : A.det≠0) (hD : D.det≠0) :
    (fromBlocks A B C D).det=A.det*D.det*
      (fromBlocks 1 (A⁻¹*B) (D⁻¹*C) 1).det := by
  have he : fromBlocks A B C D = fromBlocks A 0 0 D *
      fromBlocks 1 (A⁻¹*B) (D⁻¹*C) 1 := by
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_one,Matrix.zero_mul,add_zero,zero_add,
      ←Matrix.mul_assoc,Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
      Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.mpr hD),Matrix.one_mul]
  rw [he,Matrix.det_mul,Matrix.det_fromBlocks_zero₂₁]

/-- The modulus depends only on the two dimensions, never on the size or
sign of the leading determinants. -/
theorem normalized_close (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (B : Matrix m n ℝ) (C : Matrix n m ℝ),
      ‖B‖≤δ → ‖C‖≤δ → |(fromBlocks 1 B C 1).det-1|<ε := by
  have hc : ContinuousAt (fun Z : Matrix (m⊕n) (m⊕n) ℝ => Z.det) 1 :=
    continuous_id.matrix_det.continuousAt
  obtain ⟨r,hr,hh⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨r/2,by positivity,fun B C hB hC => ?_⟩
  have hn : ‖fromBlocks (1 : Matrix m m ℝ) B C (1 : Matrix n n ℝ)-1‖ ≤ r/2 := by
    apply (Matrix.norm_le_iff (by positivity)).mpr
    intro i j
    cases i <;> cases j
    · simp [Matrix.fromBlocks,Matrix.one_apply]; positivity
    · simpa [Matrix.fromBlocks,Matrix.one_apply] using
        ((Matrix.norm_le_iff (by positivity)).mp hB _ _)
    · simpa [Matrix.fromBlocks,Matrix.one_apply] using
        ((Matrix.norm_le_iff (by positivity)).mp hC _ _)
    · simp [Matrix.fromBlocks,Matrix.one_apply]; positivity
  have h := hh (lt_of_le_of_lt (by simpa only [dist_eq_norm] using hn) (by linarith))
  simpa only [Matrix.det_one,Real.dist_eq] using h

end SmoothObstruction.MinorGraph

namespace SmoothObstruction.MinorGraph
open Matrix
open scoped Matrix.Norms.Elementwise
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Three signed relative errors compose without an absolute determinant
floor. The constants here leave room for the source's four-Jacobian bound. -/
lemma triple_relative_error {a b c ε : ℝ} (hε : 0≤ε) (hε1 : ε≤1)
    (ha : |a-1|≤ε) (hb : |b-1|≤ε) (hc : |c-1|≤ε) :
    |a*b*c-1|≤7*ε := by
  have hbb : |b|≤2 := by
    have hh := abs_sub_le b 1 0
    norm_num at hh
    linarith
  have hcc : |c|≤2 := by
    have hh := abs_sub_le c 1 0
    norm_num at hh
    linarith
  calc
    _ = |(a-1)*b*c+(b-1)*c+(c-1)| := by congr 1; ring
    _ ≤ |(a-1)*b*c|+|(b-1)*c|+|c-1| := by
      linarith [abs_add_le ((a-1)*b*c+(b-1)*c) (c-1),
        abs_add_le ((a-1)*b*c) ((b-1)*c)]
    _ = |a-1| *|b| *|c|+|b-1| *|c|+|c-1| := by rw [abs_mul,abs_mul,abs_mul]
    _ ≤ ε*2*2+ε*2+ε := by
      gcongr
    _ = 7*ε := by ring

/-- The actual joint endpoint determinant, measured relative to the OLD
leading volumes. Off-diagonal hypotheses are actual inverse-block entries,
so `common_perturbed_endpoint_graph_bound` supplies precisely these bounds.
Both blocks may be empty and the old leading volumes may be arbitrarily
small or have either sign. -/
theorem joint_relative_transfer : ∃ δ : ℝ,0<δ ∧
    ∀ (A₀ : Matrix m m ℝ) (D₀ : Matrix n n ℝ)
      (A : Matrix m m ℝ) (B : Matrix m n ℝ)
      (C : Matrix n m ℝ) (D : Matrix n n ℝ),
      A₀.det≠0 → D₀.det≠0 →
      |A.det/A₀.det-1|≤(1/100:ℝ) → |D.det/D₀.det-1|≤(1/100:ℝ) →
      (∀ i j,|(A⁻¹*B) i j|≤δ) → (∀ i j,|(D⁻¹*C) i j|≤δ) →
      |(fromBlocks A B C D).det/(A₀.det*D₀.det)-1|≤(1/10:ℝ) := by
  obtain ⟨δ,hδ,hclose⟩ := normalized_close (m:=m) (n:=n) (1/100:ℝ) (by norm_num)
  refine ⟨δ,hδ,fun A₀ D₀ A B C D hA₀ hD₀ hA hD hAB hDC => ?_⟩
  have hAn : A.det≠0 := by intro ha; norm_num [ha] at hA
  have hDn : D.det≠0 := by intro hd; norm_num [hd] at hD
  have hab : ‖A⁻¹*B‖≤δ := (Matrix.norm_le_iff hδ.le).mpr (fun i j => by simpa using hAB i j)
  have hdc : ‖D⁻¹*C‖≤δ := (Matrix.norm_le_iff hδ.le).mpr (fun i j => by simpa using hDC i j)
  have hj := hclose (A⁻¹*B) (D⁻¹*C) hab hdc
  have he : (fromBlocks A B C D).det/(A₀.det*D₀.det)=
      A.det/A₀.det*(D.det/D₀.det)*(fromBlocks 1 (A⁻¹*B) (D⁻¹*C) 1).det := by
    rw [block_factorization A B C D hAn hDn]
    field_simp
  rw [he]
  have hh := triple_relative_error (by norm_num : (0:ℝ)≤1/100)
    (by norm_num : (1/100:ℝ)≤1) hA hD hj.le
  exact hh.trans (by norm_num)
end SmoothObstruction.MinorGraph

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_TubeProjection
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
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- All the one-step tube/Taylor hypotheses used by the boundary-value
solver follow from actual one-step smoothness on the finite compact atlas.
The only variable-domain input is the literal avoidance of the boundary. -/
theorem actual_tube_data (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1≤C ∧ ∀ (i j : ι) (x : M) (δ : ℝ),
      x∈K i → S x∈K j → 0≤δ → δ ≤ r →
      closedBall ((extChartAt I (a i)) x) δ⊆interior (range I) →
      closedBall ((extChartAt I (a i)) x) δ⊆(extChartAt I (a i)).target ∧
      closedBall ((extChartAt I (a i)) x) δ⊆domainU I S (a i) (a j) ∧
      ∀ y∈closedBall ((extChartAt I (a i)) x) δ,
        ContDiffAt ℝ ∞ (localMap I S (a i) (a j)) y ∧
        ‖fderiv ℝ (localMap I S (a i) (a j)) y‖≤C ∧
        ‖fderiv ℝ (localMap I S (a i) (a j)) y-
          fderiv ℝ (localMap I S (a i) (a j)) ((extChartAt I (a i)) x)‖≤
            C*‖y-(extChartAt I (a i)) x‖ := by
  obtain ⟨r,C,hr,hC,hh⟩ := actual_uniform_c2 I hclosed S a K hK hKU
  refine ⟨r,C,hr,hC,fun i j x δ hx hSx hδ hδr hsafe => ?_⟩
  have hball := closedBall_subset_closedBall hδr (x:=(extChartAt I (a i)) x)
  have hdat := hh i j x hx hSx
  have hdom := hball.trans hdat.1
  refine ⟨?_,hdom,fun y hy => ?_⟩
  · intro y hy
    rw [extChartAt,OpenPartialHomeomorph.extend_target]
    exact ⟨(hdom hy).1,interior_subset (hsafe hy)⟩
  · have hyd := hdat.2 y (hball hy) (hsafe hy)
    refine ⟨hyd.1,hyd.2.1,?_⟩
    apply (convex_closedBall ((extChartAt I (a i)) x) δ).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    · intro z hz
      exact ((hdat.2 z (hball hz) (hsafe hz)).1.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
    · intro z hz
      exact (hdat.2 z (hball hz) (hsafe hz)).2.2
    · exact mem_closedBall_self hδ
    · exact hy
end SmoothObstruction.ManifoldCoordinates

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

namespace SmoothObstruction.ProductBasis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma blockMap_apply (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V)
    (v : EuclideanSpace ℝ (ι ⊕ κ)) :
    blockMap U V h bU bV v=
      (bU.repr.symm (EuclideanSpace.sumEquivProd v).1:E)+
      (bV.repr.symm (EuclideanSpace.sumEquivProd v).2:E) := rfl

end SmoothObstruction.ProductBasis

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_EndpointFrames
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.EndpointFrame
open Set Matrix
open scoped EuclideanGeometry
variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

lemma coordinates_projection (W : Submodule ℝ E)
    (b : OrthonormalBasis (Fin d) ℝ E) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (x : E) :
    coordinates b r (W.starProjection x)=coordinates b r x := by
  ext i
  simp only [coordinates_apply,b.repr_apply_apply]
  have hi : powersetCard.ofFinEmbEquiv.symm r i∈r :=
    (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem r _).mp ⟨i,rfl⟩
  have hh := W.inner_orthogonalProjectionOnto_eq_of_mem_left
    (⟨b (powersetCard.ofFinEmbEquiv.symm r i),hr _ hi⟩ : W) x
  exact hh

/-- Endpoint-coordinate equality is precisely the reference projected
endpoint datum used by the genuine boundary-value problem. -/
lemma coordinates_eq_iff (W : Submodule ℝ E)
    (b : OrthonormalBasis (Fin d) ℝ E) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (hz : ∀ x∈W,∀ j∉r,b.repr x j=0) (x y : E) :
    coordinates b r x=coordinates b r y ↔ W.starProjection x=W.starProjection y := by
  classical
  constructor
  · intro h
    apply b.repr.injective
    ext j
    by_cases hj : j∈r
    · obtain ⟨i,rfl⟩ := (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem r j).mpr hj
      have he := (coordinates_projection W b r hr x).trans
        (h.trans (coordinates_projection W b r hr y).symm)
      exact congrArg (fun z : EuclideanSpace ℝ (Fin p) => z i) he
    · rw [hz _ (W.starProjection_apply_mem x) _ hj,hz _ (W.starProjection_apply_mem y) _ hj]
  · intro h
    rw [←coordinates_projection W b r hr x,←coordinates_projection W b r hr y,h]
end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.ProductBasis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
lemma blockMap_basis_inl (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V) (i : ι) :
    blockMap U V h bU bV (EuclideanSpace.basisFun (ι⊕κ) ℝ (Sum.inl i))=bU i := by
  classical
  rw [blockMap_apply]
  have he : EuclideanSpace.sumEquivProd (EuclideanSpace.basisFun (ι⊕κ) ℝ (Sum.inl i))=
      (EuclideanSpace.basisFun ι ℝ i,0) := by
    ext j <;> simp [EuclideanSpace.basisFun_apply,EuclideanSpace.sumEquivProd]
  rw [he]
  simp only [map_zero,Submodule.coe_zero,add_zero]
  exact congrArg Subtype.val (bU.repr.symm_apply_eq.mpr (bU.repr_self i).symm)

lemma blockMap_basis_inr (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V) (i : κ) :
    blockMap U V h bU bV (EuclideanSpace.basisFun (ι⊕κ) ℝ (Sum.inr i))=bV i := by
  classical
  rw [blockMap_apply]
  have he : EuclideanSpace.sumEquivProd (EuclideanSpace.basisFun (ι⊕κ) ℝ (Sum.inr i))=
      (0,EuclideanSpace.basisFun κ ℝ i) := by
    ext j <;> simp [EuclideanSpace.basisFun_apply,EuclideanSpace.sumEquivProd]
  rw [he]
  simp only [map_zero,Submodule.coe_zero,zero_add]
  exact congrArg Subtype.val (bV.repr.symm_apply_eq.mpr (bV.repr_self i).symm)
end SmoothObstruction.ProductBasis

namespace SmoothObstruction.EndpointFrame
open Set Matrix ProductBasis ExteriorStability
variable {d p q : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

lemma joint_hasFDerivAt (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    {f g : E → E} {x : E} {A B : E →L[ℝ] E}
    (hf : HasFDerivAt f A x) (hg : HasFDerivAt g B x) :
    HasFDerivAt (joint bF bP rF rP f g) (jointLinear bF bP rF rP A B) x := by
  exact (EuclideanSpace.sumEquivProd.symm.hasFDerivAt).comp x
    (((coordinates bF rF).hasFDerivAt.comp x hf).prodMk
      ((coordinates bP rP).hasFDerivAt.comp x hg))

lemma joint_matrix (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis (Fin p) ℝ U) (bV : OrthonormalBasis (Fin q) ℝ V)
    (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    (A B : E →L[ℝ] E) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin p ⊕ Fin q) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin p ⊕ Fin q) ℝ).toBasis
      ((jointLinear bF bP rF rP A B).comp (blockMap U V h bU bV).toContinuousLinearMap).toLinearMap=
    Matrix.fromBlocks (endpointMatrix bF p rF A (fun i => (bU i:E)))
      (endpointMatrix bF p rF A (fun i => (bV i:E)))
      (endpointMatrix bP q rP B (fun i => (bU i:E)))
      (endpointMatrix bP q rP B (fun i => (bV i:E))) := by
  have hL (j : Fin p) : blockMap U V h bU bV (EuclideanSpace.single (Sum.inl j) 1)=(bU j:E) :=
    by simpa only [EuclideanSpace.basisFun_apply] using blockMap_basis_inl U V h bU bV j
  have hR (j : Fin q) : blockMap U V h bU bV (EuclideanSpace.single (Sum.inr j) 1)=(bV j:E) :=
    by simpa only [EuclideanSpace.basisFun_apply] using blockMap_basis_inr U V h bU bV j
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [LinearMap.toMatrix_apply,jointLinear,hL,hR,
      endpointMatrix,EuclideanSpace.sumEquivProd]

/-- The determinant of the actual joint endpoint differential in the common
product input coordinates is exactly the block determinant estimated by the
maximal-minor algebra. No leading volume lower floor is asserted. -/
lemma joint_det (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis (Fin p) ℝ U) (bV : OrthonormalBasis (Fin q) ℝ V)
    (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    (A B : E →L[ℝ] E) :
    ((jointLinear bF bP rF rP A B).comp (blockMap U V h bU bV).toContinuousLinearMap).det=
    (Matrix.fromBlocks (endpointMatrix bF p rF A (fun i => (bU i:E)))
      (endpointMatrix bF p rF A (fun i => (bV i:E)))
      (endpointMatrix bP q rP B (fun i => (bU i:E)))
      (endpointMatrix bP q rP B (fun i => (bV i:E)))).det := by
  rw [←joint_matrix U V h bU bV bF bP rF rP A B,LinearMap.det_toMatrix]
end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Smooth local solution of all four endpoint equations, with its ACTUAL
nondegenerate derivative. This statement is insensitive to zero-dimensional
endpoint groups and keeps all four endpoint derivatives separate. -/
theorem local_branch (f₀ f₁ g₀ g₁ : E → E) (x y z w : E)
    (A B C D : E ≃L[ℝ] E) (σ : (E×E) ≃L[ℝ] (E×E))
    (hf₀ : ContDiffAt ℝ ∞ f₀ x) (hf₁ : ContDiffAt ℝ ∞ f₁ y)
    (hg₀ : ContDiffAt ℝ ∞ g₀ z) (hg₁ : ContDiffAt ℝ ∞ g₁ w)
    (hA : HasFDerivAt f₀ (A : E →L[ℝ] E) x)
    (hB : HasFDerivAt f₁ (B : E →L[ℝ] E) y)
    (hC : HasFDerivAt g₀ (C : E →L[ℝ] E) z)
    (hD : HasFDerivAt g₁ (D : E →L[ℝ] E) w)
    (heq : Prod.map g₀ g₁ (z,w)=σ (Prod.map f₀ f₁ (x,y))) :
    ∃ Φ : E×E → E×E, Φ (x,y)=(z,w) ∧ ContDiffAt ℝ ∞ Φ (x,y) ∧
      HasFDerivAt Φ (derivative A B C D σ : (E×E) →L[ℝ] (E×E)) (x,y) ∧
      ∀ᶠ u in 𝓝 (x,y),Prod.map g₀ g₁ (Φ u)=σ (Prod.map f₀ f₁ u) := by
  let F := Prod.map f₀ f₁
  let G := Prod.map g₀ g₁
  have hF : ContDiffAt ℝ ∞ F (x,y) := hf₀.prodMap hf₁
  have hG : ContDiffAt ℝ ∞ G (z,w) := hg₀.prodMap hg₁
  have hFd : HasFDerivAt F (A.prodCongr B : (E×E) →L[ℝ] (E×E)) (x,y) :=
    hA.prodMap (x,y) hB
  have hGd : HasFDerivAt G (C.prodCongr D : (E×E) →L[ℝ] (E×E)) (z,w) :=
    hC.prodMap (z,w) hD
  have hn : (∞ : ℕ∞ω)≠0 := by simp
  let ψ := hG.localInverse hGd hn
  let Φ := ψ ∘ σ ∘ F
  have hψ : ContDiffAt ℝ ∞ ψ (G (z,w)) := hG.to_localInverse hGd hn
  have hψd : HasFDerivAt ψ ((C.prodCongr D).symm : (E×E) →L[ℝ] (E×E)) (G (z,w)) :=
    (hG.hasStrictFDerivAt' hGd hn).to_localInverse.hasFDerivAt
  have hmid : ContDiffAt ℝ ∞ (σ ∘ F) (x,y) := σ.contDiff.contDiffAt.comp (x,y) hF
  have hmidD := σ.hasFDerivAt.comp (x,y) hFd
  have hpt : G (z,w)=(σ ∘ F) (x,y) := heq
  refine ⟨Φ,?_,?_,?_,?_⟩
  · change ψ ((σ ∘ F) (x,y))=(z,w)
    rw [←hpt]
    exact hG.localInverse_apply_image hGd hn
  · rw [hpt] at hψ
    exact hψ.comp (x,y) hmid
  · rw [hpt] at hψd
    exact hψd.comp (x,y) hmidD
  · have hh := (hG.hasStrictFDerivAt' hGd hn).eventually_right_inverse
    rw [hpt] at hh
    exact hmid.continuousAt.tendsto.eventually hh

section Determinant
variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
lemma derivative_det (A B C D : E ≃L[ℝ] E)
    (σ : (E×E) ≃L[ℝ] (E×E)) :
    (derivative A B C D σ : (E×E) →L[ℝ] (E×E)).det =
      (σ : (E×E) →L[ℝ] (E×E)).det * (A : E →L[ℝ] E).det *
        (B : E →L[ℝ] E).det / ((C : E →L[ℝ] E).det*(D : E →L[ℝ] E).det) := by
  change LinearMap.det (((C.prodCongr D).symm : (E×E) →L[ℝ] (E×E)).toLinearMap.comp
    ((σ : (E×E) →L[ℝ] (E×E)).toLinearMap.comp
      ((A.prodCongr B : (E×E) →L[ℝ] (E×E)).toLinearMap)))=_
  rw [LinearMap.det_comp,LinearMap.det_comp]
  have hinv := LinearEquiv.det_coe_symm (C.prodCongr D).toLinearEquiv
  change ((C.prodCongr D).symm : (E×E) →L[ℝ] (E×E)).det =
    ((C.prodCongr D : (E×E) →L[ℝ] (E×E)).det)⁻¹ at hinv
  change ((C.prodCongr D).symm : (E×E) →L[ℝ] (E×E)).det *
    ((σ : (E×E) →L[ℝ] (E×E)).det *
      ((A.prodCongr B : (E×E) →L[ℝ] (E×E)).det))=_
  rw [hinv]
  change ((C : E →L[ℝ] E).toLinearMap.prodMap (D : E →L[ℝ] E).toLinearMap).det⁻¹ *
    ((σ : (E×E) →L[ℝ] (E×E)).det *
      ((A : E →L[ℝ] E).toLinearMap.prodMap (B : E →L[ℝ] E).toLinearMap).det)=_
  rw [LinearMap.det_prodMap,LinearMap.det_prodMap]
  ring

omit [CompleteSpace E] in
lemma derivative_abs_det (A B C D : E ≃L[ℝ] E)
    (σ : (E×E) ≃L[ℝ] (E×E)) (hσ : |(σ : (E×E) →L[ℝ] (E×E)).det|=1) :
    |(derivative A B C D σ : (E×E) →L[ℝ] (E×E)).det| =
      |(A : E →L[ℝ] E).det| * |(B : E →L[ℝ] E).det| /
        (|(C : E →L[ℝ] E).det| * |(D : E →L[ℝ] E).det|) := by
  rw [derivative_det,abs_div,abs_mul,abs_mul,abs_mul,hσ,one_mul]
end Determinant

end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.JacobianBounds

lemma abs_ratio_bounds {a b : ℝ} (hb : b≠0) (h : |a/b-1|≤(1/10:ℝ)) :
    (9/10:ℝ)*|b|≤|a| ∧ |a|≤(11/10:ℝ)*|b| := by
  have ha : abs (abs (a/b) - 1)≤(1/10:ℝ) := by
    simpa only [abs_one] using (abs_abs_sub_abs_le_abs_sub (a/b) 1).trans h
  have hlo : (9/10:ℝ)≤|a/b| := by linarith [(abs_le.mp ha).1]
  have hup : |a/b|≤(11/10:ℝ) := by linarith [(abs_le.mp ha).2]
  rw [abs_div] at hlo hup
  exact ⟨(le_div_iff₀ (abs_pos.mpr hb)).mp hlo,(div_le_iff₀ (abs_pos.mpr hb)).mp hup⟩

/-- Four relative maximal-minor errors cancel the actual leading volumes
individually. Rates of the two input orbits never need to be compared. -/
theorem four_cancel
    (a b c d u v w z : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0 < c) (hd : 0<d)
    (hu : |u/(a*b)-1|≤(1/10:ℝ)) (hv : |v/(c*d)-1|≤(1/10:ℝ))
    (hw : |w/(a*d)-1|≤(1/10:ℝ)) (hz : |z/(c*b)-1|≤(1/10:ℝ)) :
    w≠0 ∧ z≠0 ∧ (81/121:ℝ)≤|u| *|v| /(|w| *|z|) ∧
      |u| *|v| /(|w| *|z|)≤(121/81:ℝ) := by
  have hU := abs_ratio_bounds (mul_ne_zero ha.ne' hb.ne') hu
  have hV := abs_ratio_bounds (mul_ne_zero hc.ne' hd.ne') hv
  have hW := abs_ratio_bounds (mul_ne_zero ha.ne' hd.ne') hw
  have hZ := abs_ratio_bounds (mul_ne_zero hc.ne' hb.ne') hz
  simp only [abs_of_pos (mul_pos ha hb)] at hU
  simp only [abs_of_pos (mul_pos hc hd)] at hV
  simp only [abs_of_pos (mul_pos ha hd)] at hW
  simp only [abs_of_pos (mul_pos hc hb)] at hZ
  have hwpos : 0 < |w| := lt_of_lt_of_le (by positivity) hW.1
  have hzpos : 0 < |z| := lt_of_lt_of_le (by positivity) hZ.1
  refine ⟨abs_pos.mp hwpos,abs_pos.mp hzpos,?_,?_⟩
  · apply (le_div_iff₀ (mul_pos hwpos hzpos)).mpr
    have hUV := mul_le_mul hU.1 hV.1 (by positivity) (abs_nonneg u)
    have hWZ := mul_le_mul hW.2 hZ.2 (abs_nonneg z) (by positivity)
    nlinarith
  · apply (div_le_iff₀ (mul_pos hwpos hzpos)).mpr
    have hUV := mul_le_mul hU.2 hV.2 (abs_nonneg v) (by positivity)
    have hWZ := mul_le_mul hW.1 hZ.1 (by positivity) (abs_nonneg w)
    nlinarith

end SmoothObstruction.JacobianBounds

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Construct the true smooth branch from four *absolute*, relative
endpoint-minor estimates. None of the four endpoint derivatives is
assumed invertible, and no leading volume is bounded away from zero. -/
theorem controlled_branch (f₀ f₁ g₀ g₁ : E → E) (x y z w : E)
    (A B C D : E →L[ℝ] E) (σ : (E×E) ≃L[ℝ] (E×E))
    (hf₀ : ContDiffAt ℝ ∞ f₀ x) (hf₁ : ContDiffAt ℝ ∞ f₁ y)
    (hg₀ : ContDiffAt ℝ ∞ g₀ z) (hg₁ : ContDiffAt ℝ ∞ g₁ w)
    (hA : HasFDerivAt f₀ A x) (hB : HasFDerivAt f₁ B y)
    (hC : HasFDerivAt g₀ C z) (hD : HasFDerivAt g₁ D w)
    (heq : Prod.map g₀ g₁ (z,w)=σ (Prod.map f₀ f₁ (x,y)))
    (hσ : |(σ : (E×E) →L[ℝ] (E×E)).det|=1)
    (a b c d : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0 < c) (hd : 0<d)
    (haA : |(|A.det| / (a*b)-1)|≤(1/10:ℝ))
    (hbB : |(|B.det| / (c*d)-1)|≤(1/10:ℝ))
    (hcC : |(|C.det| / (a*d)-1)|≤(1/10:ℝ))
    (hdD : |(|D.det| / (c*b)-1)|≤(1/10:ℝ)) :
    ∃ Φ : E×E → E×E,Φ (x,y)=(z,w) ∧ ContDiffAt ℝ ∞ Φ (x,y) ∧
      (81/121:ℝ) ≤ |(fderiv ℝ Φ (x,y)).det| ∧
      |(fderiv ℝ Φ (x,y)).det| ≤ (121/81:ℝ) ∧
      ∀ᶠ u in 𝓝 (x,y),Prod.map g₀ g₁ (Φ u)=σ (Prod.map f₀ f₁ u) := by
  have hAn : A.det≠0 := by intro h; norm_num [h] at haA
  have hBn : B.det≠0 := by intro h; norm_num [h] at hbB
  have hCn : C.det≠0 := by intro h; norm_num [h] at hcC
  have hDn : D.det≠0 := by intro h; norm_num [h] at hdD
  obtain ⟨Φ,hpt,hcd,hder,he⟩ := local_branch f₀ f₁ g₀ g₁ x y z w
    (equiv_of_det A hAn) (equiv_of_det B hBn) (equiv_of_det C hCn) (equiv_of_det D hDn) σ
    hf₀ hf₁ hg₀ hg₁ (by simpa only [equiv_of_det_coe] using hA)
    (by simpa only [equiv_of_det_coe] using hB)
    (by simpa only [equiv_of_det_coe] using hC)
    (by simpa only [equiv_of_det_coe] using hD) heq
  have hdet : |(fderiv ℝ Φ (x,y)).det|=|A.det| * |B.det| / (|C.det| * |D.det|) := by
    rw [hder.fderiv,derivative_abs_det _ _ _ _ σ hσ]
    simp only [equiv_of_det_coe]
  have hbound := (JacobianBounds.four_cancel a b c d |A.det| |B.det| |C.det| |D.det|
    ha hb hc hd haA hbB hcC hdD).2.2
  simp only [abs_abs] at hbound
  exact ⟨Φ,hpt,hcd,hdet.symm ▸ hbound.1,hdet.symm ▸ hbound.2,he⟩
end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {p q : ℕ}
local notation "F" => EuclideanSpace ℝ (Fin p ⊕ Fin q)

lemma sumExchange_abs_det : |(sumExchange (p:=p) (q:=q) : (F×F) →L[ℝ] (F×F)).det|=1 := by
  let e := sumExchange (p:=p) (q:=q)
  have he : e.symm=e := by
    ext x i <;> rfl
  have hh := e.toLinearEquiv.det_mul_det_symm
  change (e : (F×F) →L[ℝ] (F×F)).det * (e.symm : (F×F) →L[ℝ] (F×F)).det=1 at hh
  rw [he] at hh
  have hab := congrArg abs hh
  rw [abs_mul,abs_one] at hab
  nlinarith [abs_nonneg ((e : (F×F) →L[ℝ] (F×F)).det)]

/-- Signed relative determinants give precisely the absolute, relative
volume estimates required by the actual inverse-function branch. -/
lemma absolute_relative {u a b ε : ℝ} (h : |u/(a*b)-1|≤ε) :
    |(|u|/(|a| * |b|))-1|≤ε := by
  have hh := (abs_abs_sub_abs_le_abs_sub (u/(a*b)) 1).trans h
  simpa only [abs_div,abs_mul,abs_one] using hh

end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

lemma linear_conjugate_det (L : E ≃L[ℝ] F) (A : E →L[ℝ] E) :
    (L.toContinuousLinearMap.comp (A.comp L.symm.toContinuousLinearMap)).det=A.det := by
  let b := Module.finBasis ℝ F
  let c := b.map L.symm.toLinearEquiv
  change LinearMap.det ((L.toContinuousLinearMap.comp (A.comp L.symm.toContinuousLinearMap)).toLinearMap)=LinearMap.det A.toLinearMap
  rw [←LinearMap.det_toMatrix b,←LinearMap.det_toMatrix c]
  congr 1

variable [CompleteSpace F] [FiniteDimensional ℝ E]
/-- The controlled endpoint branch in the original physical coordinates.
The same (possibly badly conditioned) starting basis is used for all four
endpoint maps, and cancels exactly from the joint Jacobian. -/
theorem physical_controlled_branch (L : F ≃L[ℝ] E)
    (f₀ f₁ g₀ g₁ : E → F) (x y z w : E)
    (A B C D : E →L[ℝ] F) (σ : (F×F) ≃L[ℝ] (F×F))
    (hf₀ : ContDiffAt ℝ ∞ f₀ x) (hf₁ : ContDiffAt ℝ ∞ f₁ y)
    (hg₀ : ContDiffAt ℝ ∞ g₀ z) (hg₁ : ContDiffAt ℝ ∞ g₁ w)
    (hA : HasFDerivAt f₀ A x) (hB : HasFDerivAt f₁ B y)
    (hC : HasFDerivAt g₀ C z) (hD : HasFDerivAt g₁ D w)
    (heq : Prod.map g₀ g₁ (z,w)=σ (Prod.map f₀ f₁ (x,y)))
    (hσ : |(σ : (F×F) →L[ℝ] (F×F)).det|=1)
    (a b c d : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0 < c) (hd : 0<d)
    (haA : |(|(A.comp L.toContinuousLinearMap).det| / (a*b)-1)|≤(1/10:ℝ))
    (hbB : |(|(B.comp L.toContinuousLinearMap).det| / (c*d)-1)|≤(1/10:ℝ))
    (hcC : |(|(C.comp L.toContinuousLinearMap).det| / (a*d)-1)|≤(1/10:ℝ))
    (hdD : |(|(D.comp L.toContinuousLinearMap).det| / (c*b)-1)|≤(1/10:ℝ)) :
    ∃ Φ : E×E → E×E,Φ (x,y)=(z,w) ∧ ContDiffAt ℝ ∞ Φ (x,y) ∧
      (81/121:ℝ) ≤ |(fderiv ℝ Φ (x,y)).det| ∧
      |(fderiv ℝ Φ (x,y)).det| ≤ (121/81:ℝ) ∧
      ∀ᶠ u in 𝓝 (x,y),Prod.map g₀ g₁ (Φ u)=σ (Prod.map f₀ f₁ u) := by
  let T := L.prodCongr L
  have cd {f : E → F} {u : E} (h : ContDiffAt ℝ ∞ f u) :
      ContDiffAt ℝ ∞ (f ∘ L) (L.symm u) := by
    have h' : ContDiffAt ℝ ∞ f (L (L.symm u)) := by simpa using h
    exact h'.comp _ L.contDiff.contDiffAt
  have der {f : E → F} {u : E} {K : E →L[ℝ] F} (h : HasFDerivAt f K u) :
      HasFDerivAt (f ∘ L) (K.comp L.toContinuousLinearMap) (L.symm u) := by
    have h' : HasFDerivAt f K (L (L.symm u)) := by simpa using h
    exact h'.comp _ L.hasFDerivAt
  obtain ⟨ψ,hpt,hcd,hlo,hup,he⟩ := controlled_branch (f₀ ∘ L) (f₁ ∘ L)
    (g₀ ∘ L) (g₁ ∘ L) (L.symm x) (L.symm y) (L.symm z) (L.symm w)
    (A.comp L.toContinuousLinearMap) (B.comp L.toContinuousLinearMap)
    (C.comp L.toContinuousLinearMap) (D.comp L.toContinuousLinearMap) σ
    (cd hf₀) (cd hf₁) (cd hg₀) (cd hg₁) (der hA) (der hB) (der hC) (der hD)
    (by simpa only [Prod.map_apply,Function.comp_apply,L.apply_symm_apply] using heq)
    hσ a b c d ha hb hc hd haA hbB hcC hdD
  let Φ := T ∘ ψ ∘ T.symm
  have hψd := (hcd.differentiableAt (by norm_num)).hasFDerivAt
  have hΦcd : ContDiffAt ℝ ∞ Φ (x,y) :=
    T.contDiff.contDiffAt.comp (x,y) (hcd.comp (x,y) T.symm.contDiff.contDiffAt)
  have hΦd : HasFDerivAt Φ
      (T.toContinuousLinearMap.comp ((fderiv ℝ ψ (L.symm x,L.symm y)).comp T.symm.toContinuousLinearMap))
      (x,y) := T.hasFDerivAt.comp (x,y) (hψd.comp (x,y) T.symm.hasFDerivAt)
  have hdet : (fderiv ℝ Φ (x,y)).det=(fderiv ℝ ψ (L.symm x,L.symm y)).det := by
    rw [hΦd.fderiv]
    exact linear_conjugate_det T _
  refine ⟨Φ,?_,hΦcd,hdet.symm ▸ hlo,hdet.symm ▸ hup,?_⟩
  · change T (ψ (L.symm x,L.symm y))=(z,w)
    rw [hpt]
    exact T.apply_symm_apply (z,w)
  · have hT : ContinuousAt T.symm (x,y) := T.symm.continuousAt
    have hh := hT.tendsto.eventually he
    filter_upwards [hh] with u hu
    simpa [Φ,T,Function.comp_def,Prod.map] using hu
end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.EndpointFrame
open Set Matrix ProductBasis ExteriorStability
open scoped ContDiff
variable {d p q : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

lemma joint_contDiffAt (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    {f g : E → E} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (joint bF bP rF rP f g) x := by
  exact EuclideanSpace.sumEquivProd.symm.contDiff.contDiffAt.comp x
    (((coordinates bF rF).contDiff.contDiffAt.comp x hf).prodMk
      ((coordinates bP rP).contDiff.contDiffAt.comp x hg))

/-- The true joint endpoint differential inherits the four-volume relative
bound from the genuine selected endpoint minors. The modulus is chosen only
from the dimensions, and permits either group to be empty. -/
theorem joint_controlled_det : ∃ δ : ℝ,0<δ ∧
    ∀ (U V : Submodule ℝ E) (h : IsCompl U V)
      (bU : OrthonormalBasis (Fin p) ℝ U) (bV : OrthonormalBasis (Fin q) ℝ V)
      (bF bP : OrthonormalBasis (Fin d) ℝ E)
      (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
      (f g : E → E) (x : E) (A₀ : Matrix (Fin p) (Fin p) ℝ)
      (D₀ : Matrix (Fin q) (Fin q) ℝ),
      DifferentiableAt ℝ f x → DifferentiableAt ℝ g x →
      A₀.det≠0 → D₀.det≠0 →
      let A := endpointMatrix bF p rF (fderiv ℝ f x) (fun i => (bU i:E))
      let B := endpointMatrix bF p rF (fderiv ℝ f x) (fun i => (bV i:E))
      let C := endpointMatrix bP q rP (fderiv ℝ g x) (fun i => (bU i:E))
      let D := endpointMatrix bP q rP (fderiv ℝ g x) (fun i => (bV i:E))
      |A.det/A₀.det-1|≤(1/100:ℝ) → |D.det/D₀.det-1|≤(1/100:ℝ) →
      (∀ i j,|(A⁻¹*B) i j|≤δ) → (∀ i j,|(D⁻¹*C) i j|≤δ) →
      |(|((fderiv ℝ (joint bF bP rF rP f g) x).comp
        (blockMap U V h bU bV).toContinuousLinearMap).det| /
        (|A₀.det| * |D₀.det|)-1)|≤(1/10:ℝ) := by
  obtain ⟨δ,hδ,hbound⟩ := MinorGraph.joint_relative_transfer (m:=Fin p) (n:=Fin q)
  refine ⟨δ,hδ,?_⟩
  intro U V h bU bV bF bP rF rP f g x A₀ D₀ hf hg hA₀ hD₀ A B C D hA hD hAB hDC
  have hder := joint_hasFDerivAt bF bP rF rP hf.hasFDerivAt hg.hasFDerivAt
  rw [hder.fderiv,joint_det U V h bU bV bF bP rF rP]
  exact EndpointBranch.absolute_relative (hbound A₀ D₀ A B C D hA₀ hD₀ hA hD hAB hDC)
end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.EndpointFrame
open Set Matrix ProductBasis ExteriorStability Filter Topology
open scoped ContDiff
variable {d p q : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin p ⊕ Fin q)

/-- Four actual endpoint maps produce one smooth two-point exchange germ.
This is a relative determinant statement at all ranks, in the original
physical coordinates. The common nonorthogonal input-basis determinant
cancels, including when either block has rank zero. -/
theorem four_endpoint_branch : ∃ δ : ℝ,0<δ ∧
    ∀ (U V : Submodule ℝ E) (_ : IsCompl U V)
      (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V)
      (b₀ b₁ c₀ c₁ : OrthonormalBasis (Fin d) ℝ E)
      (r₀ r₁ : powersetCard (Fin d) p) (s₀ s₁ : powersetCard (Fin d) q)
      (f₀ f₁ g₀ g₁ : E → E) (x y z w : E)
      (A₀ A₁ : Matrix (Fin p) (Fin p) ℝ) (D₀ D₁ : Matrix (Fin q) (Fin q) ℝ),
      GoodEndpoint δ b₀ r₀ (fun i => (u i:E)) (fun i => (v i:E)) f₀ x A₀ →
      GoodEndpoint δ b₀ r₀ (fun i => (u i:E)) (fun i => (v i:E)) f₀ z A₀ →
      GoodEndpoint δ b₁ r₁ (fun i => (u i:E)) (fun i => (v i:E)) f₁ y A₁ →
      GoodEndpoint δ b₁ r₁ (fun i => (u i:E)) (fun i => (v i:E)) f₁ w A₁ →
      GoodEndpoint δ c₀ s₀ (fun i => (v i:E)) (fun i => (u i:E)) g₀ x D₀ →
      GoodEndpoint δ c₀ s₀ (fun i => (v i:E)) (fun i => (u i:E)) g₀ w D₀ →
      GoodEndpoint δ c₁ s₁ (fun i => (v i:E)) (fun i => (u i:E)) g₁ y D₁ →
      GoodEndpoint δ c₁ s₁ (fun i => (v i:E)) (fun i => (u i:E)) g₁ z D₁ →
      coordinates b₀ r₀ (f₀ z)=coordinates b₀ r₀ (f₀ x) →
      coordinates b₁ r₁ (f₁ w)=coordinates b₁ r₁ (f₁ y) →
      coordinates c₀ s₀ (g₀ w)=coordinates c₀ s₀ (g₀ x) →
      coordinates c₁ s₁ (g₁ z)=coordinates c₁ s₁ (g₁ y) →
      ∃ Φ : E×E → E×E,Φ (x,y)=(z,w) ∧ ContDiffAt ℝ ∞ Φ (x,y) ∧
        (81/121:ℝ)≤|(fderiv ℝ Φ (x,y)).det| ∧
        |(fderiv ℝ Φ (x,y)).det|≤(121/81:ℝ) ∧
        ∀ᶠ t in 𝓝 (x,y),
          coordinates b₀ r₀ (f₀ (Φ t).1)=coordinates b₀ r₀ (f₀ t.1) ∧
          coordinates b₁ r₁ (f₁ (Φ t).2)=coordinates b₁ r₁ (f₁ t.2) ∧
          coordinates c₀ s₀ (g₀ (Φ t).2)=coordinates c₀ s₀ (g₀ t.1) ∧
          coordinates c₁ s₁ (g₁ (Φ t).1)=coordinates c₁ s₁ (g₁ t.2) := by
  obtain ⟨δ,hδ,hdet⟩ := joint_controlled_det (d:=d) (p:=p) (q:=q)
  refine ⟨δ,hδ,?_⟩
  intro U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ f₀ f₁ g₀ g₁ x y z w A₀ A₁ D₀ D₁
    hxF hzF hyF hwF hxP hwP hyP hzP heF heF' heP heP'
  let F₀ := joint b₀ c₀ r₀ s₀ f₀ g₀
  let F₁ := joint b₁ c₁ r₁ s₁ f₁ g₁
  let G₀ := joint b₀ c₁ r₀ s₁ f₀ g₁
  let G₁ := joint b₁ c₀ r₁ s₀ f₁ g₀
  have hd {b c : OrthonormalBasis (Fin d) ℝ E}
      {r : powersetCard (Fin d) p} {s : powersetCard (Fin d) q}
      {f g : E → E} {t : E} {A : Matrix (Fin p) (Fin p) ℝ}
      {D : Matrix (Fin q) (Fin q) ℝ}
      (hf : GoodEndpoint δ b r (fun i => (u i:E)) (fun i => (v i:E)) f t A)
      (hg : GoodEndpoint δ c s (fun i => (v i:E)) (fun i => (u i:E)) g t D) :=
    hdet U V h u v b c r s f g t A D
      (hf.1.differentiableAt (by simp)) (hg.1.differentiableAt (by simp))
      hf.2.1 hg.2.1 hf.2.2.1 hg.2.2.1 hf.2.2.2 hg.2.2.2
  have hF₀ := joint_contDiffAt b₀ c₀ r₀ s₀ hxF.1 hxP.1
  have hF₁ := joint_contDiffAt b₁ c₁ r₁ s₁ hyF.1 hyP.1
  have hG₀ := joint_contDiffAt b₀ c₁ r₀ s₁ hzF.1 hzP.1
  have hG₁ := joint_contDiffAt b₁ c₀ r₁ s₀ hwF.1 hwP.1
  have he : Prod.map G₀ G₁ (z,w)=EndpointBranch.sumExchange (Prod.map F₀ F₁ (x,y)) := by
    ext i <;> cases i <;>
      simp [F₀,F₁,G₀,G₁,joint,EndpointBranch.sumExchange,EndpointBranch.exchange,
        EuclideanSpace.sumEquivProd,heF,heF',heP,heP']
  obtain ⟨Φ,hΦ,hcd,hlo,hup,heq⟩ := EndpointBranch.physical_controlled_branch
    (blockMap U V h u v) F₀ F₁ G₀ G₁ x y z w
    (fderiv ℝ F₀ x) (fderiv ℝ F₁ y) (fderiv ℝ G₀ z) (fderiv ℝ G₁ w)
    EndpointBranch.sumExchange hF₀ hF₁ hG₀ hG₁
    (hF₀.differentiableAt (by simp)).hasFDerivAt
    (hF₁.differentiableAt (by simp)).hasFDerivAt
    (hG₀.differentiableAt (by simp)).hasFDerivAt
    (hG₁.differentiableAt (by simp)).hasFDerivAt he EndpointBranch.sumExchange_abs_det
    |A₀.det| |D₀.det| |A₁.det| |D₁.det|
    (abs_pos.mpr hxF.2.1) (abs_pos.mpr hxP.2.1)
    (abs_pos.mpr hyF.2.1) (abs_pos.mpr hyP.2.1)
    (hd hxF hxP) (hd hyF hyP) (hd hzF hzP) (hd hwF hwP)
  refine ⟨Φ,hΦ,hcd,hlo,hup,?_⟩
  filter_upwards [heq] with t ht
  have h₀ := congrArg (fun t : F×F => EuclideanSpace.sumEquivProd t.1) ht
  have h₁ := congrArg (fun t : F×F => EuclideanSpace.sumEquivProd t.2) ht
  simp only [G₀,G₁,F₀,F₁,EndpointBranch.sumExchange,
    ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.prodCongr_apply] at h₀ h₁
  exact ⟨congrArg Prod.fst h₀,congrArg Prod.fst h₁,congrArg Prod.snd h₁,congrArg Prod.snd h₀⟩
end SmoothObstruction.EndpointFrame

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
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Uniform comparison of actual chart displacements on the retained interior
balls. This is a consequence of the identity diffeomorphism's genuine smooth
coordinate maps, not an assumed Riemannian/Lipschitz metric. -/
theorem uniform_chart_transfer (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1≤C ∧ ∀ (i j : ι) (x y : M) (δ : ℝ),
      x∈K i → x∈K j → 0≤δ → δ ≤ r →
      closedBall ((extChartAt I (a i)) x) δ⊆interior (range I) →
      y∈(chartAt H (a i)).source →
      ‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖≤δ →
      y∈(chartAt H (a j)).source ∧
      ‖(extChartAt I (a j)) y-(extChartAt I (a j)) x‖≤
        C*‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖ := by
  let Id : Diffeomorph I I M M ∞ := Diffeomorph.refl I M ∞
  obtain ⟨r,C,hr,hC,ht⟩ := actual_tube_data I hclosed Id a K hK hKU
  refine ⟨r,C,hr,hC,fun i j x y δ hxi hxj hδ hδr hsafe hyi hxy => ?_⟩
  have hd := ht i j x δ hxi hxj hδ hδr hsafe
  have hyb : (extChartAt I (a i)) y∈closedBall ((extChartAt I (a i)) x) δ :=
    mem_closedBall_iff_norm.mpr hxy
  have hyj := (hd.2.1 hyb).2
  have hiy : (extChartAt I (a i)).symm ((extChartAt I (a i)) y)=y :=
    (extChartAt I (a i)).left_inv (by simpa only [extChartAt_source] using hyi)
  have hix : (extChartAt I (a i)).symm ((extChartAt I (a i)) x)=x :=
    (extChartAt I (a i)).left_inv (by simpa only [extChartAt_source] using hKU i hxi)
  change Id ((extChartAt I (a i)).symm ((extChartAt I (a i)) y))∈(chartAt H (a j)).source at hyj
  rw [hiy] at hyj
  refine ⟨hyj,?_⟩
  have hbound := (convex_closedBall ((extChartAt I (a i)) x) δ).norm_image_sub_le_of_norm_fderiv_le
    (𝕜:=ℝ) (f:=localMap I Id (a i) (a j))
    (fun u hu => (hd.2.2 u hu).1.differentiableAt (by norm_num))
    (fun u hu => (hd.2.2 u hu).2.1) (mem_closedBall_self hδ) hyb
  simpa only [localMap,Function.comp_apply,hix,hiy,Id,Diffeomorph.coe_refl,id_eq] using hbound
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_EndpointMass
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.AtlasCores
open Set Filter Topology
variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Fintype ι]

/-- A finite closed atlas selector can only approach charts whose compact
carrier contains the limiting point. It need not be a continuous selector. -/
theorem closed_selector_germ (K : ι → Set Y) (hK : ∀ i,IsClosed (K i))
    (q : Y → ι) (hq : ∀ y,y∈K (q y)) (y : Y) :
    ∀ᶠ z in 𝓝 y,y∈K (q z) := by
  have hall : ∀ i,∀ᶠ z in 𝓝 y,q z=i → y∈K i := by
    intro i
    by_cases hy : y∈K i
    · exact Eventually.of_forall (fun _ _ => hy)
    · filter_upwards [(hK i).isOpen_compl.mem_nhds hy] with z hz he
      exact (hz (he ▸ hq z)).elim
  filter_upwards [Filter.eventually_all.mpr hall] with z hz
  exact hz (q z) rfl

/-- Local analytic branches may be checked simultaneously in finitely many
possible chart codes, without adding those codes to any global partition. -/
theorem eventually_selected (K : ι → Set Y) (hK : ∀ i,IsClosed (K i))
    (q : Y → ι) (hq : ∀ y,y∈K (q y)) (f : X → Y) (x : X)
    (hf : ContinuousAt f x) (V : ι → Set X)
    (hV : ∀ i,f x∈K i → V i∈𝓝 x) :
    ∀ᶠ u in 𝓝 x,u∈V (q (f u)) := by
  have hcodes := hf.eventually (closed_selector_germ K hK q hq (f x))
  have hall : ∀ i,∀ᶠ u in 𝓝 x,f x∈K i → u∈V i := by
    intro i
    by_cases hi : f x∈K i
    · filter_upwards [hV i hi] with u hu using fun _ => hu
    · exact Eventually.of_forall (fun _ h => (hi h).elim)
  filter_upwards [hcodes,Filter.eventually_all.mpr hall] with u hu hv
  exact hv (q (f u)) hu
end SmoothObstruction.AtlasCores

namespace SmoothObstruction.AtlasCores
open Set Filter Topology
variable {X Y E ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [Fintype ι]

/-- A smooth local branch in all possible old charts satisfies the selected
canonical tube relation on a whole relative neighborhood. No regularity of
the finite chart selector is asserted and no intermediate chart pattern is
recorded in the partition. -/
theorem selected_tube_germ (K U : ι → Set Y) (hK : ∀ i,IsClosed (K i))
    (hU : ∀ i,IsOpen (U i)) (hKU : ∀ i,K i⊆U i)
    (q : Y → ι) (hq : ∀ y,y∈K (q y))
    (φ : ι → Y → E) (hφ : ∀ i,ContinuousOn (φ i) (U i))
    (f g : X → Y) (x : X) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (δ : ℝ) (hbase : ∀ i,f x∈K i →
      g x∈U i ∧ ‖φ i (g x)-φ i (f x)‖<δ) :
    ∀ᶠ u in 𝓝 x,g u∈U (q (f u)) ∧
      ‖φ (q (f u)) (g u)-φ (q (f u)) (f u)‖≤δ := by
  apply eventually_selected K hK q hq f x hf
    (fun i => {u | g u∈U i ∧ ‖φ i (g u)-φ i (f u)‖≤δ})
  intro i hi
  have hgf := hbase i hi
  have hcf : ContinuousAt (fun u => φ i (f u)) x :=
    ((hφ i).continuousAt ((hU i).mem_nhds (hKU i hi))).comp hf
  have hcg : ContinuousAt (fun u => φ i (g u)) x :=
    ((hφ i).continuousAt ((hU i).mem_nhds hgf.1)).comp hg
  filter_upwards [hg.eventually ((hU i).mem_nhds hgf.1),
    (hcg.sub hcf).norm.eventually (gt_mem_nhds hgf.2)] with u hu hv
  exact ⟨hu,hv.le⟩

/-- Finitely many positive and negative iterate charts may be handled at
once. The number of cases affects only a local neighborhood, never the
number of partition labels or an error/mass bound. -/
theorem selected_path_tube_germ {T : Type*} [Finite T]
    (K U : ι → Set Y) (hK : ∀ i,IsClosed (K i))
    (hU : ∀ i,IsOpen (U i)) (hKU : ∀ i,K i⊆U i)
    (q : Y → ι) (hq : ∀ y,y∈K (q y))
    (φ : ι → Y → E) (hφ : ∀ i,ContinuousOn (φ i) (U i))
    (f g : T → X → Y) (x : X)
    (hf : ∀ t,ContinuousAt (f t) x) (hg : ∀ t,ContinuousAt (g t) x)
    (δ : ℝ) (hbase : ∀ t i,f t x∈K i →
      g t x∈U i ∧ ‖φ i (g t x)-φ i (f t x)‖<δ) :
    ∀ᶠ u in 𝓝 x,∀ t,g t u∈U (q (f t u)) ∧
      ‖φ (q (f t u)) (g t u)-φ (q (f t u)) (f t u)‖≤δ := by
  exact Filter.eventually_all.mpr (fun t => selected_tube_germ K U hK hU hKU
    q hq φ hφ (f t) (g t) x (hf t) (hg t) δ (hbase t))
end SmoothObstruction.AtlasCores

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- A genuine sharp orbit tube persists in all selected old charts along a
continuous local branch. Intermediate chart selectors need not be locally
constant; their finite compact cores suffice. -/
theorem actual_selected_tube_germ (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1≤C ∧
      ∀ {X T : Type*} [TopologicalSpace X] [Finite T]
        (c : M → ι) (_ : ∀ z,z∈K (c z))
        (f g : T → X → M) (x : X) (ρ δ : ℝ),
        (∀ t,ContinuousAt (f t) x) → (∀ t,ContinuousAt (g t) x) →
        0≤ρ → ρ ≤ r → C*ρ<δ →
        (∀ t,closedBall ((extChartAt I (a (c (f t x)))) (f t x)) ρ⊆interior (range I)) →
        (∀ t,g t x∈(extChartAt I (a (c (f t x)))).source ∧
          ‖(extChartAt I (a (c (f t x)))) (g t x)-
            (extChartAt I (a (c (f t x)))) (f t x)‖≤ρ) →
        ∀ᶠ u in 𝓝 x,∀ t,g t u∈(extChartAt I (a (c (f t u)))).source ∧
          ‖(extChartAt I (a (c (f t u)))) (g t u)-
            (extChartAt I (a (c (f t u)))) (f t u)‖≤δ := by
  obtain ⟨r,C,hr,hC,ht⟩ := uniform_chart_transfer I hclosed a K hK hKU
  refine ⟨r,C,hr,hC,?_⟩
  intro X T _ _ c hc f g x ρ δ hf hg hρ hρr hδ hsafe hbase
  apply AtlasCores.selected_path_tube_germ K
    (fun i => (extChartAt I (a i)).source) (fun i => (hK i).isClosed)
    (fun i => by simpa only [extChartAt_source] using (chartAt H (a i)).open_source)
    (fun i => by simpa only [extChartAt_source] using hKU i)
    c hc (fun i => extChartAt I (a i)) (fun i => continuousOn_extChartAt (I := I) (a i))
    f g x hf hg δ
  intro t i hi
  obtain ⟨hs,hb⟩ := ht (c (f t x)) i (f t x) (g t x) ρ (hc _) hi hρ hρr (hsafe t)
    (by simpa only [extChartAt_source] using (hbase t).1) (hbase t).2
  exact ⟨by simpa only [extChartAt_source] using hs,
    lt_of_le_of_lt (hb.trans (mul_le_mul_of_nonneg_left (hbase t).2 (by linarith))) hδ⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Actual orbit tubes persist locally under continuous input and output
branches without continuity of the atlas selector. -/
theorem original_tube_germ (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1≤C ∧
      ∀ {X : Type*} [TopologicalSpace X] (S : Diffeomorph I I M M ∞)
        (c : M → ι) (_ : ∀ z,z∈K (c z))
        (f g : X → M) (x : X) (n : ℕ) (ρ δ : ℝ),
        ContinuousAt f x → ContinuousAt g x →
        0≤ρ → ρ ≤ r → C*ρ<δ →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] (f x))))) (S^[t.val] (f x))) ρ
          ⊆interior (range I)) →
        originalTube I S a c (n:=n) ρ (f x) (g x) →
        ∀ᶠ u in 𝓝 x,originalTube I S a c (n:=n) δ (f u) (g u) := by
  obtain ⟨r,C,hr,hC,hgerm⟩ := actual_selected_tube_germ I hclosed a K hK hKU
  refine ⟨r,C,hr,hC,?_⟩
  intro X _ S c hc f g x n ρ δ hf hg hρ hρr hδ hsafe hbase
  have hh := hgerm c hc (fun t : Fin (n+1) => S^[t.val] ∘ f)
    (fun t : Fin (n+1) => S^[t.val] ∘ g) x ρ δ
    (fun t => (S.continuous.iterate t.val).continuousAt.comp hf)
    (fun t => (S.continuous.iterate t.val).continuousAt.comp hg)
    hρ hρr hδ hsafe (fun t => ⟨by simpa only [extChartAt_source,Function.comp_apply] using (hbase t).1,(hbase t).2⟩)
  simpa only [originalTube,Function.comp_apply,extChartAt_source] using hh
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- The authentic smooth local pair branch agrees with the canonical switch
on a relative neighborhood of the retained set. No regularity of good gauge
witnesses or intermediate chart labels enters this assertion. -/
theorem original_pair_germ (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1≤C ∧
      ∀ {X J A : Type*} [TopologicalSpace X]
        (S : Diffeomorph I I M M ∞) (c : M → ι) (_ : ∀ z,z∈K (c z))
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
        (n : ℕ) (ρ δ : ℝ) (Φ : M×M → M×M)
        (e Ψ : X → M×M) (x : X),
        ContinuousAt e x → ContinuousAt Ψ x → 0≤ρ → ρ ≤ r → C*ρ<δ →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] (e x).1)))) (S^[t.val] (e x).1)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] (e x).1)))) (S.symm^[t.val] (e x).1)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] (e x).2)))) (S^[t.val] (e x).2)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] (e x).2)))) (S.symm^[t.val] (e x).2)) ρ⊆interior (range I)) →
        originalTube I S a c (n:=n) ρ (e x).1 (Ψ x).1 →
        originalTube I S.symm a c (n:=n) ρ (e x).2 (Ψ x).1 →
        originalTube I S a c (n:=n) ρ (e x).2 (Ψ x).2 →
        originalTube I S.symm a c (n:=n) ρ (e x).1 (Ψ x).2 →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z →
            z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ᶠ t in 𝓝 x,
          originalEndpoint I S a c (n:=n) (Wf (P (e t).1,P (S^[n] (e t).1))) (e t).1 (Ψ t).1 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P (e t).2,P (S.symm^[n] (e t).2))) (e t).2 (Ψ t).1 ∧
          originalEndpoint I S a c (n:=n) (Wf (P (e t).2,P (S^[n] (e t).2))) (e t).2 (Ψ t).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P (e t).1,P (S.symm^[n] (e t).1))) (e t).1 (Ψ t).2) →
        ∀ᶠ t in 𝓝 x,(e t).1∈R → (e t).2∈R → L (e t).1=L (e t).2 → Ψ t=Φ (e t) := by
  obtain ⟨r,C,hr,hC,hgerm⟩ := original_tube_germ I hclosed a K hK hKU
  refine ⟨r,C,hr,hC,?_⟩
  intro X J A _ S c hc P L R Wf Wb n ρ δ Φ e Ψ x he hΨ hρ hρr hδ
    hsafe h1 h2 h3 h4 huniq hsecond heq
  have ht1 := hgerm S c hc (fun t => (e t).1) (fun t => (Ψ t).1) x n ρ δ
    he.fst hΨ.fst hρ hρr hδ (fun t => (hsafe t).1) h1
  have ht2 := hgerm S.symm c hc (fun t => (e t).2) (fun t => (Ψ t).1) x n ρ δ
    he.snd hΨ.fst hρ hρr hδ (fun t => (hsafe t).2.2.2) h2
  have ht3 := hgerm S c hc (fun t => (e t).2) (fun t => (Ψ t).2) x n ρ δ
    he.snd hΨ.snd hρ hρr hδ (fun t => (hsafe t).2.2.1) h3
  have ht4 := hgerm S.symm c hc (fun t => (e t).1) (fun t => (Ψ t).2) x n ρ δ
    he.fst hΨ.snd hρ hρr hδ (fun t => (hsafe t).2.1) h4
  filter_upwards [ht1,ht2,ht3,ht4,heq] with t h1t h2t h3t h4t ht
  intro hu hv hL
  apply Prod.ext
  · exact huniq _ hu _ hv hL _ h1t h2t ht.1 ht.2.1
  · obtain ⟨h1',h2',h3',h4'⟩ := hsecond _ hu _ hv hL
    exact (huniq _ hv _ hu hL.symm _ h3t h4t ht.2.2.1 ht.2.2.2).trans
      (huniq _ hv _ hu hL.symm _ h1' h2' h3' h4').symm
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ChartDensity
open Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Measurable total chart extensions agree with the authentic inverse chart
on a neighborhood of every interior coordinate point. -/
lemma inverse_germ (a : M) (u : E₀) (hu : u∈(extChartAt I a).target)
    (hi : u∈interior (range I)) :
    ContinuousAt (extChartAt I a).symm u ∧
    ∀ᶠ v in 𝓝 u,inverse I a v=(extChartAt I a).symm v ∧
      coordinates I a ((extChartAt I a).symm v)=v := by
  have ht := extChartAt_target_mem_nhdsWithin_of_mem hu
  rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hi)] at ht
  refine ⟨(continuousOn_extChartAt_symm a u hu).continuousAt ht,?_⟩
  filter_upwards [ht] with v hv
  refine ⟨inverse_eq I a v hv,?_⟩
  rw [coordinates_eq I a _ ((extChartAt I a).map_target hv)]
  exact (extChartAt I a).right_inv hv

lemma pair_inverse_germ (a : M) (u : E₀×E₀)
    (h₁ : u.1∈(extChartAt I a).target) (h₂ : u.2∈(extChartAt I a).target)
    (i₁ : u.1∈interior (range I)) (i₂ : u.2∈interior (range I)) :
    let r₀ := Prod.map (extChartAt I a).symm (extChartAt I a).symm
    let r := Prod.map (inverse I a) (inverse I a)
    let e := Prod.map (coordinates I a) (coordinates I a)
    ContinuousAt r₀ u ∧ ∀ᶠ v in 𝓝 u,r v=r₀ v ∧ e (r₀ v)=v := by
  intro r₀ r e
  obtain ⟨hc₁,hg₁⟩ := inverse_germ I a u.1 h₁ i₁
  obtain ⟨hc₂,hg₂⟩ := inverse_germ I a u.2 h₂ i₂
  refine ⟨(hc₁.comp continuousAt_fst).prodMk (hc₂.comp continuousAt_snd),?_⟩
  filter_upwards [continuousAt_fst.eventually hg₁,continuousAt_snd.eventually hg₂] with v hv₁ hv₂
  exact ⟨Prod.ext hv₁.1 hv₂.1,Prod.ext hv₁.2 hv₂.2⟩

/-- Physical agreement on retained inputs gives the exact coordinate germ
required for change of variables, despite arbitrary chart extensions away
from their sources. Only the original retained set is used. -/
theorem retained_pair_germ (a : M) (G : Set (M×M)) (Φ : M×M → M×M)
    (Ψ : E₀×E₀ → E₀×E₀) (u : E₀×E₀) (hΨ : ContinuousAt Ψ u)
    (hu₁ : u.1∈(extChartAt I a).target) (hu₂ : u.2∈(extChartAt I a).target)
    (iu₁ : u.1∈interior (range I)) (iu₂ : u.2∈interior (range I))
    (hv₁ : (Ψ u).1∈(extChartAt I a).target) (hv₂ : (Ψ u).2∈(extChartAt I a).target)
    (iv₁ : (Ψ u).1∈interior (range I)) (iv₂ : (Ψ u).2∈interior (range I))
    (hag : let r₀ := Prod.map (extChartAt I a).symm (extChartAt I a).symm
      ∀ᶠ v in 𝓝 u,r₀ v∈G → r₀ (Ψ v)=Φ (r₀ v)) :
    let e := Prod.map (coordinates I a) (coordinates I a)
    let r := Prod.map (inverse I a) (inverse I a)
    Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e r G] u] (e ∘ Φ ∘ r) := by
  intro e r
  let r₀ := Prod.map (extChartAt I a).symm (extChartAt I a).symm
  have hinput := (pair_inverse_germ I a u hu₁ hu₂ iu₁ iu₂).2
  have hout := hΨ.eventually ((pair_inverse_germ I a (Ψ u) hv₁ hv₂ iv₁ iv₂).2)
  have hall : ∀ᶠ v in 𝓝 u,v∈ChartDomination.coordinateSet e r G → Ψ v=(e ∘ Φ ∘ r) v := by
    filter_upwards [hinput,hout,hag] with v hv hv' hag'
    intro hvG
    have hrv : r v=r₀ v := hv.1
    have hg : r₀ v∈G := by rw [←hrv]; exact hvG.1
    have heq : r₀ (Ψ v)=Φ (r₀ v) := hag' hg
    change Ψ v=e (Φ (r v))
    rw [hrv,←heq]
    exact hv'.2.symm
  filter_upwards [hall.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with v hv hvG
  exact hv hvG
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d p : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    {ι A : Type*}
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Endpoint rows in a fixed old chart are exactly the canonical projected
equation when the ORIGINAL endpoint label is retained. -/
lemma original_endpoint_iff_coordinates (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) (P : M → A)
    (hPc : ∀ x y,P x=P y → c x=c y) (W : A×A → Submodule ℝ E₀)
    (a₀ x : M) (n : ℕ) (u v : E₀)
    (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W (P x,P (S^[n] x)))
    (hz : ∀ z∈W (P x,P (S^[n] x)),∀ j∉r,b.repr z j=0)
    (hP₀ : P ((extChartAt I a₀).symm u)=P x)
    (hP₁ : P (S^[n] ((extChartAt I a₀).symm u))=P (S^[n] x)) :
    originalEndpoint I S a c (n:=n)
      (W (P ((extChartAt I a₀).symm u),P (S^[n] ((extChartAt I a₀).symm u))))
      ((extChartAt I a₀).symm u) ((extChartAt I a₀).symm v) ↔
    EndpointFrame.coordinates b r
      ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm) v)=
    EndpointFrame.coordinates b r
      ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm) u) := by
  rw [originalEndpoint,hP₀,hP₁,hPc _ _ hP₁]
  exact (EndpointFrame.coordinates_eq_iff _ b r hr hz _ _).symm

/-- The four original endpoint equations of a smooth pair branch follow
from the four IFT row equations, using only the OLD starting and endpoint
labels. No intermediate orbit label is frozen or added to the cell. -/
theorem original_equations_germ {q : ℕ}
    (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι) (P : M → A)
    (hPc : ∀ x y,P x=P y → c x=c y)
    (Wf Wb : A×A → Submodule ℝ E₀) (a₀ x y : M) (n : ℕ)
    (b₀ b₁ c₀ c₁ : OrthonormalBasis (Fin d) ℝ E₀)
    (r₀ r₁ : powersetCard (Fin d) p) (s₀ s₁ : powersetCard (Fin d) q)
    (hb₀ : ∀ j∈r₀,b₀ j∈Wf (P x,P (S^[n] x)))
    (hz₀ : ∀ z∈Wf (P x,P (S^[n] x)),∀ j∉r₀,b₀.repr z j=0)
    (hb₁ : ∀ j∈r₁,b₁ j∈Wf (P y,P (S^[n] y)))
    (hz₁ : ∀ z∈Wf (P y,P (S^[n] y)),∀ j∉r₁,b₁.repr z j=0)
    (hc₀ : ∀ j∈s₀,c₀ j∈Wb (P x,P (S.symm^[n] x)))
    (hv₀ : ∀ z∈Wb (P x,P (S.symm^[n] x)),∀ j∉s₀,c₀.repr z j=0)
    (hc₁ : ∀ j∈s₁,c₁ j∈Wb (P y,P (S.symm^[n] y)))
    (hv₁ : ∀ z∈Wb (P y,P (S.symm^[n] y)),∀ j∉s₁,c₁.repr z j=0)
    (Ψ : E₀×E₀ → E₀×E₀) (u : E₀×E₀)
    (hlabels : ∀ᶠ t in 𝓝 u,
      P ((extChartAt I a₀).symm t.1)=P x ∧
      P ((extChartAt I a₀).symm t.2)=P y ∧
      P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
      P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
      P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
      P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y))
    (heq : ∀ᶠ t in 𝓝 u,
      EndpointFrame.coordinates b₀ r₀ ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm) (Ψ t).1)=
        EndpointFrame.coordinates b₀ r₀ ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm) t.1) ∧
      EndpointFrame.coordinates b₁ r₁ ((extChartAt I (a (c (S^[n] y))) ∘ S^[n] ∘ (extChartAt I a₀).symm) (Ψ t).2)=
        EndpointFrame.coordinates b₁ r₁ ((extChartAt I (a (c (S^[n] y))) ∘ S^[n] ∘ (extChartAt I a₀).symm) t.2) ∧
      EndpointFrame.coordinates c₀ s₀ ((extChartAt I (a (c (S.symm^[n] x))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm) (Ψ t).2)=
        EndpointFrame.coordinates c₀ s₀ ((extChartAt I (a (c (S.symm^[n] x))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm) t.1) ∧
      EndpointFrame.coordinates c₁ s₁ ((extChartAt I (a (c (S.symm^[n] y))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm) (Ψ t).1)=
        EndpointFrame.coordinates c₁ s₁ ((extChartAt I (a (c (S.symm^[n] y))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm) t.2)) :
    let e := Prod.map (extChartAt I a₀).symm (extChartAt I a₀).symm
    ∀ᶠ t in 𝓝 u,
      originalEndpoint I S a c (n:=n) (Wf (P (e t).1,P (S^[n] (e t).1))) (e t).1 (e (Ψ t)).1 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P (e t).2,P (S.symm^[n] (e t).2))) (e t).2 (e (Ψ t)).1 ∧
      originalEndpoint I S a c (n:=n) (Wf (P (e t).2,P (S^[n] (e t).2))) (e t).2 (e (Ψ t)).2 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P (e t).1,P (S.symm^[n] (e t).1))) (e t).1 (e (Ψ t)).2 := by
  intro e
  filter_upwards [hlabels,heq] with t ht he
  exact ⟨(original_endpoint_iff_coordinates I S a c P hPc Wf a₀ x n t.1 (Ψ t).1 b₀ r₀ hb₀ hz₀ ht.1 ht.2.2.1).mpr he.1,
    (original_endpoint_iff_coordinates I S.symm a c P hPc Wb a₀ y n t.2 (Ψ t).1 c₁ s₁ hc₁ hv₁ ht.2.1 ht.2.2.2.2.2).mpr he.2.2.2,
    (original_endpoint_iff_coordinates I S a c P hPc Wf a₀ y n t.2 (Ψ t).2 b₁ r₁ hb₁ hz₁ ht.2.1 ht.2.2.2.1).mpr he.2.1,
    (original_endpoint_iff_coordinates I S.symm a c P hPc Wb a₀ x n t.1 (Ψ t).2 c₀ s₀ hc₀ hv₀ ht.1 ht.2.2.2.2.1).mpr he.2.2.1⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric EuclideanSplitting ExteriorStability EndpointFrame
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

omit [IsManifold I ∞ M] [Fintype ι] in
lemma originalTube_self (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n : ℕ} {ρ : ℝ} (hρ : 0≤ρ) (x : M)
    (hsrc : ∀ z,z∈(chartAt H (a (c z))).source) : originalTube I S a c (n:=n) ρ x x := by
  intro t
  exact ⟨hsrc _,by simpa only [sub_self,norm_zero] using hρ⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d p q : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

omit [IsManifold I ∞ M] [Fintype ι] in
lemma originalEndpoint_coordinates (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) (n : ℕ) (a₀ x z : M) (W : Submodule ℝ E₀)
    (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (hz : ∀ z∈W,∀ j∉r,b.repr z j=0)
    (hx : x∈(extChartAt I a₀).source) (hzt : z∈(extChartAt I a₀).source)
    (he : originalEndpoint I S a c (n:=n) W x z) :
    coordinates b r ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm)
      ((extChartAt I a₀) z))=
    coordinates b r ((extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm)
      ((extChartAt I a₀) x)) := by
  simp only [Function.comp_apply,(extChartAt I a₀).left_inv hx,(extChartAt I a₀).left_inv hzt]
  exact (EndpointFrame.coordinates_eq_iff W b r hr hz _ _).mpr he

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction
lemma finite_positive_bound {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i,0<f i) :
    ∃ b : ℝ,0<b ∧ ∀ i,b≤f i := by
  classical
  by_cases h : Nonempty ι
  · let := h
    refine ⟨Finset.univ.inf' Finset.univ_nonempty f,?_,?_⟩
    · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hf i)
    · intro i; exact Finset.inf'_le _ (Finset.mem_univ i)
  · exact ⟨1,by norm_num,fun i => (h ⟨i⟩).elim⟩
end SmoothObstruction

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_GlobalSwitching
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.EndpointFrame
open Set Matrix ProductBasis ExteriorStability Filter Topology
open scoped ContDiff
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
lemma GoodEndpoint.mono {r s : ℕ} {δ ε : ℝ}
    {b : OrthonormalBasis (Fin d) ℝ E} {a : powersetCard (Fin d) r}
    {u : Fin r → E} {v : Fin s → E} {f : E → E} {x : E}
    {D₀ : Matrix (Fin r) (Fin r) ℝ} (h : GoodEndpoint δ b a u v f x D₀) (hδε : δ≤ε) :
    GoodEndpoint ε b a u v f x D₀ :=
  ⟨h.1,h.2.1,h.2.2.1,fun i j => (h.2.2.2 i j).trans hδε⟩

/-- A single endpoint minor tolerance for every possible rank in dimension d. -/
theorem four_endpoint_branch_uniform : ∃ δ : ℝ,0<δ ∧
    ∀ {p q : ℕ},p≤d → q≤d →
    ∀ (U V : Submodule ℝ E) (_ : IsCompl U V)
      (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V)
      (b₀ b₁ c₀ c₁ : OrthonormalBasis (Fin d) ℝ E)
      (r₀ r₁ : powersetCard (Fin d) p) (s₀ s₁ : powersetCard (Fin d) q)
      (f₀ f₁ g₀ g₁ : E → E) (x y z w : E)
      (A₀ A₁ : Matrix (Fin p) (Fin p) ℝ) (D₀ D₁ : Matrix (Fin q) (Fin q) ℝ),
      GoodEndpoint δ b₀ r₀ (fun i => (u i:E)) (fun i => (v i:E)) f₀ x A₀ →
      GoodEndpoint δ b₀ r₀ (fun i => (u i:E)) (fun i => (v i:E)) f₀ z A₀ →
      GoodEndpoint δ b₁ r₁ (fun i => (u i:E)) (fun i => (v i:E)) f₁ y A₁ →
      GoodEndpoint δ b₁ r₁ (fun i => (u i:E)) (fun i => (v i:E)) f₁ w A₁ →
      GoodEndpoint δ c₀ s₀ (fun i => (v i:E)) (fun i => (u i:E)) g₀ x D₀ →
      GoodEndpoint δ c₀ s₀ (fun i => (v i:E)) (fun i => (u i:E)) g₀ w D₀ →
      GoodEndpoint δ c₁ s₁ (fun i => (v i:E)) (fun i => (u i:E)) g₁ y D₁ →
      GoodEndpoint δ c₁ s₁ (fun i => (v i:E)) (fun i => (u i:E)) g₁ z D₁ →
      coordinates b₀ r₀ (f₀ z)=coordinates b₀ r₀ (f₀ x) →
      coordinates b₁ r₁ (f₁ w)=coordinates b₁ r₁ (f₁ y) →
      coordinates c₀ s₀ (g₀ w)=coordinates c₀ s₀ (g₀ x) →
      coordinates c₁ s₁ (g₁ z)=coordinates c₁ s₁ (g₁ y) →
      ∃ Φ : E×E → E×E,Φ (x,y)=(z,w) ∧ ContDiffAt ℝ ∞ Φ (x,y) ∧
        (81/121:ℝ)≤|(fderiv ℝ Φ (x,y)).det| ∧
        |(fderiv ℝ Φ (x,y)).det|≤(121/81:ℝ) ∧
        ∀ᶠ t in 𝓝 (x,y),
          coordinates b₀ r₀ (f₀ (Φ t).1)=coordinates b₀ r₀ (f₀ t.1) ∧
          coordinates b₁ r₁ (f₁ (Φ t).2)=coordinates b₁ r₁ (f₁ t.2) ∧
          coordinates c₀ s₀ (g₀ (Φ t).2)=coordinates c₀ s₀ (g₀ t.1) ∧
          coordinates c₁ s₁ (g₁ (Φ t).1)=coordinates c₁ s₁ (g₁ t.2) := by
  classical
  have hex (z : Fin (d+1)×Fin (d+1)) := four_endpoint_branch (d:=d) (p:=z.1.val) (q:=z.2.val)
  choose δ hδ hbranch using hex
  obtain ⟨β,hβ,hβδ⟩ := SmoothObstruction.finite_positive_bound δ hδ
  refine ⟨β,hβ,?_⟩
  intro p q hp hq U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ f₀ f₁ g₀ g₁ x y z w A₀ A₁ D₀ D₁
    hxF hzF hyF hwF hxP hwP hyP hzP heF heF' heP heP'
  let j : Fin (d+1)×Fin (d+1) := (⟨p,by omega⟩,⟨q,by omega⟩)
  exact hbranch j U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ f₀ f₁ g₀ g₁ x y z w A₀ A₁ D₀ D₁
    (hxF.mono (hβδ j)) (hzF.mono (hβδ j)) (hyF.mono (hβδ j)) (hwF.mono (hβδ j))
    (hxP.mono (hβδ j)) (hwP.mono (hβδ j)) (hyP.mono (hβδ j)) (hzP.mono (hβδ j)) heF heF' heP heP'
end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The authentic eight endpoint minors give the local Jacobian germ of the
ORIGINAL measurable switch. Rank-zero blocks are included. The agreement is
relative to retained original inputs, not an extension or a different law. -/
theorem controlled_original_germ_uniform (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C β : ℝ,0 < r ∧ 1≤C ∧ 0<β ∧
      ∀ {p q : ℕ},p≤d → q≤d →
      ∀ {A J : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (ρ δ : ℝ)
        (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
        (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
        0≤ρ → ρ ≤ r → C*ρ<δ →
        (∀ u∈G,u.1∈R ∧ u.2∈R ∧ L u.1=L u.2) →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z → z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) ρ⊆interior (range I)) →
        let z := (Φ (x,y)).1
        let w := (Φ (x,y)).2
        originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
        originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
        let a₀ := a (c x)
        let X := (extChartAt I a₀) x
        let Y := (extChartAt I a₀) y
        let Z := (extChartAt I a₀) z
        let W := (extChartAt I a₀) w
        let f₀ := extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm
        let f₁ := extChartAt I (a (c (S^[n] y))) ∘ S^[n] ∘ (extChartAt I a₀).symm
        let g₀ := extChartAt I (a (c (S.symm^[n] x))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm
        let g₁ := extChartAt I (a (c (S.symm^[n] y))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm
        ∀ (U V : Submodule ℝ E₀) (_ : IsCompl U V)
          (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V)
          (b₀ b₁ c₀ c₁ : OrthonormalBasis (Fin d) ℝ E₀)
          (r₀ r₁ : powersetCard (Fin d) p) (s₀ s₁ : powersetCard (Fin d) q)
          (A₀ A₁ : Matrix (Fin p) (Fin p) ℝ) (D₀ D₁ : Matrix (Fin q) (Fin q) ℝ),
          (∀ j∈r₀,b₀ j∈Wf (P x,P (S^[n] x))) →
          (∀ v∈Wf (P x,P (S^[n] x)),∀ j∉r₀,b₀.repr v j=0) →
          (∀ j∈r₁,b₁ j∈Wf (P y,P (S^[n] y))) →
          (∀ v∈Wf (P y,P (S^[n] y)),∀ j∉r₁,b₁.repr v j=0) →
          (∀ j∈s₀,c₀ j∈Wb (P x,P (S.symm^[n] x))) →
          (∀ v∈Wb (P x,P (S.symm^[n] x)),∀ j∉s₀,c₀.repr v j=0) →
          (∀ j∈s₁,c₁ j∈Wb (P y,P (S.symm^[n] y))) →
          (∀ v∈Wb (P y,P (S.symm^[n] y)),∀ j∉s₁,c₁.repr v j=0) →
          GoodEndpoint β b₀ r₀ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₀ X A₀ →
          GoodEndpoint β b₀ r₀ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₀ Z A₀ →
          GoodEndpoint β b₁ r₁ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₁ Y A₁ →
          GoodEndpoint β b₁ r₁ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₁ W A₁ →
          GoodEndpoint β c₀ s₀ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₀ X D₀ →
          GoodEndpoint β c₀ s₀ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₀ W D₀ →
          GoodEndpoint β c₁ s₁ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₁ Y D₁ →
          GoodEndpoint β c₁ s₁ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₁ Z D₁ →
          coordinates b₀ r₀ (f₀ Z)=coordinates b₀ r₀ (f₀ X) →
          coordinates b₁ r₁ (f₁ W)=coordinates b₁ r₁ (f₁ Y) →
          coordinates c₀ s₀ (g₀ W)=coordinates c₀ s₀ (g₀ X) →
          coordinates c₁ s₁ (g₁ Z)=coordinates c₁ s₁ (g₁ Y) →
          (∀ᶠ t in 𝓝 (X,Y),
            P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
            P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
            P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y)) →
          let e := Prod.map (ChartDensity.coordinates I a₀) (ChartDensity.coordinates I a₀)
          let s := Prod.map (ChartDensity.inverse I a₀) (ChartDensity.inverse I a₀)
          ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ (X,Y)) (X,Y) ∧
            (81/121:ℝ)≤|(fderiv ℝ Ψ (X,Y)).det| ∧
            Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] (X,Y)] (e ∘ Φ ∘ s) := by
  obtain ⟨r,C,hr,hC,hgerm⟩ := original_pair_germ I hclosed a K hK hKU
  obtain ⟨β,hβ,hbranch⟩ := four_endpoint_branch_uniform (d:=d)
  refine ⟨r,C,β,hr,hC,hβ,?_⟩
  intro p q hp hq A J S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρr hρδ hG huniq hsecond hsafe
    z w ht1 ht2 ht3 ht4 a₀ X Y Z W f₀ f₁ g₀ g₁ U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ A₀ A₁ D₀ D₁
    hb₀ hz₀ hb₁ hz₁ hc₀ hv₀ hc₁ hv₁ hxF hzF hyF hwF hxB hwB hyB hzB he₀ he₁ he₂ he₃ hlabels e s
  obtain ⟨Ψ,hΨ,hcd,hlo,_,heq⟩ := hbranch hp hq U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁
    f₀ f₁ g₀ g₁ X Y Z W A₀ A₁ D₀ D₁ hxF hzF hyF hwF hxB hwB hyB hzB he₀ he₁ he₂ he₃
  let r₀' := Prod.map (extChartAt I a₀).symm (extChartAt I a₀).symm
  have hsrcx : x∈(extChartAt I a₀).source := by simpa only [extChartAt_source] using hKU _ (hc x)
  have hsrcy : y∈(extChartAt I a₀).source := by
    dsimp only [a₀]; rw [hcxy]; simpa only [extChartAt_source] using hKU _ (hc y)
  have hsrcz : z∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht1 0).1
  have hsrcw : w∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht4 0).1
  have hx : r₀' (X,Y)=(x,y) := Prod.ext ((extChartAt I a₀).left_inv hsrcx) ((extChartAt I a₀).left_inv hsrcy)
  have hz : r₀' (Ψ (X,Y))=(z,w) := by
    rw [hΨ]; exact Prod.ext ((extChartAt I a₀).left_inv hsrcz) ((extChartAt I a₀).left_inv hsrcw)
  have hXi : X∈interior (range I) := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply] using (hsafe 0).1 (mem_closedBall_self hρ)
  have hYi : Y∈interior (range I) := by
    dsimp only [Y,a₀]; rw [hcxy]
    simpa only [Fin.val_zero,Function.iterate_zero_apply] using (hsafe 0).2.2.1 (mem_closedBall_self hρ)
  have hZi : Z∈interior (range I) := by
    apply (hsafe 0).1
    exact mem_closedBall.mpr (by simpa only [Fin.val_zero,Function.iterate_zero_apply,dist_eq_norm] using (ht1 0).2)
  have hWi : W∈interior (range I) := by
    apply (hsafe 0).2.1
    exact mem_closedBall.mpr (by simpa only [Fin.val_zero,Function.iterate_zero_apply,dist_eq_norm] using (ht4 0).2)
  have hct := (ChartDensity.pair_inverse_germ I a₀ (X,Y)
    ((extChartAt I a₀).map_source hsrcx) ((extChartAt I a₀).map_source hsrcy) hXi hYi).1
  have hco : ContinuousAt r₀' (Z,W) := (ChartDensity.pair_inverse_germ I a₀ (Z,W)
    ((extChartAt I a₀).map_source hsrcz) ((extChartAt I a₀).map_source hsrcw) hZi hWi).1
  have hctΨ : ContinuousAt (r₀' ∘ Ψ) (X,Y) := (hΨ ▸ hco).comp hcd.continuousAt
  have heq' := original_equations_germ I S a c P hPc Wf Wb a₀ x y n b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁
    hb₀ hz₀ hb₁ hz₁ hc₀ hv₀ hc₁ hv₁ Ψ (X,Y) hlabels heq
  have hag := hgerm S c hc P L R Wf Wb n ρ δ Φ r₀' (r₀' ∘ Ψ) (X,Y)
    hct hctΨ hρ hρr hρδ (by simpa only [hx] using hsafe)
    (by simpa only [Function.comp_apply,hx,hz] using ht1)
    (by simpa only [Function.comp_apply,hx,hz] using ht2)
    (by simpa only [Function.comp_apply,hx,hz] using ht3)
    (by simpa only [Function.comp_apply,hx,hz] using ht4) huniq hsecond heq'
  refine ⟨Ψ,(hcd.differentiableAt (by simp)).hasFDerivAt,hlo,?_⟩
  apply ChartDensity.retained_pair_germ I a₀ G Φ Ψ (X,Y) hcd.continuousAt
    ((extChartAt I a₀).map_source hsrcx) ((extChartAt I a₀).map_source hsrcy) hXi hYi
  · simpa only [hΨ] using (extChartAt I a₀).map_source hsrcz
  · simpa only [hΨ] using (extChartAt I a₀).map_source hsrcw
  · simpa only [hΨ] using hZi
  · simpa only [hΨ] using hWi
  · filter_upwards [hag] with t ht
    intro htG
    exact ht (hG _ htG).1 (hG _ htG).2.1 (hG _ htG).2.2
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Fixed old-chart endpoint families give the actual retained-set relative germ. -/
theorem family_original_germ_uniform_oai (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C β : ℝ,0 < r ∧ 1≤C ∧ 0<β ∧
      ∀ {p q : ℕ},p≤d → q≤d →
      ∀ {A J : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (ρ δ : ℝ)
        (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
        (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
        0≤ρ → ρ ≤ r → C*ρ<δ →
        (∀ u∈G,u.1∈R ∧ u.2∈R ∧ L u.1=L u.2) →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z → z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) ρ⊆interior (range I)) →
        let z := (Φ (x,y)).1
        let w := (Φ (x,y)).2
        originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
        originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
        let a₀ := a (c x)
        let X := (extChartAt I a₀) x
        let Y := (extChartAt I a₀) y
        ∀ (U V : Submodule ℝ E₀) (_ : IsCompl U V)
          (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V),
          OriginalEndpointControl I S a c n ρ β (Wf (P x,P (S^[n] x))) (fun i => (u i:E₀)) (fun i => (v i:E₀)) x →
          OriginalEndpointControl I S a c n ρ β (Wf (P y,P (S^[n] y))) (fun i => (u i:E₀)) (fun i => (v i:E₀)) y →
          OriginalEndpointControl I S.symm a c n ρ β (Wb (P x,P (S.symm^[n] x))) (fun i => (v i:E₀)) (fun i => (u i:E₀)) x →
          OriginalEndpointControl I S.symm a c n ρ β (Wb (P y,P (S.symm^[n] y))) (fun i => (v i:E₀)) (fun i => (u i:E₀)) y →
          originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
          originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z →
          (∀ᶠ t in 𝓝 (X,Y),
            P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
            P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
            P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y)) →
          let e := Prod.map (ChartDensity.coordinates I a₀) (ChartDensity.coordinates I a₀)
          let s := Prod.map (ChartDensity.inverse I a₀) (ChartDensity.inverse I a₀)
          ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ (X,Y)) (X,Y) ∧
            (81/121:ℝ)≤|(fderiv ℝ Ψ (X,Y)).det| ∧
            Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] (X,Y)] (e ∘ Φ ∘ s) := by
  obtain ⟨r,C,β,hr,hC,hβ,hh⟩ := controlled_original_germ_uniform I hclosed a K hK hKU
  refine ⟨r,C,β,hr,hC,hβ,?_⟩
  intro p q hp hq A J S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρr hρδ hG huniq hsecond hsafe
    z w ht1 ht2 ht3 ht4 a₀ X Y U V h u v hf₀ hf₁ hb₀ hb₁ he₀ he₁ he₂ he₃ hlabels e s
  obtain ⟨b₀,r₀,A₀,hbF₀,hzF₀,hmF₀⟩ := hf₀
  obtain ⟨b₁,r₁,A₁,hbF₁,hzF₁,hmF₁⟩ := hf₁
  obtain ⟨c₀,s₀,D₀,hbB₀,hzB₀,hmB₀⟩ := hb₀
  obtain ⟨c₁,s₁,D₁,hbB₁,hzB₁,hmB₁⟩ := hb₁
  have hsrc (x : M) : x∈(chartAt H (a (c x))).source := hKU _ (hc x)
  have hx : x∈(extChartAt I a₀).source := by simpa only [extChartAt_source] using hsrc x
  have hy : y∈(extChartAt I a₀).source := by dsimp only [a₀]; rw [hcxy]; simpa only [extChartAt_source] using hsrc y
  have hz : z∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht1 0).1
  have hw : w∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht4 0).1
  have hfx := hmF₀ x (originalTube_self I S a c hρ x hsrc)
  have hfy := hmF₁ y (originalTube_self I S a c hρ y hsrc)
  have hbx := hmB₀ x (originalTube_self I S.symm a c hρ x hsrc)
  have hby := hmB₁ y (originalTube_self I S.symm a c hρ y hsrc)
  have hfw := hmF₁ w ht3
  have hbz := hmB₁ z ht2
  rw [←hcxy] at hfy hby hfw hbz
  exact hh hp hq S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρr hρδ hG huniq hsecond hsafe
    ht1 ht2 ht3 ht4 U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ A₀ A₁ D₀ D₁
    hbF₀ hzF₀ hbF₁ hzF₁ hbB₀ hzB₀ hbB₁ hzB₁
    hfx (hmF₀ z ht1) hfy hfw hbx (hmB₀ w ht4) hby hbz
    (originalEndpoint_coordinates I S a c n a₀ x z _ b₀ r₀ hbF₀ hzF₀ hx hz he₀)
    (originalEndpoint_coordinates I S a c n a₀ y w _ b₁ r₁ hbF₁ hzF₁ hy hw he₁)
    (originalEndpoint_coordinates I S.symm a c n a₀ x w _ c₀ s₀ hbB₀ hzB₀ hx hw he₂)
    (originalEndpoint_coordinates I S.symm a c n a₀ y z _ c₁ s₁ hbB₁ hzB₁ hy hz he₃) hlabels
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.SmoothObstruction.ManifoldCoordinates.family_original_germ_uniform_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.SmoothObstruction.ManifoldCoordinates.family_original_germ_uniform_oai.{u_1, u_2, u_3, u_4, u_5}
