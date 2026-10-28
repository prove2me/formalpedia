-- Prove2me | solution 1 for OAI.SmoothObstruction.ManifoldCoordinates.genuine_pair_switch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:18:31.046448+00:00
-- url     : https://prove2.me/submissions/a59958ea-4ece-4177-bad3-db4bcc8c2c98

import Mathlib
import Definitions.Def_SmoothObstruction
import Definitions.Def_OAIQ5T3000
import Theorems.Thm_OAI_SmoothObstruction_ManifoldCoordinates_gauge_original_germ_sharp

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
end OAICompat434

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

lemma norm_mask (S : Finset (Fin d)) : ‖mask S‖ ≤ 1 := by
  rw [mask,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i; split <;> norm_num

lemma norm_projection (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    {K : ℝ} (S : Finset (Fin d)) (t : ℕ)
    (hU : ‖U t‖ ≤ Real.exp K) (hV : ‖V t‖ ≤ Real.exp K) :
    ‖projection U V S t‖ ≤ Real.exp (2*K) := by
  calc
    _ ≤ ‖U t‖ * ‖mask S‖ * ‖V t‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp K * 1 * Real.exp K := by gcongr; exact norm_mask S
    _ = _ := by rw [mul_one,←Real.exp_add]; congr 1; ring

lemma norm_rate_mask {lam : Fin d → ℝ} {l c : ℝ} (hl : 0 ≤ l)
    (S : Finset (Fin d)) (hc : ∀ j ∈ S, lam j ≤ c) :
    ‖rate lam l*mask S‖ ≤ Real.exp (c*l) := by
  simp only [rate,mask,Matrix.diagonal_mul_diagonal,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
  intro i
  by_cases hi : i ∈ S
  · simp only [hi,ite_true,mul_one,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [hc i hi]
  · simp only [hi,ite_false,mul_zero,norm_zero]; exact Real.exp_nonneg _

/-- Subinterval propagation on a selected group. The only conditioning
loss is at the two endpoints. -/
lemma norm_transition_projection (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hVU : ∀ t, V t*U t=1) (lam : Fin d → ℝ) {K c : ℝ}
    (S : Finset (Fin d)) (s t : ℕ) (hst : s ≤ t)
    (hU : ‖U t‖ ≤ Real.exp K) (hV : ‖V s‖ ≤ Real.exp K)
    (hc : ∀ j ∈ S, lam j ≤ c) :
    ‖transition U V lam s t*projection U V S s‖ ≤
      Real.exp (c*((t:ℝ)-s)+2*K) := by
  have hr : 0 ≤ (t:ℝ)-s := sub_nonneg.mpr (by exact_mod_cast hst)
  have heq : transition U V lam s t*projection U V S s =
      U t*(rate lam ((t:ℝ)-s)*mask S)*V s := by
    dsimp [transition,projection]
    calc
      _ = U t*(rate lam ((t:ℝ)-s)*(V s*U s)*mask S)*V s := by noncomm_ring
      _ = _ := by rw [hVU,mul_one]
  rw [heq]
  calc
    _ ≤ ‖U t‖ * ‖rate lam ((t:ℝ)-s)*mask S‖ * ‖V s‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp K * Real.exp (c*((t:ℝ)-s)) * Real.exp K := by
      gcongr; exact norm_rate_mask hr S hc
    _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring

lemma norm_rate_mask_lower {lam : Fin d → ℝ} {l c : ℝ} (hl : l ≤ 0)
    (S : Finset (Fin d)) (hc : ∀ j ∈ S, c ≤ lam j) :
    ‖rate lam l*mask S‖ ≤ Real.exp (c*l) := by
  simp only [rate,mask,Matrix.diagonal_mul_diagonal,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
  intro i
  by_cases hi : i ∈ S
  · simp only [hi,ite_true,mul_one,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [hc i hi]
  · simp only [hi,ite_false,mul_zero,norm_zero]; exact Real.exp_nonneg _

lemma norm_backward_projection (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hVU : ∀ t, V t*U t=1) (lam : Fin d → ℝ) {K c : ℝ}
    (S : Finset (Fin d)) (s t : ℕ) (hst : s ≤ t)
    (hU : ‖U s‖ ≤ Real.exp K) (hV : ‖V t‖ ≤ Real.exp K)
    (hc : ∀ j ∈ S, c ≤ lam j) :
    ‖transition U V lam t s*projection U V S t‖ ≤
      Real.exp (-c*((t:ℝ)-s)+2*K) := by
  have hr : (s:ℝ)-t ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hst)
  have heq : transition U V lam t s*projection U V S t =
      U s*(rate lam ((s:ℝ)-t)*mask S)*V t := by
    dsimp [transition,projection]
    calc
      _ = U s*(rate lam ((s:ℝ)-t)*(V t*U t)*mask S)*V t := by noncomm_ring
      _ = _ := by rw [hVU,mul_one]
  rw [heq]
  calc
    _ ≤ ‖U s‖ * ‖rate lam ((s:ℝ)-t)*mask S‖ * ‖V t‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp K * Real.exp (c*((s:ℝ)-t)) * Real.exp K := by
      gcongr; exact norm_rate_mask_lower hr S hc
    _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
end SmoothObstruction.EuclideanSplitting

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
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The actual derivative cocycle is the derivative of the actual local
coordinate map. Charts may be independently selected at each endpoint;
the formula is valid on half-space models without changing derivatives. -/
theorem coord_eq_fderivWithin (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) :
    fderivWithin ℝ (localMap I S a b) (range I) ((extChartAt I a) x)=coord I S a b x := by
  have hit : (extChartAt I a) x∈(extChartAt I a).target :=
    (extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1)
  have hir : (extChartAt I a) x∈range I := extChartAt_target_subset_range a hit
  have huniq : UniqueMDiffWithinAt (𝓘(ℝ,E (d:=d))) (range I) ((extChartAt I a) x) :=
    (I.uniqueDiffOn _ hir).uniqueMDiffWithinAt
  have hs := mdifferentiableWithinAt_extChartAt_symm (I:=I) hit
  have hf : MDifferentiableAt I (𝓘(ℝ,E (d:=d))) (extChartAt I b ∘ S) x :=
    (mdifferentiableAt_extChartAt hx.2).comp x (S.contMDiff.mdifferentiable (by simp) x)
  have hcomp := mfderiv_comp_mfderivWithin_of_eq hf hs huniq
    ((extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1))
  have hchain := mfderiv_comp x (mdifferentiableAt_extChartAt (I:=I) hx.2)
    (S.contMDiff.mdifferentiable (by simp) x)
  rw [hchain] at hcomp
  have hcoord := inTangentCoordinates_eq_mfderiv_comp
    (I:=I) (I':=I) (f:=fun p : M×M => p.1) (g:=fun p : M×M => p.2)
    (ϕ:=fun p => mfderiv I I S p.1) (x₀:=(a,b)) (x:=(x,S x)) hx.1 hx.2
  change coord I S a b x=_ at hcoord
  rw [mfderivWithin_eq_fderivWithin] at hcomp
  have he := hcomp.trans hcoord.symm
  change fderivWithin ℝ ((extChartAt I b ∘ S) ∘ (extChartAt I a).symm)
    (range I) ((extChartAt I a) x)=coord I S a b x at he
  simpa only [localMap,Function.comp_assoc] using he

/-- In an interior orbit tube this is an ordinary derivative, exactly the
input of the finite-array nonlinear construction. -/
theorem hasFDerivAt_localMap (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b)
    (hint : (extChartAt I a) x∈interior (range I)) :
    HasFDerivAt (localMap I S a b) (coord I S a b x) ((extChartAt I a) x) := by
  have hs := mdifferentiableWithinAt_extChartAt_symm (I:=I)
    ((extChartAt I a).map_source (by simpa only [extChartAt_source] using hx.1))
  have hf : MDifferentiableAt I (𝓘(ℝ,E (d:=d))) (extChartAt I b ∘ S) x :=
    (mdifferentiableAt_extChartAt hx.2).comp x (S.contMDiff.mdifferentiable (by simp) x)
  have hh := hf.comp_mdifferentiableWithinAt_of_eq _ hs ((extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx.1))
  have hd : DifferentiableWithinAt ℝ (localMap I S a b) (range I) ((extChartAt I a) x) := by
    exact mdifferentiableWithinAt_iff_differentiableWithinAt.mp hh
  rw [←coord_eq_fderivWithin I S a b x hx]
  exact hd.hasFDerivWithinAt.hasFDerivAt (mem_interior_iff_mem_nhds.mp hint)
end SmoothObstruction.ManifoldCoordinates

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

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma interior_coord (a x : M) (hx : x∈(chartAt H a).source) :
    (extChartAt I a) x∈interior (range I) ↔ I.IsInteriorPoint x := by
  rw [I.isInteriorPoint_iff_of_mem_atlas (by simp : (∞ : ℕ∞ω)≠0)
    (chart_mem_atlas H a) hx]
  exact ⟨fun h => (chartAt H a).mem_interior_extend_target
    ((chartAt H a).map_source hx) h,
    fun h => (chartAt H a).interior_extend_target_subset_interior_range h⟩

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SpectralBins
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
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma mem_coordinateSpace (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    x∈coordinateSpace S ↔ ∀ j∉S,x j=0 := by
  rw [coordinateSpace,Submodule.map_equiv_eq_comap_symm]
  exact Pi.mem_spanSubset_iff

lemma finrank_coordinateSpace (S : Finset (Fin d)) :
    Module.finrank ℝ (coordinateSpace S)=S.card := by
  rw [coordinateSpace,LinearEquiv.finrank_map_eq,Pi.dim_spanSubset,Set.ncard_coe_finset]

lemma mask_apply (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (mask S) x) j=if j∈S then x j else 0 := by
  change ((mask S)*ᵥ (WithLp.ofLp x)) j=_
  rw [mask,Matrix.mulVec_diagonal]
  split <;> simp_all

lemma coordinateSpace_fixed (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    x∈coordinateSpace S ↔ Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (mask S) x=x := by
  rw [mem_coordinateSpace]
  constructor
  · intro hx
    ext j
    rw [mask_apply]
    split_ifs with hj
    · rfl
    · exact (hx j hj).symm
  · intro hx j hj
    have he := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x j) hx
    rw [mask_apply,ite_eq_right hj] at he
    exact he.symm

lemma finrank_groupSpace (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (S : Finset (Fin d)) :
    Module.finrank ℝ (groupSpace U V hUV hVU S)=S.card := by
  rw [groupSpace,LinearEquiv.finrank_map_eq,finrank_coordinateSpace]

lemma groupSpace_fixed (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (S : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    x∈groupSpace U V hUV hVU S ↔
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U*mask S*V) x=x := by
  rw [groupSpace,Submodule.map_equiv_eq_comap_symm]
  change (gaugeEquiv U V hUV hVU).symm x∈coordinateSpace S ↔ _
  rw [coordinateSpace_fixed]
  constructor
  · intro hx
    have he := congrArg (gaugeEquiv U V hUV hVU) hx
    rw [(gaugeEquiv U V hUV hVU).apply_symm_apply] at he
    simpa only [gaugeEquiv_apply,gaugeEquiv_symm_apply,map_mul,
      mul_apply_eq_comp] using he
  · intro hx
    apply (gaugeEquiv U V hUV hVU).injective
    rw [(gaugeEquiv U V hUV hVU).apply_symm_apply]
    simpa only [gaugeEquiv_apply,gaugeEquiv_symm_apply,map_mul,
      mul_apply_eq_comp] using hx

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator

variable {d L : ℕ} {K : ℝ}

lemma Gauge.rank (A : Gauge d L K) (S : Finset (Fin d)) :
    Module.finrank ℝ (A.space S)=S.card :=
  finrank_groupSpace _ _ _ _ _

end SmoothObstruction.ShortBin

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
-- module Solutions.OAIQ5_T3.SmoothObstruction_GreenOperator
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

namespace SmoothObstruction.FiniteGreen
open Finset
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

namespace Splitting
variable {A : Evolution E} (B : Splitting A)

namespace Terminal
variable {B} {n : ℕ} (C : B.Terminal (H:=H) n)
lemma fast_J (h : H) : B.fast n (C.J h)=C.J h :=
  congrArg (fun F : H →L[ℝ] E => F h) C.range

lemma kernel_factor : C.kernel=
    -(((A.map 0 n).comp (B.fast n)).comp
      (C.J.comp (C.P.comp ((A.map n 0).comp (B.slow 0))))) := by
  unfold kernel
  congr 1
  ext v
  change A.map 0 n (C.J (C.P (A.map n 0 (B.slow 0 v))))=
    A.map 0 n (B.fast n (C.J (C.P (A.map n 0 (B.slow 0 v)))))
  rw [C.fast_J]

end Terminal
end Splitting
end SmoothObstruction.FiniteGreen

namespace SmoothObstruction.EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma forward_decay (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d))
    {K g : ℝ} {s t : ℕ} (hst : s ≤ t)
    (hU : ‖U t‖ ≤ Real.exp K) (hV : ‖V s‖ ≤ Real.exp K)
    (hgap : ∀ j∈S,lam j ≤ -g) :
    ‖((evolution U V lam hUV hVU).map t s).comp
      ((splitting U V lam hUV hVU S).slow s)‖ ≤
      Real.exp (2*K)*Real.exp (-g*((t:ℝ)-s)) := by
  change ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S s)‖ ≤ _
  rw [←map_mul,Matrix.l2_opNorm_toEuclideanCLM,←Real.exp_add]
  convert norm_transition_projection U V hVU lam S s t hst hU hV hgap using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma backward_decay (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d))
    {K g : ℝ} {s t : ℕ} (hst : s ≤ t)
    (hU : ‖U s‖ ≤ Real.exp K) (hV : ‖V t‖ ≤ Real.exp K)
    (hgap : ∀ j∈Sᶜ,g ≤ lam j) :
    ‖((evolution U V lam hUV hVU).map s t).comp
      ((splitting U V lam hUV hVU S).fast t)‖ ≤
      Real.exp (2*K)*Real.exp (-g*((t:ℝ)-s)) := by
  change ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam t s)*
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ t)‖ ≤ _
  rw [←map_mul,Matrix.l2_opNorm_toEuclideanCLM,←Real.exp_add]
  convert norm_backward_projection U V hVU lam Sᶜ s t hst hU hV hgap using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d : ℕ} (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d))

lemma splitting_slow_norm {K : ℝ} (t : ℕ)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K) :
    ‖(splitting U V lam hUV hVU S).slow t‖≤Real.exp (2*K) := by
  change ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S t)‖≤_
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  exact norm_projection U V S t hU hV

lemma splitting_fast_norm {K : ℝ} (t : ℕ)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K) :
    ‖(splitting U V lam hUV hVU S).fast t‖≤Real.exp (2*K) := by
  exact splitting_slow_norm U V lam hUV hVU Sᶜ t hU hV

/-- The genuine unweighted Green bounds do not require negative slow rates.
Their growth is only the threshold times the window, not the largest rate. -/
theorem unweighted_bounds {K a : ℝ} {n : ℕ} (ha : 0≤a)
    (hU : ∀ t≤n,‖U t‖≤Real.exp K) (hV : ∀ t≤n,‖V t‖≤Real.exp K)
    (hs : ∀ j∈S,lam j≤a) (hf : ∀ j∈Sᶜ,-a≤lam j) :
    (∀ s t,s≤t → t≤n → ‖((evolution U V lam hUV hVU).map t s).comp
      ((splitting U V lam hUV hVU S).slow s)‖≤Real.exp (2*K+a*n)) ∧
    (∀ s t,s≤t → t≤n → ‖((evolution U V lam hUV hVU).map s t).comp
      ((splitting U V lam hUV hVU S).fast t)‖≤Real.exp (2*K+a*n)) := by
  have ht (s t : ℕ) (htn : t≤n) : a*((t:ℝ)-s)≤a*n := by
    have hh : (t:ℝ)≤n := by exact_mod_cast htn
    nlinarith [Nat.cast_nonneg (α:=ℝ) s]
  constructor
  · intro s t hst htn
    have hh := forward_decay U V lam hUV hVU S (g:=-a) hst (hU t htn)
      (hV s (hst.trans htn)) (by simpa only [neg_neg] using hs)
    simp only [neg_neg] at hh
    apply hh.trans
    rw [←Real.exp_add]
    exact Real.exp_le_exp.mpr (add_le_add le_rfl (ht s t htn))
  · intro s t hst htn
    have hh := backward_decay U V lam hUV hVU S (g:=-a) hst
      (hU s (hst.trans htn)) (hV t htn) hf
    simp only [neg_neg] at hh
    apply hh.trans
    rw [←Real.exp_add]
    exact Real.exp_le_exp.mpr (add_le_add le_rfl (ht s t htn))

/-- At the full endpoints the threshold cancels between slow forward and
fast inverse growth, including the positive-slow case. -/
theorem endpoint_gap_bounds {K γ g : ℝ} (n : ℕ)
    (hU : ∀ t≤n,‖U t‖≤Real.exp K) (hV : ∀ t≤n,‖V t‖≤Real.exp K)
    (hs : ∀ j∈S,lam j≤γ-g) (hf : ∀ j∈Sᶜ,γ+g≤lam j) :
    ‖((evolution U V lam hUV hVU).map n 0).comp
      ((splitting U V lam hUV hVU S).slow 0)‖≤Real.exp (2*K)*Real.exp ((γ-g)*n) ∧
    ‖((evolution U V lam hUV hVU).map 0 n).comp
      ((splitting U V lam hUV hVU S).fast n)‖≤Real.exp (2*K)*Real.exp (-(γ+g)*n) := by
  constructor
  · simpa only [Nat.cast_zero,sub_zero,neg_neg] using
      forward_decay U V lam hUV hVU S (g:=-(γ-g)) (Nat.zero_le n)
        (hU n le_rfl) (hV 0 (Nat.zero_le n)) (by simpa only [neg_neg] using hs)
  · simpa only [Nat.cast_zero,sub_zero] using
      backward_decay U V lam hUV hVU S (g:=γ+g) (Nat.zero_le n)
        (hU 0 (Nat.zero_le n)) (hV n le_rfl) hf
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.FiniteGreen.Splitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : Evolution E} (B : Splitting A)

variable [FiniteDimensional ℝ E]

lemma referenceMatching_inverse_norm (t : ℕ) {K : ℝ}
    (hs : ‖B.slow t‖≤K) (hf : ‖B.fast t‖≤K) :
    ‖(B.referenceMatching t).symm.toContinuousLinearMap‖≤K := by
  have hK : 0≤K := (norm_nonneg (B.slow t)).trans hs
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  change ‖((⟨B.slow t x,⟨x,rfl⟩⟩ : (B.slow t).range),
    (⟨-B.fast t x,⟨-x,by simp⟩⟩ : (B.fast t).range))‖≤K*‖x‖
  rw [Prod.norm_def,max_le_iff]
  constructor
  · exact ((B.slow t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x))
  · change ‖-B.fast t x‖≤K*‖x‖
    rw [norm_neg]
    exact ((B.fast t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg x))
end SmoothObstruction.FiniteGreen.Splitting

namespace SmoothObstruction.CloseProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma inverse_norm (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) :
    ‖(equiv U V hdim hclose).symm.toContinuousLinearMap‖ ≤ 2 := by
  apply (equiv U V hdim hclose).symm.toContinuousLinearMap.opNorm_le_bound (by norm_num)
  intro y
  have hh := lower U V hclose ((equiv U V hdim hclose).symm y)
  rwa [←equiv_apply U V hdim hclose,(equiv U V hdim hclose).apply_symm_apply] at hh

end SmoothObstruction.CloseProjection

namespace SmoothObstruction.BoundaryNeumann
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
lemma inverse_bound (L M : E ≃L[ℝ] F) (D : E →L[ℝ] F) {K : ℝ}
    (hM : ∀ x,M x=L x+D x)
    (hK : ‖L.symm.toContinuousLinearMap‖ ≤ K)
    (hD : ‖L.symm.toContinuousLinearMap.comp D‖ ≤ 1/2) :
    ‖M.symm.toContinuousLinearMap‖ ≤ 2*K := by
  have hKn : 0 ≤ K := (norm_nonneg _).trans hK
  apply ContinuousLinearMap.opNorm_le_bound M.symm.toContinuousLinearMap (by positivity)
  intro y
  let x := M.symm y
  have he : x+L.symm (D x)=L.symm y := by
    have hh := M.apply_symm_apply y
    change M x=y at hh
    rw [hM] at hh
    have hh' := congrArg L.symm hh
    simpa only [map_add,L.symm_apply_apply] using hh'
  have hnx : ‖x‖ ≤ ‖L.symm y‖+‖L.symm (D x)‖ := by
    calc
      _ = ‖L.symm y-L.symm (D x)‖ := by rw [←he,add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  have hny : ‖L.symm y‖ ≤ K*‖y‖ :=
    (L.symm.toContinuousLinearMap.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have hdx : ‖L.symm (D x)‖ ≤ (1/2:ℝ)*‖x‖ :=
    ((L.symm.toContinuousLinearMap.comp D).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  change ‖x‖ ≤ _
  linarith

lemma inverse_norm (L : E ≃L[ℝ] F) (D : E →L[ℝ] F) {K : ℝ}
    (hK : ‖L.symm.toContinuousLinearMap‖ ≤ K)
    (hD : ‖L.symm.toContinuousLinearMap.comp D‖ ≤ 1/2) :
    ‖(perturb L D (hD.trans_lt (by norm_num))).symm.toContinuousLinearMap‖ ≤ 2*K :=
  inverse_bound L _ D (perturb_apply L D _) hK hD

end SmoothObstruction.BoundaryNeumann

namespace SmoothObstruction.CloseComplement
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A pair of spaces close to a quantitatively complementary reference pair
is genuinely complementary. The inverse is constructed by Neumann inversion
on the reference product, and its norm is controlled. -/
theorem exists_matching (U₀ V₀ U V : Submodule ℝ E)
    (L₀ : (U₀ × V₀) ≃L[ℝ] E) (hL₀ : ∀ x,L₀ x=(x.1:E)-(x.2:E))
    (hdU : Module.finrank ℝ U₀=Module.finrank ℝ U)
    (hdV : Module.finrank ℝ V₀=Module.finrank ℝ V)
    {ε K : ℝ} (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hcU : ‖U₀.starProjection-U.starProjection‖≤ε)
    (hcV : ‖V₀.starProjection-V.starProjection‖≤ε)
    (hK : ‖L₀.symm.toContinuousLinearMap‖≤K) (hsmall : K*(2*ε)≤1/2) :
    ∃ L : (U × V) ≃L[ℝ] E,(∀ x,L x=(x.1:E)-(x.2:E)) ∧
      ‖L.symm.toContinuousLinearMap‖≤2*K := by
  let eU := CloseProjection.equiv U₀ U hdU (hcU.trans hεhalf)
  let eV := CloseProjection.equiv V₀ V hdV (hcV.trans hεhalf)
  let J : (U₀ × V₀) ≃L[ℝ] U × V := eU.prodCongr eV
  have hJ : ‖J.toContinuousLinearMap‖≤1 := by
    apply J.toContinuousLinearMap.opNorm_le_bound zero_le_one
    intro x
    rw [one_mul,Prod.norm_def,max_le_iff]
    constructor
    · change ‖U.starProjection (x.1:E)‖≤‖x‖
      exact (Submodule.norm_starProjection_apply_le _ _).trans (norm_fst_le x)
    · change ‖V.starProjection (x.2:E)‖≤‖x‖
      exact (Submodule.norm_starProjection_apply_le _ _).trans (norm_snd_le x)
  have hdiffU (x : U₀) : ‖(eU x:E)-(x:E)‖≤ε*‖x‖ := by
    have h := (U₀.starProjection-U.starProjection).le_opNorm (x:E)
    rw [_root_.sub_apply,U₀.starProjection_eq_self_iff.mpr x.property] at h
    change ‖U.starProjection (x:E)-(x:E)‖≤ε*‖x‖
    rw [norm_sub_rev]
    exact h.trans (mul_le_mul_of_nonneg_right hcU (norm_nonneg _))
  have hdiffV (x : V₀) : ‖(eV x:E)-(x:E)‖≤ε*‖x‖ := by
    have h := (V₀.starProjection-V.starProjection).le_opNorm (x:E)
    rw [_root_.sub_apply,V₀.starProjection_eq_self_iff.mpr x.property] at h
    change ‖V.starProjection (x:E)-(x:E)‖≤ε*‖x‖
    rw [norm_sub_rev]
    exact h.trans (mul_le_mul_of_nonneg_right hcV (norm_nonneg _))
  let D := (difference U V).comp J.toContinuousLinearMap-L₀.toContinuousLinearMap
  have hD : ‖D‖≤2*ε := by
    apply D.opNorm_le_bound (by positivity)
    intro x
    change ‖difference U V (J x)-L₀ x‖≤(2*ε)*‖x‖
    rw [difference_apply,hL₀]
    have he : ((J x).1:E)-((J x).2:E)-((x.1:E)-(x.2:E))=
      ((eU x.1:E)-(x.1:E))-((eV x.2:E)-(x.2:E)) := by
        change (eU x.1:E)-(eV x.2:E)-((x.1:E)-(x.2:E))=_
        abel
    rw [he]
    calc
      _ ≤ ‖(eU x.1:E)-(x.1:E)‖+‖(eV x.2:E)-(x.2:E)‖ := norm_sub_le _ _
      _ ≤ ε*‖x.1‖+ε*‖x.2‖ := add_le_add (hdiffU _) (hdiffV _)
      _ ≤ ε*‖x‖+ε*‖x‖ := by gcongr <;> [exact norm_fst_le x; exact norm_snd_le x]
      _ = _ := by ring
  have hKn : 0≤K := (norm_nonneg L₀.symm.toContinuousLinearMap).trans hK
  have hsmall' : ‖L₀.symm.toContinuousLinearMap.comp D‖≤1/2 := by
    apply ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
    exact (mul_le_mul hK hD (norm_nonneg D) hKn).trans hsmall
  let M := BoundaryNeumann.perturb L₀ D (hsmall'.trans_lt (by norm_num))
  let L := J.symm.trans M
  refine ⟨L,?_,?_⟩
  · intro x
    change M (J.symm x)=(x.1:E)-(x.2:E)
    rw [BoundaryNeumann.perturb_apply]
    change L₀ (J.symm x)+(difference U V (J (J.symm x))-L₀ (J.symm x))=_
    rw [J.apply_symm_apply,difference_apply]
    abel
  · have hMi : ‖M.symm.toContinuousLinearMap‖≤2*K := BoundaryNeumann.inverse_norm L₀ D hK hsmall'
    change ‖J.toContinuousLinearMap.comp M.symm.toContinuousLinearMap‖≤2*K
    apply ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
    exact (mul_le_mul hJ hMi (norm_nonneg M.symm.toContinuousLinearMap) zero_le_one).trans_eq (one_mul _)

end SmoothObstruction.CloseComplement

namespace SmoothObstruction.FiniteGreen.Splitting
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {A : Evolution E} (B : Splitting A)

lemma terminalProjection_P_norm (n : ℕ) (V : Submodule ℝ E)
    (hdim : Module.finrank ℝ (B.fast n).range=Module.finrank ℝ V)
    (hclose : ‖(B.fast n).range.starProjection-V.starProjection‖≤1/2) :
    ‖(B.terminalProjection n V hdim hclose).P‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖V.starProjection x‖≤1*‖x‖
  rw [one_mul]
  exact Submodule.norm_starProjection_apply_le _ _

lemma terminalProjection_J_norm (n : ℕ) (V : Submodule ℝ E)
    (hdim : Module.finrank ℝ (B.fast n).range=Module.finrank ℝ V)
    (hclose : ‖(B.fast n).range.starProjection-V.starProjection‖≤1/2) :
    ‖(B.terminalProjection n V hdim hclose).J‖≤2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖(CloseProjection.equiv (B.fast n).range V hdim hclose).symm x‖≤2*‖x‖
  apply ((CloseProjection.equiv (B.fast n).range V hdim hclose).symm.toContinuousLinearMap.le_opNorm x).trans
  exact mul_le_mul_of_nonneg_right (CloseProjection.inverse_norm _ _ hdim hclose) (norm_nonneg x)
end SmoothObstruction.FiniteGreen.Splitting

namespace SmoothObstruction.FiniteGreen.Splitting.Terminal
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {A : Evolution E} {B : Splitting A} {n : ℕ} (C : B.Terminal (H:=H) n)

/-- The endpoint graph correction is small even when the slow rates are
positive. The two complementary exponentials cancel their threshold,
leaving the spectral gap; no hyperbolic sign assumption was added. -/
lemma kernel_norm_gap {G g γ : ℝ} (hG : 0≤G)
    (hback : ‖(A.map 0 n).comp (B.fast n)‖≤G*Real.exp (-(γ+g)*n))
    (hforw : ‖(A.map n 0).comp (B.slow 0)‖≤G*Real.exp ((γ-g)*n))
    (hJ : ‖C.J‖≤2) (hP : ‖C.P‖≤1) :
    ‖C.kernel‖≤2*G^2*Real.exp (-2*g*n) := by
  rw [C.kernel_factor,norm_neg]
  calc
    _ ≤ ‖(A.map 0 n).comp (B.fast n)‖*(‖C.J‖*(‖C.P‖*‖(A.map n 0).comp (B.slow 0)‖)) := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      gcongr
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (G*Real.exp (-(γ+g)*n))*(2*(1*(G*Real.exp ((γ-g)*n)))) := by gcongr
    _ = 2*G^2*Real.exp (-2*g*n) := by
      rw [show -2*g*(n:ℝ)=-(γ+g)*n+(γ-g)*n by ring,Real.exp_add]
      ring
end SmoothObstruction.FiniteGreen.Splitting.Terminal

namespace SmoothObstruction.EuclideanSplitting
variable {d : ℕ} (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d))

lemma splitting_slow_range (t : ℕ) :
    ((splitting U V lam hUV hVU S).slow t).range=
      groupSpace (U t) (V t) (hUV t) (hVU t) S := by
  ext x
  rw [groupSpace_fixed]
  constructor
  · rintro ⟨y,rfl⟩
    exact (splitting U V lam hUV hVU S).slow_self t y
  · intro hx
    exact ⟨x,hx⟩

lemma splitting_fast_range (t : ℕ) :
    ((splitting U V lam hUV hVU S).fast t).range=
      groupSpace (U t) (V t) (hUV t) (hVU t) Sᶜ :=
  splitting_slow_range U V lam hUV hVU Sᶜ t
end SmoothObstruction.EuclideanSplitting

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_BoundaryMatching
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

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d n : ℕ} {K : ℝ}

lemma Gauge.space_eq_range (A : Gauge d n K) (S : Finset (Fin d)) :
    A.space S=((A.splitting S).slow 0).range :=
  (splitting_slow_range _ _ _ _ _ _ _).symm

/-- The orthogonal common-bin space comparisons construct the middle
matching equivalence for two genuine gauges with a possibly positive slow
threshold. Complementarity is proved, not assumed for the moving spaces. -/
theorem gauge_matching (A₀ A Z : Gauge d n K) (S₀ S T : Finset (Fin d))
    {ε : ℝ} (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hdS : S₀.card=S.card) (hdT : S₀ᶜ.card=T.card)
    (hcS : ‖(A₀.space S₀).starProjection-(A.space S).starProjection‖≤ε)
    (hcT : ‖(A₀.space S₀ᶜ).starProjection-(Z.space T).starProjection‖≤ε)
    (hsmall : Real.exp (2*K)*(2*ε)≤1/2) :
    ∃ L : (((A.splitting S).slow 0).range×((Z.splitting T).slow 0).range) ≃L[ℝ]
      EuclideanSpace ℝ (Fin d),
      (∀ x,L x=(x.1:EuclideanSpace ℝ (Fin d))-(x.2:EuclideanSpace ℝ (Fin d))) ∧
      ‖L.symm.toContinuousLinearMap‖≤2*Real.exp (2*K) := by
  let B := A₀.splitting S₀
  have hs : ‖B.slow 0‖≤Real.exp (2*K) :=
    splitting_slow_norm _ _ _ _ _ _ 0 (A₀.normU _ (Nat.zero_le n)) (A₀.normV _ (Nat.zero_le n))
  have hf : ‖B.fast 0‖≤Real.exp (2*K) :=
    splitting_fast_norm _ _ _ _ _ _ 0 (A₀.normU _ (Nat.zero_le n)) (A₀.normV _ (Nat.zero_le n))
  have heS : (B.slow 0).range=A₀.space S₀ := (A₀.space_eq_range S₀).symm
  have heT : (B.fast 0).range=A₀.space S₀ᶜ :=
    splitting_fast_range _ _ _ _ _ _ _
  have hdS' : Module.finrank ℝ (B.slow 0).range=Module.finrank ℝ ((A.splitting S).slow 0).range := by
    rw [heS,←A.space_eq_range,A₀.rank,A.rank,hdS]
  have hdT' : Module.finrank ℝ (B.fast 0).range=Module.finrank ℝ ((Z.splitting T).slow 0).range := by
    rw [heT,←Z.space_eq_range,A₀.rank,Z.rank,hdT]
  apply CloseComplement.exists_matching (B.slow 0).range (B.fast 0).range
    ((A.splitting S).slow 0).range ((Z.splitting T).slow 0).range
    (B.referenceMatching 0) (B.referenceMatching_apply 0) hdS' hdT' hε hεhalf
  · simpa only [heS,←A.space_eq_range] using hcS
  · simpa only [heT,←Z.space_eq_range] using hcT
  · exact B.referenceMatching_inverse_norm 0 hs hf
  · exact hsmall
end SmoothObstruction.ShortBin

namespace SmoothObstruction.FiniteGreen
open Finset
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace Splitting
variable {A : Evolution E} (B : Splitting A)

namespace Terminal
variable {B} {n : ℕ} (C : B.Terminal (H:=H) n)

lemma trajectory_zero : C.trajectory (fun _ => 0) 0 0=fun _ => 0 := by
  funext t
  simp [trajectory,terminalValue,Evolution.forward,Evolution.backward]

end Terminal

end Splitting

namespace Matching
variable [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

omit [FiniteDimensional ℝ E] in
lemma correction_norm {k₁ k₂ : ℝ} (hk₁ : ‖C₁.kernel‖ ≤ k₁) (hk₂ : ‖C₂.kernel‖ ≤ k₂) :
    ‖correction C₁ C₂‖ ≤ k₁+k₂ := by
  have h₁ := (norm_nonneg _).trans hk₁
  have h₂ := (norm_nonneg _).trans hk₂
  apply (correction C₁ C₂).opNorm_le_bound (by positivity)
  intro x
  calc
    _ ≤ ‖C₁.kernel x.1‖+‖C₂.kernel x.2‖ := norm_sub_le _ _
    _ ≤ k₁*‖x.1‖+k₂*‖x.2‖ := by
      gcongr
      · exact (C₁.kernel.le_opNorm _).trans (mul_le_mul_of_nonneg_right hk₁ (norm_nonneg _))
      · exact (C₂.kernel.le_opNorm _).trans (mul_le_mul_of_nonneg_right hk₂ (norm_nonneg _))
    _ ≤ k₁*‖x‖+k₂*‖x‖ := by
      gcongr
      · exact norm_fst_le x
      · exact norm_snd_le x
    _ = _ := by ring

end Matching
end SmoothObstruction.FiniteGreen

namespace SmoothObstruction.FiniteGreen
open Finset
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

namespace Evolution
variable (A : Evolution E)
lemma forward_bound (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (a : E) {n t : ℕ}
    {G F : ℝ} (hG : 0≤G) (hF : 0≤F) (ht : t≤n) (ha : P 0 a=a)
    (hp : ∀ s u,s≤u → u≤n → ‖(A.map u s).comp (P s)‖ ≤ G)
    (hf : ∀ j<n,‖f j‖ ≤ F) :
    ‖A.forward P f a t‖ ≤ G*‖a‖+(n:ℝ)*G*F := by
  have hterm (s u : ℕ) (hsu : s≤u) (hu : u≤n) (v : E) :
      ‖A.map u s (P s v)‖ ≤ G*‖v‖ :=
    ((A.map u s).comp (P s)).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right (hp s u hsu hu) (norm_nonneg _))
  have hi : ‖A.map t 0 a‖ ≤ G*‖a‖ := by
    simpa only [ha] using hterm 0 t (by omega) ht a
  unfold forward
  calc
    _ ≤ ‖A.map t 0 a‖+‖∑ j∈range t,A.map t (j+1) (P (j+1) (f j))‖ := norm_add_le _ _
    _ ≤ G*‖a‖+∑ j∈range t,G*F := by
      gcongr
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro j hj
      have hjt := mem_range.mp hj
      exact (hterm (j+1) t (by omega) ht (f j)).trans
        (mul_le_mul_of_nonneg_left (hf j (by omega)) hG)
    _ ≤ _ := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      have htt : (t:ℝ)≤n := by exact_mod_cast ht
      nlinarith [mul_nonneg hG hF,mul_le_mul_of_nonneg_right htt (mul_nonneg hG hF)]

lemma backward_bound (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (c : E) {n t : ℕ}
    {G F : ℝ} (hG : 0≤G) (hF : 0≤F) (ht : t≤n) (hc : P n c=c)
    (hp : ∀ s u,s≤u → u≤n → ‖(A.map s u).comp (P u)‖ ≤ G)
    (hf : ∀ j<n,‖f j‖ ≤ F) :
    ‖A.backward P f c n t‖ ≤ G*‖c‖+(n:ℝ)*G*F := by
  have hterm (s u : ℕ) (hsu : s≤u) (hu : u≤n) (v : E) :
      ‖A.map s u (P u v)‖ ≤ G*‖v‖ :=
    ((A.map s u).comp (P u)).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right (hp s u hsu hu) (norm_nonneg _))
  have hi : ‖A.map t n c‖ ≤ G*‖c‖ := by
    simpa only [hc] using hterm t n ht le_rfl c
  unfold backward
  calc
    _ ≤ ‖A.map t n c‖+‖∑ j∈Ico t n,A.map t (j+1) (P (j+1) (f j))‖ := norm_sub_le _ _
    _ ≤ G*‖c‖+∑ j∈Ico t n,G*F := by
      gcongr
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro j hj
      have hjt := mem_Ico.mp hj
      exact (hterm t (j+1) (by omega) (by omega) (f j)).trans
        (mul_le_mul_of_nonneg_left (hf j hjt.2) hG)
    _ ≤ _ := by
      simp only [sum_const,Nat.card_Ico,nsmul_eq_mul]
      have htt : ((n-t:ℕ):ℝ)≤n := by exact_mod_cast Nat.sub_le n t
      nlinarith [mul_nonneg hG hF,mul_le_mul_of_nonneg_right htt (mul_nonneg hG hF)]
end Evolution

namespace Splitting.Terminal
variable {A : Evolution E} {B : Splitting A} {n : ℕ} (C : B.Terminal (H:=H) n)

/-- A uniform half-orbit estimate. A polynomial factor in n is harmless
under the source's log(n+1)≤bn floor, but is explicitly retained here. -/
lemma trajectory_bound (f : ℕ → E) (a : E) (h : H) {G F : ℝ}
    (hG : 1≤G) (hF : 0≤F) (ha : B.slow 0 a=a)
    (hs : ∀ s u,s≤u → u≤n → ‖(A.map u s).comp (B.slow s)‖ ≤ G)
    (hb : ∀ s u,s≤u → u≤n → ‖(A.map s u).comp (B.fast u)‖ ≤ G)
    (hJ : ‖C.J‖ ≤ G) (hP : ‖C.P‖ ≤ G)
    (hf : ∀ j<n,‖f j‖ ≤ F) (hh : ‖h‖ ≤ F) {t : ℕ} (ht : t≤n) :
    ‖C.trajectory f a h t‖ ≤ (G+G^4)*‖a‖+(2*G+G^4)*(n:ℝ)*F+G^2*F := by
  have hGn : 0≤G := by linarith
  let R := G*‖a‖+(n:ℝ)*G*F
  have hfor (u : ℕ) (hu : u≤n) : ‖A.forward B.slow f a u‖ ≤ R :=
    A.forward_bound B.slow f a hGn hF hu ha hs hf
  have hc : ‖C.terminalValue f a h‖ ≤ G*(F+G*R) := by
    apply C.J.le_opNorm _ |>.trans
    apply mul_le_mul hJ _ (norm_nonneg _) hGn
    apply (norm_sub_le _ _).trans
    apply add_le_add hh
    exact (C.P.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hfor n le_rfl) hGn))
  have hbak := A.backward_bound B.fast f (C.terminalValue f a h) hGn hF ht (C.fast_J _) hb hf
  unfold trajectory
  calc
    _ ≤ ‖A.forward B.slow f a t‖+‖A.backward B.fast f (C.terminalValue f a h) n t‖ := norm_add_le _ _
    _ ≤ R+(G*(G*(F+G*R))+(n:ℝ)*G*F) :=
      add_le_add (hfor t ht) (hbak.trans (add_le_add (mul_le_mul_of_nonneg_left hc hGn) le_rfl))
    _ = _ := by dsimp only [R]; ring

end Splitting.Terminal
end SmoothObstruction.FiniteGreen

namespace SmoothObstruction.FiniteGreen.Matching
open Finset
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

/-- A quantitative bound for every genuine two-half boundary solution.
The explicit polynomial is retained; the source's logarithmic time floor
later absorbs it into the subexponential factor. -/
theorem solution_bound (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E)) {U K F : ℝ}
    (hU : 1≤U) (hK : ‖L.symm.toContinuousLinearMap‖≤K) (hF : 0≤F)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hs₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map u s).comp (B₁.slow s)‖≤U)
    (hb₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map s u).comp (B₁.fast u)‖≤U)
    (hs₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map u s).comp (B₂.slow s)‖≤U)
    (hb₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map s u).comp (B₂.fast u)‖≤U)
    (hJ₁ : ‖C₁.J‖≤U) (hP₁ : ‖C₁.P‖≤U)
    (hJ₂ : ‖C₂.J‖≤U) (hP₂ : ‖C₂.P‖≤U)
    (f₁ f₂ w₁ w₂ : ℕ → E) (h₁ : H) (h₂ : G) (m : E)
    (hf₁ : ∀ j<n₁,‖f₁ j‖≤F) (hf₂ : ∀ j<n₂,‖f₂ j‖≤F)
    (hh₁ : ‖h₁‖≤F) (hh₂ : ‖h₂‖≤F) (hm : ‖m‖≤F)
    (hw₁ : ∀ t<n₁,w₁ (t+1)=A₁.map (t+1) t (w₁ t)+f₁ t)
    (hw₂ : ∀ t<n₂,w₂ (t+1)=A₂.map (t+1) t (w₂ t)+f₂ t)
    (he₁ : C₁.P (w₁ n₁)=h₁) (he₂ : C₂.P (w₂ n₂)=h₂)
    (hmatch : w₁ 0-w₂ 0=m) :
    let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
    let Q := (U+U^4)*(2*K)*(1+2*D)+D
    (∀ t≤n₁,‖w₁ t‖≤Q*F) ∧ (∀ t≤n₂,‖w₂ t‖≤Q*F) := by
  have hUn : 0≤U := by linarith
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
  have hD : 0≤D := by dsimp [D]; positivity
  let M := BoundaryNeumann.perturb L (correction C₁ C₂) (hsmall.trans_lt (by norm_num))
  have hMi : ‖M.symm.toContinuousLinearMap‖≤2*K :=
    BoundaryNeumann.inverse_norm L (correction C₁ C₂) hK hsmall
  let b₁ : B₁.initialSpace := ⟨B₁.slow 0 (w₁ 0),⟨w₁ 0,rfl⟩⟩
  let b₂ : B₂.initialSpace := ⟨B₂.slow 0 (w₂ 0),⟨w₂ 0,rfl⟩⟩
  have hv₁ := C₁.trajectory_unique f₁ b₁ (B₁.slow_initial b₁) h₁ w₁ hw₁ rfl he₁
  have hv₂ := C₂.trajectory_unique f₂ b₂ (B₂.slow_initial b₂) h₂ w₂ hw₂ rfl he₂
  let q₁ := C₁.trajectory f₁ 0 h₁ 0
  let q₂ := C₂.trajectory f₂ 0 h₂ 0
  have hn₁ : (n₁:ℝ)≤(n₁+n₂:ℕ) := by exact_mod_cast Nat.le_add_right n₁ n₂
  have hn₂ : (n₂:ℝ)≤(n₁+n₂:ℕ) := by exact_mod_cast Nat.le_add_left n₂ n₁
  have hq₁ : ‖q₁‖≤D*F := by
    have h := C₁.trajectory_bound f₁ 0 h₁ hU hF (by simp) hs₁ hb₁ hJ₁ hP₁ hf₁ hh₁ (Nat.zero_le n₁)
    simp only [norm_zero,mul_zero,zero_add] at h
    apply h.trans
    dsimp only [D]
    calc
      _ ≤ (2*U+U^4)*((n₁+n₂:ℕ):ℝ)*F+U^2*F := by gcongr
      _ = _ := by ring
  have hq₂ : ‖q₂‖≤D*F := by
    have h := C₂.trajectory_bound f₂ 0 h₂ hU hF (by simp) hs₂ hb₂ hJ₂ hP₂ hf₂ hh₂ (Nat.zero_le n₂)
    simp only [norm_zero,mul_zero,zero_add] at h
    apply h.trans
    dsimp only [D]
    calc
      _ ≤ (2*U+U^4)*((n₁+n₂:ℕ):ℝ)*F+U^2*F := by gcongr
      _ = _ := by ring
  have hMb : M (b₁,b₂)=m-q₁+q₂ := by
    rw [BoundaryNeumann.perturb_apply,hL,correction_apply]
    rw [hv₁ 0 (by omega),hv₂ 0 (by omega),
      C₁.trajectory_initial _ _ (B₁.slow_initial _) _,
      C₂.trajectory_initial _ _ (B₂.slow_initial _) _] at hmatch
    change (b₁:E)-(b₂:E)+(C₁.kernel b₁-C₂.kernel b₂)=m-q₁+q₂
    change (b₁:E)+C₁.kernel b₁+q₁-((b₂:E)+C₂.kernel b₂+q₂)=m at hmatch
    calc
      _ = ((b₁:E)+C₁.kernel b₁+q₁-((b₂:E)+C₂.kernel b₂+q₂))-q₁+q₂ := by abel
      _ = _ := by rw [hmatch]
  have hbn : ‖(b₁,b₂)‖≤(2*K)*(1+2*D)*F := by
    have hb : (b₁,b₂)=M.symm (m-q₁+q₂) := ((M.symm_apply_eq).mpr hMb.symm).symm
    rw [hb]
    calc
      _ ≤ (2*K)*‖m-q₁+q₂‖ := (M.symm.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hMi (norm_nonneg _))
      _ ≤ (2*K)*(F+D*F+D*F) := mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hm hq₁)) hq₂))
        (by positivity)
      _ = _ := by ring
  have hbn₁ : ‖(b₁:E)‖≤(2*K)*(1+2*D)*F := (norm_fst_le (b₁,b₂)).trans hbn
  have hbn₂ : ‖(b₂:E)‖≤(2*K)*(1+2*D)*F := (norm_snd_le (b₁,b₂)).trans hbn
  constructor
  · intro t ht
    rw [hv₁ t ht]
    apply (C₁.trajectory_bound f₁ b₁ h₁ hU hF (B₁.slow_initial _) hs₁ hb₁ hJ₁ hP₁ hf₁ hh₁ ht).trans
    change _≤((U+U^4)*(2*K)*(1+2*D)+D)*F
    calc
      _ ≤ (U+U^4)*((2*K)*(1+2*D)*F)+(2*U+U^4)*((n₁+n₂:ℕ):ℝ)*F+U^2*F := by gcongr
      _ = _ := by dsimp only [D]; ring
  · intro t ht
    rw [hv₂ t ht]
    apply (C₂.trajectory_bound f₂ b₂ h₂ hU hF (B₂.slow_initial _) hs₂ hb₂ hJ₂ hP₂ hf₂ hh₂ ht).trans
    change _≤((U+U^4)*(2*K)*(1+2*D)+D)*F
    calc
      _ ≤ (U+U^4)*((2*K)*(1+2*D)*F)+(2*U+U^4)*((n₁+n₂:ℕ):ℝ)*F+U^2*F := by gcongr
      _ = _ := by dsimp only [D]; ring

end SmoothObstruction.FiniteGreen.Matching

namespace SmoothObstruction.FiniteGreen.Matching
open Finset
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

theorem boundary_inverse_norm (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E)) {U K : ℝ}
    (hU : 1≤U) (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hs₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map u s).comp (B₁.slow s)‖≤U)
    (hb₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map s u).comp (B₁.fast u)‖≤U)
    (hs₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map u s).comp (B₂.slow s)‖≤U)
    (hb₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map s u).comp (B₂.fast u)‖≤U)
    (hJ₁ : ‖C₁.J‖≤U) (hP₁ : ‖C₁.P‖≤U)
    (hJ₂ : ‖C₂.J‖≤U) (hP₂ : ‖C₂.P‖≤U) :
    let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
    ‖(boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))).symm.toContinuousLinearMap‖≤
      (U+U^4)*(2*K)*(1+2*D)+D := by
  let V := boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))
  let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
  let Q := (U+U^4)*(2*K)*(1+2*D)+D
  have hUn : 0≤U := by linarith
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  have hQ : 0≤Q := by dsimp [Q,D]; positivity
  change ‖V.symm.toContinuousLinearMap‖≤Q
  apply V.symm.toContinuousLinearMap.opNorm_le_bound hQ
  intro d
  let w := V.symm d
  have hw : boundary C₁ C₂ w=d := V.apply_symm_apply d
  have hw₁ : ∀ t<n₁,extend w.1 (t+1)=A₁.map (t+1) t (extend w.1 t)+extend d.1 t := by
    intro t ht
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.1 ⟨t,ht⟩) hw
    change w.1 ⟨t+1,by omega⟩-A₁.map (t+1) t (w.1 ⟨t,by omega⟩)=d.1 ⟨t,ht⟩ at h
    simp only [extend,dite_eq_left (show t+1<n₁+1 by omega),dite_eq_left (show t<n₁+1 by omega),dite_eq_left ht]
    rw [←h]; abel
  have hw₂ : ∀ t<n₂,extend w.2 (t+1)=A₂.map (t+1) t (extend w.2 t)+extend d.2.1 t := by
    intro t ht
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.1 ⟨t,ht⟩) hw
    change w.2 ⟨t+1,by omega⟩-A₂.map (t+1) t (w.2 ⟨t,by omega⟩)=d.2.1 ⟨t,ht⟩ at h
    simp only [extend,dite_eq_left (show t+1<n₂+1 by omega),dite_eq_left (show t<n₂+1 by omega),dite_eq_left ht]
    rw [←h]; abel
  have he₁ : C₁.P (extend w.1 n₁)=d.2.2.2.1 := by
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.1) hw
    change C₁.P (w.1 (Fin.last n₁))=d.2.2.2.1 at h
    change C₁.P (extend w.1 (Fin.last n₁))=d.2.2.2.1
    rw [extend_apply]; exact h
  have he₂ : C₂.P (extend w.2 n₂)=d.2.2.2.2 := by
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.2) hw
    change C₂.P (w.2 (Fin.last n₂))=d.2.2.2.2 at h
    change C₂.P (extend w.2 (Fin.last n₂))=d.2.2.2.2
    rw [extend_apply]; exact h
  have hm : extend w.1 0-extend w.2 0=d.2.2.1 := by
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.1) hw
    change w.1 0-w.2 0=d.2.2.1 at h
    change extend w.1 (0 : Fin (n₁+1))-extend w.2 (0 : Fin (n₂+1))=d.2.2.1
    rw [extend_apply,extend_apply]; exact h
  have hf₁ : ∀ j<n₁,‖extend d.1 j‖≤‖d‖ := by
    intro j hj
    rw [extend,dite_eq_left hj]
    exact (norm_le_pi_norm d.1 ⟨j,hj⟩).trans (norm_fst_le d)
  have hf₂ : ∀ j<n₂,‖extend d.2.1 j‖≤‖d‖ := by
    intro j hj
    rw [extend,dite_eq_left hj]
    exact (norm_le_pi_norm d.2.1 ⟨j,hj⟩).trans ((norm_fst_le d.2).trans (norm_snd_le d))
  have hh₁ : ‖d.2.2.2.1‖≤‖d‖ := (norm_fst_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans (norm_snd_le d)))
  have hh₂ : ‖d.2.2.2.2‖≤‖d‖ := (norm_snd_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans (norm_snd_le d)))
  have hmid : ‖d.2.2.1‖≤‖d‖ := (norm_fst_le _).trans ((norm_snd_le _).trans (norm_snd_le d))
  obtain ⟨h₁,h₂⟩ := solution_bound C₁ C₂ L hL hU hK (norm_nonneg d) hsmall
    hs₁ hb₁ hs₂ hb₂ hJ₁ hP₁ hJ₂ hP₂
    (extend d.1) (extend d.2.1) (extend w.1) (extend w.2)
    d.2.2.2.1 d.2.2.2.2 d.2.2.1 hf₁ hf₂ hh₁ hh₂ hmid hw₁ hw₂ he₁ he₂ hm
  change ‖w‖≤Q*‖d‖
  rw [Prod.norm_def,max_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hQ (norm_nonneg d))).mpr
    intro t
    simpa only [extend_apply] using h₁ t (by omega)
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hQ (norm_nonneg d))).mpr
    intro t
    simpa only [extend_apply] using h₂ t (by omega)

end SmoothObstruction.FiniteGreen.Matching

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

namespace SmoothObstruction.JacobianDomination
open MeasureTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Change of variables on the retained set itself. A density lower bound
on the actual Jacobian gives domination without normalizing the retained
measure. Global injectivity is essential here. -/
theorem map_density_restrict_le (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (d : E → ℝ≥0∞) (s : Set E) (hs : MeasurableSet s)
    (f : E → E) (hf : Measurable f) (J : E → E →L[ℝ] E)
    (hJ : ∀ x∈s,HasFDerivWithinAt f (J x) s x) (hinj : InjOn f s)
    (C : ℝ≥0∞) (hC : C≠∞)
    (hlower : ∀ x∈s,d x ≤ C*(ENNReal.ofReal |(J x).det| *d (f x))) :
    ((μ.withDensity d).restrict s).map f ≤ C • μ.withDensity d := by
  apply Measure.le_iff.mpr
  intro t ht
  rw [Measure.map_apply hf ht,Measure.restrict_apply (hf ht),
    withDensity_apply _ ((hf ht).inter hs),Measure.smul_apply,
    withDensity_apply _ ht,smul_eq_mul]
  let a := f ⁻¹' t ∩ s
  have ha : MeasurableSet a := (hf ht).inter hs
  have hsub : f '' a ⊆ t := by rintro y ⟨x,hx,rfl⟩; exact hx.1
  calc
    (∫⁻ x in a,d x ∂μ) ≤ ∫⁻ x in a,C*(ENNReal.ofReal |(J x).det| *d (f x)) ∂μ := by
      apply setLIntegral_mono' ha
      intro x hx
      exact hlower x hx.2
    _ = C*(∫⁻ x in a,ENNReal.ofReal |(J x).det| *d (f x) ∂μ) :=
      lintegral_const_mul' C _ hC
    _ = C*(∫⁻ y in f '' a,d y ∂μ) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ ha
        (fun x hx => (hJ x hx.2).mono inter_subset_right) (hinj.mono inter_subset_right)]
    _ ≤ C*(∫⁻ y in t,d y ∂μ) := by
      gcongr

end SmoothObstruction.JacobianDomination

namespace SmoothObstruction.JacobianDomination
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Agreement with genuine local derivative branches on relative retained
neighborhoods gives a measurable total extension and the original retained-law
domination. The within-set change-of-variables theorem avoids any assumption
of measurable frame witnesses or measurable choices of local branches. -/
theorem local_branches_domination (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (d : E → ℝ≥0∞) (s : Set E) (hs : MeasurableSet s)
    (f : E → E) (J : E → E →L[ℝ] E)
    (hlocal : ∀ x∈s,∃ g : E → E,HasFDerivAt g (J x) x ∧ g =ᶠ[𝓝[s] x] f)
    (hinj : InjOn f s) (C : ℝ≥0∞) (hC : C≠∞)
    (hlower : ∀ x∈s,d x≤C*(ENNReal.ofReal |(J x).det| *d (f x))) :
    ∃ F : E → E,Measurable F ∧ EqOn F f s ∧
      ((μ.withDensity d).restrict s).map F≤C • μ.withDensity d := by
  classical
  have hder : ∀ x∈s,HasFDerivWithinAt f (J x) s x := by
    intro x hx
    obtain ⟨g,hg,he⟩ := hlocal x hx
    exact hg.hasFDerivWithinAt.congr_of_eventuallyEq he.symm (he.eq_of_nhdsWithin hx).symm
  have hc : ContinuousOn f s := fun x hx => (hder x hx).continuousWithinAt
  let F := s.piecewise f (fun _ => 0)
  have hF : Measurable F := hc.measurable_piecewise continuous_const.continuousOn hs
  have he : EqOn F f s := fun x hx => ite_eq_left hx
  refine ⟨F,hF,he,map_density_restrict_le μ d s hs F hF J
    (fun x hx => (hder x hx).congr' he hx) (hinj.congr he.symm) C hC ?_⟩
  intro x hx
  rw [he hx]
  exact hlower x hx
end SmoothObstruction.JacobianDomination

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

/-- A local coordinate change transfers a genuine retained-set smooth branch
estimate back to the original measure. This provides a measurable extension
in the original space without an assumed globally measurable frame choice.
No retained mass is normalized, and the original carrier may be only Borel. -/
theorem local_domination (μ : Measure X) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (d : E → ℝ≥0∞)
    (Q G : Set X) (hQ : μ Qᶜ = 0) (hGQ : G ⊆ Q) (hG : MeasurableSet G)
    (e : X → E) (r : E → X) (he : Measurable e) (hr : Measurable r)
    (hleft : ∀ x∈Q,r (e x)=x) (hcoords : μ.map e=m.withDensity d)
    (f : X → X) (hfQ : MapsTo f G Q)
    (φ : E → E) (J : E → E →L[ℝ] E)
    (hcompat : ∀ x∈G,φ (e x)=e (f x))
    (hlocal : ∀ u∈coordinateSet e r G,
      ∃ g : E → E, HasFDerivAt g (J u) u ∧
        g =ᶠ[𝓝[coordinateSet e r G] u] φ)
    (hinj : InjOn φ (coordinateSet e r G)) (C : ℝ≥0∞) (hC : C≠∞)
    (hlower : ∀ u∈coordinateSet e r G,
      d u≤C*(ENNReal.ofReal |(J u).det| * d (φ u))) :
    ∃ F : X → X,Measurable F ∧ EqOn F f G ∧
      (μ.restrict G).map F≤C • μ := by
  have hs := measurable_coordinateSet e r he hr G hG
  obtain ⟨ψ,hψ,hψφ,hdom⟩ := JacobianDomination.local_branches_domination
    m d (coordinateSet e r G) hs φ J hlocal hinj C hC hlower
  let F : X → X := r ∘ ψ ∘ e
  have hF : Measurable F := hr.comp (hψ.comp he)
  have hrecover : (μ.map e).map r=μ := by
    rw [Measure.map_map hr he]
    have hh : r ∘ e =ᵐ[μ] id := by
      filter_upwards [show ∀ᵐ x ∂μ,x∈Q from hQ] with x hx
      exact hleft x hx
    rw [Measure.map_congr hh,Measure.map_id]
  refine ⟨F,hF,?_,?_⟩
  · intro x hx
    have hx' : e x∈coordinateSet e r G := by
      rw [coordinateSet_eq_image e r G (fun y hy => hleft y (hGQ hy))]
      exact mem_image_of_mem e hx
    change r (ψ (e x))=f x
    rw [hψφ hx',hcompat x hx,hleft (f x) (hfQ hx)]
  · have h := Measure.map_mono hdom hr
    rw [←hcoords,Measure.map_smul C,hrecover] at h
    rw [←map_restrict_coordinateSet μ Q G hQ e r he hr hG hleft] at h
    simpa only [Measure.map_map hr hψ,Measure.map_map (hr.comp hψ) he,
      Function.comp_assoc,F] using h
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
-- module Solutions.OAIQ5_T3.SmoothObstruction_NonlinearMatching
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

namespace SmoothObstruction.SmoothRemainder
open Set Metric
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual, rather than hypothesized, nonlinear remainder has the
small Lipschitz constant needed by the boundary contraction. -/
theorem remainder_lipschitz (f : E → F) {x : E} {δ C : ℝ}
    (hC : 0≤C)
    (hf : ∀ y∈closedBall x δ,DifferentiableAt ℝ f y)
    (hder : ∀ y∈closedBall x δ,‖fderiv ℝ f y-fderiv ℝ f x‖≤C*‖y-x‖)
    {u v : E} (hu : ‖u‖≤δ) (hv : ‖v‖≤δ) :
    ‖remainder f x u-remainder f x v‖≤C*δ*‖u-v‖ := by
  have hmem (w : E) (hw : w∈closedBall (0 : E) δ) : x+w∈closedBall x δ := by
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hw
  have hr (w : E) (hw : w∈closedBall (0 : E) δ) : HasFDerivWithinAt
      (remainder f x) (fderiv ℝ f (x+w)-fderiv ℝ f x) (closedBall (0 : E) δ) w := by
    have h := (((hf (x+w) (hmem w hw)).hasFDerivAt.comp w
      ((hasFDerivAt_id w).const_add x)).sub_const (f x)).sub
        ((fderiv ℝ f x).hasFDerivAt)
    change HasFDerivAt (remainder f x) _ w at h
    simpa only [ContinuousLinearMap.comp_id] using h.hasFDerivWithinAt
  have hb (w : E) (hw : w∈closedBall (0 : E) δ) :
      ‖fderiv ℝ f (x+w)-fderiv ℝ f x‖≤C*δ := by
    have hh := hder _ (hmem w hw)
    simp only [add_sub_cancel_left] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_zero_right] using hw) hC)
  exact (convex_closedBall (0 : E) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le hr hb
    (by simpa only [mem_closedBall,dist_zero_right] using hv)
    (by simpa only [mem_closedBall,dist_zero_right] using hu)

end SmoothObstruction.SmoothRemainder

namespace SmoothObstruction.ArrayRemainder
open Set Metric
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H]
  [NormedAddCommGroup G]
  {n₁ n₂ : ℕ}

theorem residual_lipschitz (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin n₁ → E) (x₂ : Fin n₂ → E) {C δ : ℝ} (hC : 0≤C) (hδ : 0≤δ)
    (h₁ : ∀ t,∀ u v : E,‖u‖≤δ → ‖v‖≤δ →
      ‖SmoothRemainder.remainder (f₁ t) (x₁ t) u-
        SmoothRemainder.remainder (f₁ t) (x₁ t) v‖≤C*δ*‖u-v‖)
    (h₂ : ∀ t,∀ u v : E,‖u‖≤δ → ‖v‖≤δ →
      ‖SmoothRemainder.remainder (f₂ t) (x₂ t) u-
        SmoothRemainder.remainder (f₂ t) (x₂ t) v‖≤C*δ*‖u-v‖)
    {u v : Paths E n₁ n₂} (hu : ‖u‖≤δ) (hv : ‖v‖≤δ) :
    ‖residual (H:=H) (G:=G) f₁ f₂ x₁ x₂ u-residual f₁ f₂ x₁ x₂ v‖≤C*δ*‖u-v‖ := by
  have hpos : 0≤C*δ*‖u-v‖ := by positivity
  have hu₁ (t : Fin (n₁+1)) : ‖u.1 t‖≤δ := (norm_le_pi_norm _ t).trans ((norm_fst_le u).trans hu)
  have hv₁ (t : Fin (n₁+1)) : ‖v.1 t‖≤δ := (norm_le_pi_norm _ t).trans ((norm_fst_le v).trans hv)
  have hu₂ (t : Fin (n₂+1)) : ‖u.2 t‖≤δ := (norm_le_pi_norm _ t).trans ((norm_snd_le u).trans hu)
  have hv₂ (t : Fin (n₂+1)) : ‖v.2 t‖≤δ := (norm_le_pi_norm _ t).trans ((norm_snd_le v).trans hv)
  rw [Prod.norm_def,max_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg hpos).mpr
    intro t
    apply (h₁ t _ _ (hu₁ t.castSucc) (hv₁ t.castSucc)).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hδ)
    exact (norm_le_pi_norm (u.1-v.1) t.castSucc).trans (norm_fst_le (u-v))
  · rw [Prod.norm_def,max_le_iff]
    constructor
    · apply (pi_norm_le_iff_of_nonneg hpos).mpr
      intro t
      apply (h₂ t _ _ (hu₂ t.castSucc) (hv₂ t.castSucc)).trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hδ)
      exact (norm_le_pi_norm (u.2-v.2) t.castSucc).trans (norm_snd_le (u-v))
    · simpa only [residual,Prod.snd_sub,Prod.snd,sub_self,norm_zero] using hpos

/-- One common compact-domain Taylor estimate gives a residual Lipschitz
constant independent of the number of orbit steps. -/
theorem residual_from_derivative (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin n₁ → E) (x₂ : Fin n₂ → E) {C δ : ℝ} (hC : 0≤C) (hδ : 0≤δ)
    (hd₁ : ∀ t,∀ y∈closedBall (x₁ t) δ,DifferentiableAt ℝ (f₁ t) y)
    (hd₂ : ∀ t,∀ y∈closedBall (x₂ t) δ,DifferentiableAt ℝ (f₂ t) y)
    (h₁ : ∀ t,∀ y∈closedBall (x₁ t) δ,‖fderiv ℝ (f₁ t) y-fderiv ℝ (f₁ t) (x₁ t)‖≤C*‖y-x₁ t‖)
    (h₂ : ∀ t,∀ y∈closedBall (x₂ t) δ,‖fderiv ℝ (f₂ t) y-fderiv ℝ (f₂ t) (x₂ t)‖≤C*‖y-x₂ t‖)
    {u v : Paths E n₁ n₂} (hu : ‖u‖≤δ) (hv : ‖v‖≤δ) :
    ‖residual (H:=H) (G:=G) f₁ f₂ x₁ x₂ u-residual f₁ f₂ x₁ x₂ v‖≤C*δ*‖u-v‖ :=
  residual_lipschitz f₁ f₂ x₁ x₂ hC hδ
    (fun t _ _ hu hv => SmoothRemainder.remainder_lipschitz (f₁ t) hC (hd₁ t) (h₁ t) hu hv)
    (fun t _ _ hu hv => SmoothRemainder.remainder_lipschitz (f₂ t) hC (hd₂ t) (h₂ t) hu hv) hu hv

/-- The nonlinear recurrence is exactly the actual coordinate orbit equation,
not just a formal shadowing sequence. -/
theorem genuine_step (f : E → E) (x x' v v' : E) (hbase : f x=x')
    (heq : v'-(fderiv ℝ f x) v=SmoothRemainder.remainder f x v) :
    f (x+v)=x'+v' := by
  unfold SmoothRemainder.remainder at heq
  rw [hbase] at heq
  have h := congrArg (fun z => z+(fderiv ℝ f x) v) heq
  simp only [sub_add_cancel] at h
  rw [h]
  abel

end SmoothObstruction.ArrayRemainder

namespace SmoothObstruction.NonlinearBoundary
open Metric Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The boundary-inverse contraction from source section4. The ambient
space can be a finite array with its supremum norm: no step-count factor
is introduced. Uniqueness is on the larger radius δ, not just the sharp
shadowing radius. -/
theorem solve (L : E ≃L[ℝ] F) (R : E → F) (a : F)
    {Q C r δ : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hr : 0 ≤ r) (hδ : 0 < δ)
    (hL : ‖L.symm.toContinuousLinearMap‖ ≤ Q)
    (ha : ‖a‖ ≤ C*r) (hR0 : R 0 = 0)
    (hR : ∀ u ∈ closedBall (0 : E) δ, ∀ v ∈ closedBall (0 : E) δ,
      ‖R u-R v‖ ≤ C*δ*‖u-v‖)
    (hsmall : Q*C*δ ≤ 1/4) (hdata : Q*C*r ≤ δ/4) :
    ∃ v : E, ‖v‖ ≤ δ/2 ∧ ‖v‖ ≤ 2*C*Q*r ∧ L v = a+R v ∧
      ∀ u : E, ‖u‖ ≤ δ → L u = a+R u → u=v := by
  let f : E → E := fun v => L.symm (a+R v)
  have hz : (0 : E) ∈ closedBall (0 : E) δ := by simpa using hδ.le
  have hbound (u : E) (hu : u ∈ closedBall (0 : E) δ) :
      ‖f u‖ ≤ Q*C*r+(1/4:ℝ)*‖u‖ := by
    have hRu : ‖R u‖ ≤ C*δ*‖u‖ := by simpa only [hR0,sub_zero] using hR u hu 0 hz
    calc
      _ ≤ Q*‖a+R u‖ := (L.symm.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
      _ ≤ Q*(C*r+C*δ*‖u‖) := mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add ha hRu)) hQ
      _ = Q*C*r+(Q*C*δ)*‖u‖ := by ring
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)) _
  have hmap : MapsTo f (closedBall (0 : E) δ) (closedBall (0 : E) δ) := by
    intro u hu
    rw [mem_closedBall,dist_zero_right]
    have hu' : ‖u‖ ≤ δ := by simpa only [mem_closedBall,dist_zero_right] using hu
    have hb := hbound u hu
    linarith
  have hdist (u v : E) (hu : u ∈ closedBall (0 : E) δ) (hv : v ∈ closedBall (0 : E) δ) :
      dist (f u) (f v) ≤ (1/4:ℝ)*dist u v := by
    simp only [dist_eq_norm,f,←map_sub,add_sub_add_left_eq_sub]
    calc
      _ ≤ Q*‖R u-R v‖ := (L.symm.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
      _ ≤ Q*(C*δ*‖u-v‖) := mul_le_mul_of_nonneg_left (hR u hu v hv) hQ
      _ = (Q*C*δ)*‖u-v‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hcontract : ContractingWith (1/4 : NNReal) (hmap.restrict f _ _) := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    exact hdist u v u.property v.property
  obtain ⟨v,hv,hfix,-, -⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hcontract hz (edist_ne_top _ _)
  have hvnorm : ‖v‖ ≤ δ := by simpa only [mem_closedBall,dist_zero_right] using hv
  have hb := hbound v hv
  have hfv : f v=v := hfix
  rw [hfv] at hb
  refine ⟨v,by linarith,?_,?_,?_⟩
  · have hp : 0 ≤ Q*C*r := mul_nonneg (mul_nonneg hQ hC) hr
    nlinarith
  · have hh := congrArg L hfv
    simpa only [f,L.apply_symm_apply] using hh.symm
  · intro u hu heq
    have humem : u ∈ closedBall (0 : E) δ := by simpa only [mem_closedBall,dist_zero_right] using hu
    have hfu : f u=u := by dsimp [f]; rw [←heq,L.symm_apply_apply]
    have hh := hdist u v humem hv
    rw [hfu,hfv] at hh
    exact dist_eq_zero.mp (by linarith [dist_nonneg (x:=u) (y:=v)])

omit [CompleteSpace E] in
/-- The nonlinear correction differs quadratically from the linear
solution, with the exact inverse cost. This is the source estimate used
for ideal coordinate exchange, once the sharp norm bound is inserted. -/
theorem nonlinear_linear_error (L : E ≃L[ℝ] F) {R : E → F} {a : F}
    {v : E} {Q C : ℝ} (hL : ‖L.symm.toContinuousLinearMap‖ ≤ Q)
    (_hC : 0 ≤ C) (hR : ‖R v‖ ≤ C*‖v‖^2) (heq : L v=a+R v) :
    ‖v-L.symm a‖ ≤ Q*C*‖v‖^2 := by
  have hQ : 0 ≤ Q := (norm_nonneg _).trans hL
  have hv : v=L.symm (a+R v) := by rw [←heq,L.symm_apply_apply]
  calc
    _ = ‖L.symm (a+R v)-L.symm a‖ := congrArg (fun w => ‖w-L.symm a‖) hv
    _ = ‖L.symm (R v)‖ := by rw [map_add,add_sub_cancel_left]
    _ ≤ Q*‖R v‖ := (L.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
    _ ≤ Q*(C*‖v‖^2) := mul_le_mul_of_nonneg_left hR hQ
    _ = _ := by ring
end SmoothObstruction.NonlinearBoundary

namespace SmoothObstruction.FiniteGreen.Matching
open Set Metric
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

/-- The finite boundary inverse and actual Taylor residual yield a genuine
pair of nonlinear coordinate orbits, with a common middle point. All
terminal equations remain exact. The derivative and propagation estimates
are precisely the finite-window inputs, not the desired orbit conclusion. -/
theorem nonlinear_orbits_unique (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E)) {U K C r δ : ℝ}
    (hU : 1≤U) (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hs₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map u s).comp (B₁.slow s)‖≤U)
    (hb₁ : ∀ s u,s≤u → u≤n₁ → ‖(A₁.map s u).comp (B₁.fast u)‖≤U)
    (hs₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map u s).comp (B₂.slow s)‖≤U)
    (hb₂ : ∀ s u,s≤u → u≤n₂ → ‖(A₂.map s u).comp (B₂.fast u)‖≤U)
    (hJ₁ : ‖C₁.J‖≤U) (hP₁ : ‖C₁.P‖≤U)
    (hJ₂ : ‖C₂.J‖≤U) (hP₂ : ‖C₂.P‖≤U)
    (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin (n₁+1) → E) (x₂ : Fin (n₂+1) → E)
    (hx₁ : ∀ t,f₁ t (x₁ t.castSucc)=x₁ t.succ)
    (hx₂ : ∀ t,f₂ t (x₂ t.castSucc)=x₂ t.succ)
    (hA₁ : ∀ t : Fin n₁,fderiv ℝ (f₁ t) (x₁ t.castSucc)=A₁.map (t+1) t)
    (hA₂ : ∀ t : Fin n₂,fderiv ℝ (f₂ t) (x₂ t.castSucc)=A₂.map (t+1) t)
    (hC : 0≤C) (hr : 0 ≤ r) (hδ : 0<δ)
    (hd₁ : ∀ t,∀ y∈closedBall (x₁ t.castSucc) δ,DifferentiableAt ℝ (f₁ t) y)
    (hd₂ : ∀ t,∀ y∈closedBall (x₂ t.castSucc) δ,DifferentiableAt ℝ (f₂ t) y)
    (hder₁ : ∀ t,∀ y∈closedBall (x₁ t.castSucc) δ,
      ‖fderiv ℝ (f₁ t) y-fderiv ℝ (f₁ t) (x₁ t.castSucc)‖≤C*‖y-x₁ t.castSucc‖)
    (hder₂ : ∀ t,∀ y∈closedBall (x₂ t.castSucc) δ,
      ‖fderiv ℝ (f₂ t) y-fderiv ℝ (f₂ t) (x₂ t.castSucc)‖≤C*‖y-x₂ t.castSucc‖)
    (hnear : ‖x₂ 0-x₁ 0‖≤C*r)
    (hcontract : let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*δ≤1/4)
    (hdata : let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*r≤δ/4) :
    let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
    let Q := (U+U^4)*(2*K)*(1+2*D)+D
    ∃ v : Paths E n₁ n₂,‖v‖≤δ/2 ∧ ‖v‖≤2*C*Q*r ∧
      (∀ t,f₁ t (x₁ t.castSucc+v.1 t.castSucc)=x₁ t.succ+v.1 t.succ) ∧
      (∀ t,f₂ t (x₂ t.castSucc+v.2 t.castSucc)=x₂ t.succ+v.2 t.succ) ∧
      x₁ 0+v.1 0=x₂ 0+v.2 0 ∧
      C₁.P (v.1 (Fin.last n₁))=0 ∧ C₂.P (v.2 (Fin.last n₂))=0 ∧
      ∀ u : Paths E n₁ n₂,‖u‖≤δ →
        (∀ t,f₁ t (x₁ t.castSucc+u.1 t.castSucc)=x₁ t.succ+u.1 t.succ) →
        (∀ t,f₂ t (x₂ t.castSucc+u.2 t.castSucc)=x₂ t.succ+u.2 t.succ) →
        x₁ 0+u.1 0=x₂ 0+u.2 0 →
        C₁.P (u.1 (Fin.last n₁))=0 → C₂.P (u.2 (Fin.last n₂))=0 → u=v := by
  classical
  let V := boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))
  let D := (2*U+U^4)*(n₁+n₂ : ℕ)+U^2
  let Q := (U+U^4)*(2*K)*(1+2*D)+D
  let a : Data E H G n₁ n₂ := (0,0,x₂ 0-x₁ 0,0,0)
  let R := ArrayRemainder.residual (H:=H) (G:=G) f₁ f₂
    (fun t => x₁ t.castSucc) (fun t => x₂ t.castSucc)
  have hUn : 0≤U := by linarith
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  have hQ : 0≤Q := by dsimp [Q,D]; positivity
  have hb : ‖V.symm.toContinuousLinearMap‖≤Q := boundary_inverse_norm C₁ C₂ L hL hU hK
    hsmall hs₁ hb₁ hs₂ hb₂ hJ₁ hP₁ hJ₂ hP₂
  have ha : ‖a‖≤C*r := by simpa [a,Prod.norm_def] using hnear
  have hR : ∀ u∈closedBall (0 : Paths E n₁ n₂) δ,
      ∀ v∈closedBall (0 : Paths E n₁ n₂) δ,‖R u-R v‖≤C*δ*‖u-v‖ := by
    intro u hu v hv
    apply ArrayRemainder.residual_from_derivative f₁ f₂ _ _ hC hδ.le
      hd₁ hd₂ hder₁ hder₂
    · simpa using hu
    · simpa using hv
  obtain ⟨v,hv,hv',heq,huniq⟩ := NonlinearBoundary.solve V R a hQ hC hr hδ hb ha
    (ArrayRemainder.residual_zero _ _ _ _) hR hcontract hdata
  refine ⟨v,hv,hv',?_,?_,?_,?_,?_,?_⟩
  · intro t
    apply ArrayRemainder.genuine_step _ _ _ _ _ (hx₁ t)
    rw [hA₁]
    have h := congrArg (fun d : Data E H G n₁ n₂ => d.1 t) heq
    simpa [V,boundaryEquiv,boundaryLinear,a,R,ArrayRemainder.residual] using h
  · intro t
    apply ArrayRemainder.genuine_step _ _ _ _ _ (hx₂ t)
    rw [hA₂]
    have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.1 t) heq
    simpa [V,boundaryEquiv,boundaryLinear,a,R,ArrayRemainder.residual] using h
  · have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.2.1) heq
    change v.1 0-v.2 0=x₂ 0-x₁ 0+0 at h
    rw [add_zero] at h
    have h' := congrArg (fun z => x₁ 0+z+v.2 0) h
    simpa [sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using h'
  · have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.2.2.1) heq
    change C₁.P _=0+0 at h
    simpa using h
  · have h := congrArg (fun d : Data E H G n₁ n₂ => d.2.2.2.2) heq
    change C₂.P _=0+0 at h
    simpa using h
  · intro u hu hs₁ hs₂ hm hp₁ hp₂
    apply huniq u hu
    apply Prod.ext
    · funext t
      change u.1 t.succ-A₁.map (t+1) t (u.1 t.castSucc)=
        0+(f₁ t (x₁ t.castSucc+u.1 t.castSucc)-f₁ t (x₁ t.castSucc)-
          (fderiv ℝ (f₁ t) (x₁ t.castSucc)) (u.1 t.castSucc))
      rw [hs₁ t,hx₁ t,hA₁ t,zero_add]
      abel
    · apply Prod.ext
      · funext t
        change u.2 t.succ-A₂.map (t+1) t (u.2 t.castSucc)=
          0+(f₂ t (x₂ t.castSucc+u.2 t.castSucc)-f₂ t (x₂ t.castSucc)-
            (fderiv ℝ (f₂ t) (x₂ t.castSucc)) (u.2 t.castSucc))
        rw [hs₂ t,hx₂ t,hA₂ t,zero_add]
        abel
      · apply Prod.ext
        · change u.1 0-u.2 0=(x₂ 0-x₁ 0)+0
          have hh := congrArg (fun z => z-x₁ 0-u.2 0) hm
          simpa only [add_zero] using (by convert hh using 1 <;> abel)
        · apply Prod.ext
          · change C₁.P (u.1 (Fin.last n₁))=0+0
            simpa only [add_zero] using hp₁
          · change C₂.P (u.2 (Fin.last n₂))=0+0
            simpa only [add_zero] using hp₂
end SmoothObstruction.FiniteGreen.Matching

namespace SmoothObstruction.IdealExchange
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Orthogonal gap control followed by an oblique complementary projector.
This retains the reference inverse cost instead of silently treating the
nonorthogonal slow/fast decomposition as orthogonal. -/
lemma annihilator_bound (U V : Submodule ℝ E) (Q : E →L[ℝ] E)
    {ε G : ℝ} (hG : 0≤G) (_hε : 0≤ε)
    (hclose : ‖U.starProjection-V.starProjection‖≤ε)
    (hQ : ‖Q‖≤G) (hzero : ∀ v∈V,Q v=0) (x : U) :
    ‖Q (x:E)‖≤G*ε*‖x‖ := by
  have he : Q (x:E)=Q ((x:E)-V.starProjection (x:E)) := by
    rw [map_sub,hzero _ (V.starProjection_apply_mem _),sub_zero]
  rw [he]
  have hdist : ‖(x:E)-V.starProjection (x:E)‖≤ε*‖x‖ := by
    have hh := (U.starProjection-V.starProjection).le_opNorm (x:E)
    rw [_root_.sub_apply,U.starProjection_eq_self_iff.mpr x.property] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg x))
  exact ((Q.le_opNorm _).trans (mul_le_mul hQ hdist (norm_nonneg _) hG)).trans_eq (by ring)

/-- A pair of small endpoint graphs over nearby complementary spaces gives
ideal exchange at time zero; the large full-window shadowing cost does not
multiply the space-comparison error. -/
theorem graph_exchange_error {A₀ : FiniteGreen.Evolution E}
    (B₀ : FiniteGreen.Splitting A₀) (U V : Submodule ℝ E)
    (C D : E →L[ℝ] E) (a : U) (b : V) (m : E)
    {ε κ G R : ℝ} (hε : 0≤ε) (hκ : 0≤κ) (hG : 0≤G) (_hR : 0≤R)
    (hcU : ‖U.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hcV : ‖V.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hC : ‖C‖≤κ) (hD : ‖D‖≤κ)
    (hP : ‖B₀.slow 0‖≤G) (hQ : ‖B₀.fast 0‖≤G)
    (ha : ‖a‖≤R) (hb : ‖b‖≤R)
    (hm : (a:E)+C a-((b:E)+D b)=m) :
    ‖((a:E)+C a)-B₀.slow 0 m‖≤2*G*(ε+κ)*R := by
  have hQa : ‖B₀.fast 0 (a:E)‖≤G*ε*R :=
    (annihilator_bound U (B₀.slow 0).range (B₀.fast 0) hG hε hcU hQ
      (by rintro v ⟨w,rfl⟩; exact B₀.fast_slow 0 w) a).trans
        (mul_le_mul_of_nonneg_left ha (by positivity))
  have hPb : ‖B₀.slow 0 (b:E)‖≤G*ε*R :=
    (annihilator_bound V (B₀.fast 0).range (B₀.slow 0) hG hε hcV hP
      (by rintro v ⟨w,rfl⟩; exact B₀.slow_fast 0 w) b).trans
        (mul_le_mul_of_nonneg_left hb (by positivity))
  have bound (Q C : E →L[ℝ] E) (v : E) (hQ : ‖Q‖≤G) (hC : ‖C‖≤κ) (hv : ‖v‖≤R) :
      ‖Q (C v)‖≤G*κ*R := by
    apply (Q.le_opNorm _).trans
    apply (mul_le_mul hQ ((C.le_opNorm _).trans
      (mul_le_mul hC hv (norm_nonneg _) hκ)) (norm_nonneg _) hG).trans_eq
    ring
  have he : ((a:E)+C a)-B₀.slow 0 m=
      B₀.fast 0 (a:E)+B₀.fast 0 (C a)+(B₀.slow 0 (b:E)+B₀.slow 0 (D b)) := by
    rw [←hm,map_sub,map_add,map_add]
    have hh := B₀.add_apply 0 ((a:E)+C a)
    rw [map_add,map_add] at hh
    rw [←hh]
    abel
  rw [he]
  calc
    _ ≤ (‖B₀.fast 0 (a:E)‖+‖B₀.fast 0 (C a)‖)+
        (‖B₀.slow 0 (b:E)‖+‖B₀.slow 0 (D b)‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ (G*ε*R+G*κ*R)+(G*ε*R+G*κ*R) :=
      add_le_add (add_le_add hQa (bound _ _ _ hQ hC ha))
        (add_le_add hPb (bound _ _ _ hP hD hb))
    _ = _ := by ring
end SmoothObstruction.IdealExchange

namespace SmoothObstruction.FiniteGreen.Matching
variable {E H G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A₀ A₁ A₂ : Evolution E} (B₀ : Splitting A₀) {B₁ : Splitting A₁} {B₂ : Splitting A₂}
    {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

/-- Quantitative ideal exchange for the actual zero-forcing boundary inverse.
The middle cost is O(exp(C b n)), separate from full-orbit exp(C g n). -/
theorem linear_initial_error
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    {K P ε κ : ℝ} (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hP : 0≤P) (hε : 0≤ε) (hκ : 0≤κ)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hc₁ : ‖B₁.initialSpace.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hc₂ : ‖B₂.initialSpace.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hk₁ : ‖C₁.kernel‖≤κ) (hk₂ : ‖C₂.kernel‖≤κ)
    (hs : ‖B₀.slow 0‖≤P) (hf : ‖B₀.fast 0‖≤P)
    (v₁ v₂ : ℕ → E) (m : E)
    (hv₁ : ∀ t<n₁,v₁ (t+1)=A₁.map (t+1) t (v₁ t))
    (hv₂ : ∀ t<n₂,v₂ (t+1)=A₂.map (t+1) t (v₂ t))
    (he₁ : C₁.P (v₁ n₁)=0) (he₂ : C₂.P (v₂ n₂)=0)
    (hm : v₁ 0-v₂ 0=m) :
    ‖v₁ 0-B₀.slow 0 m‖≤4*P*K*(ε+κ)*‖m‖ := by
  let M := BoundaryNeumann.perturb L (correction C₁ C₂) (hsmall.trans_lt (by norm_num))
  let a : B₁.initialSpace := ⟨B₁.slow 0 (v₁ 0),⟨v₁ 0,rfl⟩⟩
  let b : B₂.initialSpace := ⟨B₂.slow 0 (v₂ 0),⟨v₂ 0,rfl⟩⟩
  have hg₁ := C₁.trajectory_unique (fun _ => 0) a (B₁.slow_initial a) 0 v₁
    (by simpa only [add_zero] using hv₁) rfl he₁
  have hg₂ := C₂.trajectory_unique (fun _ => 0) b (B₂.slow_initial b) 0 v₂
    (by simpa only [add_zero] using hv₂) rfl he₂
  have h0₁ : v₁ 0=(a:E)+C₁.kernel a := by
    rw [hg₁ 0 (Nat.zero_le n₁),C₁.trajectory_initial _ _ (B₁.slow_initial a),
      C₁.trajectory_zero]
    simp
  have h0₂ : v₂ 0=(b:E)+C₂.kernel b := by
    rw [hg₂ 0 (Nat.zero_le n₂),C₂.trajectory_initial _ _ (B₂.slow_initial b),
      C₂.trajectory_zero]
    simp
  have hMa : M (a,b)=m := by
    rw [BoundaryNeumann.perturb_apply,hL,correction_apply]
    rw [h0₁,h0₂] at hm
    calc
      _ = (a:E)+C₁.kernel a-((b:E)+C₂.kernel b) := by abel
      _ = m := hm
  have hn : ‖(a,b)‖≤(2*K)*‖m‖ := by
    have hi := BoundaryNeumann.inverse_norm L (correction C₁ C₂) hK hsmall
    have ha : M.symm m=(a,b) := M.symm_apply_eq.mpr hMa.symm
    rw [←ha]
    exact (M.symm.toContinuousLinearMap.le_opNorm m).trans
      (mul_le_mul_of_nonneg_right hi (norm_nonneg m))
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  rw [h0₁]
  apply (IdealExchange.graph_exchange_error B₀ B₁.initialSpace B₂.initialSpace
    C₁.kernel C₂.kernel a b m hε hκ hP (by positivity) hc₁ hc₂ hk₁ hk₂ hs hf
    ((norm_fst_le (a,b)).trans hn) ((norm_snd_le (a,b)).trans hn)
    (by rwa [h0₁,h0₂] at hm)).trans_eq
  ring
end SmoothObstruction.FiniteGreen.Matching

namespace SmoothObstruction.ArrayRemainder
open Set Metric
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n₁ n₂ : ℕ}

omit [NormedSpace ℝ H] [NormedSpace ℝ G] in
/-- The actual array residual is quadratic in the sup norm, with a constant
independent of either window length. The smaller radius is the array norm. -/
theorem residual_quadratic (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin n₁ → E) (x₂ : Fin n₂ → E) {C δ : ℝ} (hC : 0≤C)
    (hd₁ : ∀ t,∀ y∈closedBall (x₁ t) δ,DifferentiableAt ℝ (f₁ t) y)
    (hd₂ : ∀ t,∀ y∈closedBall (x₂ t) δ,DifferentiableAt ℝ (f₂ t) y)
    (h₁ : ∀ t,∀ y∈closedBall (x₁ t) δ,‖fderiv ℝ (f₁ t) y-fderiv ℝ (f₁ t) (x₁ t)‖≤C*‖y-x₁ t‖)
    (h₂ : ∀ t,∀ y∈closedBall (x₂ t) δ,‖fderiv ℝ (f₂ t) y-fderiv ℝ (f₂ t) (x₂ t)‖≤C*‖y-x₂ t‖)
    {v : Paths E n₁ n₂} (hv : ‖v‖≤δ) :
    ‖residual (H:=H) (G:=G) f₁ f₂ x₁ x₂ v‖≤C*‖v‖^2 := by
  have hh := residual_from_derivative (H:=H) (G:=G) f₁ f₂ x₁ x₂ hC (norm_nonneg v)
    (fun t y hy => hd₁ t y (closedBall_subset_closedBall hv hy))
    (fun t y hy => hd₂ t y (closedBall_subset_closedBall hv hy))
    (fun t y hy => h₁ t y (closedBall_subset_closedBall hv hy))
    (fun t y hy => h₂ t y (closedBall_subset_closedBall hv hy))
    (le_refl ‖v‖) (show ‖(0 : Paths E n₁ n₂)‖≤‖v‖ by simp)
  simpa only [residual_zero,sub_zero,pow_two,mul_assoc] using hh
end SmoothObstruction.ArrayRemainder

namespace SmoothObstruction.FiniteGreen.Matching
variable {E H G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A₀ A₁ A₂ : Evolution E} (B₀ : Splitting A₀) {B₁ : Splitting A₁} {B₂ : Splitting A₂}
    {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

theorem array_linear_initial_error
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    {K P ε κ : ℝ} (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hP : 0≤P) (hε : 0≤ε) (hκ : 0≤κ)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hc₁ : ‖B₁.initialSpace.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hc₂ : ‖B₂.initialSpace.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hk₁ : ‖C₁.kernel‖≤κ) (hk₂ : ‖C₂.kernel‖≤κ)
    (hs : ‖B₀.slow 0‖≤P) (hf : ‖B₀.fast 0‖≤P)
    (v : Paths E n₁ n₂) (m : E) (hv : boundary C₁ C₂ v=(0,0,m,0,0)) :
    ‖v.1 0-B₀.slow 0 m‖≤4*P*K*(ε+κ)*‖m‖ := by
  have h₁ : ∀ t<n₁,extend v.1 (t+1)=A₁.map (t+1) t (extend v.1 t) := by
    intro t ht
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.1 ⟨t,ht⟩) hv
    change v.1 ⟨t+1,by omega⟩-A₁.map (t+1) t (v.1 ⟨t,by omega⟩)=0 at h
    simpa only [extend,dite_eq_left (show t+1<n₁+1 by omega),dite_eq_left (show t<n₁+1 by omega)]
      using sub_eq_zero.mp h
  have h₂ : ∀ t<n₂,extend v.2 (t+1)=A₂.map (t+1) t (extend v.2 t) := by
    intro t ht
    have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.1 ⟨t,ht⟩) hv
    change v.2 ⟨t+1,by omega⟩-A₂.map (t+1) t (v.2 ⟨t,by omega⟩)=0 at h
    simpa only [extend,dite_eq_left (show t+1<n₂+1 by omega),dite_eq_left (show t<n₂+1 by omega)]
      using sub_eq_zero.mp h
  have he₁ : C₁.P (extend v.1 n₁)=0 := by
    change C₁.P (extend v.1 (Fin.last n₁))=0
    rw [extend_apply]
    exact congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.1) hv
  have he₂ : C₂.P (extend v.2 n₂)=0 := by
    change C₂.P (extend v.2 (Fin.last n₂))=0
    rw [extend_apply]
    exact congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.2) hv
  have hm : extend v.1 0-extend v.2 0=m := by
    change extend v.1 (0 : Fin (n₁+1))-extend v.2 (0 : Fin (n₂+1))=m
    rw [extend_apply,extend_apply]
    exact congrArg (fun z : Data E H G n₁ n₂ => z.2.2.1) hv
  have hh := linear_initial_error B₀ C₁ C₂ L hL hK hP hε hκ hsmall hc₁ hc₂
    hk₁ hk₂ hs hf (extend v.1) (extend v.2) m h₁ h₂ he₁ he₂ hm
  change ‖extend v.1 (0 : Fin (n₁+1))-B₀.slow 0 m‖≤_ at hh
  rwa [extend_apply] at hh

/-- Linear graph-space error and nonlinear residual have DIFFERENT costs.
In particular, no full-window inverse multiplies the common-bin gap error. -/
theorem array_nonlinear_initial_error
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    {K P ε κ Q C : ℝ} (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hP : 0≤P) (hε : 0≤ε) (hκ : 0≤κ) (hC : 0≤C)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hc₁ : ‖B₁.initialSpace.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hc₂ : ‖B₂.initialSpace.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hk₁ : ‖C₁.kernel‖≤κ) (hk₂ : ‖C₂.kernel‖≤κ)
    (hs : ‖B₀.slow 0‖≤P) (hf : ‖B₀.fast 0‖≤P)
    (R : Paths E n₁ n₂ → Data E H G n₁ n₂) (v : Paths E n₁ n₂) (m : E)
    (hR : ‖R v‖≤C*‖v‖^2)
    (heq : boundary C₁ C₂ v=(0,0,m,0,0)+R v)
    (hQ : ‖(boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))).symm.toContinuousLinearMap‖≤Q) :
    ‖v.1 0-B₀.slow 0 m‖≤4*P*K*(ε+κ)*‖m‖+Q*C*‖v‖^2 := by
  let V := boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))
  let w := V.symm (0,0,m,0,0)
  have hw : boundary C₁ C₂ w=(0,0,m,0,0) := V.apply_symm_apply _
  have he := NonlinearBoundary.nonlinear_linear_error V hQ hC hR heq
  have hl := array_linear_initial_error B₀ C₁ C₂ L hL hK hP hε hκ hsmall hc₁ hc₂
    hk₁ hk₂ hs hf w m hw
  calc
    _ ≤ ‖w.1 0-B₀.slow 0 m‖+‖v.1 0-w.1 0‖ := by
      convert norm_add_le (w.1 0-B₀.slow 0 m) (v.1 0-w.1 0) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      abel
    _ ≤ _ := add_le_add hl (((norm_le_pi_norm (v.1-w.1) 0).trans (norm_fst_le (v-w))).trans he)
end SmoothObstruction.FiniteGreen.Matching

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ManifoldMatching
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
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
/-- An exact finite coordinate solution lying in the original chart targets
is a genuine manifold orbit, also in a half-space model. -/
theorem realize_array (S : Diffeomorph I I M M ∞) {n : ℕ}
    (a : Fin (n+1) → M) (u : Fin (n+1) → E (d:=d))
    (hu : ∀ t,u t∈(extChartAt I (a t)).target)
    (hdom : ∀ t : Fin n,u t.castSucc∈domainU I S (a t.castSucc) (a t.succ))
    (hstep : ∀ t : Fin n,localMap I S (a t.castSucc) (a t.succ) (u t.castSucc)=u t.succ) :
    ∃ z : M,∀ t : Fin (n+1),S^[t.val] z∈(chartAt H (a t)).source ∧
      (extChartAt I (a t)) (S^[t.val] z)=u t := by
  let z := (extChartAt I (a 0)).symm (u 0)
  refine ⟨z,?_⟩
  have h (t : ℕ) (ht : t<n+1) : S^[t] z=(extChartAt I (a ⟨t,ht⟩)).symm (u ⟨t,ht⟩) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      have ht' : t<n := by omega
      have hh := hstep ⟨t,ht'⟩
      have htS : S ((extChartAt I (a ⟨t,by omega⟩)).symm (u ⟨t,by omega⟩))
          ∈(extChartAt I (a ⟨t+1,ht⟩)).source := by
        have hm := (hdom ⟨t,ht'⟩).2
        change S ((extChartAt I (a ⟨t,by omega⟩)).symm (u ⟨t,by omega⟩))
          ∈(chartAt H (a ⟨t+1,ht⟩)).source at hm
        simpa only [extChartAt_source] using hm
      rw [Function.iterate_succ_apply',ih (by omega)]
      exact (extChartAt I (a ⟨t+1,ht⟩)).left_inv htS |>.symm.trans
        (congrArg (extChartAt I (a ⟨t+1,ht⟩)).symm hh)
  intro t
  rw [h t t.isLt]
  exact ⟨by simpa only [extChartAt_source] using (extChartAt I (a t)).map_target (hu t),
    (extChartAt I (a t)).right_inv (hu t)⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Matching the time-zero coordinate realizes the TWO-sided exact arrays
as one actual orbit. In particular no pair of unrelated local branches is
substituted for the smooth switch. -/
theorem realize_bilateral_array (S : Diffeomorph I I M M ∞) {n : ℕ}
    (a b : Fin (n+1) → M) (u v : Fin (n+1) → E (d:=d))
    (ha : a 0=b 0) (huv : u 0=v 0)
    (hu : ∀ t,u t∈(extChartAt I (a t)).target)
    (hv : ∀ t,v t∈(extChartAt I (b t)).target)
    (hud : ∀ t : Fin n,u t.castSucc∈domainU I S (a t.castSucc) (a t.succ))
    (hvd : ∀ t : Fin n,v t.castSucc∈domainU I S.symm (b t.castSucc) (b t.succ))
    (hus : ∀ t : Fin n,localMap I S (a t.castSucc) (a t.succ) (u t.castSucc)=u t.succ)
    (hvs : ∀ t : Fin n,localMap I S.symm (b t.castSucc) (b t.succ) (v t.castSucc)=v t.succ) :
    ∃ z : M,(∀ t : Fin (n+1),S^[t.val] z∈(chartAt H (a t)).source ∧
      (extChartAt I (a t)) (S^[t.val] z)=u t) ∧
      (∀ t : Fin (n+1),S.symm^[t.val] z∈(chartAt H (b t)).source ∧
      (extChartAt I (b t)) (S.symm^[t.val] z)=v t) := by
  obtain ⟨z,hz⟩ := realize_array I S a u hu hud hus
  obtain ⟨w,hw⟩ := realize_array I S.symm b v hv hvd hvs
  have hz0 : z=(extChartAt I (a 0)).symm (u 0) := by
    have hz0 := hz 0
    simp only [Fin.val_zero,Function.iterate_zero,id_eq] at hz0
    rw [←hz0.2,(extChartAt I (a 0)).left_inv (by simpa only [extChartAt_source] using hz0.1)]
  have hw0 : w=(extChartAt I (b 0)).symm (v 0) := by
    have hw0 := hw 0
    simp only [Fin.val_zero,Function.iterate_zero,id_eq] at hw0
    rw [←hw0.2,(extChartAt I (b 0)).left_inv (by simpa only [extChartAt_source] using hw0.1)]
  have heq : z=w := by rw [hz0,hw0,ha,huv]
  exact ⟨z,hz,by simpa only [heq] using hw⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ShortBin
open EuclideanSplitting FiniteGreen FiniteGreen.Matching
open scoped Matrix.Norms.L2Operator
variable {d n : ℕ} {K : ℝ}

lemma Gauge.evolution_step (A : Gauge d n K) (D : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (t : ℕ) (h : (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm D*A.U t=
      A.U (t+1)*rate A.lam 1) : A.evolution.map (t+1) t=D := by
  change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition A.U A.V A.lam t (t+1))=D
  rw [transition,show ((t+1:ℕ):ℝ)-(t:ℝ)=1 by push_cast; ring,←h,mul_assoc,A.UV t,mul_one]
  exact (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).apply_symm_apply D

lemma Gauge.unweighted (A : Gauge d n K) (S : Finset (Fin d)) {a : ℝ}
    (ha : 0≤a) (hs : ∀ j∈S,A.lam j≤a) (hf : ∀ j∈Sᶜ,-a≤A.lam j) :
    (∀ s t,s≤t → t≤n → ‖(A.evolution.map t s).comp ((A.splitting S).slow s)‖≤Real.exp (2*K+a*n)) ∧
    (∀ s t,s≤t → t≤n → ‖(A.evolution.map s t).comp ((A.splitting S).fast t)‖≤Real.exp (2*K+a*n)) :=
  unweighted_bounds A.U A.V A.lam A.UV A.VU S ha A.normU A.normV hs hf

/-- All the finite-interval linear boundary hypotheses are produced from
raw common-bin gauge comparisons and fixed endpoint projections. The norm
of the matching inverse is a middle-time cost, and the endpoint correction
retains threshold cancellation, including a positive slow threshold. -/
theorem gauge_boundary_control (A₀ A Z : Gauge d n K) (S₀ S T : Finset (Fin d))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hdV : Module.finrank ℝ ((A.splitting S).fast n).range=Module.finrank ℝ V)
    (hdW : Module.finrank ℝ ((Z.splitting T).fast n).range=Module.finrank ℝ W)
    (hcV : ‖((A.splitting S).fast n).range.starProjection-V.starProjection‖≤1/2)
    (hcW : ‖((Z.splitting T).fast n).range.starProjection-W.starProjection‖≤1/2)
    {ε γ g : ℝ} (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hdS : S₀.card=S.card) (hdT : S₀ᶜ.card=T.card)
    (hcS : ‖(A₀.space S₀).starProjection-(A.space S).starProjection‖≤ε)
    (hcT : ‖(A₀.space S₀ᶜ).starProjection-(Z.space T).starProjection‖≤ε)
    (hsmall : Real.exp (2*K)*(2*ε)≤1/2)
    (hsA : ∀ j∈S,A.lam j≤γ-g) (hfA : ∀ j∈Sᶜ,γ+g≤A.lam j)
    (hsZ : ∀ j∈T,Z.lam j≤ -γ-g) (hfZ : ∀ j∈Tᶜ,-γ+g≤Z.lam j)
    (hgap : (2*Real.exp (2*K))*(2*(2*Real.exp (2*K)^2*Real.exp (-2*g*n)))≤1/2) :
    let C₁ := (A.splitting S).terminalProjection n V hdV hcV
    let C₂ := (Z.splitting T).terminalProjection n W hdW hcW
    ∃ L : ((A.splitting S).initialSpace×(Z.splitting T).initialSpace) ≃L[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ v,L v=(v.1:EuclideanSpace ℝ (Fin d))-(v.2:EuclideanSpace ℝ (Fin d))) ∧
      ‖L.symm.toContinuousLinearMap‖≤2*Real.exp (2*K) ∧
      ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2 ∧
      ‖C₁.kernel‖≤2*Real.exp (2*K)^2*Real.exp (-2*g*n) ∧
      ‖C₂.kernel‖≤2*Real.exp (2*K)^2*Real.exp (-2*g*n) := by
  intro C₁ C₂
  obtain ⟨L,hL,hK⟩ := gauge_matching A₀ A Z S₀ S T hε hεhalf hdS hdT hcS hcT hsmall
  have hA := endpoint_gap_bounds A.U A.V A.lam A.UV A.VU S n A.normU A.normV hsA hfA
  have hZ := endpoint_gap_bounds Z.U Z.V Z.lam Z.UV Z.VU T n Z.normU Z.normV hsZ hfZ
  have heA : ‖C₁.kernel‖≤2*Real.exp (2*K)^2*Real.exp (-2*g*n) :=
    C₁.kernel_norm_gap (Real.exp_nonneg _) hA.2 hA.1
      ((A.splitting S).terminalProjection_J_norm n V hdV hcV)
      ((A.splitting S).terminalProjection_P_norm n V hdV hcV)
  have heZ : ‖C₂.kernel‖≤2*Real.exp (2*K)^2*Real.exp (-2*g*n) :=
    C₂.kernel_norm_gap (Real.exp_nonneg _) hZ.2 hZ.1
      ((Z.splitting T).terminalProjection_J_norm n W hdW hcW)
      ((Z.splitting T).terminalProjection_P_norm n W hdW hcW)
  refine ⟨L,hL,hK,?_,heA,heZ⟩
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply le_trans (mul_le_mul hK (correction_norm C₁ C₂ heA heZ) (norm_nonneg (correction C₁ C₂)) (by positivity))
  simpa only [two_mul] using hgap
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ShortBin
lemma bvpGrowth_ge_two (K a : ℝ) (n : ℕ) : 2≤bvpGrowth K a n := by
  dsimp [bvpGrowth]; linarith [Real.exp_pos (2*K+a*n)]
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open FiniteGreen FiniteGreen.Matching ShortBin

omit [IsManifold I ∞ M] in
lemma interior_iterate (S : Diffeomorph I I M M ∞) {x : M} (hx : I.IsInteriorPoint x) (t : ℕ) :
    I.IsInteriorPoint (S^[t] x) := by
  induction t with
  | zero => exact hx
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact ((S.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp ih

/-- The long gauge equations identify every step of the evolution with
an ACTUAL coordinate derivative. -/
lemma gauge_actual_step (S : Diffeomorph I I M M ∞) (a b x : M)
    {n : ℕ} {K : ℝ} (A : ShortBin.Gauge d n K) (t : ℕ)
    (hx : x∈(chartAt H a).source) (hSx : S x∈(chartAt H b).source)
    (hint : I.IsInteriorPoint x)
    (hEq : (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (coord I S a b x)*A.U t=
      A.U (t+1)*EuclideanSplitting.rate A.lam 1) :
    fderiv ℝ (localMap I S a b) ((extChartAt I a) x)=A.evolution.map (t+1) t := by
  rw [A.evolution_step (coord I S a b x) t hEq]
  exact (hasFDerivAt_localMap I S a b x ⟨hx,hSx⟩ ((interior_coord I a x hx).mpr hint)).fderiv

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.FiniteGreen.Matching
open Set Metric
variable {E H G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A₀ A₁ A₂ : Evolution E} (B₀ : Splitting A₀) {B₁ : Splitting A₁} {B₂ : Splitting A₂}
    {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

/-- A genuine nonlinear coordinate solution satisfies the exact boundary
residual equation, hence the sharp ideal-exchange estimate. -/
theorem genuine_initial_error
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    {K P ε κ Q C δ : ℝ} (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (hP : 0≤P) (hε : 0≤ε) (hκ : 0≤κ) (hC : 0≤C)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hc₁ : ‖B₁.initialSpace.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hc₂ : ‖B₂.initialSpace.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hk₁ : ‖C₁.kernel‖≤κ) (hk₂ : ‖C₂.kernel‖≤κ)
    (hs : ‖B₀.slow 0‖≤P) (hf : ‖B₀.fast 0‖≤P)
    (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin (n₁+1) → E) (x₂ : Fin (n₂+1) → E)
    (hx₁ : ∀ t,f₁ t (x₁ t.castSucc)=x₁ t.succ)
    (hx₂ : ∀ t,f₂ t (x₂ t.castSucc)=x₂ t.succ)
    (hA₁ : ∀ t : Fin n₁,fderiv ℝ (f₁ t) (x₁ t.castSucc)=A₁.map (t+1) t)
    (hA₂ : ∀ t : Fin n₂,fderiv ℝ (f₂ t) (x₂ t.castSucc)=A₂.map (t+1) t)
    (hd₁ : ∀ t,∀ y∈closedBall (x₁ t.castSucc) δ,DifferentiableAt ℝ (f₁ t) y)
    (hd₂ : ∀ t,∀ y∈closedBall (x₂ t.castSucc) δ,DifferentiableAt ℝ (f₂ t) y)
    (hder₁ : ∀ t,∀ y∈closedBall (x₁ t.castSucc) δ,
      ‖fderiv ℝ (f₁ t) y-fderiv ℝ (f₁ t) (x₁ t.castSucc)‖≤C*‖y-x₁ t.castSucc‖)
    (hder₂ : ∀ t,∀ y∈closedBall (x₂ t.castSucc) δ,
      ‖fderiv ℝ (f₂ t) y-fderiv ℝ (f₂ t) (x₂ t.castSucc)‖≤C*‖y-x₂ t.castSucc‖)
    (v : Paths E n₁ n₂) (hv : ‖v‖≤δ)
    (hs₁ : ∀ t,f₁ t (x₁ t.castSucc+v.1 t.castSucc)=x₁ t.succ+v.1 t.succ)
    (hs₂ : ∀ t,f₂ t (x₂ t.castSucc+v.2 t.castSucc)=x₂ t.succ+v.2 t.succ)
    (hm : x₁ 0+v.1 0=x₂ 0+v.2 0)
    (hp₁ : C₁.P (v.1 (Fin.last n₁))=0) (hp₂ : C₂.P (v.2 (Fin.last n₂))=0)
    (hQ : ‖(boundaryEquiv C₁ C₂ L hL (hsmall.trans_lt (by norm_num))).symm.toContinuousLinearMap‖≤Q) :
    ‖v.1 0-B₀.slow 0 (x₂ 0-x₁ 0)‖≤4*P*K*(ε+κ)*‖x₂ 0-x₁ 0‖+Q*C*‖v‖^2 := by
  let R := ArrayRemainder.residual (H:=H) (G:=G) f₁ f₂
    (fun t => x₁ t.castSucc) (fun t => x₂ t.castSucc)
  apply array_nonlinear_initial_error B₀ C₁ C₂ L hL hK hP hε hκ hC hsmall hc₁ hc₂
    hk₁ hk₂ hs hf R v (x₂ 0-x₁ 0)
    (ArrayRemainder.residual_quadratic f₁ f₂ _ _ hC hd₁ hd₂ hder₁ hder₂ hv) _ hQ
  apply Prod.ext
  · funext t
    change v.1 t.succ-A₁.map (t+1) t (v.1 t.castSucc)=
      0+(f₁ t (x₁ t.castSucc+v.1 t.castSucc)-f₁ t (x₁ t.castSucc)-
        (fderiv ℝ (f₁ t) (x₁ t.castSucc)) (v.1 t.castSucc))
    rw [hs₁ t,hx₁ t,hA₁ t,zero_add]
    abel
  · apply Prod.ext
    · funext t
      change v.2 t.succ-A₂.map (t+1) t (v.2 t.castSucc)=
        0+(f₂ t (x₂ t.castSucc+v.2 t.castSucc)-f₂ t (x₂ t.castSucc)-
          (fderiv ℝ (f₂ t) (x₂ t.castSucc)) (v.2 t.castSucc))
      rw [hs₂ t,hx₂ t,hA₂ t,zero_add]
      abel
    · apply Prod.ext
      · change v.1 0-v.2 0=(x₂ 0-x₁ 0)+0
        have hh := congrArg (fun z => z-x₁ 0-v.2 0) hm
        simpa only [add_zero] using (by convert hh using 1 <;> abel)
      · apply Prod.ext
        · change C₁.P (v.1 (Fin.last n₁))=0+0
          simpa only [add_zero] using hp₁
        · change C₂.P (v.2 (Fin.last n₂))=0+0
          simpa only [add_zero] using hp₂
end SmoothObstruction.FiniteGreen.Matching

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
open FiniteGreen FiniteGreen.Matching

/-- The authentic local-coordinate nonlinear boundary construction gives
ONE actual point of the manifold, with both orbit halves and the fixed
terminal equations. The ball-domain conditions keep every inverse chart
and every one-step expression inside the ORIGINAL manifold. -/
theorem actual_join_ideal (S : Diffeomorph I I M M ∞) {n : ℕ}
    (a b : Fin (n+1) → M) (x y : M) (hab : a 0=b 0)
    (hx : ∀ t : Fin (n+1),S^[t.val] x∈(chartAt H (a t)).source)
    (hy : ∀ t : Fin (n+1),S.symm^[t.val] y∈(chartAt H (b t)).source)
    (A₁ A₂ : Evolution (E (d:=d))) (B₁ : Splitting A₁) (B₂ : Splitting A₂)
    (C₁ : B₁.Terminal (H:=F) n) (C₂ : B₂.Terminal (H:=G) n)
    (L : (B₁.initialSpace×B₂.initialSpace) ≃L[ℝ] E (d:=d))
    (hL : ∀ z,L z=(z.1:E (d:=d))-(z.2:E (d:=d)))
    {U K C r δ : ℝ} (hU : 1≤U) (hK : ‖L.symm.toContinuousLinearMap‖≤K)
    (A₀ : Evolution (E (d:=d))) (B₀ : Splitting A₀)
    {P ε κ : ℝ} (hP : 0≤P) (hε : 0≤ε) (hκ : 0≤κ)
    (hc₁ : ‖B₁.initialSpace.starProjection-(B₀.slow 0).range.starProjection‖≤ε)
    (hc₂ : ‖B₂.initialSpace.starProjection-(B₀.fast 0).range.starProjection‖≤ε)
    (hk₁ : ‖C₁.kernel‖≤κ) (hk₂ : ‖C₂.kernel‖≤κ)
    (hslow : ‖B₀.slow 0‖≤P) (hfast : ‖B₀.fast 0‖≤P)
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖≤1/2)
    (hs₁ : ∀ s u,s≤u → u≤n → ‖(A₁.map u s).comp (B₁.slow s)‖≤U)
    (hb₁ : ∀ s u,s≤u → u≤n → ‖(A₁.map s u).comp (B₁.fast u)‖≤U)
    (hs₂ : ∀ s u,s≤u → u≤n → ‖(A₂.map u s).comp (B₂.slow s)‖≤U)
    (hb₂ : ∀ s u,s≤u → u≤n → ‖(A₂.map s u).comp (B₂.fast u)‖≤U)
    (hJ₁ : ‖C₁.J‖≤U) (hP₁ : ‖C₁.P‖≤U)
    (hJ₂ : ‖C₂.J‖≤U) (hP₂ : ‖C₂.P‖≤U)
    (hC : 0≤C) (hr : 0 ≤ r) (hδ : 0<δ)
    (hA₁ : ∀ t : Fin n,fderiv ℝ (localMap I S (a t.castSucc) (a t.succ))
      ((extChartAt I (a t.castSucc)) (S^[t.val] x))=A₁.map (t+1) t)
    (hA₂ : ∀ t : Fin n,fderiv ℝ (localMap I S.symm (b t.castSucc) (b t.succ))
      ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y))=A₂.map (t+1) t)
    (hd₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (S^[t.val] x)) δ,
      DifferentiableAt ℝ (localMap I S (a t.castSucc) (a t.succ)) z)
    (hd₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y)) δ,
      DifferentiableAt ℝ (localMap I S.symm (b t.castSucc) (b t.succ)) z)
    (hder₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (S^[t.val] x)) δ,
      ‖fderiv ℝ (localMap I S (a t.castSucc) (a t.succ)) z-
        fderiv ℝ (localMap I S (a t.castSucc) (a t.succ))
          ((extChartAt I (a t.castSucc)) (S^[t.val] x))‖≤
        C*‖z-(extChartAt I (a t.castSucc)) (S^[t.val] x)‖)
    (hder₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y)) δ,
      ‖fderiv ℝ (localMap I S.symm (b t.castSucc) (b t.succ)) z-
        fderiv ℝ (localMap I S.symm (b t.castSucc) (b t.succ))
          ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y))‖≤
        C*‖z-(extChartAt I (b t.castSucc)) (S.symm^[t.val] y)‖)
    (ht₁ : ∀ t : Fin (n+1),closedBall ((extChartAt I (a t)) (S^[t.val] x)) δ⊆
      (extChartAt I (a t)).target)
    (ht₂ : ∀ t : Fin (n+1),closedBall ((extChartAt I (b t)) (S.symm^[t.val] y)) δ⊆
      (extChartAt I (b t)).target)
    (hdom₁ : ∀ t : Fin n,closedBall ((extChartAt I (a t.castSucc)) (S^[t.val] x)) δ⊆
      domainU I S (a t.castSucc) (a t.succ))
    (hdom₂ : ∀ t : Fin n,closedBall ((extChartAt I (b t.castSucc)) (S.symm^[t.val] y)) δ⊆
      domainU I S.symm (b t.castSucc) (b t.succ))
    (hnear : ‖(extChartAt I (b 0)) y-(extChartAt I (a 0)) x‖≤C*r)
    (hcontract : let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*δ≤1/4)
    (hdata : let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*K)*(1+2*D)+D)*C*r≤δ/4) :
    let D := (2*U+U^4)*(n+n : ℕ)+U^2
    let Q := (U+U^4)*(2*K)*(1+2*D)+D
    ∃ z : M,
      (∀ t : Fin (n+1),S^[t.val] z∈(chartAt H (a t)).source ∧
        ‖(extChartAt I (a t)) (S^[t.val] z)-(extChartAt I (a t)) (S^[t.val] x)‖≤δ/2) ∧
      (∀ t : Fin (n+1),S.symm^[t.val] z∈(chartAt H (b t)).source ∧
        ‖(extChartAt I (b t)) (S.symm^[t.val] z)-(extChartAt I (b t)) (S.symm^[t.val] y)‖≤δ/2) ∧
      C₁.P ((extChartAt I (a (Fin.last n))) (S^[n] z)-
        (extChartAt I (a (Fin.last n))) (S^[n] x))=0 ∧
      C₂.P ((extChartAt I (b (Fin.last n))) (S.symm^[n] z)-
        (extChartAt I (b (Fin.last n))) (S.symm^[n] y))=0 ∧
      (∀ t : Fin (n+1),‖(extChartAt I (a t)) (S^[t.val] z)-
        (extChartAt I (a t)) (S^[t.val] x)‖≤2*C*Q*r) ∧
      (∀ t : Fin (n+1),‖(extChartAt I (b t)) (S.symm^[t.val] z)-
        (extChartAt I (b t)) (S.symm^[t.val] y)‖≤2*C*Q*r) ∧
      ‖(extChartAt I (a 0)) z-(extChartAt I (a 0)) x-
        B₀.slow 0 ((extChartAt I (b 0)) y-(extChartAt I (a 0)) x)‖≤
        4*P*K*(ε+κ)*(C*r)+Q*C*(2*C*Q*r)^2 ∧
      ∀ z' : M,
        (∀ t : Fin (n+1),S^[t.val] z'∈(chartAt H (a t)).source ∧
          ‖(extChartAt I (a t)) (S^[t.val] z')-(extChartAt I (a t)) (S^[t.val] x)‖≤δ) →
        (∀ t : Fin (n+1),S.symm^[t.val] z'∈(chartAt H (b t)).source ∧
          ‖(extChartAt I (b t)) (S.symm^[t.val] z')-(extChartAt I (b t)) (S.symm^[t.val] y)‖≤δ) →
        C₁.P ((extChartAt I (a (Fin.last n))) (S^[n] z')-
          (extChartAt I (a (Fin.last n))) (S^[n] x))=0 →
        C₂.P ((extChartAt I (b (Fin.last n))) (S.symm^[n] z')-
          (extChartAt I (b (Fin.last n))) (S.symm^[n] y))=0 → z'=z := by
  let u : Fin (n+1) → E (d:=d) := fun t => (extChartAt I (a t)) (S^[t.val] x)
  let v : Fin (n+1) → E (d:=d) := fun t => (extChartAt I (b t)) (S.symm^[t.val] y)
  let f : Fin n → E (d:=d) → E (d:=d) := fun t => localMap I S (a t.castSucc) (a t.succ)
  let g : Fin n → E (d:=d) → E (d:=d) := fun t => localMap I S.symm (b t.castSucc) (b t.succ)
  have hu (t : Fin n) : f t (u t.castSucc)=u t.succ := by
    simp only [f,u,localMap,Function.comp_apply]
    rw [(extChartAt I (a t.castSucc)).left_inv (by simpa only [extChartAt_source] using hx t.castSucc)]
    exact congrArg (extChartAt I (a t.succ)) (Function.iterate_succ_apply' S _ x).symm
  have hv (t : Fin n) : g t (v t.castSucc)=v t.succ := by
    simp only [g,v,localMap,Function.comp_apply]
    rw [(extChartAt I (b t.castSucc)).left_inv (by simpa only [extChartAt_source] using hy t.castSucc)]
    exact congrArg (extChartAt I (b t.succ)) (Function.iterate_succ_apply' S.symm _ y).symm
  obtain ⟨w,hw,hwsharp,hf,hg,hmid,hp,hq,hunique⟩ := nonlinear_orbits_unique C₁ C₂ L hL hU hK hsmall
    hs₁ hb₁ hs₂ hb₂ hJ₁ hP₁ hJ₂ hP₂ f g u v hu hv hA₁ hA₂ hC hr hδ hd₁ hd₂ hder₁ hder₂
    (by simpa only [u,v,Fin.val_zero,Function.iterate_zero,id_eq] using hnear) hcontract hdata
  have hw₁ (t : Fin (n+1)) : ‖w.1 t‖≤δ/2 :=
    (norm_le_pi_norm w.1 t).trans ((norm_fst_le w).trans hw)
  have hw₂ (t : Fin (n+1)) : ‖w.2 t‖≤δ/2 :=
    (norm_le_pi_norm w.2 t).trans ((norm_snd_le w).trans hw)
  have hwδ : δ/2≤δ := by linarith
  have hb₁' (t : Fin (n+1)) : u t+w.1 t∈closedBall (u t) δ := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left]
    exact (hw₁ t).trans hwδ
  have hb₂' (t : Fin (n+1)) : v t+w.2 t∈closedBall (v t) δ := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left]
    exact (hw₂ t).trans hwδ
  obtain ⟨z,hz,hz'⟩ := realize_bilateral_array I S a b (fun t => u t+w.1 t) (fun t => v t+w.2 t)
    hab hmid (fun t => ht₁ t (hb₁' t)) (fun t => ht₂ t (hb₂' t))
    (fun t => hdom₁ t (hb₁' t.castSucc)) (fun t => hdom₂ t (hb₂' t.castSucc)) hf hg
  let D := (2*U+U^4)*(n+n : ℕ)+U^2
  let Q := (U+U^4)*(2*K)*(1+2*D)+D
  have hKn : 0≤K := (norm_nonneg L.symm.toContinuousLinearMap).trans hK
  have hUn : 0≤U := by linarith
  have hQn : 0≤Q := by dsimp [Q,D]; positivity
  have hQ := boundary_inverse_norm C₁ C₂ L hL hU hK hsmall
    hs₁ hb₁ hs₂ hb₂ hJ₁ hP₁ hJ₂ hP₂
  have hi := genuine_initial_error B₀ C₁ C₂ L hL hK hP hε hκ hC hsmall hc₁ hc₂
    hk₁ hk₂ hslow hfast f g u v hu hv hA₁ hA₂ hd₁ hd₂ hder₁ hder₂ w
    (hw.trans hwδ) hf hg hmid hp hq hQ
  have hi' : ‖w.1 0-B₀.slow 0 (v 0-u 0)‖≤
      4*P*K*(ε+κ)*(C*r)+Q*C*(2*C*Q*r)^2 := by
    apply hi.trans
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [u,v,Fin.val_zero,Function.iterate_zero,id_eq] using hnear
    · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hQn hC)
      exact pow_le_pow_left₀ (norm_nonneg w) hwsharp 2
  refine ⟨z,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro t
    refine ⟨(hz t).1,?_⟩
    rw [(hz t).2]
    simpa only [u,add_sub_cancel_left] using hw₁ t
  · intro t
    refine ⟨(hz' t).1,?_⟩
    rw [(hz' t).2]
    simpa only [v,add_sub_cancel_left] using hw₂ t
  · have hzL := (hz (Fin.last n)).2
    simp only [Fin.val_last] at hzL
    rw [hzL]
    simpa only [u,Fin.val_last,add_sub_cancel_left] using hp
  · have hzL := (hz' (Fin.last n)).2
    simp only [Fin.val_last] at hzL
    rw [hzL]
    simpa only [v,Fin.val_last,add_sub_cancel_left] using hq
  · intro t
    rw [(hz t).2]
    simpa only [u,add_sub_cancel_left] using
      (norm_le_pi_norm w.1 t).trans ((norm_fst_le w).trans hwsharp)
  · intro t
    rw [(hz' t).2]
    simpa only [v,add_sub_cancel_left] using
      (norm_le_pi_norm w.2 t).trans ((norm_snd_le w).trans hwsharp)
  · have hz0 := (hz 0).2
    simp only [Fin.val_zero,Function.iterate_zero,id_eq] at hz0
    rw [hz0]
    simpa only [u,v,Fin.val_zero,Function.iterate_zero,id_eq,add_sub_cancel_left] using hi'
  · intro z' hx' hy' hp' hq' 
    let w' : Paths (E (d:=d)) n n :=
      (fun t => (extChartAt I (a t)) (S^[t.val] z')-u t,
       fun t => (extChartAt I (b t)) (S.symm^[t.val] z')-v t)
    have hn : ‖w'‖≤δ := by
      rw [Prod.norm_def,max_le_iff]
      constructor
      · exact (pi_norm_le_iff_of_nonneg hδ.le).mpr (fun t => (hx' t).2)
      · exact (pi_norm_le_iff_of_nonneg hδ.le).mpr (fun t => (hy' t).2)
    have huf (t : Fin (n+1)) : u t+w'.1 t=(extChartAt I (a t)) (S^[t.val] z') := by
      dsimp only [w']; abel
    have hvf (t : Fin (n+1)) : v t+w'.2 t=(extChartAt I (b t)) (S.symm^[t.val] z') := by
      dsimp only [w']; abel
    have he : w'=w := hunique w' hn (fun t => by
        rw [huf,huf]
        simp only [f,localMap,Function.comp_apply]
        rw [(extChartAt I (a t.castSucc)).left_inv
          (by simpa only [extChartAt_source] using (hx' t.castSucc).1)]
        exact congrArg (extChartAt I (a t.succ)) (Function.iterate_succ_apply' S _ z').symm)
      (fun t => by
        rw [hvf,hvf]
        simp only [g,localMap,Function.comp_apply]
        rw [(extChartAt I (b t.castSucc)).left_inv
          (by simpa only [extChartAt_source] using (hy' t.castSucc).1)]
        exact congrArg (extChartAt I (b t.succ)) (Function.iterate_succ_apply' S.symm _ z').symm)
      (by rw [huf,hvf,hab]; rfl)
      (by simpa only [w',u,Fin.val_last] using hp')
      (by simpa only [w',v,Fin.val_last] using hq')
    apply (extChartAt I (a 0)).injOn
      (by simpa only [extChartAt_source,Fin.val_zero,Function.iterate_zero,id_eq] using (hx' 0).1)
      (by simpa only [extChartAt_source,Fin.val_zero,Function.iterate_zero,id_eq] using (hz 0).1)
    have hfirst := congrArg (fun q : Paths (E (d:=d)) n n => q.1 0) he
    have hc := (hz 0).2
    simp only [Fin.val_zero,Function.iterate_zero,id_eq] at hc
    rw [hc,←hfirst, huf]
    rfl
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open FiniteGreen FiniteGreen.Matching ShortBin
theorem gauged_join_ideal (Smap : Diffeomorph I I M M ∞) {n : ℕ}
    (a b : Fin (n+1) → M) (x y : M) (hab : a 0=b 0)
    (hx : ∀ t : Fin (n+1),Smap^[t.val] x∈(chartAt H (a t)).source)
    (hy : ∀ t : Fin (n+1),Smap.symm^[t.val] y∈(chartAt H (b t)).source)
    (hintx : I.IsInteriorPoint x) (hinty : I.IsInteriorPoint y)
    {K ε γ g α : ℝ} (A₀ A Z : Gauge d n K) (S₀ S T : Finset (Fin d))
    (V W : Submodule ℝ (E (d:=d)))
    (hdV : Module.finrank ℝ ((A.splitting S).fast n).range=Module.finrank ℝ V)
    (hdW : Module.finrank ℝ ((Z.splitting T).fast n).range=Module.finrank ℝ W)
    (hcV : ‖((A.splitting S).fast n).range.starProjection-V.starProjection‖≤1/2)
    (hcW : ‖((Z.splitting T).fast n).range.starProjection-W.starProjection‖≤1/2)
    (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hdS : S₀.card=S.card) (hdT : S₀ᶜ.card=T.card)
    (hcS : ‖(A₀.space S₀).starProjection-(A.space S).starProjection‖≤ε)
    (hcT : ‖(A₀.space S₀ᶜ).starProjection-(Z.space T).starProjection‖≤ε)
    (hsmall : Real.exp (2*K)*(2*ε)≤1/2)
    (hsA : ∀ j∈S,A.lam j≤γ-g) (hfA : ∀ j∈Sᶜ,γ+g≤A.lam j)
    (hsZ : ∀ j∈T,Z.lam j≤ -γ-g) (hfZ : ∀ j∈Tᶜ,-γ+g≤Z.lam j)
    (hgap : (2*Real.exp (2*K))*(2*(2*Real.exp (2*K)^2*Real.exp (-2*g*n)))≤1/2)
    (hα : |γ|+|g|≤α)
    (hstep₁ : ∀ t : Fin n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I Smap (a t.castSucc) (a t.succ) (Smap^[t.val] x))*A.U t=
        A.U (t+1)*EuclideanSplitting.rate A.lam 1)
    (hstep₂ : ∀ t : Fin n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I Smap.symm (b t.castSucc) (b t.succ) (Smap.symm^[t.val] y))*Z.U t=
        Z.U (t+1)*EuclideanSplitting.rate Z.lam 1)
    {C r δ : ℝ}
    (hC : 0≤C) (hr : 0 ≤ r) (hδ : 0<δ)
    (hd₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (Smap^[t.val] x)) δ,
      DifferentiableAt ℝ (localMap I Smap (a t.castSucc) (a t.succ)) z)
    (hd₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)) δ,
      DifferentiableAt ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ)) z)
    (hder₁ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (a t.castSucc)) (Smap^[t.val] x)) δ,
      ‖fderiv ℝ (localMap I Smap (a t.castSucc) (a t.succ)) z-
        fderiv ℝ (localMap I Smap (a t.castSucc) (a t.succ))
          ((extChartAt I (a t.castSucc)) (Smap^[t.val] x))‖≤
        C*‖z-(extChartAt I (a t.castSucc)) (Smap^[t.val] x)‖)
    (hder₂ : ∀ t : Fin n,∀ z∈closedBall ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)) δ,
      ‖fderiv ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ)) z-
        fderiv ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ))
          ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y))‖≤
        C*‖z-(extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)‖)
    (ht₁ : ∀ t : Fin (n+1),closedBall ((extChartAt I (a t)) (Smap^[t.val] x)) δ⊆
      (extChartAt I (a t)).target)
    (ht₂ : ∀ t : Fin (n+1),closedBall ((extChartAt I (b t)) (Smap.symm^[t.val] y)) δ⊆
      (extChartAt I (b t)).target)
    (hdom₁ : ∀ t : Fin n,closedBall ((extChartAt I (a t.castSucc)) (Smap^[t.val] x)) δ⊆
      domainU I Smap (a t.castSucc) (a t.succ))
    (hdom₂ : ∀ t : Fin n,closedBall ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y)) δ⊆
      domainU I Smap.symm (b t.castSucc) (b t.succ))
    (hnear : ‖(extChartAt I (b 0)) y-(extChartAt I (a 0)) x‖≤C*r)
    (hcontract : bvpInverseBound K α n*C*δ≤1/4)
    (hdata : bvpInverseBound K α n*C*r≤δ/4) :
    let C₁ := (A.splitting S).terminalProjection n V hdV hcV
    let C₂ := (Z.splitting T).terminalProjection n W hdW hcW
    let Q := bvpInverseBound K α n
    ∃ z : M,
      (∀ t : Fin (n+1),Smap^[t.val] z∈(chartAt H (a t)).source ∧
        ‖(extChartAt I (a t)) (Smap^[t.val] z)-(extChartAt I (a t)) (Smap^[t.val] x)‖≤δ/2) ∧
      (∀ t : Fin (n+1),Smap.symm^[t.val] z∈(chartAt H (b t)).source ∧
        ‖(extChartAt I (b t)) (Smap.symm^[t.val] z)-(extChartAt I (b t)) (Smap.symm^[t.val] y)‖≤δ/2) ∧
      C₁.P ((extChartAt I (a (Fin.last n))) (Smap^[n] z)-
        (extChartAt I (a (Fin.last n))) (Smap^[n] x))=0 ∧
      C₂.P ((extChartAt I (b (Fin.last n))) (Smap.symm^[n] z)-
        (extChartAt I (b (Fin.last n))) (Smap.symm^[n] y))=0 ∧
      (∀ t : Fin (n+1),‖(extChartAt I (a t)) (Smap^[t.val] z)-
        (extChartAt I (a t)) (Smap^[t.val] x)‖≤2*C*Q*r) ∧
      (∀ t : Fin (n+1),‖(extChartAt I (b t)) (Smap.symm^[t.val] z)-
        (extChartAt I (b t)) (Smap.symm^[t.val] y)‖≤2*C*Q*r) ∧
      ‖(extChartAt I (a 0)) z-(extChartAt I (a 0)) x-
        (A₀.splitting S₀).slow 0 ((extChartAt I (b 0)) y-(extChartAt I (a 0)) x)‖≤
        4*Real.exp (2*K)*(2*Real.exp (2*K))*(ε+2*Real.exp (2*K)^2*Real.exp (-2*g*n))*(C*r)+
          Q*C*(2*C*Q*r)^2 ∧
      ∀ z' : M,
        (∀ t : Fin (n+1),Smap^[t.val] z'∈(chartAt H (a t)).source ∧
          ‖(extChartAt I (a t)) (Smap^[t.val] z')-(extChartAt I (a t)) (Smap^[t.val] x)‖≤δ) →
        (∀ t : Fin (n+1),Smap.symm^[t.val] z'∈(chartAt H (b t)).source ∧
          ‖(extChartAt I (b t)) (Smap.symm^[t.val] z')-(extChartAt I (b t)) (Smap.symm^[t.val] y)‖≤δ) →
        C₁.P ((extChartAt I (a (Fin.last n))) (Smap^[n] z')-
          (extChartAt I (a (Fin.last n))) (Smap^[n] x))=0 →
        C₂.P ((extChartAt I (b (Fin.last n))) (Smap.symm^[n] z')-
          (extChartAt I (b (Fin.last n))) (Smap.symm^[n] y))=0 → z'=z := by
  intro C₁ C₂ Q
  obtain ⟨L,hL,hK,hcorr,hκ₁,hκ₂⟩ := gauge_boundary_control A₀ A Z S₀ S T V W
    hdV hdW hcV hcW hε hεhalf hdS hdT hcS hcT hsmall hsA hfA hsZ hfZ hgap
  have hnα : 0≤α := (add_nonneg (abs_nonneg γ) (abs_nonneg g)).trans hα
  have hboundA := A.unweighted S hnα
    (fun j hj => (hsA j hj).trans (by linarith [le_abs_self γ,neg_le_abs g]))
    (fun j hj => le_trans (by linarith [neg_le_abs γ,neg_le_abs g]) (hfA j hj))
  have hboundZ := Z.unweighted T hnα
    (fun j hj => (hsZ j hj).trans (by linarith [neg_le_abs γ,neg_le_abs g]))
    (fun j hj => le_trans (by linarith [le_abs_self γ,neg_le_abs g]) (hfZ j hj))
  have hU : 1≤bvpGrowth K α n := (by norm_num : (1:ℝ)≤2).trans (bvpGrowth_ge_two K α n)
  have hUG : Real.exp (2*K+α*n)≤bvpGrowth K α n := by dsimp [bvpGrowth]; linarith
  have hA₁ (t : Fin n) : fderiv ℝ (localMap I Smap (a t.castSucc) (a t.succ))
      ((extChartAt I (a t.castSucc)) (Smap^[t.val] x))=A.evolution.map (t+1) t :=
    gauge_actual_step I Smap _ _ _ A t (hx t.castSucc)
      (by simpa only [Fin.val_succ,Function.iterate_succ_apply'] using hx t.succ)
      (interior_iterate I Smap hintx t) (hstep₁ t)
  have hA₂ (t : Fin n) : fderiv ℝ (localMap I Smap.symm (b t.castSucc) (b t.succ))
      ((extChartAt I (b t.castSucc)) (Smap.symm^[t.val] y))=Z.evolution.map (t+1) t :=
    gauge_actual_step I Smap.symm _ _ _ Z t (hy t.castSucc)
      (by simpa only [Fin.val_succ,Function.iterate_succ_apply'] using hy t.succ)
      (interior_iterate I Smap.symm hinty t) (hstep₂ t)
  have hcontract' : let U := bvpGrowth K α n
      let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*(2*Real.exp (2*K)))*(1+2*D)+D)*C*δ≤1/4 := by
    simpa only [bvpInverseBound,show 2*(2*Real.exp (2*K))=4*Real.exp (2*K) by ring] using hcontract
  have hdata' : let U := bvpGrowth K α n
      let D := (2*U+U^4)*(n+n : ℕ)+U^2
      ((U+U^4)*(2*(2*Real.exp (2*K)))*(1+2*D)+D)*C*r≤δ/4 := by
    simpa only [bvpInverseBound,show 2*(2*Real.exp (2*K))=4*Real.exp (2*K) by ring] using hdata
  have hs₀ : ‖(A₀.splitting S₀).slow 0‖≤Real.exp (2*K) :=
    EuclideanSplitting.splitting_slow_norm _ _ _ _ _ _ 0
      (A₀.normU _ (Nat.zero_le n)) (A₀.normV _ (Nat.zero_le n))
  have hf₀ : ‖(A₀.splitting S₀).fast 0‖≤Real.exp (2*K) :=
    EuclideanSplitting.splitting_fast_norm _ _ _ _ _ _ 0
      (A₀.normU _ (Nat.zero_le n)) (A₀.normV _ (Nat.zero_le n))
  have hc₁ : ‖(A.splitting S).initialSpace.starProjection-
      ((A₀.splitting S₀).slow 0).range.starProjection‖≤ε := by
    simpa only [FiniteGreen.Splitting.initialSpace,←A.space_eq_range,←A₀.space_eq_range,
      norm_sub_rev] using hcS
  have hc₂ : ‖(Z.splitting T).initialSpace.starProjection-
      ((A₀.splitting S₀).fast 0).range.starProjection‖≤ε := by
    have heT : ((A₀.splitting S₀).fast 0).range = A₀.space S₀ᶜ :=
      EuclideanSplitting.splitting_fast_range _ _ _ _ _ _ 0
    simpa only [FiniteGreen.Splitting.initialSpace,←Z.space_eq_range,
      heT,norm_sub_rev] using hcT
  have hjoin := actual_join_ideal I Smap a b x y hab hx hy A.evolution Z.evolution
    (A.splitting S) (Z.splitting T) C₁ C₂ L hL hU hK A₀.evolution (A₀.splitting S₀)
    (Real.exp_nonneg _) hε (by positivity) hc₁ hc₂ hκ₁ hκ₂ hs₀ hf₀ hcorr
    (fun s u hsu hun => (hboundA.1 s u hsu hun).trans hUG)
    (fun s u hsu hun => (hboundA.2 s u hsu hun).trans hUG)
    (fun s u hsu hun => (hboundZ.1 s u hsu hun).trans hUG)
    (fun s u hsu hun => (hboundZ.2 s u hsu hun).trans hUG)
    (((A.splitting S).terminalProjection_J_norm n V hdV hcV).trans (bvpGrowth_ge_two K α n))
    (((A.splitting S).terminalProjection_P_norm n V hdV hcV).trans hU)
    (((Z.splitting T).terminalProjection_J_norm n W hdW hcW).trans (bvpGrowth_ge_two K α n))
    (((Z.splitting T).terminalProjection_P_norm n W hdW hcW).trans hU)
    hC hr hδ hA₁ hA₂ hd₁ hd₂ hder₁ hder₂ ht₁ ht₂ hdom₁ hdom₂ hnear hcontract' hdata'
  simpa only [Q,bvpInverseBound,show 2*(2*Real.exp (2*K))=4*Real.exp (2*K) by ring] using hjoin
end SmoothObstruction.ManifoldCoordinates

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

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n : ℕ} {B R : ℝ} {x : M}
open FiniteGreen ShortBin

lemma BilateralGauge.forward_space (A : BilateralGauge I S a c n B R x)
    (T : Finset (Fin d)) :
    (A.forward I S a c).space T=A.forwardSpace I S a c 0 T := by
  simp only [Gauge.space,BilateralGauge.forward,BilateralGauge.forwardSpace,
    Gauge.ofFinite,Nat.zero_min]

lemma BilateralGauge.backward_space (A : BilateralGauge I S a c n B R x)
    (T : Finset (Fin d)) :
    (A.backward I S a c).space T=A.forwardSpace I S a c 0 T := by
  simp only [Gauge.space,BilateralGauge.backward,BilateralGauge.forwardSpace,
    Gauge.ofFinite,Nat.zero_min,A.centerU,A.centerV]

lemma BilateralGauge.forward_fast (A : BilateralGauge I S a c n B R x)
    (T : Finset (Fin d)) :
    (((A.forward I S a c).splitting T).fast n).range=
      A.forwardSpace I S a c n Tᶜ := by
  rw [Gauge.splitting,EuclideanSplitting.splitting_fast_range]
  simp only [BilateralGauge.forward,BilateralGauge.forwardSpace,Gauge.ofFinite,Nat.min_self]

lemma BilateralGauge.backward_fast (A : BilateralGauge I S a c n B R x)
    (T : Finset (Fin d)) :
    (((A.backward I S a c).splitting T).fast n).range=
      A.backwardSpace I S a c n Tᶜ := by
  rw [Gauge.splitting,EuclideanSplitting.splitting_fast_range]
  simp only [BilateralGauge.backward,BilateralGauge.backwardSpace,Gauge.ofFinite,Nat.min_self]

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
open FiniteGreen ShortBin

private lemma projection_diff_iff (V : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d)) :
    V.orthogonalProjectionOnto (u-v)=0 ↔ V.starProjection u=V.starProjection v := by
  constructor
  · intro h
    have hh := congrArg Subtype.val h
    change V.starProjection (u-v)=0 at hh
    simpa only [map_sub,sub_eq_zero] using hh
  · intro h
    apply Subtype.ext
    change V.starProjection (u-v)=0
    simpa only [map_sub,sub_eq_zero] using h

/-- An actual two-sided joining. The uniform geometry is chosen BEFORE the
window, good gauges, cells, thresholds, or endpoint ranks. Every tube and Taylor
hypothesis is derived here from the source finite atlas; the only tube-domain
condition retained is the literal avoidance of the manifold boundary. -/
theorem original_gauged_join (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r₀ C : ℝ,0 < r₀ ∧ 1≤C ∧
      ∀ (c : M → ι) (n : ℕ) (B R ε γ g α r δ : ℝ) (q x y : M)
        (A₀ : BilateralGauge I S a c n B R q)
        (Ax : BilateralGauge I S a c n B R x)
        (Ay : BilateralGauge I S a c n B R y)
        (T₀ Tx Ty : Finset (Fin d))
        (V W : Submodule ℝ (EuclideanSpace ℝ (Fin d))),
        (∀ v,v∈K (c v)) → c x=c y → I.IsInteriorPoint x → I.IsInteriorPoint y →
        Module.finrank ℝ (Ax.forwardSpace I S a c n Tx)=Module.finrank ℝ V →
        Module.finrank ℝ (Ay.backwardSpace I S a c n Tyᶜ)=Module.finrank ℝ W →
        ‖(Ax.forwardSpace I S a c n Tx).starProjection-V.starProjection‖≤1/2 →
        ‖(Ay.backwardSpace I S a c n Tyᶜ).starProjection-W.starProjection‖≤1/2 →
        0≤ε → ε≤1/2 → T₀.card=Tx.card → T₀.card=Ty.card →
        ‖(A₀.forwardSpace I S a c 0 T₀ᶜ).starProjection-
          (Ax.forwardSpace I S a c 0 Txᶜ).starProjection‖≤ε →
        ‖(A₀.forwardSpace I S a c 0 T₀).starProjection-
          (Ay.forwardSpace I S a c 0 Ty).starProjection‖≤ε →
        Real.exp (2*B)*(2*ε)≤1/2 →
        (∀ j∈Txᶜ,Ax.lam j≤γ-g) → (∀ j∈Tx,γ+g≤Ax.lam j) →
        (∀ j∈Tyᶜ,Ay.lam j≤γ-g) → (∀ j∈Ty,γ+g≤Ay.lam j) →
        (2*Real.exp (2*B))*(2*(2*Real.exp (2*B)^2*Real.exp (-2*g*n)))≤1/2 →
        |γ|+|g|≤α → 0 ≤ r → 0<δ → δ ≤ r₀ →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆
          interior (range I)) →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) δ⊆
          interior (range I)) →
        ‖(extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x‖≤C*r →
        bvpInverseBound B α n*C*δ≤1/4 → bvpInverseBound B α n*C*r≤δ/4 →
        ∃ z : M,
          originalTube I S a c (n:=n) (δ/2) x z ∧
          originalTube I S.symm a c (n:=n) (δ/2) y z ∧
          originalEndpoint I S a c (n:=n) V x z ∧
          originalEndpoint I S.symm a c (n:=n) W y z ∧
          originalTube I S a c (n:=n) (2*C*bvpInverseBound B α n*r) x z ∧
          originalTube I S.symm a c (n:=n) (2*C*bvpInverseBound B α n*r) y z ∧
          ‖(extChartAt I (a (c x))) z-(extChartAt I (a (c x))) x-
            ((A₀.forward I S a c).splitting T₀ᶜ).slow 0
              ((extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x)‖≤
            4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C*r)+
              bvpInverseBound B α n*C*(2*C*bvpInverseBound B α n*r)^2 ∧
          ∀ z' : M,originalTube I S a c (n:=n) δ x z' →
            originalTube I S.symm a c (n:=n) δ y z' →
            originalEndpoint I S a c (n:=n) V x z' →
            originalEndpoint I S.symm a c (n:=n) W y z' → z'=z := by
  obtain ⟨rF,CF,hrF,hCF,hF⟩ := actual_tube_data I hclosed S a K hK hKU
  obtain ⟨rB,CB,hrB,hCB,hB⟩ := actual_tube_data I hclosed S.symm a K hK hKU
  let C := max CF CB
  have hFC : CF≤C := le_max_left _ _
  have hBC : CB≤C := le_max_right _ _
  have hC : 1≤C := hCF.trans hFC
  refine ⟨min rF rB,C,lt_min hrF hrB,hC,?_⟩
  intro c n B R ε γ g α r δ q x y A₀ Ax Ay T₀ Tx Ty V W hc hxy hix hiy
    hdV hdW hcV hcW hε hεhalf hdS hdT hcS hcT hsmall hsx hfx hsy hfy hgap hα hr hδ hδr
    hsafeF hsafeB hnear hcontract hdata
  let af : Fin (n+1) → M := fun t => a (c (S^[t.val] x))
  let ab : Fin (n+1) → M := fun t => a (c (S.symm^[t.val] y))
  have hgeomF (t : Fin (n+1)) := hF (c (S^[t.val] x)) (c (S (S^[t.val] x)))
    (S^[t.val] x) δ (hc _) (hc _) hδ.le (hδr.trans (min_le_left _ _)) (hsafeF t)
  have hgeomB (t : Fin (n+1)) := hB (c (S.symm^[t.val] y)) (c (S.symm (S.symm^[t.val] y)))
    (S.symm^[t.val] y) δ (hc _) (hc _) hδ.le (hδr.trans (min_le_right _ _)) (hsafeB t)
  have hstepF (t : Fin n) : (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S (af t.castSucc) (af t.succ) (S^[t.val] x))*(Ax.forward I S a c).U t=
        (Ax.forward I S a c).U (t+1)*EuclideanSplitting.rate (Ax.forward I S a c).lam 1 := by
    simpa only [af,Fin.val_castSucc,Fin.val_succ,BilateralGauge.forward,Gauge.ofFinite,
      Nat.min_eq_left t.isLt.le,Nat.min_eq_left (Nat.succ_le_of_lt t.isLt)] using Ax.stepF t t.isLt
  have hstepB (t : Fin n) : (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S.symm (ab t.castSucc) (ab t.succ) (S.symm^[t.val] y))*(Ay.backward I S a c).U t=
        (Ay.backward I S a c).U (t+1)*EuclideanSplitting.rate (Ay.backward I S a c).lam 1 := by
    simpa only [ab,Fin.val_castSucc,Fin.val_succ,BilateralGauge.backward,Gauge.ofFinite,
      Nat.min_eq_left t.isLt.le,Nat.min_eq_left (Nat.succ_le_of_lt t.isLt)] using Ay.stepB t t.isLt
  have hdV' : Module.finrank ℝ (((Ax.forward I S a c).splitting Txᶜ).fast n).range=
      Module.finrank ℝ V := by
    have he := Ax.forward_fast I S a c Txᶜ
    simp only [compl_compl] at he
    exact (congrArg (fun Z : Submodule ℝ (EuclideanSpace ℝ (Fin d)) => Module.finrank ℝ Z) he).trans hdV
  have hcV' : ‖(((Ax.forward I S a c).splitting Txᶜ).fast n).range.starProjection-
      V.starProjection‖≤1/2 := by simpa only [Ax.forward_fast,compl_compl] using hcV
  have hdW' : Module.finrank ℝ (((Ay.backward I S a c).splitting Ty).fast n).range=
      Module.finrank ℝ W := by
    exact (congrArg (fun Z : Submodule ℝ (EuclideanSpace ℝ (Fin d)) => Module.finrank ℝ Z)
      (Ay.backward_fast I S a c Ty)).trans hdW
  have hcW' : ‖(((Ay.backward I S a c).splitting Ty).fast n).range.starProjection-
      W.starProjection‖≤1/2 := by simpa only [Ay.backward_fast] using hcW
  have hjoin := gauged_join_ideal I S af ab x y
    (by simp only [af,ab,Fin.val_zero,Function.iterate_zero_apply,hxy])
    (fun t => hKU _ (hc _)) (fun t => hKU _ (hc _)) hix hiy
    (A₀.forward I S a c) (Ax.forward I S a c) (Ay.backward I S a c) T₀ᶜ Txᶜ Ty V W
    hdV' hdW' hcV' hcW' hε hεhalf
    (by simp only [Finset.card_compl,hdS]) (by simpa only [compl_compl] using hdT)
    (by simpa only [BilateralGauge.forward_space] using hcS)
    (by simpa only [BilateralGauge.forward_space,BilateralGauge.backward_space,compl_compl] using hcT)
    hsmall hsx (by simpa only [compl_compl,BilateralGauge.forward,Gauge.ofFinite] using hfx)
    (by intro j hj; change -Ay.lam j≤ -γ-g; linarith [hfy j hj])
    (by intro j hj; change -γ+g≤ -Ay.lam j; linarith [hsy j hj])
    hgap hα hstepF hstepB (show 0≤C by linarith) hr hδ
    (by intro t z hz; simpa only [af,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using ((hgeomF t.castSucc).2.2 z hz).1.differentiableAt (by simp))
    (by intro t z hz; simpa only [ab,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using ((hgeomB t.castSucc).2.2 z hz).1.differentiableAt (by simp))
    (by intro t z hz
        simpa only [af,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using
          (((hgeomF t.castSucc).2.2 z hz).2.2).trans (mul_le_mul_of_nonneg_right hFC (norm_nonneg _)))
    (by intro t z hz
        simpa only [ab,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using
          (((hgeomB t.castSucc).2.2 z hz).2.2).trans (mul_le_mul_of_nonneg_right hBC (norm_nonneg _)))
    (fun t => (hgeomF t).1) (fun t => (hgeomB t).1)
    (by intro t; simpa only [af,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using (hgeomF t.castSucc).2.1)
    (by intro t; simpa only [ab,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using (hgeomB t.castSucc).2.1)
    (by simpa only [af,ab,Fin.val_zero,Function.iterate_zero_apply] using hnear) hcontract hdata
  obtain ⟨z,hzF,hzB,hzV,hzW,hsharpF,hsharpB,hideal,hunique⟩ := hjoin
  have hV (z' : M) :
      (((Ax.forward I S a c).splitting Txᶜ).terminalProjection n V hdV' hcV').P
        ((extChartAt I (af (Fin.last n))) (S^[n] z')-
          (extChartAt I (af (Fin.last n))) (S^[n] x))=0 ↔
      originalEndpoint I S a c (n:=n) V x z' := by
    exact projection_diff_iff V _ _
  have hW (z' : M) :
      (((Ay.backward I S a c).splitting Ty).terminalProjection n W hdW' hcW').P
        ((extChartAt I (ab (Fin.last n))) (S.symm^[n] z')-
          (extChartAt I (ab (Fin.last n))) (S.symm^[n] y))=0 ↔
      originalEndpoint I S.symm a c (n:=n) W y z' := by
    exact projection_diff_iff W _ _
  refine ⟨z,hzF,hzB,(hV z).mp hzV,(hW z).mp hzW,?_,?_,hideal,?_⟩
  · exact fun t => ⟨(hzF t).1,hsharpF t⟩
  · exact fun t => ⟨(hzB t).1,hsharpB t⟩
  · intro z' hzF' hzB' hzV' hzW'
    exact hunique z' hzF' hzB' ((hV z').mpr hzV') ((hW z').mpr hzW')
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

namespace SmoothObstruction.PairLaw
open MeasureTheory Set Finset
open scoped ENNReal
variable {X α : Type*} [MeasurableSpace X] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Cellwise pair domination sums with the ORIGINAL weights 1/μ(Q). There
is no renormalization after restricting to G or to endpoint patterns. -/
theorem law_domination (μ : Measure X) (P : X → α)
    (G : Set (X × X)) (Φ : X × X → X × X) (hΦ : Measurable Φ)
    (C : ℝ≥0∞)
    (hc : ∀ a,(((cell μ P a).prod (cell μ P a)).restrict G).map Φ≤
      C • (cell μ P a).prod (cell μ P a)) :
    ((law μ P).restrict G).map Φ≤C • law μ P := by
  have he : ((law μ P).restrict G).map Φ=
      ∑ a,(μ (P ⁻¹' {a}))⁻¹ • (((cell μ P a).prod (cell μ P a)).restrict G).map Φ := by
    rw [law,←Measure.restrictₗ_apply,map_sum,
      ←Measure.mapₗ_apply_of_measurable hΦ,map_sum]
    simp only [Measure.restrictₗ_apply,Measure.restrict_smul,
      Measure.mapₗ_apply_of_measurable hΦ,Measure.map_smul]
  rw [he,law,Finset.smul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [smul_smul,mul_comm] using
    smul_le_smul_left ((μ (P ⁻¹' {a}))⁻¹) (hc a)

/-- Joint domination yields exactly the first-output switch law 2μ, not
a law normalized by the retained mass. -/
theorem first_output_domination (μ : Measure X) [IsFiniteMeasure μ]
    (P : X → α) (hP : Measurable P) (G : Set (X × X))
    (Φ : X × X → X × X) (hΦ : Measurable Φ) (C : ℝ≥0∞)
    (hdom : ((law μ P).restrict G).map Φ≤C • law μ P) :
    ((law μ P).restrict G).map (fun z => (Φ z).1)≤C • μ := by
  have h := Measure.map_mono hdom measurable_fst
  rw [Measure.map_map measurable_fst hΦ,
    Measure.map_smul,first_marginal μ P hP] at h
  exact h
end SmoothObstruction.PairLaw

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

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- A common output in two small selected tubes puts their centers in each
other's original chart, with a uniform linear coordinate bound. The chart
selector can be discontinuous: only its finite compact carrying patches are
used. This is the comparison needed to invoke old-tube rigidity when two
canonical switches have the same output. -/
theorem uniform_common_output (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1≤C ∧ ∀ (i j : ι) (x y z : M) (ρ : ℝ),
      x∈K i → y∈K j → 0≤ρ → ρ ≤ r →
      closedBall ((extChartAt I (a j)) y) ρ⊆interior (range I) →
      z∈(chartAt H (a i)).source → z∈(chartAt H (a j)).source →
      ‖(extChartAt I (a i)) z-(extChartAt I (a i)) x‖≤ρ →
      ‖(extChartAt I (a j)) z-(extChartAt I (a j)) y‖≤ρ →
      y∈(chartAt H (a i)).source ∧
      ‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖≤C*ρ := by
  have hex (i : ι) : ∃ v : ℝ,0<v ∧ cthickening v (K i)⊆(chartAt H (a i)).source :=
    (hK i).exists_cthickening_subset_open (chartAt H (a i)).open_source (hKU i)
  choose v hv hvU using hex
  obtain ⟨v₀,hv₀,hv₀i⟩ := CarriedCharts.finite_positive_lower v hv
  let L (i : ι) := cthickening v₀ (K i)
  have hL (i : ι) : IsCompact (L i) := (hK i).cthickening
  have hLU (i : ι) : L i⊆(chartAt H (a i)).source :=
    (cthickening_mono (hv₀i i) (K i)).trans (hvU i)
  obtain ⟨r,C,hr,hC,ht⟩ := uniform_chart_transfer I hclosed a L hL hLU
  obtain ⟨s,hs,hm⟩ := CoordinateTubes.uniform_inverse_modulus I hclosed a K hK hKU
    (ε:=v₀/3) (by positivity)
  refine ⟨min r s,C+1,lt_min hr hs,by linarith,?_⟩
  intro i j x y z ρ hxi hyj hρ hρr hsafe hzi hzj hzx hzy
  have hρs : ρ ≤ s := hρr.trans (min_le_right _ _)
  have hzx' := hm i x hxi z hzi (hzx.trans hρs)
  have hzy' := hm j y hyj z hzj (hzy.trans hρs)
  have hyx : dist y x≤v₀ := by
    have hh := dist_triangle y z x
    rw [dist_comm y z] at hh
    linarith
  have hyi : y∈L i := mem_cthickening_of_dist_le _ _ _ _ hxi hyx
  have hyj' : y∈L j := self_subset_cthickening (K j) hyj
  have ht' := ht j i y z ρ hyj' hyi hρ (hρr.trans (min_le_left _ _)) hsafe hzj hzy
  refine ⟨hLU i hyi,?_⟩
  have htri := norm_sub_le_norm_sub_add_norm_sub ((extChartAt I (a i)) y) ((extChartAt I (a i)) z)
    ((extChartAt I (a i)) x)
  rw [norm_sub_rev ((extChartAt I (a i)) y) ((extChartAt I (a i)) z)] at htri
  have hcz : C*‖(extChartAt I (a j)) z-(extChartAt I (a j)) y‖≤C*ρ :=
    mul_le_mul_of_nonneg_left hzy (by linarith)
  nlinarith [ht'.2]
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.SwitchRecovery
open Set
variable {X α β E F : Type*}

/-- Exact recovered cell and endpoint labels force the same four endpoint
maps even when the two inputs were certified by different frame witnesses. -/
theorem global_injective_tubes
    (c : X → α) (b : X → β) (future past : X → X)
    (U : α → β → X → E) (V : α → β → X → F)
    (TF TB RF RB : X → X → Prop) (R : Set X) (G : Set (X × X))
    (Φ : X × X → X × X)
    (hcommonF : ∀ x∈R,∀ y∈R,∀ z,TF x z → TF y z → RF x y)
    (hcommonB : ∀ x∈R,∀ y∈R,∀ z,TB x z → TB y z → RB x y)
    (hgood : ∀ u∈G,u.1∈R ∧ u.2∈R)
    (hc : ∀ u∈G,c u.1=c u.2 ∧ c (Φ u).1=c u.1)
    (hb : ∀ u∈G,
      b (future (Φ u).1)=b (future u.1) ∧
      b (past (Φ u).2)=b (past u.1) ∧
      b (future (Φ u).2)=b (future u.2) ∧
      b (past (Φ u).1)=b (past u.2))
    (heq : ∀ u∈G,
      U (c u.1) (b (future u.1)) (Φ u).1=U (c u.1) (b (future u.1)) u.1 ∧
      V (c u.1) (b (past u.1)) (Φ u).2=V (c u.1) (b (past u.1)) u.1 ∧
      U (c u.2) (b (future u.2)) (Φ u).2=U (c u.2) (b (future u.2)) u.2 ∧
      V (c u.2) (b (past u.2)) (Φ u).1=V (c u.2) (b (past u.2)) u.2)
    (hshadow : ∀ u∈G,TF u.1 (Φ u).1 ∧ TB u.1 (Φ u).2 ∧
      TF u.2 (Φ u).2 ∧ TB u.2 (Φ u).1)
    (hrigid : ∀ x∈R,∀ y,
      U (c x) (b (future x)) y=U (c x) (b (future x)) x →
      V (c x) (b (past x)) y=V (c x) (b (past x)) x →
      RF x y → RB x y → y=x) :
    InjOn Φ G := by
  intro u hu v hv huv
  have hc₁ : c v.1=c u.1 := (hc v hv).2.symm.trans (by rw [←huv]; exact (hc u hu).2)
  have hc₂ : c v.2=c u.2 := (hc v hv).1.symm.trans (hc₁.trans (hc u hu).1)
  have hb₁ : b (future v.1)=b (future u.1) := (hb v hv).1.symm.trans (by rw [←huv]; exact (hb u hu).1)
  have hb₂ : b (past v.1)=b (past u.1) := (hb v hv).2.1.symm.trans (by rw [←huv]; exact (hb u hu).2.1)
  have hb₃ : b (future v.2)=b (future u.2) := (hb v hv).2.2.1.symm.trans (by rw [←huv]; exact (hb u hu).2.2.1)
  have hb₄ : b (past v.2)=b (past u.2) := (hb v hv).2.2.2.symm.trans (by rw [←huv]; exact (hb u hu).2.2.2)
  have he₁ := (heq v hv).1.symm
  have he₂ := (heq v hv).2.1.symm
  have he₃ := (heq v hv).2.2.1.symm
  have he₄ := (heq v hv).2.2.2.symm
  rw [hc₁,hb₁,←huv] at he₁
  rw [hc₁,hb₂,←huv] at he₂
  rw [hc₂,hb₃,←huv] at he₃
  rw [hc₂,hb₄,←huv] at he₄
  have hsu := hshadow u hu
  have hsv := hshadow v hv
  rw [←huv] at hsv
  have hxu := (hgood u hu).1
  have hyu := (hgood u hu).2
  have hxv := (hgood v hv).1
  have hyv := (hgood v hv).2
  exact Prod.ext
    (hrigid u.1 hxu v.1 (he₁.trans (heq u hu).1) (he₂.trans (heq u hu).2.1)
      (hcommonF u.1 hxu v.1 hxv (Φ u).1 hsu.1 hsv.1)
      (hcommonB u.1 hxu v.1 hxv (Φ u).2 hsu.2.1 hsv.2.1)).symm
    (hrigid u.2 hyu v.2 (he₃.trans (heq u hu).2.2.1) (he₄.trans (heq u hu).2.2.2)
      (hcommonF u.2 hyu v.2 hyv (Φ u).2 hsu.2.2.1 hsv.2.2.1)
      (hcommonB u.2 hyu v.2 hyv (Φ u).1 hsu.2.2.2 hsv.2.2.2)).symm
end SmoothObstruction.SwitchRecovery

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Common sharp outputs recover the original full orbit tube, despite all
intermediate selected charts being allowed to differ. -/
theorem original_common_tubes (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1≤C ∧ ∀ (S : Diffeomorph I I M M ∞)
      (c : M → ι) (n : ℕ) (ρ δ : ℝ) (x y z : M),
      (∀ v,v∈K (c v)) → 0≤ρ → ρ ≤ r → C*ρ≤δ →
      (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ
        ⊆interior (range I)) →
      originalTube I S a c (n:=n) ρ x z → originalTube I S a c (n:=n) ρ y z →
      originalTube I S a c (n:=n) δ x y := by
  obtain ⟨r,C,hr,hC,hh⟩ := uniform_common_output I hclosed a K hK hKU
  refine ⟨r,C,hr,hC,?_⟩
  intro S c n ρ δ x y z hc hρ hρr hδ hsafe hx hy t
  obtain ⟨hs,hb⟩ := hh (c (S^[t.val] x)) (c (S^[t.val] y))
    (S^[t.val] x) (S^[t.val] y) (S^[t.val] z) ρ (hc _) (hc _)
    hρ hρr (hsafe t) (hx t).1 (hy t).1 (hx t).2 (hy t).2
  exact ⟨hs,hb.trans hδ⟩

omit [ProperSpace M] [IsManifold I ∞ M] [Fintype ι] in
/-- Original cell and endpoint recovery makes the measurable canonical
switch globally one-to-one. The four endpoint equations are the original
ones, and rigidity is invoked in OLD charts, not independently chosen ones. -/
theorem original_switch_injective {C J : Type*}
    (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    (P : M → C) (L : M → J) (π : J → C) (chart : C → ι)
    (hπ : ∀ x,π (L x)=P x) (hchart : ∀ x,chart (P x)=c x)
    (n : ℕ) (δ ρ : ℝ) (R : Set M) (G : Set (M×M)) (Φ : M×M → M×M)
    (Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hcommonF : ∀ x∈R,∀ y∈R,∀ z,
      originalTube I S a c (n:=n) ρ x z → originalTube I S a c (n:=n) ρ y z →
      originalTube I S a c (n:=n) δ x y)
    (hcommonB : ∀ x∈R,∀ y∈R,∀ z,
      originalTube I S.symm a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
      originalTube I S.symm a c (n:=n) δ x y)
    (hgood : ∀ u∈G,u.1∈R ∧ u.2∈R)
    (hcell : ∀ u∈G,L u.1=L u.2 ∧ L (Φ u).1=L u.1)
    (hlabels : ∀ u∈G,
      P (S^[n] (Φ u).1)=P (S^[n] u.1) ∧
      P (S.symm^[n] (Φ u).2)=P (S.symm^[n] u.1) ∧
      P (S^[n] (Φ u).2)=P (S^[n] u.2) ∧
      P (S.symm^[n] (Φ u).1)=P (S.symm^[n] u.2))
    (heq : ∀ u∈G,
      originalEndpoint I S a c (n:=n) (Wf (P u.1,P (S^[n] u.1))) u.1 (Φ u).1 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P u.1,P (S.symm^[n] u.1))) u.1 (Φ u).2 ∧
      originalEndpoint I S a c (n:=n) (Wf (P u.2,P (S^[n] u.2))) u.2 (Φ u).2 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P u.2,P (S.symm^[n] u.2))) u.2 (Φ u).1)
    (hshadow : ∀ u∈G,
      originalTube I S a c (n:=n) ρ u.1 (Φ u).1 ∧
      originalTube I S.symm a c (n:=n) ρ u.1 (Φ u).2 ∧
      originalTube I S a c (n:=n) ρ u.2 (Φ u).2 ∧
      originalTube I S.symm a c (n:=n) ρ u.2 (Φ u).1)
    (hrigid : ∀ x∈R,∀ z,
      originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ x z →
      originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
      originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x z → z=x) :
    InjOn Φ G := by
  let U : J → C → M → EuclideanSpace ℝ (Fin d) := fun Q b z =>
    (Wf (π Q,b)).starProjection ((extChartAt I (a (chart b))) (S^[n] z))
  let V : J → C → M → EuclideanSpace ℝ (Fin d) := fun Q b z =>
    (Wb (π Q,b)).starProjection ((extChartAt I (a (chart b))) (S.symm^[n] z))
  have hf (x z : M) : U (L x) (P (S^[n] x)) z=U (L x) (P (S^[n] x)) x ↔
      originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z := by
    simp only [U,hπ,hchart,originalEndpoint]
  have hb (x z : M) : V (L x) (P (S.symm^[n] x)) z=V (L x) (P (S.symm^[n] x)) x ↔
      originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x z := by
    simp only [V,hπ,hchart,originalEndpoint]
  refine SwitchRecovery.global_injective_tubes L P (S^[n]) (S.symm^[n]) U V
    (originalTube I S a c (n:=n) ρ) (originalTube I S.symm a c (n:=n) ρ)
    (originalTube I S a c (n:=n) δ) (originalTube I S.symm a c (n:=n) δ)
    R G Φ hcommonF hcommonB hgood hcell hlabels ?_ hshadow ?_
  · intro u hu
    obtain ⟨h1,h2,h3,h4⟩ := heq u hu
    exact ⟨(hf _ _).mpr h1,(hb _ _).mpr h2,(hf _ _).mpr h3,(hb _ _).mpr h4⟩
  · intro x hx z h1 h2 h3 h4
    exact hrigid x hx z h3 h4 ((hf _ _).mp h1) ((hb _ _).mp h2)
end SmoothObstruction.ManifoldCoordinates

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

/-- Recovery of the ORIGINAL coarse label, without recording an orbit-chart
itinerary in the partition. The only exclusions are the fixed chart core and
old coarse-grid wall strip at the particular time under consideration. -/
theorem original_tube_labels
    (hclosed : IsClosed (range I)) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {s : ℝ} (hs : 0 < s) :
    ∃ σ : ℝ,0<σ ∧ ∀ {C : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
      (P : M → C) (V W : Set M) (δ ρ : ℝ) (n : ℕ),
      (∀ u,u∈K (c u)) →
      (∀ x∈V,∀ z,dist z x ≤ s → c z=c x) →
      (∀ x z,x∉W → c z=c x →
        ‖ChartDensity.coordinates I (a (c x)) z-ChartDensity.coordinates I (a (c x)) x‖≤δ/4 →
        P z=P x) → ρ≤σ → ρ≤δ/4 →
      ∀ x z,originalTube I S a c (n:=n) ρ x z →
      ∀ t : Fin (n+1),S^[t.val] x∈V → S^[t.val] x∉W → P (S^[t.val] z)=P (S^[t.val] x) := by
  obtain ⟨σ,hσ,hm⟩ := uniform_original_shadow I hclosed a K hK hKU hs
  refine ⟨σ,hσ,?_⟩
  intro C S c P V W δ ρ n hc hcore hrec hρσ hρδ x z ht t hv hw
  apply hrec _ _ hw (hcore _ hv _ ((hm S c n ρ x z hc hρσ ht t).le))
  rw [ChartDensity.coordinates_eq I _ _ (by simpa only [extChartAt_source] using (ht t).1),
    ChartDensity.coordinates_eq I _ _ (by simpa only [extChartAt_source] using hKU _ (hc _))]
  exact (ht t).2.trans hρδ

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric MeasureTheory
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Actual sharp tubes and old coarse/product grid margins recover both
full ORIGINAL cells and all four endpoint labels. Common-output old tubes
then prove global injectivity, even for unequal selected intermediate charts.
No partition is refined by an endpoint, frame witness, or orbit itinerary. -/
theorem recovered_original_pair (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {s : ℝ} (hs : 0 < s) :
    ∃ σ r₁ C₁ : ℝ,0<σ ∧ 0 < r₁ ∧ 1≤C₁ ∧
      ∀ {C J : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
        (P : M → C) (L : M → J) (π : J → C) (chart : C → ι)
        (_ : ∀ x,π (L x)=P x) (_ : ∀ x,chart (P x)=c x)
        (n : ℕ) (δ ρ δc δp H₀ E : ℝ) (R V Wc Wp : Set M)
        (U : M → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (Φ : M×M → M×M) (Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
        (∀ x,x∈K (c x)) → 0≤ρ → ρ≤σ → ρ≤δc/4 → ρ ≤ r₁ → C₁*ρ≤δ →
        0≤H₀ → H₀*E≤δp/4 →
        (∀ x∈V,∀ z,dist z x ≤ s → c z=c x) →
        (∀ x z,x∉Wc → c z=c x →
          ‖ChartDensity.coordinates I (a (c x)) z-ChartDensity.coordinates I (a (c x)) x‖≤δc/4 → P z=P x) →
        (∀ x y z,x∈R → L x=L y → x∉Wp → y∉Wp → P z=P x →
          H₀*‖ChartDensity.coordinates I (a (c x)) z-(ChartDensity.coordinates I (a (c x)) x+
            U x (ChartDensity.coordinates I (a (c x)) y-ChartDensity.coordinates I (a (c x)) x))‖≤δp/4 → L z=L x) →
        (∀ x∈R,x∈V ∧ x∉Wc ∧ x∉Wp ∧
          S^[n] x∈V ∧ S^[n] x∉Wc ∧ S.symm^[n] x∈V ∧ S.symm^[n] x∉Wc) →
        (∀ x∈R,∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) δ⊆interior (range I)) →
        (∀ u : M×M,u.1∈R → u.2∈R → L u.1=L u.2 →
          originalTube I S a c (n:=n) ρ u.1 (Φ u).1 ∧
          originalTube I S.symm a c (n:=n) ρ u.2 (Φ u).1 ∧
          originalTube I S a c (n:=n) ρ u.2 (Φ u).2 ∧
          originalTube I S.symm a c (n:=n) ρ u.1 (Φ u).2 ∧
          ‖(extChartAt I (a (c u.1))) (Φ u).1-(extChartAt I (a (c u.1))) u.1-
            U u.1 ((extChartAt I (a (c u.2))) u.2-(extChartAt I (a (c u.1))) u.1)‖≤E ∧
          ‖(extChartAt I (a (c u.2))) (Φ u).2-(extChartAt I (a (c u.2))) u.2-
            U u.2 ((extChartAt I (a (c u.1))) u.1-(extChartAt I (a (c u.2))) u.2)‖≤E) →
        (∀ u : M×M,u.1∈R → u.2∈R → L u.1=L u.2 →
          originalEndpoint I S a c (n:=n) (Wf (P u.1,P (S^[n] u.1))) u.1 (Φ u).1 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u.1,P (S.symm^[n] u.1))) u.1 (Φ u).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P u.2,P (S^[n] u.2))) u.2 (Φ u).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u.2,P (S.symm^[n] u.2))) u.2 (Φ u).1) →
        (∀ x∈R,∀ z,
          originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ x z →
          originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x z → z=x) →
        let G := {u : M×M | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
        (∀ u∈G,L (Φ u).1=L u.1 ∧ L (Φ u).2=L u.2) ∧
        (∀ u∈G,P (S^[n] (Φ u).1)=P (S^[n] u.1) ∧
          P (S.symm^[n] (Φ u).2)=P (S.symm^[n] u.1) ∧
          P (S^[n] (Φ u).2)=P (S^[n] u.2) ∧
          P (S.symm^[n] (Φ u).1)=P (S.symm^[n] u.2)) ∧ InjOn Φ G := by
  obtain ⟨σ,hσ,hl⟩ := original_tube_labels I hclosed a K hK hKU hs
  obtain ⟨r₁,C₁,hr₁,hC₁,hcommon⟩ := original_common_tubes I hclosed a K hK hKU
  refine ⟨σ,r₁,C₁,hσ,hr₁,hC₁,?_⟩
  intro C J S c P L π chart hπ hchart n δ ρ δc δp H₀ E R V Wc Wp U Φ Wf Wb
    hc hρ hρσ hρc hρr hρδ hH₀ hE hcore hcoarse hprod hret hsafe ht heq hrigid G
  have hρδ' : ρ≤δ := (le_mul_of_one_le_left hρ hC₁).trans hρδ
  have hPs {x y : M} (hh : L x=L y) : P x=P y := by rw [←hπ x,←hπ y,hh]
  have hcs {x y : M} (hh : L x=L y) : c x=c y := by rw [←hchart x,←hchart y,hPs hh]
  have hlabel (F : Diffeomorph I I M M ∞) (x z : M)
      (hh : originalTube I F a c (n:=n) ρ x z) (t : Fin (n+1))
      (hv : F^[t.val] x∈V) (hw : F^[t.val] x∉Wc) : P (F^[t.val] z)=P (F^[t.val] x) :=
    hl F c P V Wc δc ρ n hc hcore hcoarse hρσ hρc x z hh t hv hw
  have hret0 (x : M) (hx : x∈R) := hret x hx
  have hsrc (x : M) : x∈(extChartAt I (a (c x))).source := by
    simpa only [extChartAt_source] using hKU _ (hc x)
  have hcell (u : M×M) (hu : u∈G) : L (Φ u).1=L u.1 ∧ L (Φ u).2=L u.2 := by
    obtain ⟨htf,htb,hsf,hsb,hiz,hiw⟩ := ht u hu.1 hu.2.1 hu.2.2
    have hzP : P (Φ u).1=P u.1 := by
      simpa only [Fin.val_zero,Function.iterate_zero_apply] using hlabel S u.1 (Φ u).1 htf 0
        (by simpa using (hret0 u.1 hu.1).1) (by simpa using (hret0 u.1 hu.1).2.1)
    have hwP : P (Φ u).2=P u.2 := by
      simpa only [Fin.val_zero,Function.iterate_zero_apply] using hlabel S u.2 (Φ u).2 hsf 0
        (by simpa using (hret0 u.2 hu.2.1).1) (by simpa using (hret0 u.2 hu.2.1).2.1)
    have htz : (Φ u).1∈(extChartAt I (a (c u.1))).source := by
      simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (htf 0).1
    have htw : (Φ u).2∈(extChartAt I (a (c u.2))).source := by
      simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (hsf 0).1
    have hcross1 : u.2∈(extChartAt I (a (c u.1))).source := by rw [hcs hu.2.2]; exact hsrc u.2
    have hcross2 : u.1∈(extChartAt I (a (c u.2))).source := by rw [←hcs hu.2.2]; exact hsrc u.1
    constructor
    · apply hprod u.1 u.2 (Φ u).1 hu.1 hu.2.2 (hret0 u.1 hu.1).2.2.1 (hret0 u.2 hu.2.1).2.2.1 hzP
      rw [ChartDensity.coordinates_eq I _ _ htz,ChartDensity.coordinates_eq I _ _ (hsrc u.1),
        ChartDensity.coordinates_eq I _ _ hcross1]
      have hh := mul_le_mul_of_nonneg_left hiz hH₀
      rw [←hcs hu.2.2] at hh
      simpa only [sub_add_eq_sub_sub] using hh.trans hE
    · apply hprod u.2 u.1 (Φ u).2 hu.2.1 hu.2.2.symm (hret0 u.2 hu.2.1).2.2.1 (hret0 u.1 hu.1).2.2.1 hwP
      rw [ChartDensity.coordinates_eq I _ _ htw,ChartDensity.coordinates_eq I _ _ (hsrc u.2),
        ChartDensity.coordinates_eq I _ _ hcross2]
      have hh := mul_le_mul_of_nonneg_left hiw hH₀
      rw [hcs hu.2.2] at hh
      simpa only [sub_add_eq_sub_sub] using hh.trans hE
  have hlabels (u : M×M) (hu : u∈G) :
      P (S^[n] (Φ u).1)=P (S^[n] u.1) ∧
      P (S.symm^[n] (Φ u).2)=P (S.symm^[n] u.1) ∧
      P (S^[n] (Φ u).2)=P (S^[n] u.2) ∧
      P (S.symm^[n] (Φ u).1)=P (S.symm^[n] u.2) := by
    obtain ⟨htf,htb,hsf,hsb,_,_⟩ := ht u hu.1 hu.2.1 hu.2.2
    have hfx := hlabel S u.1 (Φ u).1 htf (Fin.last n) (hret0 u.1 hu.1).2.2.2.1 (hret0 u.1 hu.1).2.2.2.2.1
    have hbx := hlabel S.symm u.1 (Φ u).2 hsb (Fin.last n) (hret0 u.1 hu.1).2.2.2.2.2.1 (hret0 u.1 hu.1).2.2.2.2.2.2
    have hfy := hlabel S u.2 (Φ u).2 hsf (Fin.last n) (hret0 u.2 hu.2.1).2.2.2.1 (hret0 u.2 hu.2.1).2.2.2.2.1
    have hby := hlabel S.symm u.2 (Φ u).1 htb (Fin.last n) (hret0 u.2 hu.2.1).2.2.2.2.2.1 (hret0 u.2 hu.2.1).2.2.2.2.2.2
    exact ⟨hfx,hbx,hfy,hby⟩
  refine ⟨hcell,hlabels,?_⟩
  apply original_switch_injective I S a c P L π chart hπ hchart n δ ρ R G Φ Wf Wb
  · intro x hx y hy z hxt hyt
    exact hcommon S c n ρ δ x y z hc hρ hρr hρδ
      (fun t => (closedBall_subset_closedBall hρδ').trans (hsafe y hy t).1) hxt hyt
  · intro x hx y hy z hxt hyt
    exact hcommon S.symm c n ρ δ x y z hc hρ hρr hρδ
      (fun t => (closedBall_subset_closedBall hρδ').trans (hsafe y hy t).2) hxt hyt
  · exact fun u hu => ⟨hu.1,hu.2.1⟩
  · exact fun u hu => ⟨hu.2.2,(hcell u hu).1⟩
  · exact hlabels
  · exact fun u hu => heq u hu.1 hu.2.1 hu.2.2
  · intro u hu
    obtain ⟨h1,h2,h3,h4,_,_⟩ := ht u hu.1 hu.2.1 hu.2.2
    exact ⟨h1,h4,h3,h2⟩
  · exact hrigid
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

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d p : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    {ι A : Type*}
local notation "E₀" => EuclideanSpace ℝ (Fin d)

lemma inverse_continuousAt_interior (a : M) (u : E₀)
    (hu : u∈(extChartAt I a).target) (hi : u∈interior (range I)) :
    ContinuousAt (extChartAt I a).symm u := by
  have ht := extChartAt_target_mem_nhdsWithin_of_mem hu
  rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hi)] at ht
  exact (continuousOn_extChartAt_symm a u hu).continuousAt ht

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Selection
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

namespace SmoothObstruction.CanonicalRelation
open Set MeasureTheory Filter Topology

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y]

/-- A Borel relation with exactly one output at every input has a genuine
measurable solution map. Its definition does not depend on any auxiliary
frame certificate used to obtain existence and uniqueness. -/
theorem measurable_solution (R : Set (X × Y)) (hR : MeasurableSet R)
    (hex : ∀ x,∃! y,(x,y)∈R) :
    ∃ f : X → Y,Measurable f ∧ (∀ x,(x,f x)∈R) ∧
      ∀ x y,(x,y)∈R → y=f x := by
  classical
  let f : X → Y := fun x => (hex x).choose
  have hf (x : X) : (x,f x)∈R := (hex x).choose_spec.1
  have hu (x : X) (y : Y) (hy : (x,y)∈R) : y=f x :=
    (hex x).choose_spec.2 y hy
  let : StandardBorelSpace R := hR.standardBorel
  let π : R → X := fun z => z.val.1
  have hπ : Measurable π := measurable_fst.comp measurable_subtype_coe
  have hsurj : Function.Surjective π := fun x => ⟨⟨(x,f x),hf x⟩,rfl⟩
  have he : f ∘ π=(fun z : R => z.val.2) := by
    funext z
    exact (hu z.val.1 z.val.2 z.property).symm
  have hm : Measurable (f ∘ π) := by
    rw [he]
    exact measurable_snd.comp measurable_subtype_coe
  exact ⟨f,(Measurable.measurable_comp_iff_of_surjective hπ hsurj).mp hm,hf,hu⟩

/-- The retained set has its original Borel subspace, not a conditioned
probability space. The measurable total extension is only for convenient
pushforward notation; it is equal to the canonical solution on the carrier. -/
theorem retained_solution [Nonempty Y] (G : Set X) (hG : MeasurableSet G)
    (R : X → Y → Prop) (hR : MeasurableSet {z : X×Y | z.1∈G ∧ R z.1 z.2})
    (hex : ∀ x∈G,∃! y,R x y) :
    ∃ f : X → Y,Measurable f ∧ (∀ x∈G,R x (f x)) ∧
      ∀ x∈G,∀ y,R x y → y=f x := by
  classical
  let : StandardBorelSpace G := hG.standardBorel
  let R' : Set (G×Y) := {z | R z.1.val z.2}
  have hR' : MeasurableSet R' := by
    have hm : Measurable (fun z : G×Y => (z.1.val,z.2)) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
    have he : R'= (fun z : G×Y => (z.1.val,z.2)) ⁻¹' {z : X×Y | z.1∈G ∧ R z.1 z.2} := by
      ext z
      simp only [R',mem_ofPred_eq,Set.mem_preimage]
      exact ⟨fun h => ⟨z.1.property,h⟩,fun h => h.2⟩
    rw [he]
    exact hR.preimage hm
  obtain ⟨f,hf,hfr,hfu⟩ := measurable_solution R' hR' (fun x => hex x x.property)
  obtain ⟨F,hF,hFf⟩ := (MeasurableEmbedding.subtype_coe hG).exists_measurable_extend hf
    (fun _ => inferInstance)
  have he (x : G) : F x=f x := congrFun hFf x
  refine ⟨F,hF,?_,?_⟩
  · intro x hx
    rw [he ⟨x,hx⟩]
    exact hfr ⟨x,hx⟩
  · intro x hx y hy
    rw [he ⟨x,hx⟩]
    exact hfu ⟨x,hx⟩ y hy

end SmoothObstruction.CanonicalRelation

namespace SmoothObstruction.SelectedTube
open Set MeasureTheory
variable {X C E : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
lemma measurable_evaluate (φ : C → X → E) (hφ : ∀ c,Measurable (φ c)) :
    Measurable (fun p : C×X => φ p.1 p.2) :=
  measurable_from_prod_countable_right hφ

lemma measurable_tube (q : X → C) (hq : Measurable q)
    (U : C → Set X) (hU : ∀ c,MeasurableSet (U c))
    (φ : C → X → E) (hφ : ∀ c,Measurable (φ c))
    (f : ℕ → X → X) (hf : ∀ t,Measurable (f t)) (n : ℕ) (δ : ℝ) :
    MeasurableSet {p : X×X | tube q U φ f n δ p.1 p.2} := by
  have hu : MeasurableSet {p : C×X | p.2∈U p.1} := by
    have he : {p : C×X | p.2∈U p.1}=⋃ c,({c} ×ˢ U c) := by
      ext p
      simp only [mem_ofPred_eq,mem_iUnion,mem_prod,mem_singleton_iff]
      exact ⟨fun h => ⟨p.1,rfl,h⟩,fun ⟨c,hc,h⟩ => hc ▸ h⟩
    rw [he]
    exact MeasurableSet.iUnion (fun c => (measurableSet_singleton c).prod (hU c))
  simp only [tube,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  have hx : Measurable (fun p : X×X => f t p.1) := (hf t).comp measurable_fst
  have hz : Measurable (fun p : X×X => f t p.2) := (hf t).comp measurable_snd
  have hc := hq.comp hx
  exact (hu.preimage (hc.prodMk hz)).inter
    (measurableSet_le (((measurable_evaluate φ hφ).comp (hc.prodMk hz)).sub
      ((measurable_evaluate φ hφ).comp (hc.prodMk hx))).norm measurable_const)
end SmoothObstruction.SelectedTube

namespace SmoothObstruction.MeasurableSwitch
open Set MeasureTheory
variable {X C E : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_relation (F P : X → X → E)
    (hF : Measurable (Function.uncurry F)) (hP : Measurable (Function.uncurry P))
    (TF TB : X → X → Prop) (hTF : MeasurableSet {p : X×X | TF p.1 p.2})
    (hTB : MeasurableSet {p : X×X | TB p.1 p.2}) :
    MeasurableSet {p : (X×X)×X | relation F P TF TB p.1 p.2} := by
  have h₁ : Measurable (fun p : (X×X)×X => (p.1.1,p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have h₂ : Measurable (fun p : (X×X)×X => (p.1.2,p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hx : Measurable (fun p : (X×X)×X => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hy : Measurable (fun p : (X×X)×X => p.1.2) :=
    measurable_snd.comp measurable_fst
  exact (measurableSet_eq_fun (hF.comp h₁) (hF.comp (hx.prodMk hx))).inter
    ((measurableSet_eq_fun (hP.comp h₂) (hP.comp (hy.prodMk hy))).inter
      ((hTF.preimage h₁).inter (hTB.preimage h₂)))

/-- The original retained carrier gives one globally measurable pair map.
There is no measurable moving-frame selection and no conditioning of a law.
Existence and uniqueness are supplied by the actual finite-tube solve. -/
theorem canonical_pair [StandardBorelSpace X] [Nonempty X]
    (G : Set (X×X)) (hG : MeasurableSet G)
    (F P : X → X → E) (hF : Measurable (Function.uncurry F))
    (hP : Measurable (Function.uncurry P))
    (TF TB : X → X → Prop) (hTF : MeasurableSet {p : X×X | TF p.1 p.2})
    (hTB : MeasurableSet {p : X×X | TB p.1 p.2})
    (hex : ∀ u∈G,∃! z,relation F P TF TB u z)
    (hex' : ∀ u∈G,∃! w,relation F P TF TB u.swap w) :
    ∃ Φ : X×X → X×X,Measurable Φ ∧
      (∀ u∈G,relation F P TF TB u (Φ u).1 ∧ relation F P TF TB u.swap (Φ u).2) ∧
      (∀ u∈G,∀ z,relation F P TF TB u z → z=(Φ u).1) ∧
      (∀ u∈G,∀ w,relation F P TF TB u.swap w → w=(Φ u).2) := by
  have hR := measurable_relation F P hF hP TF TB hTF hTB
  have hRG : MeasurableSet {p : (X×X)×X | p.1∈G ∧ relation F P TF TB p.1 p.2} :=
    (hG.preimage measurable_fst).inter hR
  have hRG' : MeasurableSet {p : (X×X)×X | p.1∈G ∧ relation F P TF TB p.1.swap p.2} :=
    (hG.preimage measurable_fst).inter (hR.preimage
      ((measurable_swap.comp measurable_fst).prodMk measurable_snd))
  obtain ⟨z,hz,hzr,hzu⟩ := CanonicalRelation.retained_solution G hG
    (relation F P TF TB) hRG hex
  obtain ⟨w,hw,hwr,hwu⟩ := CanonicalRelation.retained_solution G hG
    (fun u => relation F P TF TB u.swap) hRG' hex'
  exact ⟨fun u => (z u,w u),hz.prodMk hw,fun u hu => ⟨hzr u hu,hwr u hu⟩,hzu,hwu⟩
end SmoothObstruction.MeasurableSwitch

namespace SmoothObstruction.EndpointObservation
open Set MeasureTheory
variable {X C B E : Type*} [MeasurableSpace X]
  [Fintype C] [Fintype B] [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace B] [MeasurableSingletonClass B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_observation (c : X → C) (hc : Measurable c)
    (b : X → B) (hb : Measurable b) (f : X → X) (hf : Measurable f)
    (φ : B → X → E) (hφ : ∀ j,Measurable (φ j)) (P : C → B → E →L[ℝ] E) :
    Measurable (Function.uncurry (observation c b f φ P)) := by
  have hh : Measurable (fun u : (C×B)×X => P u.1.1 u.1.2 (φ u.1.2 (f u.2))) := by
    apply measurable_from_prod_countable_right
    intro ij
    exact (P ij.1 ij.2).continuous.measurable.comp ((hφ ij.2).comp hf)
  exact hh.comp (((hc.comp measurable_fst).prodMk
    (hb.comp (hf.comp measurable_fst))).prodMk measurable_snd)

end SmoothObstruction.EndpointObservation

namespace SmoothObstruction.ManifoldCoordinates
open Set MeasureTheory
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]

lemma borelChart_eq (a z : M) (hz : z∈(chartAt H a).source) :
    borelChart I a z=(extChartAt I a) z := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hz

variable [MeasurableSpace M] [BorelSpace M]

lemma measurable_borelChart (a : M) : Measurable (borelChart I a) := by
  classical
  apply ContinuousOn.measurable_piecewise _ continuousOn_const (chartAt H a).open_source.measurableSet
  simpa only [extChartAt_source] using continuousOn_extChartAt (I:=I) a

variable {ι C : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι) (n : ℕ)

lemma measurable_originalTube (hc : Measurable c)
    (hsource : ∀ z,z∈(chartAt H (a (c z))).source) (δ : ℝ) :
    MeasurableSet {p : M×M | originalTube I S a c (n:=n) δ p.1 p.2} := by
  have he : {p : M×M | originalTube I S a c (n:=n) δ p.1 p.2}=
      {p | SelectedTube.tube c (fun j => (chartAt H (a j)).source)
        (fun j => borelChart I (a j)) (fun t => S^[t]) n δ p.1 p.2} := by
    ext p
    constructor <;> intro hp t <;> obtain ⟨hs,ht⟩ := hp t
    · exact ⟨hs,by simpa only [borelChart_eq I _ _ hs,
        borelChart_eq I _ _ (hsource _)] using ht⟩
    · exact ⟨hs,by simpa only [borelChart_eq I _ _ hs,
        borelChart_eq I _ _ (hsource _)] using ht⟩
  rw [he]
  exact SelectedTube.measurable_tube c hc (fun j => (chartAt H (a j)).source)
    (fun j => (chartAt H (a j)).open_source.measurableSet)
    (fun j => borelChart I (a j)) (fun j => measurable_borelChart I (a j))
    (fun t => S^[t]) (fun t => S.continuous.measurable.iterate t) n δ

lemma measurable_originalObservation (hc : Measurable c) (P : M → C) (hP : Measurable P)
    (W : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    Measurable (Function.uncurry (originalObservation I S a c n P W)) := by
  exact EndpointObservation.measurable_observation P hP (fun x => (P x,c x))
    (hP.prodMk hc) (S^[n]) (S.continuous.measurable.iterate n)
    (fun j : C×ι => borelChart I (a j.2)) (fun j => measurable_borelChart I (a j.2))
    (fun q j => (W (q,j.1)).starProjection)

omit [MeasurableSpace M] [BorelSpace M]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

lemma originalObservation_eq_iff (P : M → C)
    (W : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x z : M)
    (hx : S^[n] x∈(chartAt H (a (c (S^[n] x)))).source)
    (hz : S^[n] z∈(chartAt H (a (c (S^[n] x)))).source) :
    originalObservation I S a c n P W x z=originalObservation I S a c n P W x x ↔
      originalEndpoint I S a c (n:=n) (W (P x,P (S^[n] x))) x z := by
  simp only [originalObservation,originalEndpoint,borelChart_eq I _ _ hx,borelChart_eq I _ _ hz]

lemma originalTube_mono {δ ε : ℝ} {x z : M} (h : δ≤ε)
    (hx : originalTube I S a c (n:=n) δ x z) :
    originalTube I S a c (n:=n) ε x z := fun t => ⟨(hx t).1,(hx t).2.trans h⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
open FiniteGreen ShortBin

/-- A measurable, witness-independent ORIGINAL pair switch. Its Borel relation
uses zero-extended charts, but all asserted equations and tube estimates are in
the original atlas. The retained set has not been normalized or repartitioned. -/
theorem canonical_original_switch_complete (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r₀ C₀ : ℝ,0 < r₀ ∧ 1≤C₀ ∧
      ∀ (C J : Type*) [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
        [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
        (c : M → ι) (P : M → C) (L : M → J) (G R : Set M)
        (n : ℕ) (B R₀ ε g α r δ : ℝ) (γ : C → ℝ)
        (A : ∀ x:G,BilateralGauge I S a c n B R₀ x)
        (T : G → Finset (Fin d)) (ref : G → G)
        (Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
        Measurable c → Measurable P → Measurable L → MeasurableSet R → R⊆G →
        (∀ v,v∈K (c v)) →
        (∀ x y,L x=L y → P x=P y) →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈R,I.IsInteriorPoint x) →
        (∀ x:G,P (ref x)=P x) →
        (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x y:G,P x=P y → ref x=ref y) →
        (∀ x:G,
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))ᶜ).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)ᶜ).starProjection‖≤ε ∧
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)).starProjection‖≤ε) →
        (∀ x:G,
          Module.finrank ℝ ((A x).forwardSpace I S a c n (T x))=
            Module.finrank ℝ (Wf (P x,P (S^[n] x))) ∧
          Module.finrank ℝ ((A x).backwardSpace I S a c n (T x)ᶜ)=
            Module.finrank ℝ (Wb (P x,P (S.symm^[n] x))) ∧
          ‖((A x).forwardSpace I S a c n (T x)).starProjection-
            (Wf (P x,P (S^[n] x))).starProjection‖≤1/2 ∧
          ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2) →
        0≤ε → ε≤1/2 → Real.exp (2*B)*(2*ε)≤1/2 →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (2*Real.exp (2*B))*(2*(2*Real.exp (2*B)^2*Real.exp (-2*g*n)))≤1/2 →
        (∀ x:G,|γ (P x)|+|g|≤α) → 0 ≤ r → 0<δ → δ ≤ r₀ →
        (∀ x∈R,∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) δ⊆interior (range I)) →
        (∀ x∈R,∀ y∈R,L x=L y →
          ‖(extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x‖≤C₀*r) →
        bvpInverseBound B α n*C₀*δ≤1/4 → bvpInverseBound B α n*C₀*r≤δ/4 →
        ∃ Φ : M×M → M×M,Measurable Φ ∧
          (∀ x y:G,x.val∈R → y.val∈R → L x=L y →
            let z := (Φ (x.val,y.val)).1
            let w := (Φ (x.val,y.val)).2
            originalTube I S a c (n:=n) (δ/2) x z ∧
            originalTube I S.symm a c (n:=n) (δ/2) y z ∧
            originalTube I S a c (n:=n) (δ/2) y w ∧
            originalTube I S.symm a c (n:=n) (δ/2) x w ∧
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z ∧
            originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z ∧
            originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w ∧
            originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w ∧
            originalTube I S a c (n:=n) (2*C₀*bvpInverseBound B α n*r) x z ∧
            originalTube I S.symm a c (n:=n) (2*C₀*bvpInverseBound B α n*r) y z ∧
            originalTube I S a c (n:=n) (2*C₀*bvpInverseBound B α n*r) y w ∧
            originalTube I S.symm a c (n:=n) (2*C₀*bvpInverseBound B α n*r) x w ∧
            ‖(extChartAt I (a (c x))) z-(extChartAt I (a (c x))) x-
              (((A (ref x)).forward I S a c).splitting (T (ref x))ᶜ).slow 0
                ((extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x)‖≤
                4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C₀*r)+
                  bvpInverseBound B α n*C₀*(2*C₀*bvpInverseBound B α n*r)^2 ∧
            ‖(extChartAt I (a (c y))) w-(extChartAt I (a (c y))) y-
              (((A (ref y)).forward I S a c).splitting (T (ref y))ᶜ).slow 0
                ((extChartAt I (a (c x))) x-(extChartAt I (a (c y))) y)‖≤
                4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C₀*r)+
                  bvpInverseBound B α n*C₀*(2*C₀*bvpInverseBound B α n*r)^2) ∧
          (∀ x∈R,∀ z,
            originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ x z →
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
            originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x z → z=x) ∧
          ∀ x∈R,∀ y∈R,L x=L y → ∀ z,
            originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ y z →
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
            originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z →
              z=(Φ (x,y)).1 := by
  obtain ⟨r₀,C₀,hr₀,hC₀,hjoin⟩ := original_gauged_join I hclosed S a K hK hKU
  refine ⟨r₀,C₀,hr₀,hC₀,?_⟩
  intro C J _ _ _ _ _ _ c P L G R n B R₀ ε g α r δ γ A T ref Wf Wb
    hc hP hL hR hRG hcover hLP hPc hint href hcard hrefeq hstart hend hε hεhalf
    hsmall hslow hfast hgap hα hr hδ hδr hsafe hnear hcontract hdata
  let F := originalObservation I S a c n P Wf
  let V := originalObservation I S.symm a c n P Wb
  let TF := originalTube I S a c (n:=n) δ
  let TB := originalTube I S.symm a c (n:=n) δ
  let Gpair : Set (M×M) := {u | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
  have hGpair : MeasurableSet Gpair :=
    (hR.preimage measurable_fst).inter ((hR.preimage measurable_snd).inter
      (measurableSet_eq_fun (hL.comp measurable_fst) (hL.comp measurable_snd)))
  have hsrc (x : M) : x∈(chartAt H (a (c x))).source := hKU _ (hcover x)
  have hspec (x y : G) (hx : x.val∈R) (hy : y.val∈R) (hxy : L x=L y) := by
    have hp := hLP x y hxy
    have hcst :
        ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
          ((A y).forwardSpace I S a c 0 (T y)).starProjection‖≤ε := by
      rw [hrefeq x y hp]
      exact (hstart y).2
    exact hjoin c n B R₀ ε (γ (P x)) g α r δ (ref x) x y
      (A (ref x)) (A x) (A y) (T (ref x)) (T x) (T y)
      (Wf (P x,P (S^[n] x))) (Wb (P y,P (S.symm^[n] y))) hcover (hPc x y hp)
      (hint x hx) (hint y hy) (hend x).1 (hend y).2.1 (hend x).2.2.1 (hend y).2.2.2
      hε hεhalf (hcard _ _ (href x)) (hcard _ _ ((href x).trans hp)) (hstart x).1 hcst hsmall
      (hslow x) (hfast x) (by simpa only [hp] using hslow y) (by simpa only [hp] using hfast y)
      hgap (hα x) hr hδ hδr (fun t => (hsafe x hx t).1) (fun t => (hsafe y hy t).2)
      (hnear x hx y hy hxy) hcontract hdata
  have hrel (x y : M) (z : M) :
      MeasurableSwitch.relation F V TF TB (x,y) z ↔
        originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z ∧
        originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z ∧
        TF x z ∧ TB y z := by
    constructor
    · rintro ⟨hf,hb,htf,htb⟩
      exact ⟨(originalObservation_eq_iff I S a c n P Wf x z (hsrc _) (htf ⟨n,by omega⟩).1).mp hf,
        (originalObservation_eq_iff I S.symm a c n P Wb y z (hsrc _) (htb ⟨n,by omega⟩).1).mp hb,htf,htb⟩
    · rintro ⟨hf,hb,htf,htb⟩
      exact ⟨(originalObservation_eq_iff I S a c n P Wf x z (hsrc _) (htf ⟨n,by omega⟩).1).mpr hf,
        (originalObservation_eq_iff I S.symm a c n P Wb y z (hsrc _) (htb ⟨n,by omega⟩).1).mpr hb,htf,htb⟩
  have hex (u : M×M) (hu : u∈Gpair) : ∃! z,MeasurableSwitch.relation F V TF TB u z := by
    let x : G := ⟨u.1,hRG hu.1⟩
    let y : G := ⟨u.2,hRG hu.2.1⟩
    obtain ⟨z,hzf,hzb,hze,hze',hsharp,hsharp',hideal,hunique⟩ := hspec x y hu.1 hu.2.1 hu.2.2
    refine ⟨z,(hrel _ _ _).mpr ⟨hze,hze',?_,?_⟩,?_⟩
    · exact originalTube_mono I S a c n (by linarith) hzf
    · exact originalTube_mono I S.symm a c n (by linarith) hzb
    · intro z' hz'
      obtain ⟨hf,hb,htf,htb⟩ := (hrel _ _ _).mp hz'
      exact hunique z' htf htb hf hb
  have hswap (u : M×M) (hu : u∈Gpair) : u.swap∈Gpair := ⟨hu.2.1,hu.1,hu.2.2.symm⟩
  obtain ⟨Φ,hΦ,hΦr,hΦu,hΦu'⟩ := MeasurableSwitch.canonical_pair Gpair hGpair F V
    (measurable_originalObservation I S a c n hc P hP Wf)
    (measurable_originalObservation I S.symm a c n hc P hP Wb) TF TB
    (measurable_originalTube I S a c n hc hsrc δ)
    (measurable_originalTube I S.symm a c n hc hsrc δ) hex (fun u hu => hex u.swap (hswap u hu))
  refine ⟨Φ,hΦ,?_,?_,?_⟩
  · intro x y hx hy hxy
    obtain ⟨z,hzf,hzb,hze,hze',hsf,hsb,hideal,hunique⟩ := hspec x y hx hy hxy
    obtain ⟨w,hwf,hwb,hwe,hwe',htf,htb,hideal',_⟩ := hspec y x hy hx hxy.symm
    have hz : z=(Φ (x.val,y.val)).1 := hΦu _ ⟨hx,hy,hxy⟩ _ ((hrel _ _ _).mpr
      ⟨hze,hze',originalTube_mono I S a c n (by linarith) hzf,
        originalTube_mono I S.symm a c n (by linarith) hzb⟩)
    have hw : w=(Φ (x.val,y.val)).2 := hΦu' _ ⟨hx,hy,hxy⟩ _ ((hrel _ _ _).mpr
      ⟨hwe,hwe',originalTube_mono I S a c n (by linarith) hwf,
        originalTube_mono I S.symm a c n (by linarith) hwb⟩)
    dsimp only
    rw [←hz,←hw]
    exact ⟨hzf,hzb,hwf,hwb,hze,hze',hwe,hwe',hsf,hsb,htf,htb,hideal,hideal'⟩
  · intro x hx z htf htb hef heb
    obtain ⟨w,_,_,_,_,_,_,_,hunique⟩ := hspec (⟨x,hRG hx⟩ : G) ⟨x,hRG hx⟩ hx hx rfl
    have hselfF : originalTube I S a c (n:=n) δ x x := by
      intro t
      exact ⟨hsrc _,by simpa only [sub_self,norm_zero] using hδ.le⟩
    have hselfB : originalTube I S.symm a c (n:=n) δ x x := by
      intro t
      exact ⟨hsrc _,by simpa only [sub_self,norm_zero] using hδ.le⟩
    exact (hunique z htf htb hef heb).trans (hunique x hselfF hselfB rfl rfl).symm
  · intro x hx y hy hxy z htf htb hef heb
    exact hΦu _ ⟨hx,hy,hxy⟩ z ((hrel x y z).mpr ⟨hef,heb,htf,htb⟩)
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_DensityLocalization
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.ChartDomination
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma density_two {a b j : ℝ} (ha : 0≤a) (hb : 3/4*a≤b) (hj : 81/121≤j) :
    ENNReal.ofReal a≤2*(ENNReal.ofReal j*ENNReal.ofReal b) := by
  have hj0 : 0≤j := by linarith
  have hb0 : 0≤b := by linarith
  have hmul := mul_le_mul_of_nonneg_left hb hj0
  have hja := mul_nonneg (sub_nonneg.mpr hj) ha
  have hh : a≤2*(j*b) := by nlinarith
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,
    ENNReal.ofReal_mul hj0] using ENNReal.ofReal_le_ofReal hh

/-- A concrete relative local branch and the two numerical lower bounds give
unnormalized domination by TWO in the original carrier measure. No choice of
local derivative or branch has to be measurable. -/
theorem local_two (μ : Measure X) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (d : E → ℝ) (Q G : Set X) (hQ : μ Qᶜ=0) (hGQ : G⊆Q) (hG : MeasurableSet G)
    (e : X → E) (r : E → X) (he : Measurable e) (hr : Measurable r)
    (hleft : ∀ x∈Q,r (e x)=x) (hcoords : μ.map e=m.withDensity (fun u => ENNReal.ofReal (d u)))
    (f : X → X) (_ : Measurable f) (hfQ : MapsTo f G Q) (hinj : InjOn f G)
    (hlocal : ∀ u∈coordinateSet e r G,∃ g : E → E,
      HasFDerivAt g (fderiv ℝ g u) u ∧ (81/121:ℝ)≤|(fderiv ℝ g u).det| ∧
      g =ᶠ[𝓝[coordinateSet e r G] u] (e ∘ f ∘ r))
    (hd : ∀ u∈coordinateSet e r G,0≤d u ∧ (3/4:ℝ)*d u≤d (e (f (r u)))) :
    (μ.restrict G).map f≤(2 : ℝ≥0∞) • μ := by
  classical
  let s := coordinateSet e r G
  choose g hg hj heq using hlocal
  let J (u : E) : E →L[ℝ] E := if hu : u∈s then fderiv ℝ (g u hu) u else 0
  have hφ : InjOn (e ∘ f ∘ r) s := by
    intro u hu v hv huv
    have hfu := hfQ hu.1
    have hfv := hfQ hv.1
    have he' : f (r u)=f (r v) := by
      have hh := congrArg r huv
      change r (e (f (r u)))=r (e (f (r v))) at hh
      rwa [hleft _ hfu,hleft _ hfv] at hh
    exact hu.2.symm.trans ((congrArg e (hinj hu.1 hv.1 he')).trans hv.2)
  obtain ⟨F,hF,hFf,hdom⟩ := local_domination μ m (fun u => ENNReal.ofReal (d u))
    Q G hQ hGQ hG e r he hr hleft hcoords f hfQ (e ∘ f ∘ r) J
    (fun x hx => by simp only [Function.comp_apply,hleft x (hGQ hx)])
    (fun u hu => ⟨g u hu,by simpa only [J,s,dite_eq_left hu] using hg u hu,heq u hu⟩)
    hφ 2 (by norm_num) (fun u hu => by
      simpa only [J,s,dite_eq_left hu,Function.comp_apply] using
        density_two (hd u hu).1 (hd u hu).2 (hj u hu))
  have hFF : F=ᵐ[μ.restrict G] f := ae_restrict_of_forall_mem hG (fun _ hx => hFf hx)
  rwa [Measure.map_congr hFF] at hdom
end SmoothObstruction.ChartDomination

namespace SmoothObstruction.ChartDensity
open MeasureTheory Set
open scoped ENNReal Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Product coordinates carry exactly the product of the ORIGINAL cell
measures, with its unchanged chart density and no normalization. -/
theorem pair_cell_density (hclosed : IsClosed (range I)) (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : SmoothPositiveDensity I μ) (a : M) :
    ∃ f : E₀ → ℝ,ContDiffOn ℝ ∞ f (extChartAt I a).target ∧
      (∀ u∈(extChartAt I a).target,0<f u) ∧
      ∀ Q : Set M,MeasurableSet Q → Q⊆(extChartAt I a).source →
        let W := ChartDomination.coordinateSet (coordinates I a) (inverse I a) Q
        let dQ := W.indicator f
        ((μ.restrict Q).prod (μ.restrict Q)).map (Prod.map (coordinates I a) (coordinates I a))=
          volume.withDensity (fun u : E₀×E₀ => ENNReal.ofReal (dQ u.1*dQ u.2)) := by
  classical
  obtain ⟨f,hf,hpos,hm⟩ := cell_density I hclosed μ hμ a
  refine ⟨f,hf,hpos,fun Q hQ hQU => ?_⟩
  dsimp only
  let W := ChartDomination.coordinateSet (coordinates I a) (inverse I a) Q
  let eQ := W.indicator (fun u => ENNReal.ofReal (f u))
  obtain ⟨heQ,hmap⟩ := hm Q hQ hQU
  have hmap' : (μ.restrict Q).map (coordinates I a)=volume.withDensity eQ := hmap
  rw [←Measure.map_prod_map _ _ (measurable_coordinates I a) (measurable_coordinates I a),hmap',
    prod_withDensity heQ heQ]
  congr 1
  funext u
  have he (v : E₀) : eQ v=ENNReal.ofReal (W.indicator f v) := by
    by_cases hv : v∈W <;> simp [eQ,Set.indicator,hv]
  have hn : 0≤W.indicator f u.1 := by
    by_cases hu : u.1∈W
    · rw [Set.indicator_of_mem hu]
      have him := ChartDomination.coordinateSet_eq_image (coordinates I a) (inverse I a) Q
        (fun x hx => inverse_coordinates I a x (hQU hx))
      obtain ⟨x,hx,he⟩ := (him ▸ hu : u.1∈coordinates I a '' Q)
      rw [←he,coordinates_eq I a x (hQU hx)]
      exact (hpos _ ((extChartAt I a).map_source (hQU hx))).le
    · simp only [Set.indicator_of_notMem hu,le_refl]
  change eQ u.1*eQ u.2=ENNReal.ofReal (W.indicator f u.1*W.indicator f u.2)
  rw [he,he,ENNReal.ofReal_mul hn]
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.ChartDensity
open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The original-cell change of variables. The density is selected ONCE per
atlas chart, before cells or retained pairs. Local branches are only required
on the retained relative neighborhood, at every rank including zero. -/
theorem pair_cell_two (hclosed : IsClosed (range I)) (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : SmoothPositiveDensity I μ) (a : M) :
    ∃ f : E₀ → ℝ,ContDiffOn ℝ ∞ f (extChartAt I a).target ∧
      (∀ u∈(extChartAt I a).target,0<f u) ∧
      ∀ Q : Set M,MeasurableSet Q → Q⊆(extChartAt I a).source →
      ∀ G : Set (M×M),MeasurableSet G → G⊆Q×ˢQ →
      ∀ Φ : M×M → M×M,Measurable Φ → MapsTo Φ G (Q×ˢQ) → InjOn Φ G →
        let e := Prod.map (coordinates I a) (coordinates I a)
        let r := Prod.map (inverse I a) (inverse I a)
        (∀ u∈ChartDomination.coordinateSet e r G,∃ Ψ : E₀×E₀ → E₀×E₀,
          HasFDerivAt Ψ (fderiv ℝ Ψ u) u ∧ (81/121:ℝ)≤|(fderiv ℝ Ψ u).det| ∧
          Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e r G] u] (e ∘ Φ ∘ r)) →
        (∀ x∈G,(3/4:ℝ)*(f ((e x).1)*f ((e x).2))≤
          f ((e (Φ x)).1)*f ((e (Φ x)).2)) →
        (((μ.restrict Q).prod (μ.restrict Q)).restrict G).map Φ≤
          (2 : ℝ≥0∞) • (μ.restrict Q).prod (μ.restrict Q) := by
  classical
  obtain ⟨f,hf,hpos,hm⟩ := pair_cell_density I hclosed μ hμ a
  refine ⟨f,hf,hpos,?_⟩
  intro Q hQ hQU G hG hGQ Φ hΦ hout hinj e r hlocal hd
  let W := ChartDomination.coordinateSet (coordinates I a) (inverse I a) Q
  let dQ := W.indicator f
  have he : Measurable e := (measurable_coordinates I a).prodMap (measurable_coordinates I a)
  have hr : Measurable r := (measurable_inverse I hclosed a).prodMap (measurable_inverse I hclosed a)
  have hleft : ∀ x∈Q×ˢQ,r (e x)=x := by
    intro x hx
    exact Prod.ext (inverse_coordinates I a x.1 (hQU hx.1))
      (inverse_coordinates I a x.2 (hQU hx.2))
  have hfull : ((μ.restrict Q).prod (μ.restrict Q)) (Q×ˢQ)ᶜ=0 := by
    rw [Measure.prod_restrict,Measure.restrict_apply (hQ.prod hQ).compl,
      compl_inter_self,measure_empty]
  have hcoord (x : M×M) (hx : x∈Q×ˢQ) :
      dQ (e x).1=f (e x).1 ∧ dQ (e x).2=f (e x).2 := by
    change W.indicator f (coordinates I a x.1)=f (coordinates I a x.1) ∧
      W.indicator f (coordinates I a x.2)=f (coordinates I a x.2)
    constructor
    · apply Set.indicator_of_mem
      exact ⟨by simpa only [Prod.map_fst,inverse_coordinates I a x.1 (hQU hx.1)] using hx.1,
        by simp only [inverse_coordinates I a x.1 (hQU hx.1)]⟩
    · apply Set.indicator_of_mem
      exact ⟨by simpa only [Prod.map_snd,inverse_coordinates I a x.2 (hQU hx.2)] using hx.2,
        by simp only [inverse_coordinates I a x.2 (hQU hx.2)]⟩
  let : Measure.IsAddHaarMeasure (volume : Measure (E₀×E₀)) := by
    change Measure.IsAddHaarMeasure ((volume : Measure E₀).prod volume)
    infer_instance
  apply ChartDomination.local_two (E := E₀×E₀) ((μ.restrict Q).prod (μ.restrict Q)) volume
    (fun u : E₀×E₀ => dQ u.1*dQ u.2) (Q×ˢQ) G hfull hGQ hG e r he hr hleft
    (hm Q hQ hQU) Φ hΦ hout hinj hlocal
  intro u hu
  have hx := hGQ hu.1
  have hy := hout hu.1
  have hin := hcoord (r u) hx
  have hot := hcoord (Φ (r u)) hy
  have hin' : dQ u.1=f u.1 ∧ dQ u.2=f u.2 := by simpa only [hu.2] using hin
  rw [hin'.1,hin'.2,hot.1,hot.2]
  refine ⟨?_,?_⟩
  · have hu₁ : u.1∈(extChartAt I a).target := by
      rw [←hu.2]
      change coordinates I a (r u).1∈(extChartAt I a).target
      rw [coordinates_eq I a _ (hQU hx.1)]
      exact (extChartAt I a).map_source (hQU hx.1)
    have hu₂ : u.2∈(extChartAt I a).target := by
      rw [←hu.2]
      change coordinates I a (r u).2∈(extChartAt I a).target
      rw [coordinates_eq I a _ (hQU hx.2)]
      exact (extChartAt I a).map_source (hQU hx.2)
    exact mul_nonneg (hpos _ hu₁).le (hpos _ hu₂).le
  · simpa only [hu.2] using hd (r u) hu.1
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.DensityUniform
open Set Metric
variable {E : Type*} [PseudoMetricSpace E]

/-- Positive compact smooth-chart densities admit uniform relative, rather
than absolute, estimates. Only continuity is used, valid up to boundary. -/
theorem relative (K : Set E) (hK : IsCompact K) (f : E → ℝ)
    (hf : ContinuousOn f K) (hpos : ∀ x∈K,0<f x) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ x∈K,∀ y∈K,dist x y<δ → |f y-f x|≤ε*f x := by
  by_cases hem : K.Nonempty
  · obtain ⟨x₀,hx₀,hmin⟩ := hK.exists_isMinOn hem hf
    have hmc : 0<ε*f x₀ := mul_pos hε (hpos x₀ hx₀)
    obtain ⟨δ,hδ,huc⟩ := Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hf)
      (ε*f x₀) hmc
    refine ⟨δ,hδ,fun x hx y hy hxy => ?_⟩
    have hh := huc x hx y hy hxy
    have hle := mul_le_mul_of_nonneg_left (hmin hx) hε.le
    have hh' : |f y-f x|≤ε*f x₀ := by simpa only [Real.dist_eq,abs_sub_comm] using hh.le
    exact hh'.trans hle
  · refine ⟨1,zero_lt_one,fun x hx => ?_⟩
    exact (hem ⟨x,hx⟩).elim

/-- The density portion of the joint switch has a uniform three-quarter
lower bound once both matched point pairs are sufficiently close. -/
theorem pair_lower (K : Set E) (hK : IsCompact K) (f : E → ℝ)
    (hf : ContinuousOn f K) (hpos : ∀ x∈K,0<f x) :
    ∃ δ : ℝ,0<δ ∧ ∀ x∈K,∀ y∈K,∀ z∈K,∀ w∈K,
      dist x z<δ → dist y w<δ → (3/4:ℝ)*(f x*f y)≤f z*f w := by
  obtain ⟨δ,hδ,hrel⟩ := relative K hK f hf hpos (by norm_num : 0<(1/10:ℝ))
  refine ⟨δ,hδ,fun x hx y hy z hz w hw hxz hyw => ?_⟩
  have hx' : (9/10:ℝ)*f x≤f z := by
    have h := abs_le.mp (hrel x hx z hz hxz); linarith
  have hy' : (9/10:ℝ)*f y≤f w := by
    have h := abs_le.mp (hrel y hy w hw hyw); linarith
  have hp := mul_le_mul hx' hy' (mul_nonneg (by norm_num) (hpos y hy).le) (hpos z hz).le
  nlinarith [mul_pos (hpos x hx) (hpos y hy)]
end SmoothObstruction.DensityUniform

namespace SmoothObstruction.ChartDensity
open Set Metric MeasureTheory Filter Topology
open scoped ENNReal Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The authentic local coordinate germs yield domination of the ORIGINAL
cell-weighted experiment. Compact positive density is controlled before any
partition or retained set is chosen. Zero-weight cells require no exception,
and neither cells nor retained pairs are conditionally renormalized. -/
theorem original_law_two (hclosed : IsClosed (range I))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r : ℝ,0 < r ∧ ∀ {J : Type*} [Fintype J] [MeasurableSpace J]
      [MeasurableSingletonClass J] (L : M → J) (c : M → ι) (chart : J → ι),
      Measurable L → (∀ x,x∈K (c x)) → (∀ x,chart (L x)=c x) →
      (∀ x y,L x=L y → ‖coordinates I (a (c x)) x-coordinates I (a (c x)) y‖ < r) →
      ∀ (G : Set (M×M)) (Φ : M×M → M×M),MeasurableSet G → Measurable Φ →
      (∀ u∈G,L u.1=L u.2 ∧ L (Φ u).1=L u.1 ∧ L (Φ u).2=L u.2) →
      InjOn Φ G →
      (∀ (j : J),let Q := L ⁻¹' {j}
        let A := G∩(Q×ˢQ)
        let e := Prod.map (coordinates I (a (chart j))) (coordinates I (a (chart j)))
        let s := Prod.map (inverse I (a (chart j))) (inverse I (a (chart j)))
        ∀ u∈ChartDomination.coordinateSet e s A,∃ Ψ : E₀×E₀ → E₀×E₀,
          HasFDerivAt Ψ (fderiv ℝ Ψ u) u ∧ (81/121:ℝ)≤|(fderiv ℝ Ψ u).det| ∧
          Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s A] u] (e ∘ Φ ∘ s)) →
      ((PairLaw.law μ L).restrict G).map Φ≤(2 : ℝ≥0∞) • PairLaw.law μ L ∧
      ((PairLaw.law μ L).restrict G).map (fun u => (Φ u).1)≤(2 : ℝ≥0∞) • μ := by
  classical
  choose f hf hpos hcell using fun i => pair_cell_two I hclosed μ hμ (a i)
  let K' (i : ι) := (extChartAt I (a i)) '' K i
  have hsrc (i : ι) : K i⊆(extChartAt I (a i)).source := by
    simpa only [extChartAt_source] using hKU i
  have hKt (i : ι) : K' i⊆(extChartAt I (a i)).target :=
    image_subset_iff.mpr (fun _ hx => (extChartAt I (a i)).map_source (hsrc i hx))
  have hcompact (i : ι) : IsCompact (K' i) :=
    (hK i).image_of_continuousOn ((continuousOn_extChartAt (a i)).mono (hsrc i))
  choose r hr hd using fun i => DensityUniform.pair_lower (K' i) (hcompact i) (f i)
    ((hf i).continuousOn.mono (hKt i)) (fun x hx => hpos i x (hKt i hx))
  obtain ⟨r₀,hr₀,hr₀r⟩ := CarriedCharts.finite_positive_lower r hr
  refine ⟨r₀,hr₀,?_⟩
  intro J _ _ _ L c chart hL hc hchart hdiam G Φ hG hΦ hkeep hinj hgerm
  have hdom : ((PairLaw.law μ L).restrict G).map Φ≤(2 : ℝ≥0∞) • PairLaw.law μ L := by
    apply PairLaw.law_domination μ L G Φ hΦ 2
    intro j
    let Q := L ⁻¹' {j}
    let A := G∩(Q×ˢQ)
    have hQ : MeasurableSet Q := hL (measurableSet_singleton _)
    have hA : MeasurableSet A := hG.inter (hQ.prod hQ)
    have hchartQ {x : M} (hx : x∈Q) : c x=chart j := by
      rw [←hchart x]; exact congrArg chart hx
    have hQK : Q⊆K (chart j) := by
      intro x hx; rw [←hchartQ hx]; exact hc x
    have hQU : Q⊆(extChartAt I (a (chart j))).source := hQK.trans (hsrc _)
    have hout : MapsTo Φ A (Q×ˢQ) := by
      rintro u ⟨hu,hux,huy⟩
      have hh := hkeep u hu
      exact ⟨hh.2.1.trans hux,hh.2.2.trans huy⟩
    have hdensity : ∀ x∈A,(3/4:ℝ)*(f (chart j) (coordinates I (a (chart j)) x.1)*
        f (chart j) (coordinates I (a (chart j)) x.2))≤
        f (chart j) (coordinates I (a (chart j)) (Φ x).1)*
          f (chart j) (coordinates I (a (chart j)) (Φ x).2) := by
      intro x hx
      have ho := hout hx
      have mem {y : M} (hy : y∈Q) : coordinates I (a (chart j)) y∈K' (chart j) := by
        rw [coordinates_eq I _ _ (hQU hy)]
        exact mem_image_of_mem _ (hQK hy)
      apply hd (chart j) _ (mem hx.2.1) _ (mem hx.2.2) _ (mem ho.1) _ (mem ho.2)
      · have he := hdiam x.1 (Φ x).1 (hkeep x hx.1).2.1.symm
        rw [hchartQ hx.2.1] at he
        apply lt_of_lt_of_le _ (hr₀r _)
        simpa only [dist_eq_norm] using he
      · have he := hdiam x.2 (Φ x).2 (hkeep x hx.1).2.2.symm
        rw [hchartQ hx.2.2] at he
        apply lt_of_lt_of_le _ (hr₀r _)
        simpa only [dist_eq_norm] using he
    have hh := hcell (chart j) Q hQ hQU A hA (fun _ hx => hx.2) Φ hΦ hout
      (hinj.mono inter_subset_left) (hgerm j) hdensity
    have he : (((μ.restrict Q).prod (μ.restrict Q)).restrict A)=
        (((μ.restrict Q).prod (μ.restrict Q)).restrict G) := by
      rw [Measure.prod_restrict,Measure.restrict_restrict hA,Measure.restrict_restrict hG]
      congr 1
      exact inter_eq_self_of_subset_left inter_subset_right
    rw [he] at hh
    exact hh
  exact ⟨hdom,PairLaw.first_output_domination μ L hL G Φ hΦ 2 hdom⟩
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.ChartDensity
open Set Metric MeasureTheory Filter Topology
open scoped ENNReal Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Physical retained-pair germs in their old starting charts suffice for the
original cell-weighted, unnormalized domination. The germ is only shrunk when
passing to the original cell; no new partition labels are introduced. -/
theorem physical_original_law_two (hclosed : IsClosed (range I))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r : ℝ,0 < r ∧ ∀ {J : Type*} [Fintype J] [MeasurableSpace J]
      [MeasurableSingletonClass J] (L : M → J) (c : M → ι) (chart : J → ι),
      Measurable L → (∀ x,x∈K (c x)) → (∀ x,chart (L x)=c x) →
      (∀ x y,L x=L y → ‖coordinates I (a (c x)) x-coordinates I (a (c x)) y‖ < r) →
      ∀ (G : Set (M×M)) (Φ : M×M → M×M),MeasurableSet G → Measurable Φ →
      (∀ u∈G,L u.1=L u.2 ∧ L (Φ u).1=L u.1 ∧ L (Φ u).2=L u.2) →
      InjOn Φ G →
      (∀ x y,(x,y)∈G →
        let e := Prod.map (coordinates I (a (c x))) (coordinates I (a (c x)))
        let s := Prod.map (inverse I (a (c x))) (inverse I (a (c x)))
        let u := ((extChartAt I (a (c x))) x,(extChartAt I (a (c x))) y)
        ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ u) u ∧
          (81/121:ℝ)≤|(fderiv ℝ Ψ u).det| ∧
          Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] u] (e ∘ Φ ∘ s)) →
      ((PairLaw.law μ L).restrict G).map Φ≤(2 : ℝ≥0∞) • PairLaw.law μ L ∧
      ((PairLaw.law μ L).restrict G).map (fun u => (Φ u).1)≤(2 : ℝ≥0∞) • μ := by
  obtain ⟨r,hr,hh⟩ := original_law_two I hclosed μ hμ a K hK hKU
  refine ⟨r,hr,?_⟩
  intro J _ _ _ L c chart hL hc hchart hdiam G Φ hG hΦ hkeep hinj hgerm
  apply hh L c chart hL hc hchart hdiam G Φ hG hΦ hkeep hinj
  intro j Q A e s u hu
  let z := s u
  have hz : z∈G := hu.1.1
  have hzQ : z.1∈Q ∧ z.2∈Q := hu.1.2
  have hcz : c z.1=chart j := by rw [←hchart z.1]; exact congrArg chart hzQ.1
  have hcz' : c z.2=chart j := by rw [←hchart z.2]; exact congrArg chart hzQ.2
  have hsrc₁ : z.1∈(extChartAt I (a (chart j))).source := by
    rw [←hcz,extChartAt_source]; exact hKU _ (hc z.1)
  have hsrc₂ : z.2∈(extChartAt I (a (chart j))).source := by
    rw [←hcz',extChartAt_source]; exact hKU _ (hc z.2)
  have he : ((extChartAt I (a (chart j))) z.1,(extChartAt I (a (chart j))) z.2)=u := by
    have h := hu.2
    change (coordinates I (a (chart j)) z.1,coordinates I (a (chart j)) z.2)=u at h
    rwa [coordinates_eq I _ _ hsrc₁,coordinates_eq I _ _ hsrc₂] at h
  obtain ⟨Ψ,hΨ,hd,hag⟩ := hgerm z.1 z.2 hz
  rw [hcz,he] at hΨ hd hag
  refine ⟨Ψ,hΨ,hd,?_⟩
  apply hag.filter_mono
  apply nhdsWithin_mono
  intro v hv
  exact ⟨hv.1.1,hv.2⟩
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    {ι C : Type*}
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The original coarse partition is locally constant at every retained
one-point input. This uses the original grid margin and fixed chart core only. -/
lemma original_coarse_germ (a : ι → M) (c : M → ι) (P : M → C)
    (x : M) (hx : x∈(chartAt H (a (c x))).source) (s δ : ℝ) (hs : 0 < s) (hδ : 0<δ)
    (hcore : ∀ y,dist y x ≤ s → c y=c x)
    (hrec : ∀ y,c y=c x →
      ‖(extChartAt I (a (c x))) y-(extChartAt I (a (c x))) x‖≤δ/4 → P y=P x) :
    ∀ᶠ y in 𝓝 x,P y=P x := by
  have hcont : ContinuousAt (fun y => ‖(extChartAt I (a (c x))) y-(extChartAt I (a (c x))) x‖) x :=
    (((continuousOn_extChartAt (a (c x))).continuousAt
      (by simpa only [extChartAt_source] using (chartAt H (a (c x))).open_source.mem_nhds hx)).sub continuousAt_const).norm
  have hz : ‖(extChartAt I (a (c x))) x-(extChartAt I (a (c x))) x‖<δ/4 := by
    simpa using (show (0:ℝ)<δ/4 by positivity)
  filter_upwards [Metric.ball_mem_nhds x hs,hcont.eventually (gt_mem_nhds hz),
    (chartAt H (a (c x))).open_source.mem_nhds hx] with y hy hdist hys
  apply hrec y (hcore y (Metric.mem_ball.mp hy).le)
  exact hdist.le

/-- Only the six original start/end labels are fixed near an input pair.
No intermediate orbit-code refinement is used. -/
lemma six_original_labels (S : Diffeomorph I I M M ∞) (P : M → C)
    (a₀ x y : M) (n : ℕ)
    (hx : x∈(extChartAt I a₀).source) (hy : y∈(extChartAt I a₀).source)
    (hiX : (extChartAt I a₀) x∈interior (range I))
    (hiY : (extChartAt I a₀) y∈interior (range I))
    (hx₀ : ∀ᶠ z in 𝓝 x,P z=P x) (hy₀ : ∀ᶠ z in 𝓝 y,P z=P y)
    (hxF : ∀ᶠ z in 𝓝 (S^[n] x),P z=P (S^[n] x))
    (hyF : ∀ᶠ z in 𝓝 (S^[n] y),P z=P (S^[n] y))
    (hxB : ∀ᶠ z in 𝓝 (S.symm^[n] x),P z=P (S.symm^[n] x))
    (hyB : ∀ᶠ z in 𝓝 (S.symm^[n] y),P z=P (S.symm^[n] y)) :
    ∀ᶠ t in 𝓝 ((extChartAt I a₀ x),(extChartAt I a₀ y)),
      P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
      P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
      P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
      P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
      P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y) := by
  have hix := inverse_continuousAt_interior I a₀ _ ((extChartAt I a₀).map_source hx) hiX
  have hiy := inverse_continuousAt_interior I a₀ _ ((extChartAt I a₀).map_source hy) hiY
  have hcx : Tendsto (fun t : E₀×E₀ => (extChartAt I a₀).symm t.1)
      (𝓝 ((extChartAt I a₀ x),(extChartAt I a₀ y))) (𝓝 x) := by
    have ht := hix.tendsto.comp (continuous_fst.tendsto ((extChartAt I a₀ x),(extChartAt I a₀ y)))
    simpa only [Function.comp_def,(extChartAt I a₀).left_inv hx] using ht
  have hcy : Tendsto (fun t : E₀×E₀ => (extChartAt I a₀).symm t.2)
      (𝓝 ((extChartAt I a₀ x),(extChartAt I a₀ y))) (𝓝 y) := by
    have ht := hiy.tendsto.comp (continuous_snd.tendsto ((extChartAt I a₀ x),(extChartAt I a₀ y)))
    simpa only [Function.comp_def,(extChartAt I a₀).left_inv hy] using ht
  have hF := S.continuous.iterate n
  have hB := S.symm.continuous.iterate n
  filter_upwards [hcx.eventually hx₀,hcy.eventually hy₀,
    ((hF.tendsto x).comp hcx).eventually hxF,((hF.tendsto y).comp hcy).eventually hyF,
    ((hB.tendsto x).comp hcx).eventually hxB,((hB.tendsto y).comp hcy).eventually hyB] with t h₀ h₁ h₂ h₃ h₄ h₅
  exact ⟨h₀,h₁,h₂,h₃,h₄,h₅⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric MeasureTheory Filter Topology EndpointFrame FiniteGreen ShortBin
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The genuine global pair switch at one scale. Every constant precedes the
partition alphabets and ranks. Inputs are actual bilateral gauges, original
grid margins, and explicit scalar budgets; the conclusion is unnormalized
ORIGINAL-law domination, not an assumed Jacobian or switch certificate. -/
theorem genuine_pair_switch_oai (hclosed : IsClosed (range I))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (s Dg : ℝ) (hs : 0 < s) (hDg : 0≤Dg) :
    ∃ r₀ C₀ σ r₁ C₁ rg Cg β K₀F CreF C₁F K₀B CreB C₁B rμ : ℝ,
      0 < r₀ ∧ 1≤C₀ ∧ 0<σ ∧ 0 < r₁ ∧ 1≤C₁ ∧ 0 < rg ∧ 1≤Cg ∧ 0<β ∧
      1≤K₀F ∧ 0≤CreF ∧ 0≤C₁F ∧ 1≤K₀B ∧ 0≤CreB ∧ 0≤C₁B ∧ 0 < rμ ∧
      ∀ {C J : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
        [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
        (c : M → ι) (P : M → C) (L : M → J) (π : J → C) (chart : C → ι)
        (G R V Wc Wp : Set M) (n : ℕ) (b R₀ Cext ε g α r δc δp H₀ : ℝ)
        (γ : C → ℝ),
        let B := Dg*(b*n)
        let δ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        let ρ := 2*C₀*bvpInverseBound B α n*r
        let E := 4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C₀*r)+
          bvpInverseBound B α n*C₀*ρ^2
        ∀ (A : ∀ x:G,BilateralGauge I S a c n B R₀ x) (T : G → Finset (Fin d)) (ref : G → G)
          (Wf Wb : C×C → Submodule ℝ E₀),
        Measurable c → Measurable P → Measurable L → MeasurableSet R → (hRG : R⊆G) →
        (∀ x,x∈K (c x)) → (∀ x,π (L x)=P x) → (∀ x,chart (P x)=c x) →
        (∀ x∈R,I.IsInteriorPoint x) →
        (∀ x:G,P (ref x)=P x) → (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x y:G,P x=P y → ref x=ref y) →
        (∀ x:G,
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))ᶜ).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)ᶜ).starProjection‖≤ε ∧
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)).starProjection‖≤ε) →
        (∀ x:G,
          Module.finrank ℝ (Wf (P x,P (S^[n] x)))=(T x).card ∧
          Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-(T x).card ∧
          ‖((A x).forwardSpace I S a c n (T x)).starProjection-
            (Wf (P x,P (S^[n] x))).starProjection‖≤1/2 ∧
          ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2) →
        0≤b → 1≤b*n → 0≤R₀ → 0≤Cext → 0≤ε → ε≤1/2 →
        Real.exp (2*B)*(2*ε)≤1/2 → 0≤g →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (2*Real.exp (2*B))*(2*(2*Real.exp (2*B)^2*Real.exp (-2*g*n)))≤1/2 →
        (∀ x:G,|γ (P x)|+|g|≤α) → 0 ≤ r → δ ≤ r₀ → δ ≤ rg →
        0≤ρ → ρ≤δ → ρ≤σ → ρ≤δc/4 → ρ ≤ r₁ → C₁*ρ≤δ → Cg*ρ<δ →
        K₀F*δ≤1 → K₀B*δ≤1 → 0<δc → 0≤H₀ → H₀*E≤δp/4 →
        (∀ p≤d,∀ F : E₀ →L[ℝ] E₀,‖ExteriorStability.exterior p F‖≤Cext*(max 1 ‖F‖)^p) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀F CreF C₁F b n g ε β) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀B CreB C₁B b n g ε β) →
        (∀ x∈R,∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) δ⊆interior (range I)) →
        (∀ x∈R,∀ y∈R,L x=L y →
          ‖(extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x‖≤C₀*r) →
        bvpInverseBound B α n*C₀*δ≤1/4 → bvpInverseBound B α n*C₀*r≤δ/4 →
        (∀ x y,L x=L y → ‖ChartDensity.coordinates I (a (c x)) x-ChartDensity.coordinates I (a (c x)) y‖ < rμ) →
        (∀ x∈V,∀ z,dist z x ≤ s → c z=c x) →
        (∀ x z,x∉Wc → c z=c x →
          ‖ChartDensity.coordinates I (a (c x)) z-ChartDensity.coordinates I (a (c x)) x‖≤δc/4 → P z=P x) →
        (∀ x y z,(hx : x∈R) → L x=L y → x∉Wp → y∉Wp → P z=P x →
          H₀*‖ChartDensity.coordinates I (a (c x)) z-(ChartDensity.coordinates I (a (c x)) x+
            (((A (ref ⟨x,hRG hx⟩)).forward I S a c).splitting (T (ref ⟨x,hRG hx⟩))ᶜ).slow 0
              (ChartDensity.coordinates I (a (c x)) y-ChartDensity.coordinates I (a (c x)) x))‖≤δp/4 → L z=L x) →
        (∀ x∈R,x∈V ∧ x∉Wc ∧ x∉Wp ∧
          S^[n] x∈V ∧ S^[n] x∉Wc ∧ S.symm^[n] x∈V ∧ S.symm^[n] x∉Wc) →
        let Gp := {u : M×M | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
        ∃ Φ : M×M → M×M,Measurable Φ ∧ MeasurableSet Gp ∧ InjOn Φ Gp ∧
          ((PairLaw.law μ L).restrict Gp).map Φ≤(2 : ℝ≥0∞) • PairLaw.law μ L ∧
          ((PairLaw.law μ L).restrict Gp).map (fun u => (Φ u).1)≤(2 : ℝ≥0∞) • μ ∧
          ∀ u∈Gp,originalTube I S a c (n:=n) ρ u.1 (Φ u).1 ∧
            originalTube I S.symm a c (n:=n) ρ u.2 (Φ u).1 := by
  classical
  obtain ⟨r₀,C₀,hr₀,hC₀,hcanonical⟩ := canonical_original_switch_complete I hclosed S a K hK hKU
  obtain ⟨σ,r₁,C₁,hσ,hr₁,hC₁,hrecover⟩ := recovered_original_pair I hclosed a K hK hKU hs
  obtain ⟨rg,Cg,β,K₀F,CreF,C₁F,K₀B,CreB,C₁B,hrg,hCg,hβ,hKF,hCrF,hCF,hKB,hCrB,hCB,hgerm⟩ :=
    gauge_original_germ_sharp I hclosed S a K hK hKU Dg hDg
  obtain ⟨rμ,hrμ,hlaw⟩ := ChartDensity.physical_original_law_two I hclosed μ hμ a K hK hKU
  refine ⟨r₀,C₀,σ,r₁,C₁,rg,Cg,β,K₀F,CreF,C₁F,K₀B,CreB,C₁B,rμ,
    hr₀,hC₀,hσ,hr₁,hC₁,hrg,hCg,hβ,hKF,hCrF,hCF,hKB,hCrB,hCB,hrμ,?_⟩
  intro C J _ _ _ _ _ _ c P L π chart G R V Wc Wp n b R₀ Cext ε g α r δc δp H₀ γ B δ ρ E
    A T ref Wf Wb hc hP hL hR hRG hcover hπ hchart hint href hcard hreff hstart hend
    hb hbn hR₀ hCext hε hεhalf hsmall hg hslow hfast hgap hα hr hδr hδrg
    hρ hρδ hρσ hρc hρr₁ hρC hρCg hδF hδB hδc hH₀ hE hpoly hbudF hbudB
    hsafe hnear hcontract hdata hdiam hcore hcoarse hprod hret Gp
  have hδ : 0<δ := Real.exp_pos _
  have hLP (x y : M) (h : L x=L y) : P x=P y := by rw [←hπ x,←hπ y,h]
  have hPc (x y : M) (h : P x=P y) : c x=c y := by rw [←hchart x,←hchart y,h]
  have hsrc (x : M) : x∈(extChartAt I (a (c x))).source := by
    rw [extChartAt_source]; exact hKU _ (hcover x)
  have hend' (x : G) :
      Module.finrank ℝ ((A x).forwardSpace I S a c n (T x))=Module.finrank ℝ (Wf (P x,P (S^[n] x))) ∧
      Module.finrank ℝ ((A x).backwardSpace I S a c n (T x)ᶜ)=Module.finrank ℝ (Wb (P x,P (S.symm^[n] x))) ∧
      ‖((A x).forwardSpace I S a c n (T x)).starProjection-(Wf (P x,P (S^[n] x))).starProjection‖≤1/2 ∧
      ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-(Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2 := by
    refine ⟨(EuclideanSplitting.finrank_groupSpace _ _ _ _ _).trans (hend x).1.symm,?_,(hend x).2.2⟩
    calc
      _ = (T x)ᶜ.card := EuclideanSplitting.finrank_groupSpace _ _ _ _ _
      _ = d-(T x).card := by rw [Finset.card_compl]; simp only [Fintype.card_fin]
      _ = _ := (hend x).2.1.symm
  obtain ⟨Φ,hΦ,hswitch,hself,huniq⟩ := hcanonical C J c P L G R n B R₀ ε g α r δ γ A T ref Wf Wb
    hc hP hL hR hRG hcover hLP hPc hint href hcard hreff hstart hend' hε hεhalf hsmall hslow hfast hgap
    hα hr hδ hδr hsafe hnear hcontract hdata
  have hpair (u : M×M) (hx : u.1∈R) (hy : u.2∈R) (he : L u.1=L u.2) :=
    hswitch ⟨u.1,hRG hx⟩ ⟨u.2,hRG hy⟩ hx hy he
  let U (x : M) : E₀ →L[ℝ] E₀ := if hx : x∈G then
    (((A (ref ⟨x,hx⟩)).forward I S a c).splitting (T (ref ⟨x,hx⟩))ᶜ).slow 0 else 0
  have hU (x : M) (hx : x∈G) : U x=
      (((A (ref ⟨x,hx⟩)).forward I S a c).splitting (T (ref ⟨x,hx⟩))ᶜ).slow 0 := by simp only [U,dite_eq_left hx]
  have hsharp (u : M×M) (hx : u.1∈R) (hy : u.2∈R) (he : L u.1=L u.2) :
      originalTube I S a c (n:=n) ρ u.1 (Φ u).1 ∧
      originalTube I S.symm a c (n:=n) ρ u.2 (Φ u).1 ∧
      originalTube I S a c (n:=n) ρ u.2 (Φ u).2 ∧
      originalTube I S.symm a c (n:=n) ρ u.1 (Φ u).2 ∧
      ‖(extChartAt I (a (c u.1))) (Φ u).1-(extChartAt I (a (c u.1))) u.1-
        U u.1 ((extChartAt I (a (c u.2))) u.2-(extChartAt I (a (c u.1))) u.1)‖≤E ∧
      ‖(extChartAt I (a (c u.2))) (Φ u).2-(extChartAt I (a (c u.2))) u.2-
        U u.2 ((extChartAt I (a (c u.1))) u.1-(extChartAt I (a (c u.2))) u.2)‖≤E := by
    rw [hU u.1 (hRG hx),hU u.2 (hRG hy)]
    exact (hpair u hx hy he).2.2.2.2.2.2.2.2
  have heqs (u : M×M) (hx : u.1∈R) (hy : u.2∈R) (he : L u.1=L u.2) :
      originalEndpoint I S a c (n:=n) (Wf (P u.1,P (S^[n] u.1))) u.1 (Φ u).1 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P u.1,P (S.symm^[n] u.1))) u.1 (Φ u).2 ∧
      originalEndpoint I S a c (n:=n) (Wf (P u.2,P (S^[n] u.2))) u.2 (Φ u).2 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P u.2,P (S.symm^[n] u.2))) u.2 (Φ u).1 := by
    have h := hpair u hx hy he
    exact ⟨h.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.1⟩
  obtain ⟨hkeep,hlabels,hinj⟩ := hrecover S c P L π chart hπ hchart n δ ρ δc δp H₀ E R V Wc Wp U Φ Wf Wb
    hcover hρ hρσ hρc hρr₁ hρC hH₀ hE hcore hcoarse
    (fun x y z hx he hxW hyW hz herr => hprod x y z hx he hxW hyW hz (by rwa [hU x (hRG hx)] at herr))
    hret hsafe hsharp heqs hself
  have hGp : MeasurableSet Gp :=
    (hR.preimage measurable_fst).inter ((hR.preimage measurable_snd).inter
      (measurableSet_eq_fun (hL.comp measurable_fst) (hL.comp measurable_snd)))
  have hlc (x : M) (hxV : x∈V) (hxW : x∉Wc) : ∀ᶠ z in 𝓝 x,P z=P x := by
    apply original_coarse_germ I a c P x (by simpa only [extChartAt_source] using hsrc x) s δc hs hδc (hcore x hxV)
    intro y hcy hdist
    apply hcoarse x y hxW hcy
    have hsy : y∈(extChartAt I (a (c x))).source := by rw [←hcy]; exact hsrc y
    rwa [ChartDensity.coordinates_eq I _ _ hsy,ChartDensity.coordinates_eq I _ _ (hsrc x)]
  have hgerms (x y : M) (hxy : (x,y)∈Gp) :
      let e := Prod.map (ChartDensity.coordinates I (a (c x))) (ChartDensity.coordinates I (a (c x)))
      let si := Prod.map (ChartDensity.inverse I (a (c x))) (ChartDensity.inverse I (a (c x)))
      let u := ((extChartAt I (a (c x))) x,(extChartAt I (a (c x))) y)
      ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ u) u ∧
        (81/121:ℝ)≤|(fderiv ℝ Ψ u).det| ∧
        Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e si Gp] u] (e ∘ Φ ∘ si) := by
    have hx := hxy.1
    have hy := hxy.2.1
    have hLxy := hxy.2.2
    have hPxy := hLP x y hLxy
    have hcxy := hPc x y hPxy
    let X : G := ⟨x,hRG hx⟩
    let Y : G := ⟨y,hRG hy⟩
    let Z : G := ref X
    have hZx : P Z=P x := href X
    have hTx : (T X).card=(T Z).card := hcard X Z hZx.symm
    have hTy : (T Y).card=(T Z).card := hcard Y Z (hPxy.symm.trans hZx.symm)
    have hrefY : ref Y=Z := hreff Y X hPxy.symm
    have hSX := hstart X
    have hSY := hstart Y
    rw [hrefY] at hSY
    have ht := hsharp (x,y) hx hy hLxy
    have he := heqs (x,y) hx hy hLxy
    apply hgerm c P L R Wf Wb n b R₀ Cext δ ε (γ (P x)) g ρ Φ Gp x y hcover hPc hcxy
      hb hbn hR₀ hCext hε hg hρ hρδ hδrg hρCg hδF hδB hpoly hbudF hbudB
      (fun u hu => hu) huniq
      (fun u hu v hv huv => ⟨originalTube_mono I S a c n hρδ (hsharp (u,v) hu hv huv).2.2.1,
        originalTube_mono I S.symm a c n hρδ (hsharp (u,v) hu hv huv).2.2.2.1,
        (heqs (u,v) hu hv huv).2.2.1,(heqs (u,v) hu hv huv).2.1⟩)
      (fun t => ⟨(hsafe x hx t).1,(hsafe x hx t).2,(hsafe y hy t).1,(hsafe y hy t).2⟩)
      ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 Z (A Z) (A X) (A Y) (T Z) (T X) (T Y) hTx hTy
      (hfast X) (fun j hj => hslow X j (Finset.mem_compl.mpr hj))
      (by simpa only [hPxy] using hfast Y) (by simpa only [hPxy] using fun j hj => hslow Y j (Finset.mem_compl.mpr hj))
      ((hend X).1.trans hTx) ((hend Y).1.trans hTy)
      ((hend X).2.1.trans (congrArg (d-·) hTx)) ((hend Y).2.1.trans (congrArg (d-·) hTy))
      (hend X).2.2.1 (hend Y).2.2.1 (hend X).2.2.2 (hend Y).2.2.2
      (by rw [norm_sub_rev]; exact hSX.2) (by rw [norm_sub_rev]; exact hSY.2)
      (by rw [norm_sub_rev]; exact hSX.1) (by rw [norm_sub_rev]; exact hSY.1)
      he.1 he.2.2.1 he.2.1 he.2.2.2
    have hsy : y∈(extChartAt I (a (c x))).source := by rw [hcxy]; exact hsrc y
    have hiX : (extChartAt I (a (c x))) x∈interior (range I) :=
      (hsafe x hx ⟨0,by omega⟩).1 (by simpa only [Function.iterate_zero_apply] using mem_closedBall_self hδ.le)
    have hiY : (extChartAt I (a (c x))) y∈interior (range I) := by
      rw [hcxy]
      exact (hsafe y hy ⟨0,by omega⟩).1 (by simpa only [Function.iterate_zero_apply] using mem_closedBall_self hδ.le)
    exact six_original_labels I S P (a (c x)) x y n (hsrc x) hsy hiX hiY
      (hlc x (hret x hx).1 (hret x hx).2.1) (hlc y (hret y hy).1 (hret y hy).2.1)
      (hlc _ (hret x hx).2.2.2.1 (hret x hx).2.2.2.2.1)
      (hlc _ (hret y hy).2.2.2.1 (hret y hy).2.2.2.2.1)
      (hlc _ (hret x hx).2.2.2.2.2.1 (hret x hx).2.2.2.2.2.2)
      (hlc _ (hret y hy).2.2.2.2.2.1 (hret y hy).2.2.2.2.2.2)
  have hlaw' := hlaw L c (chart ∘ π) hL hcover (fun x => by simp only [Function.comp_apply,hπ,hchart])
    hdiam Gp Φ hGp hΦ (fun u hu => ⟨hu.2.2,hkeep u hu⟩) hinj hgerms
  exact ⟨Φ,hΦ,hGp,hinj,hlaw'.1,hlaw'.2,fun u hu => ⟨(hsharp u hu.1 hu.2.1 hu.2.2).1,(hsharp u hu.1 hu.2.1 hu.2.2).2.1⟩⟩
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.SmoothObstruction.ManifoldCoordinates.genuine_pair_switch_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.SmoothObstruction.ManifoldCoordinates.genuine_pair_switch_oai.{u_1, u_2, u_3, u_4, u_5}
