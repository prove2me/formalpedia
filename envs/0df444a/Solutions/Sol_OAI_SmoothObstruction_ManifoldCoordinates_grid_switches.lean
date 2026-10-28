-- Prove2me | solution 1 for OAI.SmoothObstruction.ManifoldCoordinates.grid_switches
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:20:21.297997+00:00
-- url     : https://prove2.me/submissions/0309d9e2-13d8-44cd-b23a-0769764968ce

import Mathlib
import Definitions.Def_SmoothObstruction
import Definitions.Def_OAIQ5T3000
import Theorems.Thm_OAI_SmoothObstruction_ManifoldCoordinates_genuine_pair_switch

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


end SmoothObstruction.ManifoldCoordinates

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

lemma transition_one_step (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hUV : ∀ t, U t*V t=1) (t : ℕ)
    (hA : A t*U t=U (t+1)*rate lam 1) :
    A t=transition U V lam t (t+1) := by
  have ht : ((t+1:ℕ):ℝ)-t=1 := by push_cast; ring
  dsimp [transition]
  rw [ht]
  calc
    _ = (A t*U t)*V t := by rw [mul_assoc,hUV,mul_one]
    _ = _ := by rw [hA]

lemma propagator_eq_transition (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hUV : ∀ t, U t*V t=1) (hVU : ∀ t, V t*U t=1)
    (N : ℕ) (hA : ∀ t < N, A t*U t=U (t+1)*rate lam 1)
    (s l : ℕ) (hl : s+l ≤ N) :
    propagator A s l=transition U V lam s (s+l) := by
  induction l with
  | zero => simpa only [Nat.add_zero,propagator] using (transition_self U V lam hUV s).symm
  | succ l ih =>
    rw [propagator,ih (by omega),transition_one_step A U V lam hUV (s+l) (hA _ (by omega)),
      transition_comp U V lam hVU]
    rfl

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

/-- Carried local expressions preserve the *original* model interior on
exactly their actual relative domains, even for manifolds with boundary. -/
theorem localMap_maps_interior (S : Diffeomorph I I M M ∞) (a b : M) :
    MapsTo (localMap I S a b) (domainU I S a b∩interior (range I))
      (interior (range I)) := by
  intro y hy
  have hyt : y∈(extChartAt I a).target := by
    rw [extChartAt,OpenPartialHomeomorph.extend_target]
    exact ⟨hy.1.1,interior_subset hy.2⟩
  let x := (extChartAt I a).symm y
  have hx : x∈(chartAt H a).source := by
    simpa only [extChartAt_source] using (extChartAt I a).map_target hyt
  have hxy : (extChartAt I a) x=y := (extChartAt I a).right_inv hyt
  have hxi : I.IsInteriorPoint x := (interior_coord I a x hx).mp (hxy.symm ▸ hy.2)
  have hSi : I.IsInteriorPoint (S x) :=
    ((S.isLocalDiffeomorph x).isInteriorPoint_iff (by simp)).mp hxi
  have hSx : S x∈(chartAt H b).source := hy.1.2
  exact (interior_coord I b (S x) hSx).mpr hSi

omit [IsManifold I ∞ M] in
lemma localMap_coordinates (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈(chartAt H a).source) :
    localMap I S a b ((extChartAt I a) x)=(extChartAt I b) (S x) := by
  simp only [localMap,Function.comp_apply,
    (extChartAt I a).left_inv (by simpa only [extChartAt_source] using hx)]
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ShortDerivative
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

namespace SmoothObstruction.RelativeProduct

variable {R : Type*}

/-- Exact variation-of-constants expansion; no commutativity is used. -/
theorem difference [Ring R] (A B : ℕ → R) (s n : ℕ) :
    segment B s n - segment A s n =
      ∑ j ∈ Finset.range n,
        segment A (s + j + 1) (n - (j + 1)) *
          (B (s + j) - A (s + j)) * segment B s j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, segment_zero, one_mul]
    have hsum :
        (∑ j ∈ Finset.range n,
          segment A (s + j + 1) (n + 1 - (j + 1)) *
            (B (s + j) - A (s + j)) * segment B s j) =
          A (s + n) * (segment B s n - segment A s n) := by
      rw [ih, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjn : j < n := Finset.mem_range.mp hj
      have hlen : n + 1 - (j + 1) = (n - (j + 1)) + 1 := by omega
      have hidx : s + j + 1 + (n - (j + 1)) = s + n := by omega
      rw [hlen, segment_succ, hidx]
      simp only [mul_assoc]
    rw [hsum, segment_succ, segment_succ]
    noncomm_ring

end SmoothObstruction.RelativeProduct

namespace SmoothObstruction.RelativeProduct
open Finset
variable {R : Type*} [NormedRing R]

lemma segment_norm_le (A : ℕ → R) (s n : ℕ) (hOne : ‖(1:R)‖≤1) {K : ℝ} (hK : 0≤K)
    (hA : ∀ t,s≤t → t < s+n → ‖A t‖≤K) : ‖segment A s n‖≤K^n := by
  induction n with
  | zero => simpa only [segment_zero,pow_zero] using hOne
  | succ n ih =>
    rw [segment_succ,pow_succ]
    exact (norm_mul_le _ _).trans (by
      simpa only [mul_comm] using mul_le_mul (hA _ (by omega) (by omega))
        (ih (fun t ht ht' => hA t ht (by omega))) (norm_nonneg _) hK)

/-- Ordinary C¹ telescoping on a short interval. Unlike the long-window
relative exterior estimate this bound pays the one-step bound, precisely
where the manuscript permits an exp(CL) loss. -/
lemma short_difference (A B : ℕ → R) (N : ℕ) (hOne : ‖(1:R)‖≤1) {K δ : ℝ}
    (hK : 1≤K) (hδ : 0≤δ)
    (hA : ∀ t<N,‖A t‖≤K) (hB : ∀ t<N,‖B t‖≤K)
    (hBA : ∀ t<N,‖B t-A t‖≤δ) :
    ‖segment B 0 N-segment A 0 N‖≤N*K^N*δ := by
  rw [difference]
  calc
    _≤∑ j∈range N,‖segment A (0+j+1) (N-(j+1))*(B (0+j)-A (0+j))*segment B 0 j‖ := norm_sum_le _ _
    _≤∑ j∈range N,K^N*δ := by
      apply sum_le_sum
      intro j hj
      have hjN := mem_range.mp hj
      have hAl := segment_norm_le A (j+1) (N-(j+1)) hOne (by linarith : 0≤K)
        (fun t _ ht => hA t (by omega))
      have hBj := segment_norm_le B 0 j hOne (by linarith : 0≤K)
        (fun t _ ht => hB t (by omega))
      calc
        _≤‖segment A (j+1) (N-(j+1))‖*‖B j-A j‖*‖segment B 0 j‖ := by
          simpa only [Nat.zero_add] using
            (norm_mul_le (segment A (j+1) (N-(j+1))*(B j-A j)) (segment B 0 j)).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _≤K^(N-(j+1))*δ*K^j := by
          apply mul_le_mul _ hBj (norm_nonneg _) (by positivity)
          exact mul_le_mul hAl (hBA j hjN) (norm_nonneg _) (by positivity)
        _=K^(N-(j+1)+j)*δ := by rw [pow_add]; ring
        _≤K^N*δ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (by omega)) hδ
    _=N*K^N*δ := by simp only [sum_const,card_range,nsmul_eq_mul]; ring
end SmoothObstruction.RelativeProduct

namespace SmoothObstruction.ShortDerivative
open Set Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma orbit_eq_iterate (f : ℕ → E → E) (x : ℕ → E) (N : ℕ)
    (hx : ∀ t<N,f t (x t)=x (t+1)) : ∀ t≤N,iterate f t (x 0)=x t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    change f t (iterate f t (x 0))=x (t+1)
    rw [ih (by omega),hx t (by omega)]

lemma derivative_iterate (f : ℕ → E → E) (x : ℕ → E)
    (A : ℕ → E →L[ℝ] E) (N : ℕ)
    (hx : ∀ t<N,f t (x t)=x (t+1))
    (hd : ∀ t<N,HasFDerivAt (f t) (A t) (x t)) :
    HasFDerivAt (iterate f N) (RelativeProduct.segment A 0 N) (x 0) := by
  induction N with
  | zero => exact hasFDerivAt_id _
  | succ N ih =>
    have hN := ih (fun t ht => hx t (by omega)) (fun t ht => hd t (by omega))
    have he := orbit_eq_iterate f x (N+1) hx N (by omega)
    have hdN := hd N (by omega)
    rw [←he] at hdN
    have h := hdN.comp (x 0) hN
    simpa only [iterate,RelativeProduct.segment_succ,Nat.zero_add,ContinuousLinearMap.mul_def] using h

/-- Nearby genuine coordinate orbits have exponentially close short
products, under uniform first and second derivative bounds on convex
patches. No derivative of the long iterate is bounded by fiat. -/
theorem short_c1_stability (f : ℕ → E → E) (x y : ℕ → E)
    (s : ℕ → Set E) (N : ℕ) {K D : ℝ} (hK : 1≤K) (hD : 0≤D)
    (hx : ∀ t<N,f t (x t)=x (t+1)) (hy : ∀ t<N,f t (y t)=y (t+1))
    (hxs : ∀ t<N,x t∈s t) (hys : ∀ t<N,y t∈s t)
    (hs : ∀ t<N,Convex ℝ (s t))
    (hf : ∀ t<N,∀ a∈s t,DifferentiableAt ℝ (f t) a)
    (hff : ∀ t<N,∀ a∈s t,DifferentiableAt ℝ (fderiv ℝ (f t)) a)
    (hfirst : ∀ t<N,∀ a∈s t,‖fderiv ℝ (f t) a‖≤K)
    (hsecond : ∀ t<N,∀ a∈s t,‖fderiv ℝ (fderiv ℝ (f t)) a‖≤D) :
    (∀ t≤N,‖y t-x t‖≤K^t*‖y 0-x 0‖) ∧
    ‖fderiv ℝ (iterate f N) (y 0)-fderiv ℝ (iterate f N) (x 0)‖≤
      N*D*K^(2*N)*‖y 0-x 0‖ := by
  have hdist : ∀ t≤N,‖y t-x t‖≤K^t*‖y 0-x 0‖ := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      rw [←hy t (by omega),←hx t (by omega)]
      have hh := (hs t (by omega)).norm_image_sub_le_of_norm_fderiv_le
        (hf t (by omega)) (hfirst t (by omega)) (hxs t (by omega)) (hys t (by omega))
      exact hh.trans (by
        calc
          _≤K*(K^t*‖y 0-x 0‖) := mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
          _=K^(t+1)*‖y 0-x 0‖ := by rw [pow_succ]; ring)
  refine ⟨hdist,?_⟩
  let A := fun t => fderiv ℝ (f t) (x t)
  let B := fun t => fderiv ℝ (f t) (y t)
  have hAx := derivative_iterate f x A N hx (fun t ht => (hf t ht _ (hxs t ht)).hasFDerivAt)
  have hBy := derivative_iterate f y B N hy (fun t ht => (hf t ht _ (hys t ht)).hasFDerivAt)
  rw [hAx.fderiv,hBy.fderiv]
  have hdiff : ∀ t<N,‖B t-A t‖≤D*K^N*‖y 0-x 0‖ := by
    intro t ht
    have hh := (hs t ht).norm_image_sub_le_of_norm_fderiv_le (hff t ht) (hsecond t ht) (hxs t ht) (hys t ht)
    exact hh.trans (by
      calc
        D*‖y t-x t‖≤D*(K^t*‖y 0-x 0‖) := mul_le_mul_of_nonneg_left (hdist t ht.le) hD
        _≤D*(K^N*‖y 0-x 0‖) := by gcongr
        _=D*K^N*‖y 0-x 0‖ := by ring)
  have hb := RelativeProduct.short_difference A B N ContinuousLinearMap.norm_id_le hK
    (by positivity : 0≤D*K^N*‖y 0-x 0‖)
    (fun t ht => hfirst t ht _ (hxs t ht)) (fun t ht => hfirst t ht _ (hys t ht)) hdiff
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  rw [show 2*N=N+N by omega,pow_add]
  ring
end SmoothObstruction.ShortDerivative

namespace SmoothObstruction.ShortDerivative
open Set Metric
open scoped ContDiff
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [Fintype ι]

/-- Bootstrap nearby genuine local-map orbits into the carried domains,
using only one-sided C2 bounds on a convex closed model (in particular a
half-space). No extension across the boundary is assumed.
The only smallness required is C^N times the initial displacement; no
long-iterate derivative estimate or continued domain membership is assumed. -/
theorem uniform_short_interior (f : ι → E → E) (K U : ι → Set E)
    (H : Set E) (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i))
    (hH : IsClosed H) (hconvH : Convex ℝ H) (hKU : ∀ i,K i⊆U i)
    (huniq : ∀ i,UniqueDiffOn ℝ (U i∩H))
    (hf : ∀ i,ContDiffOn ℝ ∞ (f i) (U i∩H))
    (hmaps : ∀ i,MapsTo (f i) (U i∩interior H) (interior H)) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ (a : ℕ → ι) (x y : ℕ → E) (N : ℕ),
      (∀ t<N,x t∈K (a t)) →
      (∀ t<N,x t∈interior H) → y 0∈interior H →
      (∀ t<N,f (a t) (x t)=x (t+1)) →
      (∀ t<N,f (a t) (y t)=y (t+1)) →
      C^N*‖y 0-x 0‖ ≤ r →
      (∀ t≤N,‖y t-x t‖ ≤ C^t*‖y 0-x 0‖ ∧ y t∈interior H) ∧
      (∀ t<N,y t∈U (a t)) ∧
      ‖fderiv ℝ (iterate (fun t => f (a t)) N) (y 0)-
        fderiv ℝ (iterate (fun t => f (a t)) N) (x 0)‖ ≤
        N*C*C^(2*N)*‖y 0-x 0‖ := by
  obtain ⟨r,C,hr,hC,hbounds⟩ := CarriedCharts.uniform_c2_boundary f K U H hK hU hH hKU huniq hf
  refine ⟨r,C,hr,hC,fun a x y N hxs hxi hyi hx hy hsmall => ?_⟩
  have hcontrol : ∀ t≤N,‖y t-x t‖ ≤ C^t*‖y 0-x 0‖ ∧ y t∈interior H := by
    intro t ht
    induction t with
    | zero => exact ⟨by simp,hyi⟩
    | succ t ih =>
      have htp : t<N := by omega
      have hi := ih (by omega)
      have hb := hbounds (a t) (x t) (hxs t htp)
      have hyb : y t∈closedBall (x t) r := by
        rw [mem_closedBall,dist_eq_norm]
        exact hi.1.trans ((mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hC (by omega : t≤N)) (norm_nonneg _)).trans hsmall)
      have hxb : x t∈closedBall (x t) r := mem_closedBall_self hr.le
      constructor
      · rw [←hx t htp,←hy t htp]
        have hstep := ((convex_closedBall (x t) r).inter hconvH.interior).norm_image_sub_le_of_norm_fderiv_le
          (fun z hz => (hb.2 z hz.1 hz.2).1.differentiableAt (by simp))
          (fun z hz => (hb.2 z hz.1 hz.2).2.1) ⟨hxb,hxi t htp⟩ ⟨hyb,hi.2⟩
        exact hstep.trans (by
          calc
            C*‖y t-x t‖ ≤ C*(C^t*‖y 0-x 0‖) :=
              mul_le_mul_of_nonneg_left hi.1 (by linarith)
            _=C^(t+1)*‖y 0-x 0‖ := by rw [pow_succ]; ring)
      · rw [←hy t htp]
        exact hmaps (a t) ⟨hb.1 hyb,hi.2⟩
  have hdist := fun t ht => (hcontrol t ht).1
  have hint := fun t ht => And.intro (hxi t ht) (hcontrol t ht.le).2
  have hyball (t : ℕ) (ht : t<N) : y t∈closedBall (x t) r := by
    rw [mem_closedBall,dist_eq_norm]
    exact (hdist t ht.le).trans ((mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hC ht.le) (norm_nonneg _)).trans hsmall)
  refine ⟨hcontrol,fun t ht => (hbounds (a t) (x t) (hxs t ht)).1 (hyball t ht),?_⟩
  exact (short_c1_stability (fun t => f (a t)) x y
    (fun t => closedBall (x t) r∩interior H) N
    hC (by linarith : 0≤C) hx hy
    (fun t ht => ⟨mem_closedBall_self hr.le,(hint t ht).1⟩)
    (fun t ht => ⟨hyball t ht,(hint t ht).2⟩)
    (fun t _ => (convex_closedBall (x t) r).inter hconvH.interior)
    (fun t ht z hz => ((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).1.differentiableAt (by simp))
    (fun t ht z hz => (((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).1.fderiv_right
      (m:=∞) (by simp)).differentiableAt (by simp))
    (fun t ht z hz => ((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).2.1)
    (fun t ht z hz => ((hbounds (a t) (x t) (hxs t ht)).2 z hz.1 hz.2).2.2)).2
end SmoothObstruction.ShortDerivative

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- The C1 comparison is for genuine manifold orbits in one fixed carried
chart sequence. Neither continued chart membership nor staying in the
interior is assumed for the perturbed orbit: both are proved. The constants
are uniform over every sequence of reference charts, orbit and length. -/
theorem actual_short_comparison (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0 < r ∧ 1 ≤ C ∧ ∀ (c : ℕ → ι) (x y : M) (N : ℕ),
      (∀ t≤N,S^[t] x∈K (c t)) → I.IsInteriorPoint x → I.IsInteriorPoint y →
      y∈(chartAt H (a (c 0))).source →
      C ^ N*‖(extChartAt I (a (c 0))) y-(extChartAt I (a (c 0))) x‖ ≤ r →
      (∀ t≤N,S^[t] y∈(chartAt H (a (c t))).source ∧
        ‖(extChartAt I (a (c t))) (S^[t] y)-(extChartAt I (a (c t))) (S^[t] x)‖ ≤
          C ^ t*‖(extChartAt I (a (c 0))) y-(extChartAt I (a (c 0))) x‖) ∧
      ‖fderiv ℝ (ShortDerivative.iterate (fun t => localMap I S (a (c t)) (a (c (t+1)))) N)
          ((extChartAt I (a (c 0))) y)-
        fderiv ℝ (ShortDerivative.iterate (fun t => localMap I S (a (c t)) (a (c (t+1)))) N)
          ((extChartAt I (a (c 0))) x)‖ ≤
          N*C*C ^ (2*N)*‖(extChartAt I (a (c 0))) y-(extChartAt I (a (c 0))) x‖ := by
  let L (ij : ι×ι) := (extChartAt I (a ij.1)) '' (K ij.1∩S ⁻¹' K ij.2)
  have hcomp (ij : ι×ι) : IsCompact (L ij) :=
    ((hK ij.1).inter_right ((hK ij.2).isClosed.preimage S.continuous)).image_of_continuousOn
      ((continuousOn_extChartAt (I:=I) (a ij.1)).mono (fun x hx => by
        simpa only [extChartAt_source] using hKU _ hx.1))
  have hsub (ij : ι×ι) : L ij⊆domainU I S (a ij.1) (a ij.2) := by
    rintro z ⟨x,hx,rfl⟩
    exact map_mem_domainU I S (a ij.1) (a ij.2) x ⟨hKU _ hx.1,hKU _ hx.2⟩
  obtain ⟨r,C,hr,hC,hh⟩ := ShortDerivative.uniform_short_interior
    (fun ij : ι×ι => localMap I S (a ij.1) (a ij.2)) L
    (fun ij => domainU I S (a ij.1) (a ij.2)) (range I) hcomp
    (fun ij => isOpen_domainU I S (a ij.1) (a ij.2)) hclosed I.convex_range hsub
    (fun ij => by simpa only [inter_comm] using
      I.uniqueDiffOn.inter (isOpen_domainU I S (a ij.1) (a ij.2)))
    (fun ij => contDiffOn_localMap I S (a ij.1) (a ij.2))
    (fun ij => localMap_maps_interior I S (a ij.1) (a ij.2))
  refine ⟨r,C,hr,hC,fun c x y N hxs hxi hyi hy0 hsmall => ?_⟩
  let f : ℕ → E (d:=d) → E (d:=d) := fun t => localMap I S (a (c t)) (a (c (t+1)))
  let X : ℕ → E (d:=d) := fun t => (extChartAt I (a (c t))) (S^[t] x)
  let Y : ℕ → E (d:=d) := fun t => ShortDerivative.iterate f t ((extChartAt I (a (c 0))) y)
  have hXi : ∀ t,I.IsInteriorPoint (S^[t] x) := by
    intro t
    induction t with
    | zero => exact hxi
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ((S.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp ih
  have hXL : ∀ t<N,X t∈L (c t,c (t+1)) := by
    intro t ht
    have hnext : S (S^[t] x) ∈ K (c (t+1)) := by
      simpa only [Function.iterate_succ_apply'] using hxs (t+1) (by omega)
    exact ⟨S^[t] x,⟨hxs t ht.le,hnext⟩,rfl⟩
  have hXint : ∀ t<N,X t∈interior (range I) := fun t ht =>
    (interior_coord I _ _ (hKU _ (hxs t ht.le))).mpr (hXi t)
  have hY0 : Y 0∈interior (range I) := (interior_coord I _ y hy0).mpr hyi
  have hXrec : ∀ t<N,f t (X t)=X (t+1) := by
    intro t ht
    simpa only [f,X,Function.iterate_succ_apply'] using
      localMap_coordinates I S (a (c t)) (a (c (t+1))) (S^[t] x) (hKU _ (hxs t ht.le))
  have hYrec : ∀ t<N,f t (Y t)=Y (t+1) := fun _ _ => rfl
  have hsmall' : C ^ N*‖Y 0-X 0‖ ≤ r := hsmall
  obtain ⟨hb,hu,hd⟩ := hh (fun t => (c t,c (t+1))) X Y N hXL hXint hY0 hXrec hYrec hsmall'
  have hactual : ∀ t≤N,S^[t] y∈(chartAt H (a (c t))).source ∧
      Y t=(extChartAt I (a (c t))) (S^[t] y) := by
    intro t ht
    induction t with
    | zero => exact ⟨hy0,rfl⟩
    | succ t ih =>
      obtain ⟨hyt,heq⟩ := ih (by omega)
      have htN : t<N := by omega
      have hm := (hu t htN).2
      change S ((extChartAt I (a (c t))).symm (Y t))∈(chartAt H (a (c (t+1)))).source at hm
      rw [heq,(extChartAt I (a (c t))).left_inv
        (by simpa only [extChartAt_source] using hyt)] at hm
      constructor
      · simpa only [Function.iterate_succ_apply'] using hm
      · rw [←hYrec t htN,heq]
        change localMap I S (a (c t)) (a (c (t+1)))
          ((extChartAt I (a (c t))) (S^[t] y))=_
        rw [localMap_coordinates I S _ _ _ hyt,Function.iterate_succ_apply']
  refine ⟨fun t ht => ⟨(hactual t ht).1,?_⟩,hd⟩
  simpa only [(hactual t ht).2,X,Y,ShortDerivative.iterate,Function.iterate_zero_apply,id_eq]
    using (hb t ht).1
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

namespace SmoothObstruction.EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma groupSpace_forward (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) {K c : ℝ} {s t : ℕ} (hst : s≤t)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V s‖≤Real.exp K)
    (hc : ∀ j∈S,lam j ≤ c) (x : groupSpace (U s) (V s) (hUV s) (hVU s) S) :
    ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t) x‖ ≤
      Real.exp (c*((t:ℝ)-s)+2*K)*‖x‖ := by
  have hx := (groupSpace_fixed (U s) (V s) (hUV s) (hVU s) S x).mp x.property
  have hb := norm_transition_projection U V hVU lam S s t hst hU hV hc
  have hn := (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
    (transition U V lam s t*projection U V S s)).le_opNorm (x:EuclideanSpace ℝ (Fin d))
  rw [Matrix.l2_opNorm_toEuclideanCLM,map_mul,mul_apply_eq_comp] at hn
  change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S s) x=x at hx
  rw [hx] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma inverse_fast_product (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) (s t : ℕ) :
    (transition U V lam t s*projection U V S t)*transition U V lam s t=
      projection U V S s := by
  rw [mul_assoc,←transition_projection U V lam hVU,
    ←mul_assoc (transition U V lam t s),transition_comp U V lam hVU,
    transition_self U V lam hUV,one_mul]

lemma groupSpace_backward_lower (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) {K c : ℝ} {s t : ℕ} (hst : s≤t)
    (hU : ‖U s‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K)
    (hc : ∀ j∈S,c≤lam j) (x : groupSpace (U s) (V s) (hUV s) (hVU s) S) :
    Real.exp (c*((t:ℝ)-s)-2*K)*‖x‖ ≤
      ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t) x‖ := by
  have hx := (groupSpace_fixed (U s) (V s) (hUV s) (hVU s) S x).mp x.property
  have hb := norm_backward_projection U V hVU lam S s t hst hU hV hc
  let P := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  let B := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
    (transition U V lam t s*projection U V S t)
  have hBP : B (P x)=x := by
    dsimp [B,P]
    rw [←mul_apply_eq_comp,←map_mul,inverse_fast_product U V hUV hVU]
    exact hx
  have hn := B.le_opNorm (P x)
  rw [hBP] at hn
  have hBn : ‖B‖≤Real.exp (-c*((t:ℝ)-s)+2*K) := by
    dsimp [B]
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact hb
  have hxn : ‖(x:EuclideanSpace ℝ (Fin d))‖ ≤
      Real.exp (-c*((t:ℝ)-s)+2*K)*‖P x‖ :=
    hn.trans (mul_le_mul_of_nonneg_right hBn (norm_nonneg _))
  have hm := mul_le_mul_of_nonneg_left hxn (Real.exp_nonneg (c*((t:ℝ)-s)-2*K))
  have he : Real.exp (c*((t:ℝ)-s)-2*K)*Real.exp (-c*((t:ℝ)-s)+2*K)=1 := by
    rw [←Real.exp_add]
    rw [show (c*((t:ℝ)-s)-2*K)+(-c*((t:ℝ)-s)+2*K)=0 by ring,Real.exp_zero]
  rw [←mul_assoc,he,one_mul] at hm
  exact hm

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.SubspaceComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The elementary dimension/count comparison underlying finite singular
rate comparison. Actual operator closeness and stretch bounds force disjointness. -/
lemma disjoint_of_stretch (P Q : E →L[ℝ] E) (U V : Submodule ℝ E)
    {a b δ : ℝ} (hgap : b+δ<a) (hclose : ‖P-Q‖ ≤ δ)
    (hU : ∀ x : U, a*‖x‖ ≤ ‖P x‖) (hV : ∀ x : V, ‖Q x‖ ≤ b*‖x‖) :
    Disjoint U V := by
  rw [Submodule.disjoint_def]
  intro x hxU hxV
  have hu := hU ⟨x,hxU⟩
  have hv := hV ⟨x,hxV⟩
  change a*‖x‖ ≤ ‖P x‖ at hu
  change ‖Q x‖ ≤ b*‖x‖ at hv
  have hd : ‖P x-Q x‖ ≤ δ*‖x‖ :=
    ((P-Q).le_opNorm x).trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
  have ht : ‖P x‖ ≤ ‖P x-Q x‖+‖Q x‖ := by
    simpa only [sub_add_cancel] using norm_add_le (P x-Q x) (Q x)
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg x]

lemma dimension_of_stretch (P Q : E →L[ℝ] E) (U V : Submodule ℝ E)
    {a b δ : ℝ} (hgap : b+δ<a) (hclose : ‖P-Q‖ ≤ δ)
    (hU : ∀ x : U, a*‖x‖ ≤ ‖P x‖) (hV : ∀ x : V, ‖Q x‖ ≤ b*‖x‖) :
    Module.finrank ℝ U+Module.finrank ℝ V ≤ Module.finrank ℝ E := by
  have hh := disjoint_of_stretch P Q U V hgap hclose hU hV
  have hd := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hh.eq_bot, finrank_bot,add_zero] at hd
  rw [←hd]
  exact Submodule.finrank_le (U⊔V)

/-- Product comparison controls directed distance using an actual inverse
fast propagator B. K is the initial fast projector; its complementary image
lies in the reference slow space. -/
lemma directed_of_product (P Q B K : E →L[ℝ] E) (U V : Submodule ℝ E)
    {β σ δ : ℝ} (hβ : 0≤β)
    (hBP : B.comp P=K) (hB : ‖B‖≤β) (hclose : ‖P-Q‖≤δ)
    (hQ : ∀ x : U, ‖Q x‖≤σ*‖x‖)
    (hV : ∀ x, x-K x∈V) :
    ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ β*(σ+δ)*‖x‖ := by
  intro x
  have hPx : ‖P x‖ ≤ (σ+δ)*‖x‖ := by
    have hd : ‖P x-Q x‖ ≤ δ*‖x‖ :=
      ((P-Q).le_opNorm x).trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
    have ht := norm_add_le (Q x) (P x-Q x)
    rw [add_sub_cancel] at ht
    have hh := hQ x
    nlinarith
  have hKx : ‖K x‖ ≤ β*(σ+δ)*‖x‖ := by
    rw [←hBP,ContinuousLinearMap.comp_apply]
    calc
      _ ≤ ‖B‖*‖P x‖ := B.le_opNorm _
      _ ≤ β*((σ+δ)*‖x‖) := mul_le_mul hB hPx (norm_nonneg _) hβ
      _ = _ := by ring
  calc
    _ ≤ ‖(x:E)-((x:E)-K x)‖ := by
      rw [Submodule.starProjection_minimal]
      exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
        (⟨(x:E)-K x,hV x⟩:V)
    _ = ‖K x‖ := by rw [sub_sub_cancel]
    _ ≤ _ := hKx

end SmoothObstruction.SubspaceComparison

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator

variable {d L : ℕ} {K : ℝ}

lemma Gauge.rank (A : Gauge d L K) (S : Finset (Fin d)) :
    Module.finrank ℝ (A.space S)=S.card :=
  finrank_groupSpace _ _ _ _ _

lemma Gauge.upper (A : Gauge d L K) (S : Finset (Fin d)) {c : ℝ}
    (hc : ∀ j∈S,A.lam j ≤ c) (x : A.space S) :
    ‖A.product x‖≤Real.exp (c*L+2*K)*‖x‖ := by
  convert! groupSpace_forward A.U A.V A.UV A.VU A.lam S (Nat.zero_le L)
      (A.normU L le_rfl) (A.normV 0 (Nat.zero_le L)) hc x using 1
  all_goals try with_reducible_and_instances rfl
  simp
  rfl

lemma Gauge.lower (A : Gauge d L K) (S : Finset (Fin d)) {c : ℝ}
    (hc : ∀ j∈S,c≤A.lam j) (x : A.space S) :
    Real.exp (c*L-2*K)*‖x‖≤‖A.product x‖ := by
  convert! groupSpace_backward_lower A.U A.V A.UV A.VU A.lam S (Nat.zero_le L)
      (A.normU 0 (Nat.zero_le L)) (A.normV L le_rfl) hc x using 1
  all_goals try with_reducible_and_instances rfl
  simp
  rfl

/-- A count comparison from actual product closeness. -/
lemma count_le (A B : Gauge d L K) {a b δ : ℝ}
    (hclose : ‖A.product-B.product‖≤δ)
    (hgap : Real.exp (b*L+2*K)+δ<Real.exp (a*L-2*K)) :
    (Finset.univ.filter (fun j => a≤A.lam j)).card ≤
      (Finset.univ.filter (fun j => b<B.lam j)).card := by
  classical
  let S := Finset.univ.filter (fun j => a≤A.lam j)
  let T := Finset.univ.filter (fun j => B.lam j≤b)
  have hd := SubspaceComparison.dimension_of_stretch A.product B.product (A.space S) (B.space T)
    hgap hclose (A.lower S (by intro j hj; exact (Finset.mem_filter.mp hj).2))
      (B.upper T (by intro j hj; exact (Finset.mem_filter.mp hj).2))
  rw [A.rank,B.rank,finrank_euclideanSpace_fin] at hd
  have he : (Finset.univ.filter (fun j => b<B.lam j))=Tᶜ := by
    ext j
    simp [T,not_le]
  have hc := Finset.card_add_card_compl T
  simp only [Fintype.card_fin] at hc
  rw [he]
  dsimp [S] at hd
  omega

lemma exponential_separation {K g δ c l : ℝ} (hc : 0 ≤ c) (hl : 0≤l)
    (hdecay : Real.exp (-2*g*l+4*K)≤1/2)
    (hnoise : δ<Real.exp (-2*K)/2) :
    Real.exp ((c-2*g)*l+2*K)+δ<Real.exp (c*l-2*K) := by
  have he : Real.exp ((c-2*g)*l+2*K)=
      Real.exp (c*l-2*K)*Real.exp (-2*g*l+4*K) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have ha : Real.exp (-2*K)≤Real.exp (c*l-2*K) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hc hl])
  have hb := mul_le_mul_of_nonneg_left hdecay (Real.exp_nonneg (c*l-2*K))
  rw [he]
  nlinarith

end SmoothObstruction.ShortBin

namespace SmoothObstruction.RateThreshold

/-- The manuscript's d+1 predetermined candidates. The choice is uniform over
all other witnesses once short-product comparison has been applied. -/
lemma exists_candidate (d : ℕ) (lam : Fin d → ℝ) {g : ℝ} (hg : 0<g) :
    ∃ j : Fin (d+1), ∀ i, 3*g < |lam i-(1+8*(j.val:ℝ))*g| := by
  classical
  by_contra! h
  choose f hf using h
  have hinj : Function.Injective f := by
    intro j k heq
    by_contra hne
    have hj := hf j
    have hk := hf k
    rw [←heq] at hk
    obtain hjlo := (abs_le.mp hj).1
    obtain hjhi := (abs_le.mp hj).2
    obtain hklo := (abs_le.mp hk).1
    obtain hkhi := (abs_le.mp hk).2
    have hv : j.val≠k.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hh | hh
    · have ha : (j.val:ℝ)+1≤k.val := by exact_mod_cast hh
      nlinarith
    · have ha : (k.val:ℝ)+1≤j.val := by exact_mod_cast hh
      nlinarith
  have hh := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hh
  omega

/-- Two dimension comparisons exclude the whole intermediate rate band;
no singular-value decomposition or arbitrary sorted-rate choice is needed. -/
lemma of_sandwich {d p : ℕ} (lam : Fin d → ℝ) {γ g : ℝ} (hg : 0<g)
    (hlo : (Finset.univ.filter (fun j => γ-g≤lam j)).card≤p)
    (hhi : p≤(Finset.univ.filter (fun j => γ+g<lam j)).card) :
    (∀ j,lam j<γ-g ∨ γ+g<lam j) ∧
    (Finset.univ.filter (fun j => γ<lam j)).card=p := by
  classical
  let A := Finset.univ.filter (fun j : Fin d => γ-g≤lam j)
  let B := Finset.univ.filter (fun j : Fin d => γ+g<lam j)
  have hBA : B⊆A := by
    intro j hj
    simp only [B,Finset.mem_filter,Finset.mem_univ,true_and] at hj
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
    linarith
  have hc : A.card≤B.card := hlo.trans hhi
  have he : B=A := Finset.eq_of_subset_of_card_le hBA hc
  have ha : A.card=p := by
    dsimp [A,B] at he
    rw [he] at hhi
    exact le_antisymm hlo hhi
  have hd : ∀ j,lam j<γ-g ∨ γ+g<lam j := by
    intro j
    by_cases hj : lam j<γ-g
    · exact Or.inl hj
    · right
      have hjA : j∈A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_of_not_gt hj⟩
      rw [←he] at hjA
      simpa only [B,Finset.mem_filter,Finset.mem_univ,true_and] using hjA
  refine ⟨hd,?_⟩
  have heC : Finset.univ.filter (fun j : Fin d => γ<lam j)=A := by
    ext j
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hj; linarith
    · intro hj
      rcases hd j with hh | hh
      · exact (not_lt_of_ge hj hh).elim
      · linarith
  rw [heC,ha]

end SmoothObstruction.RateThreshold

namespace SmoothObstruction.ShortBin
open scoped Matrix.Norms.L2Operator
variable {d L : ℕ} {K : ℝ}

/-- All witnesses in one bin share the same predetermined threshold and
rank. This proves the source bin threshold without singular-value minmax. -/
theorem common_gap {ι : Type*} (A : ι→Gauge d L K) (e : ι) {g δ : ℝ}
    (hg : 0<g) (hclose : ∀ i,‖(A i).product-(A e).product‖≤δ)
    (hdecay : Real.exp (-2*g*L+4*K)≤1/2)
    (hnoise : δ<Real.exp (-2*K)/2) :
    ∃ j : Fin (d+1), let γ := (1+8*(j.val:ℝ))*g
      ∀ i, (∀ k,(A i).lam k<γ-g ∨ γ+g<(A i).lam k) ∧
        (Finset.univ.filter (fun k => γ<(A i).lam k)).card=
          (Finset.univ.filter (fun k => γ<(A e).lam k)).card := by
  classical
  obtain ⟨j,hj⟩ := RateThreshold.exists_candidate d (A e).lam hg
  refine ⟨j,?_⟩
  dsimp only
  let γ := (1+8*(j.val:ℝ))*g
  have hγ : g≤γ := by
    dsimp [γ]
    nlinarith [Nat.cast_nonneg (α:=ℝ) j.val]
  have hrep : ∀ k,(A e).lam k<γ-3*g ∨ γ+3*g<(A e).lam k := by
    intro k
    have hh := hj k
    change 3*g < |(A e).lam k-γ| at hh
    rcases le_total ((A e).lam k) γ with hh' | hh'
    · rw [abs_of_nonpos (sub_nonpos.mpr hh')] at hh
      left; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hh')] at hh
      right; linarith
  have hflo : Finset.univ.filter (fun k => γ-3*g<(A e).lam k)=
      Finset.univ.filter (fun k => γ<(A e).lam k) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rcases hrep k with hh | hh <;> constructor <;> intro hh' <;> linarith
  have hfhi : Finset.univ.filter (fun k => γ+3*g≤(A e).lam k)=
      Finset.univ.filter (fun k => γ<(A e).lam k) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rcases hrep k with hh | hh <;> constructor <;> intro hh' <;> linarith
  intro i
  have hlo := count_le (A i) (A e) (a:=γ-g) (b:=γ-3*g) (hclose i) (by
    convert exponential_separation (c:=γ-g) (l:=(L:ℝ)) (by linarith)
      (Nat.cast_nonneg L) hdecay hnoise using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring)
  have hclose' : ‖(A e).product-(A i).product‖≤δ := by
    rw [norm_sub_rev]; exact hclose i
  have hhi := count_le (A e) (A i) (a:=γ+3*g) (b:=γ+g) hclose' (by
    convert exponential_separation (c:=γ+3*g) (l:=(L:ℝ)) (by linarith)
      (Nat.cast_nonneg L) hdecay hnoise using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring)
  rw [hflo] at hlo
  rw [hfhi] at hhi
  exact RateThreshold.of_sandwich (A i).lam hg hlo hhi

end SmoothObstruction.ShortBin

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Exact identification of the diagonal-gauge propagator with the derivative
of the genuine nonautonomous chart expression. No product identity is assumed. -/
lemma actual_gauge_product (S : Diffeomorph I I M M ∞) (a : ℕ → M)
    (x : M) {N : ℕ} {K : ℝ} (A : ShortBin.Gauge d N K)
    (hchart : ∀ t≤N,S^[t] x∈(chartAt H (a t)).source)
    (hint : I.IsInteriorPoint x)
    (hEq : ∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S (a t) (a (t+1)) (S^[t] x))*A.U t=
        A.U (t+1)*EuclideanSplitting.rate A.lam 1) :
    fderiv ℝ (ShortDerivative.iterate (fun t => localMap I S (a t) (a (t+1))) N)
      ((extChartAt I (a 0)) x)=A.product := by
  let F := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
  let D (t : ℕ) := coord I S (a t) (a (t+1)) (S^[t] x)
  let f (t : ℕ) := localMap I S (a t) (a (t+1))
  let X (t : ℕ) := (extChartAt I (a t)) (S^[t] x)
  have hi : ∀ t,I.IsInteriorPoint (S^[t] x) := by
    intro t
    induction t with
    | zero => exact hint
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ((S.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp ih
  have hx : ∀ t<N,f t (X t)=X (t+1) := by
    intro t ht
    simpa only [f,X,Function.iterate_succ_apply'] using
      localMap_coordinates I S (a t) (a (t+1)) (S^[t] x) (hchart t ht.le)
  have hd : ∀ t<N,HasFDerivAt (f t) (D t) (X t) := by
    intro t ht
    apply hasFDerivAt_localMap
    · refine ⟨hchart t ht.le,?_⟩
      simpa only [Set.mem_preimage,Function.iterate_succ_apply'] using hchart (t+1) (by omega)
    · exact (interior_coord I _ _ (hchart t ht.le)).mpr (hi t)
  have hder := (ShortDerivative.derivative_iterate f X D N hx hd).fderiv
  have hp : ∀ l,F (EuclideanSplitting.propagator (fun t => F.symm (D t)) 0 l)=
      RelativeProduct.segment D 0 l := by
    intro l
    induction l with
    | zero => simp only [EuclideanSplitting.propagator,RelativeProduct.segment_zero,map_one]
    | succ l ih =>
      simp only [EuclideanSplitting.propagator,RelativeProduct.segment_succ,Nat.zero_add,
        map_mul,StarAlgEquiv.apply_symm_apply,ih]
  have ht := EuclideanSplitting.propagator_eq_transition (fun t => F.symm (D t))
    A.U A.V A.lam A.UV A.VU N hEq 0 N (by omega)
  rw [←hp N,ht] at hder
  simpa only [f,X,Function.iterate_zero_apply,Nat.zero_add,ShortBin.Gauge.product,F] using hder
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.DirectedProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma reverse_directed (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V) {ε : ℝ} (hε0 : 0≤ε) (hε : ε ≤ 1/2)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) (y : V) :
    ‖(y:E)-U.starProjection y‖ ≤ 2*ε*‖y‖ := by
  let e := equiv U V hdim hε h
  let x := e.symm y
  have hxy : V.starProjection x=(y:E) := by
    have hh := congrArg (fun v : V => (v:E)) (e.apply_symm_apply y)
    exact hh
  have hn : ‖x‖ ≤ 2*‖y‖ := by
    have hh := lower U V hε h x
    change ‖x‖ ≤ 2*‖V.starProjection x‖ at hh
    rwa [hxy] at hh
  calc
    ‖(y:E)-U.starProjection y‖ ≤ ‖(y:E)-x‖ := by
      rw [Submodule.starProjection_minimal]
      exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ x
    _ = ‖(x:E)-V.starProjection x‖ := by rw [hxy,norm_sub_rev]
    _ ≤ ε*‖x‖ := h x
    _ ≤ ε*(2*‖y‖) := mul_le_mul_of_nonneg_left hn hε0
    _ = _ := by ring

lemma one_sided_norm (U V : Submodule ℝ E) {ε : ℝ} (hε : 0≤ε)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) :
    ‖(1-V.starProjection)*U.starProjection‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro x
  change ‖U.starProjection x-V.starProjection (U.starProjection x)‖ ≤ ε*‖x‖
  exact (h (U.orthogonalProjectionOnto x)).trans
    (mul_le_mul_of_nonneg_left (U.norm_starProjection_apply_le x) hε)

/-- A directed subspace estimate and equality of dimensions imply a full
projector-distance bound. No chosen singular-vector continuity is assumed. -/
theorem projector_distance (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V) {ε : ℝ} (hε0 : 0≤ε) (hε : ε ≤ 1/2)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) :
    ‖U.starProjection-V.starProjection‖ ≤ 3*ε := by
  have hA := one_sided_norm U V hε0 h
  have hB := one_sided_norm V U (by positivity : 0≤2*ε)
    (reverse_directed U V hdim hε0 hε h)
  have he : U.starProjection-V.starProjection =
      (1-V.starProjection)*U.starProjection-star ((1-U.starProjection)*V.starProjection) := by
    rw [star_mul,star_sub,star_one,(isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq]
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(1-V.starProjection)*U.starProjection‖+
        ‖star ((1-U.starProjection)*V.starProjection)‖ := norm_sub_le _ _
    _ = ‖(1-V.starProjection)*U.starProjection‖+
        ‖(1-U.starProjection)*V.starProjection‖ := by
      congr 1
      exact ContinuousLinearMap.adjoint.norm_map _
    _ ≤ ε+2*ε := add_le_add hA hB
    _ = _ := by ring

end SmoothObstruction.DirectedProjection

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d L : ℕ} {K : ℝ}

lemma Gauge.complement_mem (A : Gauge d L K) (S : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    x-Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V Sᶜ 0) x∈A.space S := by
  have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ =>
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) M x) (projection_compl A.U A.V A.UV S 0)
  rw [map_add,_root_.add_apply,map_one] at he
  change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V S 0) x+
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V Sᶜ 0) x=x at he
  rw [←eq_sub_iff_add_eq.mpr he]
  apply (groupSpace_fixed _ _ _ _ _ _).mpr
  change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V S 0)
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V S 0) x)=_
  rw [←mul_apply_eq_comp,←map_mul,projection_idem A.U A.V A.VU]

/-- Actual short-product control of the slow subspace. The inverse fast
propagator is constructed, rather than supplied as a desired estimate. -/
lemma slow_directed (A B : Gauge d L K) (S T : Finset (Fin d)) {γ g δ : ℝ}
    (hclose : ‖A.product-B.product‖≤δ)
    (hAf : ∀ j∈Sᶜ,γ+g≤A.lam j) (hBs : ∀ j∈T,B.lam j≤γ-g) :
    ∀ x : B.space T, ‖(x:EuclideanSpace ℝ (Fin d))-(A.space S).starProjection x‖ ≤
      Real.exp (-(γ+g)*L+2*K)*(Real.exp ((γ-g)*L+2*K)+δ)*‖x‖ := by
  let J := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
    (transition A.U A.V A.lam L 0*projection A.U A.V Sᶜ L)
  let P := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V Sᶜ 0)
  have hJP : J.comp A.product=P := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
      (transition A.U A.V A.lam L 0*projection A.U A.V Sᶜ L)*
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition A.U A.V A.lam 0 L)=_
    rw [←map_mul,inverse_fast_product A.U A.V A.UV A.VU]
  have hJ : ‖J‖≤Real.exp (-(γ+g)*L+2*K) := by
    dsimp only [J]
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    simpa only [Nat.cast_zero,sub_zero] using
      norm_backward_projection A.U A.V A.VU A.lam Sᶜ 0 L (Nat.zero_le L)
        (A.normU 0 (Nat.zero_le L)) (A.normV L le_rfl) hAf
  exact SubspaceComparison.directed_of_product A.product B.product J P (B.space T) (A.space S)
    (Real.exp_nonneg _) hJP hJ hclose (B.upper T hBs) (A.complement_mem S)

lemma slow_projector_distance (A B : Gauge d L K) (S T : Finset (Fin d))
    {γ g δ : ℝ} (hdim : S.card=T.card)
    (hclose : ‖A.product-B.product‖≤δ)
    (hAf : ∀ j∈Sᶜ,γ+g≤A.lam j) (hBs : ∀ j∈T,B.lam j≤γ-g)
    (hδ : 0≤δ)
    (hsmall : Real.exp (-(γ+g)*L+2*K)*(Real.exp ((γ-g)*L+2*K)+δ)≤1/2) :
    ‖(B.space T).starProjection-(A.space S).starProjection‖ ≤
      3*(Real.exp (-(γ+g)*L+2*K)*(Real.exp ((γ-g)*L+2*K)+δ)) := by
  apply DirectedProjection.projector_distance _ _
    (by rw [A.rank,B.rank,hdim]) (by positivity) hsmall
  exact slow_directed A B S T hclose hAf hBs

end SmoothObstruction.ShortBin

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d L : ℕ} {K : ℝ}

/-- A simultaneous fixed threshold and two common reference subspaces for
all two-sided finite gauges in a bin. The two backward gauges are compared
through their actual products, not through continuity of frame choices. -/
theorem common_splittings {ι : Type*} (A Z : ι → Gauge d L K) (e : ι)
    {g δ : ℝ} (hg : 0<g) (hδ : 0≤δ)
    (hforward : ∀ i,‖(A i).product-(A e).product‖≤δ)
    (hbackward : ∀ i,‖(Z i).product-(Z e).product‖≤δ)
    (hU : ∀ i,(Z i).U 0=(A i).U 0) (hV : ∀ i,(Z i).V 0=(A i).V 0)
    (hlam : ∀ i k,(Z i).lam k= -(A i).lam k)
    (hdecay : Real.exp (-2*g*L+4*K)≤1/2)
    (hnoise : δ<Real.exp (-2*K)/2)
    (hsmall : Real.exp (-2*g*L+4*K)+δ*Real.exp ((1+8*(d:ℝ))*g*L+2*K)≤1/2) :
    ∃ j : Fin (d+1), let γ := (1+8*(j.val:ℝ))*g
      (∀ i,(∀ k,(A i).lam k<γ-g ∨ γ+g<(A i).lam k) ∧
        (Finset.univ.filter (fun k => γ<(A i).lam k)).card=
          (Finset.univ.filter (fun k => γ<(A e).lam k)).card) ∧
      let ε := Real.exp (-2*g*L+4*K)+δ*Real.exp ((1+8*(d:ℝ))*g*L+2*K)
      (∀ i,‖((A i).space (Finset.univ.filter (fun k => (A i).lam k≤γ))).starProjection-
        ((A e).space (Finset.univ.filter (fun k => (A e).lam k≤γ))).starProjection‖≤3*ε) ∧
      ∀ i,‖((A i).space (Finset.univ.filter (fun k => γ<(A i).lam k))).starProjection-
        ((A e).space (Finset.univ.filter (fun k => γ<(A e).lam k))).starProjection‖≤3*ε := by
  classical
  obtain ⟨j,hj⟩ := common_gap A e hg hforward hdecay hnoise
  refine ⟨j,hj,?_⟩
  let γ := (1+8*(j.val:ℝ))*g
  let Γ := (1+8*(d:ℝ))*g
  let ε := Real.exp (-2*g*L+4*K)+δ*Real.exp (Γ*L+2*K)
  let slow (i : ι) := Finset.univ.filter (fun k => (A i).lam k≤γ)
  let fast (i : ι) := Finset.univ.filter (fun k => γ<(A i).lam k)
  have hγ : g≤γ ∧ γ≤Γ := by
    have hval : (j.val:ℝ)≤d := by exact_mod_cast (show j.val≤d by omega)
    dsimp [γ,Γ]
    constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) j.val]
  have hf (i : ι) (k : Fin d) (hk : k∈fast i) : γ+g≤(A i).lam k := by
    have hh : γ<(A i).lam k := by simpa only [fast,Finset.mem_filter,Finset.mem_univ,true_and] using hk
    rcases (hj i).1 k with h | h <;> linarith
  have hs (i : ι) (k : Fin d) (hk : k∈slow i) : (A i).lam k≤γ-g := by
    have hh : (A i).lam k≤γ := by simpa only [slow,Finset.mem_filter,Finset.mem_univ,true_and] using hk
    rcases (hj i).1 k with h | h <;> linarith
  have hsc (i : ι) : (slow i)ᶜ=fast i := by ext k; simp [slow,fast]
  have hfc (i : ι) : (fast i)ᶜ=slow i := by ext k; simp [slow,fast]
  have hfdim (i : ι) : (fast e).card=(fast i).card := (hj i).2.symm
  have hsdim (i : ι) : (slow e).card=(slow i).card := by
    rw [←hfc e,←hfc i,Finset.card_compl,Finset.card_compl,hfdim i]
  have hbound (a : ℝ) (ha : a≤Γ) :
      Real.exp (a*L+2*K)*(Real.exp ((-2*g-a)*L+2*K)+δ)≤ε := by
    rw [mul_add,←Real.exp_add]
    have hE : a*(L:ℝ)+2*K+((-2*g-a)*L+2*K)= -2*g*L+4*K := by ring
    rw [hE]
    change Real.exp (-2*g*L+4*K)+Real.exp (a*L+2*K)*δ ≤
      Real.exp (-2*g*L+4*K)+δ*Real.exp (Γ*L+2*K)
    apply add_le_add (le_refl _)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hδ
    apply Real.exp_le_exp.mpr
    exact add_le_add (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg L)) (le_refl _)
  have hp : Real.exp (-(γ+g)*L+2*K)*(Real.exp ((γ-g)*L+2*K)+δ)≤ε := by
    have heq : -2*g- (-(γ+g))=γ-g := by ring
    simpa only [heq] using hbound (-(γ+g)) (by linarith)
  have hm : Real.exp ((γ-g)*L+2*K)*(Real.exp ((-γ-g)*L+2*K)+δ)≤ε := by
    have heq : -2*g-(γ-g)= -γ-g := by ring
    simpa only [heq] using hbound (γ-g) (by linarith)
  have hZ (i : ι) (S : Finset (Fin d)) : (Z i).space S=(A i).space S := by
    simp only [Gauge.space,hU,hV]
  constructor
  · intro i
    apply (slow_projector_distance (A e) (A i) (slow e) (slow i) (hsdim i)
      (by rw [norm_sub_rev]; exact hforward i)
      (by rw [hsc]; exact hf e) (hs i) hδ (hp.trans hsmall)).trans
    exact mul_le_mul_of_nonneg_left hp (by norm_num)
  · intro i
    have hneg : -(-γ+g)=γ-g := by ring
    have ht := slow_projector_distance (Z e) (Z i) (fast e) (fast i)
      (γ:=-γ) (g:=g) (δ:=δ) (hfdim i)
      (by rw [norm_sub_rev]; exact hbackward i)
      (by intro k hk; rw [hlam]; have hh := hs e k (hfc e ▸ hk); linarith)
      (by intro k hk; rw [hlam]; have hh := hf i k hk; linarith) hδ
      (by simpa only [hneg] using hm.trans hsmall)
    rw [hZ i,hZ e,hneg] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hm (by norm_num))
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

lemma mem_of_coord_mem_carrier (a y : M) {U : Set M}
    (hy : y∈(chartAt H a).source) (hu : (extChartAt I a) y∈carrier I a U) : y∈U := by
  have hh := hu.2
  change (extChartAt I a).symm ((extChartAt I a) y)∈U at hh
  rwa [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hy)] at hh

/-- Compact charts provide a uniform positive COORDINATE margin for any
specified finite open enlargement, also in half-space models. -/
theorem uniform_margin {ι : Type*} [Fintype ι] (a : ι → M) (K U : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hU : ∀ i,IsOpen (U i))
    (hKU : ∀ i,K i⊆U i) (hKs : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ δ : ℝ,0<δ ∧ ∀ i x,x∈K i → ∀ y,y∈(chartAt H (a i)).source →
      ‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖≤δ → y∈U i := by
  let L (i : ι) := (extChartAt I (a i)) '' K i
  have hL (i : ι) : IsCompact (L i) :=
    (hK i).image_of_continuousOn ((continuousOn_extChartAt (I:=I) (a i)).mono
      (fun _ hx => by simpa only [extChartAt_source] using hKs i hx))
  have hex (i : ι) : ∃ r : ℝ,0 < r ∧ cthickening r (L i)⊆carrier I (a i) (U i) := by
    apply (hL i).exists_cthickening_subset_open (isOpen_carrier I _ (hU i))
    rintro z ⟨x,hx,rfl⟩
    exact coord_mem_carrier I _ _ (hKs i hx) (hKU i hx)
  choose r hr hu using hex
  obtain ⟨δ,hδ,hδr⟩ := CarriedCharts.finite_positive_lower r hr
  refine ⟨δ,hδ,fun i x hx y hy hxy => ?_⟩
  apply mem_of_coord_mem_carrier I _ _ hy
  apply hu i
  apply closedBall_subset_cthickening (E:=L i) ⟨x,hx,rfl⟩ (r i)
  simpa only [mem_closedBall,dist_eq_norm] using hxy.trans (hδr i)

end SmoothObstruction.CoordinateTubes

namespace SmoothObstruction.CoordinateTubes
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]

/-- In a compatible metric, the same coordinate margin puts nearby
carried points in any prescribed geometric atlas tube. -/
theorem uniform_metric_tube {ι : Type*} [Fintype ι]
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKs : ∀ i,K i⊆(chartAt H (a i)).source) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ,0<δ ∧ ∀ i x,x∈K i → ∀ y,y∈(chartAt H (a i)).source →
      ‖(extChartAt I (a i)) y-(extChartAt I (a i)) x‖≤δ →
        y∈cthickening r (K i) := by
  obtain ⟨δ,hδ,hh⟩ := uniform_margin I a K (fun i => thickening r (K i)) hK
    (fun i => isOpen_thickening) (fun i => self_subset_thickening hr _) hKs
  exact ⟨δ,hδ,fun i x hx y hy hxy => thickening_subset_cthickening r _ (hh i x hx y hy hxy)⟩
end SmoothObstruction.CoordinateTubes

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

omit [ProperSpace M] in
/-- Strengthen actual short comparison by a prescribed uniform atlas tube.
Membership of the nearby orbit at ALL intermediate times is a conclusion. -/
theorem actual_tube_comparison (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {τ : ℝ} (hτ : 0<τ) :
    ∃ r C : ℝ,0 < r ∧ 1≤C ∧ ∀ (c : ℕ → ι) (x y : M) (N : ℕ),
      (∀ t≤N,S^[t] x∈K (c t)) → I.IsInteriorPoint x → I.IsInteriorPoint y →
      y∈(chartAt H (a (c 0))).source →
      C ^ N*‖(extChartAt I (a (c 0))) y-(extChartAt I (a (c 0))) x‖ ≤ r →
      (∀ t≤N,S^[t] y∈(chartAt H (a (c t))).source ∧
        S^[t] y∈cthickening τ (K (c t))) ∧
      ‖fderiv ℝ (ShortDerivative.iterate (fun t => localMap I S (a (c t)) (a (c (t+1)))) N)
          ((extChartAt I (a (c 0))) y)-
        fderiv ℝ (ShortDerivative.iterate (fun t => localMap I S (a (c t)) (a (c (t+1)))) N)
          ((extChartAt I (a (c 0))) x)‖≤
          N*C*C ^ (2*N)*‖(extChartAt I (a (c 0))) y-(extChartAt I (a (c 0))) x‖ := by
  obtain ⟨r,C,hr,hC,hh⟩ := actual_short_comparison I hclosed S a K hK hKU
  obtain ⟨δ,hδ,hmargin⟩ := CoordinateTubes.uniform_metric_tube I a K hK hKU hτ
  refine ⟨min r δ,C,lt_min hr hδ,hC,fun c x y N hx hxi hyi hys hsmall => ?_⟩
  obtain ⟨ht,hd⟩ := hh c x y N hx hxi hyi hys (hsmall.trans (min_le_left _ _))
  refine ⟨fun t htn => ⟨(ht t htn).1,?_⟩,hd⟩
  apply hmargin (c t) (S^[t] x) (hx t htn) _ (ht t htn).1
  apply (ht t htn).2.trans
  apply le_trans _ (hsmall.trans (min_le_right _ _))
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC htn) (norm_nonneg _)

/-- Genuine good-path gauges can be attached simultaneously to the two
reference chart codes of a nearby orbit. No continued chart membership,
frame continuity, or derivative comparison is an extra hypothesis. -/
theorem uniform_genuine_bin_gauges (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF rB CB D : ℝ,0 < rF ∧ 1≤CF ∧ 0 < rB ∧ 1≤CB ∧ 1≤D ∧
      ∀ (c : M → ι) (J : Type*) (x : J → M) (e : J) (cF cB : ℕ → ι)
        (n N : ℕ) (B R h : ℝ) (A : ∀ i,BilateralGauge I S a c n B R (x i)),
        (∀ y,y∈K (c y)) → N≤n → cB 0=cF 0 →
        (∀ t≤N,S^[t] (x e)∈K (cF t)) →
        (∀ t≤N,S.symm^[t] (x e)∈K (cB t)) →
        (∀ i,I.IsInteriorPoint (x i)) →
        (∀ i,x i∈(chartAt H (a (cF 0))).source) →
        (∀ i,‖(extChartAt I (a (cF 0))) (x i)-(extChartAt I (a (cF 0))) (x e)‖≤h) →
        CF^N*h ≤ rF → CB^N*h ≤ rB →
        ∃ F Z : J → ShortBin.Gauge d N (B+Real.log D),
          (∀ i k,(F i).lam k=(A i).lam k ∧ (Z i).lam k= -(A i).lam k) ∧
          (∀ i,(Z i).U 0=(F i).U 0 ∧ (Z i).V 0=(F i).V 0) ∧
          (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S (a (cF t)) (a (cF (t+1))) (S^[t] (x i)))*(F i).U t=
              (F i).U (t+1)*EuclideanSplitting.rate (F i).lam 1) ∧
          (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S.symm (a (cB t)) (a (cB (t+1))) (S.symm^[t] (x i)))*(Z i).U t=
              (Z i).U (t+1)*EuclideanSplitting.rate (Z i).lam 1) ∧
          (∀ i,‖(F i).product-(F e).product‖≤N*CF*CF^(2*N)*h) ∧
          (∀ i,‖(Z i).product-(Z e).product‖≤N*CB*CB^(2*N)*h) ∧
          ∀ i t,t≤N →
            (F i).U t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (c (S^[t] (x i)))) (a (cF t)) (S^[t] (x i)))*(A i).UF t ∧
            (F i).V t=(A i).VF t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (cF t)) (a (c (S^[t] (x i)))) (S^[t] (x i))) ∧
            (Z i).U t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (c (S.symm^[t] (x i)))) (a (cB t)) (S.symm^[t] (x i)))*(A i).UB t ∧
            (Z i).V t=(A i).VB t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (cB t)) (a (c (S.symm^[t] (x i)))) (S.symm^[t] (x i))) := by
  classical
  obtain ⟨τ,D,hτ,hD,hcarry⟩ := uniform_carried_bilateral_explicit I a K hK hKU
  obtain ⟨rF,CF,hrF,hCF,hhF⟩ := actual_tube_comparison I hclosed S a K hK hKU hτ
  obtain ⟨rB,CB,hrB,hCB,hhB⟩ := actual_tube_comparison I hclosed S.symm a K hK hKU hτ
  refine ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,
    fun c J x e cF cB n N B R h A hc hN h0 hxF hxB hint hsource hdist hsF hsB => ?_⟩
  have hdistB (i : J) : ‖(extChartAt I (a (cB 0))) (x i)-(extChartAt I (a (cB 0))) (x e)‖≤h := by
    simpa only [h0] using hdist i
  have hsourceB (i : J) : x i∈(chartAt H (a (cB 0))).source := by
    simpa only [h0] using hsource i
  have htF (i : J) := hhF cF (x e) (x i) N hxF (hint e) (hint i) (hsource i)
    ((mul_le_mul_of_nonneg_left (hdist i) (pow_nonneg (zero_le_one.trans hCF) N)).trans hsF)
  have htB (i : J) := hhB cB (x e) (x i) N hxB (hint e) (hint i) (hsourceB i)
    ((mul_le_mul_of_nonneg_left (hdistB i) (pow_nonneg (zero_le_one.trans hCB) N)).trans hsB)
  choose F Z hFlam hZlam hU hV hstepF hstepB hform using fun i =>
    hcarry S c (x i) N B R ((A i).restrict I S a c hN) cF cB hc h0
      (fun t ht => ((htF i).1 t ht).2) (fun t ht => ((htB i).1 t ht).2)
  refine ⟨F,Z,fun i k => ⟨hFlam i k,hZlam i k⟩,fun i => ⟨hU i,hV i⟩,hstepF,hstepB,?_,?_,?_⟩
  · intro i
    have hp (j : J) := actual_gauge_product I S (fun t => a (cF t)) (x j) (F j)
      (fun t ht => ((htF j).1 t ht).1) (hint j) (hstepF j)
    rw [←hp i,←hp e]
    exact ((htF i).2).trans (mul_le_mul_of_nonneg_left (hdist i) (by positivity))
  · intro i
    have hp (j : J) := actual_gauge_product I S.symm (fun t => a (cB t)) (x j) (Z j)
      (fun t ht => ((htB j).1 t ht).1) (hint j) (hstepB j)
    rw [←hp i,←hp e]
    exact ((htB i).2).trans (mul_le_mul_of_nonneg_left (hdistB i) (by positivity))
  · exact hform
end SmoothObstruction.ManifoldCoordinates

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

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- A one-sided family of actual gauges can be carried to reference charts
using only the short orbit interval. This is also applicable at a long-window
endpoint, without demanding good data beyond that endpoint. -/
theorem uniform_genuine_single_gauges (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C₁ D : ℝ,0 < r ∧ 1≤C₁ ∧ 1≤D ∧
      ∀ (c : M → ι) (J : Type*) (x : J → M) (e : J) (cR : ℕ → ι)
        (N : ℕ) (B h : ℝ) (A : J → ShortBin.Gauge d N B),
        (∀ y,y∈K (c y)) →
        (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (c (S^[t] (x i)))) (a (c (S^[t+1] (x i)))) (S^[t] (x i)))*(A i).U t=
            (A i).U (t+1)*EuclideanSplitting.rate (A i).lam 1) →
        (∀ t≤N,S^[t] (x e)∈K (cR t)) →
        (∀ i,I.IsInteriorPoint (x i)) →
        (∀ i,x i∈(chartAt H (a (cR 0))).source) →
        (∀ i,‖(extChartAt I (a (cR 0))) (x i)-(extChartAt I (a (cR 0))) (x e)‖≤h) →
        C₁^N*h ≤ r →
        ∃ F : J → ShortBin.Gauge d N (B+Real.log D),
          (∀ i,(F i).lam=(A i).lam) ∧
          (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I S (a (cR t)) (a (cR (t+1))) (S^[t] (x i)))*(F i).U t=
              (F i).U (t+1)*EuclideanSplitting.rate (F i).lam 1) ∧
          (∀ i,‖(F i).product-(F e).product‖≤N*C₁*C₁^(2*N)*h) ∧
          ∀ i t,t≤N →
            (F i).U t=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (c (S^[t] (x i)))) (a (cR t)) (S^[t] (x i)))*(A i).U t ∧
            (F i).V t=(A i).V t*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (cR t)) (a (c (S^[t] (x i)))) (S^[t] (x i))) := by
  classical
  obtain ⟨τ,D,hτ,hD,hcarry⟩ := uniform_carried_gauge_explicit I a K hK hKU
  obtain ⟨r,C₁,hr,hC,hh⟩ := actual_tube_comparison I hclosed S a K hK hKU hτ
  refine ⟨r,C₁,D,hr,hC,hD,fun c J x e cR N B h A hc hA hx hint hsource hdist hs => ?_⟩
  have ht (i : J) := hh cR (x e) (x i) N hx (hint e) (hint i) (hsource i)
    ((mul_le_mul_of_nonneg_left (hdist i) (pow_nonneg (zero_le_one.trans hC) N)).trans hs)
  have hc' (i : J) (t : ℕ) (_ht : t≤N) :
      S^[t] (x i)∈cthickening τ (K (c (S^[t] (x i)))) := self_subset_cthickening _ (hc _)
  choose PF QF hiF hbF hform hstep using fun i =>
    hcarry S (fun t => S^[t] (x i)) (fun t => c (S^[t] (x i))) cR
      (A i).U (A i).V (A i).lam N B (hc' i) (fun t ht' => ((ht i).1 t ht').2)
      (fun t _ => (Function.iterate_succ_apply' _ _ _).symm)
      (fun t => ⟨(A i).UV t,(A i).VU t⟩)
      (fun t ht' => ⟨(A i).normU t ht',(A i).normV t ht'⟩) (hA i)
  have hbound : D*Real.exp B=Real.exp (B+Real.log D) := by
    rw [Real.exp_add,Real.exp_log (lt_of_lt_of_le zero_lt_one hD),mul_comm]
  have hb (i : J) (t : ℕ) (ht : t≤N) :
      ‖PF i t‖≤Real.exp (B+Real.log D) ∧ ‖QF i t‖≤Real.exp (B+Real.log D) := by
    simpa only [hbound] using hbF i t ht
  let F (i : J) := ShortBin.Gauge.ofFinite (PF i) (QF i) (A i).lam (hiF i) (hb i)
  have hstep' (i : J) (t : ℕ) (ht : t<N) :
      (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
        (coord I S (a (cR t)) (a (cR (t+1))) (S^[t] (x i)))*(F i).U t=
          (F i).U (t+1)*EuclideanSplitting.rate (F i).lam 1 := by
    simpa only [F,ShortBin.Gauge.ofFinite,Nat.min_eq_left ht.le,
      Nat.min_eq_left (show t+1≤N by omega)] using hstep i t ht
  refine ⟨F,fun _ => rfl,hstep',?_,?_⟩
  · intro i
    have hp (j : J) := actual_gauge_product I S (fun t => a (cR t)) (x j) (F j)
      (fun t ht' => ((ht j).1 t ht').1) (hint j) (hstep' j)
    rw [←hp i,←hp e]
    exact ((ht i).2).trans (mul_le_mul_of_nonneg_left (hdist i) (by positivity))
  · intro i t ht'
    simpa only [F,ShortBin.Gauge.ofFinite,Nat.min_eq_left ht'] using hform i t

omit [ProperSpace M] [Fintype ι] in
lemma BilateralGauge.endpointBackward_step (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) (hc : ∀ y,y∈(chartAt H (a (c y))).source)
    {n N : ℕ} {B R : ℝ} {x : M} (A : BilateralGauge I S a c n B R x) (hN : N≤n) :
    let F := A.endpointBackward I S a c (N:=N)
    ∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S.symm (a (c (S.symm^[t] (S^[n] x))))
        (a (c (S.symm^[t+1] (S^[n] x)))) (S.symm^[t] (S^[n] x)))*F.U t=
      F.U (t+1)*EuclideanSplitting.rate F.lam 1 := by
  intro F t ht
  have hr (s : ℕ) (hs : s≤n) : S.symm^[s] (S^[n] x)=S^[n-s] x :=
    OrbitCocycle.backward_center S.toHomeomorph x hs
  rw [hr t (by omega),hr (t+1) (by omega)]
  have he : n-(t+1)+1=n-t := by omega
  have hh := reverse_gauge_step I S (fun j => a (c (S^[j] x)))
    (fun j => S^[j] x) A.UF A.lam (n-(t+1))
    (by simp only [Function.iterate_succ_apply']) (hc _) (hc _)
    (A.stepF _ (by omega))
  simpa only [he,F,BilateralGauge.endpointBackward] using hh
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Quantitative endpoint comparison at a FIXED starting threshold, for all
actual witnesses reaching one endpoint bin. Only the past short segment is
used at the forward endpoint. The displayed basis identities attach the
comparison to the actual long-window spaces. -/
theorem uniform_endpoint_fast_comparison (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C₁ D : ℝ,0 < r ∧ 1≤C₁ ∧ 1≤D ∧
      ∀ (c : M → ι) (J : Type*) (x : J → M) (e : J) (cR : ℕ → ι)
        (n N : ℕ) (B R h γ g : ℝ) (T : J → Finset (Fin d))
        (A : ∀ i,BilateralGauge I S a c n B R (x i)),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ t≤N,S.symm^[t] (S^[n] (x e))∈K (cR t)) →
        (∀ i,I.IsInteriorPoint (S^[n] (x i))) →
        (∀ i,S^[n] (x i)∈(chartAt H (a (cR 0))).source) →
        (∀ i,‖(extChartAt I (a (cR 0))) (S^[n] (x i))-
          (extChartAt I (a (cR 0))) (S^[n] (x e))‖≤h) →
        C₁^N*h ≤ r → 0≤h →
        (∀ i,(T e).card=(T i).card) →
        (∀ i,∀ j∈(T i)ᶜ,(A i).lam j≤γ-g) →
        (∀ i,∀ j∈T i,γ+g≤(A i).lam j) →
        (let ε := Real.exp ((γ-g)*N+2*(B+Real.log D))*
          (Real.exp ((-γ-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)
        ε≤1/2) →
        ∃ F : J → ShortBin.Gauge d N (B+Real.log D),
          (∀ i j,(F i).lam j= -(A i).lam j) ∧
          (∀ i,(F i).U 0=(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (coord I (Diffeomorph.refl I M ∞) (a (c (S^[n] (x i))))
              (a (cR 0)) (S^[n] (x i)))*(A i).UF n ∧
            (F i).V 0=(A i).VF n*(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
              (coord I (Diffeomorph.refl I M ∞) (a (cR 0))
                (a (c (S^[n] (x i)))) (S^[n] (x i)))) ∧
          ∀ i,‖((F i).space (T i)).starProjection-((F e).space (T e)).starProjection‖≤
            3*(Real.exp ((γ-g)*N+2*(B+Real.log D))*
              (Real.exp ((-γ-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)) := by
  obtain ⟨r,C₁,D,hr,hC,hD,hh⟩ := uniform_genuine_single_gauges I hclosed S.symm a K hK hKU
  refine ⟨r,C₁,D,hr,hC,hD,fun c J x e cR n N B R h γ g T A hc hN hx hint
    hsource hdist ht hn hdim hslow hfast hsmall => ?_⟩
  obtain ⟨F,hlam,hstep,hprod,hform⟩ := hh c J (fun i => S^[n] (x i)) e cR N B h
    (fun i => (A i).endpointBackward I S a c) hc
    (fun i => (A i).endpointBackward_step I S a c (fun y => hKU _ (hc y)) hN)
    hx hint hsource hdist ht
  have hlam' (i : J) (j : Fin d) : (F i).lam j= -(A i).lam j := congrFun (hlam i) j
  refine ⟨F,hlam',?_,?_⟩
  · intro i
    simpa only [Function.iterate_zero_apply,BilateralGauge.endpointBackward,Nat.sub_zero]
      using hform i 0 (Nat.zero_le N)
  · intro i
    have he : -(-γ+g)=γ-g := by ring
    have hs : Real.exp (-(-γ+g)*N+2*(B+Real.log D))*
        (Real.exp ((-γ-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)≤1/2 := by
      simpa only [he] using hsmall
    have hp : ‖(F e).product-(F i).product‖≤N*C₁*C₁^(2*N)*h := by
      rw [norm_sub_rev]
      exact hprod i
    have hcl := ShortBin.slow_projector_distance (F e) (F i) (T e) (T i) (γ := -γ)
      (hdim i) hp
      (by intro j hj; rw [hlam']; linarith [hslow e j hj])
      (by intro j hj; rw [hlam']; linarith [hfast i j hj]) (by positivity) hs
    simpa only [he] using hcl
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ExteriorPowers
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped ContDiff BigOperators
open Module

namespace SmoothObstruction.ExteriorStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Exterior powers depend smoothly on the input operator. -/
theorem contDiff_exterior (p : ℕ) :
    ContDiff ℝ ∞ (exterior (E := E) p) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  have hv : v ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ p (M := E))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, rfl⟩ := hv
    simp only [exterior_apply, exteriorPower.map_apply_ιMulti]
    apply (contDiff_wedge p).comp
    exact contDiff_pi.mpr fun i => contDiff_id.clm_apply contDiff_const
  | zero => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : E →L[ℝ] E => (0 : ⋀[ℝ]^p E)))
  | add x y hx hy ihx ihy => simpa only [map_add] using ihx.add ihy
  | smul a x hx ih => simpa only [map_smul] using ih.const_smul a

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exterior_smul (p : ℕ) (c : ℝ) (A : E →L[ℝ] E) :
    exterior p (c • A)=c^p • exterior p A := by
  apply ContinuousLinearMap.coe_injective
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorPower.map p (c • A).toLinearMap (exteriorPower.ιMulti ℝ p v) =
    c^p • exteriorPower.map p A.toLinearMap (exteriorPower.ιMulti ℝ p v)
  simp only [exteriorPower.map_apply_ιMulti,Function.comp_def,
    ContinuousLinearMap.coe_coe,smul_apply]
  simpa using (exteriorPower.ιMulti ℝ p (M:=E)).map_smul_univ (fun _ => c) (fun i => A (v i))

/-- A fixed dimensional polynomial bound sufficient to absorb changes of
gauge into the source's exp(Cbn) factor, with exterior degree zero included. -/
theorem exists_power_bound (p : ℕ) : ∃ C : ℝ,1≤C ∧ ∀ A : E →L[ℝ] E,
    ‖exterior p A‖≤C*(max 1 ‖A‖)^p := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) 1).exists_bound_of_continuousOn
    (f:=exterior (E:=E) p) (contDiff_exterior p).continuous.continuousOn
  refine ⟨max C 1,le_max_right _ _,?_⟩
  intro A
  let r := max 1 ‖A‖
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hAr : ‖r⁻¹ • A‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).mpr (by simpa only [mul_one] using le_max_right (1:ℝ) ‖A‖)
  have ha := hC (r⁻¹ • A) (by simpa only [mem_closedBall,dist_zero_right] using hAr)
  have he : A=r • (r⁻¹ • A) := by rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  calc
    _ = ‖r^p • exterior p (r⁻¹ • A)‖ := by
      congr 1
      conv_lhs => rw [he,exterior_smul]
    _ ≤ r^p*‖exterior p (r⁻¹ • A)‖ := by
      simpa only [Real.norm_eq_abs,abs_of_pos (pow_pos hr p)] using
        ContinuousLinearMap.opNorm_smul_le (r^p) (exterior p (r⁻¹ • A))
    _ ≤ r^p*(max C 1) := mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (pow_nonneg hr.le p)
    _ = _ := by ring

end SmoothObstruction.ExteriorStability

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

/-- The source floor forces the gap×short-time scale to infinity. This is
`g L ≥ b^(3/4)n` for `g = sqrt b`, `L = ceil(b^(1/4)n)`. -/
lemma gap_scale_lower {b n : ℝ} (hn : 1≤n) (hb : n^(-1/10:ℝ)≤b) :
    n^(37/40:ℝ)≤b^(3/4:ℝ)*n := by
  have hnpos : 0<n := by linarith
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _) hb
    (show (0:ℝ)≤3/4 by norm_num)
  rw [←Real.rpow_mul hnpos.le] at hh
  calc
    n^(37/40:ℝ) = n^((-1/10:ℝ)*(3/4)+1) := by norm_num
    _ = n^((-1/10:ℝ)*(3/4))*n := by rw [Real.rpow_add hnpos,Real.rpow_one]
    _ ≤ b^(3/4:ℝ)*n := mul_le_mul_of_nonneg_right hh hnpos.le

/-- All fixed exponential gauge losses are absorbed by the genuine spectral
gap×short-time exponent. Neither the gap nor the rates need be bounded away
from zero. -/
theorem gap_cost_absorption {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop)
    (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => Real.exp (C*b k*n k-c*b k^(3/4:ℝ)*n k)) l (𝓝 0) := by
  have hn1 : ∀ᶠ k in l,1≤n k := hn.eventually (eventually_ge_atTop 1)
  have hP : Tendsto (fun k => b k^(3/4:ℝ)*n k) l atTop := by
    apply tendsto_atTop_mono' l ?_
      ((tendsto_rpow_atTop (show (0:ℝ)<37/40 by norm_num)).comp hn)
    filter_upwards [hn1,hfloor] with k hnk hbk
    exact gap_scale_lower hnk hbk
  have hquarter : Tendsto (fun k => b k^(1/4:ℝ)) l (𝓝 0) := by
    have hh := ((Real.continuous_rpow_const (show (0:ℝ)≤1/4 by norm_num)).tendsto 0).comp hb
    simpa only [Function.comp_def,Real.zero_rpow (show (1/4:ℝ)≠0 by norm_num)] using hh
  have hs : ∀ᶠ k in l,C*b k^(1/4:ℝ) ≤ c/2 := by
    apply Tendsto.eventually_le_const (show (0:ℝ) < c/2 by linarith)
    simpa only [mul_zero] using hquarter.const_mul C
  have hzero := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hP.const_mul_atTop (show 0 < c/2 by linarith))
  apply squeeze_zero' _ _ hzero
  · exact Filter.Eventually.of_forall fun k => (Real.exp_pos _).le
  · filter_upwards [hbpos,hn1,hs] with k hbk hnk hsk
    apply Real.exp_le_exp.mpr
    have hbseq : b k^(1/4:ℝ)*b k^(3/4:ℝ)=b k := by
      rw [←Real.rpow_add hbk]
      norm_num
    have hh := mul_le_mul_of_nonneg_right hsk
      (show 0≤b k^(3/4:ℝ)*n k from mul_nonneg (Real.rpow_nonneg hbk.le _) (by linarith))
    have he : (C*b k^(1/4:ℝ))*(b k^(3/4:ℝ)*n k)=C*b k*n k := by
      calc
        _ = C*(b k^(1/4:ℝ)*b k^(3/4:ℝ))*n k := by ring
        _ = _ := by rw [hbseq]
    rw [he] at hh
    nlinarith
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.SmoothScales
open Filter Topology
/-- Uniform exponentially small common-projector errors absorb every fixed
gauge cost. This is the form needed by the finite leading-minor lower bound. -/
theorem weighted_gap_error {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {c A : ℝ} (hc : 0 < c) (hA : 0≤A) (C : ℝ)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤Real.exp (-c*b k^(3/4:ℝ)*n k)) :
    Tendsto (fun k => A*Real.exp (C*b k*n k)*δ k) l (𝓝 0) := by
  have hz := (gap_cost_absorption hbpos hb hn hfloor C hc).const_mul A
  simp only [mul_zero] at hz
  apply squeeze_zero' _ _ hz
  · filter_upwards [hδ] with k hk
    exact mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) hk.1
  · filter_upwards [hδ] with k hk
    calc
      _ ≤ A*Real.exp (C*b k*n k)*Real.exp (-c*b k^(3/4:ℝ)*n k) :=
        mul_le_mul_of_nonneg_left hk.2 (mul_nonneg hA (Real.exp_pos _).le)
      _ = A*Real.exp (C*b k*n k-c*b k^(3/4:ℝ)*n k) := by
        rw [mul_assoc,←Real.exp_add]
        congr 2
        ring
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.SmoothScales
open Filter Topology

/-- The literal dimension/gauge cost in the common-fast leading-minor
proof is eventually small. Its parameters are fixed before bins and frames
are selected, and the good-frame error has the source gap×short-time scale. -/
theorem common_frame_budget {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {c F C N : ℝ} (hc : 0 < c) (hF : 0≤F) (hN : 0≤N)
    (K₀ : ℝ) (p : ℕ)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤Real.exp (-c*b k^(3/4:ℝ)*n k)) :
    ∀ᶠ k in l,
      (F*δ k)*(1+((C*(Real.exp (K₀*b k*n k))^p)^2*(C*2^p))*
        (C*(C^2*(Real.exp (K₀*b k*n k))^(2*p)*N)))≤1/2 := by
  have hz₁ := weighted_gap_error hbpos hb hn hfloor hc hF 0 hδ
  have hz₂ := weighted_gap_error hbpos hb hn hfloor hc
    (show 0≤F*C^6*2^p*N by positivity) ((4*p:ℕ)*K₀) hδ
  have hz := hz₁.add hz₂
  simp only [add_zero] at hz
  have he (k : α) :
      (F*δ k)*(1+((C*(Real.exp (K₀*b k*n k))^p)^2*(C*2^p))*
        (C*(C^2*(Real.exp (K₀*b k*n k))^(2*p)*N)))=
      F*Real.exp (0*b k*n k)*δ k+
        (F*C^6*2^p*N)*Real.exp (((4*p:ℕ):ℝ)*K₀*b k*n k)*δ k := by
    have hexp : Real.exp (((4*p:ℕ):ℝ)*K₀*b k*n k)=
        (Real.exp (K₀*b k*n k))^(4*p) := by
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    simp only [zero_mul,Real.exp_zero,mul_one,Nat.mul_comm 2 p,Nat.mul_comm 4 p,pow_mul]
    ring
  have hh : Tendsto (fun k =>
      (F*δ k)*(1+((C*(Real.exp (K₀*b k*n k))^p)^2*(C*2^p))*
        (C*(C^2*(Real.exp (K₀*b k*n k))^(2*p)*N)))) l (𝓝 0) := by
    apply hz.congr
    intro k
    exact (he k).symm
  exact hh.eventually_le_const (by norm_num : (0:ℝ)<1/2)
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.SmoothScales
open Filter Topology

/-- The full-time gap dominates the short-time gap scale and every fixed
gauge cost. No uniform positive lower bound on the spectral gap is assumed. -/
theorem weighted_full_gap {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {c A : ℝ} (hc : 0 < c) (hA : 0≤A) (C : ℝ) :
    Tendsto (fun k => A*Real.exp (C*b k*n k)*
      Real.exp (-c*b k^(1/2:ℝ)*n k)) l (𝓝 0) := by
  apply weighted_gap_error hbpos hb hn hfloor hc hA C
  have hb1 := hb.eventually_le_const (by norm_num : (0:ℝ)<1)
  have hn0 := hn.eventually (eventually_ge_atTop 0)
  filter_upwards [hbpos,hb1,hn0] with k hbk hb1k hnk
  refine ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr ?_⟩
  have hh := Real.rpow_le_rpow_of_exponent_ge hbk hb1k
    (show (1/2:ℝ)≤3/4 by norm_num)
  have hp := mul_le_mul_of_nonneg_right hh hnk
  nlinarith

/-- The literal finite-gauge Cramer bound tends to zero, uniformly over
all common bins satisfying the same scalar data. Fixed constants account
for the dimension, endpoint projections and unit wedge norms. -/
theorem common_graph_budget {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {c C N V W : ℝ} (hc : 0 < c) (hN : 0≤N)
    (hV : 0≤V) (hW : 0≤W) (K₀ : ℝ) (p : ℕ)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤Real.exp (-c*b k^(3/4:ℝ)*n k)) :
    Tendsto (fun k =>
      2*((C*(Real.exp (K₀*b k*n k))^p)^2*(C*2^p))*
        ((C*(C*(Real.exp (K₀*b k*n k))^p)^2*N*V)*
            Real.exp (-2*b k^(1/2:ℝ)*n k)+
         (C*(C^2*(Real.exp (K₀*b k*n k))^(2*p)*N))*W*δ k)) l (𝓝 0) := by
  have hz₁ := weighted_full_gap hbpos hb hn hfloor
    (by norm_num : (0:ℝ)<2) (show 0≤2*C^6*2^p*N*V by positivity) ((4*p:ℕ)*K₀)
  have hz₂ := weighted_gap_error hbpos hb hn hfloor hc
    (show 0≤2*C^6*2^p*N*W by positivity) ((4*p:ℕ)*K₀) hδ
  have hz := hz₁.add hz₂
  simp only [add_zero] at hz
  apply hz.congr
  intro k
  have hexp : Real.exp (((4*p:ℕ):ℝ)*K₀*b k*n k)=
      (Real.exp (K₀*b k*n k))^(4*p) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  simp only [Nat.mul_comm 2 p,Nat.mul_comm 4 p,pow_mul]
  ring

/-- Relative nonlinear errors preserve the vanishing Cramer bound. -/
theorem perturbed_graph_decay {α : Type*} {l : Filter α} {θ ε : α → ℝ}
    (hθ : Tendsto θ l (𝓝 0)) (hε : Tendsto ε l (𝓝 0)) :
    Tendsto (fun k => (θ k+ε k)/(1-ε k)) l (𝓝 0) := by
  have hh := (hθ.add hε).div (tendsto_const_nhds.sub hε)
    (by norm_num : (1:ℝ)-0≠0)
  change Tendsto (fun k => (θ k+ε k)/(1-ε k)) l (𝓝 ((0+0)/(1-0))) at hh
  norm_num at hh
  exact hh
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.SmoothScales

lemma positive {b : ℝ} (hb : 0 < b) : 0 < B b := Real.rpow_pos_of_pos hb _

lemma ratio {b : ℝ} (hb : 0 < b) : b / B b = b ^ (7 / 8 : ℝ) := by
  calc
    b / B b = b ^ (1 : ℝ) / b ^ (1 / 8 : ℝ) := by simp [B]
    _ = b ^ ((1 : ℝ) - 1 / 8) := (Real.rpow_sub hb _ _).symm
    _ = b ^ (7 / 8 : ℝ) := by norm_num

lemma lower_bound {b n : ℝ} (hn : 1 ≤ n) (hb : n ^ (-1 / 10 : ℝ) ≤ b) :
    n ^ (79 / 80 : ℝ) ≤ B b * n := by
  have hnpos : 0 < n := by linarith
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _) hb (show (0 : ℝ) ≤ 1 / 8 by norm_num)
  rw [← Real.rpow_mul hnpos.le] at h
  have h' := mul_le_mul_of_nonneg_right h hnpos.le
  calc
    n ^ (79 / 80 : ℝ) = n ^ ((-1 / 10 : ℝ) * (1 / 8)) * n := by
      calc
        n ^ (79 / 80 : ℝ) = n ^ ((-1 / 10 : ℝ) * (1 / 8) + 1) := by norm_num
        _ = n ^ ((-1 / 10 : ℝ) * (1 / 8)) * n := by rw [Real.rpow_add hnpos, Real.rpow_one]
    _ ≤ B b * n := h'

lemma square_dominates {b n : ℝ} (hn : 1 ≤ n) (hb : n ^ (-1 / 10 : ℝ) ≤ b) :
    n ≤ (B b * n)^2 := by
  have hl := lower_bound hn hb
  have hpos : 0 ≤ n ^ (79 / 80 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc
    n = n ^ (1 : ℝ) := by simp
    _ ≤ n ^ ((79 / 80 : ℝ) * 2) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    _ = (n ^ (79 / 80 : ℝ))^2 := by rw [Real.rpow_mul (by linarith), Real.rpow_two]
    _ ≤ (B b * n)^2 := pow_le_pow_left₀ hpos hl 2

lemma ratio_tendsto_zero {α : Type*} {l : Filter α} {b : α → ℝ}
    (hbpos : ∀ᶠ k in l, 0 < b k) (hb : Tendsto b l (𝓝 0)) :
    Tendsto (fun k => b k / B (b k)) l (𝓝 0) := by
  have h := ((Real.continuous_rpow_const (show (0 : ℝ) ≤ 7 / 8 by norm_num)).tendsto 0).comp hb
  simp only [Real.zero_rpow (show (7 / 8 : ℝ) ≠ 0 by norm_num)] at h
  apply h.congr'
  filter_upwards [hbpos] with k hk
  exact (ratio hk).symm

/-- Quantitative exponential decay used in the relative-minor transfer. It
holds for every fixed real coefficient `C`, including all constants coming
from the dimension, charts, and inverse basis bounds. -/
theorem decisive_decay {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l, 0 < b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop)
    (hfloor : ∀ᶠ k in l, n k ^ (-1 / 10 : ℝ) ≤ b k) (C : ℝ) :
    Tendsto (fun k => n k * Real.exp (-(3 / 2 : ℝ) * B (b k) * n k + C * b k * n k))
      l (𝓝 0) := by
  have hn1 : ∀ᶠ k in l, 1 ≤ n k := hn.eventually (eventually_ge_atTop 1)
  have hsmall : ∀ᶠ k in l, C * (b k / B (b k)) ≤ 1 / 2 := by
    apply Tendsto.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num)
    simpa using (ratio_tendsto_zero hbpos hb).const_mul C
  have hBn : Tendsto (fun k => B (b k) * n k) l atTop := by
    apply tendsto_atTop_mono' l ?_ ((tendsto_rpow_atTop (show (0 : ℝ) < 79 / 80 by norm_num)).comp hn)
    filter_upwards [hn1, hfloor] with k hk hbf
    exact lower_bound hk hbf
  have hzero := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hBn
  apply squeeze_zero' _ _ hzero
  · filter_upwards [hn1] with k hk
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  · filter_upwards [hn1, hfloor, hbpos, hsmall] with k hnk hfk hbk hsk
    have hB := positive hbk
    have hCB : C * b k ≤ B (b k) / 2 := by
      have hh := (div_le_iff₀ hB).mp (show C * b k / B (b k) ≤ 1 / 2 by simpa [mul_div_assoc] using hsk)
      linarith
    have hexp : -(3 / 2 : ℝ) * B (b k) * n k + C * b k * n k ≤ -(B (b k) * n k) := by
      have := mul_le_mul_of_nonneg_right hCB (show 0 ≤ n k by linarith)
      nlinarith
    exact mul_le_mul (square_dominates hnk hfk) (Real.exp_le_exp.mpr hexp)
      (Real.exp_pos _).le (sq_nonneg _)
end SmoothObstruction.SmoothScales

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

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma one_le_frameWedgeConstant (p : ℕ) : 1≤frameWedgeConstant (E:=E) p :=
  (exists_common_frame_wedge_control (E:=E) p).choose_spec.1

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma one_le_unitWedgeConstant (p : ℕ) : 1≤unitWedgeConstant (E:=E) p := le_max_right _ _

end SmoothObstruction.ExteriorStability

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
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

omit [ProperSpace M] in
lemma coord_refl_same (a x : M) (hx : x∈(chartAt H a).source) :
    coord I (Diffeomorph.refl I M ∞) a a x=1 := by
  rw [←chartChange_coe I a a x hx hx]
  ext v
  simp [chartChange]

/-- The common-bin spaces now belong to the ORIGINAL good bilateral gauges.
All carried intermediate charts have disappeared from the conclusion. Only
initial coarse-bin coordinates are used, so no orbit-code partition appears. -/
theorem uniform_genuine_bin_splitting (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF rB CB D : ℝ,0 < rF ∧ 1 ≤ CF ∧ 0 < rB ∧ 1 ≤ CB ∧ 1 ≤ D ∧
      ∀ (c : M → ι) (J : Type*) (x : J → M) (e : J)
        (n N : ℕ) (B R h g : ℝ) (A : ∀ i,BilateralGauge I S a c n B R (x i)),
        (∀ y,y∈K (c y)) → N ≤ n → (∀ i,c (x i)=c (x e)) →
        (∀ i,I.IsInteriorPoint (x i)) →
        (∀ i,‖(extChartAt I (a (c (x e)))) (x i)-
          (extChartAt I (a (c (x e)))) (x e)‖ ≤ h) →
        CF^N*h ≤ rF → CB^N*h ≤ rB → 0 < g →
        Real.exp (-2*g*N+4*(B+Real.log D)) ≤ 1/2 →
        let δ := ((N:ℝ)*CF*CF^(2*N)+N*CB*CB^(2*N))*h
        δ < Real.exp (-2*(B+Real.log D))/2 →
        Real.exp (-2*g*N+4*(B+Real.log D))+
          δ*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D)) ≤ 1/2 →
        ∃ j : Fin (d+1), let γ := (1+8*(j.val:ℝ))*g
          (∀ i,(∀ k,(A i).lam k < γ-g ∨ γ+g < (A i).lam k) ∧
            (Finset.univ.filter (fun k => γ < (A i).lam k)).card=
              (Finset.univ.filter (fun k => γ < (A e).lam k)).card) ∧
          let ε := Real.exp (-2*g*N+4*(B+Real.log D))+
            δ*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))
          (∀ i,‖(((A i).forward I S a c).space (Finset.univ.filter (fun k => (A i).lam k ≤ γ))).starProjection-
            (((A e).forward I S a c).space (Finset.univ.filter (fun k => (A e).lam k ≤ γ))).starProjection‖ ≤ 3*ε) ∧
          ∀ i,‖(((A i).forward I S a c).space (Finset.univ.filter (fun k => γ < (A i).lam k))).starProjection-
            (((A e).forward I S a c).space (Finset.univ.filter (fun k => γ < (A e).lam k))).starProjection‖ ≤ 3*ε := by
  classical
  obtain ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,hh⟩ :=
    uniform_genuine_bin_gauges I hclosed S a K hK hKU
  refine ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,
    fun c J x e n N B R h g A hc hN hcommon hint hdist hsF hsB hg hdecay hnoise hsmall => ?_⟩
  let cF (t : ℕ) := c (S^[t] (x e))
  let cB (t : ℕ) := c (S.symm^[t] (x e))
  have hsource (i : J) : x i∈(chartAt H (a (c (x e)))).source := by
    rw [←hcommon i]
    exact hKU _ (hc _)
  obtain ⟨F,Z,hlam,hcenter,hstepF,hstepB,hprodF,hprodB,hform⟩ :=
    hh c J x e cF cB n N B R h A hc hN rfl
      (fun _ _ => hc _) (fun _ _ => hc _) hint hsource hdist hsF hsB
  have hzero (i : J) : (F i).U 0=(A i).UF 0 ∧ (F i).V 0=(A i).VF 0 := by
    have hh := hform i 0 (Nat.zero_le N)
    have hid := coord_refl_same I (a (c (x e))) (x i) (hsource i)
    have hh' := And.intro hh.1 hh.2.1
    simpa only [cF,Function.iterate_zero_apply,hcommon i,hid,map_one,one_mul,mul_one] using hh'
  have hspace (i : J) (T : Finset (Fin d)) :
      (F i).space T=((A i).forward I S a c).space T := by
    simp only [ShortBin.Gauge.space,BilateralGauge.forward,ShortBin.Gauge.ofFinite,
      Nat.zero_min,(hzero i).1,(hzero i).2]
  have hh0 : 0 ≤ h := (norm_nonneg _).trans (hdist e)
  let δ := ((N:ℝ)*CF*CF^(2*N)+N*CB*CB^(2*N))*h
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hnF : 0 ≤ (N:ℝ)*CF*CF^(2*N)*h := by positivity
  have hnB : 0 ≤ (N:ℝ)*CB*CB^(2*N)*h := by positivity
  have hbF : (N:ℝ)*CF*CF^(2*N)*h ≤ δ := by dsimp [δ]; nlinarith
  have hbB : (N:ℝ)*CB*CB^(2*N)*h ≤ δ := by dsimp [δ]; nlinarith
  obtain ⟨j,hgap,hslow,hfast⟩ := ShortBin.common_splittings F Z e hg hδ
    (fun i => (hprodF i).trans hbF) (fun i => (hprodB i).trans hbB)
    (fun i => (hcenter i).1) (fun i => (hcenter i).2)
    (fun i k => by rw [(hlam i k).2,(hlam i k).1]) hdecay hnoise hsmall
  have hFl (i : J) : (F i).lam=(A i).lam := funext fun k => (hlam i k).1
  refine ⟨j,?_,?_,?_⟩
  · simpa only [hFl] using hgap
  · simpa only [hFl,hspace] using hslow
  · simpa only [hFl,hspace] using hfast
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Endpoint-bin comparison with NO carried basis or extra threshold in the
conclusion. The reference is chosen among original certificates reaching the
same endpoint bin from a fixed starting bin. -/
theorem uniform_original_endpoint_fast_comparison (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C₁ D : ℝ,0 < r ∧ 1≤C₁ ∧ 1≤D ∧
      ∀ (c : M → ι) (J : Type*) (x : J → M) (e : J)
        (n N : ℕ) (B R h γ g : ℝ) (T : J → Finset (Fin d))
        (A : ∀ i,BilateralGauge I S a c n B R (x i)),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ i,c (S^[n] (x i))=c (S^[n] (x e))) →
        (∀ i,I.IsInteriorPoint (S^[n] (x i))) →
        (∀ i,‖(extChartAt I (a (c (S^[n] (x e))))) (S^[n] (x i))-
          (extChartAt I (a (c (S^[n] (x e))))) (S^[n] (x e))‖≤h) →
        C₁^N*h ≤ r → 0≤h →
        (∀ i,(T e).card=(T i).card) →
        (∀ i,∀ j∈(T i)ᶜ,(A i).lam j≤γ-g) →
        (∀ i,∀ j∈T i,γ+g≤(A i).lam j) →
        (let ε := Real.exp ((γ-g)*N+2*(B+Real.log D))*
          (Real.exp ((-γ-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)
        ε≤1/2) →
        ∀ i,‖(A i |>.forwardSpace I S a c n (T i)).starProjection-
          (A e |>.forwardSpace I S a c n (T e)).starProjection‖≤
            3*(Real.exp ((γ-g)*N+2*(B+Real.log D))*
              (Real.exp ((-γ-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)) := by
  obtain ⟨r,C₁,D,hr,hC,hD,hh⟩ :=
    uniform_endpoint_fast_comparison I hclosed S a K hK hKU
  refine ⟨r,C₁,D,hr,hC,hD,fun c J x e n N B R h γ g T A hc hN hcommon
    hint hdist ht hn hdim hslow hfast hsmall => ?_⟩
  let cR (t : ℕ) := c (S.symm^[t] (S^[n] (x e)))
  have hsource (i : J) : S^[n] (x i)∈(chartAt H (a (cR 0))).source := by
    change S^[n] (x i)∈(chartAt H (a (c (S^[n] (x e))))).source
    rw [←hcommon i]
    exact hKU _ (hc _)
  obtain ⟨F,hlam,hform,hclose⟩ := hh c J x e cR n N B R h γ g T A hc hN
    (fun _ _ => hc _) hint hsource hdist ht hn hdim hslow hfast hsmall
  have hzero (i : J) : (F i).U 0=(A i).UF n ∧ (F i).V 0=(A i).VF n := by
    have hid := coord_refl_same I (a (cR 0)) (S^[n] (x i)) (hsource i)
    have hc0 : c (S^[n] (x i))=cR 0 := hcommon i
    simpa only [hc0,hid,map_one,one_mul,mul_one] using hform i
  have hspace (i : J) : (F i).space (T i)=(A i).forwardSpace I S a c n (T i) := by
    simp only [ShortBin.Gauge.space,BilateralGauge.forwardSpace,(hzero i).1,(hzero i).2]
  intro i
  simpa only [hspace] using hclose i
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
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι C : Type*} [Fintype ι]

lemma slowSet_eq_compl (v : Fin d → ℝ) (γ : ℝ) : slowSet v γ=(fastSet v γ)ᶜ := by
  classical
  ext j
  simp only [fastSet,slowSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl,not_lt]

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
theorem finite_starting_references_uniform (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF rB CB D : ℝ,0 < rF ∧ 1≤CF ∧ 0 < rB ∧ 1≤CB ∧ 1≤D ∧
      ∀ (C : Type*) (c : M → ι) (P : M → C) (G : Set M)
        (n N : ℕ) (B R h g : ℝ) (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint x) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        CF^N*h ≤ rF → CB^N*h ≤ rB → 0<g →
        Real.exp (-2*g*N+4*(B+Real.log D))≤1/2 →
        (let δ := ((N:ℝ)*CF*CF^(2*N)+N*CB*CB^(2*N))*h
         δ<Real.exp (-2*(B+Real.log D))/2 ∧
         Real.exp (-2*g*N+4*(B+Real.log D))+
           δ*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))≤1/2) →
        ∃ j : Active P G → Fin (d+1),∀ Q : Active P G,
          let x₀ : G := (reference P G Q).val
          let γ := (1+8*((j Q).val:ℝ))*g
          let ε := Real.exp (-2*g*N+4*(B+Real.log D))+
            (((N:ℝ)*CF*CF^(2*N)+N*CB*CB^(2*N))*h)*
              Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))
          ∀ x:G,P x=Q.val →
            (∀ k,(A x).lam k<γ-g ∨ γ+g<(A x).lam k) ∧
            (Finset.univ.filter (fun k => γ<(A x).lam k)).card=
              (Finset.univ.filter (fun k => γ<(A x₀).lam k)).card ∧
            ‖(((A x).forward I S a c).space (Finset.univ.filter (fun k => (A x).lam k≤γ))).starProjection-
              (((A x₀).forward I S a c).space (Finset.univ.filter (fun k => (A x₀).lam k≤γ))).starProjection‖≤3*ε ∧
            ‖(((A x).forward I S a c).space (Finset.univ.filter (fun k => γ<(A x).lam k))).starProjection-
              (((A x₀).forward I S a c).space (Finset.univ.filter (fun k => γ<(A x₀).lam k))).starProjection‖≤3*ε := by
  classical
  obtain ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,hh⟩ :=
    uniform_genuine_bin_splitting I hclosed S a K hK hKU
  refine ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,?_⟩
  intro C c P G n N B R h g A hc hN hco hint hdiam hsF hsB hg hdec hsmall
  have hex (Q : Active P G) := hh c (Fiber P G Q) (fun x => x.val.val)
    (reference P G Q) n N B R h g (fun x => A x.val) hc hN
    (fun x => hco _ _ (x.property.trans (reference P G Q).property.symm))
    (fun x => hint _ x.val.property)
    (fun x => hdiam _ _ (x.property.trans (reference P G Q).property.symm))
    hsF hsB hg hdec hsmall.1 hsmall.2
  choose j hj using hex
  refine ⟨j,?_⟩
  intro Q x₀ γ ε x hx
  have hgx := (hj Q).1 (⟨x,hx⟩ : Fiber P G Q)
  exact ⟨hgx.1,hgx.2,(hj Q).2.1 ⟨x,hx⟩,(hj Q).2.2 ⟨x,hx⟩⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
theorem finite_endpoint_references_uniform (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C₁ D : ℝ,0 < r ∧ 1≤C₁ ∧ 1≤D ∧
      ∀ (C : Type*) (c : M → ι) (P : M → C) (G : Set M) (n N : ℕ) (B R h g : ℝ)
        (γ : C → ℝ) (T : G → Finset (Fin d))
        (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint (S^[n] x)) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        C₁^N*h ≤ r → 0≤h →
        (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (∀ q : C,let ε := Real.exp ((γ q-g)*N+2*(B+Real.log D))*
          (Real.exp ((-γ q-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)
          ε≤1/2) →
        let EKey := fun x => (P x,P (S^[n] x))
        ∃ W : Active EKey G → Submodule ℝ (EuclideanSpace ℝ (Fin d)),
          ∀ Q : Active EKey G,∀ x:G,EKey x=Q.val →
            Module.finrank ℝ (W Q)=(T x).card ∧
            ‖((A x).forwardSpace I S a c n (T x)).starProjection-(W Q).starProjection‖≤
              3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log D))*
                (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)) := by
  classical
  obtain ⟨r,C₁,D,hr,hC,hD,hh⟩ := uniform_original_endpoint_fast_comparison I hclosed S a K hK hKU
  refine ⟨r,C₁,D,hr,hC,hD,?_⟩
  intro C c P G n N B R h g γ T A hc hN hco hint hdiam ht hn hdim hslow hfast hsmall EKey
  let ref (Q : Active EKey G) : G := (reference EKey G Q).val
  let W (Q : Active EKey G) := (A (ref Q)).forwardSpace I S a c n (T (ref Q))
  refine ⟨W,?_⟩
  intro Q x hx
  have hp (y : Fiber EKey G Q) : EKey y.val=EKey (ref Q) :=
    y.property.trans (reference EKey G Q).property.symm
  have hq (y : Fiber EKey G Q) : P y.val=P (ref Q) := congrArg Prod.fst (hp y)
  have hend (y : Fiber EKey G Q) : P (S^[n] y.val.val)=P (S^[n] (ref Q).val) :=
    congrArg Prod.snd (hp y)
  have he : P x=P (ref Q) := hq ⟨x,hx⟩
  constructor
  · exact (EuclideanSplitting.finrank_groupSpace ((A (ref Q)).UF n)
      ((A (ref Q)).VF n) ((A (ref Q)).invF n).1 ((A (ref Q)).invF n).2
      (T (ref Q))).trans (hdim _ _ he.symm)
  · have hb := hh c (Fiber EKey G Q) (fun y => y.val.val) (reference EKey G Q)
      n N B R h (γ (P (ref Q))) g (fun y => T y.val) (fun y => A y.val)
      hc hN (fun y => hco _ _ (hend y)) (fun y => hint _ y.val.property)
      (fun y => hdiam _ _ (hend y)) ht hn (fun y => hdim _ _ (hq y).symm)
      (fun y j hj => by simpa only [←hq y] using hslow y.val j hj)
      (fun y j hj => by simpa only [←hq y] using hfast y.val j hj)
      (hsmall (P (ref Q))) (⟨x,hx⟩ : Fiber EKey G Q)
    simpa only [W,ref,he] using hb
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
theorem bilateral_endpoint_references_uniform (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF DF rB CB DB : ℝ,0 < rF ∧ 1≤CF ∧ 1≤DF ∧ 0 < rB ∧ 1≤CB ∧ 1≤DB ∧
      ∀ (C : Type*) (c : M → ι) (P : M → C) (G : Set M) (n N : ℕ) (B R h g : ℝ)
        (γ : C → ℝ) (T : G → Finset (Fin d))
        (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint (S^[n] x) ∧ I.IsInteriorPoint (S.symm^[n] x)) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        CF^N*h ≤ rF → CB^N*h ≤ rB → 0≤h →
        (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (∀ q : C,Real.exp ((γ q-g)*N+2*(B+Real.log DF))*
          (Real.exp ((-γ q-g)*N+2*(B+Real.log DF))+N*CF*CF^(2*N)*h)≤1/2) →
        (∀ q : C,Real.exp ((-γ q-g)*N+2*(B+Real.log DB))*
          (Real.exp ((γ q-g)*N+2*(B+Real.log DB))+N*CB*CB^(2*N)*h)≤1/2) →
        ∃ Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d)),∀ x:G,
          Module.finrank ℝ (Wf (P x,P (S^[n] x)))=(T x).card ∧
          Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-(T x).card ∧
          ‖((A x).forwardSpace I S a c n (T x)).starProjection-
            (Wf (P x,P (S^[n] x))).starProjection‖≤
              3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log DF))*
                (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log DF))+N*CF*CF^(2*N)*h)) ∧
          ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n] x))).starProjection‖≤
              3*(Real.exp ((-γ (P x)-g)*N+2*(B+Real.log DB))*
                (Real.exp ((γ (P x)-g)*N+2*(B+Real.log DB))+N*CB*CB^(2*N)*h)) := by
  classical
  obtain ⟨rF,CF,DF,hrF,hCF,hDF,hF⟩ := finite_endpoint_references_uniform I hclosed S a K hK hKU
  obtain ⟨rB,CB,DB,hrB,hCB,hDB,hB⟩ := finite_endpoint_references_uniform I hclosed S.symm a K hK hKU
  refine ⟨rF,CF,DF,rB,CB,DB,hrF,hCF,hDF,hrB,hCB,hDB,?_⟩
  intro C c P G n N B R h g γ T A hc hN hco hint hdiam htF htB hh hcard hslow hfast hsmallF hsmallB
  obtain ⟨WF,hWF⟩ := hF C c P G n N B R h g γ T A hc hN hco
    (fun x hx => (hint x hx).1) hdiam htF hh hcard hslow hfast hsmallF
  have hcardB (x y : G) (hxy : P x=P y) : (T x)ᶜ.card=(T y)ᶜ.card := by
    simp only [Finset.card_compl,Fintype.card_fin,hcard x y hxy]
  have hsB (x : G) (j : Fin d) (hj : j∈((T x)ᶜ)ᶜ) :
      -((A x).lam j)≤(-γ (P x))-g := by
    simp only [compl_compl] at hj
    linarith [hfast x j hj]
  have hfB (x : G) (j : Fin d) (hj : j∈(T x)ᶜ) :
      (-γ (P x))+g≤-((A x).lam j) := by linarith [hslow x j hj]
  obtain ⟨WB,hWB⟩ := hB C c P G n N B R h g (fun q => -γ q) (fun x => (T x)ᶜ)
    (fun x => (A x).reverse I S a c) hc hN hco (fun x hx => (hint x hx).2)
    hdiam htB hh hcardB hsB hfB (by simpa only [neg_neg] using hsmallB)
  let PF (x : M) := (P x,P (S^[n] x))
  let PB (x : M) := (P x,P (S.symm^[n] x))
  refine ⟨extend PF G WF ⊥,extend PB G WB ⊥,?_⟩
  intro x
  have hFx := hWF (key PF G x) x rfl
  have hBx := hWB (key PB G x) x rfl
  have eF := extend_key PF G WF (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) x
  have eB := extend_key PB G WB (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) x
  dsimp only [PF,PB] at eF eB hFx hBx ⊢
  rw [eF,eB]
  refine ⟨hFx.1,?_,hFx.2,?_⟩
  · simpa only [Finset.card_compl,Fintype.card_fin] using hBx.1
  · simpa only [BilateralGauge.reverse_forwardSpace,neg_neg] using hBx.2
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
theorem finite_references_uniform (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r₁ C₁ r₂ C₂ D r₃ C₃ D₃ r₄ C₄ D₄ : ℝ,
      0 < r₁ ∧ 1≤C₁ ∧ 0 < r₂ ∧ 1≤C₂ ∧ 1≤D ∧
      0 < r₃ ∧ 1≤C₃ ∧ 1≤D₃ ∧ 0 < r₄ ∧ 1≤C₄ ∧ 1≤D₄ ∧
      ∀ (C : Type*) (c : M → ι) (P : M → C) (G : Set M) (n N : ℕ) (B R h g : ℝ)
        (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint x) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        C₁^N*h ≤ r₁ → C₂^N*h ≤ r₂ → C₃^N*h ≤ r₃ → C₄^N*h ≤ r₄ → 0≤h → 0<g →
        Real.exp (-2*g*N+4*(B+Real.log D))≤1/2 →
        (let δ := ((N:ℝ)*C₁*C₁^(2*N)+N*C₂*C₂^(2*N))*h
         δ<Real.exp (-2*(B+Real.log D))/2 ∧
         Real.exp (-2*g*N+4*(B+Real.log D))+
           δ*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))≤1/2) →
        (∀ j : Fin (d+1),let γ := (1+8*(j.val:ℝ))*g
          Real.exp ((γ-g)*N+2*(B+Real.log D₃))*
            (Real.exp ((-γ-g)*N+2*(B+Real.log D₃))+N*C₃*C₃^(2*N)*h)≤1/2) →
        (∀ j : Fin (d+1),let γ := (1+8*(j.val:ℝ))*g
          Real.exp ((-γ-g)*N+2*(B+Real.log D₄))*
            (Real.exp ((γ-g)*N+2*(B+Real.log D₄))+N*C₄*C₄^(2*N)*h)≤1/2) →
        ∃ j : C → Fin (d+1),
          let γ (q : C) := (1+8*((j q).val:ℝ))*g
          let T (x : G) := fastSet (A x).lam (γ (P x))
          let ε := Real.exp (-2*g*N+4*(B+Real.log D))+
            (((N:ℝ)*C₁*C₁^(2*N)+N*C₂*C₂^(2*N))*h)*
              Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))
          ∃ Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d)),
            (∀ x:G,∀ i∈(T x)ᶜ,(A x).lam i≤γ (P x)-g) ∧
            (∀ x:G,∀ i∈T x,γ (P x)+g≤(A x).lam i) ∧
            (∀ x y:G,P x=P y → (T x).card=(T y).card) ∧
            (∀ x:G,let y : G := (reference P G (key P G x)).val
              ‖(((A x).forward I S a c).space (T x)ᶜ).starProjection-
                (((A y).forward I S a c).space (T y)ᶜ).starProjection‖≤3*ε ∧
              ‖(((A x).forward I S a c).space (T x)).starProjection-
                (((A y).forward I S a c).space (T y)).starProjection‖≤3*ε) ∧
            ∀ x:G,
              Module.finrank ℝ (Wf (P x,P (S^[n] x)))=(T x).card ∧
              Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-(T x).card ∧
              ‖((A x).forwardSpace I S a c n (T x)).starProjection-
                (Wf (P x,P (S^[n] x))).starProjection‖≤
                  3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log D₃))*
                    (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D₃))+N*C₃*C₃^(2*N)*h)) ∧
              ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
                (Wb (P x,P (S.symm^[n] x))).starProjection‖≤
                  3*(Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D₄))*
                    (Real.exp ((γ (P x)-g)*N+2*(B+Real.log D₄))+N*C₄*C₄^(2*N)*h)) := by
  classical
  obtain ⟨r₁,C₁,r₂,C₂,D,hr₁,hC₁,hr₂,hC₂,hD,hs⟩ :=
    finite_starting_references_uniform I hclosed S a K hK hKU
  obtain ⟨r₃,C₃,D₃,r₄,C₄,D₄,hr₃,hC₃,hD₃,hr₄,hC₄,hD₄,he⟩ :=
    bilateral_endpoint_references_uniform I hclosed S a K hK hKU
  refine ⟨r₁,C₁,r₂,C₂,D,r₃,C₃,D₃,r₄,C₄,D₄,
    hr₁,hC₁,hr₂,hC₂,hD,hr₃,hC₃,hD₃,hr₄,hC₄,hD₄,?_⟩
  intro C c P G n N B R h g A hc hN hco hint hdiam ht₁ ht₂ ht₃ ht₄ hh hg hd hsml hfml hbml
  obtain ⟨j₀,hj₀⟩ := hs C c P G n N B R h g A hc hN hco hint hdiam ht₁ ht₂ hg hd hsml
  let j := FiniteBins.extend P G j₀ (0 : Fin (d+1))
  let γ (q : C) := (1+8*((j q).val:ℝ))*g
  let T (x : G) := fastSet (A x).lam (γ (P x))
  have hj (x : G) : j (P x)=j₀ (key P G x) := extend_key P G j₀ _ x
  have hgap (x : G) (i : Fin d) : (A x).lam i<γ (P x)-g ∨ γ (P x)+g<(A x).lam i := by
    have hh := (hj₀ (key P G x) x rfl).1 i
    simpa only [γ,hj] using hh
  have hsc (x : G) (i : Fin d) (hi : i∈(T x)ᶜ) : (A x).lam i≤γ (P x)-g := by
    have hl : (A x).lam i≤γ (P x) := by simpa only [T,fastSet,Finset.mem_compl,Finset.mem_filter,
      Finset.mem_univ,true_and,not_lt] using hi
    rcases hgap x i with hi | hi
    · exact hi.le
    · linarith
  have hfc (x : G) (i : Fin d) (hi : i∈T x) : γ (P x)+g≤(A x).lam i := by
    have hl : γ (P x)<(A x).lam i := by simpa only [T,fastSet,Finset.mem_filter,
      Finset.mem_univ,true_and] using hi
    rcases hgap x i with hi | hi
    · linarith
    · exact hi.le
  have hcard (x y : G) (hxy : P x=P y) : (T x).card=(T y).card := by
    have hx := (hj₀ (key P G x) x rfl).2.1
    have hy := (hj₀ (key P G x) y hxy.symm).2.1
    dsimp only [T,fastSet,γ]
    rw [←hxy,hj x]
    exact hx.trans hy.symm
  have hi (F : Diffeomorph I I M M ∞) (x : M) (hx : I.IsInteriorPoint x) (t : ℕ) :
      I.IsInteriorPoint (F^[t] x) := by
    induction t with
    | zero => exact hx
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ((F.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp ih
  obtain ⟨Wf,Wb,hW⟩ := he C c P G n N B R h g γ T A hc hN hco
    (fun x hx => ⟨hi S x (hint x hx) n,hi S.symm x (hint x hx) n⟩)
    hdiam ht₃ ht₄ hh hcard hsc hfc (fun q => hfml (j q)) (fun q => hbml (j q))
  refine ⟨j,Wf,Wb,hsc,hfc,hcard,?_,hW⟩
  intro x y
  have hy : P y=P x := (reference P G (key P G x)).property
  have hxs := (hj₀ (key P G x) x rfl).2.2
  dsimp only [T]
  rw [←slowSet_eq_compl,←slowSet_eq_compl]
  simpa only [γ,hy,hj x,slowSet,fastSet] using hxs
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

lemma sum_norm_sq (v : EuclideanSpace ℝ (ι ⊕ κ)) :
    ‖(EuclideanSpace.sumEquivProd v).1‖^2+‖(EuclideanSpace.sumEquivProd v).2‖^2=‖v‖^2 := by
  have hh := WithLp.prod_norm_sq_eq_of_L2 ((PiLp.sumPiLpEquivProdLpPiLp (𝕜:=ℝ) 2 (fun _ : ι ⊕ κ => ℝ)) v)
  rw [LinearIsometryEquiv.norm_map] at hh
  exact hh.symm

/-- The source's basis consists of orthonormal columns within each summand.
Its forward norm is uniformly bounded even when the angle is small. -/
lemma norm_blockMap (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V) :
    ‖(blockMap U V h bU bV).toContinuousLinearMap‖≤Real.sqrt 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  rw [ContinuousLinearEquiv.coe_coe,blockMap_apply]
  apply (norm_add_le _ _).trans
  change ‖bU.repr.symm (EuclideanSpace.sumEquivProd v).1‖+
    ‖bV.repr.symm (EuclideanSpace.sumEquivProd v).2‖≤_
  rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num)]
  nlinarith [sum_norm_sq v,sq_nonneg (‖(EuclideanSpace.sumEquivProd v).1‖-‖(EuclideanSpace.sumEquivProd v).2‖)]

lemma blockMap_symm_components (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V) (x : E) :
    EuclideanSpace.sumEquivProd ((blockMap U V h bU bV).symm x)=
      (bU.repr (U.projectionOnto V h x),bV.repr (V.projectionOnto U h.symm x)) := by
  change EuclideanSpace.sumEquivProd (EuclideanSpace.sumEquivProd.symm
    ((bU.repr.toContinuousLinearEquiv.prodCongr bV.repr.toContinuousLinearEquiv)
      ((U.prodEquivOfIsCompl V h).symm x)))=_
  rw [ContinuousLinearEquiv.apply_symm_apply,Submodule.prodEquivOfIsCompl_symm_apply]
  rfl

/-- Only the inverse pays the complementary-projection condition number. -/
lemma norm_blockMap_symm (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V)
    {H : ℝ} (hH : 0≤H)
    (hU : ∀ x,‖U.projectionOnto V h x‖≤H*‖x‖)
    (hV : ∀ x,‖V.projectionOnto U h.symm x‖≤H*‖x‖) :
    ‖(blockMap U V h bU bV).symm.toContinuousLinearMap‖≤Real.sqrt 2*H := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖(blockMap U V h bU bV).symm x‖^2≤_
  rw [←sum_norm_sq,blockMap_symm_components]
  simp only [LinearIsometryEquiv.norm_map]
  have hu := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hU x)
  have hv := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hV x)
  rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num)]
  nlinarith
end SmoothObstruction.ProductBasis

namespace SmoothObstruction.ProductBasis
open Set
open scoped EuclideanGeometry
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A fixed ambient coordinate alphabet for the orthonormal-within-group
product basis. The rank may vary from bin to bin without being charged as an
orbit code. Even rank-zero groups retain the exact mixing property. -/
theorem exists_coordinates (U V : Submodule ℝ E) (h : IsCompl U V)
    {H : ℝ} (hH : 0≤H)
    (hU : ∀ x,‖U.projectionOnto V h x‖≤H*‖x‖)
    (hV : ∀ x,‖V.projectionOnto U h.symm x‖≤H*‖x‖) :
    ∃ A : E ≃L[ℝ] E,
      ‖A.toContinuousLinearMap‖≤Real.sqrt 2 ∧
      ‖A.symm.toContinuousLinearMap‖≤Real.sqrt 2*H ∧
      ∀ x y : E,∀ i : Fin d,
        (A.symm (x+(U.projectionOnto V h (y-x):E))) i=(A.symm x) i ∨
        (A.symm (x+(U.projectionOnto V h (y-x):E))) i=(A.symm y) i := by
  classical
  let bU := stdOrthonormalBasis ℝ U
  let bV := stdOrthonormalBasis ℝ V
  have hcard : Fintype.card (Fin (Module.finrank ℝ U) ⊕ Fin (Module.finrank ℝ V))=
      Fintype.card (Fin d) := by
    simpa using (Submodule.finrank_add_eq_of_isCompl h)
  let e : (Fin (Module.finrank ℝ U) ⊕ Fin (Module.finrank ℝ V)) ≃ Fin d :=
    Fintype.equivOfCardEq hcard
  let J := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  let A : E ≃L[ℝ] E := J.symm.toContinuousLinearEquiv.trans (blockMap U V h bU bV)
  have hnormJ (x : E) : ‖J.symm x‖=‖x‖ := J.symm.norm_map x
  have hnormA (x : E) : ‖A x‖≤Real.sqrt 2*‖x‖ := by
    exact ((blockMap U V h bU bV).toContinuousLinearMap.le_opNorm (J.symm x)).trans
      (by rw [hnormJ]; exact mul_le_mul_of_nonneg_right (norm_blockMap U V h bU bV) (norm_nonneg _))
  have hnormAi (x : E) : ‖A.symm x‖≤(Real.sqrt 2*H)*‖x‖ := by
    change ‖J ((blockMap U V h bU bV).symm x)‖≤_
    rw [J.norm_map]
    exact ((blockMap U V h bU bV).symm.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (norm_blockMap_symm U V h bU bV hH hU hV) (norm_nonneg _))
  refine ⟨A,ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hnormA,
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) hnormAi,?_⟩
  intro x y i
  have hmix : EuclideanSpace.sumEquivProd ((blockMap U V h bU bV).symm
      (x+(U.projectionOnto V h (y-x):E)))=
      (bU.repr (U.projectionOnto V h y),bV.repr (V.projectionOnto U h.symm x)) := by
    rw [blockMap_symm_components]
    apply Prod.ext
    · change bU.repr (U.projectionOnto V h (x+(U.projectionOnto V h (y-x):E))) = _
      congr 1
      rw [map_add,Submodule.projectionOnto_apply_left,map_sub]
      abel
    · change bV.repr (V.projectionOnto U h.symm (x+(U.projectionOnto V h (y-x):E))) = _
      congr 1
      rw [map_add,Submodule.projectionOnto_apply_right,add_zero]
  have hval (z : E) (j : Fin (Module.finrank ℝ U) ⊕ Fin (Module.finrank ℝ V)) :
      (A.symm z) (e j)=((blockMap U V h bU bV).symm z) j := by
    change (J ((blockMap U V h bU bV).symm z)) (e j)=_
    simp [J,LinearIsometryEquiv.piLpCongrLeft_apply]
  obtain ⟨j,rfl⟩ := e.surjective i
  rw [hval,hval,hval]
  rcases j with j | j
  · right
    have hm := congrArg (fun p => (p.1 : EuclideanSpace ℝ (Fin (Module.finrank ℝ U))) j) hmix
    have hx := congrArg (fun p => (p.1 : EuclideanSpace ℝ (Fin (Module.finrank ℝ U))) j)
      (blockMap_symm_components U V h bU bV y)
    exact hm.trans hx.symm
  · left
    have hm := congrArg (fun p => (p.2 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) j) hmix
    have hx := congrArg (fun p => (p.2 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) j)
      (blockMap_symm_components U V h bU bV x)
    exact hm.trans hx.symm
end SmoothObstruction.ProductBasis

namespace SmoothObstruction.FiniteGreen.Splitting
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T : Evolution E} (B : Splitting T)

lemma range_projection_slow (t : ℕ) (x : E) :
    ((B.slow t).range.projectionOnto (B.fast t).range (B.ranges_isCompl t) x:E)=B.slow t x := by
  have h := B.add_apply t x
  conv_lhs => rw [←h]
  rw [map_add]
  have hs := Submodule.projectionOnto_apply_left (B.ranges_isCompl t)
    (⟨B.slow t x,⟨x,rfl⟩⟩ : (B.slow t).range)
  have hf := Submodule.projectionOnto_apply_right (B.ranges_isCompl t)
    (⟨B.fast t x,⟨x,rfl⟩⟩ : (B.fast t).range)
  rw [hs,hf,add_zero]

lemma range_projection_fast (t : ℕ) (x : E) :
    ((B.fast t).range.projectionOnto (B.slow t).range (B.ranges_isCompl t).symm x:E)=B.fast t x := by
  have h := B.add_apply t x
  conv_lhs => rw [←h]
  rw [map_add]
  have hs := Submodule.projectionOnto_apply_right (B.ranges_isCompl t).symm
    (⟨B.slow t x,⟨x,rfl⟩⟩ : (B.slow t).range)
  have hf := Submodule.projectionOnto_apply_left (B.ranges_isCompl t).symm
    (⟨B.fast t x,⟨x,rfl⟩⟩ : (B.fast t).range)
  rw [hs,hf,zero_add]
end SmoothObstruction.FiniteGreen.Splitting

namespace SmoothObstruction.ProductBasis
open SmoothObstruction.FiniteGreen
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The authentic complementary splitting produces its own uniform product
coordinate map, with the exact slow/fast ideal mix and no rank assumptions. -/
theorem splitting_coordinates {T : Evolution E} (B : Splitting T) (t : ℕ)
    {H : ℝ} (hH : 0≤H) (hs : ‖B.slow t‖≤H) (hf : ‖B.fast t‖≤H) :
    ∃ A : E ≃L[ℝ] E,
      ‖A.toContinuousLinearMap‖≤Real.sqrt 2 ∧
      ‖A.symm.toContinuousLinearMap‖≤Real.sqrt 2*H ∧
      ∀ x y : E,∀ i : Fin d,
        (A.symm (x+B.slow t (y-x))) i=(A.symm x) i ∨
        (A.symm (x+B.slow t (y-x))) i=(A.symm y) i := by
  obtain ⟨A,hA,hAi,hm⟩ := exists_coordinates (B.slow t).range (B.fast t).range
    (B.ranges_isCompl t) hH
    (fun x => by
      change ‖((B.slow t).range.projectionOnto (B.fast t).range (B.ranges_isCompl t) x:E)‖≤_
      rw [B.range_projection_slow]
      exact ((B.slow t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
    (fun x => by
      change ‖((B.fast t).range.projectionOnto (B.slow t).range (B.ranges_isCompl t).symm x:E)‖≤_
      rw [B.range_projection_fast]
      exact ((B.fast t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg x)))
  exact ⟨A,hA,hAi,fun x y i => by simpa only [B.range_projection_slow] using hm x y i⟩
end SmoothObstruction.ProductBasis

namespace SmoothObstruction.ShortBin
open scoped Matrix.Norms.L2Operator
variable {d n : ℕ} {K : ℝ}

/-- Authentic gauges give product coordinates for the original coarse bin.
The coordinate groups are allowed to have either rank zero or full rank. -/
theorem Gauge.product_coordinates (A : Gauge d n K) (S : Finset (Fin d)) :
    ∃ L : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d),
      ‖L.toContinuousLinearMap‖≤Real.sqrt 2 ∧
      ‖L.symm.toContinuousLinearMap‖≤Real.sqrt 2*Real.exp (2*K) ∧
      ∀ x y : EuclideanSpace ℝ (Fin d),∀ i : Fin d,
        (L.symm (x+(A.splitting S).slow 0 (y-x))) i=(L.symm x) i ∨
        (L.symm (x+(A.splitting S).slow 0 (y-x))) i=(L.symm y) i := by
  apply ProductBasis.splitting_coordinates (A.splitting S) 0 (Real.exp_pos _).le
  · exact EuclideanSplitting.splitting_slow_norm _ _ _ _ _ _ 0
      (A.normU _ (Nat.zero_le n)) (A.normV _ (Nat.zero_le n))
  · exact EuclideanSplitting.splitting_fast_norm _ _ _ _ _ _ 0
      (A.normU _ (Nat.zero_le n)) (A.normV _ (Nat.zero_le n))
end SmoothObstruction.ShortBin

namespace SmoothObstruction.FiniteBins
open Set
variable {X C : Type*} {d n : ℕ} {K : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Extend the genuinely selected bin coordinates to unused bins. The arbitrary
identity coordinates are never used by a retained input. -/
theorem product_coordinates (P : X → C) (G : Set X) (hK : 0≤K)
    (A : Active P G → ShortBin.Gauge d n K) (S : Active P G → Finset (Fin d)) :
    ∃ L : C → E ≃L[ℝ] E,
      (∀ c,‖(L c).toContinuousLinearMap‖≤Real.sqrt 2) ∧
      (∀ c,‖(L c).symm.toContinuousLinearMap‖≤Real.sqrt 2*Real.exp (2*K)) ∧
      ∀ c : Active P G,∀ x y : E,∀ i : Fin d,
        ((L c.val).symm (x+((A c).splitting (S c)).slow 0 (y-x))) i=
          ((L c.val).symm x) i ∨
        ((L c.val).symm (x+((A c).splitting (S c)).slow 0 (y-x))) i=
          ((L c.val).symm y) i := by
  classical
  choose L hL hLi hm using fun c => (A c).product_coordinates (S c)
  let F (c : C) : E ≃L[ℝ] E := if h : ∃ x∈G,P x=c then L ⟨c,h⟩ else ContinuousLinearEquiv.refl ℝ E
  have hroot : 1≤Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hexp : 1≤Real.exp (2*K) := Real.one_le_exp_iff.mpr (by positivity)
  refine ⟨F,?_,?_,?_⟩
  · intro c
    dsimp only [F]
    split_ifs with hc
    · exact hL _
    · exact (show ‖(ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap‖≤1 from ContinuousLinearMap.norm_id_le).trans hroot
  · intro c
    dsimp only [F]
    split_ifs with hc
    · exact hLi _
    · exact (show ‖(ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap‖≤1 from ContinuousLinearMap.norm_id_le).trans
        (le_trans hroot (by nlinarith [Real.sqrt_nonneg (2:ℝ)]))
  · intro c x y i
    rcases c with ⟨c,hc⟩
    simpa only [F,dite_eq_left hc] using hm ⟨c,hc⟩ x y i
end SmoothObstruction.FiniteBins

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

lemma measurable_coordinates (a : M) : Measurable (coordinates I a) := by
  classical
  exact (continuousOn_extChartAt a).measurable_piecewise continuous_const.continuousOn
    (by rw [extChartAt_source]; exact (chartAt H a).open_source.measurableSet)

omit [MeasurableSpace M] [BorelSpace M] in
lemma coordinates_eq (a x : M) (hx : x∈(extChartAt I a).source) :
    coordinates I a x=extChartAt I a x := by
  classical
  exact ite_eq_left hx

end SmoothObstruction.ChartDensity

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_GridCells
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

namespace SmoothObstruction.GridMargin
open Set MeasureTheory

lemma street_measurable (δ : ℝ) (N : ℕ) (k : Fin N) : MeasurableSet (street δ N k) := by
  have he : street δ N k=⋃ j : ℤ,{x : ℝ | |x-δ*((N:ℝ)*j+k.val)|≤δ/4} := by
    ext x; simp [street]
  rw [he]
  exact MeasurableSet.iUnion fun _ => measurableSet_le (by fun_prop) measurable_const

lemma centers_lt_eq {a b : ℤ} {δ : ℝ} (hδ : 0<δ)
    (hab : |δ*((a:ℝ)-b)|≤δ/2) : a=b := by
  have hd : |(a:ℝ)-b|<1 := by
    rw [abs_mul,abs_of_pos hδ] at hab
    nlinarith [abs_nonneg ((a:ℝ)-b)]
  have hdi : |a-b|<1 := by exact_mod_cast hd
  have he : a-b=0 := by
    have hh := abs_lt.mp hdi
    omega
  omega

lemma street_disjoint {δ : ℝ} (hδ : 0<δ) (N : ℕ) :
    Pairwise (fun k l : Fin N => Disjoint (street δ N k) (street δ N l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j,hj⟩ := hx
  obtain ⟨m,hm⟩ := hy
  have h := (abs_sub_le (δ*((N:ℝ)*j+k.val)) x (δ*((N:ℝ)*m+l.val)))
  rw [abs_sub_comm (δ*((N:ℝ)*j+k.val)) x] at h
  have hab : |δ*((((N:ℤ)*j+k.val : ℤ):ℝ)-(((N:ℤ)*m+l.val : ℤ):ℝ))|≤δ/2 := by
    push_cast
    calc
      _ = |δ*((N:ℝ)*j+k.val)-δ*((N:ℝ)*m+l.val)| := by congr 1; ring
      _ ≤ _ := h.trans (by linarith)
  have he := centers_lt_eq hδ hab
  have hmod := congrArg (fun z : ℤ => z%(N:ℤ)) he
  have hk : (k.val:ℤ)%(N:ℤ)=k.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast k.isLt)
  have hl : (l.val:ℤ)%(N:ℤ)=l.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast l.isLt)
  simp only [Int.add_emod,Int.mul_emod_right,zero_add,hk,hl] at hmod
  exact hkl (Fin.ext (by exact_mod_cast hmod))

/-- Within a retained scalar cell, a perturbation less than the full margin
cannot change the integer cell index. -/
lemma floor_stable {r a x y ε : ℝ} (hr : 0 < r)
    (hx : ∀ j : ℤ,ε < |x-(a+r*j)|) (hxy : |y-x|≤ε) :
    ⌊(y-a)/r⌋=⌊(x-a)/r⌋ := by
  let j : ℤ := ⌊(x-a)/r⌋
  have hj₁ := Int.floor_le ((x-a)/r)
  have hj₂ := Int.lt_floor_add_one ((x-a)/r)
  have hlo : a+r*j≤x := by nlinarith [(le_div_iff₀ hr).mp hj₁]
  have hhi : x<a+r*(j+1) := by nlinarith [(div_lt_iff₀ hr).mp hj₂]
  have hleft := hx j
  have hright := hx (j+1)
  rw [abs_of_nonneg (by linarith)] at hleft
  rw [abs_of_nonpos (by push_cast; linarith)] at hright
  have hy := abs_le.mp hxy
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hr).mpr
    dsimp [j] at *
    nlinarith
  · apply (div_lt_iff₀ hr).mpr
    push_cast at hright
    dsimp [j] at *
    nlinarith
end SmoothObstruction.GridMargin

namespace SmoothObstruction.GridMargin
open Set MeasureTheory
variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

lemma measurable_gridIndex (δ : ℝ) (N : ℕ) (k : Fin N) :
    Measurable (gridIndex δ N k) := by unfold gridIndex; fun_prop

lemma gridIndex_stable {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N)
    (k : Fin N) {x y : ℝ} (hx : x∉street δ N k) (hxy : |y-x| ≤ δ/4) :
    gridIndex δ N k y=gridIndex δ N k x := by
  apply floor_stable (mul_pos hδ (by exact_mod_cast hN)) _ hxy
  intro j
  have hj : ¬ |x-δ*((N:ℝ)*j+k.val)| ≤ δ/4 := fun h => hx ⟨j,h⟩
  have he : δ*k.val+(δ*N)*j=δ*((N:ℝ)*j+k.val) := by ring
  rw [he]
  exact lt_of_not_ge hj

lemma boundedLabel_inj {m : ℕ} {i j : ℤ}
    (hi : -(m:ℤ) ≤ i  ∧  i ≤ m) (hj : -(m:ℤ) ≤ j  ∧  j ≤ m)
    (he : boundedLabel m i=boundedLabel m j) : i=j := by
  have hv := congrArg Fin.val he
  simp only [boundedLabel] at hv
  omega

lemma floor_bounds {x : ℝ} {m : ℕ} (hx : |x| ≤ (m:ℝ)) :
    -(m:ℤ) ≤ ⌊x⌋  ∧  ⌊x⌋ ≤ m := by
  constructor
  · apply Int.le_floor.mpr
    push_cast
    exact (abs_le.mp hx).1
  · exact_mod_cast (Int.floor_le x).trans (abs_le.mp hx).2

omit [Fintype ι] in
lemma measurable_productLabel (m : ℕ) (δ : ℝ) (N : ℕ) (k : ι → Fin N)
    (c : X → ι → ℝ) (hc : ∀ i,Measurable (fun x =>  c x i)) :
    Measurable (productLabel m δ N k c) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_of_countable (boundedLabel m)).comp ((measurable_gridIndex δ N (k i)).comp (hc i))

lemma same_cell_coord {r a x y : ℝ} (hr : 0 < r)
    (he : ⌊(x-a)/r⌋=⌊(y-a)/r⌋) : |y-x| < r := by
  have hx₁ := Int.floor_le ((x-a)/r)
  have hx₂ := Int.lt_floor_add_one ((x-a)/r)
  have hy₁ := Int.floor_le ((y-a)/r)
  have hy₂ := Int.lt_floor_add_one ((y-a)/r)
  rw [←he] at hy₁ hy₂
  apply abs_lt.mpr
  constructor  <;>  nlinarith [(le_div_iff₀ hr).mp hx₁,(le_div_iff₀ hr).mp hy₁,
    (div_lt_iff₀ hr).mp hx₂,(div_lt_iff₀ hr).mp hy₂]

end SmoothObstruction.GridMargin

namespace SmoothObstruction.GridMargin
open Set MeasureTheory

/-- Each finite original measure admits the same translated-street estimate,
scaled by its original total mass. This is used on partition fibres without
changing the final pair law. -/
theorem exists_small_street_finite (μ : Measure ℝ) [IsFiniteMeasure μ]
    {δ : ℝ} (hδ : 0<δ) {N : ℕ} (hN : 0<N) :
    ∃ k : Fin N,μ.real (street δ N k)≤μ.real univ/(N:ℝ) := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hs : (∑ k : Fin N,μ.real (street δ N k))≤μ.real univ :=
    sum_measureReal_le_measureReal_univ (μ:=μ) (s:=Finset.univ)
      (fun k _ => street_measurable δ N k)
      (fun k _ l _ hkl => street_disjoint hδ N hkl)
  by_contra hh
  push Not at hh
  have hl := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ) Finset.univ_nonempty
    (fun k _ => hh k)
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hv : (∑ _k : Fin N,μ.real univ/(N:ℝ))=μ.real univ := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  rw [hv] at hl
  linarith

variable {X ι C : Type*} [MeasurableSpace X] [Fintype ι]

/-- Simultaneous margins for a finite, not necessarily probability, law. -/
theorem exists_product_margins_finite (μ : Measure X) [IsFiniteMeasure μ]
    (c : X → ι → ℝ) (hc : ∀ i,Measurable (fun x => c x i))
    {δ : ℝ} (hδ : 0<δ) {N : ℕ} (hN : 0<N) :
    ∃ k : ι → Fin N,
      μ.real (⋃ i,(fun x => c x i) ⁻¹' street δ N (k i)) ≤
        (Fintype.card ι:ℝ)*μ.real univ/N := by
  have hchoice (i : ι) : ∃ k : Fin N,
      μ.real ((fun x => c x i) ⁻¹' street δ N k) ≤ μ.real univ/(N:ℝ) := by
    obtain ⟨k,hk⟩ := exists_small_street_finite (μ.map (fun x => c x i)) hδ hN
    refine ⟨k,?_⟩
    simpa only [Measure.real,Measure.map_apply (hc i) (street_measurable δ N k),
      Measure.map_apply (hc i) MeasurableSet.univ,preimage_univ] using hk
  choose k hk using hchoice
  refine ⟨k,?_⟩
  calc
    _ ≤ ∑ i,μ.real ((fun x => c x i) ⁻¹' street δ N (k i)) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι,μ.real univ/(N:ℝ) := Finset.sum_le_sum fun i _ => hk i
    _ = _ := by simp [mul_div_assoc]

variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

/-- Independently translated grids in each fibre of a finite measurable
partition retain the same original total-mass budget. The number of fibres
does not multiply the loss. -/
theorem fibrewise_margins (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (c : C → X → ι → ℝ)
    (hc : ∀ a i,Measurable (fun x => c a x i))
    {δ : ℝ} (hδ : 0<δ) {N : ℕ} (hN : 0<N) :
    ∃ k : C → ι → Fin N,
      μ.real (⋃ a,(P ⁻¹' {a}) ∩ ⋃ i,(fun x => c a x i) ⁻¹' street δ N (k a i)) ≤
        (Fintype.card ι:ℝ)/N := by
  have hchoice (a : C) := exists_product_margins_finite (μ.restrict (P ⁻¹' {a}))
    (c a) (hc a) hδ hN
  choose k hk using hchoice
  let D (a : C) := ⋃ i,(fun x => c a x i) ⁻¹' street δ N (k a i)
  have hD (a : C) : MeasurableSet (D a) :=
    MeasurableSet.iUnion (fun i => (hc a i) (street_measurable δ N _))
  have hQ (a : C) : MeasurableSet (P ⁻¹' {a}) := hP (measurableSet_singleton a)
  have hs : (∑ a,μ.real (P ⁻¹' {a}))=1 := by
    have hd : Pairwise (fun i j : C => Disjoint (P ⁻¹' {i}) (P ⁻¹' {j})) := by
      intro i j hij
      exact (Set.disjoint_singleton.mpr hij).preimage P
    rw [←measureReal_iUnion_fintype (μ:=μ) hd hQ]
    have he : (⋃ a,P ⁻¹' {a})=univ := by ext x; simp
    rw [he]
    simp
  refine ⟨k,?_⟩
  calc
    _ ≤ ∑ a,μ.real ((P ⁻¹' {a})∩D a) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ a,(Fintype.card ι:ℝ)*μ.real (P ⁻¹' {a})/N := by
      apply Finset.sum_le_sum
      intro a _
      have h := hk a
      rw [Measure.real,Measure.restrict_apply (hD a),Measure.real,
        Measure.restrict_apply MeasurableSet.univ,univ_inter] at h
      simpa only [Measure.real,inter_comm] using h
    _ = (Fintype.card ι:ℝ)/N := by
      rw [←Finset.sum_div,←Finset.mul_sum,hs,mul_one]
end SmoothObstruction.GridMargin

namespace SmoothObstruction.GridRefinement
open Set MeasureTheory
open SmoothObstruction.GridMargin
variable {X C ι : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_label (P : X → C) (hP : Measurable P)
    (c : C → X → ι → ℝ) (hc : ∀ a i,Measurable (fun x => c a x i))
    (m : ℕ) (δ : ℝ) (N : ℕ) (k : C → ι → Fin N) :
    Measurable (label P c m δ N k) := by
  have h : Measurable (fun p : C × X => productLabel m δ N (k p.1) (c p.1) p.2) :=
    measurable_from_prod_countable_right (fun a => measurable_productLabel m δ N (k a) (c a) (hc a))
  change Measurable (fun x => (P x,productLabel m δ N (k (P x)) (c (P x)) x))
  have hg : Measurable (fun x : X => (P x,x)) := hP.prodMk measurable_id
  have hq := h.comp hg
  exact hP.prodMk hq

end SmoothObstruction.GridRefinement

namespace SmoothObstruction.GridRefinement
open Set MeasureTheory
open SmoothObstruction.GridMargin
variable {X C ι : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The retained product margins survive a complementary coordinate mix.
Each output coordinate may follow either retained input, so this applies
simultaneously to both actual orbit joins. Mass is still the original law. -/
theorem exists_mixing_refinement (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (c : C → X → ι → ℝ)
    (hc : ∀ a i,Measurable (fun x => c a x i))
    (m : ℕ) {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N) :
    ∃ (k : C → ι → Fin N) (W : Set X),
      MeasurableSet W ∧ μ.real W ≤ (Fintype.card ι:ℝ)/N ∧
      Measurable (label P c m δ N k) ∧
      (∀ x y z,x∉W → y∉W →
        label P c m δ N k x=label P c m δ N k y → P z=P x →
        (∀ i,|c (P x) z i-c (P x) x i| ≤ δ/4 ∨
          |c (P x) z i-c (P x) y i| ≤ δ/4) →
        label P c m δ N k z=label P c m δ N k x) ∧
      (∀ x y,label P c m δ N k x=label P c m δ N k y →
        (∀ i,|(c (P x) x i-δ*(k (P x) i).val)/(δ*N)| ≤ (m:ℝ)) →
        (∀ i,|(c (P x) y i-δ*(k (P x) i).val)/(δ*N)| ≤ (m:ℝ)) →
        ∀ i,|c (P x) x i-c (P x) y i| < δ*N) := by
  classical
  obtain ⟨k,hk⟩ := fibrewise_margins μ P hP c hc hδ hN
  let W := ⋃ a,(P ⁻¹' {a}) ∩ ⋃ i,(fun x => c a x i) ⁻¹' street δ N (k a i)
  have hW : MeasurableSet W := MeasurableSet.iUnion (fun a =>
    (hP (measurableSet_singleton a)).inter
      (MeasurableSet.iUnion (fun i => (hc a i) (street_measurable δ N _))))
  have hout (x : X) (hx : x∉W) (i : ι) : c (P x) x i∉street δ N (k (P x) i) := by
    intro hi
    exact hx (mem_iUnion.mpr ⟨P x,rfl,mem_iUnion.mpr ⟨i,hi⟩⟩)
  refine ⟨k,W,hW,hk,measurable_label P hP c hc m δ N k,?_,?_⟩
  · intro x y z hx hy he hp hm
    have hxy : P x=P y := congrArg Prod.fst he
    apply Prod.ext hp
    change productLabel m δ N (k (P z)) (c (P z)) z=
      productLabel m δ N (k (P x)) (c (P x)) x
    rw [hp]
    funext i
    rcases hm i with hi | hi
    · exact congrArg (boundedLabel m) (gridIndex_stable hδ hN _ (hout x hx i) hi)
    · have hy' : c (P x) y i∉street δ N (k (P x) i) := by
        simpa only [hxy] using hout y hy i
      have he' := congrArg (fun p : C × (ι → Fin (2*m+1)) => p.2 i) he
      change boundedLabel m (gridIndex δ N (k (P x) i) (c (P x) x i))=
        boundedLabel m (gridIndex δ N (k (P y) i) (c (P y) y i)) at he'
      rw [←hxy] at he'
      exact (congrArg (boundedLabel m) (gridIndex_stable hδ hN _ hy' hi)).trans he'.symm
  · intro x y he hx hy i
    have hxy : P x=P y := congrArg Prod.fst he
    have he' := congrArg (fun p : C × (ι → Fin (2*m+1)) => p.2 i) he
    change boundedLabel m (gridIndex δ N (k (P x) i) (c (P x) x i))=
      boundedLabel m (gridIndex δ N (k (P y) i) (c (P y) y i)) at he'
    rw [←hxy] at he'
    have hidx := boundedLabel_inj (floor_bounds (hx i)) (floor_bounds (hy i)) he'
    exact same_cell_coord (mul_pos hδ (by exact_mod_cast hN)) hidx.symm
end SmoothObstruction.GridRefinement

namespace SmoothObstruction.ProductCells
open Set MeasureTheory
open SmoothObstruction.GridMargin SmoothObstruction.GridRefinement
variable {X C : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

lemma norm_le_coords {u : E} {h : ℝ} (hh : 0≤h) (hu : ∀ i,|u i|≤h) :
    ‖u‖≤((d:ℝ)+1)*h := by
  have hs : ‖u‖^2≤(d:ℝ)*h^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin d,h^2 := Finset.sum_le_sum (fun i _ => by
        have hi := hu i
        nlinarith [sq_abs (u i),abs_nonneg (u i)])
      _ = _ := by simp
  have hd : 0≤(d:ℝ) := Nat.cast_nonneg _
  have hp : 0≤((d:ℝ)+1)*h := by positivity
  have hsq : (d:ℝ)*h^2≤(((d:ℝ)+1)*h)^2 := by
    nlinarith [sq_nonneg ((d:ℝ)*h),mul_nonneg hd (sq_nonneg h)]
  nlinarith [norm_nonneg u]

lemma grid_range {δ D H : ℝ} (hδ : 0<δ) (hD : 0≤D) (hH : 0≤H)
    {N : ℕ} (hN : 0<N) (k : Fin N) {v : ℝ} (hv : |v|≤H*D) :
    |(v-δ*k.val)/(δ*N)|≤(⌈H*D/(δ*N)+1⌉₊:ℝ) := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  have hk : (k.val:ℝ)≤N := by exact_mod_cast k.isLt.le
  have hi : 0≤δ*(k.val:ℝ) := by positivity
  have hab : |v-δ*k.val|≤H*D+δ*N := by
    calc
      _ ≤ |v|+|δ*k.val| := abs_sub _ _
      _ ≤ H*D+δ*N := by rw [abs_of_nonneg hi]; nlinarith
  rw [abs_div,abs_of_pos (mul_pos hδ hn)]
  calc
    _ ≤ (H*D+δ*N)/(δ*N) := div_le_div_of_nonneg_right hab (by positivity)
    _ = H*D/(δ*N)+1 := by field_simp
    _ ≤ _ := Nat.le_ceil _

/-- Finite product cells for arbitrary measurable geometric coordinates.
The original probability law loses at most d/N near product streets. The
number of cells is exactly the finite grid alphabet; no rank or orbit code
is counted. Stability is stated in the physical coordinates needed for joins. -/
theorem exists_cells (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (φ : C → X → E)
    (hφ : ∀ c,Measurable (φ c)) (A : C → E ≃L[ℝ] E)
    {D H F δ : ℝ} (hD : 0≤D) (hH : 0≤H) (hF : 0≤F) (hδ : 0<δ)
    (hbound : ∀ x,‖φ (P x) x‖≤D)
    (hAi : ∀ c,‖(A c).symm.toContinuousLinearMap‖≤H)
    (hA : ∀ c,‖(A c).toContinuousLinearMap‖≤F)
    {N : ℕ} (hN : 0<N) :
    let m := ⌈H*D/(δ*N)+1⌉₊
    ∃ (L : X → C × (Fin d → Fin (2*m+1))) (W : Set X),
      Measurable L ∧ MeasurableSet W ∧ μ.real W≤(d:ℝ)/N ∧
      (∀ x,(L x).1=P x) ∧
      (∀ x y,L x=L y → ‖φ (P x) x-φ (P x) y‖≤F*((d:ℝ)+1)*(δ*N)) ∧
      (∀ x y z,L x=L y → x∉W → y∉W → P z=P x →
        (∀ i,|((A (P x)).symm (φ (P x) z)) i-
          ((A (P x)).symm (φ (P x) x)) i|≤δ/4 ∨
          |((A (P x)).symm (φ (P x) z)) i-
          ((A (P x)).symm (φ (P x) y)) i|≤δ/4) → L z=L x) ∧
      Fintype.card (C × (Fin d → Fin (2*m+1)))=Fintype.card C*(2*m+1)^d := by
  classical
  dsimp only
  let m := ⌈H*D/(δ*N)+1⌉₊
  let c (a : C) (x : X) (i : Fin d) := ((A a).symm (φ a x)) i
  have hc (a : C) (i : Fin d) : Measurable (fun x => c a x i) :=
    (show Measurable (fun u : E => u i) by fun_prop).comp
      ((A a).symm.continuous.measurable.comp (hφ a))
  obtain ⟨k,W,hW,hm,hL,hstable,hdiam⟩ :=
    exists_mixing_refinement μ P hP c hc m hδ hN
  let L := label P c m δ N k
  have hrange (x : X) (i : Fin d) :
      |(c (P x) x i-δ*(k (P x) i).val)/(δ*N)|≤(m:ℝ) := by
    apply grid_range hδ hD hH hN
    calc
      _ = ‖((A (P x)).symm (φ (P x) x)) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(A (P x)).symm (φ (P x) x)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖(A (P x)).symm.toContinuousLinearMap‖*‖φ (P x) x‖ :=
        (A (P x)).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ H*D := mul_le_mul (hAi _) (hbound x) (norm_nonneg _) hH
  refine ⟨L,W,hL,hW,by simpa using hm,fun _ => rfl,?_,?_,by simp⟩
  · intro x y he
    have hxy : P x=P y := congrArg Prod.fst he
    have hh := hdiam x y he (hrange x) (by simpa only [hxy] using hrange y)
    have hb : ‖(A (P x)).symm (φ (P x) x)-(A (P x)).symm (φ (P x) y)‖≤
        ((d:ℝ)+1)*(δ*N) := by
      apply norm_le_coords (by positivity)
      intro i
      exact (hh i).le
    calc
      _ = ‖A (P x) ((A (P x)).symm (φ (P x) x)-(A (P x)).symm (φ (P x) y))‖ := by
        rw [map_sub]; simp
      _ ≤ ‖(A (P x)).toContinuousLinearMap‖*
          ‖(A (P x)).symm (φ (P x) x)-(A (P x)).symm (φ (P x) y)‖ :=
        (A (P x)).toContinuousLinearMap.le_opNorm _
      _ ≤ F*(((d:ℝ)+1)*(δ*N)) := mul_le_mul (hA _) hb (norm_nonneg _) hF
      _ = _ := by ring
  · intro x y z he hx hy hp hh
    exact hstable x y z hx hy he hp hh
end SmoothObstruction.ProductCells

namespace SmoothObstruction.ChartDensity
open Set MeasureTheory
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
/-- A uniform selected-coordinate bound follows from the compact atlas,
without any regularity assumption on the selection itself. -/
theorem selected_coordinate_bound (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (q : M → ι) (hqK : ∀ x,x∈K (q x)) :
    ∃ D : ℝ,1≤D ∧ ∀ x,‖coordinates I (a (q x)) x‖≤D := by
  classical
  have hex (i : ι) : ∃ R : ℝ,∀ x∈K i,‖(extChartAt I (a i)) x‖≤R := by
    have hc := (hK i).image_of_continuousOn
      ((continuousOn_extChartAt (I:=I) (a i)).mono
        (by simpa only [extChartAt_source] using hKU i))
    obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
    exact ⟨R,fun x hx => hR _ ⟨x,hx,rfl⟩⟩
  choose R hR using hex
  let D := 1+∑ i,|R i|
  have hp : 0≤∑ i,|R i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨D,by dsimp [D]; linarith,fun x => ?_⟩
  rw [coordinates_eq I _ _ (by simpa only [extChartAt_source] using hKU _ (hqK x))]
  calc
    _ ≤ R (q x) := hR _ _ (hqK x)
    _ ≤ |R (q x)| := le_abs_self _
    _ ≤ ∑ i,|R i| := Finset.single_le_sum (fun i _ => abs_nonneg (R i)) (Finset.mem_univ _)
    _ ≤ D := by dsimp [D]; linarith

omit [T2Space M] in
/-- Genuine finite coarse bins in a compact atlas. Their translated margins
are estimated using the ORIGINAL measure, with no assumptions about its
interaction with the good gauge set. Only the selected starting chart is
part of the finite alphabet. -/
theorem exists_coarse_cells [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (q : M → ι) (hq : Measurable q) (hqK : ∀ x,x∈K (q x)) :
    ∃ D : ℝ,1≤D ∧ ∀ {δ : ℝ},0<δ → ∀ {N : ℕ},0<N →
      let m := ⌈D/(δ*N)+1⌉₊
      ∃ (P : M → ι × (Fin d → Fin (2*m+1))) (W : Set M),
        Measurable P ∧ MeasurableSet W ∧ μ.real W≤(d:ℝ)/N ∧
        (∀ x,(P x).1=q x) ∧
        (∀ x y,P x=P y →
          ‖coordinates I (a (q x)) x-coordinates I (a (q x)) y‖≤((d:ℝ)+1)*(δ*N)) ∧
        (∀ x z,x∉W → q z=q x →
          ‖coordinates I (a (q x)) z-coordinates I (a (q x)) x‖≤δ/4 → P z=P x) ∧
        Fintype.card (ι × (Fin d → Fin (2*m+1)))=Fintype.card ι*(2*m+1)^d := by
  obtain ⟨D,hD,hbound⟩ := selected_coordinate_bound I a K hK hKU q hqK
  refine ⟨D,hD,?_⟩
  intro δ hδ N hN
  have hh := ProductCells.exists_cells μ q hq (fun i => coordinates I (a i))
      (fun i => measurable_coordinates I (a i))
      (fun _ => ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)))
      (D:=D) (H:=1) (F:=1) (by linarith) (by norm_num) (by norm_num) hδ hbound
      (fun _ => ContinuousLinearMap.norm_id_le) (fun _ => ContinuousLinearMap.norm_id_le) hN
  dsimp only at hh
  rw [one_mul] at hh
  simp only [one_mul] at hh
  obtain ⟨P,W,hP,hW,hm,hqP,hd,hs,hcard⟩ := hh
  refine ⟨P,W,hP,hW,hm,hqP,hd,?_,hcard⟩
  intro x z hx hqz hz
  apply hs x x z rfl hx hx hqz
  intro i
  left
  exact (PiLp.norm_apply_le
    (coordinates I (a (q x)) z-coordinates I (a (q x)) x) i).trans hz
end SmoothObstruction.ChartDensity

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PairLaw
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Classical
open Finset

namespace SmoothObstruction.PairLaw
open MeasureTheory Set Finset
open scoped ENNReal
variable {X α : Type*} [MeasurableSpace X] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

lemma second_marginal (μ : Measure X) [IsFiniteMeasure μ] (P : X → α) (hP : Measurable P) :
    (law μ P).map Prod.snd=μ := by
  rw [law,←Measure.mapₗ_apply_of_measurable measurable_snd,map_sum]
  simp only [Measure.mapₗ_apply_of_measurable measurable_snd,
    Measure.map_smul,
    Measure.map_snd_prod,smul_smul,normalized_cell]
  exact sum_cells μ P hP

lemma bad_pair_bound (μ : Measure X) [IsProbabilityMeasure μ] (P : X → α) (hP : Measurable P)
    (R : Set X) (hR : MeasurableSet R) :
    law μ P (R ×ˢ R)ᶜ ≤ 2*μ Rᶜ := by
  have he : (R ×ˢ R)ᶜ=(Prod.fst ⁻¹' Rᶜ)∪(Prod.snd ⁻¹' Rᶜ) := by
    ext z; simp only [mem_compl_iff,mem_prod,mem_union,Set.mem_preimage]; tauto
  rw [he]
  have hf := congrArg (fun ν : Measure X => ν Rᶜ) (first_marginal μ P hP)
  have hs := congrArg (fun ν : Measure X => ν Rᶜ) (second_marginal μ P hP)
  rw [Measure.map_apply measurable_fst hR.compl] at hf
  rw [Measure.map_apply measurable_snd hR.compl] at hs
  exact (measure_union_le _ _).trans (by rw [hf,hs,two_mul])

end SmoothObstruction.PairLaw

end

section

namespace SmoothObstruction
open MeasureTheory Filter Topology Set
open scoped ENNReal
attribute [instance] SwitchData.fin SwitchData.meas SwitchData.singletons
end SmoothObstruction

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

/-- The original cell-weighted experiment is carried by pairs in the same
cell, including zero-mass cells without any special convention. -/
lemma same_cell_ae (μ : Measure X) [IsFiniteMeasure μ] (P : X → α)
    (hP : Measurable P) : ∀ᵐ z ∂law μ P,P z.1=P z.2 := by
  classical
  rw [law,ae_finsetSum_measure_iff]
  intro a _
  apply Measure.ae_smul_measure
  have hQ : MeasurableSet (P ⁻¹' {a}) := hP (measurableSet_singleton a)
  rw [cell,Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (hQ.prod hQ)] with z hz
  exact (show P z.1=a from hz.1).trans (show P z.2=a from hz.2).symm

/-- Retention is measured in the original pair probability, rather than in
any conditional law on the good set. -/
theorem retained_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → α) (hP : Measurable P) (R : Set X) (hR : MeasurableSet R) :
    let G := (R ×ˢ R) ∩ {z : X×X | P z.1=P z.2}
    MeasurableSet G ∧ (law μ P) Gᶜ≤2*μ Rᶜ ∧
      1-2*μ.real Rᶜ≤(law μ P).real G := by
  intro G
  have hsame : MeasurableSet {z : X×X | P z.1=P z.2} :=
    measurableSet_eq_fun (hP.comp measurable_fst) (hP.comp measurable_snd)
  have hG : MeasurableSet G := (hR.prod hR).inter hsame
  have he : G=ᵐ[law μ P] R ×ˢ R := by
    filter_upwards [same_cell_ae μ P hP] with z hz
    apply propext
    change (z∈R ×ˢ R ∧ P z.1=P z.2) ↔ z∈R ×ˢ R
    simp only [hz,and_true]
  have hl : (law μ P) Gᶜ≤2*μ Rᶜ := by
    rw [measure_congr he.compl]
    exact bad_pair_bound μ P hP R hR
  let := law_probability μ P hP
  refine ⟨hG,hl,?_⟩
  have hreal : (law μ P).real Gᶜ≤2*μ.real Rᶜ := by
    have h := ENNReal.toReal_mono (show 2*μ Rᶜ≠∞ by finiteness) hl
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,Measure.real] using h
  rw [probReal_compl_eq_one_sub hG] at hreal
  linarith

end SmoothObstruction.PairLaw

namespace SmoothObstruction.OrbitSafety
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

/-- A finite two-sided safety exclusion is charged to the original invariant
measure at every time, without conditioning the retained law. -/
theorem bilateral_bad_bound (μ : Measure X) (f g : X → X)
    (hf : MeasurePreserving f μ μ) (hg : MeasurePreserving g μ μ)
    (W : Set X) (hW : MeasurableSet W) (n : ℕ) :
    let Z := (⋃ t : Fin (n+1),(f^[t.val]) ⁻¹' W) ∪
      (⋃ t : Fin (n+1),(g^[t.val]) ⁻¹' W)
    MeasurableSet Z ∧ μ Z≤(2*(n+1) : ℝ≥0∞)*μ W ∧
      ∀ x,x∉Z → ∀ t≤n,(f^[t]) x∉W ∧ (g^[t]) x∉W := by
  intro Z
  have hm : MeasurableSet Z :=
    (MeasurableSet.iUnion (fun t : Fin (n+1) => hW.preimage (hf.iterate t.val).measurable)).union
      (MeasurableSet.iUnion (fun t : Fin (n+1) => hW.preimage (hg.iterate t.val).measurable))
  have h1 : μ (⋃ t : Fin (n+1),(f^[t.val]) ⁻¹' W)≤(n+1 : ℝ≥0∞)*μ W := by
    calc
      _ ≤ ∑ t : Fin (n+1),μ ((f^[t.val]) ⁻¹' W) := measure_iUnion_fintype_le μ _
      _ = _ := by simp only [(hf.iterate _).measure_preimage hW.nullMeasurableSet,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  have h2 : μ (⋃ t : Fin (n+1),(g^[t.val]) ⁻¹' W)≤(n+1 : ℝ≥0∞)*μ W := by
    calc
      _ ≤ ∑ t : Fin (n+1),μ ((g^[t.val]) ⁻¹' W) := measure_iUnion_fintype_le μ _
      _ = _ := by simp only [(hg.iterate _).measure_preimage hW.nullMeasurableSet,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  refine ⟨hm,?_,?_⟩
  · exact (measure_union_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  · intro x hx t ht
    constructor
    · intro h
      exact hx (Or.inl (mem_iUnion.mpr ⟨⟨t,Nat.lt_succ_of_le ht⟩,h⟩))
    · intro h
      exact hx (Or.inr (mem_iUnion.mpr ⟨⟨t,Nat.lt_succ_of_le ht⟩,h⟩))
end SmoothObstruction.OrbitSafety

namespace SmoothObstruction.RetainedGlobal
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

lemma real_union_le (μ : Measure X) [IsFiniteMeasure μ] (A B : Set X) :
    μ.real (A∪B)≤μ.real A+μ.real B := by
  have h := ENNReal.toReal_mono (show μ A+μ B≠∞ by finiteness) (measure_union_le A B)
  simpa only [Measure.real,ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] using h

/-- The actual one-point retained carrier. The fixed atlas core is checked
only at 0 and the two endpoints. Coarse margins, product margins, and all
boundary-tube checks are charged in the original stationary measure. -/
theorem exists_retained (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : X → X) (hf : MeasurePreserving f μ μ) (hg : MeasurePreserving g μ μ)
    (G V Wc Wp Wb : Set X) (hG : MeasurableSet G) (hV : MeasurableSet V)
    (hWc : MeasurableSet Wc) (hWp : MeasurableSet Wp) (hWb : MeasurableSet Wb) (n : ℕ) :
    ∃ R : Set X,MeasurableSet R ∧ R⊆G ∧
      μ.real Rᶜ≤μ.real Gᶜ+3*(μ.real Vᶜ+μ.real Wc)+μ.real Wp+
        2*((n:ℝ)+1)*μ.real Wb ∧
      ∀ x∈R,x∈V ∧ x∉Wc ∧ x∉Wp ∧
        f^[n] x∈V ∧ f^[n] x∉Wc ∧ g^[n] x∈V ∧ g^[n] x∉Wc ∧
        ∀ t≤n,f^[t] x∉Wb ∧ g^[t] x∉Wb := by
  let B := Vᶜ∪Wc
  have hB : MeasurableSet B := hV.compl.union hWc
  let Z := (⋃ t : Fin (n+1),(f^[t.val]) ⁻¹' Wb) ∪
    (⋃ t : Fin (n+1),(g^[t.val]) ⁻¹' Wb)
  obtain ⟨hZ,hZm,hZsafe⟩ := OrbitSafety.bilateral_bad_bound μ f g hf hg Wb hWb n
  let R := G∩(B∪(f^[n]) ⁻¹' B∪(g^[n]) ⁻¹' B∪Wp∪Z)ᶜ
  have hR : MeasurableSet R := hG.inter
    (((((hB.union (hB.preimage (hf.iterate n).measurable)).union
      (hB.preimage (hg.iterate n).measurable)).union hWp).union hZ).compl)
  have hmB : μ.real B≤μ.real Vᶜ+μ.real Wc := real_union_le μ _ _
  have hmF : μ.real ((f^[n]) ⁻¹' B)=μ.real B := by
    exact congrArg ENNReal.toReal ((hf.iterate n).measure_preimage hB.nullMeasurableSet)
  have hmG : μ.real ((g^[n]) ⁻¹' B)=μ.real B := by
    exact congrArg ENNReal.toReal ((hg.iterate n).measure_preimage hB.nullMeasurableSet)
  have hmZ : μ.real Z≤2*((n:ℝ)+1)*μ.real Wb := by
    have hh := ENNReal.toReal_mono (show (2*((n:ℝ≥0∞)+1))*μ Wb≠∞ by finiteness) hZm
    simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofNat,
      ENNReal.toReal_add (by finiteness : (n:ℝ≥0∞)≠∞) (by norm_num : (1:ℝ≥0∞)≠∞),
      ENNReal.toReal_natCast,ENNReal.toReal_one] using hh
  refine ⟨R,hR,inter_subset_left,?_,?_⟩
  · have he : Rᶜ=Gᶜ∪(B∪(f^[n]) ⁻¹' B∪(g^[n]) ⁻¹' B∪Wp∪Z) := by
      simp only [R,compl_inter,compl_compl]
    rw [he]
    have h0 := real_union_le μ Gᶜ (B∪(f^[n]) ⁻¹' B∪(g^[n]) ⁻¹' B∪Wp∪Z)
    have h1 := real_union_le μ (B∪(f^[n]) ⁻¹' B∪(g^[n]) ⁻¹' B∪Wp) Z
    have h2 := real_union_le μ (B∪(f^[n]) ⁻¹' B∪(g^[n]) ⁻¹' B) Wp
    have h3 := real_union_le μ (B∪(f^[n]) ⁻¹' B) ((g^[n]) ⁻¹' B)
    have h4 := real_union_le μ B ((f^[n]) ⁻¹' B)
    rw [hmF] at h4
    rw [hmG] at h3
    linarith
  · intro x hx
    have hh : x∉B ∧ f^[n] x∉B ∧ g^[n] x∉B ∧ x∉Wp ∧ x∉Z := by
      have h := hx.2
      simp only [mem_compl_iff,mem_union,Set.mem_preimage,not_or] at h
      exact ⟨h.1.1.1.1,h.1.1.1.2,h.1.1.2,h.1.2,h.2⟩
    have hb0 : x∈V ∧ x∉Wc := by simpa only [B,mem_union,mem_compl_iff,not_or,not_not] using hh.1
    have hbp : f^[n] x∈V ∧ f^[n] x∉Wc := by
      simpa only [B,mem_union,mem_compl_iff,not_or,not_not] using hh.2.1
    have hbm : g^[n] x∈V ∧ g^[n] x∉Wc := by
      simpa only [B,mem_union,mem_compl_iff,not_or,not_not] using hh.2.2.1
    exact ⟨hb0.1,hb0.2,hh.2.2.2.1,hbp.1,hbp.2,hbm.1,hbm.2,hZsafe x hh.2.2.2.2⟩

/-- Retained original cell-pair probability, with all exclusion losses and
without replacing cell weights by good-set weights. -/
theorem pair_mass {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : X → α) (hP : Measurable P)
    (R : Set X) (hR : MeasurableSet R) {η : ℝ} (hm : μ.real Rᶜ≤η/2) :
    let G := (R ×ˢ R)∩{z : X×X | P z.1=P z.2}
    MeasurableSet G ∧ 1-η≤(PairLaw.law μ P).real G := by
  intro G
  obtain ⟨hG,_,hb⟩ := PairLaw.retained_bound μ P hP R hR
  exact ⟨hG,by linarith⟩
end SmoothObstruction.RetainedGlobal

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

open scoped BigOperators
open scoped ContDiff BigOperators
open Module
open Filter Topology
open scoped Real

namespace SmoothObstruction.RelativeAsymptotics
open Filter Topology

/-- Exterior relative errors absorb every fixed exponential gauge cost.
The multiplicative nonlinear error remains the authentic envelope times
its exponential, not a dimension- or bin-dependent replacement. -/
theorem weighted_envelope_tendsto {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (C C₁ C₂ C₃ A K : ℝ) :
    Tendsto (fun k => A*Real.exp (K*b k*n k)*
      (envelope C 0 C₁ C₂ C₃ (b k) (n k)*
        Real.exp (envelope C 0 C₁ C₂ C₃ (b k) (n k)))) l (𝓝 0) := by
  have hv (J : ℝ) : Tendsto (fun k => envelope C J C₁ C₂ C₃ (b k) (n k)) l (𝓝 0) := by
    simpa only [envelope,mul_zero] using
      (SmoothScales.decisive_decay hbpos hb hn hfloor (2*C₁+J)).const_mul
        (2*C*C₃*Real.exp C₂)
  have hh := ((hv K).mul ((Real.continuous_exp.tendsto 0).comp (hv 0))).const_mul A
  simp only [Real.exp_zero,mul_one,mul_zero] at hh
  apply hh.congr
  intro k
  dsimp only [envelope,Function.comp_apply]
  rw [show -(3/2:ℝ)*SmoothScales.B (b k)*n k+(2*C₁+K)*b k*n k=
    K*b k*n k+(-(3/2:ℝ)*SmoothScales.B (b k)*n k+(2*C₁+0)*b k*n k) by ring,
    Real.exp_add]
  ring

/-- Literal leading-minor relative perturbation parameter tends to zero. -/
theorem common_relative_budget {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (C Crel C₁ C₂ C₃ D W : ℝ) (p : ℕ) :
    Tendsto (fun k => 2*((C*(Real.exp (D*b k*n k))^p)^2*(C*2^p))*C*
      (envelope Crel 0 C₁ C₂ C₃ (b k) (n k)*
        Real.exp (envelope Crel 0 C₁ C₂ C₃ (b k) (n k)))*W) l (𝓝 0) := by
  apply (weighted_envelope_tendsto hbpos hb hn hfloor Crel C₁ C₂ C₃
    (2*C^4*2^p*W) ((2*p:ℕ)*D)).congr
  intro k
  have he : Real.exp (((2*p:ℕ):ℝ)*D*b k*n k)=(Real.exp (D*b k*n k))^(2*p) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  simp only [Nat.mul_comm 2 p,pow_mul]
  ring
end SmoothObstruction.RelativeAsymptotics

namespace SmoothObstruction.EndpointBudget
open Filter Topology

/-- One eventual scalar budget works at ALL ranks, before choosing any
starting cell, endpoint label, good gauge, or input frame. -/
theorem all_ranks {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (d : ℕ) (C Crel C₁ C₂ C₃ D c : ℝ) (hc : 0 < c)
    (F N V W β : Fin (d+1) → ℝ)
    (hF : ∀ p,0≤F p) (hN : ∀ p,0≤N p) (hV : ∀ p,0≤V p)
    (hW : ∀ p,0≤W p) (hβ : ∀ p,0<β p)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤Real.exp (-c*b k^(3/4:ℝ)*n k)) :
    ∀ᶠ k in l,∀ p : Fin (d+1),
      (F p*δ k)*(1+leading C (D*b k*n k) p.val*normCost C (D*b k*n k) (N p) p.val)≤1/2 ∧
      relative C Crel C₁ C₂ C₃ D (V p) (b k) (n k) p.val≤1/100 ∧
      (graph C D (N p) (V p) (W p) (b k) (n k) (δ k) p.val+
        relative C Crel C₁ C₂ C₃ D (V p) (b k) (n k) p.val)/
        (1-relative C Crel C₁ C₂ C₃ D (V p) (b k) (n k) p.val)≤β p := by
  apply Filter.eventually_all.mpr
  intro p
  have hf := SmoothScales.common_frame_budget (C:=C) hbpos hb hn hfloor hc (hF p) (hN p) D p.val hδ
  have hr := RelativeAsymptotics.common_relative_budget hbpos hb hn hfloor C Crel C₁ C₂ C₃ D (V p) p.val
  have hg := SmoothScales.common_graph_budget (C:=C) hbpos hb hn hfloor hc (hN p) (hV p) (hW p) D p.val hδ
  change Tendsto (fun k => relative C Crel C₁ C₂ C₃ D (V p) (b k) (n k) p.val) l (𝓝 0) at hr
  change Tendsto (fun k => graph C D (N p) (V p) (W p) (b k) (n k) (δ k) p.val) l (𝓝 0) at hg
  filter_upwards [hf,hr.eventually_le_const (by norm_num : (0:ℝ)<1/100),
    (SmoothScales.perturbed_graph_decay hg hr).eventually_le_const (hβ p)] with k hk hrk hgk
  exact ⟨hk,hrk,hgk⟩
end SmoothObstruction.EndpointBudget

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ShortScales
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.ScaleHierarchy

lemma lower_bound {b n p : ℝ} (hn : 1 ≤ n) (hp : 0 ≤ p)
    (hb : n ^ (-1 / 10 : ℝ) ≤ b) :
    n ^ (1 - p / 10) ≤ b ^ p * n := by
  have hnpos : 0 < n := by linarith
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _) hb hp
  rw [← Real.rpow_mul hnpos.le] at h
  calc
    n ^ (1-p/10) = n ^ ((-1/10:ℝ)*p+1) := by congr 1; ring
    _ = n ^ ((-1/10:ℝ)*p)*n := by rw [Real.rpow_add hnpos, Real.rpow_one]
    _ ≤ b^p*n := mul_le_mul_of_nonneg_right h hnpos.le

lemma square_dominates {b n p : ℝ} (hn : 1 ≤ n) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hb : n ^ (-1 / 10 : ℝ) ≤ b) : n ≤ (b ^ p * n)^2 := by
  have hnpos : 0 < n := by linarith
  calc
    n = n ^ (1:ℝ) := by simp
    _ ≤ n ^ ((1-p/10)*2) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    _ = (n^(1-p/10))^2 := by rw [Real.rpow_mul hnpos.le, Real.rpow_two]
    _ ≤ (b^p*n)^2 := pow_le_pow_left₀ (Real.rpow_nonneg hnpos.le _)
      (lower_bound hn hp hb) 2

lemma ratio_tendsto_zero {ι : Type*} {l : Filter ι} {b : ι → ℝ} {p q : ℝ}
    (hqp : p < q) (hbpos : ∀ᶠ k in l, 0 < b k) (hb : Tendsto b l (𝓝 0)) :
    Tendsto (fun k => b k ^ q / b k ^ p) l (𝓝 0) := by
  have h := ((Real.continuous_rpow_const (show 0 ≤ q-p by linarith)).tendsto 0).comp hb
  simp only [Real.zero_rpow (show q-p ≠ 0 by linarith)] at h
  apply h.congr'
  filter_upwards [hbpos] with k hk
  exact Real.rpow_sub hk q p

/-- General separated-power budget. The floor and the original time scale are
unchanged; every fixed polynomial cost and exponential `b^q n` cost is absorbed. -/
theorem polynomial_decay {ι : Type*} {l : Filter ι} {b n : ι → ℝ}
    {p q c C : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hqp : p < q) (hc : 0 < c)
    (hbpos : ∀ᶠ k in l, 0 < b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop)
    (hfloor : ∀ᶠ k in l, n k ^ (-1 / 10 : ℝ) ≤ b k) (m : ℕ) :
    Tendsto (fun k => n k ^ m * Real.exp (C * b k ^ q * n k - c * b k ^ p * n k))
      l (𝓝 0) := by
  have hn1 : ∀ᶠ k in l, 1 ≤ n k := hn.eventually (eventually_ge_atTop 1)
  have hsmall : ∀ᶠ k in l, C*(b k^q/b k^p) ≤ c/2 := by
    apply Tendsto.eventually_le_const (show (0:ℝ) < c/2 by linarith)
    simpa using (ratio_tendsto_zero hqp hbpos hb).const_mul C
  have hP : Tendsto (fun k => b k^p*n k) l atTop := by
    apply tendsto_atTop_mono' l ?_
      ((tendsto_rpow_atTop (show (0:ℝ)<1-p/10 by linarith)).comp hn)
    filter_upwards [hn1,hfloor] with k hk hf
    exact lower_bound hk hp hf
  have hzero := ((isLittleO_pow_exp_pos_mul_atTop (2*m) (show (0:ℝ) < c/2 by linarith)).tendsto_div_nhds_zero).comp hP
  have hzero' : Tendsto (fun k => (b k^p*n k)^(2*m)*Real.exp (-(c/2)*(b k^p*n k))) l (𝓝 0) := by
    change Tendsto (fun k => (b k^p*n k)^(2*m) / Real.exp ((c/2)*(b k^p*n k))) l (𝓝 0) at hzero
    simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_mul] using hzero
  apply squeeze_zero' _ _ hzero'
  · filter_upwards [hn1] with k hk
    exact mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le
  · filter_upwards [hn1,hfloor,hbpos,hsmall] with k hk hf hb hsmall
    have hbp := Real.rpow_pos_of_pos hb p
    have hCb : C*b k^q ≤ (c/2)*b k^p := by
      apply (div_le_iff₀ hbp).mp
      simpa only [mul_div_assoc] using hsmall
    have hexp : C*b k^q*n k-c*b k^p*n k ≤ -(c/2)*(b k^p*n k) := by
      have := mul_le_mul_of_nonneg_right hCb (show 0≤n k by linarith)
      nlinarith
    have hpow : n k^m ≤ (b k^p*n k)^(2*m) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by linarith) (square_dominates hk hp hp1 hf) m
    exact mul_le_mul hpow (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
      (pow_nonneg (mul_nonneg hbp.le (by linarith)) _)
end SmoothObstruction.ScaleHierarchy

namespace SmoothObstruction.ShortBin
lemma bvp_nonneg (K a : ℝ) (n : ℕ) : 0≤bvpInverseBound K a n := by
  have hU : 0≤bvpGrowth K a n := by unfold bvpGrowth; positivity
  unfold bvpInverseBound
  positivity

lemma bvp_cost {K a : ℝ} (n : ℕ) (hK : 0≤K) (ha : 0≤a) :
    bvpInverseBound K a n ≤ 1000000*((n:ℝ)+1)*Real.exp (18*K+8*a*n) := by
  let U := bvpGrowth K a n
  let D := (2*U+U^4)*(n+n : ℕ)+U^2
  have hU : 1≤U := by dsimp [U,bvpGrowth]; linarith [Real.exp_pos (2*K+a*n)]
  have hU0 := le_trans (by norm_num : (0:ℝ)≤1) hU
  have he : 1≤Real.exp (2*K+a*n) := Real.one_le_exp_iff.mpr (by positivity)
  have hUe : U≤3*Real.exp (2*K+a*n) := by dsimp [U,bvpGrowth]; linarith
  have hU4 : U≤U^4 := by simpa using pow_le_pow_right₀ hU (show 1≤4 by omega)
  have hU24 : U^2≤U^4 := pow_le_pow_right₀ hU (by omega)
  have hU41 : 1≤U^4 := one_le_pow₀ hU
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
  have hD : D≤7*((n:ℝ)+1)*U^4 := by
    have hg := mul_le_mul_of_nonneg_right (show 2*U+U^4≤3*U^4 by linarith)
      (show (0:ℝ)≤(n+n:ℕ) by positivity)
    dsimp [D]
    push_cast at *
    nlinarith
  have hD0 : 0≤D := by dsimp [D]; positivity
  have hfactor : 1+2*D≤15*((n:ℝ)+1)*U^4 := by nlinarith
  have heK : 1≤Real.exp (2*K) := Real.one_le_exp_iff.mpr (by positivity)
  have hDe : D≤7*((n:ℝ)+1)*Real.exp (2*K)*U^8 := by
    calc
      D ≤ 7*((n:ℝ)+1)*U^4 := hD
      _ ≤ 7*((n:ℝ)+1)*Real.exp (2*K)*U^8 := by
        have hp : U^4≤U^8 := pow_le_pow_right₀ hU (by omega)
        have hp' : U^4≤Real.exp (2*K)*U^8 := le_trans hp (le_mul_of_one_le_left (by positivity) heK)
        nlinarith [mul_le_mul_of_nonneg_left hp' (show 0≤7*((n:ℝ)+1) by positivity)]
  have hQ : bvpInverseBound K a n≤127*((n:ℝ)+1)*Real.exp (2*K)*U^8 := by
    have h₁ : (U+U^4)*(4*Real.exp (2*K))≤(2*U^4)*(4*Real.exp (2*K)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h₂ := mul_le_mul h₁ hfactor (show 0≤1+2*D by positivity)
      (show 0≤(2*U^4)*(4*Real.exp (2*K)) by positivity)
    change (U+U^4)*(4*Real.exp (2*K))*(1+2*D)+D≤_
    nlinarith [h₂,hDe]
  have hp := pow_le_pow_left₀ hU0 hUe 8
  have hUE : U^8≤6561*Real.exp (16*K+8*a*n) := by
    calc
      U^8 ≤ (3*Real.exp (2*K+a*n))^8 := hp
      _ = 6561*Real.exp (16*K+8*a*n) := by
        rw [mul_pow,←Real.exp_nat_mul]
        norm_num
        ring
  calc
    bvpInverseBound K a n ≤ 127*((n:ℝ)+1)*Real.exp (2*K)*U^8 := hQ
    _ ≤ 127*((n:ℝ)+1)*Real.exp (2*K)*(6561*Real.exp (16*K+8*a*n)) :=
      mul_le_mul_of_nonneg_left hUE (by positivity)
    _ = 833247*((n:ℝ)+1)*Real.exp (18*K+8*a*n) := by
      calc
        _ = 833247*((n:ℝ)+1)*(Real.exp (2*K)*Real.exp (16*K+8*a*n)) := by ring
        _ = _ := by rw [←Real.exp_add]; congr 2; ring
    _ ≤ 1000000*((n:ℝ)+1)*Real.exp (18*K+8*a*n) := by gcongr; norm_num
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ShortBin
open Filter Topology

/-- Explicit BVP cost is absorbed by the prescribed spatial exponent. -/
theorem bvp_decay {ι : Type*} {l : Filter ι} {b : ι → ℝ} {n : ι → ℕ}
    {K a : ι → ℝ} {p q c D : ℝ}
    (hp : 0≤p) (hp1 : p≤1) (hpq : p<q) (hc : 0 < c)
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (hK : ∀ᶠ k in l,0≤K k ∧ K k≤D*b k^q*n k)
    (ha : ∀ᶠ k in l,0≤a k ∧ a k≤D*b k^q) :
    Tendsto (fun k => bvpInverseBound (K k) (a k) (n k)*
      Real.exp (-c*b k^p*n k)) l (𝓝 0) := by
  have hz := (ScaleHierarchy.polynomial_decay (C:=26*D) hp hp1 hpq hc
    hbpos hb hn hfloor 1).const_mul 2000000
  simp only [pow_one,mul_zero] at hz
  have hn1 := hn.eventually (eventually_ge_atTop 1)
  apply squeeze_zero' (Filter.Eventually.of_forall fun k =>
    mul_nonneg (bvp_nonneg _ _ _) (Real.exp_pos _).le) _ hz
  filter_upwards [hK,ha,hn1] with k hK ha hn1
  have hexp : 18*K k+8*a k*n k≤26*D*b k^q*n k := by
    have hh := mul_le_mul_of_nonneg_right ha.2 (Nat.cast_nonneg (n k))
    nlinarith [hK.2]
  calc
    _ ≤ (1000000*((n k:ℝ)+1)*Real.exp (18*K k+8*a k*n k))*Real.exp (-c*b k^p*n k) :=
      mul_le_mul_of_nonneg_right (bvp_cost (n k) hK.1 ha.1) (Real.exp_pos _).le
    _ ≤ (1000000*(2*(n k:ℝ))*Real.exp (26*D*b k^q*n k))*Real.exp (-c*b k^p*n k) := by
      gcongr
      linarith
    _ = 2000000*((n k:ℝ)*Real.exp (26*D*b k^q*n k-c*b k^p*n k)) := by
      rw [sub_eq_add_neg,Real.exp_add]
      ring_nf

end SmoothObstruction.ShortBin

end

section

namespace SmoothObstruction.ShortBin
open Filter Topology
/-- Polynomial powers of the actual BVP inverse cost remain absorbable. -/
theorem bvp_power_decay {ι : Type*} {l : Filter ι} {b : ι → ℝ} {n : ι → ℕ}
    {K a : ι → ℝ} {p q c D J : ℝ}
    (hp : 0≤p) (hp1 : p≤1) (hpq : p<q) (hc : 0 < c)
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (hK : ∀ᶠ k in l,0≤K k ∧ K k≤D*b k^q*n k)
    (ha : ∀ᶠ k in l,0≤a k ∧ a k≤D*b k^q) (m : ℕ) :
    Tendsto (fun k => (bvpInverseBound (K k) (a k) (n k))^m *
      Real.exp (J*b k^q*n k-c*b k^p*n k)) l (𝓝 0) := by
  let c' := c/((m:ℝ)+1)
  have hc' : 0 < c' := div_pos hc (by positivity)
  have h₁ := (bvp_decay hp hp1 hpq hc' hbpos hb hn hfloor hK ha).pow m
  have h₂ := ScaleHierarchy.polynomial_decay (C:=J) hp hp1 hpq hc' hbpos hb hn hfloor 0
  simp only [pow_zero,one_mul] at h₂
  have h := h₁.mul h₂
  simp only [mul_zero] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro k
  dsimp only
  rw [mul_pow,←Real.exp_nat_mul,mul_assoc,←Real.exp_add]
  congr 2
  have he : c'*((m:ℝ)+1)=c := by dsimp only [c']; field_simp
  rw [←he]
  ring

/-- The sharp join radius and ideal-cell exchange error at the literal source
spatial scales. The error is measured after applying the inverse product basis. -/
theorem spatial_switch_limits {ι : Type*} {l : Filter ι} {b : ι → ℝ} {n : ι → ℕ}
    {ε : ι → ℝ} (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (hε : ∀ᶠ k in l,0≤ε k ∧ ε k≤Real.exp (-b k^(3/4:ℝ)*n k))
    (Dg A C₀ : ℝ) (hDg : 0≤Dg) (hA : 0≤A) :
    let B (k : ι) := Dg*(b k*n k)
    let g (k : ι) := b k^(1/2:ℝ)
    let r (k : ι) := Real.exp (-2*b k^(1/8:ℝ)*n k)
    let δ (k : ι) := Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k)
    let V (k : ι) := bvpInverseBound (B k) (A*g k) (n k)
    let ρ (k : ι) := 2*C₀*V k*r k
    let E (k : ι) := 4*Real.exp (2*B k)*(2*Real.exp (2*B k))*
      (ε k+2*Real.exp (2*B k)^2*Real.exp (-2*g k*n k))*(C₀*r k)+V k*C₀*(ρ k)^2
    Tendsto (fun k => ρ k/δ k) l (𝓝 0) ∧
      Tendsto (fun k => ρ k/Real.exp (-b k^(1/8:ℝ)*n k)) l (𝓝 0) ∧
      Tendsto ρ l (𝓝 0) ∧
      Tendsto (fun k => Real.sqrt 2*Real.exp (2*B k)*E k/r k) l (𝓝 0) := by
  intro B g r δ V ρ E
  let D := max Dg A
  have hD : 0≤D := hDg.trans (le_max_left _ _)
  have hK : ∀ᶠ k in l,0≤B k ∧ B k≤D*b k^(1/2:ℝ)*n k := by
    filter_upwards [hbpos,hb.eventually_le_const (by norm_num : (0:ℝ)<1)] with k hk hk1
    have hr : b k≤b k^(1/2:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hk hk1 (by norm_num : (1/2:ℝ)≤1)
    refine ⟨mul_nonneg hDg (mul_nonneg hk.le (Nat.cast_nonneg _)),?_⟩
    dsimp only [B]
    calc
      Dg*(b k*n k) = Dg*b k*n k := by ring
      _ ≤ D*b k^(1/2:ℝ)*n k := by gcongr; exact le_max_left _ _
  have ha : ∀ᶠ k in l,0≤A*g k ∧ A*g k≤D*b k^(1/2:ℝ) := by
    filter_upwards [hbpos] with k hk
    exact ⟨mul_nonneg hA (Real.rpow_nonneg hk.le _),
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hk.le _)⟩
  have hdec (c : ℝ) (hc : 0 < c) := bvp_decay (p:=1/8) (q:=1/2) (c:=c)
    (by norm_num) (by norm_num) (by norm_num) hc hbpos hb hn hfloor hK ha
  have hρδ := (hdec (1/2) (by norm_num)).const_mul (2*C₀)
  have hρh := (hdec 1 (by norm_num)).const_mul (2*C₀)
  have hρ0 := (hdec 2 (by norm_num)).const_mul (2*C₀)
  simp only [mul_zero] at hρδ hρh hρ0
  have hfirst : Tendsto (fun k => Real.exp (6*B k)*ε k) l (𝓝 0) := by
    have hh := ScaleHierarchy.polynomial_decay (p:=3/4) (q:=1) (c:=1) (C:=6*Dg)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
    simp only [pow_zero,one_mul,Real.rpow_one] at hh
    apply squeeze_zero' _ _ hh
    · filter_upwards [hε] with k hk; exact mul_nonneg (Real.exp_pos _).le hk.1
    · filter_upwards [hε] with k hk
      calc
        _ ≤ Real.exp (6*B k)*Real.exp (-b k^(3/4:ℝ)*n k) := mul_le_mul_of_nonneg_left hk.2 (Real.exp_pos _).le
        _ = _ := by rw [←Real.exp_add]; congr 1; dsimp [B]; ring
  have hsecond := ScaleHierarchy.polynomial_decay (p:=1/2) (q:=1) (c:=2) (C:=10*Dg)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
  simp only [pow_zero,one_mul,Real.rpow_one] at hsecond
  have hthird : Tendsto (fun k => V k^3*Real.exp (2*B k-2*b k^(1/8:ℝ)*n k)) l (𝓝 0) := by
    have hh := bvp_power_decay (p:=1/8) (q:=1/2) (c:=2) (J:=2*Dg)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor hK ha 3
    apply squeeze_zero' (Filter.Eventually.of_forall fun k => mul_nonneg (pow_nonneg (bvp_nonneg _ _ _) _) (Real.exp_pos _).le) _ hh
    filter_upwards [hbpos,hb.eventually_le_const (by norm_num : (0:ℝ)<1)] with k hk hk1
    have hr : b k≤b k^(1/2:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hk hk1 (by norm_num : (1/2:ℝ)≤1)
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg (bvp_nonneg _ _ _) _)
    dsimp only [B]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hDg) (Nat.cast_nonneg (n k))
    nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · apply hρδ.congr'; apply Filter.Eventually.of_forall; intro k
    have he : Real.exp (-(1/2:ℝ)*b k^(1/8:ℝ)*n k)=
        Real.exp (-2*b k^(1/8:ℝ)*n k)/Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k) := by
      rw [←Real.exp_sub]; congr 1; ring
    dsimp only [ρ,δ,r,V]
    rw [he]
    ring
  · apply hρh.congr'; apply Filter.Eventually.of_forall; intro k
    have he : Real.exp (-1*b k^(1/8:ℝ)*n k)=
        Real.exp (-2*b k^(1/8:ℝ)*n k)/Real.exp (-b k^(1/8:ℝ)*n k) := by
      rw [←Real.exp_sub]; congr 1; ring
    dsimp only [ρ,r,V]
    rw [he]
    ring
  · simpa only [ρ,r,V,mul_assoc] using hρ0
  · have hh := ((hfirst.const_mul (8*Real.sqrt 2*C₀)).add
      (hsecond.const_mul (16*Real.sqrt 2*C₀))).add (hthird.const_mul (4*Real.sqrt 2*C₀^3))
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'; apply Filter.Eventually.of_forall; intro k
    have he (m : ℕ) : Real.exp ((m:ℝ)*(2*B k))=Real.exp (2*B k)^m := Real.exp_nat_mul _ _
    have he6 : Real.exp (6*B k)=Real.exp (2*B k)^3 := by convert he 3 using 1; ring_nf
    have he10 : Real.exp (10*Dg*b k*n k)=Real.exp (2*B k)^5 := by
      convert he 5 using 1; dsimp only [B]; ring_nf
    dsimp only [E,ρ,r,g]
    rw [Real.exp_sub,he6,he10, Real.exp_sub]
    simp only [neg_mul,Real.exp_neg]
    field_simp
    ring
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ShortBin
open Filter Topology
/-- Scalar hypotheses of the genuine switch, at the unchanged source scales.
Both grid widths are fixed multiples of the original h0 and r. -/
theorem spatial_ready {ι : Type*} {l : Filter ι} {b : ι → ℝ} {n : ι → ℕ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (Dg A C₀ C₁ Cg K₀F K₀B r₀ rg σ r₁ rμ Ac Ap : ℝ)
    (hDg : 0≤Dg) (hA : 0≤A) (hC₀ : 1≤C₀)
    (hr₀ : 0 < r₀) (hrg : 0 < rg) (hσ : 0<σ) (hr₁ : 0 < r₁) (hrμ : 0 < rμ)
    (hAc : 0<Ac) (hAp : 0<Ap) :
    let B (k : ι) := Dg*(b k*n k)
    let g (k : ι) := b k^(1/2:ℝ)
    let ε (k : ι) := Real.exp (-b k^(3/4:ℝ)*n k)
    let h₀ (k : ι) := Real.exp (-b k^(1/8:ℝ)*n k)
    let r (k : ι) := Real.exp (-2*b k^(1/8:ℝ)*n k)
    let δ (k : ι) := Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k)
    let V (k : ι) := bvpInverseBound (B k) (A*g k) (n k)
    let ρ (k : ι) := 2*C₀*V k*r k
    let E (k : ι) := 4*Real.exp (2*B k)*(2*Real.exp (2*B k))*
      (ε k+2*Real.exp (2*B k)^2*Real.exp (-2*g k*n k))*(C₀*r k)+V k*C₀*(ρ k)^2
    ∀ᶠ k in l,1≤b k*n k ∧ ε k≤1/2 ∧ Real.exp (2*B k)*(2*ε k)≤1/2 ∧
      (2*Real.exp (2*B k))*(2*(2*Real.exp (2*B k)^2*Real.exp (-2*g k*n k)))≤1/2 ∧
      δ k ≤ r₀ ∧ δ k ≤ rg ∧ ρ k≤δ k ∧ ρ k≤σ ∧ ρ k≤(h₀ k/Ac)/4 ∧ ρ k ≤ r₁ ∧
      C₁*ρ k≤δ k ∧ Cg*ρ k<δ k ∧ K₀F*δ k≤1 ∧ K₀B*δ k≤1 ∧
      Real.sqrt 2*Real.exp (2*B k)*E k≤(r k/Ap)/4 ∧
      V k*C₀*δ k≤1/4 ∧ V k*C₀*r k≤δ k/4 ∧ r k < rμ ∧ δ k≤h₀ k := by
  intro B g ε h₀ r δ V ρ E
  have hεenv : ∀ᶠ k in l,0≤ε k ∧ ε k≤Real.exp (-b k^(3/4:ℝ)*n k) :=
    Filter.Eventually.of_forall fun k => ⟨(Real.exp_pos _).le,le_rfl⟩
  obtain ⟨hρδ,hρh,hρ,hE⟩ := spatial_switch_limits hbpos hb hn hfloor hεenv Dg A C₀ hDg hA
  have hdec (p c : ℝ) (hp : 0≤p) (hp1 : p≤1) (hpq : p<1) (hc : 0 < c) :
      Tendsto (fun k => Real.exp (-c*b k^p*n k)) l (𝓝 0) := by
    have hh := ScaleHierarchy.polynomial_decay (q:=1) (C:=0) hp hp1 hpq hc hbpos hb hn hfloor 0
    simpa only [pow_zero,one_mul,zero_mul,zero_sub,neg_mul] using hh
  have hδ0 : Tendsto δ l (𝓝 0) := hdec (1/8) (3/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hr0 : Tendsto r l (𝓝 0) := hdec (1/8) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hε0 : Tendsto ε l (𝓝 0) := by
    simpa only [neg_one_mul] using hdec (3/4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsmall : Tendsto (fun k => Real.exp (2*B k)*(2*ε k)) l (𝓝 0) := by
    have hh := ScaleHierarchy.polynomial_decay (p:=3/4) (q:=1) (c:=1) (C:=2*Dg)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
    simp only [pow_zero,one_mul,Real.rpow_one] at hh
    have ht := hh.const_mul 2
    simp only [mul_zero] at ht
    apply ht.congr'; apply Filter.Eventually.of_forall; intro k
    dsimp only [B,ε]
    rw [mul_left_comm,←Real.exp_add]
    congr 2; ring
  have hgap : Tendsto (fun k => (2*Real.exp (2*B k))*(2*(2*Real.exp (2*B k)^2*Real.exp (-2*g k*n k)))) l (𝓝 0) := by
    have hh := ScaleHierarchy.polynomial_decay (p:=1/2) (q:=1) (c:=2) (C:=6*Dg)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
    simp only [pow_zero,one_mul,Real.rpow_one] at hh
    have ht := hh.const_mul 8
    simp only [mul_zero] at ht
    apply ht.congr'; apply Filter.Eventually.of_forall; intro k
    have he : Real.exp (2*B k)*Real.exp (2*B k)^2*Real.exp (-2*g k*n k)=
        Real.exp (6*Dg*b k*n k-2*b k^(1/2:ℝ)*n k) := by
      rw [←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]
      congr 1; dsimp only [B,g]; ring
    dsimp only
    rw [show (2*Real.exp (2*B k))*(2*(2*Real.exp (2*B k)^2*Real.exp (-2*g k*n k)))=
      8*(Real.exp (2*B k)*Real.exp (2*B k)^2*Real.exp (-2*g k*n k)) by ring,he]
  have hCρδ : Tendsto (fun k => C₁*(ρ k/δ k)) l (𝓝 0) := by simpa only [mul_zero] using hρδ.const_mul C₁
  have hCgρδ : Tendsto (fun k => Cg*(ρ k/δ k)) l (𝓝 0) := by simpa only [mul_zero] using hρδ.const_mul Cg
  have hKFδ : Tendsto (fun k => K₀F*δ k) l (𝓝 0) := by simpa only [mul_zero] using hδ0.const_mul K₀F
  have hKBδ : Tendsto (fun k => K₀B*δ k) l (𝓝 0) := by simpa only [mul_zero] using hδ0.const_mul K₀B
  filter_upwards [hbpos,hfloor,hn.eventually (eventually_ge_atTop (1:ℝ)),
    hε0.eventually_le_const (by norm_num : (0:ℝ)<1/2),
    hsmall.eventually_le_const (by norm_num : (0:ℝ)<1/2),
    hgap.eventually_le_const (by norm_num : (0:ℝ)<1/2),
    hδ0.eventually_le_const hr₀,hδ0.eventually_le_const hrg,
    hρδ.eventually_le_const (by norm_num : (0:ℝ)<1/2),hρ.eventually_le_const hσ,
    hρh.eventually_le_const (by positivity : (0:ℝ)<1/(4*Ac)),hρ.eventually_le_const hr₁,
    hCρδ.eventually_le_const (by norm_num : (0:ℝ)<1),hCgρδ.eventually_lt_const (by norm_num : (0:ℝ)<1),
    hKFδ.eventually_le_const (by norm_num : (0:ℝ)<1),hKBδ.eventually_le_const (by norm_num : (0:ℝ)<1),
    hE.eventually_le_const (by positivity : (0:ℝ)<1/(4*Ap)),hr0.eventually_lt_const hrμ]
    with k hbpos hf hn1 heps hsmall hgap hδr hδrg hρδ hρσ hρh hρr hCρ hCgρ hKF hKB hE hrμ
  have hδpos : 0<δ k := Real.exp_pos _
  have hrpos : 0 < r k := Real.exp_pos _
  have hhpos : 0<h₀ k := Real.exp_pos _
  have hBn : 0≤b k^(1/8:ℝ)*n k := by positivity
  have hδsq : δ k*δ k ≤ r k := by
    dsimp only [δ,r]; rw [←Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith only [hBn]
  have hρhalf : ρ k≤δ k/2 := by
    have hh := (div_le_iff₀ hδpos).mp hρδ
    linarith
  have hVC₀ : 0≤V k*C₀ := mul_nonneg (bvp_nonneg _ _ _) (by linarith)
  have hdata : V k*C₀*r k≤δ k/4 := by dsimp only [ρ] at hρhalf; nlinarith only [hρhalf]
  have hcontract : V k*C₀*δ k≤1/4 := by
    have hh := mul_le_mul_of_nonneg_left hδsq hVC₀
    have hmul : (V k*C₀*δ k)*δ k≤(1/4:ℝ)*δ k := by nlinarith only [hh,hdata]
    exact (mul_le_mul_iff_left₀ hδpos).mp (by simpa only [mul_comm] using hmul)
  have hbn : 1≤b k*n k := by
    have hs := ScaleHierarchy.lower_bound (p:=1) hn1 (by norm_num) hf
    have hp := Real.one_le_rpow hn1 (by norm_num : (0:ℝ)≤1-(1:ℝ)/10)
    simpa only [Real.rpow_one] using hp.trans hs
  refine ⟨hbn,heps,hsmall,hgap,hδr,hδrg,by linarith,hρσ,?_,hρr,?_,?_,hKF,hKB,?_,hcontract,hdata,hrμ,?_⟩
  · have hh := (div_le_iff₀ hhpos).mp hρh
    calc
      _ ≤ (1/(4*Ac))*h₀ k := hh
      _ = (h₀ k/Ac)/4 := by ring
  · rw [←mul_div_assoc] at hCρ
    exact (div_le_iff₀ hδpos).mp hCρ |>.trans_eq (one_mul _)
  · rw [←mul_div_assoc] at hCgρ
    exact (div_lt_iff₀ hδpos).mp hCgρ |>.trans_eq (one_mul _)
  · have hh := (div_le_iff₀ hrpos).mp hE
    calc
      _ ≤ (1/(4*Ap))*r k := hh
      _ = (r k/Ap)/4 := by ring
  · dsimp only [δ,h₀]; apply Real.exp_le_exp.mpr; nlinarith only [hBn]
end SmoothObstruction.ShortBin

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SwitchScales
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.ManifoldCoordinates
open Set MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]
open ChartDensity

/-- The actual full finite product partition is constructed from one original
gauge reference per active starting bin. Wall strips are charged to the ORIGINAL
measure. No endpoint or orbit chart code is included in the cell alphabet. The
recovery assertion is precisely the ideal exchange needed by both joins. -/
theorem finite_product_partition_uniform (μ : Measure M) [IsProbabilityMeasure μ]
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (c : M → ι) (hc : ∀ x,x∈K (c x)) :
    ∃ D : ℝ,1≤D ∧ ∀ (C : Type*) [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] (P : M → C),Measurable P → ∀ (chart : C → ι),
      (∀ x,chart (P x)=c x) → ∀ (G : Set M) (n : ℕ) (B R : ℝ),0≤B →
      ∀ (A : ∀ x:G,BilateralGauge I S a c n B R x) (T : G → Finset (Fin d))
        (δ : ℝ),0<δ → ∀ N : ℕ,0<N →
      let H₀ := Real.sqrt 2*Real.exp (2*B)
      let m := ⌈H₀*D/(δ*N)+1⌉₊
      ∃ (L : M → C × (Fin d → Fin (2*m+1))) (W : Set M),
        Measurable L ∧ MeasurableSet W ∧ μ.real W≤(d:ℝ)/N ∧
        (∀ x,(L x).1=P x) ∧
        (∀ x y,L x=L y →
          ‖coordinates I (a (c x)) x-coordinates I (a (c x)) y‖≤
            Real.sqrt 2*((d:ℝ)+1)*(δ*N)) ∧
        (∀ (x y z : M) (hx : x∈G),L x=L y → x∉W → y∉W → P z=P x →
          let ref : G := (reference P G (key P G ⟨x,hx⟩)).val
          H₀*‖coordinates I (a (c x)) z-(coordinates I (a (c x)) x+
            (((A ref).forward I S a c).splitting (T ref)ᶜ).slow 0
              (coordinates I (a (c x)) y-coordinates I (a (c x)) x))‖≤δ/4 →
          L z=L x) ∧
        Fintype.card (C × (Fin d → Fin (2*m+1)))=Fintype.card C*(2*m+1)^d := by
  obtain ⟨D,hD,hbound⟩ := selected_coordinate_bound I a K hK hKU c hc
  refine ⟨D,hD,?_⟩
  intro C _ _ _ P hP chart hchart G n B R hB A T δ hδ N hN H₀ m
  let ref (Q : Active P G) : G := (reference P G Q).val
  obtain ⟨E,hE,hEi,hmix⟩ := product_coordinates P G hB
    (fun Q => (A (ref Q)).forward I S a c) (fun Q => (T (ref Q))ᶜ)
  let φ (Q : C) (x : M) := coordinates I (a (chart Q)) x
  have hb (x : M) : ‖φ (P x) x‖≤D := by simpa only [φ,hchart] using hbound x
  obtain ⟨L,W,hL,hW,hWm,hLP,hdiam,hstable,hcard⟩ := ProductCells.exists_cells μ P hP φ
    (fun Q => measurable_coordinates I (a (chart Q))) E (show 0≤D by linarith)
    (show 0≤H₀ by dsimp [H₀]; positivity) (Real.sqrt_nonneg _) hδ hb hEi hE hN
  refine ⟨L,W,hL,hW,hWm,hLP,?_,?_,hcard⟩
  · intro x y hxy
    simpa only [φ,hchart] using hdiam x y hxy
  · intro x y z hx hxy hxW hyW hz ref₀ herror
    apply hstable x y z hxy hxW hyW hz
    let Q : Active P G := key P G ⟨x,hx⟩
    let ideal := φ (P x) x+(((A (ref Q)).forward I S a c).splitting (T (ref Q))ᶜ).slow 0
      (φ (P x) y-φ (P x) x)
    have herr : H₀*‖φ (P x) z-ideal‖≤δ/4 := by
      simpa only [ideal,φ,hchart,ref,Q] using herror
    have he (i : Fin d) : |((E (P x)).symm (φ (P x) z)) i-((E (P x)).symm ideal) i|≤δ/4 := by
      calc
        _ = ‖(((E (P x)).symm (φ (P x) z-ideal)) i)‖ := by rw [map_sub]; rfl
        _ ≤ ‖(E (P x)).symm (φ (P x) z-ideal)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖(E (P x)).symm.toContinuousLinearMap‖*‖φ (P x) z-ideal‖ :=
          (E (P x)).symm.toContinuousLinearMap.le_opNorm _
        _ ≤ H₀*‖φ (P x) z-ideal‖ := mul_le_mul_of_nonneg_right (hEi _) (norm_nonneg _)
        _ ≤ δ/4 := herr
    intro i
    have hh := hmix Q (φ (P x) x) (φ (P x) y) i
    change ((E (P x)).symm ideal) i=((E (P x)).symm (φ (P x) x)) i ∨
      ((E (P x)).symm ideal) i=((E (P x)).symm (φ (P x) y)) i at hh
    rcases hh with hh|hh
    · exact Or.inl (by simpa only [hh] using he i)
    · exact Or.inr (by simpa only [hh] using he i)
end SmoothObstruction.ManifoldCoordinates

end

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.SwitchScales
open Filter Topology
open scoped Real

lemma ceil_bounds {b n : ℝ} (hn : 1≤n) (hfloor : n^(-1/10:ℝ)≤b) :
    b^(1/4:ℝ)*n≤(shortTime b n : ℝ) ∧ (shortTime b n : ℝ)≤2*b^(1/4:ℝ)*n := by
  have hl := ScaleHierarchy.lower_bound (p:=1/4) hn (by norm_num) hfloor
  have hp : 1≤b^(1/4:ℝ)*n := by
    apply le_trans _ hl
    exact Real.one_le_rpow hn (by norm_num)
  refine ⟨Nat.le_ceil _,?_⟩
  have hh := Nat.ceil_lt_add_one (show 0≤b^(1/4:ℝ)*n by linarith)
  change (shortTime b n : ℝ)<b^(1/4:ℝ)*n+1 at hh
  linarith

lemma gap_short_lower {b n : ℝ} (hb : 0<b) :
    shortSignal b n≤gap b*(shortTime b n : ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil (b^(1/4:ℝ)*n))
    (Real.rpow_nonneg hb.le (1/2:ℝ))
  have he : b^(1/2:ℝ)*(b^(1/4:ℝ)*n)=shortSignal b n := by
    rw [←mul_assoc,←Real.rpow_add hb]; norm_num [shortSignal]
  rwa [he] at hh

lemma short_eventually {ι : Type*} {l : Filter ι} {b n : ι → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k) :
    ∀ᶠ k in l,(shortTime (b k) (n k) : ℝ)≤n k ∧ 0<b k ∧ b k≤1 ∧ 1≤n k ∧
      (shortTime (b k) (n k) : ℝ)≤2*b k^(1/4:ℝ)*n k := by
  have hr : Tendsto (fun k => b k^(1/4:ℝ)) l (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1/4:ℝ)≠0),Function.comp_def] using
      ((Real.continuous_rpow_const (show (0:ℝ)≤1/4 by norm_num)).tendsto 0).comp hb
  filter_upwards [hbpos,hn.eventually (eventually_ge_atTop 1),
    hb.eventually_le_const (by norm_num : (0:ℝ)<1),
    hr.eventually_le_const (by norm_num : (0:ℝ)<1/2),hfloor] with k hp hn1 hb1 hr1 hf
  have hL := (ceil_bounds hn1 hf).2
  refine ⟨hL.trans ?_,hp,hb1,hn1,hL⟩
  nlinarith [mul_le_mul_of_nonneg_right hr1 (show 0≤n k by linarith)]

/-- The genuine short-product noise with its ceiling time is swallowed by
one original spatial exponent, even after a full short-gap exponential cost. -/
theorem short_noise_decay {ι : Type*} {l : Filter ι} {b n : ι → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {J C : ℝ} (hJ : 0≤J) (hC : 0≤C) :
    Tendsto (fun k => n k*Real.exp (J*(shortTime (b k) (n k):ℝ)+C*b k*n k+
      shortSignal (b k) (n k)-root (b k)*n k)) l (𝓝 0) := by
  have hz := ScaleHierarchy.polynomial_decay (p:=1/8) (q:=1/4) (c:=1)
    (C:=2*J+C+1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hbpos hb hn hfloor 1
  simp only [pow_one,one_mul] at hz
  apply squeeze_zero' _ _ hz
  · filter_upwards [hn.eventually (eventually_ge_atTop 0)] with k hk
    exact mul_nonneg hk (Real.exp_pos _).le
  · filter_upwards [short_eventually hbpos hb hn hfloor] with k hk
    have hbq : b k≤b k^(1/4:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hk.2.1 hk.2.2.1
        (show (1/4:ℝ)≤1 by norm_num)
    have hb3 : b k^(3/4:ℝ)≤b k^(1/4:ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hk.2.1 hk.2.2.1 (by norm_num)
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith [hk.2.2.2.1])
    have h₁ := mul_le_mul_of_nonneg_left hk.2.2.2.2 hJ
    have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbq hC)
      (show 0≤n k by linarith [hk.2.2.2.1])
    have h₃ := mul_le_mul_of_nonneg_right hb3 (show 0≤n k by linarith [hk.2.2.2.1])
    dsimp [shortSignal,root]
    nlinarith

/-- All common-bin projector errors, including the true product difference
`L C C^(2L) h0`, are exponentially small at the authentic gap×time scale. -/
theorem projector_budget {ι : Type*} {l : Filter ι} {b n : ι → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {C D A : ℝ} (hC : 1≤C) (hD : 0≤D) (hA : 0≤A) :
    let L (k : ι) := shortTime (b k) (n k)
    let K (k : ι) := D*b k*n k
    let noise (k : ι) := (L k:ℝ)*C*C^(2*L k)*Real.exp (-root (b k)*n k)
    let err (k : ι) := Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)+
      noise k*Real.exp (A*gap (b k)*(L k:ℝ)+2*K k)
    ∀ᶠ k in l,3*err k≤Real.exp (-shortSignal (b k) (n k)) := by
  intro L K noise err
  have hlog : 0≤Real.log C := Real.log_nonneg hC
  have hz₁ := ScaleHierarchy.polynomial_decay (p:=3/4) (q:=1) (c:=1) (C:=4*D)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
  simp only [pow_zero,one_mul,Real.rpow_one] at hz₁
  have hz₂ := (short_noise_decay hbpos hb hn hfloor
    (J:=2*Real.log C+A) (C:=2*D) (by positivity) (by positivity)).const_mul C
  simp only [mul_zero] at hz₂
  have hz : Tendsto (fun k => 3*(Real.exp (4*D*b k*n k-shortSignal (b k) (n k))+
      C*(n k*Real.exp ((2*Real.log C+A)*(L k:ℝ)+2*D*b k*n k+
        shortSignal (b k) (n k)-root (b k)*n k)))) l (𝓝 0) := by
    simpa only [add_zero,mul_zero,shortSignal,L] using (hz₁.add hz₂).const_mul 3
  filter_upwards [short_eventually hbpos hb hn hfloor,
    hz.eventually_le_const (by norm_num : (0:ℝ)<1)] with k hk hzbound
  have hg : gap (b k)≤1 := Real.rpow_le_one hk.2.1.le hk.2.2.1 (by norm_num)
  have hnp : 0≤n k := by linarith [hk.2.2.2.1]
  have hL : 0≤(L k:ℝ) := Nat.cast_nonneg _
  have heC : C^(2*L k)=Real.exp (2*Real.log C*(L k:ℝ)) := by
    rw [show 2*Real.log C*(L k:ℝ)=((2*L k:ℕ):ℝ)*Real.log C by push_cast; ring,
      Real.exp_nat_mul,Real.exp_log (by linarith : 0<C)]
  have hfirst : Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)*
      Real.exp (shortSignal (b k) (n k))≤
      Real.exp (4*D*b k*n k-shortSignal (b k) (n k)) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := gap_short_lower (n:=n k) hk.2.1
    dsimp only [K,L]
    linarith
  have hsecond : noise k*Real.exp (A*gap (b k)*(L k:ℝ)+2*K k)*
      Real.exp (shortSignal (b k) (n k))≤
      C*(n k*Real.exp ((2*Real.log C+A)*(L k:ℝ)+2*D*b k*n k+
        shortSignal (b k) (n k)-root (b k)*n k)) := by
    dsimp only [noise]
    rw [heC]
    have he : (L k:ℝ)*C*Real.exp (2*Real.log C*(L k:ℝ))*Real.exp (-root (b k)*n k)*
        Real.exp (A*gap (b k)*(L k:ℝ)+2*K k)*Real.exp (shortSignal (b k) (n k))=
        C*((L k:ℝ)*Real.exp (2*Real.log C*(L k:ℝ)-root (b k)*n k+
          (A*gap (b k)*(L k:ℝ)+2*K k)+shortSignal (b k) (n k))) := by
      simp only [sub_eq_add_neg,neg_mul,Real.exp_add,Real.exp_neg]
      ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by linarith : 0≤C)
    apply mul_le_mul hk.1 (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hnp
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hA) hL
    dsimp only [K]
    nlinarith
  have hbound : 3*err k*Real.exp (shortSignal (b k) (n k))≤1 := by
    dsimp only [err]
    have hh := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num : (0:ℝ)≤3)
    calc
      _ = 3*(Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)*Real.exp (shortSignal (b k) (n k))+
        noise k*Real.exp (A*gap (b k)*(L k:ℝ)+2*K k)*Real.exp (shortSignal (b k) (n k))) := by ring
      _ ≤ _ := hh
      _ ≤ 1 := hzbound
  have he : Real.exp (-shortSignal (b k) (n k))*Real.exp (shortSignal (b k) (n k))=1 := by
    rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
  exact (mul_le_mul_iff_left₀ (Real.exp_pos _)).mp (hbound.trans_eq he.symm)
end SmoothObstruction.SwitchScales

end

section

namespace SmoothObstruction.SwitchScales
open Filter Topology
/-- A simultaneous usable envelope for all starting/endpoint bin estimates.
The short time is still the source ceiling, not an adjustable subsequence. -/
theorem reference_budget {ι : Type*} {l : Filter ι} {b n : ι → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {C D A r : ℝ} (hC : 1≤C) (hD : 0≤D) (hA : 0≤A) (hr : 0 < r) :
    let L (k : ι) := shortTime (b k) (n k)
    let K (k : ι) := D*b k*n k
    let h (k : ι) := Real.exp (-root (b k)*n k)
    let noise (k : ι) := (L k:ℝ)*C*C^(2*L k)*h k
    let err (k : ι) := Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)+
      noise k*Real.exp (A*gap (b k)*(L k:ℝ)+2*K k)
    ∀ᶠ k in l,(L k:ℝ)≤n k ∧ 1≤(L k:ℝ) ∧
      C^(L k)*h k ≤ r ∧ noise k<Real.exp (-2*K k)/2 ∧
      Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)≤1/2 ∧ err k≤1/2 ∧
      3*err k≤Real.exp (-shortSignal (b k) (n k)) ∧
      Real.exp (-shortSignal (b k) (n k))≤1/2 := by
  intro L K h noise err
  have he := ScaleHierarchy.polynomial_decay (p:=3/4) (q:=1) (c:=1) (C:=0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbpos hb hn hfloor 0
  simp only [pow_zero,one_mul,zero_mul,zero_sub] at he
  have he' : Tendsto (fun k => Real.exp (-shortSignal (b k) (n k))) l (𝓝 0) := by
    simpa only [shortSignal,neg_mul] using he
  filter_upwards [projector_budget hbpos hb hn hfloor hC hD hA,
    short_eventually hbpos hb hn hfloor,hfloor,
    he'.eventually_le_const (lt_min (by norm_num : (0:ℝ)<1/4) hr)] with k hbudget ht hf he
  have hL : 1≤(L k:ℝ) := by
    have hh := ScaleHierarchy.lower_bound (p:=1/4) ht.2.2.2.1 (by norm_num) hf
    have hrp := Real.one_le_rpow ht.2.2.2.1 (by norm_num : (0:ℝ)≤1-(1/4:ℝ)/10)
    exact (hrp.trans hh).trans (Nat.le_ceil _)
  have hK : 0≤K k := mul_nonneg (mul_nonneg hD ht.2.1.le) (by linarith [ht.2.2.2.1])
  have hg : 0≤gap (b k) := Real.rpow_nonneg ht.2.1.le _
  have hnz : 0≤noise k := by dsimp only [noise,h]; positivity
  have hLeft : Real.exp (-2*gap (b k)*(L k:ℝ)+4*K k)≤err k := by
    exact le_add_of_nonneg_right (mul_nonneg hnz (Real.exp_pos _).le)
  have hnoise : noise k≤err k := by
    have hex : 1≤Real.exp (A*gap (b k)*(L k:ℝ)+2*K k) := Real.one_le_exp_iff.mpr (by positivity)
    have hh := mul_le_mul_of_nonneg_left hex hnz
    dsimp only [err]; nlinarith [Real.exp_pos (-2*gap (b k)*(L k:ℝ)+4*K k)]
  have hne : noise k*Real.exp (2*K k)≤err k := by
    have hex : Real.exp (2*K k)≤Real.exp (A*gap (b k)*(L k:ℝ)+2*K k) := Real.exp_le_exp.mpr (le_add_of_nonneg_left (mul_nonneg (mul_nonneg hA hg) (Nat.cast_nonneg _)))
    have hh := mul_le_mul_of_nonneg_left hex hnz
    dsimp only [err]; linarith [Real.exp_pos (-2*gap (b k)*(L k:ℝ)+4*K k)]
  have herr : err k≤1/4 := by
    have h := he.trans (min_le_left _ _)
    have herrpos : 0≤err k := (Real.exp_pos _).le.trans hLeft
    linarith
  refine ⟨ht.1,hL,?_,?_,hLeft.trans (by linarith),by linarith,hbudget,he.trans (by linarith [min_le_left (1/4:ℝ) r])⟩
  · have hp : C^(L k)≤C^(2*L k) := pow_le_pow_right₀ hC (by omega)
    have hc : 1≤(L k:ℝ)*C := one_le_mul_of_one_le_of_one_le hL hC
    have hn : C^(L k)*h k≤noise k := by
      dsimp only [noise]
      calc
        _ ≤ C^(2*L k)*h k := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ ≤ ((L k:ℝ)*C)*C^(2*L k)*h k := by
          have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg (pow_nonneg (by linarith : 0≤C) (2*L k)) (show 0≤h k from (Real.exp_pos _).le))
          simpa only [one_mul,mul_assoc] using hh
    have hre : Real.exp (-shortSignal (b k) (n k)) ≤ r := he.trans (min_le_right _ _)
    have herrpos : 0≤err k := (Real.exp_pos _).le.trans hLeft
    exact hn.trans (hnoise.trans (by linarith))
  · have hmul := mul_lt_mul_of_pos_right (show noise k*Real.exp (2*K k)<1/2 by linarith)
      (Real.exp_pos (-2*K k))
    have heq : Real.exp (2*K k)*Real.exp (-2*K k)=1 := by rw [←Real.exp_add]; simp
    calc
      _ = (noise k*Real.exp (2*K k))*Real.exp (-2*K k) := by rw [mul_assoc,heq,mul_one]
      _ < _ := hmul
      _ = _ := by ring
end SmoothObstruction.SwitchScales

namespace SmoothObstruction.SwitchScales
open Filter Topology

theorem refNoise_nonneg {C h : ℝ} (hC : 0≤C) (hh : 0≤h) (N : ℕ) :
    0 ≤ refNoise C N h := by unfold refNoise; positivity

theorem refNoise_mono {C D h : ℝ} {N : ℕ} (hC : 0≤C) (hCD : C≤D) (hh : 0≤h) :
    refNoise C N h ≤ refNoise D N h := by
  have hD : 0≤D := hC.trans hCD
  apply mul_le_mul_of_nonneg_right _ hh
  apply mul_le_mul (mul_le_mul_of_nonneg_left hCD (Nat.cast_nonneg N))
    (pow_le_pow_left₀ hC hCD (2*N)) (pow_nonneg hC _) (by positivity)

theorem refNoise_add_le {C₁ C₂ C h : ℝ} {N : ℕ}
    (h₁ : 0≤C₁) (h₂ : 0≤C₂) (hC : C₁+C₂≤C) (hh : 0≤h) :
    refNoise C₁ N h+refNoise C₂ N h ≤ refNoise C N h := by
  have hc₁ : C₁≤C := by linarith
  have hc₂ : C₂≤C := by linarith
  have hpow₁ := pow_le_pow_left₀ h₁ hc₁ (2*N)
  have hpow₂ := pow_le_pow_left₀ h₂ hc₂ (2*N)
  calc
    _ ≤ (N:ℝ)*C₁*C^(2*N)*h+(N:ℝ)*C₂*C^(2*N)*h := by
      exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow₁ (by positivity)) hh)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow₂ (by positivity)) hh)
    _ = (N:ℝ)*(C₁+C₂)*C^(2*N)*h := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hh
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg N)) (pow_nonneg (by linarith) _)

theorem refError_mono {K₀ K A g noise₀ noise : ℝ} {N : ℕ}
    (hK : K₀≤K) (hn : 0≤noise₀) (hnoise : noise₀≤noise) :
    refError K₀ A g N noise₀ ≤ refError K A g N noise := by
  apply add_le_add (Real.exp_le_exp.mpr (by linarith))
  exact mul_le_mul hnoise (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
    (hn.trans hnoise)

theorem endpoint_refError_le {K₀ K A g u noise₀ noise : ℝ} {N : ℕ}
    (hK : K₀≤K) (hu : u≤A*g) (hn : 0≤noise₀) (hnoise : noise₀≤noise) :
    Real.exp (u*N+2*K₀)*(Real.exp ((-2*g-u)*N+2*K₀)+noise₀) ≤ refError K A g N noise := by
  rw [mul_add,←Real.exp_add]
  have he : u*(N:ℝ)+2*K₀+((-2*g-u)*N+2*K₀)=-2*g*N+4*K₀ := by ring
  rw [he]
  apply add_le_add (Real.exp_le_exp.mpr (by linarith))
  rw [mul_comm]
  apply mul_le_mul hnoise _ (Real.exp_pos _).le (hn.trans hnoise)
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg N)
  linarith

/-- All model-dependent reference constants are absorbed without changing b,n
or the source short-time, mesh and clean projector-error scales. -/
theorem reference_constants_eventually {κ : Type*} {l : Filter κ} {b n : κ → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (d : ℕ) {Dg C₁ C₂ C₃ C₄ D D₃ D₄ r₁ r₂ r₃ r₄ : ℝ}
    (hDg : 0≤Dg) (hC₁ : 1≤C₁) (hC₂ : 1≤C₂) (hC₃ : 1≤C₃) (hC₄ : 1≤C₄)
    (hD : 1≤D) (hD₃ : 1≤D₃) (hD₄ : 1≤D₄)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃) (hr₄ : 0 < r₄) :
    let L (k : κ) := shortTime (b k) (n k)
    let B (k : κ) := Dg*(b k*n k)
    let h (k : κ) := Real.exp (-root (b k)*n k)
    let g (k : κ) := gap (b k)
    let ε (k : κ) := Real.exp (-shortSignal (b k) (n k))
    let err (k : κ) := refError (B k+Real.log D) (1+8*d) (g k) (L k)
      (refNoise C₁ (L k) (h k)+refNoise C₂ (L k) (h k))
    ∀ᶠ k in l,(L k:ℝ)≤n k ∧ 1≤(L k:ℝ) ∧ 0<g k ∧
      C₁^(L k)*h k ≤ r₁ ∧ C₂^(L k)*h k ≤ r₂ ∧ C₃^(L k)*h k ≤ r₃ ∧ C₄^(L k)*h k ≤ r₄ ∧
      refNoise C₁ (L k) (h k)+refNoise C₂ (L k) (h k)<Real.exp (-2*(B k+Real.log D))/2 ∧
      Real.exp (-2*g k*(L k:ℝ)+4*(B k+Real.log D))≤1/2 ∧
      err k≤1/2 ∧ 3*err k≤ε k ∧ ε k≤1/2 ∧
      ∀ j : Fin (d+1),let γ := (1+8*(j.val:ℝ))*g k
        (Real.exp ((γ-g k)*(L k:ℝ)+2*(B k+Real.log D₃))*
          (Real.exp ((-γ-g k)*(L k:ℝ)+2*(B k+Real.log D₃))+refNoise C₃ (L k) (h k))≤ε k/3) ∧
        (Real.exp ((-γ-g k)*(L k:ℝ)+2*(B k+Real.log D₄))*
          (Real.exp ((γ-g k)*(L k:ℝ)+2*(B k+Real.log D₄))+refNoise C₄ (L k) (h k))≤ε k/3) := by
  intro L B h g ε err
  let C := C₁+C₂+C₃+C₄+1
  let Dbar := Dg+Real.log D+Real.log D₃+Real.log D₄
  have hlD := Real.log_nonneg hD
  have hlD₃ := Real.log_nonneg hD₃
  have hlD₄ := Real.log_nonneg hD₄
  have hDb : 0≤Dbar := by dsimp [Dbar]; positivity
  have hC : 1≤C := by dsimp [C]; linarith
  have hc₁ : C₁≤C := by dsimp [C]; linarith
  have hc₂ : C₂≤C := by dsimp [C]; linarith
  have hc₃ : C₃≤C := by dsimp [C]; linarith
  have hc₄ : C₄≤C := by dsimp [C]; linarith
  have hc12 : C₁+C₂≤C := by dsimp [C]; linarith
  have hr : 0 < min (min r₁ r₂) (min r₃ r₄) := lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄)
  have hbudget := reference_budget hbpos hb hn hfloor hC hDb (by positivity : 0≤(1+8*(d:ℝ))) hr
  filter_upwards [hbudget,hbpos,hfloor,hn.eventually (eventually_ge_atTop (1:ℝ))] with k ht hbpos hf hn1
  let K := Dbar*b k*n k
  let noise := refNoise C (L k) (h k)
  let e := refError K (1+8*d) (g k) (L k) noise
  have hbn : 1≤b k*n k := by
    have hs := ScaleHierarchy.lower_bound (p:=1) hn1 (by norm_num) hf
    have hpow := Real.one_le_rpow hn1 (by norm_num : (0:ℝ)≤1-(1:ℝ)/10)
    simpa only [Real.rpow_one] using hpow.trans hs
  have hK (D' : ℝ) (hD' : 0≤Real.log D') (hd : Dg+Real.log D'≤Dbar) : B k+Real.log D'≤K := by
    have hm := mul_le_mul_of_nonneg_right hd (by linarith : 0≤b k*n k)
    have hm' := mul_le_mul_of_nonneg_left hbn hD'
    dsimp only [B,K]
    nlinarith only [hm,hm']
  have hKD := hK D hlD (by dsimp [Dbar]; linarith)
  have hKD₃ := hK D₃ hlD₃ (by dsimp [Dbar]; linarith)
  have hKD₄ := hK D₄ hlD₄ (by dsimp [Dbar]; linarith)
  have hhp : 0≤h k := (Real.exp_pos _).le
  have hn12 : refNoise C₁ (L k) (h k)+refNoise C₂ (L k) (h k)≤noise :=
    refNoise_add_le (by linarith) (by linarith) hc12 hhp
  have hn3 : refNoise C₃ (L k) (h k)≤noise := refNoise_mono (by linarith) hc₃ hhp
  have hn4 : refNoise C₄ (L k) (h k)≤noise := refNoise_mono (by linarith) hc₄ hhp
  have he : err k≤e := refError_mono hKD (by apply add_nonneg <;> apply refNoise_nonneg <;> linarith) hn12
  have hτ (C' r' : ℝ) (hC' : 0≤C') (hc' : C'≤C) (hr' : min (min r₁ r₂) (min r₃ r₄) ≤ r') :
      C'^(L k)*h k ≤ r' :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC' hc' _) hhp).trans (ht.2.2.1.trans hr')
  have hg : 0<g k := Real.rpow_pos_of_pos hbpos _
  refine ⟨ht.1,ht.2.1,hg,hτ C₁ r₁ (by linarith) hc₁ ((min_le_left _ _).trans (min_le_left _ _)),
    hτ C₂ r₂ (by linarith) hc₂ ((min_le_left _ _).trans (min_le_right _ _)),
    hτ C₃ r₃ (by linarith) hc₃ ((min_le_right _ _).trans (min_le_left _ _)),
    hτ C₄ r₄ (by linarith) hc₄ ((min_le_right _ _).trans (min_le_right _ _)),?_,?_,?_,?_,ht.2.2.2.2.2.2.2,?_⟩
  · exact (hn12.trans_lt ht.2.2.2.1).trans_le (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  · exact (Real.exp_le_exp.mpr (by linarith : -2*g k*(L k:ℝ)+4*(B k+Real.log D)≤-2*g k*(L k:ℝ)+4*K)).trans ht.2.2.2.2.1
  · exact he.trans ht.2.2.2.2.2.1
  · exact (mul_le_mul_of_nonneg_left he (by norm_num)).trans ht.2.2.2.2.2.2.1
  · intro j γ
    have hj : (j.val:ℝ)≤d := by exact_mod_cast (show j.val≤d by omega)
    have hγ₀ : 0≤γ := by dsimp only [γ]; positivity
    have hγ : γ≤(1+8*(d:ℝ))*g k := by
      apply mul_le_mul_of_nonneg_right _ hg.le
      linarith
    have hf := endpoint_refError_le (N:=L k) hKD₃
      (show γ-g k≤(1+8*(d:ℝ))*g k by linarith) (refNoise_nonneg (by linarith : 0≤C₃) hhp _) hn3
    have hb := endpoint_refError_le (N:=L k) hKD₄
      (show -γ-g k≤(1+8*(d:ℝ))*g k by linarith) (refNoise_nonneg (by linarith : 0≤C₄) hhp _) hn4
    have he3 : e≤ε k/3 := by have hh := ht.2.2.2.2.2.2.1; change 3*e≤ε k at hh; linarith
    constructor
    · convert hf.trans he3 using 1; congr 3; ring
    · convert hb.trans he3 using 1; congr 3; ring
end SmoothObstruction.SwitchScales

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins ShortBin SwitchScales
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Authentic finite-bin references on every sufficiently large original scale.
The constants depend on the model and atlas, not the scale, alphabets, gauges,
or good set. The clean error is exp(-b^(3/4)n). -/
theorem eventual_finite_references (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {κ : Type*} {l : Filter κ} {b : κ → ℝ} {n : κ → ℕ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) l atTop)
    (hfloor : ∀ᶠ k in l,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (Dg R : ℝ) (hDg : 0≤Dg) :
    ∀ᶠ k in l,∀ (C : Type*) (c : M → ι) (P : M → C) (G : Set M)
      (A : ∀ x:G,BilateralGauge I S a c (n k) (Dg*(b k*n k)) R x),
      (∀ y,y∈K (c y)) → (∀ x y,P x=P y → c x=c y) →
      (∀ x∈G,I.IsInteriorPoint x) →
      (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤
        Real.exp (-root (b k)*n k)) →
      ∃ (γ : C → ℝ) (T : G → Finset (Fin d)) (ref : G → G)
        (Wf Wb : C×C → Submodule ℝ E₀),
        (ref = fun x => (reference P G (key P G x)).val) ∧
        (∀ q,|γ q|+|gap (b k)|≤(2+8*(d:ℝ))*gap (b k)) ∧
        (∀ x:G,P (ref x)=P x) ∧
        (∀ x y:G,P x=P y → (T x).card=(T y).card) ∧
        (∀ x y:G,P x=P y → ref x=ref y) ∧
        (∀ x:G,∀ i∈(T x)ᶜ,(A x).lam i≤γ (P x)-gap (b k)) ∧
        (∀ x:G,∀ i∈T x,γ (P x)+gap (b k)≤(A x).lam i) ∧
        (∀ x:G,
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))ᶜ).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)ᶜ).starProjection‖≤Real.exp (-shortSignal (b k) (n k)) ∧
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)).starProjection‖≤Real.exp (-shortSignal (b k) (n k))) ∧
        (∀ x:G,
          Module.finrank ℝ (Wf (P x,P (S^[n k] x)))=(T x).card ∧
          Module.finrank ℝ (Wb (P x,P (S.symm^[n k] x)))=d-(T x).card ∧
          ‖((A x).forwardSpace I S a c (n k) (T x)).starProjection-
            (Wf (P x,P (S^[n k] x))).starProjection‖≤1/2 ∧
          ‖((A x).backwardSpace I S a c (n k) (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n k] x))).starProjection‖≤1/2) := by
  classical
  obtain ⟨r₁,C₁,r₂,C₂,D,r₃,C₃,D₃,r₄,C₄,D₄,hr₁,hC₁,hr₂,hC₂,hD,hr₃,hC₃,hD₃,hr₄,hC₄,hD₄,hrefs⟩ :=
    finite_references_uniform I hclosed S a K hK hKU
  have hbudget := reference_constants_eventually hbpos hb hn hfloor d hDg hC₁ hC₂ hC₃ hC₄ hD hD₃ hD₄ hr₁ hr₂ hr₃ hr₄
  filter_upwards [hbudget] with k hk
  rcases hk with ⟨hN,hN1,hg,ht₁,ht₂,ht₃,ht₄,hnoise,hdec,herr,herr3,hεhalf,hend⟩
  intro C c P G A hcover hco hint hdiam
  let N := shortTime (b k) (n k)
  let g := gap (b k)
  let h := Real.exp (-root (b k)*n k)
  let B := Dg*(b k*n k)
  let ε := Real.exp (-shortSignal (b k) (n k))
  have hN' : N≤n k := by exact_mod_cast hN
  have hfsmall (j : Fin (d+1)) := (hend j).1
  have hbsmall (j : Fin (d+1)) := (hend j).2
  obtain ⟨j,Wf,Wb,hslow,hfast,hcard,hstart,hend'⟩ := hrefs C c P G (n k) N B R h g A
    hcover hN' hco hint hdiam ht₁ ht₂ ht₃ ht₄ (Real.exp_pos _).le hg hdec
    (by simpa only [refNoise,refError,←add_mul] using And.intro hnoise herr)
    (fun j => by have hh := hfsmall j; change _≤ε/3 at hh; have he : ε≤1/2 := hεhalf; dsimp only [refNoise] at hh; linarith)
    (fun j => by have hh := hbsmall j; change _≤ε/3 at hh; have he : ε≤1/2 := hεhalf; dsimp only [refNoise] at hh; linarith)
  let γ (q : C) := (1+8*((j q).val:ℝ))*g
  let T (x : G) := fastSet (A x).lam (γ (P x))
  let ref (x : G) : G := (reference P G (key P G x)).val
  have hzero (x : G) (U : Finset (Fin d)) :
      ((A x).forward I S a c).space U=(A x).forwardSpace I S a c 0 U := by
    simp only [ShortBin.Gauge.space,BilateralGauge.forward,ShortBin.Gauge.ofFinite,
      Nat.zero_min,BilateralGauge.forwardSpace]
  refine ⟨γ,T,ref,Wf,Wb,rfl,?_,?_,hcard,?_,hslow,hfast,?_,?_⟩
  · intro q
    have hγ : 0≤γ q := by dsimp only [γ]; positivity
    rw [abs_of_nonneg hγ,abs_of_nonneg hg.le]
    have hj : ((j q).val:ℝ)≤d := by exact_mod_cast (show (j q).val≤d by omega)
    have hm := mul_le_mul_of_nonneg_right hj hg.le
    dsimp only [γ]; nlinarith only [hm]
  · intro x; exact (reference P G (key P G x)).property
  · intro x y hxy
    have he : key P G x=key P G y := Subtype.ext hxy
    exact congrArg (fun q : Active P G => (reference P G q).val) he
  · intro x
    have hh := hstart x
    simp only [hzero] at hh
    have he : 3*(Real.exp (-2*g*(N:ℝ)+4*(B+Real.log D))+
        (((N:ℝ)*C₁*C₁^(2*N)+N*C₂*C₂^(2*N))*h)*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D)))≤ε := by
      simpa only [refError,refNoise,←add_mul] using herr3
    constructor
    · rw [norm_sub_rev]; exact hh.1.trans he
    · rw [norm_sub_rev]; exact hh.2.trans he
  · intro x
    have hx := hend' x
    refine ⟨hx.1,hx.2.1,?_,?_⟩
    · have hh := hfsmall (j (P x)); dsimp only [refNoise] at hh
      have hb : 3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log D₃))*
          (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D₃))+N*C₃*C₃^(2*N)*h))≤ε := by linarith
      exact hx.2.2.1.trans (hb.trans hεhalf)
    · have hh := hbsmall (j (P x)); dsimp only [refNoise] at hh
      have hb : 3*(Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D₄))*
          (Real.exp ((γ (P x)-g)*N+2*(B+Real.log D₄))+N*C₄*C₄^(2*N)*h))≤ε := by linarith
      exact hx.2.2.2.trans (hb.trans hεhalf)
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

namespace SmoothObstruction.EndpointBudget
open Set Filter Topology ExteriorStability
/-- The literal endpoint hypotheses, simultaneously at every rank of the
unchanged ambient dimension. -/
theorem eventual_admissible {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (d : ℕ) (Dg R C K₀ Crel C₁ c β : ℝ) (hc : 0 < c) (hβ : 0<β)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤Real.exp (-c*b k^(3/4:ℝ)*n k)) :
    ∀ᶠ k in l,∀ p≤d,
      admissible d p Dg R C K₀ Crel C₁ (b k) (n k) (b k^(1/2:ℝ)) (δ k) β := by
  have he := all_ranks hbpos hb hn hfloor d C Crel C₁ (d*R) K₀ Dg c hc
    (fun p : Fin (d+1) => frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) p.val)
    (fun p : Fin (d+1) => (Fintype.card (powersetCard (Fin d) p.val):ℝ))
    (fun p : Fin (d+1) => ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) p.val‖)
    (fun p : Fin (d+1) => unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) p.val)
    (fun _ => β)
    (fun p => (by norm_num : (0:ℝ)≤1).trans (one_le_frameWedgeConstant p.val))
    (fun p => Nat.cast_nonneg _) (fun p => ContinuousMultilinearMap.opNorm_nonneg _) 
    (fun p => (by norm_num : (0:ℝ)≤1).trans (one_le_unitWedgeConstant p.val))
    (fun _ => hβ) hδ
  filter_upwards [he] with k hk
  intro p hp
  have h := hk ⟨p,by omega⟩
  simpa only [admissible,leading,normCost,mixedCost,relative,graph,mul_assoc] using h
end SmoothObstruction.EndpointBudget

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]
    {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [ProperSpace M] [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M] in
lemma interior_of_selected_ball (a x : M) (hx : x∈(chartAt H a).source) {r : ℝ} (hr : 0 ≤ r)
    (hs : closedBall ((extChartAt I a) x) r⊆interior (range I)) : I.IsInteriorPoint x := by
  apply (I.isInteriorPoint_iff_of_mem_atlas (n:=∞) (by simp) (chart_mem_atlas H a) hx).mpr
  exact (chartAt H a).mem_interior_extend_target ((chartAt H a).map_source hx)
    (hs (mem_closedBall_self hr))

/-- Finite translates, canonical references, the original retained carrier,
and the genuine global switch are compatible at all sufficiently large scales.
The explicit cell cardinality counts only two starting grids, never orbit labels. -/
theorem grid_switches_oai (hclosed : IsClosed (range I))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
    (S : Diffeomorph I I M M ∞) (hS : MeasurePreserving S μ μ)
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKU : ∀ i,K i⊆(chartAt H (a i)).source) (c : M → ι) (hc : Measurable c)
    (hcover : ∀ x,x∈K (c x)) (V : Set M) (hV : MeasurableSet V)
    (s : ℝ) (hs : 0 < s) (hcore : ∀ x∈V,∀ y,dist y x ≤ s → c y=c x)
    (η : ℝ) (hη : 0<η) (hVm : μ.real Vᶜ≤η/100)
    (b : ℕ → ℝ) (n : ℕ → ℕ) (hbpos : ∀ k,0<b k) (hb : Tendsto b atTop (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) atTop atTop)
    (hfloor : ∀ k,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (Dg R₀ : ℝ) (hDg : 0≤Dg) (hR₀ : 0≤R₀)
    (G : ℕ → Set M) (hG : ∀ k,MeasurableSet (G k)) (hGm : ∀ k,μ.real (G k)ᶜ≤η/100)
    (hA : ∀ᶠ k in atTop,∀ x∈G k,Nonempty (BilateralGauge I S a c (n k) (Dg*(b k*n k)) R₀ x))
    (Cb : ℝ) (_ : 0≤Cb)
    (hcollar : ∀ r : ℝ,0 ≤ r → ∃ W : Set M,MeasurableSet W ∧ μ.real W≤Cb*r ∧
      ∀ i x,x∈K i → x∉W → closedBall ((extChartAt I (a i)) x) r⊆interior (range I)) :
    ∃ (Dc Dp : ℝ) (N : ℕ) (ρ : ℕ → ℝ),1≤Dc ∧ 1≤Dp ∧ 0<N ∧
      Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k in atTop,
      let B := Dg*(b k*n k)
      let h₀ := Real.exp (-b k^(1/8:ℝ)*n k)
      let r := Real.exp (-2*b k^(1/8:ℝ)*n k)
      let δc := h₀/(((d:ℝ)+1)*N)
      let δp := r/(Real.sqrt 2*((d:ℝ)+1)*N)
      let mc := ⌈Dc/(δc*N)+1⌉₊
      let mp := ⌈(Real.sqrt 2*Real.exp (2*B))*Dp/(δp*N)+1⌉₊
      ∃ (J : Type) (_ : Fintype J) (_ : MeasurableSpace J) (_ : MeasurableSingletonClass J)
        (L : M → J) (Gp : Set (M×M)) (Φ : M×M → M×M),
        Fintype.card J=Fintype.card ι*(2*mc+1)^d*(2*mp+1)^d ∧
        Measurable L ∧ MeasurableSet Gp ∧ Measurable Φ ∧
        1-η≤(PairLaw.law μ L).real Gp ∧
        ((PairLaw.law μ L).restrict Gp).map (fun u => (Φ u).1)≤(2:ℝ≥0∞) • μ ∧
        ∀ u∈Gp,originalTube I S a c (n:=n k) (ρ k) u.1 (Φ u).1 ∧
          originalTube I S.symm a c (n:=n k) (ρ k) u.2 (Φ u).1 := by
  classical
  obtain ⟨r₀,C₀,σ,r₁,C₁,rg,Cg,β,K₀F,CreF,C₁F,K₀B,CreB,C₁B,rμ,
    hr₀,hC₀,hσ,hr₁,hC₁,hrg,hCg,hβ,hKF,hCrF,hCF,hKB,hCrB,hCB,hrμ,hswitch⟩ :=
    genuine_pair_switch I hclosed μ hμ S a K hK hKU s Dg hs hDg
  obtain ⟨Dc,hDc,hcoarse⟩ := ChartDensity.exists_coarse_cells I μ a K hK hKU c hc hcover
  obtain ⟨Dp,hDp,hproduct⟩ := finite_product_partition_uniform I μ S a K hK hKU c hcover
  obtain ⟨N,hN⟩ := exists_nat_gt ((d:ℝ)/(η/100)+1)
  have hNpos : 0<N := by
    have : 0≤(d:ℝ)/(η/100) := by positivity
    exact_mod_cast (by linarith : (0:ℝ)<N)
  have hNm : (d:ℝ)/N≤η/100 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hNpos)).mpr
    have h := (div_le_iff₀ (by positivity : (0:ℝ)<η/100)).mp (show (d:ℝ)/(η/100)≤N by linarith)
    simpa only [mul_comm] using h
  let Ac : ℝ := ((d:ℝ)+1)*N
  let Ap : ℝ := Real.sqrt 2*((d:ℝ)+1)*N
  have hAc : 0<Ac := by dsimp only [Ac]; positivity
  have hAp : 0<Ap := by dsimp only [Ap]; positivity
  let BB (k : ℕ) := Dg*(b k*n k)
  let g (k : ℕ) := b k^(1/2:ℝ)
  let α (k : ℕ) := (2+8*(d:ℝ))*g k
  let ε (k : ℕ) := Real.exp (-b k^(3/4:ℝ)*n k)
  let h₀ (k : ℕ) := Real.exp (-b k^(1/8:ℝ)*n k)
  let r (k : ℕ) := Real.exp (-2*b k^(1/8:ℝ)*n k)
  let δ (k : ℕ) := Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k)
  let ρ (k : ℕ) := 2*C₀*ShortBin.bvpInverseBound (BB k) (α k) (n k)*r k
  have hbfe : ∀ᶠ k in atTop,0<b k := Filter.Eventually.of_forall hbpos
  have hffe : ∀ᶠ k in atTop,(n k:ℝ)^(-1/10:ℝ)≤b k := Filter.Eventually.of_forall hfloor
  have hεenv : ∀ᶠ k in atTop,0≤ε k ∧ ε k≤Real.exp (-b k^(3/4:ℝ)*n k) :=
    Filter.Eventually.of_forall (fun k => ⟨(Real.exp_pos _).le,le_rfl⟩)
  have hρ0 := (ShortBin.spatial_switch_limits hbfe hb hn hffe hεenv Dg (2+8*(d:ℝ)) C₀ hDg (by positivity)).2.2.1
  have hspatial := ShortBin.spatial_ready hbfe hb hn hffe Dg (2+8*(d:ℝ)) C₀ C₁ Cg K₀F K₀B
    r₀ rg σ r₁ rμ Ac Ap hDg (by positivity) hC₀ hr₀ hrg hσ hr₁ hrμ hAc hAp
  have hrefs := eventual_finite_references I hclosed S a K hK hKU hbfe hb hn hffe Dg R₀ hDg
  choose Cp hCp hCpbound using fun p : Fin (d+1) =>
    ExteriorStability.exists_power_bound (E:=EuclideanSpace ℝ (Fin d)) p.val
  let Cext := 1+∑ p,Cp p
  have hCext : 0≤Cext := by
    have := Finset.sum_nonneg (s:=Finset.univ) (fun p _ => (show (0:ℝ)≤1 by norm_num).trans (hCp p))
    dsimp only [Cext]
    linarith
  have hpoly (p : ℕ) (hp : p≤d) (F : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      ‖ExteriorStability.exterior p F‖≤Cext*(max 1 ‖F‖)^p := by
    have hh := hCpbound ⟨p,by omega⟩ F
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hc := Finset.single_le_sum (fun q _ => (show (0:ℝ)≤1 by norm_num).trans (hCp q)) (Finset.mem_univ (⟨p,by omega⟩ : Fin (d+1)))
    dsimp only [Cext]; linarith
  have hbudgetF := EndpointBudget.eventual_admissible hbfe hb hn hffe d Dg R₀ Cext K₀F CreF C₁F 1 β (by norm_num) hβ
    (by simpa only [neg_one_mul] using hεenv)
  have hbudgetB := EndpointBudget.eventual_admissible hbfe hb hn hffe d Dg R₀ Cext K₀B CreB C₁B 1 β (by norm_num) hβ
    (by simpa only [neg_one_mul] using hεenv)
  have hdec (m : ℕ) : Tendsto (fun k => (n k:ℝ)^m*h₀ k) atTop (𝓝 0) := by
    have hh := ScaleHierarchy.polynomial_decay (p:=1/8) (q:=1) (c:=1) (C:=0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbfe hb hn hffe m
    simpa only [zero_mul,zero_sub,one_mul,neg_mul,h₀] using hh
  have hcollar0 : Tendsto (fun k => (2*(n k:ℝ)+3)*(Cb*h₀ k)) atTop (𝓝 0) := by
    have hh := ((hdec 1).const_mul (2*Cb)).add ((hdec 0).const_mul (3*Cb))
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'; apply Filter.Eventually.of_forall; intro k; simp only [pow_one,pow_zero,one_mul]; ring
  refine ⟨Dc,Dp,N,ρ,hDc,hDp,hNpos,hρ0,?_⟩
  filter_upwards [hspatial,hrefs,hbudgetF,hbudgetB,hA,
    hcollar0.eventually_le_const (by positivity : (0:ℝ)<η/100)] with k hsp href hbudF hbudB hAk hcolmass
  rcases hsp with ⟨hbn,heps,hsmall,hgap,hδr,hδrg,hρδ,hρσ,hρc,hρr₁,hρC,hρCg,hδF,hδB,hE,hcontract,hdata,hrrμ,hδh⟩
  dsimp only
  let dc := h₀ k/Ac
  let dp := r k/Ap
  have hdc : 0<dc := div_pos (Real.exp_pos _) hAc
  have hdp : 0<dp := div_pos (Real.exp_pos _) hAp
  obtain ⟨P,Wc,hP,hWc,hWcm,hPc,hPdiam,hPrec,hPcard⟩ := hcoarse hdc hNpos
  let C := ι × (Fin d → Fin (2*⌈Dc/(dc*N)+1⌉₊+1))
  have hPc' (x y : M) (he : P x=P y) : c x=c y := by rw [←hPc x,←hPc y,he]
  have hsrc (x : M) : x∈(extChartAt I (a (c x))).source := by rw [extChartAt_source]; exact hKU _ (hcover x)
  have hceq : ((d:ℝ)+1)*(dc*N)=h₀ k := by dsimp only [dc,Ac]; field_simp
  have hpeq : Real.sqrt 2*((d:ℝ)+1)*(dp*N)=r k := by dsimp only [dp,Ap]; field_simp
  obtain ⟨Wb,hWb,hWbm,hWs⟩ := hcollar (h₀ k) (Real.exp_pos _).le
  let G' := G k\Wb
  have hiG (x : M) (hx : x∈G') : I.IsInteriorPoint x :=
    interior_of_selected_ball I _ _ (hKU _ (hcover x)) (Real.exp_pos _).le (hWs _ x (hcover x) hx.2)
  let A (x : G') : BilateralGauge I S a c (n k) (BB k) R₀ x := (hAk x x.property.1).some
  have hco (x y : M) (he : P x=P y) :
      ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h₀ k := by
    have hh := hPdiam x y he
    rw [hceq] at hh
    rw [ChartDensity.coordinates_eq I _ _ (hsrc x),hPc' x y he] at hh
    rw [ChartDensity.coordinates_eq I _ _ (hsrc y)] at hh
    exact hh
  obtain ⟨γ,T,ref,Wf,Wback,hrefeq,hα,hrefP,hcard,hreff,hslow,hfast,hstart,hend⟩ :=
    href C c P G' A hcover hPc' hiG hco
  subst ref
  have hBB : 0≤BB k := mul_nonneg hDg (mul_nonneg (hbpos k).le (Nat.cast_nonneg _))
  obtain ⟨L,Wp,hL,hWp,hWpm,hLP,hLdiam,hLrec,hLcard⟩ :=
    hproduct C P hP Prod.fst hPc G' (n k) (BB k) R₀ hBB A T dp hdp N hNpos
  have hSsymm : MeasurePreserving S.symm μ μ := MeasurePreserving.symm S.toHomeomorph.toMeasurableEquiv hS
  obtain ⟨R,hR,hRG,hRm,hret⟩ := RetainedGlobal.exists_retained μ S S.symm hS hSsymm
    G' V Wc Wp Wb ((hG k).diff hWb) hV hWc hWp hWb (n k)
  have hmassR : μ.real Rᶜ≤η/2 := by
    have hG'm : μ.real G'ᶜ≤μ.real (G k)ᶜ+μ.real Wb := by
      simpa only [G',compl_sdiff,union_comm] using RetainedGlobal.real_union_le μ (G k)ᶜ Wb
    have hcoef : 0≤2*(n k:ℝ)+3 := by positivity
    have hbc := mul_le_mul_of_nonneg_left hWbm hcoef
    have hWc' := hWcm.trans hNm
    have hWp' := hWpm.trans hNm
    have hg' := hGm k
    nlinarith only [hRm,hG'm,hbc,hWc',hWp',hVm,hg',hcolmass,hη]
  have hLp (x y : M) (he : L x=L y) : P x=P y := by rw [←hLP x,←hLP y,he]
  have hLc (x y : M) (he : L x=L y) : c x=c y := hPc' x y (hLp x y he)
  have hLdiam' (x y : M) (he : L x=L y) :
      ‖ChartDensity.coordinates I (a (c x)) x-ChartDensity.coordinates I (a (c x)) y‖ ≤ r k := by
    simpa only [hpeq] using hLdiam x y he
  obtain ⟨Φ,hΦ,hGp,hinj,hlaw,hmarg,htube⟩ := hswitch (C:=C) c P L Prod.fst Prod.fst G' R V Wc Wp
    (n k) (b k) R₀ Cext (ε k) (g k) (α k) (r k) dc dp
    (Real.sqrt 2*Real.exp (2*BB k)) γ A T (fun x => (FiniteBins.reference P G' (FiniteBins.key P G' x)).val) Wf Wback hc hP hL hR hRG hcover hLP hPc
    (fun x hx => hiG x (hRG hx)) hrefP hcard hreff (by simpa only [ε,SwitchScales.shortSignal,neg_mul] using hstart) hend
    (hbpos k).le hbn hR₀ hCext (Real.exp_pos _).le heps hsmall (Real.rpow_nonneg (hbpos k).le _)
    hslow hfast hgap (fun x => hα (P x)) (Real.exp_pos _).le hδr hδrg
    (by exact mul_nonneg (mul_nonneg (by linarith) (ShortBin.bvp_nonneg _ _ _)) (Real.exp_pos _).le)
    hρδ hρσ hρc hρr₁ hρC hρCg hδF hδB hdc (by positivity) hE hpoly hbudF hbudB
    (fun x hx t => ⟨(closedBall_subset_closedBall hδh).trans (hWs _ _ (hcover _) ((hret x hx).2.2.2.2.2.2.2 _ (by omega)).1),
      (closedBall_subset_closedBall hδh).trans (hWs _ _ (hcover _) ((hret x hx).2.2.2.2.2.2.2 _ (by omega)).2)⟩)
    (fun x hx y hy he => by
      have hh := hLdiam' x y he
      rw [ChartDensity.coordinates_eq I _ _ (hsrc x),hLc x y he,
        ChartDensity.coordinates_eq I _ _ (hsrc y),norm_sub_rev] at hh
      rw [hLc x y he]
      exact hh.trans (le_mul_of_one_le_left (Real.exp_pos _).le hC₀))
    hcontract hdata (fun x y he => (hLdiam' x y he).trans_lt hrrμ) hcore hPrec
    (fun x y z hx he hxW hyW hz herr => by
      apply hLrec x y z (hRG hx) he hxW hyW hz
      exact herr)
    (fun x hx => ⟨(hret x hx).1,(hret x hx).2.1,(hret x hx).2.2.1,
      (hret x hx).2.2.2.1,(hret x hx).2.2.2.2.1,(hret x hx).2.2.2.2.2.1,(hret x hx).2.2.2.2.2.2.1⟩)
  let Gp := {u : M×M | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
  have hmass := (RetainedGlobal.pair_mass μ L hL R hR hmassR).2
  refine ⟨_,inferInstance,inferInstance,inferInstance,L,Gp,Φ,?_,hL,hGp,hΦ,?_,hmarg,htube⟩
  · exact hLcard.trans (by rw [hPcard])
  · have he : Gp=R.prod R∩{u : M×M | L u.1=L u.2} := by
      ext u; exact ⟨fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩,fun h => ⟨h.1.1,h.1.2,h.2⟩⟩
    rw [he]
    exact hmass
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SmoothObstruction.ManifoldCoordinates.grid_switches_oai.{u_1, u_2} := @OAI.SmoothObstruction.ManifoldCoordinates.grid_switches_oai.{u_1, u_2}
