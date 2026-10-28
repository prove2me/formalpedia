-- Prove2me | solution 1 for OAI.StandardMapEntropy.actual_grid_square_product_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:38:47.608467+00:00
-- url     : https://prove2.me/submissions/cbc02236-6730-4185-b15a-e54de8f13c4b

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_BridgeScalarControl_prefix_dirichlet_q44
import Theorems.Thm_OAI_StandardMapEntropy_actual_backward_carry_full_q44
import Theorems.Thm_OAI_StandardMapEntropy_actual_compact_graph_labels_full_q44

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

lemma liftedOrbit_step (k q₀ q₁ : ℝ) (n : ℕ) :
    liftedOrbit k q₀ q₁ (n + 2) =
      phi k (liftedOrbit k q₀ q₁ (n + 1)) - liftedOrbit k q₀ q₁ n := rfl

open scoped Matrix.Norms.Operator

open Filter
open scoped Topology

open Metric

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LiftDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma liftIter_add (k : ℝ) (i j : ℤ) (z : ℝ × ℝ) :
    liftIter k (i+j) z=liftIter k i (liftIter k j z) := by
  simp only [liftIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma liftIter_nat (k : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    liftIter k n z=(liftedOrbit k z.2 z.1 (n+1),liftedOrbit k z.2 z.1 n) := by
  induction n with
  | zero => simp [liftIter,liftedOrbit]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_comm,liftIter_add,ih]
    simp only [liftIter,zpow_one]
    change (phi k (liftedOrbit k z.2 z.1 (n+1))-liftedOrbit k z.2 z.1 n,
      liftedOrbit k z.2 z.1 (n+1))=_
    rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GraphCalculus
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma hasStrictDerivAt_phi (k x : ℝ) : HasStrictDerivAt (phi k) (potential k x) x := by
  have h := ((hasStrictDerivAt_id x).const_mul 2).add
    (((Real.hasStrictDerivAt_sin (2*Real.pi*x)).comp x
      ((hasStrictDerivAt_id x).const_mul (2*Real.pi))).const_mul k)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [potential]
  ring

lemma hasStrictFDerivAt_liftedOrbit (k q a : ℝ) (n : ℕ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 n)
      (sSolution (orbitCoefficient k q a) n • ContinuousLinearMap.fst ℝ ℝ ℝ+
       tSolution (orbitCoefficient k q a) n • ContinuousLinearMap.snd ℝ ℝ ℝ) (q,a) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [sSolution,tSolution,linearSolution] using
      (hasStrictFDerivAt_fst : HasStrictFDerivAt (Prod.fst : ℝ × ℝ → ℝ) _ (q,a))
  | one => simpa [sSolution,tSolution,linearSolution] using
      (hasStrictFDerivAt_snd : HasStrictFDerivAt (Prod.snd : ℝ × ℝ → ℝ) _ (q,a))
  | more n h0 h1 =>
    have h := ((hasStrictDerivAt_phi k (liftedOrbit k q a (n+1))).comp_hasStrictFDerivAt (q,a) h1).sub h0
    apply h.congr_fderiv
    apply ContinuousLinearMap.ext
    intro z
    change potential k (liftedOrbit k q a (n+1)) *
      (sSolution (orbitCoefficient k q a) (n+1)*z.1+tSolution (orbitCoefficient k q a) (n+1)*z.2)-
      (sSolution (orbitCoefficient k q a) n*z.1+tSolution (orbitCoefficient k q a) n*z.2) =
      (orbitCoefficient k q a (n+1)*sSolution (orbitCoefficient k q a) (n+1)-sSolution (orbitCoefficient k q a) n)*z.1+
      (orbitCoefficient k q a (n+1)*tSolution (orbitCoefficient k q a) (n+1)-tSolution (orbitCoefficient k q a) n)*z.2
    dsimp only [orbitCoefficient]
    ring

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GraphParameterContinuity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma continuous_liftedOrbit_pair (k : ℝ) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 n) :=
  continuous_iff_continuousAt.mpr (fun z =>
    (hasStrictFDerivAt_liftedOrbit k z.1 z.2 n).continuousAt)
lemma continuousOn_linearSolution_params {α : Type*} [TopologicalSpace α]
    (s : Set α) (v : α → ℕ → ℝ) (a b : α → ℝ)
    (hv : ∀ n, ContinuousOn (fun x => v x n) s)
    (ha : ContinuousOn a s) (hb : ContinuousOn b s) (n : ℕ) :
    ContinuousOn (fun x => linearSolution (v x) (a x) (b x) n) s := by
  induction n using Nat.twoStepInduction with
  | zero => exact ha
  | one => exact hb
  | more n h0 h1 => exact ((hv (n+1)).mul h1).sub h0
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GraphSubsetCalculus
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma hasFDerivWithinAt_of_regular_level {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (F : E × ℝ → ℝ) (b : E → ℝ) (s : Set E) (x : E)
    (A : E →L[ℝ] ℝ) (t : ℝ)
    (hD : HasStrictFDerivAt F
      (A.comp (ContinuousLinearMap.fst ℝ E ℝ)+t • ContinuousLinearMap.snd ℝ E ℝ) (x,b x))
    (ht : t ≠ 0) (hb : ContinuousWithinAt b s x)
    (hlevel : ∀ᶠ y in 𝓝[s] x, F (y,b y)=F (x,b x)) :
    HasFDerivWithinAt b ((-t⁻¹) • A) s x := by
  let L : (E × ℝ) →L[ℝ] ℝ :=
    A.comp (ContinuousLinearMap.fst ℝ E ℝ)+t • ContinuousLinearMap.snd ℝ E ℝ
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := t⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
  let ψ := hD.implicitFunctionOfProdDomain hInv
  have he : ∀ᶠ y in 𝓝[s] x, ψ y=b y := by
    have hpair : Tendsto (fun y => (y,b y)) (𝓝[s] x) (𝓝 (x,b x)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.prodMk_nhds hb
    filter_upwards [hpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),hlevel] with y hy hy'
    exact hy.mp hy'
  have he0 : ψ x=b x := ((hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv).self_of_nhds).mp rfl
  have hd := (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hInv).hasFDerivAt.hasFDerivWithinAt (s := s)
  have heq : -(L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse.comp
      (L.comp (ContinuousLinearMap.inl ℝ E ℝ)) = (-t⁻¹) • A := by
    apply ContinuousLinearMap.ext
    intro z
    have hh : (L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse
        ((L.comp (ContinuousLinearMap.inl ℝ E ℝ)) z)=t⁻¹*A z := by
      apply hInv.inverse_apply_eq.mpr
      simp [L,ht]
    change -((L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse
      ((L.comp (ContinuousLinearMap.inl ℝ E ℝ)) z))=(-t⁻¹)*A z
    rw [hh,neg_mul]
  change HasFDerivWithinAt ψ _ s x at hd
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq (EventuallyEq.symm he) he0.symm
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ChangeVariablesBounds
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measure_image_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) (f : E → E)
    (D : E → E →L[ℝ] E) (c C : ℝ) (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hinj : InjOn f s)
    (hlo : ∀ x ∈ s, c ≤ |(D x).det|) (hhi : ∀ x ∈ s, |(D x).det| ≤ C) :
    ENNReal.ofReal c*μ s ≤ μ (f '' s) ∧ μ (f '' s) ≤ ENNReal.ofReal C*μ s := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image μ hs hD hinj]
  constructor
  · calc
      _ = ∫⁻ x in s, ENNReal.ofReal c ∂μ := by simp
      _ ≤ _ := setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hlo x hx))
  · calc
      _ ≤ ∫⁻ x in s, ENNReal.ofReal C ∂μ :=
        setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hhi x hx))
      _ = _ := by simp

lemma weighted_image_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) (f : E → E)
    (D : E → E →L[ℝ] E) (c C : ℝ) (g : E → ℝ≥0∞) (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hinj : InjOn f s)
    (hlo : ∀ x ∈ s, c ≤ |(D x).det|) (hhi : ∀ x ∈ s, |(D x).det| ≤ C) :
    ENNReal.ofReal c*(∫⁻ x in s, g (f x) ∂μ) ≤ ∫⁻ x in f '' s, g x ∂μ ∧
      (∫⁻ x in f '' s, g x ∂μ) ≤ ENNReal.ofReal C*(∫⁻ x in s, g (f x) ∂μ) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hD hinj g]
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hs (fun x hx => mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hlo x hx)) (by positivity))
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hs (fun x hx => mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hhi x hx)) (by positivity))

lemma weighted_sweep_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) (f : E → E)
    (D : E → E →L[ℝ] E) (c : ℝ) (g w : E → ℝ≥0∞) (δ : ℝ≥0∞)
    (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hinj : InjOn f s)
    (hlo : ∀ x ∈ s, c ≤ |(D x).det|)
    (hobs : ∀ x ∈ s, w x ≤ g (f x)+δ) :
    ENNReal.ofReal c*(∫⁻ x in s, w x ∂μ) ≤
      (∫⁻ x in f '' s, g x ∂μ)+ENNReal.ofReal c*δ*μ s := by
  calc
    _ ≤ ENNReal.ofReal c*(∫⁻ x in s, g (f x)+δ ∂μ) :=
      mul_le_mul_of_nonneg_left (setLIntegral_mono' hs hobs) (by positivity)
    _ = ENNReal.ofReal c*(∫⁻ x in s, g (f x) ∂μ)+ENNReal.ofReal c*δ*μ s := by
      rw [lintegral_add_right _ measurable_const]
      simp [mul_add,mul_assoc]
    _ ≤ _ := add_le_add (by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hD hinj g,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' hs (fun x hx => mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hlo x hx)) (by positivity))) le_rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GraphJacobians
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma planeMatrix_det (a b c d : ℝ) : (planeMatrix a b c d).det=a*d-b*c := by
  change (planeMatrix a b c d).toLinearMap.det=_
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Module.Basis.coe_finTwoProd_repr]

lemma label_graph_derivative (Q : ℝ × ℝ → ℝ) (X : ℝ × ℝ → ℝ)
    (S : Set (ℝ × ℝ)) (z : ℝ × ℝ) (yc a b u v : ℝ)
    (hQ : HasStrictFDerivAt Q (planeDual u v) (X z,z.2))
    (hR : HasStrictFDerivAt Q (planeDual a b) (z.1,yc))
    (hu : u ≠ 0) (hX : ContinuousWithinAt X S z)
    (hlevel : ∀ᶠ w in 𝓝[S] z, Q (X w,w.2)=Q (w.1,yc))
    (hlevel0 : Q (X z,z.2)=Q (z.1,yc)) :
    HasFDerivWithinAt (fun w => (X w,w.2)) (planeMatrix (a/u) (-v/u) 0 1) S z := by
  let F : (ℝ × ℝ) × ℝ → ℝ := fun w => Q (w.2,w.1.2)-Q (w.1.1,yc)
  let A := planeDual (-a) v
  have hD : HasStrictFDerivAt F
      (A.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+u • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (z,X z) := by
    have hp1 := hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (z,X z))
    have hp2 := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := z)).comp (z,X z) (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (z,X z)))
    have hp3 := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := z)).comp (z,X z) (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (z,X z)))
    have hh := (hQ.comp (z,X z) (hp1.prodMk hp2)).sub
      (hR.comp (z,X z) (hp3.prodMk (hasStrictFDerivAt_const yc (z,X z))))
    apply hh.congr_fderiv
    apply ContinuousLinearMap.ext
    intro w
    change u*w.2+v*w.1.2-(a*w.1.1+b*0)=(-a*w.1.1+v*w.1.2)+u*w.2
    ring
  have hx := hasFDerivWithinAt_of_regular_level F X S z A u hD hu hX (by
    filter_upwards [hlevel] with w hw
    dsimp only [F]
    rw [hw,hlevel0]; ring)
  have ht := hx.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).hasFDerivWithinAt
  apply ht.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  apply Prod.ext
  · change (-u⁻¹)*((-a)*w.1+v*w.2)=a/u*w.1+(-v/u)*w.2
    ring
  · change w.2=0*w.1+1*w.2
    ring

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RecenteredGraphs
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma hasStrictFDerivAt_liftedOrbit_swap (k x y : ℝ) (n : ℕ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => liftedOrbit k z.2 z.1 n)
      (planeDual (tSolution (orbitCoefficient k y x) n)
        (sSolution (orbitCoefficient k y x) n)) (x,y) := by
  have h := (hasStrictFDerivAt_liftedOrbit k y x n).comp (x,y)
    ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (x,y))).prodMk
      (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (x,y))))
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  change sSolution (orbitCoefficient k y x) n*w.2+tSolution (orbitCoefficient k y x) n*w.1=tSolution (orbitCoefficient k y x) n*w.1+sSolution (orbitCoefficient k y x) n*w.2
  ring

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightedChart
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma product_slice_bound (E I : Set ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ≥0∞)
    (K : ℝ≥0∞) (hE : MeasurableSet E) (_hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I)
    (hslice : ∀ x ∈ E, ∫⁻ y in I, T.indicator f (x,y) ≤ K) :
    (∫⁻ z in T, f z) ≤ K*volume E := by
  have he : (∫⁻ z in T, f z) = ∫⁻ z in E ×ˢ I, T.indicator f z := by
    rw [lintegral_indicator hT,Measure.restrict_restrict hT,inter_eq_left.mpr hsub]
  rw [he]
  change (∫⁻ z, T.indicator f z ∂(volume.prod volume).restrict (E ×ˢ I)) ≤ _
  rw [← Measure.prod_restrict]
  calc
    _ ≤ ∫⁻ x in E, ∫⁻ y in I, T.indicator f (x,y) := lintegral_prod_le _
    _ ≤ ∫⁻ x in E, K := setLIntegral_mono' hE hslice
    _ = _ := by simp

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusIntegral
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy

lemma unit_cell_integral (g : Torus → ℝ≥0∞) (hg : Measurable g) (a b : ℝ) :
    (∫⁻ z in Ioc a (a+1) ×ˢ Ioc b (b+1), g (liftProjection z)) = ∫⁻ z, g z ∂area := by
  have h := (AddCircle.measurePreserving_mk (1:ℝ) a).prod (AddCircle.measurePreserving_mk (1:ℝ) b)
  rw [Measure.prod_restrict] at h
  exact h.lintegral_comp hg

lemma interval_four_cell_cover (x : ℝ) (hx : x ∈ Ioc (-2:ℝ) 2) :
    ∃ j : Fin 4, x ∈ Ioc ((j:ℝ)-2) ((j:ℝ)-2+1) := by
  by_cases h1 : x ≤ -1
  · exact ⟨0,by norm_num at *; exact ⟨hx.1,h1⟩⟩
  by_cases h2 : x ≤ 0
  · exact ⟨1,by norm_num at *; exact ⟨by linarith,h2⟩⟩
  by_cases h3 : x ≤ 1
  · exact ⟨2,by norm_num at *; exact ⟨by linarith,h3⟩⟩
  · exact ⟨3,by norm_num at *; exact ⟨by linarith,hx.2⟩⟩

lemma bounded_lift_integral (g : Torus → ℝ≥0∞) (hg : Measurable g)
    (S : Set (ℝ × ℝ)) (hS : S ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2) :
    (∫⁻ z in S, g (liftProjection z)) ≤ 16*(∫⁻ z, g z ∂area) := by
  let cell : (Fin 4 × Fin 4) → Set (ℝ × ℝ) := fun j =>
    Ioc ((j.1:ℝ)-2) ((j.1:ℝ)-2+1) ×ˢ Ioc ((j.2:ℝ)-2) ((j.2:ℝ)-2+1)
  have hcover : S ⊆ ⋃ j, cell j := by
    intro z hz
    obtain ⟨i,hi⟩ := interval_four_cell_cover z.1 (hS hz).1
    obtain ⟨j,hj⟩ := interval_four_cell_cover z.2 (hS hz).2
    exact mem_iUnion.mpr ⟨(i,j),hi,hj⟩
  calc
    _ ≤ ∫⁻ z in ⋃ j, cell j, g (liftProjection z) := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ z in cell j, g (liftProjection z) := lintegral_iUnion_le _ _
    _ = _ := by simp only [cell,unit_cell_integral g hg,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]; norm_num
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ClosedEligibility
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma continuous_orbitCoefficient_pair (k : ℝ) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => orbitCoefficient k z.1 z.2 n) := by
  have h := continuous_liftedOrbit_pair k n
  unfold orbitCoefficient potential
  exact continuous_const.add (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul h)))

lemma isClosed_prefixEligible (k : ℝ) (B J : ℕ) :
    IsClosed {z : ℝ × ℝ | prefixEligible k B J z} := by
  have hc n := continuous_transferProduct_params (fun z : ℝ × ℝ => orbitCoefficient k z.1 z.2)
    (continuous_orbitCoefficient_pair k) n
  have ht : Continuous (fun z : ℝ × ℝ => tSolution (orbitCoefficient k z.1 z.2) J) := by
    rw [← continuousOn_univ]
    exact continuousOn_linearSolution_params univ (fun z : ℝ × ℝ => orbitCoefficient k z.1 z.2) (fun _ => 0) (fun _ => 1) (fun p => (continuous_orbitCoefficient_pair k p).continuousOn)
      continuousOn_const continuousOn_const J
  simp only [prefixEligible,ofPred_and,ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le continuous_const (hc i).norm
  · exact isClosed_le ((hc B).norm.div_const 3) ht.abs
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointTransport
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma liftIter_neg_swap (k : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    liftIter k (-(n:ℤ)) z=(liftIter k (n:ℤ) z.swap).swap := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ((n+1:ℕ):ℤ)=1+(n:ℤ) by omega,show -(1+(n:ℤ))=(-1)+(-(n:ℤ)) by ring,
      liftIter_add,liftIter_add,ih]
    simp only [liftIter,zpow_neg_one,zpow_one,Equiv.Perm.inv_def,liftStep_symm_apply,liftStep_apply,
      Prod.fst_swap,Prod.snd_swap,Prod.swap_prod_mk]
lemma graph_endpoint_close (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (n B : ℕ) (hn : 1 ≤ n)
    (hB : B=n ∨ B=n+1)
    (hterm : liftedOrbit k z.2 z.1 (n+1)=liftedOrbit k w.2 w.1 (n+1))
    (hbound : ∀ i : Fin n,
      |liftedOrbit k z.2 z.1 (i+1)-liftedOrbit k w.2 w.1 (i+1)| ≤
        8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) :
    dist (liftIter k (B:ℤ) z) (liftIter k (B:ℤ) w) ≤
      8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) := by
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have hMn : 0 ≤ 8/growthBase k^((4/5:ℝ)*(n:ℝ)) := by positivity
  have hn' : n-1+1=n := by omega
  have hlast := hbound (⟨n-1,by omega⟩ : Fin n)
  have hreal : ((n-1:ℕ):ℝ)+1=n := by exact_mod_cast hn'
  simp only [hn',hreal] at hlast
  have he : dist (liftIter k (B:ℤ) z) (liftIter k (B:ℤ) w) ≤
      8/growthBase k^((4/5:ℝ)*(n:ℝ)) := by
    rcases hB with rfl|rfl
    · rw [liftIter_nat,liftIter_nat,Prod.dist_eq,Real.dist_eq,Real.dist_eq,hterm,sub_self,abs_zero]
      exact max_le hMn hlast
    · rw [liftIter_nat,liftIter_nat,Prod.dist_eq,Real.dist_eq,Real.dist_eq,liftedOrbit_step,
        liftedOrbit_step,hterm,sub_self,abs_zero]
      have he : |phi k (liftedOrbit k w.2 w.1 (n+1))-liftedOrbit k z.2 z.1 n-
          (phi k (liftedOrbit k w.2 w.1 (n+1))-liftedOrbit k w.2 w.1 n)| =
          |liftedOrbit k z.2 z.1 n-liftedOrbit k w.2 w.1 n| := by
        rw [sub_sub_sub_cancel_left,abs_sub_comm]
      rw [he]
      exact max_le hlast hMn
  apply he.trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hM
  have hle : (B-1:ℕ) ≤ n := by rcases hB with rfl|rfl <;> omega
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by norm_num)
lemma graph_backward_endpoint_close (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (n B : ℕ) (hn : 1 ≤ n)
    (hB : B=n ∨ B=n+1)
    (hterm : liftedOrbit k z.1 z.2 (n+1)=liftedOrbit k w.1 w.2 (n+1))
    (hbound : ∀ i : Fin n,
      |liftedOrbit k z.1 z.2 (i+1)-liftedOrbit k w.1 w.2 (i+1)| ≤
        8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) :
    dist (liftIter k (-(B:ℤ)) z) (liftIter k (-(B:ℤ)) w) ≤
      8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) := by
  rw [liftIter_neg_swap,liftIter_neg_swap]
  simpa only [Prod.dist_eq,Prod.fst_swap,Prod.snd_swap,max_comm] using graph_endpoint_close k hk z.swap w.swap n B hn hB hterm hbound
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SweepSlice
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma sweep_slice_bound (I D : Set ℝ) (f : (ℝ × ℝ) → (ℝ × ℝ))
    (J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (w : ℝ → ℝ≥0∞) (g : Torus → ℝ≥0∞) (c : ℝ) (δ : ℝ≥0∞)
    (hI : MeasurableSet I) (hD : MeasurableSet D) (hw : Measurable w) (hg : Measurable g)
    (hJ : ∀ z ∈ I ×ˢ D, HasFDerivWithinAt f (J z) (I ×ˢ D) z)
    (hinj : InjOn f (I ×ˢ D))
    (hlo : ∀ z ∈ I ×ˢ D, c ≤ |(J z).det|)
    (himage : f '' (I ×ˢ D) ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2)
    (hobs : ∀ z ∈ I ×ˢ D, w z.2 ≤ g (liftProjection (f z))+δ) :
    (ENNReal.ofReal c*volume I)*(∫⁻ y in D, w y) ≤
      16*(∫⁻ z, g z ∂area)+(ENNReal.ofReal c*volume I)*δ*volume D := by
  have hbase := weighted_sweep_bound volume (I ×ˢ D) f J c (g ∘ liftProjection)
    (fun z => w z.2) δ (hI.prod hD) hJ hinj hlo hobs
  have he : (∫⁻ z in I ×ˢ D, w z.2) = volume I*(∫⁻ y in D, w y) := by
    change (∫⁻ z, w z.2 ∂(volume.prod volume).restrict (I ×ˢ D)) = _
    have hw' : Measurable (fun z : ℝ × ℝ => w z.2) := hw.comp measurable_snd
    rw [← Measure.prod_restrict,lintegral_prod _ hw'.aemeasurable]
    simp [mul_comm]
  rw [he] at hbase
  have hm : volume (I ×ˢ D) = volume I*volume D := Measure.prod_prod _ _
  rw [hm] at hbase
  calc
    _ = ENNReal.ofReal c*(volume I*(∫⁻ y in D, w y)) := by ring
    _ ≤ (∫⁻ z in f '' (I ×ˢ D), g (liftProjection z))+ENNReal.ofReal c*δ*(volume I*volume D) := hbase
    _ ≤ 16*(∫⁻ z, g z ∂area)+(ENNReal.ofReal c*volume I)*δ*volume D := by
      have h := bounded_lift_integral g hg (f '' (I ×ˢ D)) himage
      calc
        _ ≤ 16*(∫⁻ z, g z ∂area)+ENNReal.ofReal c*δ*(volume I*volume D) := add_le_add h le_rfl
        _ = _ := by ring

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LiftEventMeasure
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma bounded_lift_event (A : Set Torus) (V : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hV : MeasurableSet V) (hb : V ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2)
    (hp : ∀ z ∈ V, liftProjection z ∈ A) : volume V ≤ 16*area A := by
  have hh := bounded_lift_integral (A.indicator (fun _ => (1:ℝ≥0∞)))
    (measurable_const.indicator hA) V hb
  have he : (∫⁻ z in V, A.indicator (fun _ => (1:ℝ≥0∞)) (liftProjection z))=volume V := by
    calc
      _ = ∫⁻ z in V, (1:ℝ≥0∞) := setLIntegral_congr_fun hV (fun z hz => indicator_of_mem (hp z hz) _)
      _ = _ := by simp
  rw [he,lintegral_indicator hA] at hh
  simpa using hh
lemma scaled_product_slice_bound (E I : Set ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ≥0∞)
    (d K : ℝ≥0∞) (hd : d ≠ ∞) (hE : MeasurableSet E) (hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I)
    (hslice : ∀ x ∈ E, d*(∫⁻ y in I, T.indicator f (x,y)) ≤ K) :
    d*(∫⁻ z in T, f z) ≤ K*volume E := by
  have hi (z : ℝ × ℝ) : T.indicator (fun w => d*f w) z=d*T.indicator f z := by
    by_cases hz : z ∈ T <;> simp [hz]
  have hh := product_slice_bound E I T (fun z => d*f z) K hE hI hT hsub (by
    intro x hx
    simpa only [hi,lintegral_const_mul' _ _ hd] using hslice x hx)
  simpa only [lintegral_const_mul' _ _ hd] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaledChart
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma scaled_weighted_chart_product (E I : Set ℝ) (T A V : Set (ℝ × ℝ))
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (D : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (g : ℝ × ℝ → ℝ≥0∞) (c C : ℝ) (d K : ℝ≥0∞) (hd : d ≠ ∞)
    (hE : MeasurableSet E) (hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I) (hA : A ⊆ f '' T) (hV : f '' (E ×ˢ I) ⊆ V)
    (hD : ∀ z ∈ E ×ˢ I, HasFDerivWithinAt f (D z) (E ×ˢ I) z)
    (hinj : InjOn f (E ×ˢ I))
    (hlo : ∀ z ∈ E ×ˢ I, c ≤ |(D z).det|)
    (hhi : ∀ z ∈ E ×ˢ I, |(D z).det| ≤ C)
    (hslice : ∀ x ∈ E, d*(∫⁻ y in I, T.indicator (g ∘ f) (x,y)) ≤ K) :
    (ENNReal.ofReal c*volume I)*d*(∫⁻ z in A, g z) ≤
      ENNReal.ofReal C*K*volume V := by
  have hw := (weighted_image_bounds volume T f D c C g hT
    (fun z hz => (hD z (hsub hz)).mono hsub) (hinj.mono hsub)
    (fun z hz => hlo z (hsub hz)) (fun z hz => hhi z (hsub hz))).2
  have hf : d*(∫⁻ z in A, g z) ≤ ENNReal.ofReal C*(K*volume E) := by
    calc
      _ ≤ d*(ENNReal.ofReal C*(∫⁻ z in T, g (f z))) :=
        mul_le_mul_of_nonneg_left ((lintegral_mono_set hA).trans hw) (by positivity)
      _ = ENNReal.ofReal C*(d*(∫⁻ z in T, g (f z))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (scaled_product_slice_bound E I T (g ∘ f) d K hd hE hI hT hsub hslice) (by positivity)
  have hl := (measure_image_bounds volume (E ×ˢ I) f D c C (hE.prod hI) hD hinj hlo hhi).1
  have hv : (ENNReal.ofReal c*volume I)*volume E ≤ volume V := by
    calc
      _ = ENNReal.ofReal c*volume (E ×ˢ I) := by
        change _ = ENNReal.ofReal c*(volume.prod volume) (E ×ˢ I)
        rw [Measure.prod_prod]; ac_rfl
      _ ≤ volume (f '' (E ×ˢ I)) := hl
      _ ≤ volume V := measure_mono hV
  calc
    _ = (ENNReal.ofReal c*volume I)*(d*(∫⁻ z in A, g z)) := by ring
    _ ≤ (ENNReal.ofReal c*volume I)*(ENNReal.ofReal C*(K*volume E)) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ = (ENNReal.ofReal C*K)*((ENNReal.ofReal c*volume I)*volume E) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BackwardSlice
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_liftProjection : Continuous liftProjection :=
  (((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd))
lemma interval_small_move (y y' : ℝ) (hy : y ∈ Icc (0:ℝ) 1) (hmove : |y'-y| ≤ 1) :
    y' ∈ Ioc (-2:ℝ) 2 := by
  have hh := abs_le.mp hmove
  constructor <;> linarith [hy.1,hy.2,hh.1,hh.2]
lemma actual_backward_slice (k : ℝ) (n B : ℕ) (hn : 1 ≤ n) (hB : B=n ∨ B=n+1) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (ha : 24/growthBase k^((4/5:ℝ)) ≤ 1/2)
    (D : Set ℝ) (hD : MeasurableSet D) (X X' : ℝ → ℝ) (l u : ℝ)
    (hlen : u-l < 1/4) (hlu : Icc l u ⊆ Icc (0:ℝ) 1)
    (hDunit : D ⊆ Icc (0:ℝ) 1)
    (hXI : ∀ y ∈ D, X y ∈ Icc l u)
    (hX : ∀ y ∈ D, HasStrictDerivAt X (X' y) y)
    (hXs : ∀ y ∈ D, |X' y| ≤ 24/growthBase k^((4/5:ℝ)))
    (hXL : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z|)
    (ht : ∀ y ∈ D, tSolution (orbitCoefficient k (X y) y) (n+1) ≠ 0)
    (hU : ∀ y ∈ D, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k (X y) y) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
    (W : Torus → ℝ) (hW : Continuous W) (hW0 : ∀ z, 0 ≤ W z) (δ : ℝ) (hδ : 0 ≤ δ)
    (htransport : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(B:ℤ)) z) (liftIter k (-(B:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) →
      |W (liftProjection z)-W (liftProjection w)| ≤ δ) :
    (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc l u))*
      (∫⁻ y in D, ENNReal.ofReal (W (liftProjection (X y,y)))) ≤
    16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc l u))*
        ENNReal.ofReal δ*volume D := by
  classical
  have hp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have ha0 : 0 ≤ 24/growthBase k^((4/5:ℝ)) := by positivity
  have htrans : (24/growthBase k^((4/5:ℝ)))^2 < 1 := by nlinarith
  obtain ⟨Θ,J,hΘ,hbase,hlevel,hinj,hJ,hdet,hclose⟩ := actual_backward_carry_full_q44 k n hn hk hq hsmall D X X' l u hlen hXI hX hXs hXL htrans ht hU
  let w : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (W (liftProjection (X y,y)))
  have hwc : ContinuousOn w D := by
    apply ENNReal.continuous_ofReal.comp_continuousOn
    apply hW.comp_continuousOn
    apply continuous_liftProjection.comp_continuousOn
    have hxc : ContinuousOn X D := fun y hy => (hX y hy).hasDerivAt.continuousAt.continuousWithinAt
    exact hxc.prodMk continuousOn_id
  have hwm : Measurable (D.indicator w) := by
    exact hwc.measurable_piecewise continuousOn_const hD
  have hbound : (fun z : ℝ × ℝ => (z.1,Θ z)) '' (Icc l u ×ˢ D) ⊆
      Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2 := by
    rintro z ⟨v,hv,rfl⟩
    have hvu := hlu hv.1
    have hxu := hlu (hXI v.2 hv.2)
    have hd : |v.1-X v.2| ≤ 1 := by apply abs_le.mpr; constructor <;> linarith [hvu.1,hvu.2,hxu.1,hxu.2]
    have hc := (hclose v.2 hv.2 v.1 hv.1).1
    refine ⟨⟨by linarith [hvu.1],by linarith [hvu.2]⟩,interval_small_move v.2 (Θ v) (hDunit hv.2) ?_⟩
    exact hc.trans (by nlinarith [abs_nonneg (v.1-X v.2)])
  have htpt (z : ℝ × ℝ) (hz : z ∈ Icc l u ×ˢ D) :
      D.indicator w z.2 ≤ ENNReal.ofReal (W (liftProjection (z.1,Θ z)))+ENNReal.ofReal δ := by
    rw [indicator_of_mem hz.2]
    have he := graph_backward_endpoint_close k hk (z.1,Θ z) (X z.2,z.2) n B hn hB
      (hlevel z.2 hz.2 z.1 hz.1) (hclose z.2 hz.2 z.1 hz.1).2
    have hh := htransport (X z.2,z.2) (z.1,Θ z) (by simpa only [dist_comm] using he)
    calc
      _ ≤ ENNReal.ofReal (W (liftProjection (z.1,Θ z))+δ) := ENNReal.ofReal_le_ofReal (by have := (abs_le.mp hh).2; linarith)
      _ = _ := ENNReal.ofReal_add (hW0 _) hδ
  have hh := sweep_slice_bound (Icc l u) D (fun z : ℝ × ℝ => (z.1,Θ z)) J
    (D.indicator w) (fun z => ENNReal.ofReal (W z)) _ (ENNReal.ofReal δ)
    measurableSet_Icc hD hwm (ENNReal.continuous_ofReal.comp hW).measurable
    hJ hinj (fun z hz => (hdet z hz).1) hbound htpt
  simpa only [setLIntegral_indicator hD,inter_self,w] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ForwardChart
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma forward_chart_jacobian (k : ℝ) (n : ℕ) (E I : Set ℝ) (X : ℝ × ℝ → ℝ) (yc : ℝ)
    (hX : ContinuousOn X (E ×ˢ I))
    (hlevel : ∀ s ∈ E, ∀ y ∈ I,
      liftedOrbit k y (X (s,y)) (n+1)=liftedOrbit k yc s (n+1))
    (ht : ∀ s ∈ E, ∀ y ∈ I, tSolution (orbitCoefficient k y (X (s,y))) (n+1) ≠ 0)
    (hr : ∀ s ∈ E, ∀ y ∈ I,
      Real.exp (-1152*Real.pi) ≤ |tSolution (orbitCoefficient k yc s) (n+1)|/
        |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ∧
      |tSolution (orbitCoefficient k yc s) (n+1)|/
        |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ≤ Real.exp (1152*Real.pi)) :
    ∃ J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      (∀ z ∈ E ×ˢ I, HasFDerivWithinAt (fun w => (X w,w.2)) (J z) (E ×ˢ I) z) ∧
      (∀ z ∈ E ×ˢ I, Real.exp (-1152*Real.pi) ≤ |(J z).det| ∧
        |(J z).det| ≤ Real.exp (1152*Real.pi)) := by
  let J := fun z : ℝ × ℝ => planeMatrix
    (tSolution (orbitCoefficient k yc z.1) (n+1)/tSolution (orbitCoefficient k z.2 (X z)) (n+1))
    (-sSolution (orbitCoefficient k z.2 (X z)) (n+1)/tSolution (orbitCoefficient k z.2 (X z)) (n+1)) 0 1
  refine ⟨J,?_,?_⟩
  · intro z hz
    apply label_graph_derivative (fun v : ℝ × ℝ => liftedOrbit k v.2 v.1 (n+1)) X (E ×ˢ I) z yc _ _ _ _
      (hasStrictFDerivAt_liftedOrbit_swap k (X z) z.2 (n+1))
      (hasStrictFDerivAt_liftedOrbit_swap k z.1 yc (n+1)) (ht z.1 hz.1 z.2 hz.2) (hX z hz)
      _ (hlevel z.1 hz.1 z.2 hz.2)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hlevel w.1 hw.1 w.2 hw.2
  · intro z hz
    simpa only [J,planeMatrix_det,mul_one,mul_zero,sub_zero,abs_div] using hr z.1 hz.1 z.2 hz.2
lemma forward_graph_lipschitz (I : Set ℝ) (X d : ℝ → ℝ) (a : ℝ)
    (hI : Convex ℝ I) (hd : ∀ y ∈ I, HasDerivAt X (d y) y)
    (hb : ∀ y ∈ I, |d y| ≤ a) (y z : ℝ) (hy : y ∈ I) (hz : z ∈ I) :
    |X y-X z| ≤ a*|y-z| := by
  have hh := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hd y hy).hasDerivWithinAt) (by intro y hy; simpa [Real.norm_eq_abs] using hb y hy) hz hy
  simpa only [Real.norm_eq_abs] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalSquareBridge
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma actual_local_square_product (k : ℝ) (hc : BridgeScalarControl k)
    (np nm Bp Bm : ℕ) (hnp : 1 ≤ np) (hnm : 1 ≤ nm)
    (hBp : Bp=np ∨ Bp=np+1) (hBm : Bm=nm ∨ Bm=nm+1) (hBp2 : 2 ≤ Bp) (hBm2 : 2 ≤ Bm)
    (lx ux ly uy : ℝ) (hly : ly ≤ uy) (hlxlen : ux-lx < 1/4) (hlylen : uy-ly < 1/4)
    (hIx : Icc lx ux ⊆ Icc (0:ℝ) 1) (hIy : Icc ly uy ⊆ Icc (0:ℝ) 1)
    (W H : Torus → ℝ) (hW : Continuous W) (hH : Continuous H) (hW0 : ∀ z, 0 ≤ W z)
    (h δ : ℝ) (hδ : 0 ≤ δ) (hδh : δ < h/2)
    (hWp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(Bm:ℤ)) z) (liftIter k (-(Bm:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bm-1:ℕ)) → |W (liftProjection z)-W (liftProjection w)| ≤ δ)
    (hHp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (Bp:ℤ) z) (liftIter k (Bp:ℤ) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bp-1:ℕ)) → |H (liftProjection z)-H (liftProjection w)| ≤ δ) :
    (ENNReal.ofReal (Real.exp (-1152*Real.pi))*volume (Icc ly uy))*
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc lx ux))*
      (∫⁻ z in {z : ℝ × ℝ | z ∈ Icc lx ux ×ˢ Icc ly uy ∧
        prefixEligible k Bp (np+1) z.swap ∧ prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)},
        ENNReal.ofReal (W (liftProjection z))) ≤
    ENNReal.ofReal (Real.exp (1152*Real.pi))*
      (16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
        (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc lx ux))*
          ENNReal.ofReal δ*volume (Icc ly uy))*
      (16*area {z | h/2 < H z}) := by
  classical
  let Ix := Icc lx ux
  let Iy := Icc ly uy
  let square := Ix ×ˢ Iy
  let S : Set (ℝ × ℝ) := (Iy ×ˢ Ix) ∩
    {z | prefixEligible k Bp (np+1) z ∧ h ≤ H (liftProjection z.swap)}
  have hS : IsCompact S := by
    apply (isCompact_Icc.prod isCompact_Icc).inter_right
    exact (isClosed_prefixEligible k Bp (np+1)).inter
      (isClosed_le continuous_const (hH.comp (continuous_liftProjection.comp continuous_swap)))
  have hdir (z : ℝ × ℝ) (hz : z ∈ S) := hc.prefix_dirichlet_q44 Bp np hnp hBp hBp2 z hz.2.1
  obtain ⟨E,X,hE,hX,hXbase,hcover,hinj,hreg,hrep⟩ := actual_compact_graph_labels_full_q44 k np hnp
    hc.nonneg hc.graph_geom hc.graph_small S hS (fun z hz => (hdir z hz).1)
    (fun z hz => (hdir z hz).2) ly uy ly ⟨le_rfl,hly⟩ hlylen (fun z hz => hz.1.1)
  let f : (ℝ × ℝ) → (ℝ × ℝ) := fun z => (X z,z.2)
  have hfc : ContinuousOn f (E ×ˢ Iy) := hX.prodMk continuous_snd.continuousOn
  obtain ⟨J,hJ,hdet⟩ := forward_chart_jacobian k np E Iy X ly hX
    (fun s hs y hy => (hreg s hs y hy).1)
    (fun s hs y hy => (hreg s hs y hy).2.1)
    (fun s hs y hy => (hreg s hs y hy).2.2.2.2)
  let V := f '' (E ×ˢ Iy)
  have hV : IsCompact V := (hE.prod isCompact_Icc).image_of_continuousOn hfc
  have hVH : ∀ z ∈ V, liftProjection z ∈ {z | h/2 < H z} := by
    rintro z ⟨v,hv,rfl⟩
    obtain ⟨w,hw,hwX⟩ := hrep v.1 hv.1
    have hh := graph_endpoint_close k hc.nonneg (f v) w.swap np Bp hnp hBp
      (hwX v.2 hv.2).1 (hwX v.2 hv.2).2.2
    have htpt := hHp (f v) w.swap hh
    have hth := hw.2.2
    change h/2 < H (liftProjection (f v))
    have hab := (abs_le.mp htpt).1
    linarith
  have hVb : V ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2 := by
    rintro z ⟨v,hv,rfl⟩
    obtain ⟨w,hw,hwX⟩ := hrep v.1 hv.1
    have hy := hIy hv.2
    have hyw := hIy hw.1.1
    have hxw := hIx hw.1.2
    have hd : |v.2-w.1| ≤ 1 := by apply abs_le.mpr; constructor <;> linarith [hy.1,hy.2,hyw.1,hyw.2]
    have hmove := (hwX v.2 hv.2).2.1
    have ha0 : 0 ≤ 24/growthBase k^((4/5:ℝ)) := by
      have hp : 0 < growthBase k := by have := growthBase_ge_four k hc.nonneg; linarith
      positivity
    refine ⟨interval_small_move w.2 (X v) hxw (hmove.trans ?_),⟨by linarith [hy.1],by linarith [hy.2]⟩⟩
    nlinarith [hc.slope_small,abs_nonneg (v.2-w.1)]
  have hVm : volume V ≤ 16*area {z | h/2 < H z} :=
    bounded_lift_event _ V (isOpen_lt continuous_const hH).measurableSet hV.measurableSet hVb hVH
  let U : Set (ℝ × ℝ) := square ∩ {z | prefixEligible k Bm (nm+1) z}
  have hUcl : IsClosed U := (isClosed_Icc.prod isClosed_Icc).inter (isClosed_prefixEligible k Bm (nm+1))
  let T := (E ×ˢ Iy) ∩ f ⁻¹' U
  have hTcl : IsClosed T := hfc.preimage_isClosed_of_isClosed (hE.isClosed.prod isClosed_Icc) hUcl
  let A := {z : ℝ × ℝ | z ∈ square ∧ prefixEligible k Bp (np+1) z.swap ∧
    prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)}
  have hA : A ⊆ f '' T := by
    intro z hz
    have hzS : z.swap ∈ S := ⟨⟨hz.1.2,hz.1.1⟩,hz.2.1,by simpa only [Prod.swap_swap] using hz.2.2.2.le⟩
    obtain ⟨s,hs,hxs⟩ := hcover z.swap hzS
    change X (s,z.2)=z.1 at hxs
    refine ⟨(s,z.2),⟨⟨hs,hz.1.2⟩,?_⟩,?_⟩
    · change (X (s,z.2),z.2) ∈ U
      rw [hxs]
      exact ⟨hz.1,hz.2.2.1⟩
    · exact Prod.ext hxs rfl
  let c := Real.exp (-1152*Real.pi)
  let C := Real.exp (1152*Real.pi)
  let d := ENNReal.ofReal (c*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume Ix
  let K := 16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+d*ENNReal.ofReal δ*volume Iy
  have hslice (s : ℝ) (hs : s ∈ E) : d*(∫⁻ y in Iy, T.indicator ((fun z => ENNReal.ofReal (W (liftProjection z))) ∘ f) (s,y)) ≤ K := by
    let Xs : ℝ → ℝ := fun y => X (s,y)
    let Xs' : ℝ → ℝ := fun y => boundaryValue (orbitCoefficient k y (Xs y)) (np+1)
    let D : Set ℝ := Iy ∩ (fun y => (Xs y,y)) ⁻¹' U
    have hXs : ContinuousOn Xs Iy := hX.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨hs,hy⟩)
    have hDc : IsClosed D := (hXs.prodMk continuousOn_id).preimage_isClosed_of_isClosed isClosed_Icc hUcl
    have hxi (y : ℝ) (hy : y ∈ D) : Xs y ∈ Ix := hy.2.1.1
    have hxd (y : ℝ) (hy : y ∈ Iy) : HasStrictDerivAt Xs (Xs' y) y := (hreg s hs y hy).2.2.1
    have hxS (y : ℝ) (hy : y ∈ Iy) : |Xs' y| ≤ 24/growthBase k^((4/5:ℝ)) := (hreg s hs y hy).2.2.2.1
    have hxL (y : ℝ) (hy : y ∈ D) (z : ℝ) (hz : z ∈ D) :
        |Xs y-Xs z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z| :=
      forward_graph_lipschitz Iy Xs Xs' _ (convex_Icc ly uy)
        (fun y hy => (hxd y hy).hasDerivAt) hxS y z hy.1 hz.1
    have hdirD (y : ℝ) (hy : y ∈ D) := hc.prefix_dirichlet_q44 Bm nm hnm hBm hBm2 (Xs y,y) hy.2.2
    have hb := actual_backward_slice k nm Bm hnm hBm hc.nonneg hc.graph_geom hc.graph_small hc.slope_small
      D hDc.measurableSet Xs Xs' lx ux hlxlen hIx (fun y hy => hIy hy.1)
      hxi (fun y hy => hxd y hy.1) (fun y hy => hxS y hy.1) hxL
      (fun y hy => (hdirD y hy).1) (fun y hy => (hdirD y hy).2) W hW hW0 δ hδ hWp
    have he : (fun y => T.indicator ((fun z => ENNReal.ofReal (W (liftProjection z))) ∘ f) (s,y)) =
        D.indicator (fun y => ENNReal.ofReal (W (liftProjection (Xs y,y)))) := by
      funext y
      by_cases hy : y ∈ D
      · have ht : (s,y) ∈ T := ⟨⟨hs,hy.1⟩,hy.2⟩
        simp only [indicator_of_mem ht,indicator_of_mem hy,Function.comp_apply,f,Xs]
      · have ht : (s,y) ∉ T := fun ht => hy ⟨ht.1.2,ht.2⟩
        simp only [indicator_of_notMem ht,indicator_of_notMem hy]
    rw [he,setLIntegral_indicator hDc.measurableSet,inter_eq_left.mpr (show D ⊆ Iy from inter_subset_left)]
    apply hb.trans
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (measure_mono (show D ⊆ Iy from inter_subset_left)) (by positivity)
  have hb := scaled_weighted_chart_product E Iy T A V f J
    (fun z => ENNReal.ofReal (W (liftProjection z))) c C d K
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ)))))
    hE.measurableSet measurableSet_Icc hTcl.measurableSet inter_subset_left hA Subset.rfl
    hJ hinj (fun z hz => (hdet z hz).1) (fun z hz => (hdet z hz).2) hslice
  exact hb.trans (mul_le_mul_of_nonneg_left hVm (by positivity))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GridBridge
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma bridgeGrid_length (i : Fin 32) : bridgeGridHi i-bridgeGridLo i=1/32 := by
  unfold bridgeGridHi bridgeGridLo; ring
lemma bridgeGrid_order (i : Fin 32) : bridgeGridLo i ≤ bridgeGridHi i := by
  have := bridgeGrid_length i; linarith
lemma bridgeGrid_subset (i : Fin 32) : bridgeGridCell i ⊆ Icc (0:ℝ) 1 := by
  intro x hx
  have hi0 : (0:ℝ) ≤ i := by positivity
  have hi1 : (i:ℝ) < 32 := by exact_mod_cast i.isLt
  change (i:ℝ)/32 ≤ x ∧ x ≤ ((i:ℝ)+1)/32 at hx
  have hi2 : (i:ℝ) ≤ 31 := by exact_mod_cast (show (i:ℕ) ≤ 31 by omega)
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
lemma bridgeGrid_volume (i : Fin 32) : volume (bridgeGridCell i)=(1/32 : ℝ≥0∞) := by
  rw [bridgeGridCell,Real.volume_Icc,bridgeGrid_length,ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num
lemma actual_grid_square_product_q44_oai (k : ℝ) (hc : BridgeScalarControl k)
    (np nm Bp Bm : ℕ) (hnp : 1 ≤ np) (hnm : 1 ≤ nm)
    (hBp : Bp=np ∨ Bp=np+1) (hBm : Bm=nm ∨ Bm=nm+1) (hBp2 : 2 ≤ Bp) (hBm2 : 2 ≤ Bm)
    (ix iy : Fin 32)
    (W H : Torus → ℝ) (hW : Continuous W) (hH : Continuous H) (hW0 : ∀ z, 0 ≤ W z)
    (h δ : ℝ) (hδ : 0 ≤ δ) (hδh : δ < h/2)
    (hWp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(Bm:ℤ)) z) (liftIter k (-(Bm:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bm-1:ℕ)) → |W (liftProjection z)-W (liftProjection w)| ≤ δ)
    (hHp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (Bp:ℤ) z) (liftIter k (Bp:ℤ) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bp-1:ℕ)) → |H (liftProjection z)-H (liftProjection w)| ≤ δ) :
    bridgeAreaScale *
      (∫⁻ z in {z : ℝ × ℝ | z ∈ bridgeGridCell ix ×ˢ bridgeGridCell iy ∧
        prefixEligible k Bp (np+1) z.swap ∧ prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)},
        ENNReal.ofReal (W (liftProjection z))) ≤
    bridgeLocalConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*area {z | h/2 < H z} := by
  have hh := actual_local_square_product k hc np nm Bp Bm hnp hnm hBp hBm hBp2 hBm2
    (bridgeGridLo ix) (bridgeGridHi ix) (bridgeGridLo iy) (bridgeGridHi iy)
    (bridgeGrid_order iy) (by rw [bridgeGrid_length]; norm_num) (by rw [bridgeGrid_length]; norm_num)
    (bridgeGrid_subset ix) (bridgeGrid_subset iy) W H hW hH hW0 h δ hδ hδh hWp hHp
  change (ENNReal.ofReal (Real.exp (-1152*Real.pi))*volume (bridgeGridCell iy))*
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (bridgeGridCell ix))*_ ≤
    ENNReal.ofReal (Real.exp (1152*Real.pi))*(16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (bridgeGridCell ix))*
        ENNReal.ofReal δ*volume (bridgeGridCell iy))*(16*area {z | h/2 < H z}) at hh
  rw [bridgeGrid_volume,bridgeGrid_volume] at hh
  have hMp : 0 < growthBase k := by have := growthBase_ge_four k hc.nonneg; linarith
  have ha0 : 0 ≤ 24/growthBase k^((4/5:ℝ)) := by positivity
  have ha2 : (24/growthBase k^((4/5:ℝ)))^2 ≤ 1/4 := by nlinarith [hc.slope_small]
  have hl : Real.exp (-1152*Real.pi)*(3/4) ≤ Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hu : ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2)) ≤ 1 := by
    apply (ENNReal.ofReal_le_one).mpr
    have hc1 : Real.exp (-1152*Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (by have := Real.pi_pos; linarith)
    calc
      _ ≤ Real.exp (-1152*Real.pi)*1 := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (24/growthBase k^((4/5:ℝ)))]) (Real.exp_pos _).le
      _ ≤ 1 := by simpa using hc1
  have hs : (1/32:ℝ≥0∞) ≤ 1 := by norm_num
  apply le_trans (mul_le_mul_of_nonneg_right (show bridgeAreaScale ≤
      (ENNReal.ofReal (Real.exp (-1152*Real.pi))*(1/32))*
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*(1/32)) from by
        unfold bridgeAreaScale; gcongr) (by positivity))
  apply hh.trans
  have he : (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*(1/32))*
       ENNReal.ofReal δ*(1/32) ≤ ENNReal.ofReal δ := by
    calc
      _ ≤ (1*1)*ENNReal.ofReal δ*1 := by gcongr
      _ = _ := by simp
  calc
    _ ≤ ENNReal.ofReal (Real.exp (1152*Real.pi))*(16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*(16*area {z | h/2 < H z}) := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp (1152*Real.pi))*(16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+16*ENNReal.ofReal δ)*(16*area {z | h/2 < H z}) := by gcongr; exact le_mul_of_one_le_left bot_le (by norm_num)
    _ = _ := by unfold bridgeLocalConstant; ring
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.actual_grid_square_product_q44_oai := @OAI.StandardMapEntropy.actual_grid_square_product_q44_oai
