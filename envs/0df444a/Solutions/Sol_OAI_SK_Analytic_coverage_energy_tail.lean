-- Prove2me | solution 1 for OAI.SK.Analytic.coverage_energy_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:02:50.892514+00:00
-- url     : https://prove2.me/submissions/7c31e968-d952-4f28-a8e5-341869c0f167

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004
import Theorems.Thm_OAI_SK_Analytic_quenchedPressure_tendsto_finiteParisiInf
import Theorems.Thm_OAI_SK_Analytic_skBlockPressure_hasDerivAt

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_Basic
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem disorder_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun J : Disorder n => J e) (gaussianReal 0 1) (disorderLaw n) := by
  exact (measurePreserving_eval (fun _ : Edge n => gaussianReal 0 1) e).hasLaw

theorem disorder_coordinate_gaussian {n : ℕ} (e : Edge n) :
    HasGaussianLaw (fun J : Disorder n => J e) (disorderLaw n) :=
  (disorder_coordinate_law e).hasGaussianLaw

theorem disorder_independent (n : ℕ) :
    iIndepFun (fun e (J : Disorder n) => J e) (disorderLaw n) := by
  exact iIndepFun_pi (fun _ => aemeasurable_id)

theorem disorder_gaussian (n : ℕ) : HasGaussianLaw (fun J : Disorder n => J) (disorderLaw n) :=
  (disorder_independent n).hasGaussianLaw disorder_coordinate_gaussian

theorem hamiltonian_gaussian {n : ℕ} (x : Config n) :
    HasGaussianLaw (fun J : Disorder n => hamiltonian J x) (disorderLaw n) := by
  have h : HasGaussianLaw
      (fun J : Disorder n => fun e : Edge n =>
        J e * spin (x e.val.1) * spin (x e.val.2)) (disorderLaw n) := by
    have hi : iIndepFun (fun e (J : Disorder n) =>
        J e * spin (x e.val.1) * spin (x e.val.2)) (disorderLaw n) := by
      exact iIndepFun_pi (μ := fun _ : Edge n => gaussianReal 0 1)
        (X := fun e z => z * spin (x e.val.1) * spin (x e.val.2))
        (fun _ => by fun_prop)
    apply hi.hasGaussianLaw
    intro e
    convert (disorder_coordinate_gaussian e).fun_smul
      (spin (x e.val.1) * spin (x e.val.2)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [smul_eq_mul]
    funext J
    ring
  simpa only [hamiltonian, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    h.fun_sum.fun_smul (Real.sqrt n)⁻¹

theorem disorder_mean_zero {n : ℕ} (e : Edge n) :
    ∫ J : Disorder n, J e ∂disorderLaw n = 0 := by
  rw [disorderLaw, integral_eval]
  exact integral_id_gaussianReal

theorem hamiltonian_mean_zero {n : ℕ} (x : Config n) :
    ∫ J : Disorder n, hamiltonian J x ∂disorderLaw n = 0 := by
  simp only [hamiltonian, div_eq_mul_inv]
  rw [integral_mul_const, integral_finsetSum]
  · simp only [integral_mul_const, disorder_mean_zero, zero_mul, Finset.sum_const_zero]
  · intro e _
    exact ((disorder_coordinate_gaussian e).integrable.mul_const _).mul_const _

theorem disorder_covariance {n : ℕ} (e f : Edge n) :
    cov[fun J : Disorder n => J e, fun J : Disorder n => J f; disorderLaw n] =
      if e = f then 1 else 0 := by
  classical
  by_cases hef : e = f
  · subst f
    rw [covariance_self (disorder_coordinate_gaussian e).aemeasurable, (disorder_coordinate_law e).variance_eq]
    simp
  · rw [(disorder_independent n).indepFun hef |>.covariance_eq_zero
      (disorder_coordinate_gaussian e).memLp_two
      (disorder_coordinate_gaussian f).memLp_two]
    simp [hef]

theorem hamiltonian_covariance_edges {n : ℕ} (x y : Config n) :
    cov[fun J : Disorder n => hamiltonian J x,
      fun J : Disorder n => hamiltonian J y; disorderLaw n] =
    (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
      (spin (y e.val.1) * spin (y e.val.2))) / n := by
  classical
  simp only [hamiltonian, div_eq_mul_inv, covariance_mul_const_left,
    covariance_mul_const_right]
  rw [covariance_fun_sum_fun_sum]
  · simp only [covariance_mul_const_left, covariance_mul_const_right, disorder_covariance]
    have hsum : (∑ e : Edge n, ∑ f : Edge n,
        (if e = f then (1 : ℝ) else 0) * spin (x e.val.1) * spin (x e.val.2) *
          spin (y f.val.1) * spin (y f.val.2)) =
        ∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
          (spin (y e.val.1) * spin (y e.val.2)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_eq_single e]
      · simp [mul_assoc]
      · intro f _ hfe
        simp [Ne.symm hfe]
      · simp
    rw [hsum]
    rw [mul_assoc, ← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg n)]
  · intro e
    exact ((disorder_coordinate_gaussian e).memLp_two.mul_const _).mul_const _
  · intro e
    exact ((disorder_coordinate_gaussian e).memLp_two.mul_const _).mul_const _

theorem sum_edges {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ e : Edge n, f e.val) = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then f (i, j) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (by simp) f]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem sum_sq_eq_edges {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i) ^ 2 = (∑ i, (a i) ^ 2) + 2 * ∑ e : Edge n, a e.val.1 * a e.val.2 := by
  classical
  rw [sum_edges (fun p : Fin n × Fin n => a p.1 * a p.2), pow_two, Fintype.sum_mul_sum]
  have hsplit (i j : Fin n) : a i * a j =
      (if i = j then a i ^ 2 else 0) +
      (if i < j then a i * a j else 0) +
      (if j < i then a i * a j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j
      simp [pow_two]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, a i * a j) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((if i = j then a i ^ 2 else 0) +
        (if i < j then a i * a j else 0) +
        (if j < i then a i * a j else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsplit i j
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hd : (∑ i : Fin n, ∑ j : Fin n, if i = j then a i ^ 2 else 0) =
      ∑ i, a i ^ 2 := by simp
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then a i * a j else 0 := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hd, hs]
  ring

theorem overlap_self {n : ℕ} (hn : 0 < n) (x : Config n) : overlap x x = 1 := by
  simp only [overlap, ← pow_two, spin_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hn.ne')

theorem hamiltonian_covariance {n : ℕ} (hn : 0 < n) (x y : Config n) :
    cov[fun J : Disorder n => hamiltonian J x,
      fun J : Disorder n => hamiltonian J y; disorderLaw n] =
      ((n : ℝ) * overlap x y ^ 2 - 1) / 2 := by
  rw [hamiltonian_covariance_edges]
  have hs := sum_sq_eq_edges (fun i => spin (x i) * spin (y i))
  have hd : (∑ i : Fin n, (spin (x i) * spin (y i)) ^ 2) = (n : ℝ) := by
    simp [mul_pow]
  rw [hd] at hs
  have he : (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
      (spin (y e.val.1) * spin (y e.val.2))) =
      ((∑ i : Fin n, spin (x i) * spin (y i)) ^ 2 - n) / 2 := by
    have hr : (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
        (spin (y e.val.1) * spin (y e.val.2))) =
        ∑ e : Edge n, (spin (x e.val.1) * spin (y e.val.1)) *
          (spin (x e.val.2) * spin (y e.val.2)) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [hr]
    linarith
  rw [he, overlap]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn']

theorem hamiltonian_variance {n : ℕ} (hn : 0 < n) (x : Config n) :
    Var[fun J : Disorder n => hamiltonian J x; disorderLaw n] = ((n : ℝ) - 1) / 2 := by
  rw [← covariance_self (hamiltonian_gaussian x).aemeasurable,
    hamiltonian_covariance hn, overlap_self hn]
  ring

theorem gaussian_exp_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : HasGaussianLaw X μ) (t : ℝ) :
    (∫ ω, Real.exp (t * X ω) ∂μ) =
      Real.exp ((∫ ω, X ω ∂μ) * t + Var[X; μ] * t ^ 2 / 2) := by
  change mgf X μ t = _
  rw [mgf_gaussianReal hX.map_eq_gaussianReal,
    Real.coe_toNNReal _ (variance_nonneg X μ)]

theorem gaussian_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : HasGaussianLaw X μ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  have := hX.isProbabilityMeasure
  rw [← mgf_pos_iff, mgf_gaussianReal hX.map_eq_gaussianReal]
  exact Real.exp_pos _

theorem hamiltonian_exp_integral {n : ℕ} (hn : 0 < n) (x : Config n) (t : ℝ) :
    (∫ J : Disorder n, Real.exp (t * hamiltonian J x) ∂disorderLaw n) =
      Real.exp (t ^ 2 * ((n : ℝ) - 1) / 4) := by
  rw [gaussian_exp_integral (hamiltonian_gaussian x),
    hamiltonian_mean_zero, hamiltonian_variance hn]
  congr 1
  ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateGaussianLaw
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem coordinateArray_continuous (n : ℕ) : Continuous (coordinateArray n) :=
  continuous_pi (fun i => (coordinateProjection n i).continuous)

theorem coordinateArray_measurePreserving (n : ℕ) (x : ℝ) :
    MeasurePreserving (coordinateArray n) (fiberGaussian n x)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  induction n with
  | zero =>
    refine ⟨(coordinateArray_continuous 0).measurable,?_⟩
    rw [fiberGaussian,Measure.map_dirac' (coordinateArray_continuous 0).measurable,
      Measure.pi_of_empty _ (coordinateArray 0 x)]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)
    have he : MeasurePreserving e (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))
        ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :=
      measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) (Fin.last n)
    have hprod := (Measure.measurePreserving_swap (μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (ν := gaussianReal 0 1)).comp (ih.prod (MeasurePreserving.id (gaussianReal 0 1)))
    have H := he.symm.comp hprod
    convert H using 1 <;> try rfl
    funext z
    apply e.injective
    rw [Function.comp_apply,e.apply_symm_apply]
    apply Prod.ext
    · simp [e,coordinateArray,coordinateProjection]
    · funext i
      simp [e,coordinateArray,coordinateProjection,Fin.init]

theorem enumeratedDisorder_measurePreserving (N : ℕ) (x : ℝ) :
    MeasurePreserving (enumeratedDisorder N) (fiberGaussian (Fintype.card (Edge N)) x)
      (disorderLaw N) := by
  have H := (measurePreserving_piCongrLeft (fun _ : Edge N => gaussianReal 0 1)
    (Fintype.equivFin (Edge N)).symm).comp (coordinateArray_measurePreserving (Fintype.card (Edge N)) x)
  convert H using 1
  · funext z e
    simp [enumeratedDisorder, coordinateArray, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  · rfl
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert! h using 1
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one,
      Pi.neg_apply,Pi.pow_apply,id_eq]
  · simp only [Pi.neg_apply,Pi.pow_apply,id_eq]
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    norm_num
    ring

theorem integrable_standardGaussian_iff (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => f x*gaussianPDFReal 0 1 x) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul,mul_comm]

theorem gaussian_integral_mul_eq_integral_deriv (f f' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable f (gaussianReal 0 1))
    (hi' : Integrable f' (gaussianReal 0 1))
    (hix : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    (∫ x, x*f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hi₀ := (integrable_standardGaussian_iff f).mp hi
  have hi₁ := (integrable_standardGaussian_iff f').mp hi'
  have hi₂ := (integrable_standardGaussian_iff (fun x => x*f x)).mp hix
  have hx : Integrable (fun x => f x*(-x*gaussianPDFReal 0 1 x)) := by
    convert hi₂.neg using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change _ = -(x*f x*gaussianPDFReal 0 1 x)
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardGaussianPDF x) hx hi₁ hi₀
  have he : (fun x => f x*(-x*gaussianPDFReal 0 1 x)) =
      (fun x => -(gaussianPDFReal 0 1 x*(x*f x))) := by funext x; ring
  rw [he,integral_neg] at h
  have h' := neg_injective h
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simpa only [smul_eq_mul,mul_comm] using h'

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [-instance] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Translation
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem TranslationInvariant.gaussianStep {f : E × ℝ → ℝ} {u : E}
    (hi : TranslationInvariant f (u,0)) (m : ℝ) : TranslationInvariant (gaussianStep m f) u := by
  intro z t
  have he (y : ℝ) : f (z+t • u,y) = f (z,y) := by
    simpa only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero] using hi (z,y) t
  unfold SK.Analytic.gaussianStep positiveGaussianLogStep
  simp only [he]

theorem affineLogPartition_translation {S : Type} [Fintype S]
    (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (u : E) (hu : ∀ s, L s u = 0) :
    TranslationInvariant (affineLogPartition c L) u := by
  intro z t
  simp only [affineLogPartition,map_add,map_smul,hu,smul_eq_mul,mul_zero,add_zero]

end Translation

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeBlockLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem gaussianStep_append (a b : ℕ) (p : ℝ) (f : ParameterSpace (a+(b+1)) → ℝ) :
    gaussianStep p (fun z => f (parameterAppend a (b+1) z)) =
      fun z => gaussianStep p f (parameterAppend a b z) := by
  rfl

theorem hierarchyPressure_split (a b : ℕ) (m : Fin (a+b) → ℝ)
    (f : ParameterSpace (a+b) → ℝ) :
    hierarchyPressure (a+b) m f = hierarchyPressure a (fun i => m (Fin.castAdd b i))
      (cascadePressure b (fun i => m (Fin.natAdd a i)) (fun z => f (parameterAppend a b z))) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change hierarchyPressure ((a+b)+1) m f = _
    rw [hierarchyPressure,ih,cascadePressure,gaussianStep_append]
    rfl

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianStepAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStep_sum_independent {I : Type} [Fintype I] [DecidableEq I]
    (f : I → E × ℝ → ℝ) (hf : ∀ i, BoundedDerivs (f i)) (j : I)
    (hi : ∀ i, i ≠ j → TranslationInvariant (f i) (0,1)) (m : ℝ) :
    gaussianStep m (fun z => ∑ i, f i z) = fun x => ∑ i, gaussianStep m (f i) x := by
  have he (i : I) (h : i ≠ j) (x : E) (y : ℝ) : f i (x,y) = f i (x,0) := by
    simpa using hi i h (x,0) y
  have hex : (fun z => ∑ i, f i z) = fun z => f j z+∑ i ∈ Finset.univ.erase j, f i (z.1,0) := by
    funext z
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    apply Finset.sum_congr rfl
    intro i h
    exact he i (Finset.mem_erase.mp h).1 z.1 z.2
  rw [hex,gaussianStep_add_prefix (hf j) (fun x => ∑ i ∈ Finset.univ.erase j, f i (x,0)) m]
  funext x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  congr 1
  apply Finset.sum_congr rfl
  intro i h
  have H : f i = fun z => f i (z.1,0) := funext (fun z => he i (Finset.mem_erase.mp h).1 z.1 z.2)
  rw [H,gaussianStep_prefix (fun y => f i (y,0)) m]
end Generic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPressure_zero (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (x : ℝ) :
    hierarchyPressure n (fun _ => 0) f x = ∫ z, f z ∂fiberGaussian n x := by
  induction n with
  | zero => simp [hierarchyPressure,fiberGaussian]
  | succ n ih =>
    rw [hierarchyPressure,ih _ (hf.gaussianStep 0),fiberGaussian,
      integral_prod _ (hf.hasExpGrowth.integrable_fiberGaussian (n+1) hf.1.continuous x)]
    simp only [gaussianStep,ite_true]

theorem hierarchyPressure_sum_independent {I : Type} [Fintype I] [DecidableEq I]
    (n : ℕ) (m : Fin n → ℝ) (owner : Fin n → I)
    (f : I → ParameterSpace n → ℝ) (hf : ∀ i, BoundedDerivs (f i))
    (hi : ∀ t i, i ≠ owner t → TranslationInvariant (f i) (coordinateAxis n t)) :
    hierarchyPressure n m (fun z => ∑ i, f i z) = fun x => ∑ i, hierarchyPressure n m (f i) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hierarchyPressure,gaussianStep_sum_independent f hf (owner (Fin.last n))
      (by simpa only [coordinateAxis_last] using hi (Fin.last n))]
    rw [ih (fun t => m t.castSucc) (fun t => owner t.castSucc)
      (fun i => gaussianStep (m (Fin.last n)) (f i))
      (fun i => (hf i).gaussianStep _) (fun t i h => ?_)]
    · rfl
    · apply TranslationInvariant.gaussianStep
      simpa only [coordinateAxis_castSucc] using hi t.castSucc i h
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BlockStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem normalizedDot_sq_le {N : ℕ} (a b : Fin N → ℝ) :
    (normalizedDot a b)^2 ≤ normalizedSquare a*normalizedSquare b := by
  have H := div_le_div_of_nonneg_right
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b) (sq_nonneg (N : ℝ))
  simpa only [normalizedDot,normalizedSquare,div_pow,div_mul_div_comm,← pow_two] using H

theorem abs_normalizedDot_le {N : ℕ} (a b : Fin N → ℝ) :
    |normalizedDot a b| ≤ Real.sqrt (normalizedSquare a)*Real.sqrt (normalizedSquare b) := by
  rw [← Real.sqrt_mul (normalizedSquare_nonneg a)]
  apply Real.le_sqrt_of_sq_le
  simpa only [sq_abs] using normalizedDot_sq_le a b

end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section MeanTower
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyMeanSquare_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) (x : ℝ) :
    Integrable (hierarchyMeanSquare n m U c j)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) x) := by
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (hierarchyMeanSquare_continuous n m U c hc j) (C := 1) _ x
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyMeanSquare_bounds n m U c hc j z).1]
  exact (hierarchyMeanSquare_bounds n m U c hc j z).2

theorem hierarchyMeanOverlap_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) :
    hierarchyMeanOverlap n m U c j ∈ Set.Icc (0 : ℝ) 1 := by
  let f := affineLogPartition (fun _ => 0) U
  let := hierarchyPathLaw_probability n m f (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  refine ⟨integral_nonneg (fun z => (hierarchyMeanSquare_bounds n m U c hc j z).1),?_⟩
  calc
    _ ≤ ∫ _ : ParameterSpace n, (1 : ℝ) ∂hierarchyPathLaw n m f 0 :=
      integral_mono (hierarchyMeanSquare_integrable n m U c hc j 0) (integrable_const 1)
        (fun z => (hierarchyMeanSquare_bounds n m U c hc j z).2)
    _ = 1 := by simp

end MeanTower
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockMassValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

 theorem blockMass_eq_sum (D N k : ℕ) (i : Fin (blockDimension D N k)) :
    blockMass D N k i = ∑ b : Fin (k+1),
      if (blockLevel D N k b).val ≤ i.val then ((k+1 : ℕ) : ℝ)⁻¹ else 0 := by
  unfold blockMass massFromAtoms blockAtom
  calc
    _ = ∑ t : Fin (blockDimension D N k+1), ∑ b : Fin (k+1),
      if blockLevel D N k b = t then
        (if t.val ≤ i.val then ((k+1 : ℕ) : ℝ)⁻¹ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val ≤ i.val <;> simp only [ht,ite_true,ite_false,ite_self,Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem blockMass_at_field (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    blockMass D N k (fieldIndex D N k b i) = (b.val : ℝ)/((k+1 : ℕ) : ℝ) := by
  rw [blockMass_eq_sum]
  have hh (c : Fin (k+1)) : (blockLevel D N k c).val ≤ (fieldIndex D N k b i).val ↔ c < b := by
    simp only [blockLevel_val,fieldIndex_val,Fin.lt_def]
    constructor
    · intro h
      by_contra hn
      have hc : b.val ≤ c.val := by omega
      have hc' := Nat.mul_le_mul_right N hc
      nlinarith [i.isLt]
    · intro h
      have hc := Nat.mul_le_mul_right N h
      nlinarith
  simp only [hh]
  rw [← Finset.sum_filter]
  have hs : Finset.univ.filter (fun c : Fin (k+1) => c < b) = Finset.Iio b := by
    ext c
    simp
  rw [hs]
  simp only [Finset.sum_const,Fin.card_Iio,nsmul_eq_mul,div_eq_mul_inv]
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_DisorderPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

instance disorderLaw_isGaussian (n : ℕ) : IsGaussian (disorderLaw n) := by
  have h := (disorder_gaussian n).isGaussian_map
  change IsGaussian (Measure.map id (disorderLaw n)) at h
  rwa [Measure.map_id] at h

theorem disorderPair_fst_law (n : ℕ) :
    HasLaw (Prod.fst : Disorder n × Disorder n → Disorder n)
      (disorderLaw n) (disorderPairLaw n) :=
  measurePreserving_fst.hasLaw

theorem disorderPair_snd_law (n : ℕ) :
    HasLaw (Prod.snd : Disorder n × Disorder n → Disorder n)
      (disorderLaw n) (disorderPairLaw n) :=
  measurePreserving_snd.hasLaw

theorem disorderPair_independent (n : ℕ) :
    IndepFun (Prod.fst : Disorder n × Disorder n → Disorder n)
      Prod.snd (disorderPairLaw n) := by
  apply (indepFun_iff_hasLaw_prodMk_prod (disorderPair_fst_law n)
    (disorderPair_snd_law n)).2
  exact HasLaw.id

theorem disorderPair_gaussian (n : ℕ) :
    HasGaussianLaw (fun p : Disorder n × Disorder n => p) (disorderPairLaw n) :=
  (disorderPair_independent n).hasGaussianLaw (disorderPair_fst_law n).hasGaussianLaw
    (disorderPair_snd_law n).hasGaussianLaw

theorem disorderPair_fst_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun p : Disorder n × Disorder n => p.1 e)
      (gaussianReal 0 1) (disorderPairLaw n) :=
  (disorder_coordinate_law e).fun_comp (disorderPair_fst_law n)

theorem disorderPair_snd_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun p : Disorder n × Disorder n => p.2 e)
      (gaussianReal 0 1) (disorderPairLaw n) :=
  (disorder_coordinate_law e).fun_comp (disorderPair_snd_law n)

theorem disorderPair_fst_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.1 e,
      fun p : Disorder n × Disorder n => p.1 f; disorderPairLaw n] =
      if e = f then 1 else 0 := by
  rw [(disorderPair_fst_law n).covariance_fun_comp
    (disorder_coordinate_law e).aemeasurable (disorder_coordinate_law f).aemeasurable]
  exact disorder_covariance e f

theorem disorderPair_snd_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.2 e,
      fun p : Disorder n × Disorder n => p.2 f; disorderPairLaw n] =
      if e = f then 1 else 0 := by
  rw [(disorderPair_snd_law n).covariance_fun_comp
    (disorder_coordinate_law e).aemeasurable (disorder_coordinate_law f).aemeasurable]
  exact disorder_covariance e f

theorem disorderPair_cross_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.1 e,
      fun p : Disorder n × Disorder n => p.2 f; disorderPairLaw n] = 0 := by
  exact ((disorderPair_independent n).comp (measurable_pi_apply e)
    (measurable_pi_apply f)).covariance_eq_zero
      (disorderPair_fst_coordinate_law e).hasGaussianLaw.memLp_two
      (disorderPair_snd_coordinate_law f).hasGaussianLaw.memLp_two

theorem covariance_linear_combination {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y Z W : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) (hW : MemLp W 2 μ)
    (a b c d : ℝ) :
    cov[fun ω => a * X ω + b * Y ω, fun ω => c * Z ω + d * W ω; μ] =
      a * c * cov[X, Z; μ] + a * d * cov[X, W; μ] +
      b * c * cov[Y, Z; μ] + b * d * cov[Y, W; μ] := by
  change cov[(fun ω => a * X ω) + (fun ω => b * Y ω),
    (fun ω => c * Z ω) + (fun ω => d * W ω); μ] = _
  rw [covariance_add_left (hX.const_mul a) (hY.const_mul b)
      ((hZ.const_mul c).add (hW.const_mul d)),
    covariance_add_right (hX.const_mul a) (hZ.const_mul c) (hW.const_mul d),
    covariance_add_right (hY.const_mul b) (hZ.const_mul c) (hW.const_mul d)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

theorem mixDisorder_gaussian (n : ℕ) (a b : ℝ) :
    HasGaussianLaw (mixDisorder (n := n) a b) (disorderPairLaw n) :=
  (disorderPair_gaussian n).map_fun (mixDisorderCLM n a b)

theorem mixDisorder_mean {n : ℕ} (a b : ℝ) (e : Edge n) :
    (∫ p, mixDisorder a b p e ∂disorderPairLaw n) = 0 := by
  change (∫ p : Disorder n × Disorder n, a * p.1 e + b * p.2 e ∂disorderPairLaw n) = 0
  rw [integral_add
    ((disorderPair_fst_coordinate_law e).hasGaussianLaw.integrable.const_mul a)
    ((disorderPair_snd_coordinate_law e).hasGaussianLaw.integrable.const_mul b),
    integral_const_mul, integral_const_mul,
    (disorderPair_fst_coordinate_law e).integral_eq,
    (disorderPair_snd_coordinate_law e).integral_eq]
  simp

theorem mixDisorder_covariance {n : ℕ} (a b c d : ℝ) (e f : Edge n) :
    cov[fun p => mixDisorder a b p e, fun p => mixDisorder c d p f; disorderPairLaw n] =
      (a * c + b * d) * (if e = f then 1 else 0) := by
  change cov[fun p : Disorder n × Disorder n => a * p.1 e + b * p.2 e,
    fun p : Disorder n × Disorder n => c * p.1 f + d * p.2 f; disorderPairLaw n] = _
  rw [covariance_linear_combination
    (disorderPair_fst_coordinate_law e).hasGaussianLaw.memLp_two
    (disorderPair_snd_coordinate_law e).hasGaussianLaw.memLp_two
    (disorderPair_fst_coordinate_law f).hasGaussianLaw.memLp_two
    (disorderPair_snd_coordinate_law f).hasGaussianLaw.memLp_two,
    disorderPair_fst_covariance, disorderPair_snd_covariance, disorderPair_cross_covariance]
  rw [covariance_comm (fun p : Disorder n × Disorder n => p.2 e),
    disorderPair_cross_covariance]
  ring

theorem mixDisorder_coordinate_law {n : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (e : Edge n) :
    HasLaw (fun p => mixDisorder a b p e) (gaussianReal 0 1) (disorderPairLaw n) := by
  have hg := (mixDisorder_gaussian n a b).eval e
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, mixDisorder_mean,
    ← covariance_self hg.aemeasurable, mixDisorder_covariance]
  simp only [ite_true, mul_one]
  have h : a * a + b * b = 1 := by nlinarith [hab]
  rw [h]
  norm_num

theorem mixDisorder_law {n : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    HasLaw (mixDisorder (n := n) a b) (disorderLaw n) (disorderPairLaw n) := by
  apply iIndepFun.hasLaw_pi (fun e => mixDisorder_coordinate_law a b hab e)
  apply (mixDisorder_gaussian n a b).iIndepFun_of_covariance_eq_zero
  intro e f hef
  rw [mixDisorder_covariance, ite_eq_right hef, mul_zero]

theorem rotateDisorder_gaussian (n : ℕ) (θ : ℝ) :
    HasGaussianLaw (rotateDisorder (n := n) θ) (disorderPairLaw n) :=
  (disorderPair_gaussian n).map_fun (rotateDisorderCLM n θ)

theorem rotateDisorder_law (n : ℕ) (θ : ℝ) :
    HasLaw (rotateDisorder (n := n) θ) (disorderPairLaw n) (disorderPairLaw n) := by
  have hind : IndepFun (mixDisorder (n := n) (Real.cos θ) (Real.sin θ))
      (mixDisorder (- Real.sin θ) (Real.cos θ)) (disorderPairLaw n) := by
    apply (rotateDisorder_gaussian n θ).indepFun_of_covariance_eval
    intro e f
    rw [mixDisorder_covariance]
    ring
  exact hind.hasLaw_prod
    (mixDisorder_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))
    (mixDisorder_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))

theorem directionalEnergy_exp_le {n : ℕ} (β ℓ : ℝ) (J K : Disorder n) :
    Real.exp (ℓ * directionalEnergy β J K) ≤
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x) := by
  have h := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := gibbs β J) (p := fun x => ℓ * β * hamiltonian K x)
    (fun x _ => le_of_lt (gibbs_pos β J x)) (gibbs_sum β J)
    (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, ← Finset.mul_sum, directionalEnergy, mul_assoc,
    mul_left_comm (gibbs β J _)] using h

theorem continuous_partition {n : ℕ} (β : ℝ) :
    Continuous (partition (n := n) β) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _ =>
    Real.continuous_exp.comp (continuous_const.mul (continuous_hamiltonian x)))

theorem continuous_gibbs {n : ℕ} (β : ℝ) (x : Config n) :
    Continuous (fun J : Disorder n => gibbs β J x) := by
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_hamiltonian x))).div
    (continuous_partition β) (fun J => ne_of_gt (partition_pos β J))

theorem gibbs_le_one {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) :
    gibbs β J x ≤ 1 := by
  rw [← gibbs_sum β J]
  exact Finset.single_le_sum (fun z _ => le_of_lt (gibbs_pos β J z)) (Finset.mem_univ x)

theorem gibbs_integrable {n : ℕ} (β : ℝ) (x : Config n) :
    Integrable (fun J : Disorder n => gibbs β J x) (disorderLaw n) := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_gibbs β x).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs, abs_of_pos (gibbs_pos β J x)] using gibbs_le_one β J x

theorem continuous_directionalEnergy {n : ℕ} (β : ℝ) :
    Continuous (fun p : Disorder n × Disorder n => directionalEnergy β p.1 p.2) := by
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun x _ =>
    ((continuous_gibbs β x).comp continuous_fst).mul
      ((continuous_hamiltonian x).comp continuous_snd))

theorem directionalEnergy_exp_integrable {n : ℕ} (β ℓ : ℝ) (J : Disorder n) :
    Integrable (fun K : Disorder n => Real.exp (ℓ * directionalEnergy β J K))
      (disorderLaw n) := by
  have hsum : Integrable (fun K : Disorder n =>
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x))
      (disorderLaw n) :=
    integrable_finsetSum _ (fun x _ =>
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _)
  apply hsum.mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_directionalEnergy β).comp (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · filter_upwards [] with K
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ J K

theorem directionalEnergy_exp_integral_le {n : ℕ} (hn : 0 < n)
    (β ℓ : ℝ) (J : Disorder n) :
    (∫ K : Disorder n, Real.exp (ℓ * directionalEnergy β J K) ∂disorderLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hsum (x : Config n) : Integrable (fun K : Disorder n =>
      gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) (disorderLaw n) :=
    (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _
  calc
    _ ≤ ∫ K : Disorder n, (∑ x : Config n,
        gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) ∂disorderLaw n :=
      integral_mono (directionalEnergy_exp_integrable β ℓ J)
        (integrable_finsetSum _ (fun x _ => hsum x)) (directionalEnergy_exp_le β ℓ J)
    _ = _ := by
      rw [integral_finsetSum _ (fun x _ => hsum x)]
      simp_rw [integral_const_mul, hamiltonian_exp_integral hn]
      rw [← Finset.sum_mul, gibbs_sum, one_mul]

theorem directionalEnergy_pair_exp_integrable {n : ℕ} (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) := by
  have hsum : Integrable (fun p : Disorder n × Disorder n =>
      ∑ x : Config n, gibbs β p.1 x * Real.exp (ℓ * β * hamiltonian p.2 x))
      (disorderPairLaw n) := by
    apply integrable_finsetSum
    intro x _
    exact (gibbs_integrable β x).mul_prod
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β))
  apply hsum.mono'
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy β))).aestronglyMeasurable
  · filter_upwards [] with p
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ p.1 p.2

theorem directionalEnergy_pair_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β p.1 p.2) ∂disorderPairLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  rw [disorderPairLaw, integral_prod _ (directionalEnergy_pair_exp_integrable β ℓ)]
  calc
    _ ≤ ∫ _J : Disorder n,
        Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂disorderLaw n :=
      integral_mono (directionalEnergy_pair_exp_integrable β ℓ).integral_prod_left
        (integrable_const _) (directionalEnergy_exp_integral_le hn β ℓ)
    _ = _ := by simp

theorem hamiltonian_mix {n : ℕ} (a b : ℝ) (p : Disorder n × Disorder n) (x : Config n) :
    hamiltonian (mixDisorder a b p) x =
      a * hamiltonian p.1 x + b * hamiltonian p.2 x := by
  simp only [hamiltonian, mixDisorder, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_LogPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem continuous_logPartition {n : ℕ} (β : ℝ) :
    Continuous (logPartition (n := n) β) :=
  (continuous_partition β).log (fun J => ne_of_gt (partition_pos β J))

theorem logPartition_hasDerivAt {n : ℕ} (β : ℝ) (J : ℝ → Disorder n)
    (K : Disorder n) (s : ℝ)
    (hJ : ∀ x, HasDerivAt (fun t => hamiltonian (J t) x) (hamiltonian K x) s) :
    HasDerivAt (fun t => logPartition β (J t)) (directionalEnergy β (J s) K) s := by
  have hp : HasDerivAt (fun t => partition β (J t))
      (∑ x : Config n, Real.exp (β * hamiltonian (J s) x) * (β * hamiltonian K x)) s := by
    exact HasDerivAt.fun_sum (fun x _ => ((hJ x).const_mul β).exp)
  have hl := hp.log (ne_of_gt (partition_pos β (J s)))
  have heq : (∑ x : Config n, Real.exp (β * hamiltonian (J s) x) *
      (β * hamiltonian K x)) / partition β (J s) =
      directionalEnergy β (J s) K := by
    simp only [directionalEnergy, gibbs, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq] at hl
  exact hl

theorem continuous_rotateDisorder (n : ℕ) :
    Continuous (fun q : ℝ × (Disorder n × Disorder n) => rotateDisorder q.1 q.2) := by
  unfold rotateDisorder mixDisorder
  fun_prop

theorem rotation_logPartition_hasDerivAt {n : ℕ} (β θ : ℝ)
    (p : Disorder n × Disorder n) (s : ℝ) :
    HasDerivAt (fun t => logPartition β (rotateDisorder (θ * t) p).1)
      (θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) s := by
  have hd : HasDerivAt (fun t => logPartition β (rotateDisorder t p).1)
      (directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) (θ * s) := by
    apply logPartition_hasDerivAt
    intro x
    simp only [rotateDisorder, hamiltonian_mix]
    exact ((Real.hasDerivAt_cos _).mul_const _).add
      ((Real.hasDerivAt_sin _).mul_const _)
  simpa only [Function.comp_def, mul_one, mul_comm] using
    hd.comp s ((hasDerivAt_id s).const_mul θ)

theorem continuous_rotation_path {n : ℕ} (θ : ℝ) (p : Disorder n × Disorder n) :
    Continuous (fun s : ℝ => rotateDisorder (θ * s) p) := by
  unfold rotateDisorder mixDisorder
  fun_prop

theorem continuous_rotation_energy {n : ℕ} (β θ : ℝ) (p : Disorder n × Disorder n) :
    Continuous (fun s : ℝ => directionalEnergy β (rotateDisorder (θ * s) p).1
      (rotateDisorder (θ * s) p).2) :=
  (continuous_directionalEnergy β).comp (continuous_rotation_path θ p)

theorem rotation_logPartition_integral {n : ℕ} (β θ : ℝ)
    (p : Disorder n × Disorder n) :
    logPartition β (rotateDisorder θ p).1 - logPartition β p.1 =
      ∫ s : ℝ in 0..1,
        θ * directionalEnergy β (rotateDisorder (θ * s) p).1
          (rotateDisorder (θ * s) p).2 := by
  have hc : Continuous (fun s : ℝ =>
      θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => rotation_logPartition_hasDerivAt β θ p s) (hc.intervalIntegrable 0 1)
  simpa only [mul_one, mul_zero, rotateDisorder, mixDisorder, Real.cos_zero,
    Real.sin_zero, zero_smul, one_smul, add_zero] using h.symm

theorem continuous_unitInterval_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f unitIntervalLaw :=
  hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

theorem unitInterval_integral (f : ℝ → ℝ) :
    (∫ s, f s ∂unitIntervalLaw) = ∫ s : ℝ in 0..1, f s := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

theorem rotation_exp_jensen {n : ℕ} (β θ ℓ : ℝ) (p : Disorder n × Disorder n) :
    Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)) ≤
      ∫ s, Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) ∂unitIntervalLaw := by
  have hc : Continuous (fun s : ℝ => ℓ * θ *
      directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _))
    (continuous_unitInterval_integrable hc)
    (continuous_unitInterval_integrable (Real.continuous_exp.comp hc))
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  rw [unitInterval_integral, rotation_logPartition_integral,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

theorem rotated_directionalEnergy_exp_integrable {n : ℕ} (β ℓ s : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2))
      (disorderPairLaw n) := by
  have hp := (rotateDisorder_law n s).measurePreserving (rotateDisorderCLM n s).continuous.measurable
  exact hp.integrable_comp_of_integrable (directionalEnergy_pair_exp_integrable β ℓ)

theorem rotated_directionalEnergy_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ s : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2)
        ∂disorderPairLaw n) ≤ Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hm : AEStronglyMeasurable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy (n := n) β))).aestronglyMeasurable
  have heq := (rotateDisorder_law n s).integral_comp (f := fun p =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) hm
  change (∫ p, ((fun q : Disorder n × Disorder n =>
    Real.exp (ℓ * directionalEnergy β q.1 q.2)) ∘ rotateDisorder s) p
      ∂disorderPairLaw n) ≤ _
  rw [heq]
  exact directionalEnergy_pair_exp_integral_le hn β ℓ

theorem continuous_rotationIntegrand {n : ℕ} (β θ ℓ : ℝ) :
    Continuous (Function.uncurry (rotationIntegrand (n := n) β θ ℓ)) := by
  have hm : Continuous (fun q : ℝ × (Disorder n × Disorder n) => (θ * q.1, q.2)) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hr := (continuous_rotateDisorder n).comp hm
  dsimp only [Function.comp_def] at hr
  have hd : Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
      directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
        (rotateDisorder (θ * q.1) q.2).2) :=
    (continuous_directionalEnergy (n := n) β).comp hr
  change Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
    Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
      (rotateDisorder (θ * q.1) q.2).2))
  exact Real.continuous_exp.comp (continuous_const.mul hd)

theorem rotationIntegrand_integrable {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) := by
  have hm : AEStronglyMeasurable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) :=
    (continuous_rotationIntegrand (n := n) β θ ℓ).aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · exact ae_of_all _ (fun s => rotated_directionalEnergy_exp_integrable β (ℓ * θ) (θ * s))
  · have hmeas := hm.norm.integral_prod_right'
    apply (integrable_const (Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4))).mono' hmeas
    filter_upwards [] with s
    have hn0 : 0 ≤ ∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n :=
      integral_nonneg (fun _ => norm_nonneg _)
    change |∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n| ≤ _
    rw [abs_of_nonneg hn0]
    simp only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s)

theorem rotation_exp_integrable {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
  have hright := (rotationIntegrand_integrable hn β θ ℓ).integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  apply hright.mono' hc.aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Function.uncurry_apply_pair, rotationIntegrand, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using
    rotation_exp_jensen β θ ℓ p

theorem rotation_exp_integral_le {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))
        ∂disorderPairLaw n) ≤
      Real.exp (ℓ ^ 2 * θ ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hf := rotationIntegrand_integrable hn β θ ℓ
  have hright : Integrable (fun p : Disorder n × Disorder n =>
      ∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) (disorderPairLaw n) :=
    hf.integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  have hleft : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
    apply hright.mono' hc.aestronglyMeasurable
    filter_upwards [] with p
    simpa only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using rotation_exp_jensen β θ ℓ p
  calc
    _ ≤ ∫ p, (∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) ∂disorderPairLaw n :=
      integral_mono hleft hright (rotation_exp_jensen β θ ℓ)
    _ = ∫ s, (∫ p, rotationIntegrand β θ ℓ s p ∂disorderPairLaw n) ∂unitIntervalLaw :=
      (integral_integral_swap hf).symm
    _ ≤ ∫ _s, Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂unitIntervalLaw :=
      integral_mono hf.integral_prod_left (integrable_const _)
        (fun s => rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s))
    _ = _ := by
      simp only [integral_const, probReal_univ, one_smul]
      congr 1
      ring

theorem logPartition_difference_exp_integrable {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β p.2 - logPartition β p.1))) (disorderPairLaw n) := by
  simpa only [rotateDisorder_pi_div_two_fst] using
    rotation_exp_integrable hn β (Real.pi / 2) ℓ

theorem logPartition_exp_integrable {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun J : Disorder n => Real.exp (ℓ * logPartition β J)) (disorderLaw n) := by
  have hp := logPartition_difference_exp_integrable hn β ℓ
  obtain ⟨J, hJ⟩ := hp.prod_right_ae.exists
  have hi := hJ.const_mul (Real.exp (ℓ * logPartition β J))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext K
  rw [← Real.exp_add]
  congr 1
  ring

theorem logPartition_integrable {n : ℕ} (hn : 0 < n) (β : ℝ) :
    Integrable (logPartition (n := n) β) (disorderLaw n) := by
  have hp := logPartition_exp_integrable hn β 1
  have hm := logPartition_exp_integrable hn β (-1)
  apply (hp.add hm).mono' (continuous_logPartition β).aestronglyMeasurable
  filter_upwards [] with J
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h := Real.add_one_le_exp (-logPartition β J)
    have he := Real.exp_pos (1 * logPartition β J)
    simp only [Pi.add_apply, one_mul, neg_one_mul] at *
    linarith
  · have h := Real.add_one_le_exp (logPartition β J)
    have he := Real.exp_pos (-1 * logPartition β J)
    simp only [Pi.add_apply, one_mul, neg_one_mul] at *
    linarith

theorem logPartition_centered_exp_jensen {n : ℕ} (hn : 0 < n) (β ℓ : ℝ)
    (J : Disorder n) :
    Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)) ≤
      ∫ K, Real.exp (ℓ * (logPartition β J - logPartition β K)) ∂disorderLaw n := by
  have hl : Integrable (fun K : Disorder n => ℓ * (logPartition β J - logPartition β K))
      (disorderLaw n) := ((integrable_const _).sub (logPartition_integrable hn β)).const_mul ℓ
  have he : Integrable (fun K : Disorder n =>
      Real.exp (ℓ * (logPartition β J - logPartition β K))) (disorderLaw n) := by
    have h := (logPartition_exp_integrable hn β (-ℓ)).const_mul
      (Real.exp (ℓ * logPartition β J))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext K
    rw [← Real.exp_add]
    congr 1
    ring
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _)) hl he
  convert hj using 2
  all_goals try with_reducible_and_instances rfl
  rw [integral_const_mul, integral_sub (integrable_const _) (logPartition_integrable hn β)]
  simp

theorem logPartition_centered_exp_integrable {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun J : Disorder n =>
      Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)))
      (disorderLaw n) := by
  have h := (logPartition_exp_integrable hn β ℓ).const_mul
    (Real.exp (-ℓ * ∫ K, logPartition β K ∂disorderLaw n))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext J
  rw [← Real.exp_add]
  congr 1
  ring

theorem logPartition_centered_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    (∫ J : Disorder n,
      Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)) ∂disorderLaw n) ≤
      Real.exp (ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 16) := by
  have hf : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β p.1 - logPartition β p.2))) (disorderPairLaw n) := by
    convert logPartition_difference_exp_integrable hn β (-ℓ) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    congr 1
    ring
  calc
    _ ≤ ∫ J, (∫ K, Real.exp (ℓ * (logPartition β J - logPartition β K)) ∂disorderLaw n)
        ∂disorderLaw n := integral_mono (logPartition_centered_exp_integrable hn β ℓ)
          hf.integral_prod_left (logPartition_centered_exp_jensen hn β ℓ)
    _ = ∫ p : Disorder n × Disorder n,
        Real.exp ((-ℓ) * (logPartition β (rotateDisorder (Real.pi / 2) p).1 -
          logPartition β p.1)) ∂disorderPairLaw n := by
      rw [← integral_prod _ hf]
      apply integral_congr_ae
      filter_upwards [] with p
      rw [rotateDisorder_pi_div_two_fst]
      congr 1
      ring
    _ ≤ Real.exp ((-ℓ) ^ 2 * (Real.pi / 2) ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) :=
      rotation_exp_integral_le hn β (Real.pi / 2) (-ℓ)
    _ = _ := by congr 1; ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_GaugeSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem logPartition_subGaussian {n : ℕ} (hn : 0 < n) (β : ℝ) :
    HasSubgaussianMGF
      (fun J : Disorder n => logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)
      (logPartitionProxy β n) (disorderLaw n) := by
  refine ⟨logPartition_centered_exp_integrable hn β, fun ℓ => ?_⟩
  apply (logPartition_centered_exp_integral_le hn β ℓ).trans
  apply Real.exp_le_exp.mpr
  change ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 16 ≤
    (Real.pi ^ 2 * β ^ 2 * (n : ℝ) / 8) * ℓ ^ 2 / 2
  have h : 0 ≤ ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 := by positivity
  nlinarith

theorem logPartition_upper_tail {n : ℕ} (hn : 0 < n) (β u : ℝ) (hu : 0 ≤ u) :
    (disorderLaw n).real {J | u ≤ logPartition β J - ∫ K, logPartition β K ∂disorderLaw n} ≤
      Real.exp (-u ^ 2 / (2 * (logPartitionProxy β n : ℝ))) :=
  (logPartition_subGaussian hn β).measure_ge_le hu

theorem logPartition_lower_tail {n : ℕ} (hn : 0 < n) (β u : ℝ) (hu : 0 ≤ u) :
    (disorderLaw n).real {J | u ≤ (∫ K, logPartition β K ∂disorderLaw n) - logPartition β J} ≤
      Real.exp (-u ^ 2 / (2 * (logPartitionProxy β n : ℝ))) := by
  simpa only [Pi.neg_apply, neg_sub] using (logPartition_subGaussian hn β).neg.measure_ge_le hu

end SK

end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AverageMeanVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fieldIndex_eq_natAdd (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    fieldIndex D N k b i = Fin.natAdd D (finProdFinEquiv (b,i)) := by
  apply Fin.ext
  change D+b.val*N+i.val = D+(i.val+N*b.val)
  ring

@[simp] theorem blockInteraction_field {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (b : Fin (k+1)) (i : Fin N) : blockInteraction (k := k) I (fieldIndex D N k b i) = {i} := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockInteraction,Fin.addCases_right,Equiv.symm_apply_apply]

@[simp] theorem blockCoefficients_field {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ)
    (b : Fin (k+1)) (i : Fin N) : blockCoefficients (N := N) a v (fieldIndex D N k b i) = v b := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockCoefficients,Fin.addCases_right,Equiv.symm_apply_apply]

theorem blockExponent_expansion {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v : Fin (k+1) → ℝ) (s : Config N) (z : ParameterSpace (blockDimension D N k)) :
    blockExponent I a v s z =
      (∑ t : Fin D, a t*spinMonomial s (I t)*coordinateProjection (blockDimension D N k) (Fin.castAdd ((k+1)*N) t) z)+
      ∑ b : Fin (k+1), ∑ i : Fin N, v b*spin (s i)*coordinateProjection (blockDimension D N k) (fieldIndex D N k b i) z := by
  unfold blockExponent spinExponent
  rw [coordinateLinear_apply,Fin.sum_univ_add]
  simp only [blockCoefficients,blockInteraction,Fin.addCases_left,Fin.addCases_right]
  congr 1
  rw [← finProdFinEquiv.sum_comp (fun t => v (finProdFinEquiv.symm t).1*
    spinMonomial s {(finProdFinEquiv.symm t).2}*
      coordinateProjection (blockDimension D N k) (Fin.natAdd D t) z)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,spinMonomial,Finset.prod_singleton,
    fieldIndex_eq_natAdd]

end SK.Analytic
namespace SK.Analytic

section MeanVariance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem abs_normalizedDot_le_one {N : ℕ} (a b : Fin N → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) : |normalizedDot a b| ≤ 1 := by
  have h₁ : Real.sqrt (normalizedSquare a) ≤ 1 := by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one a ha)
  have h₂ : Real.sqrt (normalizedSquare b) ≤ 1 := by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one b hb)
  exact (abs_normalizedDot_le a b).trans (by nlinarith [Real.sqrt_nonneg (normalizedSquare a),Real.sqrt_nonneg (normalizedSquare b)])

end MeanVariance
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section CascadeProbability
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {S : Type} [Fintype S] [Nonempty S]

theorem affineGibbs_continuous (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (s : S) :
    Continuous (fun x => affineGibbs c L x s) := by
  exact (Real.continuous_exp.comp (continuous_const.add (L s).continuous)).div
    (continuous_finsetSum _ (fun t _ => Real.continuous_exp.comp (continuous_const.add (L t).continuous)))
    (fun x => (affinePartition_pos c L x).ne')

theorem affineGibbs_le_one (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) :
    affineGibbs c L x s ≤ 1 := by
  rw [← affineGibbs_sum c L x]
  exact Finset.single_le_sum (fun t _ => (affineGibbs_pos c L x t).le) (Finset.mem_univ s)

theorem affineGibbs_norm_le_one (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) :
    ‖affineGibbs c L x s‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_pos (affineGibbs_pos c L x s)]
  exact affineGibbs_le_one c L x s

end CascadeProbability
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianSpinTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped MatrixOrder BigOperators
noncomputable section
open scoped BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Matrix
namespace SK.Analytic
section FiniteCovariance
variable {S I : Type} [Fintype S] [Fintype I]

omit [Fintype I] in
theorem finiteMean_apply (p : S → ℝ) (v : S → I → ℝ) (i : I) :
    finiteMean p v i = ∑ s, p s*v s i := by simp only [finiteMean,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

end FiniteCovariance
end SK.Analytic

end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
namespace SK.Analytic
open Matrix
section ReplicaOverlap
variable {S I : Type} [Fintype S] [Fintype I]

theorem finiteReplicaMoment_dot (p : S → ℝ) (v : S → I → ℝ) :
    finiteReplicaMoment p (fun s t => v s ⬝ᵥ v t) = finiteMean p v ⬝ᵥ finiteMean p v := by
  simp only [finiteMean,finiteReplicaMoment,sum_dotProduct,dotProduct_sum,
    smul_dotProduct,dotProduct_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [dotProduct_comm (v t) (v s)]
  ring

end ReplicaOverlap
end SK.Analytic

end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_nonneg (n : ℕ) (m : Fin n → ℝ) (f g : ParameterSpace n → ℝ)
    (hg : ∀ z, 0 ≤ g z) (j : Fin (n+1)) (z : ParameterSpace n) :
    0 ≤ hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => exact hg z
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using hg z
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      apply ih
      intro x
      exact integral_nonneg (fun y => hg (x,y))

theorem hierarchyMomentLevel_const (n : ℕ) (m : Fin n → ℝ) (f : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (a : ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun _ => a) j = fun _ => a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      rw [gaussianAverage_const_prefix hf _ (fun _ => a),ih _ _ (hf.gaussianStep _)]

theorem hierarchyMomentLevel_const_mul (n : ℕ) (m : Fin n → ℝ) (f g : ParameterSpace n → ℝ)
    (a : ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => a*g z) j = fun z => a*hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · have he : gaussianAverage (m (Fin.last n)) f (fun z => a*g z) =
          fun z => a*gaussianAverage (m (Fin.last n)) f g z := by
        funext z; exact integral_const_mul a _
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,he,ih]

theorem hierarchyMomentLevel_sum {T : Type} [Fintype T] (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f)
    (g : T → ParameterSpace n → ℝ) (hg : ∀ t, Continuous (g t))
    (C : T → ℝ) (hC : ∀ t, 0 ≤ C t) (hb : ∀ t z, ‖g t z‖ ≤ C t) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => ∑ t, g t z) j =
      fun z => ∑ t, hierarchyMomentLevel n m f (g t) j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · have he : gaussianAverage (m (Fin.last n)) f (fun z => ∑ t, g t z) =
          fun z => ∑ t, gaussianAverage (m (Fin.last n)) f (g t) z := by
        funext z
        let := gaussianStepLaw_probability hf (m (Fin.last n)) z
        apply integral_finsetSum
        intro t _
        exact Integrable.of_bound ((hg t).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
          (C t) (ae_of_all _ (fun y => hb t (z,y)))
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,he]
      rw [ih _ _ (hf.gaussianStep _) _
        (fun t => gaussianAverage_continuous hf _ (hg t) (hC t) (hb t))
        (fun t z => gaussianAverage_norm_le hf _ (hb t) z) j]

section Probability
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchySpinWeight_regular (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (s : S) :
    Continuous (fun z => hierarchySpinWeight n m U j z s) ∧
      ∀ z, ‖hierarchySpinWeight n m U j z s‖ ≤ 1 :=
  hierarchyMomentLevel_bounded_continuous n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (affineGibbs_continuous (fun _ => 0) U s) (by norm_num) (fun z => affineGibbs_norm_le_one (fun _ => 0) U z s) j

theorem hierarchySpinWeight_nonneg (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (z : ParameterSpace n) (s : S) : 0 ≤ hierarchySpinWeight n m U j z s :=
  hierarchyMomentLevel_nonneg n m _ _ (fun z => le_of_lt (affineGibbs_pos (fun _ => 0) U z s)) j z

theorem hierarchySpinWeight_sum (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (z : ParameterSpace n) : ∑ s, hierarchySpinWeight n m U j z s = 1 := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition (fun _ => 0) U)
    (affineLogPartition_boundedDerivs (fun _ => 0) U) (fun s z => affineGibbs (fun _ => 0) U z s)
    (affineGibbs_continuous (fun _ => 0) U) (fun _ => 1) (fun _ => by norm_num)
    (fun s z => affineGibbs_norm_le_one (fun _ => 0) U z s) j
  have he : (fun z => ∑ s, affineGibbs (fun _ => 0) U z s) = fun _ => 1 :=
    funext (fun z => affineGibbs_sum (fun _ => 0) U z)
  rw [he,hierarchyMomentLevel_const n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U)] at H
  exact (congrFun H z).symm

theorem hierarchySpinMean_eq_sum (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchySpinMean n m U v j z = ∑ s, hierarchySpinWeight n m U j z s*v s := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition (fun _ => 0) U)
    (affineLogPartition_boundedDerivs (fun _ => 0) U) (fun s z => v s*affineGibbs (fun _ => 0) U z s)
    (fun s => continuous_const.mul (affineGibbs_continuous (fun _ => 0) U s))
    (fun s => ‖v s‖) (fun s => norm_nonneg _) (fun s z => by
      rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (affineGibbs_norm_le_one (fun _ => 0) U z s) (norm_nonneg _)).trans_eq (mul_one _)) j
  simp_rw [hierarchyMomentLevel_const_mul] at H
  change hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U)
    (fun z => ∑ s, affineGibbs (fun _ => 0) U z s*v s) j z = _
  simpa only [hierarchySpinWeight,mul_comm] using congrFun H z
end Probability
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinParameterRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section ParameterHierarchy
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hierarchyPressure_paramRegular (n : ℕ) (m : Fin n → ℝ)
    (f : P × ParameterSpace n → ℝ) (hf : ParamRegular f) :
    ParamRegular (fun z : P × ℝ => hierarchyPressure n m (fun w => f (z.1,w)) z.2) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact ih (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ =>
        f (z.1.1,(z.1.2,z.2)))) (hf.gaussianStep (m (Fin.last n)))

end ParameterHierarchy

theorem spinPressure_paramRegular {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (c : Config N → ℝ) (m : Fin d → ℝ) :
    ParamRegular (fun z : (Fin d → ℝ) × ℝ =>
      hierarchyPressure d m (affineLogPartition c (spinExponent d z.1 I)) z.2) :=
  hierarchyPressure_paramRegular d m _ (spinTerminal_paramRegular d I c)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaVarianceSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix
section ReplicaVarianceSplit
variable {S : Type} [Fintype S]

theorem finiteReplicaMoment_const (p : S → ℝ) (hp : ∑ s, p s = 1) (c : ℝ) :
    finiteReplicaMoment p (fun _ _ => c) = c := by
  simp only [finiteReplicaMoment,← Finset.mul_sum,← Finset.sum_mul,hp,mul_one,one_mul]

theorem finiteReplicaMoment_add (p : S → ℝ) (g h : S → S → ℝ) :
    finiteReplicaMoment p (fun s t => g s t+h s t) = finiteReplicaMoment p g+finiteReplicaMoment p h := by
  simp only [finiteReplicaMoment,mul_add,Finset.sum_add_distrib]

theorem finiteReplicaMoment_const_mul (p : S → ℝ) (g : S → S → ℝ) (c : ℝ) :
    finiteReplicaMoment p (fun s t => c*g s t) = c*finiteReplicaMoment p g := by
  simp only [finiteReplicaMoment,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _
  ring

theorem finiteReplicaMoment_sub_square (p : S → ℝ) (hp : ∑ s, p s = 1) (g : S → S → ℝ) (r : ℝ) :
    finiteReplicaMoment p (fun s t => (g s t-r)^2) =
      finiteReplicaMoment p (fun s t => (g s t)^2)-2*r*finiteReplicaMoment p g+r^2 := by
  have he : (fun s t => (g s t-r)^2) = fun s t => (g s t)^2+(-2*r)*g s t+r^2 := by
    funext s t; ring
  rw [he,finiteReplicaMoment_add,finiteReplicaMoment_add,finiteReplicaMoment_const_mul,finiteReplicaMoment_const p hp]
  ring

theorem finiteReplicaMoment_normalizedDot {N : ℕ} (p : S → ℝ) (v : S → Fin N → ℝ) :
    finiteReplicaMoment p (fun s t => normalizedDot (v s) (v t)) = normalizedSquare (finiteMean p v) := by
  have he : (fun s t => normalizedDot (v s) (v t)) = fun s t => (N : ℝ)⁻¹*(v s ⬝ᵥ v t) := by
    funext s t; simp only [normalizedDot,dotProduct,div_eq_mul_inv]; ring
  rw [he,finiteReplicaMoment_const_mul,finiteReplicaMoment_dot]
  simp only [normalizedSquare,dotProduct,pow_two,div_eq_mul_inv,mul_comm]

end ReplicaVarianceSplit
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix
section FiniteReplicaBounds
variable {S : Type} [Fintype S]

theorem finiteReplicaMoment_mono (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (g h : S → S → ℝ)
    (hgh : ∀ s t, g s t ≤ h s t) : finiteReplicaMoment p g ≤ finiteReplicaMoment p h := by
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (hgh s t) (mul_nonneg (hp s) (hp t))

theorem finiteReplicaMoment_nonneg (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (g : S → S → ℝ)
    (hg : ∀ s t, 0 ≤ g s t) : 0 ≤ finiteReplicaMoment p g :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ => mul_nonneg (mul_nonneg (hp s) (hp t)) (hg s t)

theorem finiteReplicaMoment_le_const (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1)
    (g : S → S → ℝ) (C : ℝ) (hg : ∀ s t, g s t ≤ C) : finiteReplicaMoment p g ≤ C := by
  exact (finiteReplicaMoment_mono p hp g (fun _ _ => C) hg).trans_eq (finiteReplicaMoment_const p hs C)

theorem finiteReplicaMoment_continuous {Ω : Type} [TopologicalSpace Ω]
    (P : Ω → S → ℝ) (hP : ∀ s, Continuous (fun z => P z s)) (g : S → S → ℝ) :
    Continuous (fun z => finiteReplicaMoment (P z) g) := by
  exact continuous_finsetSum _ (fun s _ => continuous_finsetSum _ (fun t _ => ((hP s).mul (hP t)).mul continuous_const))
end FiniteReplicaBounds

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyReplica
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyMeanSquare_eq_finiteMean {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchyMeanSquare n m U (fun i s => v s i) j z = normalizedSquare (finiteMean (hierarchySpinWeight n m U j z) v) := by
  simp only [hierarchyMeanSquare,hierarchySpinMean_eq_sum]
  congr 1
  funext i
  exact (finiteMean_apply _ _ i).symm

theorem hierarchyOverlap_integrand_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) (z : ParameterSpace n) :
    let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
    let Q := finiteReplicaMoment (hierarchySpinWeight n m U j z) (fun s t => (normalizedDot (v s) (v t)-r)^2)
    0 ≤ Q ∧ Q ≤ 4 := by
  dsimp only
  refine ⟨finiteReplicaMoment_nonneg _ (hierarchySpinWeight_nonneg n m U j z) _ (fun _ _ => sq_nonneg _),?_⟩
  apply finiteReplicaMoment_le_const _ (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z)
  intro s t
  have hdot := abs_normalizedDot_le_one (v s) (v t) (hv s) (hv t)
  have hr := hierarchyMeanOverlap_bounds n m U (fun i s => v s i)
    (fun i s => by simpa only [Real.norm_eq_abs] using hv s i) j
  have ha : |normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j| ≤ 2 := by
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hr.1]; linarith [hr.2])
  have hb := abs_nonneg (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)
  nlinarith [sq_abs (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)]

theorem hierarchyOverlapError_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    0 ≤ hierarchyOverlapError n m U v j ∧ hierarchyOverlapError n m U v j ≤ 4 := by
  let f := affineLogPartition (fun _ => 0) U
  let := hierarchyPathLaw_probability n m f (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  have hc := finiteReplicaMoment_continuous (hierarchySpinWeight n m U j)
    (fun s => (hierarchySpinWeight_regular n m U j s).1)
    (fun s t => (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)^2)
  have hi := Integrable.of_bound (μ := hierarchyPathLaw n m f 0) hc.aestronglyMeasurable 4
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyOverlap_integrand_bounds n m U v hv j z).1]
      exact (hierarchyOverlap_integrand_bounds n m U v hv j z).2)
  refine ⟨integral_nonneg (fun z => (hierarchyOverlap_integrand_bounds n m U v hv j z).1),?_⟩
  calc
    _ ≤ ∫ _ : ParameterSpace n, (4 : ℝ) ∂hierarchyPathLaw n m f 0 :=
      integral_mono hi (integrable_const 4) (fun z => (hierarchyOverlap_integrand_bounds n m U v hv j z).2)
    _ = 4 := by simp
end HierarchyReplica
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyReplicaSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section SecondMoment
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyReplicaSecond_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) : Integrable (fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t))^2))
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (finiteReplicaMoment_continuous _ (fun s => (hierarchySpinWeight_regular n m U j s).1) _) (C := 1) _ 0
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (finiteReplicaMoment_nonneg _ (hierarchySpinWeight_nonneg n m U j z) _ (fun _ _ => sq_nonneg _))]
  apply finiteReplicaMoment_le_const _ (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z)
  intro s t
  have H := abs_normalizedDot_le_one (v s) (v t) (hv s) (hv t)
  have H0 := abs_nonneg (normalizedDot (v s) (v t))
  nlinarith [sq_abs (normalizedDot (v s) (v t))]

theorem hierarchyOverlapError_eq_second_sub_sq {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) : hierarchyOverlapError n m U v j = hierarchyReplicaSecond n m U v j -
      (hierarchyMeanOverlap n m U (fun i s => v s i) j)^2 := by
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
  have hs := hierarchyReplicaSecond_integrable n m U v hv j
  have hm := hierarchyMeanSquare_integrable n m U (fun i s => v s i)
    (fun i s => by simpa only [Real.norm_eq_abs] using hv s i) j 0
  have he (z : ParameterSpace n) : finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t)-r)^2) =
      finiteReplicaMoment (hierarchySpinWeight n m U j z) (fun s t => (normalizedDot (v s) (v t))^2)-
        2*r*hierarchyMeanSquare n m U (fun i s => v s i) j z+r^2 := by
    rw [finiteReplicaMoment_sub_square _ (hierarchySpinWeight_sum n m U j z),
      finiteReplicaMoment_normalizedDot,← hierarchyMeanSquare_eq_finiteMean]
  change (∫ z, finiteReplicaMoment (hierarchySpinWeight n m U j z)
    (fun s t => (normalizedDot (v s) (v t)-r)^2) ∂μ) = hierarchyReplicaSecond n m U v j-r^2
  simp_rw [he]
  rw [integral_add (f := fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
    (fun s t => (normalizedDot (v s) (v t))^2)-2*r*hierarchyMeanSquare n m U (fun i s => v s i) j z)
    (g := fun _ => r^2) (hs.sub (hm.const_mul (2*r))) (integrable_const (r^2)),
    integral_sub hs (hm.const_mul (2*r)),integral_const_mul]
  have hc : (∫ _ : ParameterSpace n, r^2 ∂μ) = r^2 := by simp [μ]
  rw [hc]
  change hierarchyReplicaSecond n m U v j-2*r*r+r^2 = hierarchyReplicaSecond n m U v j-r^2
  ring
end SecondMoment
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKBlockCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem spinMonomial_skInteraction (N : ℕ) (i : Fin (Fintype.card (Edge N))) (s : Config N) :
    spinMonomial s (skInteraction N i) =
      spin (s ((Fintype.equivFin (Edge N)).symm i).val.1)*
        spin (s ((Fintype.equivFin (Edge N)).symm i).val.2) := by
  exact Finset.prod_pair (ne_of_lt (((Fintype.equivFin (Edge N)).symm i).property))

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_ZeroFieldEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cascadePressure_root (b : ℕ) (m : Fin b → ℝ) (g : E → ℝ) :
    cascadePressure b m (fun z => g (cascadeRoot (E := E) b z)) = g := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change cascadePressure b _ (gaussianStep _ (fun z => g (cascadeRoot (E := E) b z.1))) = g
    rw [gaussianStep_prefix (fun z => g (cascadeRoot (E := E) b z)) (m (Fin.last b)),ih]
end Generic

theorem coordinateProjection_append_prefix (a b : ℕ) (i : Fin a)
    (z : CascadeSpace (ParameterSpace a) b) :
    coordinateProjection (a+b) (Fin.castAdd b i) (parameterAppend a b z) =
      coordinateProjection a i (cascadeRoot (E := ParameterSpace a) b z) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change coordinateProjection ((a+b)+1) (Fin.castSucc (Fin.castAdd b i))
      (parameterAppend a b z.1,z.2) = _
    rw [coordinateProjection_castSucc,ih]
    rfl

theorem blockExponent_zeroFields_append {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (s : Config N) (z : CascadeSpace (ParameterSpace D) ((k+1)*N)) :
    blockExponent I a (fun _ : Fin (k+1) => 0) s (parameterAppend D ((k+1)*N) z) =
      spinExponent D a I s (cascadeRoot (E := ParameterSpace D) ((k+1)*N) z) := by
  rw [blockExponent_expansion]
  simp only [zero_mul,Finset.sum_const_zero,add_zero,coordinateProjection_append_prefix,
    spinExponent,coordinateLinear_apply]

theorem blockMass_at_disorder (D N k : ℕ) (i : Fin D) :
    blockMass D N k (Fin.castAdd ((k+1)*N) i) = 0 := by
  rw [blockMass_eq_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [ite_eq_right]
  simp only [blockLevel_val,Fin.val_castAdd]
  omega

theorem skBlockRoot_zero_fields (N k : ℕ) (β : ℝ) :
    skBlockRoot N k β (fun _ => 0) =
      ∫ z, affineLogPartition (fun _ : Config N => 0)
        (spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N)) z
        ∂fiberGaussian (Fintype.card (Edge N)) 0 := by
  unfold skBlockRoot
  rw [hierarchyPressure_split]
  have he : (fun z => affineLogPartition (fun _ : Config N => 0)
      (blockExponent (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) (fun _ : Fin (k+1) => 0))
        (parameterAppend (Fintype.card (Edge N)) ((k+1)*N) z)) =
      fun z => affineLogPartition (fun _ : Config N => 0)
        (spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N))
          (cascadeRoot (E := ParameterSpace (Fintype.card (Edge N))) ((k+1)*N) z) := by
    funext z
    simp only [affineLogPartition,blockExponent_zeroFields_append]
  rw [he,cascadePressure_root]
  simp only [blockMass_at_disorder]
  apply hierarchyPressure_zero
  exact affineLogPartition_boundedDerivs _ _
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_QuenchedEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinExponent_sk_eq (N : ℕ) (β : ℝ) (s : Config N)
    (z : ParameterSpace (Fintype.card (Edge N))) :
    spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N) s z =
      β*hamiltonian (enumeratedDisorder N z) s := by
  simp only [spinExponent,coordinateLinear_apply,spinMonomial_skInteraction,hamiltonian,
    enumeratedDisorder]
  rw [← (Fintype.equivFin (Edge N)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  simp only [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem affineLogPartition_sk_eq (N : ℕ) (β : ℝ)
    (z : ParameterSpace (Fintype.card (Edge N))) :
    affineLogPartition (fun _ : Config N => 0)
      (spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N)) z =
      logPartition β (enumeratedDisorder N z) := by
  simp only [affineLogPartition,spinExponent_sk_eq,zero_add,logPartition,partition]

theorem skBlockRoot_zero_fields_eq (N k : ℕ) (β : ℝ) :
    skBlockRoot N k β (fun _ => 0) = ∫ J, logPartition β J ∂disorderLaw N := by
  rw [skBlockRoot_zero_fields]
  simp only [affineLogPartition_sk_eq]
  have H := enumeratedDisorder_measurePreserving N 0
  rw [← H.map_eq,integral_map H.measurable.aemeasurable (continuous_logPartition β).aestronglyMeasurable]
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockAdaptiveOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem blockCoefficients_contDiff {D N k : ℕ} (a : Fin D → ℝ) (β : ℝ) :
    ContDiff ℝ 2 (fun p : ℝ × (Fin (k+1) → ℝ) =>
      blockCoefficients (N := N) (fun i => p.1*a i) (fun b => β*p.2 b)) := by
  apply contDiff_pi.mpr
  intro t
  refine Fin.addCases (fun i => ?_) (fun i => ?_) t
  · simp only [blockCoefficients,Fin.addCases_left]
    exact contDiff_fst.mul contDiff_const
  · simp only [blockCoefficients,Fin.addCases_right]
    exact contDiff_const.mul ((contDiff_apply ℝ ℝ _).comp contDiff_snd)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_AdaptiveSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem cumulativeGapMap_sum (k : ℕ) (q : Fin (k+1) → ℝ) :
    ∑ b, cumulativeGapMap k q b = q (Fin.last k) := by
  rw [Fin.sum_univ_succ]
  simp only [cumulativeGapMap_zero,cumulativeGapMap_succ,Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ q
  have h2 := Fin.sum_univ_castSucc q
  linarith

theorem cumulativeGapMap_castSucc (k : ℕ) (q : Fin (k+2) → ℝ) (b : Fin (k+1)) :
    cumulativeGapMap (k+1) q b.castSucc = cumulativeGapMap k (fun i => q i.castSucc) b := by
  refine Fin.cases ?_ (fun i => ?_) b
  · rfl
  · rfl

theorem cumulativeGapMap_partial_sum (k : ℕ) (q : Fin (k+1) → ℝ) (l : Fin (k+1)) :
    (∑ b, if b ≤ l then cumulativeGapMap k q b else 0) = q l := by
  induction k with
  | zero => simp [Fin.eq_zero l]
  | succ k ih =>
    refine Fin.lastCases ?_ (fun l => ?_) l
    · simp only [Fin.le_last,ite_true,cumulativeGapMap_sum]
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.castSucc_le_castSucc_iff,cumulativeGapMap_castSucc]
      have h : ¬ Fin.last (k+1) ≤ l.castSucc := by simp [Fin.le_def]; omega
      rw [ite_eq_right h,add_zero]
      exact ih (fun i => q i.castSucc) l

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKAdaptiveContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem skBlockRoot_contDiff (N k : ℕ) :
    ContDiff ℝ 2 (fun p : ℝ × (Fin (k+1) → ℝ) => skBlockRoot N k p.1 p.2) := by
  have H := parameter_contDiff_at_field
    (spinPressure_paramRegular (blockDimension (Fintype.card (Edge N)) N k)
      (blockInteraction (skInteraction N)) (fun _ => 0)
      (blockMass (Fintype.card (Edge N)) N k)).1 (0:ℝ)
  have HC := H.comp (blockCoefficients_contDiff (N := N) (k := k)
    (fun _ : Fin (Fintype.card (Edge N)) => 1/Real.sqrt (N:ℝ)) 1)
  convert HC using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  simp only [mul_one_div,one_mul]
  rfl

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarHierarchy_compress (n : ℕ) {r : ℕ} (e : Fin r → Fin n)
    (he : StrictMono e) (m v : Fin n → ℝ)
    (hv : ∀ t, (∀ j, e j ≠ t) → v t = 0) (f : ℝ → ℝ) :
    scalarHierarchy n m v f = scalarHierarchy r (m ∘ e) (v ∘ e) f := by
  induction n generalizing r f with
  | zero =>
    cases r with
    | zero => rfl
    | succ r => exact Fin.elim0 (e 0)
  | succ n ih =>
    cases r with
    | zero =>
      have hlast : v (Fin.last n) = 0 := hv _ (fun j => Fin.elim0 j)
      simp only [scalarHierarchy,hlast,scalarStep_zero]
      exact ih (fun j => Fin.elim0 j) (fun a => Fin.elim0 a)
        (fun i => m i.castSucc) (fun i => v i.castSucc)
        (fun t _ => hv t.castSucc (fun j => Fin.elim0 j)) f
    | succ r =>
      by_cases hlast : e (Fin.last r) = Fin.last n
      · have hlt (i : Fin r) : (e i.castSucc).val < n := by
          have H := he (Fin.castSucc_lt_last i)
          rw [hlast] at H
          exact H
        let e' : Fin r → Fin n := fun i => ⟨(e i.castSucc).val,hlt i⟩
        have hcast (i : Fin r) : (e' i).castSucc = e i.castSucc := Fin.ext rfl
        have he' : StrictMono e' := by
          intro a b hab
          exact he (show a.castSucc < b.castSucc from hab)
        have hv' (t : Fin n) (ht : ∀ j, e' j ≠ t) : v t.castSucc = 0 := by
          apply hv
          intro j
          refine Fin.lastCases ?_ (fun i => ?_) j
          · rw [hlast]
            exact (Fin.castSucc_ne_last t).symm
          · intro h
            exact ht i (Fin.ext (congrArg (fun z : Fin (n+1) => z.val) h))
        rw [scalarHierarchy,scalarHierarchy,← hlast]
        have H := ih e' he' (fun i => m i.castSucc) (fun i => v i.castSucc) hv'
          (scalarStep (m (e (Fin.last r))) (v (e (Fin.last r))) f)
        simpa only [Function.comp_def,hcast] using H
      · have hlt (i : Fin (r+1)) : (e i).val < n := by
          have H := he.monotone (Fin.le_last i)
          have H' : (e (Fin.last r)).val < n := by
            have H'' := (e (Fin.last r)).isLt
            have Hne : (e (Fin.last r)).val ≠ n := by
              intro h
              exact hlast (Fin.ext h)
            omega
          exact lt_of_le_of_lt H H'
        let e' : Fin (r+1) → Fin n := fun i => ⟨(e i).val,hlt i⟩
        have hcast (i : Fin (r+1)) : (e' i).castSucc = e i := Fin.ext rfl
        have he' : StrictMono e' := by
          intro a b hab
          exact he hab
        have hzero : v (Fin.last n) = 0 := by
          apply hv
          intro j h
          have H := hlt j
          rw [h] at H
          exact (lt_irrefl n) H
        have hv' (t : Fin n) (ht : ∀ j, e' j ≠ t) : v t.castSucc = 0 := by
          apply hv
          intro j h
          exact ht j (Fin.ext (congrArg (fun z : Fin (n+1) => z.val) h))
        rw [scalarHierarchy,hzero,scalarStep_zero]
        have H := ih e' he' (fun i => m i.castSucc) (fun i => v i.castSucc) hv' f
        simpa only [Function.comp_def,hcast] using H
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinSiteTensorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Terminal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineLogPartition_sites (N : ℕ) (L : Fin N → E →L[ℝ] ℝ) :
    affineLogPartition (fun _ : Config N => 0) (fun s => ∑ i, spin (s i) • L i) =
      fun z => ∑ i, affineLogPartition (fun _ : Bool => 0) (fun b => spin b • L i) z := by
  funext z
  simp only [affineLogPartition,zero_add,sum_apply,
    smul_apply,smul_eq_mul,Real.exp_sum]
  rw [← Fintype.prod_sum (fun i b => Real.exp (spin b * L i z)),Real.log_prod]
  intro i _
  exact (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'

end Terminal

theorem blockExponent_zero_disorder {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (v : Fin (k+1) → ℝ) (s : Config N) :
    blockExponent I (fun _ => 0) v s = ∑ i, spin (s i) • siteField (D := D) v i := by
  ext z
  rw [blockExponent_expansion]
  simp only [zero_mul,Finset.sum_const_zero,zero_add,siteField,
    sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem blockLogPartition_zero_disorder {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (v : Fin (k+1) → ℝ) :
    affineLogPartition (fun _ => 0) (blockExponent I (fun _ => 0) v) =
      fun z => ∑ i, siteLogPartition (D := D) v i z := by
  convert affineLogPartition_sites N (siteField (D := D) v) using 1
  · congr 1
    funext s
    exact blockExponent_zero_disorder I v s
  · rfl

@[simp] theorem fieldOwner_field {D N k : ℕ} (i₀ : Fin N) (b : Fin (k+1)) (i : Fin N) :
    fieldOwner i₀ (fieldIndex D N k b i) = i := by
  rw [fieldIndex_eq_natAdd]
  unfold fieldOwner
  rw [Fin.addCases_right]
  rw [Equiv.symm_apply_apply]

theorem siteLogPartition_invariant {D N k : ℕ} (v : Fin (k+1) → ℝ) (i₀ i : Fin N)
    (t : Fin (blockDimension D N k)) (h : i ≠ fieldOwner i₀ t) :
    TranslationInvariant (siteLogPartition (D := D) v i) (coordinateAxis (blockDimension D N k) t) := by
  apply affineLogPartition_translation
  intro b
  simp only [smul_apply,siteField,sum_apply,
    smul_eq_mul,coordinateProjection_coordinateAxis]
  have he (j : Fin (k+1)) : fieldIndex D N k j i ≠ t := by
    intro ht
    apply h
    rw [← ht,fieldOwner_field]
  simp only [he,ite_false,mul_zero,Finset.sum_const_zero]

theorem skBlockRoot_zero_disorder_tensorizes {N k : ℕ} (hN : 0 < N) (v : Fin (k+1) → ℝ) :
    skBlockRoot N k 0 v =
      ∑ i, hierarchyPressure (blockDimension (Fintype.card (Edge N)) N k)
        (blockMass (Fintype.card (Edge N)) N k)
        (siteLogPartition (D := Fintype.card (Edge N)) v i) 0 := by
  simp only [skBlockRoot,zero_div,blockLogPartition_zero_disorder]
  exact congrFun (hierarchyPressure_sum_independent _ _ (fieldOwner ⟨0,hN⟩)
    (fun i => siteLogPartition (D := Fintype.card (Edge N)) v i)
    (fun i => affineLogPartition_boundedDerivs _ _)
    (fun t i h => siteLogPartition_invariant v ⟨0,hN⟩ i t h)) 0
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSpinRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem siteScalarCoefficients_field {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (i : Fin N) (z : ParameterSpace (blockDimension D N k)) :
    (∑ t, siteScalarCoefficients (D := D) v i t*coordinateProjection (blockDimension D N k) t z) =
      siteField (D := D) v i z := by
  simp only [siteScalarCoefficients,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [siteField,sum_apply,smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem hierarchyPressure_site_scalar {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N) :
    hierarchyPressure (blockDimension D N k) (blockMass D N k)
      (siteLogPartition (D := D) v i) =
    fun _ => scalarHierarchy (blockDimension D N k) (blockMass D N k)
      (siteScalarCoefficients (D := D) v i) scalarSpinTerminal 0 := by
  have he : siteLogPartition (D := D) v i = fun z =>
      scalarSpinTerminal (0+∑ t, siteScalarCoefficients (D := D) v i t*
        coordinateProjection (blockDimension D N k) t z) := by
    funext z
    rw [zero_add,siteScalarCoefficients_field]
    exact affineLogPartition_bool (siteField (D := D) v i) z
  rw [he]
  exact hierarchyPressure_scalar_linear _ _ _ scalarSpinTerminal (fun _ => 0)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fieldIndex_strictMono (D N k : ℕ) (i : Fin N) :
    StrictMono (fun b => fieldIndex D N k b i) := by
  intro a b hab
  change D+a.val*N+i.val < D+b.val*N+i.val
  exact Nat.add_lt_add_right (Nat.add_lt_add_left
    (Nat.mul_lt_mul_of_pos_right hab (Nat.zero_lt_of_lt i.isLt)) D) i.val

theorem siteScalarCoefficients_at {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (i : Fin N) (b : Fin (k+1)) :
    siteScalarCoefficients (D := D) v i (fieldIndex D N k b i) = v b := by
  have he (a : Fin (k+1)) : fieldIndex D N k a i = fieldIndex D N k b i ↔ a=b :=
    (fieldIndex_strictMono D N k i).injective.eq_iff
  simp only [siteScalarCoefficients,he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem siteScalarCoefficients_off {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (i : Fin N) (t : Fin (blockDimension D N k)) (ht : ∀ b, fieldIndex D N k b i ≠ t) :
    siteScalarCoefficients (D := D) v i t = 0 := by
  simp only [siteScalarCoefficients,ht,ite_false,Finset.sum_const_zero]

theorem hierarchyPressure_site_condensed {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N) :
    hierarchyPressure (blockDimension D N k) (blockMass D N k)
      (siteLogPartition (D := D) v i) =
      fun _ => scalarHierarchy (k+1) (quantileMass k) v scalarSpinTerminal 0 := by
  rw [hierarchyPressure_site_scalar]
  have H := scalarHierarchy_compress (blockDimension D N k)
    (fun b => fieldIndex D N k b i) (fieldIndex_strictMono D N k i)
    (blockMass D N k) (siteScalarCoefficients (D := D) v i)
    (fun t ht => siteScalarCoefficients_off v i t ht) scalarSpinTerminal
  have hm : (blockMass D N k ∘ fun b => fieldIndex D N k b i) = quantileMass k := by
    funext b
    exact blockMass_at_field D N k b i
  have hv : (siteScalarCoefficients (D := D) v i ∘ fun b => fieldIndex D N k b i) = v := by
    funext b
    exact siteScalarCoefficients_at v i b
  rw [hm,hv] at H
  rw [H]

theorem skBlockRoot_zero_disorder_scalar {N k : ℕ} (hN : 0 < N) (v : Fin (k+1) → ℝ) :
    skBlockRoot N k 0 v = (N:ℝ)*scalarHierarchy (k+1) (quantileMass k) v scalarSpinTerminal 0 := by
  rw [skBlockRoot_zero_disorder_tensorizes hN]
  simp only [hierarchyPressure_site_condensed,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_GuerraUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fixed_field_summation (k : ℕ) (Q r w : Fin (k+1) → ℝ) :
    (∑ b, cumulativeGapMap k Q b*(1-∑ l, if b ≤ l then w l*r l else 0)) =
      Q (Fin.last k)-∑ l, w l*Q l*r l := by
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,cumulativeGapMap_sum,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  have he (b : Fin (k+1)) : cumulativeGapMap k Q b*(if b ≤ l then w l*r l else 0) =
      (if b ≤ l then cumulativeGapMap k Q b else 0)*(w l*r l) := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul,cumulativeGapMap_partial_sum]
  ring

theorem quenched_le_extendedQuantileParisi {N k : ℕ} (hN : 0 < N) (β : ℝ)
    (Q : Fin (k+1) → ℝ) (hgap : ∀ j, 0 ≤ cumulativeGapMap k Q j) :
    (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ) ≤ extendedQuantileParisi k β Q := by
  let h : ℝ → ℝ := fun t => β*Real.sqrt t
  let v : ℝ → Fin (k+1) → ℝ := fun t j => β*Real.sqrt (1-t)*Real.sqrt (cumulativeGapMap k Q j)
  let f : ℝ → ℝ := fun t => skBlockRoot N k (h t) (v t)/(N:ℝ)
  let C : ℝ := (β^2/4)*(1-2*Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2)
  let U := fun t => blockExponent (skInteraction N) (fun _ => h t/Real.sqrt (N:ℝ)) (v t)
  let r := fun t j => hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k) (U t) (fun i s => spin (s i))
    (blockLevel (Fintype.card (Edge N)) N k j)
  let s := fun t j => hierarchyReplicaSecond (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k) (U t) (fun s i => spin (s i))
    (blockLevel (Fintype.card (Edge N)) N k j)
  let d := fun t => (β^2/4)*(1-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*s t j)-
    (β^2/2)*(Q (Fin.last k)-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j*r t j)
  have hcont : Continuous f := by
    have hv : Continuous v := by
      apply continuous_pi
      intro j
      exact (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))).mul continuous_const
    exact ((skBlockRoot_contDiff N k).continuous.comp
      ((continuous_const.mul Real.continuous_sqrt).prodMk hv)).div_const _
  have hd : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (d t) t := by
    intro t ht
    let hp := β*(1/(2*Real.sqrt t))
    let vp := fun j => β*(-1/(2*Real.sqrt (1-t)))*Real.sqrt (cumulativeGapMap k Q j)
    have hh : HasDerivAt h hp t := (Real.hasDerivAt_sqrt ht.1.ne').const_mul β
    have hv : HasDerivAt v vp t := by
      apply hasDerivAt_pi.mpr
      intro j
      simpa only [v,vp,Pi.sub_apply,id_eq,zero_sub] using ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).sqrt
        (by linarith [ht.2] : 1-t ≠ 0)).const_mul β).mul_const (Real.sqrt (cumulativeGapMap k Q j))
    have hhp : h t*hp/2 = β^2/4 := by
      have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht.1).ne'
      dsimp only [h,hp]
      field_simp
      ring
    have hvp (j : Fin (k+1)) : vp j*v t j = -(β^2/2)*cumulativeGapMap k Q j := by
      have hs : Real.sqrt (1-t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith [ht.2])).ne'
      dsimp only [vp,v]
      calc
        _ = -(β^2/2)*(Real.sqrt (cumulativeGapMap k Q j))^2*
          (Real.sqrt (1-t)/Real.sqrt (1-t)) := by ring
        _ = _ := by rw [div_self hs,mul_one,Real.sq_sqrt (hgap j)]
    have H := skBlockPressure_hasDerivAt hN h v hh hv
    dsimp only at H
    apply H.congr_deriv
    rw [hhp]
    simp only [hvp]
    have hsum : (∑ b, -(β^2/2)*cumulativeGapMap k Q b*
        (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r t l else 0)) =
        -(β^2/2)*(Q (Fin.last k)-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q l*r t l) := by
      rw [← fixed_field_summation k Q (r t) (fun _ => ((k+1:ℕ):ℝ)⁻¹),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    change (β^2/4)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*s t l)+
      (∑ b, -(β^2/2)*cumulativeGapMap k Q b*
        (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r t l else 0)) = d t
    rw [hsum]
    dsimp only [d]
    ring
  have hbound (t : ℝ) : d t ≤ C := by
    have hs (j : Fin (k+1)) : 2*Q j*r t j-(Q j)^2 ≤ s t j := by
      have H := (hierarchyOverlapError_bounds _ (blockMass (Fintype.card (Edge N)) N k) (U t) (fun s i => spin (s i))
        (fun s i => by cases s i <;> norm_num [spin])
        (blockLevel (Fintype.card (Edge N)) N k j)).1
      rw [hierarchyOverlapError_eq_second_sub_sq _ _ _ _
        (fun s i => by cases s i <;> norm_num [spin])] at H
      change 0 ≤ s t j-(r t j)^2 at H
      nlinarith [sq_nonneg (r t j-Q j)]
    have H : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(2*Q j*r t j-(Q j)^2)) ≤
        ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*s t j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hs j) (by positivity))
    have he (j : Fin (k+1)) : ((k+1:ℕ):ℝ)⁻¹*(2*Q j*r t j-(Q j)^2) =
        2*(((k+1:ℕ):ℝ)⁻¹*Q j*r t j)-((k+1:ℕ):ℝ)⁻¹*(Q j)^2 := by ring
    simp only [he,Finset.sum_sub_distrib] at H
    rw [← Finset.mul_sum (s := Finset.univ) (f := fun j : Fin (k+1) => ((k+1:ℕ):ℝ)⁻¹*Q j*r t j)] at H
    have HB := mul_le_mul_of_nonneg_left H (show 0 ≤ β^2/4 by positivity)
    dsimp only [d,C]
    nlinarith
  have H : f 1-C ≤ f 0 := by
    have HM : AntitoneOn (fun t => f t-C*t) (Set.Icc (0:ℝ) 1) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0:ℝ) 1)
        (hcont.sub (continuous_const.mul continuous_id)).continuousOn
        (fun t ht => ((hd t (by simpa only [interior_Icc] using ht)).sub
          ((hasDerivAt_id t).const_mul C)).hasDerivWithinAt)
        (fun t _ => by simpa only [mul_one] using sub_nonpos.mpr (hbound t))
    simpa using HM (by norm_num) (by norm_num) (by norm_num : (0:ℝ) ≤ 1)
  have hzero : f 0 = scalarHierarchy (k+1) (quantileMass k)
      (fun b => β*Real.sqrt (cumulativeGapMap k Q b)) scalarSpinTerminal 0 := by
    simp only [f,h,v,Real.sqrt_zero,mul_zero,sub_zero,Real.sqrt_one,mul_one,
      skBlockRoot_zero_disorder_scalar hN]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')
  have hone : f 1 = (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ) := by
    simp only [f,h,v,Real.sqrt_one,mul_one,sub_self,Real.sqrt_zero,mul_zero,zero_mul,
      skBlockRoot_zero_fields_eq]
  rw [hzero,hone] at H
  change _ ≤ _+C
  linarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileClamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cumulativeGapMap_nonneg_iff (k : ℕ) (Q : Fin (k+1) → ℝ) :
    (∀ j, 0 ≤ cumulativeGapMap k Q j) ↔ 0 ≤ Q 0 ∧ Monotone Q := by
  constructor
  · intro h
    refine ⟨h 0,Fin.monotone_iff_le_succ.mpr (fun j => ?_)⟩
    exact sub_nonneg.mp (h j.succ)
  · rintro ⟨h0,hm⟩ j
    refine Fin.cases h0 (fun i => ?_) j
    exact sub_nonneg.mpr (hm (Fin.castSucc_le_succ i))

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_ThermodynamicLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem finiteParisiValues_nonempty (β : ℝ) : (finiteParisiValues β).Nonempty := by
  refine ⟨extendedQuantileParisi 0 β (fun _ => 0),0,fun _ => 0,?_,?_,rfl⟩
  · exact monotone_const
  · intro j; exact ⟨le_rfl,zero_le_one⟩

theorem quenched_le_finiteParisiValue {N : ℕ} (hN : 0 < N) (β : ℝ)
    {p : ℝ} (hp : p ∈ finiteParisiValues β) : quenchedPressure β N ≤ p := by
  obtain ⟨k,Q,hm,hQ,rfl⟩ := hp
  exact quenched_le_extendedQuantileParisi hN β Q
    ((cumulativeGapMap_nonneg_iff k Q).mpr ⟨(hQ 0).1,hm⟩)

theorem finiteParisiValues_bddBelow (β : ℝ) : BddBelow (finiteParisiValues β) :=
  ⟨quenchedPressure β 1,fun _ hp => quenched_le_finiteParisiValue (by norm_num) β hp⟩

theorem finiteParisiInf_le {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hm : Monotone Q) (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    finiteParisiInf β ≤ extendedQuantileParisi k β Q :=
  csInf_le (finiteParisiValues_bddBelow β) ⟨k,Q,hm,hQ,rfl⟩

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_EnergyTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem gibbsEnergyTail_le {N : ℕ} {β γ : ℝ} (hβγ : β < γ)
    (e : ℝ) (J : Disorder N) :
    gibbsEnergyTail β e J ≤
      Real.exp (logPartition γ J-logPartition β J-(γ-β)*(N:ℝ)*e) := by
  have hZβ := partition_pos β J
  have hZγ := partition_pos γ J
  have he : Real.exp (logPartition γ J-logPartition β J-(γ-β)*(N:ℝ)*e) =
      Real.exp (-((γ-β)*(N:ℝ)*e))*partition γ J/partition β J := by
    rw [show logPartition γ J-logPartition β J-(γ-β)*(N:ℝ)*e =
      -((γ-β)*(N:ℝ)*e)+(logPartition γ J-logPartition β J) by ring,
      Real.exp_add,Real.exp_sub]
    simp only [logPartition,Real.exp_log hZγ,Real.exp_log hZβ]
    ring
  rw [he]
  unfold gibbsEnergyTail
  calc
    _ ≤ ∑ s : Config N,
        Real.exp (-((γ-β)*(N:ℝ)*e))*Real.exp (γ*hamiltonian J s)/partition β J := by
      apply Finset.sum_le_sum
      intro s _
      split_ifs with hs
      · unfold gibbs
        apply div_le_div_of_nonneg_right _ hZβ.le
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have H := mul_le_mul_of_nonneg_left hs.le (sub_pos.mpr hβγ).le
        nlinarith
      · positivity
    _ = _ := by rw [← Finset.sum_div,← Finset.mul_sum]; rfl

theorem logPartition_upper_tail_linear {N : ℕ} (hN : 0 < N) {β a : ℝ}
    (hβ : β ≠ 0) (ha : 0 ≤ a) :
    (disorderLaw N).real {J | a*(N:ℝ) ≤ logPartition β J-
      ∫ K, logPartition β K ∂disorderLaw N} ≤
      Real.exp (-(4*a^2/(Real.pi^2*β^2))*(N:ℝ)) := by
  have H := logPartition_upper_tail hN β (a*(N:ℝ)) (by positivity)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  change -(4*a^2/(Real.pi^2*β^2))*(N:ℝ) =
    -(a*(N:ℝ))^2/(2*(Real.pi^2*β^2*(N:ℝ)/8))
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem logPartition_lower_tail_linear {N : ℕ} (hN : 0 < N) {β a : ℝ}
    (hβ : β ≠ 0) (ha : 0 ≤ a) :
    (disorderLaw N).real {J | a*(N:ℝ) ≤
      (∫ K, logPartition β K ∂disorderLaw N)-logPartition β J} ≤
      Real.exp (-(4*a^2/(Real.pi^2*β^2))*(N:ℝ)) := by
  have H := logPartition_lower_tail hN β (a*(N:ℝ)) (by positivity)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  change -(4*a^2/(Real.pi^2*β^2))*(N:ℝ) =
    -(a*(N:ℝ))^2/(2*(Real.pi^2*β^2*(N:ℝ)/8))
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem gibbsEnergyTail_probability_le {N : ℕ} (hN : 0 < N) {β γ e a : ℝ}
    (hβ : 0 < β) (hβγ : β < γ) (ha : 0 < a)
    (hP : quenchedPressure γ N-quenchedPressure β N ≤ (γ-β)*e-3*a) :
    (disorderLaw N).real {J | Real.exp (-a*(N:ℝ)) < gibbsEnergyTail β e J} ≤
      2*Real.exp (-(4*a^2/(Real.pi^2*γ^2))*(N:ℝ)) := by
  let A := {J : Disorder N | a*(N:ℝ) ≤ logPartition γ J-
    ∫ K, logPartition γ K ∂disorderLaw N}
  let B := {J : Disorder N | a*(N:ℝ) ≤
    (∫ K, logPartition β K ∂disorderLaw N)-logPartition β J}
  have hsub : {J : Disorder N | Real.exp (-a*(N:ℝ)) < gibbsEnergyTail β e J} ⊆ A ∪ B := by
    intro J hJ
    by_contra hbad
    have hA : logPartition γ J-(∫ K, logPartition γ K ∂disorderLaw N) < a*(N:ℝ) :=
      lt_of_not_ge (fun h => hbad (Or.inl h))
    have hB : (∫ K, logPartition β K ∂disorderLaw N)-logPartition β J < a*(N:ℝ) :=
      lt_of_not_ge (fun h => hbad (Or.inr h))
    have hPlin := mul_le_mul_of_nonneg_right hP (show (0:ℝ) ≤ N by positivity)
    have hNne : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [quenchedPressure,sub_mul,div_mul_cancel₀ _ hNne] at hPlin
    have hbound := gibbsEnergyTail_le hβγ e J
    have hsmall : logPartition γ J-logPartition β J-(γ-β)*(N:ℝ)*e ≤ -a*(N:ℝ) := by
      nlinarith
    exact (not_lt_of_ge (hbound.trans (Real.exp_le_exp.mpr hsmall))) hJ
  have hγ : 0 < γ := hβ.trans hβγ
  have Hγ := logPartition_upper_tail_linear hN hγ.ne' ha.le
  have Hβ := logPartition_lower_tail_linear hN hβ.ne' ha.le
  have hrate : 4*a^2/(Real.pi^2*γ^2) ≤ 4*a^2/(Real.pi^2*β^2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Real.pi)
    nlinarith
  have Hβ' : (disorderLaw N).real B ≤
      Real.exp (-(4*a^2/(Real.pi^2*γ^2))*(N:ℝ)) := by
    apply Hβ.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hrate) (by positivity)
  exact (measureReal_mono hsub).trans ((measureReal_union_le A B).trans (by linarith))
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarOneAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem scalarMagnetization_zero : scalarMagnetization 0 = 0 := by
  simp [scalarMagnetization]

theorem scalarMagnetization_hasDerivAt (z : ℝ) :
    HasDerivAt scalarMagnetization (1/(Real.cosh z)^2) z := by
  have H : HasDerivAt scalarMagnetization
      ((Real.cosh z*Real.cosh z-Real.sinh z*Real.sinh z)/(Real.cosh z)^2) z :=
    (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z) (Real.cosh_pos z).ne'
  apply H.congr_deriv
  congr 1
  nlinarith [Real.cosh_sq_sub_sinh_sq z]

theorem scalarMagnetization_lipschitz : LipschitzWith 1 scalarMagnetization := by
  rw [← lipschitzOnWith_univ]
  apply (convex_univ : Convex ℝ (Set.univ : Set ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun z _ => (scalarMagnetization_hasDerivAt z).hasDerivWithinAt)
  intro z _
  change ‖(1/(Real.cosh z)^2:ℝ)‖ ≤ (1:ℝ)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (div_le_one (by positivity)).mpr
  nlinarith [Real.one_le_cosh z]

theorem scalarMagnetization_abs_le (z : ℝ) : |scalarMagnetization z| ≤ |z| := by
  simpa [scalarMagnetization_zero,Real.dist_eq] using scalarMagnetization_lipschitz.dist_le_mul z 0

theorem scalarSpinTerminal_integrable (v : ℝ) :
    Integrable (fun y => scalarSpinTerminal (v*y)) (gaussianReal 0 1) := by
  have hi : Integrable (fun y : ℝ => |scalarSpinTerminal 0|+|v| * |y|) (gaussianReal 0 1) :=
    (integrable_const _).add (((memLp_id_gaussianReal 1).integrable (by norm_num)).norm.const_mul |v|)
  apply hi.mono' (scalarSpinTerminal_lipschitz.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  filter_upwards [] with y
  have H := scalarSpinTerminal_lipschitz.dist_le_mul (v*y) 0
  simp only [Real.dist_eq,sub_zero,NNReal.coe_one,one_mul,abs_mul] at H
  rw [Real.norm_eq_abs]
  have h := abs_add_le (scalarSpinTerminal (v*y)-scalarSpinTerminal 0) (scalarSpinTerminal 0)
  rw [sub_add_cancel] at h
  change |scalarSpinTerminal (v*y)| ≤ |scalarSpinTerminal 0|+|v| * |y|
  linarith

theorem scalarGaussianValue_hasDerivAt (v : ℝ) :
    HasDerivAt scalarGaussianValue (∫ y, y*scalarMagnetization (v*y) ∂gaussianReal 0 1) v := by
  have HC := scalarMagnetization_lipschitz.continuous
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) (bound := fun y : ℝ => |y|)
    (F := fun x y : ℝ => scalarSpinTerminal (x*y))
    (F' := fun x y : ℝ => y*scalarMagnetization (x*y))
    (by simp) (Filter.Eventually.of_forall (fun _ =>
      (scalarSpinTerminal_lipschitz.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable))
    (scalarSpinTerminal_integrable v)
    (continuous_id.mul (HC.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y _ _ => ?_))
    ((memLp_id_gaussianReal 1).integrable (by norm_num)).norm
    (Filter.Eventually.of_forall (fun y x _ => ?_))).2
  · rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (scalarMagnetization_abs_le_one _)
  · simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using (scalarSpinTerminal_hasDerivAt (x*y)).comp x ((hasDerivAt_id x).mul_const y)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarOneAtomMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem scalarGaussianOverlap_integrable (v : ℝ) :
    Integrable (fun y => (scalarMagnetization (v*y))^2) (gaussianReal 0 1) := by
  apply (integrable_const (1:ℝ)).mono'
    ((scalarMagnetization_lipschitz.continuous.comp (continuous_const.mul continuous_id)).pow 2).aestronglyMeasurable
  filter_upwards [] with y
  change ‖(scalarMagnetization (v*y))^2‖ ≤ 1
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (_:ℝ))] using scalarMagnetization_sq_le_one (v*y)

theorem scalarGaussianValue_derivative (v : ℝ) :
    HasDerivAt scalarGaussianValue (v*(1-scalarGaussianOverlap v)) v := by
  have HC := scalarMagnetization_lipschitz.continuous
  have iu : Integrable (fun y => scalarMagnetization (v*y)) (gaussianReal 0 1) := by
    apply (integrable_const (1:ℝ)).mono' (HC.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    filter_upwards [] with y
    exact scalarMagnetization_abs_le_one (v*y)
  have idu : Integrable (fun y => v*(1-(scalarMagnetization (v*y))^2)) (gaussianReal 0 1) :=
    ((integrable_const (1:ℝ)).sub (scalarGaussianOverlap_integrable v)).const_mul v
  have iyu : Integrable (fun y => y*scalarMagnetization (v*y)) (gaussianReal 0 1) := by
    apply (((memLp_id_gaussianReal 1).integrable (by norm_num)).norm).mono'
      (continuous_id.mul (HC.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    filter_upwards [] with y
    change ‖y*scalarMagnetization (v*y)‖ ≤ ‖y‖
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (scalarMagnetization_abs_le_one _)
  have hd (y : ℝ) : HasDerivAt (fun y => scalarMagnetization (v*y))
      (v*(1-(scalarMagnetization (v*y))^2)) y := by
    have H := (scalarMagnetization_hasDerivAt (v*y)).comp y ((hasDerivAt_id y).const_mul v)
    rw [scalarMagnetization_derivative_identity] at H
    simpa only [Function.comp_def,mul_one,mul_comm] using H
  have HI := gaussian_integral_mul_eq_integral_deriv _ _ hd iu idu iyu
  rw [integral_const_mul,integral_sub (integrable_const _) (scalarGaussianOverlap_integrable v)] at HI
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at HI
  simpa only [HI,scalarGaussianOverlap] using scalarGaussianValue_hasDerivAt v

theorem gaussian_square_integral : (∫ y : ℝ, y^2 ∂gaussianReal 0 1) = 1 := by
  have H := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at H
  simpa only [integral_id_gaussianReal,sub_zero,NNReal.coe_one] using H

theorem scalarGaussianOverlap_normalized_tendsto :
    Tendsto (fun v : ℝ => scalarGaussianOverlap v/v^2) (𝓝[>] 0) (𝓝 1) := by
  have HB : ∀ᶠ v : ℝ in 𝓝[>] 0, ∀ᵐ y ∂gaussianReal 0 1,
      ‖(scalarMagnetization (v*y)/v)^2‖ ≤ y^2 := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv : 0 < v := hv
    filter_upwards [] with y
    have h : |scalarMagnetization (v*y)/v| ≤ |y| := by
      rw [abs_div,abs_of_pos hv,div_le_iff₀ hv]
      simpa only [abs_mul,abs_of_pos hv,mul_comm] using scalarMagnetization_abs_le (v*y)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq.mpr h
  have HL : ∀ᵐ y ∂gaussianReal 0 1,
      Tendsto (fun v : ℝ => (scalarMagnetization (v*y)/v)^2) (𝓝[>] 0) (𝓝 (y^2)) := by
    filter_upwards [] with y
    have H : HasDerivAt (fun v : ℝ => scalarMagnetization (v*y)) y 0 := by
      have H := (scalarMagnetization_hasDerivAt (0*y)).comp 0 ((hasDerivAt_id (0:ℝ)).mul_const y)
      simpa only [Function.comp_def,id_eq,zero_mul,Real.cosh_zero,one_pow,div_one,one_mul] using H
    have HT := H.tendsto_slope_zero_right
    simp only [zero_add,zero_mul,scalarMagnetization_zero,sub_zero,smul_eq_mul] at HT
    simpa only [div_eq_mul_inv,mul_comm] using HT.pow 2
  have HI := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1) (F := fun v y : ℝ => (scalarMagnetization (v*y)/v)^2) (fun y : ℝ => y^2)
    (Filter.Eventually.of_forall (fun v =>
      (((scalarMagnetization_lipschitz.continuous.comp (continuous_const.mul continuous_id)).div_const v).pow 2).aestronglyMeasurable))
    HB (memLp_id_gaussianReal 2).integrable_sq HL
  simp only [div_pow,integral_div,gaussian_square_integral] at HI
  exact HI
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarInstability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem oneAtomTrial_hasDerivAt {β : ℝ} (hβ : 0 < β) (v : ℝ) :
    HasDerivAt (oneAtomTrial β) (v*(v^2/β^2-scalarGaussianOverlap v)) v := by
  have H := (scalarGaussianValue_derivative v).add
    ((((hasDerivAt_const v (1:ℝ)).sub (((hasDerivAt_id v).pow 2).div_const (β^2))).pow 2).const_mul (β^2/4))
  apply H.congr_deriv
  dsimp only [Pi.sub_apply,Pi.pow_apply,id_eq]
  norm_num only [Nat.cast_ofNat,show 2-1=1 by rfl,pow_one]
  field_simp [hβ.ne']
  ring

theorem oneAtomTrial_zero (β : ℝ) : oneAtomTrial β 0 = Real.log 2+β^2/4 := by
  simp [oneAtomTrial,scalarGaussianValue,scalarSpinTerminal]

theorem exists_oneAtomTrial_lt_annealed {β : ℝ} (hβ : 1 < β) :
    ∃ v : ℝ, 0 < v ∧ v < β ∧ oneAtomTrial β v < Real.log 2+β^2/4 := by
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  have hc : 1/β^2 < (1:ℝ) := (div_lt_one (sq_pos_of_pos hβpos)).mpr (by nlinarith)
  have HE := scalarGaussianOverlap_normalized_tendsto.eventually (eventually_gt_nhds hc)
  have Hβ : ∀ᶠ v : ℝ in 𝓝[>] 0, v < β :=
    (eventually_lt_nhds hβpos).filter_mono nhdsWithin_le_nhds
  obtain ⟨b,hb,hE⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (HE.and Hβ)
  have hbpos : 0 < b := hb
  have hanti : StrictAntiOn (oneAtomTrial β) (Set.Icc 0 b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      ((continuous_iff_continuousAt.mpr (fun v => (oneAtomTrial_hasDerivAt hβpos v).continuousAt)).continuousOn)
    intro v hv
    rw [interior_Icc] at hv
    rw [(oneAtomTrial_hasDerivAt hβpos v).deriv]
    apply mul_neg_of_pos_of_neg hv.1
    have H := (hE ⟨hv.1,hv.2.le⟩).1
    have H' := (lt_div_iff₀ (sq_pos_of_pos hv.1)).mp H
    rw [div_eq_mul_inv] at H' ⊢
    exact sub_neg.mpr (by nlinarith)
  refine ⟨b,hbpos,(hE ⟨hbpos,le_rfl⟩).2,?_⟩
  rw [← oneAtomTrial_zero β]
  exact hanti ⟨le_rfl,hbpos.le⟩ ⟨hbpos.le,le_rfl⟩ hbpos

theorem extendedQuantileParisi_one (β q : ℝ) :
    extendedQuantileParisi 0 β (fun _ => q) =
      scalarGaussianValue (β*Real.sqrt q)+(β^2/4)*(1-q)^2 := by
  simp only [extendedQuantileParisi,scalarHierarchy]
  have he : (Fin.last 0 : Fin 1) = 0 := rfl
  rw [he,cumulativeGapMap_zero]
  norm_num only [quantileMass,Fin.val_zero,Nat.cast_add,Nat.cast_zero,Nat.cast_one,zero_add,zero_div]
  simp only [scalarStep,gaussianStep,ite_true,zero_add,one_mul,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,one_smul]
  change scalarGaussianValue (β*Real.sqrt q)+(β^2/4)*(1-2*q+q^2) = _
  ring

theorem oneAtomTrial_eq_extended {β v : ℝ} (hβ : 0 < β) (hv : 0 ≤ v) :
    oneAtomTrial β v = extendedQuantileParisi 0 β (fun _ => v^2/β^2) := by
  rw [extendedQuantileParisi_one]
  have hs : β*Real.sqrt (v^2/β^2) = v := by
    rw [Real.sqrt_div (sq_nonneg v),Real.sqrt_sq hv,Real.sqrt_sq hβ.le]
    field_simp [hβ.ne']
  rw [hs]
  rfl

theorem finiteParisiInf_lt_annealed {β : ℝ} (hβ : 1 < β) :
    finiteParisiInf β < Real.log 2+β^2/4 := by
  obtain ⟨v,hv,hvβ,H⟩ := exists_oneAtomTrial_lt_annealed hβ
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  rw [oneAtomTrial_eq_extended hβpos hv.le] at H
  apply lt_of_le_of_lt (finiteParisiInf_le β (fun _ => v^2/β^2) monotone_const (fun _ => ?_)) H
  constructor
  · positivity
  · apply (div_le_one (sq_pos_of_pos hβpos)).mpr
    nlinarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem quantileOverlapMean_bounds (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ) (j : Fin (k+1)) :
    quantileOverlapMean k β Q j ∈ Set.Icc 0 1 :=
  hierarchyMeanOverlap_bounds _ _ _ _ (fun i s => by cases s i <;> norm_num [spin]) _

theorem extendedQuantileParisi_continuous (k : ℕ) (β : ℝ) :
    Continuous (extendedQuantileParisi k β) := by
  have hv : Continuous (fun Q : Fin (k+1) → ℝ => fun b => β*Real.sqrt (cumulativeGapMap k Q b)) := by
    apply continuous_pi
    intro b
    exact continuous_const.mul (Real.continuous_sqrt.comp ((continuous_apply b).comp (cumulativeGapMap k).continuous))
  have H := (skBlockRoot_contDiff 1 k).continuous.comp ((continuous_const (y := (0:ℝ))).prodMk hv)
  change Continuous (fun Q : Fin (k+1) → ℝ => skBlockRoot 1 k 0 (fun b => β*Real.sqrt (cumulativeGapMap k Q b))) at H
  simp only [skBlockRoot_zero_disorder_scalar (by norm_num : 0 < 1),Nat.cast_one,one_mul] at H
  apply H.add
  apply continuous_const.mul
  exact (continuous_const.sub (continuous_const.mul (continuous_apply (Fin.last k)))).add
    (continuous_finsetSum _ (fun j _ => continuous_const.mul ((continuous_apply j).pow 2)))

theorem extendedQuantileParisi_hasDerivAt {k : ℕ} (β : ℝ)
    (Q : ℝ → Fin (k+1) → ℝ) {t : ℝ} {V : Fin (k+1) → ℝ}
    (hQ : HasDerivAt Q V t) (hgap : ∀ j, 0 < cumulativeGapMap k (Q t) j) :
    HasDerivAt (fun u => extendedQuantileParisi k β (Q u))
      ((β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*
        (Q t j-quantileOverlapMean k β (Q t) j)) t := by
  let v := fun u j => β*Real.sqrt (cumulativeGapMap k (Q u) j)
  let vp := fun j => β*(cumulativeGapMap k V j/(2*Real.sqrt (cumulativeGapMap k (Q t) j)))
  let r := quantileOverlapMean k β (Q t)
  have hv : HasDerivAt v vp t := by
    apply hasDerivAt_pi.mpr
    intro j
    have H := hasDerivAt_pi.mp ((cumulativeGapMap k).hasFDerivAt.comp_hasDerivAt t hQ) j
    exact (H.sqrt (hgap j).ne').const_mul β
  have hvp (j : Fin (k+1)) : vp j*v t j = (β^2/2)*cumulativeGapMap k V j := by
    have hsqrt := (Real.sqrt_pos.mpr (hgap j)).ne'
    dsimp only [vp,v]
    field_simp [hsqrt]
  have H := skBlockPressure_hasDerivAt (N := 1) (by norm_num) (fun _ => 0) v
    (hasDerivAt_const t (0:ℝ)) hv
  dsimp only at H
  simp only [zero_mul,zero_div,zero_add,Nat.cast_one,div_one,
    skBlockRoot_zero_disorder_scalar (by norm_num : 0 < 1),one_mul,hvp] at H
  have he : (∑ b, (β^2/2)*cumulativeGapMap k V b*
      (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r l else 0)) =
      (β^2/2)*(V (Fin.last k)-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V l*r l) := by
    rw [← fixed_field_summation k V r (fun _ => ((k+1:ℕ):ℝ)⁻¹),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  change HasDerivAt (fun u => scalarHierarchy (k+1) (quantileMass k) (v u) scalarSpinTerminal 0)
    (∑ b, (β^2/2)*cumulativeGapMap k V b*
      (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r l else 0)) t at H
  rw [he] at H
  have HS : HasDerivAt (fun u => ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q u j)^2)
      (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(2*Q t j*V j)) t := by
    apply HasDerivAt.fun_sum
    intro j _
    simpa using ((hasDerivAt_pi.mp hQ j).pow 2).const_mul (((k+1:ℕ):ℝ)⁻¹)
  have HC := (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_pi.mp hQ (Fin.last k)).const_mul 2)).add HS).const_mul (β^2/4)
  have HA := H.add HC
  apply HA.congr_deriv
  have he1 : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(2*Q t j*V j)) =
      2*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*Q t j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he2 : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*(Q t j-r j)) =
      (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*Q t j)-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*r j := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  change _ = (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*(Q t j-r j)
  rw [he1,he2]
  ring
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem extendedQuantileParisi_lipschitz_positive {k : ℕ} (β : ℝ) (A B : Fin (k+1) → ℝ)
    (hA : ∀ j, A j ∈ Set.Icc 0 1) (hB : ∀ j, B j ∈ Set.Icc 0 1)
    (hgA : ∀ j, 0 < cumulativeGapMap k A j) (hgB : ∀ j, 0 < cumulativeGapMap k B j) :
    |extendedQuantileParisi k β B-extendedQuantileParisi k β A| ≤
      (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|B j-A j| := by
  let Q := fun t : ℝ => (1-t) • A+t • B
  let d := fun t => (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*
    (Q t j-quantileOverlapMean k β (Q t) j)
  have hQ (t : ℝ) : HasDerivAt Q (B-A) t := by
    apply hasDerivAt_pi.mpr
    intro j
    have H := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const (A j)).add
      ((hasDerivAt_id t).mul_const (B j))
    exact H.congr_deriv (by simp; ring)
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (j : Fin (k+1)) : 0 < cumulativeGapMap k (Q t) j := by
    simp only [Q,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    by_cases h : t=0
    · simpa [h] using hgA j
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2) (hgA j).le) (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h)) (hgB j))
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (j : Fin (k+1)) : Q t j ∈ Set.Icc 0 1 := by
    change (1-t)*A j+t*B j ∈ Set.Icc 0 1
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hA j).1) (mul_nonneg ht.1 (hB j).1)
    · have h1 := mul_le_mul_of_nonneg_left (hA j).2 (sub_nonneg.mpr ht.2)
      have h2 := mul_le_mul_of_nonneg_left (hB j).2 ht.1
      linarith
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt (fun t => extendedQuantileParisi k β (Q t)) (d t) t :=
    extendedQuantileParisi_hasDerivAt β Q (hQ t) (hg t ht)
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      ‖d t‖ ≤ (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|B j-A j| := by
    rw [Real.norm_eq_abs]
    dsimp only [d]
    rw [abs_mul,abs_of_nonneg (show 0 ≤ β^2/2 by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    have hr := quantileOverlapMean_bounds k β (Q t) j
    have hdif : |Q t j-quantileOverlapMean k β (Q t) j| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [(hb t ht j).1,(hb t ht j).2,hr.1,hr.2]
    rw [abs_mul,abs_mul,abs_of_nonneg (show 0 ≤ ((k+1:ℕ):ℝ)⁻¹ by positivity)]
    exact mul_le_of_le_one_right (by positivity) hdif
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt) (fun t ht => hbound t ⟨ht.1,ht.2.le⟩)
  simpa only [Q,sub_self,zero_smul,one_smul,zero_add,sub_zero,add_zero,Real.norm_eq_abs] using H

theorem strictQuantile_gap (k : ℕ) (j : Fin (k+1)) :
    cumulativeGapMap k (strictQuantile k) j = 1/((k:ℝ)+2) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [cumulativeGapMap_zero,strictQuantile]
  · simp only [cumulativeGapMap_succ,strictQuantile,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    ring

theorem strictQuantile_mem (k : ℕ) (j : Fin (k+1)) : strictQuantile k j ∈ Set.Icc 0 1 := by
  have hj : (j.val:ℝ)+1 ≤ (k:ℝ)+1 := by exact_mod_cast Nat.succ_le_of_lt j.isLt
  unfold strictQuantile
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    linarith

theorem regularizeQuantile_positive {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, 0 ≤ cumulativeGapMap k Q j) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1) (j : Fin (k+1)) :
    0 < cumulativeGapMap k (regularizeQuantile k Q ε) j := by
  simp only [regularizeQuantile,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,strictQuantile_gap]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hε.2) (hQ j))
    (mul_pos hε.1 (by positivity))

theorem regularizeQuantile_mem {k : ℕ} (Q : Fin (k+1) → ℝ) (hQ : ∀ j, Q j ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Icc 0 1) (j : Fin (k+1)) :
    regularizeQuantile k Q ε j ∈ Set.Icc 0 1 := by
  change (1-ε)*Q j+ε*strictQuantile k j ∈ Set.Icc 0 1
  have hR := strictQuantile_mem k j
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) (hQ j).1) (mul_nonneg hε.1 hR.1)
  · have H1 := mul_le_mul_of_nonneg_left (hQ j).2 (sub_nonneg.mpr hε.2)
    have H2 := mul_le_mul_of_nonneg_left hR.2 hε.1
    linarith

theorem regularizeQuantile_tendsto (k : ℕ) (Q : Fin (k+1) → ℝ) :
    Tendsto (fun n : ℕ => regularizeQuantile k Q (1/((n:ℝ)+1))) atTop (𝓝 Q) := by
  have H : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [regularizeQuantile,sub_zero,one_smul,zero_smul,add_zero] using
    (((tendsto_const_nhds (x := (1:ℝ))).sub H).smul (tendsto_const_nhds (x := Q))).add
      (H.smul (tendsto_const_nhds (x := strictQuantile k)))

theorem extendedQuantileParisi_lipschitz {k : ℕ} (β : ℝ) (A B : Fin (k+1) → ℝ)
    (hA : ∀ j, A j ∈ Set.Icc 0 1) (hB : ∀ j, B j ∈ Set.Icc 0 1)
    (hmA : Monotone A) (hmB : Monotone B) :
    |extendedQuantileParisi k β B-extendedQuantileParisi k β A| ≤
      (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|B j-A j| := by
  have hgA := (cumulativeGapMap_nonneg_iff k A).mpr ⟨(hA 0).1,hmA⟩
  have hgB := (cumulativeGapMap_nonneg_iff k B).mpr ⟨(hB 0).1,hmB⟩
  let ε := fun n : ℕ => 1/((n:ℝ)+1)
  have hε (n : ℕ) : ε n ∈ Set.Ioc 0 1 := by
    dsimp only [ε]
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have H (n : ℕ) : |extendedQuantileParisi k β (regularizeQuantile k B (ε n))-
      extendedQuantileParisi k β (regularizeQuantile k A (ε n))| ≤
      (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|B j-A j| := by
    apply (extendedQuantileParisi_lipschitz_positive β _ _
      (regularizeQuantile_mem A hA ⟨(hε n).1.le,(hε n).2⟩)
      (regularizeQuantile_mem B hB ⟨(hε n).1.le,(hε n).2⟩)
      (regularizeQuantile_positive A hgA (hε n)) (regularizeQuantile_positive B hgB (hε n))).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have he : regularizeQuantile k B (ε n) j-regularizeQuantile k A (ε n) j = (1-ε n)*(B j-A j) := by
      simp only [regularizeQuantile,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr (hε n).2)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [(hε n).1])
  have HA := (extendedQuantileParisi_continuous k β).continuousAt.tendsto.comp (regularizeQuantile_tendsto k A)
  have HB := (extendedQuantileParisi_continuous k β).continuousAt.tendsto.comp (regularizeQuantile_tendsto k B)
  exact le_of_tendsto (HB.sub HA).abs (Eventually.of_forall H)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteScalarGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem quantileFirstMoment_nonneg (k : ℕ) (Q : Fin (k+1) → ℝ) (hQ : ∀ j, 0 ≤ Q j) :
    0 ≤ quantileFirstMoment k Q :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (hQ j))

theorem quantileFirstMoment_sq_le (k : ℕ) (Q : Fin (k+1) → ℝ) :
    (quantileFirstMoment k Q)^2 ≤ quantileSecondMoment k Q := by
  let a := quantileFirstMoment k Q
  have H : 0 ≤ ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j-a)^2 :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (sq_nonneg _))
  have he (j : Fin (k+1)) : ((k+1:ℕ):ℝ)⁻¹*(Q j-a)^2 =
      ((k+1:ℕ):ℝ)⁻¹*(Q j)^2-(2*a)*(((k+1:ℕ):ℝ)⁻¹*Q j)+a^2*((k+1:ℕ):ℝ)⁻¹ := by ring
  simp_rw [he] at H
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib] at H
  have h1 : (∑ j : Fin (k+1), (2*a)*(((k+1:ℕ):ℝ)⁻¹*Q j)) = (2*a)*a := by
    rw [← Finset.mul_sum]
    rfl
  have h2 : (∑ _j : Fin (k+1), a^2*((k+1:ℕ):ℝ)⁻¹) = a^2 := by
    rw [← Finset.mul_sum,uniformAtom_sum,mul_one]
  rw [h1,h2] at H
  change 0 ≤ quantileSecondMoment k Q-(2*a)*a+a^2 at H
  dsimp only [a] at H
  nlinarith

theorem scalarHierarchy_zero_variance (n : ℕ) (m : Fin n → ℝ) (f : ℝ → ℝ) :
    scalarHierarchy n m (fun _ => 0) f = f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [scalarHierarchy,scalarStep_zero]
    exact ih _ f

theorem extendedQuantileParisi_zero (k : ℕ) (β : ℝ) :
    extendedQuantileParisi k β (fun _ => 0) = Real.log 2+β^2/4 := by
  have hg : cumulativeGapMap k (fun _ => 0) = 0 := map_zero _
  have he : (fun b => β*Real.sqrt (cumulativeGapMap k (fun _ => 0) b)) = fun _ => 0 := by
    rw [hg]
    simp
  rw [extendedQuantileParisi,he,scalarHierarchy_zero_variance]
  simp [scalarSpinTerminal]

theorem quantileSecondMoment_of_gap {k : ℕ} {β δ : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ)
    (Q : Fin (k+1) → ℝ) (hm : Monotone Q) (hQ : ∀ j, Q j ∈ Set.Icc 0 1)
    (hgap : extendedQuantileParisi k β Q ≤ Real.log 2+β^2/4-δ) :
    (2*δ/β^2)^2 ≤ quantileSecondMoment k Q := by
  have H := extendedQuantileParisi_lipschitz β (fun _ => 0) Q
    (fun _ => ⟨le_rfl,zero_le_one⟩) hQ monotone_const hm
  rw [extendedQuantileParisi_zero] at H
  simp only [sub_zero,abs_of_nonneg (hQ _).1] at H
  have H' := neg_le_abs (extendedQuantileParisi k β Q-(Real.log 2+β^2/4))
  have hmean : 2*δ/β^2 ≤ quantileFirstMoment k Q := by
    apply (div_le_iff₀ (sq_pos_of_pos hβ)).mpr
    change _ ≤ (β^2/2)*quantileFirstMoment k Q at H
    nlinarith
  apply le_trans _ (quantileFirstMoment_sq_le k Q)
  apply sq_le_sq.mpr
  rw [abs_of_nonneg (by positivity : 0 ≤ 2*δ/β^2),
    abs_of_nonneg (quantileFirstMoment_nonneg k Q (fun j => (hQ j).1))]
  exact hmean

theorem extendedQuantileParisi_temperature_rescale {k : ℕ} {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (Q : Fin (k+1) → ℝ) :
    extendedQuantileParisi k γ ((β/γ)^2 • Q) = extendedQuantileParisi k β Q+
      (γ^2-β^2)/4*(1-(β^2/γ^2)*quantileSecondMoment k Q) := by
  have he (j : Fin (k+1)) : γ*Real.sqrt (cumulativeGapMap k ((β/γ)^2 • Q) j) =
      β*Real.sqrt (cumulativeGapMap k Q j) := by
    simp only [map_smul,Pi.smul_apply,smul_eq_mul]
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (div_nonneg hβ.le hγ.le)]
    field_simp
  have hs : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(((β/γ)^2 • Q) j)^2) =
      (β/γ)^4*quantileSecondMoment k Q := by
    unfold quantileSecondMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  simp only [extendedQuantileParisi,he]
  rw [hs]
  rw [show (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2) = quantileSecondMoment k Q from rfl]
  simp only [Pi.smul_apply,smul_eq_mul]
  field_simp [hγ.ne']
  ring

theorem rescaledQuantiles_admissible {k : ℕ} {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ)
    (Q : Fin (k+1) → ℝ) (hm : Monotone Q) (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    Monotone ((β/γ)^2 • Q) ∧ ∀ j, ((β/γ)^2 • Q) j ∈ Set.Icc 0 1 := by
  have hγ : 0 < γ := hβ.trans_le hβγ
  have ha : (β/γ)^2 ≤ 1 := by
    apply (sq_le_one_iff_abs_le_one _).mpr
    rw [abs_of_nonneg (div_nonneg hβ.le hγ.le)]
    exact (div_le_one hγ).mpr hβγ
  constructor
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (hm hij) (sq_nonneg _)
  · intro j
    change (β/γ)^2*Q j ∈ Set.Icc 0 1
    constructor
    · exact mul_nonneg (sq_nonneg _) (hQ j).1
    · exact (mul_le_of_le_one_right (sq_nonneg _) (hQ j).2).trans ha
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_FiniteTemperatureBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem finiteParisiInf_temperature_upper {β γ δ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ)
    (hδ : 0 < δ) (hgap : finiteParisiInf β ≤ Real.log 2+β^2/4-2*δ) :
    finiteParisiInf γ ≤ finiteParisiInf β+
      (γ^2-β^2)/4*(1-(β^2/γ^2)*(2*δ/β^2)^2) := by
  have hγ : 0 < γ := hβ.trans_le hβγ
  have hK : 0 ≤ (γ^2-β^2)/4 := by nlinarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have hsmall : 0 < min ε δ := lt_min hε hδ
  obtain ⟨p,hp,hpLt⟩ := exists_lt_of_csInf_lt (finiteParisiValues_nonempty β)
    (show finiteParisiInf β < finiteParisiInf β+min ε δ by linarith)
  obtain ⟨k,Q,hm,hQ,rfl⟩ := hp
  have hg : extendedQuantileParisi k β Q ≤ Real.log 2+β^2/4-δ := by
    linarith [min_le_right ε δ]
  have hS := quantileSecondMoment_of_gap hβ hδ.le Q hm hQ hg
  obtain ⟨hm',hQ'⟩ := rescaledQuantiles_admissible hβ hβγ Q hm hQ
  have HT := finiteParisiInf_le γ ((β/γ)^2 • Q) hm' hQ'
  rw [extendedQuantileParisi_temperature_rescale hβ hγ Q] at HT
  have HP : (γ^2-β^2)/4*(1-(β^2/γ^2)*quantileSecondMoment k Q) ≤
      (γ^2-β^2)/4*(1-(β^2/γ^2)*(2*δ/β^2)^2) := by
    apply mul_le_mul_of_nonneg_left _ hK
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hS (by positivity)) 1
  linarith [min_le_left ε δ]

theorem exists_strict_finiteParisiInf_secant {β : ℝ} (hβ : 1 < β) :
    ∃ γ : ℝ, β < γ ∧ (finiteParisiInf γ-finiteParisiInf β)/(γ-β) < β/2 := by
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  let δ := (Real.log 2+β^2/4-finiteParisiInf β)/2
  have hδ : 0 < δ := by dsimp only [δ]; linarith [finiteParisiInf_lt_annealed hβ]
  let c := (2*δ/β^2)^2
  have hc : 0 < c := sq_pos_of_pos (div_pos (mul_pos (by norm_num) hδ) (sq_pos_of_pos hβpos))
  let S := fun γ : ℝ => (γ+β)/4*(1-(β^2/γ^2)*c)
  have HS : ContinuousAt S β := by
    dsimp only [S]
    fun_prop (disch := positivity)
  have hS : S β < β/2 := by
    dsimp only [S]
    rw [div_self (sq_pos_of_pos hβpos).ne',one_mul]
    nlinarith [mul_pos hβpos hc]
  have HE : ∀ᶠ γ in 𝓝[>] β, S γ < β/2 :=
    (HS.tendsto.eventually (eventually_lt_nhds hS)).filter_mono nhdsWithin_le_nhds
  have HM : ∀ᶠ γ in 𝓝[>] β, β < γ := self_mem_nhdsWithin
  obtain ⟨γ,hγβ,hγS⟩ := (HM.and HE).exists
  have hβγ : β < γ := hγβ
  have HU := finiteParisiInf_temperature_upper hβpos hβγ.le hδ
    (show finiteParisiInf β ≤ Real.log 2+β^2/4-2*δ by dsimp only [δ]; linarith)
  have hd : 0 < γ-β := sub_pos.mpr hβγ
  have he : ((γ^2-β^2)/4*(1-(β^2/γ^2)*c))/(γ-β) = S γ := by
    dsimp only [S]
    field_simp [hd.ne', (hβpos.trans hβγ).ne']
    ring
  refine ⟨γ,hβγ,lt_of_le_of_lt ?_ hγS⟩
  rw [← he]
  exact div_le_div_of_nonneg_right (by dsimp only [c]; linarith [HU]) hd.le
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_EnergyTailGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem coverage_energy_tail_oai {β : ℝ} (hβ : 1 < β) :
    ∃ e₁ : ℝ, e₁ ∈ Set.Ioo 0 (β/2) ∧ ∃ cE : ℝ, 0 < cE ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        (disorderLaw N).real {J | Real.exp (-cE*(N:ℝ)) < gibbsEnergyTail β e₁ J} ≤
          Real.exp (-cE*(N:ℝ)) := by
  obtain ⟨γ,hβγ,hsec⟩ := exists_strict_finiteParisiInf_secant hβ
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  have hγpos : 0 < γ := hβpos.trans hβγ
  have hd : 0 < γ-β := sub_pos.mpr hβγ
  let L := (finiteParisiInf γ-finiteParisiInf β)/(γ-β)
  obtain ⟨e₁,he₁low,he₁high⟩ := exists_between
    (show max 0 L < β/2 from max_lt (by positivity) hsec)
  have he₁pos : 0 < e₁ := lt_of_le_of_lt (le_max_left 0 L) he₁low
  have hLe : L < e₁ := lt_of_le_of_lt (le_max_right 0 L) he₁low
  let a := (γ-β)*(e₁-L)/6
  have ha : 0 < a := by dsimp only [a]; positivity
  let r := 4*a^2/(Real.pi^2*γ^2)
  have hr : 0 < r := by dsimp only [r]; positivity
  let cE := min a (r/2)
  have hcE : 0 < cE := lt_min ha (by positivity)
  have hca : cE ≤ a := min_le_left _ _
  have hcr : 2*cE ≤ r := by dsimp only [cE]; linarith [min_le_right a (r/2)]
  have Hlim : Tendsto (fun N : ℕ => quenchedPressure γ N-quenchedPressure β N)
      atTop (𝓝 (finiteParisiInf γ-finiteParisiInf β)) :=
    (quenchedPressure_tendsto_finiteParisiInf hγpos).sub
      (quenchedPressure_tendsto_finiteParisiInf hβpos)
  have hlim : finiteParisiInf γ-finiteParisiInf β < (γ-β)*e₁-3*a := by
    have hL : (γ-β)*L = finiteParisiInf γ-finiteParisiInf β := by
      dsimp only [L]; field_simp
    dsimp only [a]
    nlinarith [mul_pos hd (sub_pos.mpr hLe)]
  have HP := Hlim.eventually (eventually_lt_nhds hlim)
  have HN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (Real.log 2/cE))
  have HE : ∀ᶠ N : ℕ in atTop,
      (disorderLaw N).real {J | Real.exp (-cE*(N:ℝ)) < gibbsEnergyTail β e₁ J} ≤
        Real.exp (-cE*(N:ℝ)) := by
    filter_upwards [HP,HN,eventually_gt_atTop (0:ℕ)] with N hP hN hNpos
    have hn : (0:ℝ) ≤ N := by positivity
    have hsub : {J : Disorder N | Real.exp (-cE*(N:ℝ)) < gibbsEnergyTail β e₁ J} ⊆
        {J | Real.exp (-a*(N:ℝ)) < gibbsEnergyTail β e₁ J} := by
      intro J hJ
      exact lt_of_le_of_lt (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg hca) hn)) hJ
    have HM := (measureReal_mono hsub).trans
      (gibbsEnergyTail_probability_le hNpos hβpos hβγ ha hP.le)
    have hlog : Real.log 2 ≤ cE*(N:ℝ) := by
      have HH := (div_le_iff₀ hcE).mp hN
      nlinarith
    have hrate : 2*cE*(N:ℝ) ≤ r*(N:ℝ) := mul_le_mul_of_nonneg_right hcr hn
    apply HM.trans
    change 2*Real.exp (-r*(N:ℝ)) ≤ Real.exp (-cE*(N:ℝ))
    rw [show (2:ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp HE
  exact ⟨e₁,⟨he₁pos,he₁high⟩,cE,hcE,N₀,hN₀⟩
end SK.Analytic

end
end

end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.coverage_energy_tail_oai := @OAI.SK.Analytic.coverage_energy_tail_oai
