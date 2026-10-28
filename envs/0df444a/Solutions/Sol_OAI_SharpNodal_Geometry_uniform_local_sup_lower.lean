-- Prove2me | solution 1 for OAI.SharpNodal.Geometry.uniform_local_sup_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:17:44.886314+00:00
-- url     : https://prove2.me/submissions/850398ab-3129-4a4f-bb57-a9b14004773d

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000
import Theorems.Thm_OAI_SharpNodal_Geometry_exists_isothermal_chart
import Theorems.Thm_OAI_SharpNodal_Geometry_laplaceBeltrami_in_chart
import Theorems.Thm_OAI_SharpNodal_Profiles_full_test_of_profile
import Theorems.Thm_OAI_SharpNodal_Profiles_sup_profile_le_local

section
-- module Solutions.OAIQ4_Nl.NodalLength_Carleman
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma partial_const (c : ℝ) (i : Fin 2) (x : Plane) :
    coordPartial (fun _ => c) i x = 0 := by simp [coordPartial]


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_MassComparison
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

namespace SharpNodal
namespace Profiles
open Carleman

lemma laplacian_const (c : ℝ) (x : Plane) : euclideanLaplacian (fun _ => c) x=0 := by
  unfold euclideanLaplacian
  apply Finset.sum_eq_zero
  intro i _
  have h : coordPartial (fun _ => c) i=(fun _ => 0) := funext (partial_const c i)
  rw [h, partial_const]

end Profiles
end SharpNodal

noncomputable section
open scoped Topology ENNReal
open MeasureTheory Filter Set
namespace SharpNodal.Profiles

lemma ereal_pos_mul_lt_coe_iff {c : ℝ} (hc : 0 < c) (a : EReal) (b : ℝ) :
    (c:EReal)*a < (b:EReal) ↔ a < ((b/c : ℝ):EReal) := by
  cases a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe a =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    simp only [lt_div_iff₀ hc, mul_comm]

lemma ereal_coe_lt_pos_mul_iff {c : ℝ} (hc : 0 < c) (a : EReal) (b : ℝ) :
    (b:EReal) < (c:EReal)*a ↔ ((b/c : ℝ):EReal) < a := by
  cases a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe a =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    simp only [div_lt_iff₀ hc, mul_comm]

lemma logRate_lt_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    logRate S m < (a:EReal) ↔ m < ENNReal.ofReal (Real.exp (2*S*a)) := by
  rw [logRate, ereal_pos_mul_lt_coe_iff (inv_pos.mpr (by positivity : 0<2*S))]
  rw [div_inv_eq_mul, show a*(2*S)=2*S*a by ring]
  rw [show ((2*S*a : ℝ):EReal)=(ENNReal.ofReal (Real.exp (2*S*a))).log by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]]
  exact ENNReal.log_lt_log_iff

lemma lt_logRate_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    (a:EReal) < logRate S m ↔ ENNReal.ofReal (Real.exp (2*S*a)) < m := by
  rw [logRate, ereal_coe_lt_pos_mul_iff (inv_pos.mpr (by positivity : 0<2*S))]
  rw [div_inv_eq_mul, show a*(2*S)=2*S*a by ring]
  rw [show ((2*S*a : ℝ):EReal)=(ENNReal.ofReal (Real.exp (2*S*a))).log by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]]
  exact ENNReal.log_lt_log_iff

lemma logRate_le_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    logRate S m ≤ (a:EReal) ↔ m ≤ ENNReal.ofReal (Real.exp (2*S*a)) := by
  simpa only [not_lt] using not_congr (lt_logRate_iff (a:=a) hS m)

lemma le_logRate_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    (a:EReal) ≤ logRate S m ↔ ENNReal.ofReal (Real.exp (2*S*a)) ≤ m := by
  simpa only [not_lt] using not_congr (logRate_lt_iff (a:=a) hS m)

lemma logRate_mono {S : ℝ} (hS : 0<S) {m₁ m₂ : ℝ≥0∞} (hm : m₁ ≤ m₂) :
    logRate S m₁≤logRate S m₂ := by
  by_contra hn
  obtain ⟨a, ha, hb⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  exact (not_lt_of_ge hm) (((logRate_lt_iff hS _).mp ha).trans ((lt_logRate_iff hS _).mp hb))

lemma exponential_gap {S : ℕ → ℝ} {a b C : ℝ} (hS : Tendsto S atTop atTop)
    (hgap : a<b) (hC : 0<C) :
    ∀ᶠ j in atTop, C*Real.exp (2*S j*a)<Real.exp (2*S j*b) := by
  have hδ : 0<2*(b-a) := by linarith
  have he : ∀ᶠ j in atTop, Real.log C/(2*(b-a))<S j :=
    hS.eventually (eventually_gt_atTop _)
  filter_upwards [he] with j hj
  have hj' : Real.log C<2*S j*(b-a) := by
    have hh := (div_lt_iff₀ hδ).mp hj
    nlinarith only [hh]
  rw [← Real.exp_log hC, ← Real.exp_add, Real.exp_lt_exp]
  nlinarith only [hj']

lemma no_exponential_gap {S : ℕ → ℝ} {A B : ℕ → ℝ≥0∞} {a b C : ℝ}
    (hS : Tendsto S atTop atTop) (hgap : a<b) (hC : 0<C)
    (hA : ∀ᶠ j in atTop, A j≤ENNReal.ofReal (Real.exp (2*S j*a)))
    (hB : ∀ᶠ j in atTop, ENNReal.ofReal (Real.exp (2*S j*b))≤B j)
    (hcomp : ∀ᶠ j in atTop, B j≤ENNReal.ofReal C*A j) : False := by
  have hg := exponential_gap hS hgap hC
  obtain ⟨j, hAj, hBj, hcj, hgj⟩ := (hA.and (hB.and (hcomp.and hg))).exists
  have hle := hBj.trans (hcj.trans (mul_le_mul' le_rfl hAj))
  rw [← ENNReal.ofReal_mul hC.le] at hle
  have hle' : Real.exp (2*S j*b)≤C*Real.exp (2*S j*a) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  exact (not_le_of_gt hgj) hle'

end SharpNodal.Profiles

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ProfileTests
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set

namespace SharpNodal.Profiles
open Carleman

lemma upperSemicontinuousOn_add_real {Ω : Set Plane} {V : Plane → EReal}
    {f : Plane → ℝ} (hV : UpperSemicontinuousOn V Ω) (hf : ContinuousOn f Ω) :
    UpperSemicontinuousOn (fun x => V x+(f x:EReal)) Ω := by
  apply hV.add' (continuous_coe_real_ereal.comp_continuousOn hf).upperSemicontinuousOn
  intro x hx
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma smooth_radiusSquare (x₀ : Plane) : Smooth (radiusSquare x₀) :=
  (contDiff_id.sub contDiff_const).norm_sq ℝ

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma hasFDerivAt_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ x : Plane) : HasFDerivAt (centeredQuadratic A x₀) (A (x-x₀)) x := by
  have ht := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀
  have hAt : HasFDerivAt (fun y => A (y-x₀)) A x := by
    convert! A.hasFDerivAt.comp x ht using 1
    all_goals try with_reducible_and_instances rfl
  convert! (hAt.clm_apply ht).const_mul (1/2:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, id_eq]
  rw [hA y (x-x₀)]
  ring

lemma fderiv_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A) (x₀ : Plane) :
    fderiv ℝ (centeredQuadratic A x₀) = fun x => A (x-x₀) :=
  funext fun x => (hasFDerivAt_centeredQuadratic hA x₀ x).fderiv

lemma partial_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ : Plane) (i : Fin 2) (x : Plane) :
    coordPartial (centeredQuadratic A x₀) i x=A (x-x₀) (EuclideanSpace.single i 1) := by
  rw [coordPartial, fderiv_centeredQuadratic hA]

lemma partial2_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ : Plane) (i j : Fin 2) (x : Plane) :
    coordPartial (coordPartial (centeredQuadratic A x₀) i) j x=
      A (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  rw [show coordPartial (centeredQuadratic A x₀) i =
    fun y => A (y-x₀) (EuclideanSpace.single i 1) from funext (partial_centeredQuadratic hA x₀ i)]
  have ht := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀
  have hh : HasFDerivAt (fun y => A (y-x₀) (EuclideanSpace.single i 1))
      (A.flip (EuclideanSpace.single i 1)) x := by
    convert! (A.flip (EuclideanSpace.single i 1)).hasFDerivAt.comp x ht using 1
    all_goals try with_reducible_and_instances rfl
  simp only [coordPartial, hh.fderiv, ContinuousLinearMap.flip_apply]

lemma laplacian_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ x : Plane) : euclideanLaplacian (centeredQuadratic A x₀) x=
      ∑ i : Fin 2, A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  simp only [euclideanLaplacian, partial2_centeredQuadratic hA]

lemma hessian_on_basis {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) (i j : Fin 2) :
    fderiv ℝ (fderiv ℝ f) x₀ (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)=
      coordPartial (coordPartial f i) j x₀ := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).differentiable (by simp)
  unfold coordPartial
  rw [fderiv_clm_apply hdf.differentiableAt (differentiableAt_const _)]
  simp

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma innerForm_apply (x y : Plane) : innerForm x y=inner ℝ x y := rfl

lemma symmetric_innerForm : SymmetricForm innerForm := by
  intro x y
  exact real_inner_comm y x

lemma formTrace_innerForm : formTrace innerForm=2 := by
  simp [formTrace, innerForm_apply]

lemma formTrace_smul (c : ℝ) (A : BilinearForm) : formTrace (c • A)=c*formTrace A := by
  simp only [formTrace, smul_apply, smul_eq_mul, Finset.mul_sum]

lemma centeredQuadratic_inner_smul (δ : ℝ) (x₀ x : Plane) :
    centeredQuadratic ((2*δ) • innerForm) x₀ x=δ*‖x-x₀‖^2 := by
  simp only [centeredQuadratic, smul_apply, smul_eq_mul, innerForm_apply,
    real_inner_self_eq_norm_sq]
  ring

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ProfileExtraction
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace

namespace SharpNodal.Profiles

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]

lemma basisProfile_le (ell : countableBasis X → EReal) (i : countableBasis X)
    {x : X} (hx : x∈i.val) : basisProfile ell x≤ell i :=
  (iInf_le_of_le i (iInf_le_of_le hx le_rfl))

lemma basisProfile_lt_iff (ell : countableBasis X → EReal) (x : X) (a : EReal) :
    basisProfile ell x<a ↔ ∃ i : countableBasis X, x∈i.val ∧ ell i<a := by
  simp only [basisProfile, iInf_lt_iff, exists_prop]

lemma upperSemicontinuous_basisProfile (ell : countableBasis X → EReal) :
    UpperSemicontinuous (basisProfile ell) := by
  intro x a hxa
  obtain ⟨i, hxi, hia⟩ := (basisProfile_lt_iff ell x a).mp hxa
  filter_upwards [(isOpen_of_mem_countableBasis i.property).mem_nhds hxi] with y hy
  exact (basisProfile_le ell i hy).trans_lt hia

lemma basisProfile_nonpos (ell : countableBasis X → EReal) (hell : ∀ i, ell i≤0)
    (x : X) : basisProfile ell x≤0 := by
  obtain ⟨G, hG, hxG, _⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open
    (mem_univ x) isOpen_univ
  exact (basisProfile_le ell ⟨G,hG⟩ hxG).trans (hell _)

theorem extract_basis_rates [MeasurableSpace X]
    (μ : ℕ → Measure X) (S : ℕ → ℝ) :
    ∃ (ell : countableBasis X → EReal) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ i : countableBasis X,
        Tendsto (fun j => logRate (S (φ j)) (μ (φ j) i.val)) atTop (𝓝 (ell i)) := by
  let z : ℕ → (countableBasis X → EReal) := fun j i => logRate (S j) (μ j i.val)
  obtain ⟨ell, φ, hφ, hz⟩ := CompactSpace.tendsto_subseq z
  refine ⟨ell, φ, hφ, fun i => ?_⟩
  exact (continuous_apply i).tendsto ell |>.comp hz

lemma basis_rates_nonpos [MeasurableSpace X] {μ : ℕ → Measure X} {S : ℕ → ℝ}
    {ell : countableBasis X → EReal} {φ : ℕ → ℕ}
    (hS : ∀ j, 0<S j) (hnorm : ∀ j, μ j univ≤1)
    (hlim : ∀ i : countableBasis X,
      Tendsto (fun j => logRate (S (φ j)) (μ (φ j) i.val)) atTop (𝓝 (ell i))) :
    ∀ i, ell i≤0 := by
  intro i
  apply le_of_tendsto (hlim i)
  filter_upwards [] with j
  change logRate (S (φ j)) (μ (φ j) i.val) ≤ (0 : ℝ)
  apply (logRate_le_iff (hS _) _).mpr
  simpa using (measure_mono (subset_univ i.val)).trans (hnorm (φ j))

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma upper_test_of_maximum {V : Plane → EReal} {q : Plane → ℝ} {F : Set Plane}
    {x₀ : Plane} (hx₀ : x₀∈interior F) (hfinite : V x₀≠⊤ ∧ V x₀≠⊥)
    (hmax : IsMaxOn (fun x => V x+((-q x:ℝ):EReal)) F x₀) :
    IsUpperTest V (fun x => q x+(V x₀).toReal-q x₀) x₀ := by
  have hv := EReal.coe_toReal hfinite.1 hfinite.2
  refine ⟨?_, ?_⟩
  · simp only [add_sub_cancel_left, hv]
  · filter_upwards [mem_interior_iff_mem_nhds.mp hx₀] with x hx
    apply (EReal.addLECancellable_coe (-q x)).add_le_add_iff_right.mp
    have hh : V x+((-q x:ℝ):EReal) ≤ V x₀+((-q x₀:ℝ):EReal) := hmax hx
    rw [← hv, ← EReal.coe_add] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [← EReal.coe_add]
    congr 1
    ring

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
namespace SharpNodal.Profiles

lemma ereal_add_coe_lt_coe_iff {v : EReal} {a b : ℝ} :
    v+(a:EReal)<(b:EReal) ↔ v<((b-a:ℝ):EReal) := by
  have heq : ((b-a:ℝ):EReal)+(a:EReal)=(b:EReal) := by
    rw [← EReal.coe_add]; congr 1; ring
  constructor
  · intro h
    by_contra hn
    have hh := add_le_add (le_of_not_gt hn) (le_refl (a:EReal))
    rw [heq] at hh
    exact (not_le_of_gt h) hh
  · intro h
    simpa only [heq] using EReal.add_lt_add_right_coe h a

lemma ereal_coe_lt_add_coe_iff {v : EReal} {a b : ℝ} :
    (b:EReal)<v+(a:EReal) ↔ ((b-a:ℝ):EReal)<v := by
  have heq : ((b-a:ℝ):EReal)+(a:EReal)=(b:EReal) := by
    rw [← EReal.coe_add]; congr 1; ring
  constructor
  · intro h
    by_contra hn
    have hh := add_le_add (le_of_not_gt hn) (le_refl (a:EReal))
    rw [heq] at hh
    exact (not_le_of_gt h) hh
  · intro h
    simpa only [heq] using EReal.add_lt_add_right_coe h a

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

omit [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X] in
lemma weightedMass_mono_set (μ : Measure X) (S : ℝ) (f : X → ℝ)
    {E F : Set X} (hEF : E⊆F) : weightedMass μ S f E≤weightedMass μ S f F :=
  lintegral_mono' (Measure.restrict_mono hEF le_rfl) le_rfl

omit [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X] in
lemma weightedMass_upper (μ : Measure X) {S c : ℝ} (hS : 0≤S) (f : X → ℝ)
    {E : Set X} (hf : ∀ x∈E, f x ≤ c) :
    weightedMass μ S f E≤ENNReal.ofReal (Real.exp (2*S*c))*μ E := by
  have hh := setLIntegral_mono (μ:=μ) (f:=fun x => ENNReal.ofReal (Real.exp (2*S*f x)))
    (g:=fun _ => ENNReal.ofReal (Real.exp (2*S*c))) measurable_const
    (fun x hx => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hf x hx) (by positivity))))
  simpa only [weightedMass, lintegral_const, Measure.restrict_apply_univ] using hh

omit [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X] in
lemma weightedMass_lower (μ : Measure X) {S c : ℝ} (hS : 0≤S) (f : X → ℝ)
    {E : Set X} (hE : MeasurableSet E) (hf : ∀ x∈E, c≤f x) :
    ENNReal.ofReal (Real.exp (2*S*c))*μ E≤weightedMass μ S f E := by
  have hh := setLIntegral_mono' (μ:=μ) hE (f:=fun _ => ENNReal.ofReal (Real.exp (2*S*c)))
    (g:=fun x => ENNReal.ofReal (Real.exp (2*S*f x))) (fun x hx =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hf x hx) (by positivity))))
  simpa only [weightedMass, lintegral_const, Measure.restrict_apply_univ] using hh

omit [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X] in
lemma weightedMass_biUnion_le (μ : Measure X) (S : ℝ) (f : X → ℝ)
    {I : Type*} (t : Finset I) (E : I → Set X) :
    weightedMass μ S f (⋃ i∈t, E i)≤∑ i∈t, weightedMass μ S f (E i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [weightedMass]
  | @insert i t hi ih =>
    simpa only [weightedMass, Finset.mem_insert, iUnion_iUnion_eq_or_left, Finset.sum_insert hi]
      using (lintegral_union_le (μ:=μ) (fun x => ENNReal.ofReal (Real.exp (2*S*f x)))
        (E i) (⋃ j∈t, E j)).trans (add_le_add le_rfl ih)

omit [OpensMeasurableSpace X] in
lemma basis_rates_mono {μ : ℕ → Measure X} {S : ℕ → ℝ}
    {ell : countableBasis X → EReal} (hS : ∀ j, 0<S j)
    (hlim : ∀ i : countableBasis X,
      Tendsto (fun j => logRate (S j) (μ j i.val)) atTop (𝓝 (ell i)))
    {i k : countableBasis X} (hik : i.val⊆k.val) : ell i≤ell k :=
  le_of_tendsto_of_tendsto (hlim i) (hlim k)
    (Eventually.of_forall fun j => logRate_mono (hS j) (measure_mono hik))

omit [OpensMeasurableSpace X] in

theorem weighted_compact_profile_upper {μ : ℕ → Measure X} {S : ℕ → ℝ}
    {ell : countableBasis X → EReal} {Ω : Set X} (hΩ : IsOpen Ω)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hlim : ∀ i : countableBasis X,
      Tendsto (fun j => logRate (S j) (μ j i.val)) atTop (𝓝 (ell i)))
    {f : X → ℝ} (hf : ContinuousOn f Ω) {F : Set X} (hF : IsCompact F) (hFΩ : F⊆Ω) :
    limsup (fun j => logRate (S j) (weightedMass (μ j) (S j) f F)) atTop≤
      ⨆ x∈F, basisProfile ell x+(f x:EReal) := by
  classical
  by_contra hn
  obtain ⟨b,hVb,hbL⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  obtain ⟨a,hVa,hab⟩ := EReal.lt_iff_exists_real_btwn.mp hVb
  have hab' : a<b := by exact_mod_cast hab
  let I := {p : countableBasis X × ℝ // ell p.1<((a-p.2:ℝ):EReal) ∧
    ∀ y∈p.1.val, f y≤p.2}
  let U : I → Set X := fun p => p.val.1.val
  have hcover : F⊆⋃ p, U p := by
    intro x hx
    have hxa : basisProfile ell x+(f x:EReal)<(a:EReal) :=
      (le_iSup₂_of_le x hx le_rfl).trans_lt hVa
    obtain ⟨z,hVz,hzf⟩ := EReal.lt_iff_exists_real_btwn.mp (ereal_add_coe_lt_coe_iff.mp hxa)
    have hfz : f x<a-z := by
      have : z<a-f x := by exact_mod_cast hzf
      linarith
    obtain ⟨i,hxi,hiz⟩ := (basisProfile_lt_iff ell x z).mp hVz
    have hevent : ∀ᶠ y in 𝓝 x, y∈i.val ∧ f y<a-z :=
      Filter.Eventually.and ((isOpen_of_mem_countableBasis i.property).mem_nhds hxi)
        ((hf.continuousAt (hΩ.mem_nhds (hFΩ hx))).eventually (gt_mem_nhds hfz))
    obtain ⟨J,hJ,hxJ,hsub⟩ := (isBasis_countableBasis X).mem_nhds_iff.mp hevent
    let k : countableBasis X := ⟨J,hJ⟩
    have hkz : ell k<((a-(a-z):ℝ):EReal) := by
      rw [show a-(a-z)=z by ring]
      exact (basis_rates_mono hSpos hlim (fun y hy => (hsub hy).1)).trans_lt hiz
    let p : I := ⟨(k,a-z),hkz,fun y hy => (hsub hy).2.le⟩
    exact mem_iUnion.mpr ⟨p,hxJ⟩
  obtain ⟨t,ht⟩ := hF.elim_finite_subcover U
    (fun p => isOpen_of_mem_countableBasis p.val.1.property) hcover
  have hterms : ∀ᶠ j in atTop, ∀ p∈t,
      weightedMass (μ j) (S j) f (U p)≤ENNReal.ofReal (Real.exp (2*S j*a)) := by
    apply (eventually_all_finset t).mpr
    intro p hp
    filter_upwards [(hlim p.val.1).eventually (gt_mem_nhds p.property.1)] with j hj
    have hr := (weightedMass_upper (μ j) (hSpos j).le f p.property.2).trans
      (mul_le_mul' le_rfl ((logRate_lt_iff (hSpos j) _).mp hj).le)
    convert! hr using 1
    all_goals try with_reducible_and_instances rfl
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hc : 0<(t.card:ℝ)+1 := by positivity
  have hgap := exponential_gap hS hab' hc
  have hbound : ∀ᶠ j in atTop,
      logRate (S j) (weightedMass (μ j) (S j) f F)≤(b:EReal) := by
    filter_upwards [hterms,hgap] with j hj hg
    apply (logRate_le_iff (hSpos j) _).mpr
    apply ((weightedMass_mono_set _ _ _ ht).trans (weightedMass_biUnion_le _ _ _ t U)).trans
    calc (∑ p∈t, weightedMass (μ j) (S j) f (U p))
        ≤ ∑ _p∈t, ENNReal.ofReal (Real.exp (2*S j*a)) := Finset.sum_le_sum fun p hp => hj p hp
      _ = (t.card:ℝ≥0∞)*ENNReal.ofReal (Real.exp (2*S j*a)) := by simp
      _ ≤ ENNReal.ofReal ((t.card:ℝ)+1)*ENNReal.ofReal (Real.exp (2*S j*a)) := by
        gcongr
        exact_mod_cast (le_add_of_nonneg_right (show (0:ℝ)≤1 by norm_num) : (t.card:ℝ)≤(t.card:ℝ)+1)
      _ = ENNReal.ofReal (((t.card:ℝ)+1)*Real.exp (2*S j*a)) := (ENNReal.ofReal_mul hc.le).symm
      _ ≤ ENNReal.ofReal (Real.exp (2*S j*b)) := ENNReal.ofReal_le_ofReal hg.le
  exact (not_le_of_gt hbL) (limsup_le_of_le (by isBoundedDefault) hbound)

theorem weighted_open_profile_lower {μ : ℕ → Measure X} {S : ℕ → ℝ}
    {ell : countableBasis X → EReal} {Ω : Set X} (hΩ : IsOpen Ω)
    (hSpos : ∀ j, 0<S j)
    (hlim : ∀ i : countableBasis X,
      Tendsto (fun j => logRate (S j) (μ j i.val)) atTop (𝓝 (ell i)))
    {f : X → ℝ} (hf : ContinuousOn f Ω) {G : Set X} (hG : IsOpen G) (hGΩ : G⊆Ω) :
    (⨆ x∈G, basisProfile ell x+(f x:EReal))≤
      liminf (fun j => logRate (S j) (weightedMass (μ j) (S j) f G)) atTop := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  by_contra hn
  obtain ⟨b,hLb,hbV⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  obtain ⟨z,hbz,hzV⟩ := EReal.lt_iff_exists_real_btwn.mp (ereal_coe_lt_add_coe_iff.mp hbV)
  have hcz : b-z<f x := by
    have : b-f x<z := by exact_mod_cast hbz
    linarith
  have hevent : ∀ᶠ y in 𝓝 x, y∈G ∧ b-z<f y :=
    Filter.Eventually.and (hG.mem_nhds hx) ((hf.continuousAt (hΩ.mem_nhds (hGΩ hx))).eventually (lt_mem_nhds hcz))
  obtain ⟨J,hJ,hxJ,hsub⟩ := (isBasis_countableBasis X).mem_nhds_iff.mp hevent
  let i : countableBasis X := ⟨J,hJ⟩
  have hzi : (z:EReal)<ell i := hzV.trans_le (basisProfile_le ell i hxJ)
  have hbound : ∀ᶠ j in atTop, (b:EReal)≤logRate (S j) (weightedMass (μ j) (S j) f G) := by
    filter_upwards [(hlim i).eventually (lt_mem_nhds hzi)] with j hj
    apply (le_logRate_iff (hSpos j) _).mpr
    have hl := weightedMass_lower (μ j) (hSpos j).le f
      (isOpen_of_mem_countableBasis hJ).measurableSet (fun y hy => (hsub hy).2.le)
    have hm := (mul_le_mul' le_rfl ((lt_logRate_iff (hSpos j) _).mp hj).le).trans hl
    have hh := hm.trans (weightedMass_mono_set _ _ _ (fun y hy => (hsub hy).1))
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  exact (not_le_of_gt hLb) (le_liminf_of_le (by isBoundedDefault) hbound)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
namespace SharpNodal.Profiles
open Carleman

lemma continuousOn_tiltedDensity {Ω : Set Plane} {U : Plane → ℝ}
    (hU : ContinuousOn U Ω) (B : Plane) (c : ℝ) :
    ContinuousOn (tiltedDensity B U c) Ω := by
  apply ENNReal.continuous_ofReal.comp_continuousOn
  exact continuousOn_const.mul (((Real.continuous_exp.comp (innerSL ℝ B).continuous.neg).continuousOn.mul hU).pow 2)

lemma tiltedDensity_weight (S : ℝ) (B : Plane) (U f : Plane → ℝ) (c : ℝ) (x : Plane) :
    tiltedDensity B U c x*ENNReal.ofReal (Real.exp (2*S*f x)) =
      ENNReal.ofReal (c*(Real.exp (tiltedWeight B S (fun y => -f y) x)*U x)^2) := by
  unfold tiltedDensity
  rw [← ENNReal.ofReal_mul' (Real.exp_pos _).le]
  congr 1
  unfold tiltedWeight
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  calc c*(Real.exp (2*(-inner ℝ B x))*U x^2)*Real.exp (2*S*f x)
      = c*(Real.exp (2*(-inner ℝ B x))*Real.exp (2*S*f x))*U x^2 := by ring
    _ = _ := by
      rw [← Real.exp_add, show 2*(-inner ℝ B x)+2*S*f x=2*(-inner ℝ B x-S*(-f x)) by ring]
      ring

lemma weightedMass_tiltedMeasure {Ω E : Set Plane}
    (hE : MeasurableSet E) (hEΩ : E⊆Ω) {U : Plane → ℝ} (hU : ContinuousOn U Ω)
    (S : ℝ) (B : Plane) (c : ℝ) (f : Plane → ℝ) :
    weightedMass (tiltedMeasure Ω B U c) S f E=tiltedMass S B U c f E := by
  unfold weightedMass tiltedMeasure
  rw [restrict_withDensity hE, Measure.restrict_restrict_of_subset hEΩ]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
    ((continuousOn_tiltedDensity hU B c).mono hEΩ |>.aemeasurable hE)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) ]
  exact lintegral_congr fun x => tiltedDensity_weight S B U f c x

theorem extract_tilted_profile {Ω : Set Plane} (hΩ : IsOpen Ω)
    (S : ℕ → ℝ) (B : ℕ → Plane) (U : ℕ → Plane → ℝ) (c : ℕ → ℝ)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop)
    (hU : ∀ j, ContinuousOn (U j) Ω)
    (hnorm : ∀ j, tiltedMass (S j) (B j) (U j) (c j) 0 Ω≤1) :
    ∃ (V : Plane → EReal) (φ : ℕ → ℕ), StrictMono φ ∧ UpperSemicontinuous V ∧
      (∀ x, V x≤0) ∧
      WeightedProfileBounds Ω (S∘φ) (B∘φ) (U∘φ) (c∘φ) V := by
  let μ := fun j => tiltedMeasure Ω (B j) (U j) (c j)
  obtain ⟨ell,φ,hφ,hlim⟩ := extract_basis_rates μ S
  refine ⟨basisProfile ell,φ,hφ,upperSemicontinuous_basisProfile ell,?_,?_⟩
  · apply basisProfile_nonpos
    apply basis_rates_nonpos hSpos _ hlim
    intro j
    have heq : μ j univ=tiltedMass (S j) (B j) (U j) (c j) 0 Ω := by
      simp only [μ,tiltedMeasure,withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ]
      apply lintegral_congr
      intro x
      simp [tiltedDensity,tiltedWeight]
    rw [heq]
    exact hnorm j
  · constructor
    · intro f hf F hF hFΩ
      have heq (j : ℕ) := weightedMass_tiltedMeasure hF.measurableSet hFΩ
        (hU (φ j)) (S (φ j)) (B (φ j)) (c (φ j)) f
      simpa only [Function.comp_apply,← heq] using
        weighted_compact_profile_upper hΩ (fun j => hSpos (φ j))
          (hS.comp hφ.tendsto_atTop) hlim hf hF hFΩ
    · intro f hf G hG hGΩ
      have heq (j : ℕ) := weightedMass_tiltedMeasure hG.measurableSet hGΩ
        (hU (φ j)) (S (φ j)) (B (φ j)) (c (φ j)) f
      simpa only [Function.comp_apply,← heq] using
        weighted_open_profile_lower hΩ (fun j => hSpos (φ j)) hlim hf hG hGΩ
end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Subharmonic
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

lemma full_test_local {Ω O : Set Plane} {V : Plane → EReal} {f : Plane → ℝ} {x₀ : Plane}
    (htest : FullTestProperty Ω V) (hO : IsOpen O) (hxO : x₀∈O) (hxΩ : x₀∈Ω)
    (hf : ContDiffOn ℝ ∞ f O) (ht : IsUpperTest V f x₀) :
    0≤euclideanLaplacian f x₀ := by
  obtain ⟨g,r,hg,hr,_,heq⟩ := smooth_extension_near hO hxO hf
  have hevent : g =ᶠ[𝓝 x₀] f := Filter.Eventually.mono (Metric.ball_mem_nhds x₀ hr) fun _ hx => heq _ hx
  have htg : IsUpperTest V g x₀ := by
    constructor
    · rw [hevent.eq_of_nhds]; exact ht.1
    · filter_upwards [ht.2,hevent] with x hx he
      rwa [he]
  have hh := htest g hg x₀ hxΩ htg
  rwa [(laplacian_eventuallyEq hevent).eq_of_nhds] at hh

lemma laplacian_add_local {O : Set Plane} {f g : Plane → ℝ} {x : Plane}
    (hO : IsOpen O) (hx : x∈O) (hf : ContDiffOn ℝ ∞ f O) (hg : Smooth g) :
    euclideanLaplacian (fun y => f y+g y) x=euclideanLaplacian f x+euclideanLaplacian g x := by
  obtain ⟨f',r,hf',hr,_,heq⟩ := smooth_extension_near hO hx hf
  have hevent : f'=ᶠ[𝓝 x] f := Filter.Eventually.mono (Metric.ball_mem_nhds x hr) fun _ hz => heq _ hz
  have hevent' : (fun y => f' y+g y)=ᶠ[𝓝 x] (fun y => f y+g y) := by
    filter_upwards [hevent] with y hy; rw [hy]
  rw [← (laplacian_eventuallyEq hevent').eq_of_nhds,laplacian_add hf' hg,
    (laplacian_eventuallyEq hevent).eq_of_nhds]

lemma laplacian_radiusSquare (x₀ x : Plane) : euclideanLaplacian (radiusSquare x₀) x=4 := by
  have heq : radiusSquare x₀=centeredQuadratic ((2:ℝ) • innerForm) x₀ := by
    ext y
    simpa only [radiusSquare,mul_one,one_mul] using (centeredQuadratic_inner_smul 1 x₀ y).symm
  have hs : SymmetricForm ((2:ℝ) • innerForm) := by
    intro y z
    simp only [smul_apply,smul_eq_mul,symmetric_innerForm y z]
  rw [heq,laplacian_centeredQuadratic hs]
  change formTrace ((2:ℝ) • innerForm)=4
  rw [formTrace_smul,formTrace_innerForm]
  norm_num

lemma laplacian_quadraticBarrier (a : Plane) (r ε m : ℝ) (x : Plane) :
    euclideanLaplacian (fun y => ε*(r^2-radiusSquare a y)+m) x= -4*ε := by
  have heq : (fun y => ε*(r^2-radiusSquare a y)+m)=
      (fun y => (ε*r^2+m)+(-ε)*radiusSquare a y) := by ext y; ring
  rw [heq,laplacian_add contDiff_const (contDiff_const.mul (smooth_radiusSquare a)),
    laplacian_const,laplacian_const_mul (smooth_radiusSquare a)]
  dsimp only
  rw [laplacian_radiusSquare]
  ring

theorem harmonic_comparison_of_full_test {Ω : Set Plane} {V : Plane → EReal}
    {h : Plane → ℝ} {a : Plane} {r : ℝ}
    (hV : UpperSemicontinuousOn V Ω) (htop : ∀ x∈Ω, V x≠⊤)
    (htest : FullTestProperty Ω V) (hr : 0 < r) (hball : Metric.closedBall a r⊆Ω)
    (hh : ContDiffOn ℝ ∞ h (Metric.ball a r))
    (hc : ContinuousOn h (Metric.closedBall a r))
    (hΔ : ∀ x∈Metric.ball a r, euclideanLaplacian h x=0)
    (hbdry : ∀ x∈Metric.sphere a r, V x≤(h x:EReal)) :
    ∀ x∈Metric.closedBall a r, V x≤(h x:EReal) := by
  intro x hx
  by_contra hn
  have hgap : (0:EReal)<V x+((-h x:ℝ):EReal) := by
    have hhx := EReal.add_lt_add_right_coe (lt_of_not_ge hn) (-h x)
    simpa only [← EReal.coe_add,add_neg_cancel,EReal.coe_zero] using hhx
  obtain ⟨δ,hδ0,hδgap⟩ := EReal.lt_iff_exists_real_btwn.mp hgap
  have hδ : 0<δ := by exact_mod_cast hδ0
  let ε := δ/(r^2+1)
  have hε : 0<ε := div_pos hδ (by positivity)
  have hεmul : ε*(r^2+1)=δ := by dsimp [ε];field_simp
  let q : Plane → ℝ := fun y => h y+ε*(r^2-radiusSquare a y)
  have hbar : Smooth (fun y => ε*(r^2-radiusSquare a y)) :=
    contDiff_const.mul (contDiff_const.sub (smooth_radiusSquare a))
  have hq : ContinuousOn q (Metric.closedBall a r) := hc.add hbar.continuous.continuousOn
  have hqvalue : (0:EReal)<V x+((-q x:ℝ):EReal) := by
    have hle : ε*(r^2-radiusSquare a x)≤δ := by
      rw [← hεmul]
      apply mul_le_mul_of_nonneg_left _ hε.le
      have := sq_nonneg ‖x-a‖
      dsimp [radiusSquare]
      linarith
    have hhx := EReal.add_lt_add_right_coe hδgap (h x)
    have hlower : ((δ+h x:ℝ):EReal)<V x := by
      simpa only [← EReal.coe_add,add_assoc,neg_add_cancel,EReal.coe_zero,add_zero] using hhx
    have hqle : (q x:EReal)≤((δ+h x:ℝ):EReal) := by
      apply EReal.coe_le_coe_iff.mpr
      dsimp [q]; linarith
    have hhq := EReal.add_lt_add_right_coe (hqle.trans_lt hlower) (-q x)
    simpa only [← EReal.coe_add,add_neg_cancel,EReal.coe_zero] using hhq
  obtain ⟨y,hy,hmax⟩ := (upperSemicontinuousOn_add_real (hV.mono hball) hq.neg).exists_isMaxOn
    ⟨a,Metric.mem_closedBall_self hr.le⟩ (isCompact_closedBall a r)
  have hpos : (0:EReal)<V y+((-q y:ℝ):EReal) := hqvalue.trans_le (hmax hx)
  have hyint : y∈Metric.ball a r := by
    apply Metric.mem_ball.mpr
    apply lt_of_le_of_ne (Metric.mem_closedBall.mp hy)
    intro he
    have hybd : y∈Metric.sphere a r := Metric.mem_sphere.mpr he
    have hqbd : q y=h y := by
      have hdist : ‖y-a‖=r := by simpa only [Metric.mem_sphere,dist_eq_norm] using hybd
      simp only [q,radiusSquare,hdist,sub_self,mul_zero,add_zero]
    have hb := add_le_add (hbdry y hybd) (le_refl ((-q y:ℝ):EReal))
    rw [hqbd,← EReal.coe_add,add_neg_cancel,EReal.coe_zero] at hb
    apply (not_le_of_gt hpos)
    simpa only [hqbd] using hb
  have hfinite : V y≠⊤ ∧ V y≠⊥ := by
    refine ⟨htop y (hball hy),?_⟩
    intro he
    rw [he,EReal.bot_add] at hpos
    exact (not_lt_of_ge bot_le) hpos
  let m := (V y).toReal-q y
  have ht := upper_test_of_maximum (Metric.ball_subset_interior_closedBall hyint) hfinite hmax
  have ht' : IsUpperTest V (fun z => h z+(ε*(r^2-radiusSquare a z)+m)) y := by
    convert! ht using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    dsimp [q,m]
    ring
  have hs := full_test_local htest Metric.isOpen_ball hyint (hball hy)
    (hh.add (hbar.add contDiff_const).contDiffOn) ht'
  rw [laplacian_add_local Metric.isOpen_ball hyint hh (hbar.add contDiff_const),
    hΔ y hyint,laplacian_quadraticBarrier,zero_add] at hs
  linarith
end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

lemma plane_laplacian_eq_mathlib {f : Plane → ℝ} (hf : Smooth f) :
    euclideanLaplacian f = Δ f := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 2) ℝ)]
  ext x
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.basisFun_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  exact (hessian_on_basis hf x i i).symm

lemma laplacian_comp_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {f : F → ℝ} (hf : ContDiff ℝ ∞ f) :
    Δ (f∘e) = (Δ f)∘e := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f∘e) b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map e)]
  ext x
  apply Finset.sum_congr rfl
  intro i _
  have hh := e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right
    hf x (i:=2) (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))
  rw [show (f∘e)=(f∘e.toContinuousLinearEquiv.toContinuousLinearMap) from rfl,hh]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  congr 1
  ext k
  fin_cases k <;> rfl

lemma plane_laplacian_comp_complex {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (x : Plane) :
    euclideanLaplacian (f∘planeComplex) x = (Δ f) (planeComplex x) := by
  have hf' : Smooth (f∘planeComplex) := by
    convert! hf.comp planeComplex.toContinuousLinearEquiv.contDiff using 1
    all_goals try with_reducible_and_instances rfl
  rw [plane_laplacian_eq_mathlib hf', laplacian_comp_isometry planeComplex hf]
  rfl

lemma compare_complex_harmonic {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (htop : ∀ x∈Ω, V x≠⊤)
    (htest : FullTestProperty Ω V) {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hΔ : ∀ z, (Δ f) z=0) {a : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r⊆Ω)
    (hbdry : ∀ x∈Metric.sphere a r, V x≤(f (planeComplex x):EReal)) :
    ∀ x∈Metric.closedBall a r, V x≤(f (planeComplex x):EReal) := by
  apply harmonic_comparison_of_full_test hV htop htest hr hball
    (hf.comp planeComplex.toContinuousLinearEquiv.contDiff).contDiffOn
    (hf.continuous.comp planeComplex.continuous).continuousOn _ hbdry
  intro x _
  exact (plane_laplacian_comp_complex hf x).trans (hΔ _)
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

lemma harmonic_extension_fourier_span {c : ℂ} {r : ℝ} (hr : r ≠ 0)
    {f : C(AddCircle (1:ℝ),ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (@fourier (1:ℝ)))) :
    ∃ P : ℂ → ℂ, ContDiff ℝ ∞ P ∧ HarmonicOnNhd P univ ∧
      ∀ t : AddCircle (1:ℝ), P (c+(r:ℂ)*AddCircle.toCircle t)=f t := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨n,rfl⟩ := hf
      have hbase (n : ℕ) : ∃ P : ℂ → ℂ, ContDiff ℝ ∞ P ∧ HarmonicOnNhd P univ ∧
          ∀ t : AddCircle (1:ℝ), P (c+(r:ℂ)*AddCircle.toCircle t)=fourier (n:ℤ) t := by
        refine ⟨fun z => ((z-c)/(r:ℂ))^n, ?_, ?_, ?_⟩
        · fun_prop
        · intro z _
          apply AnalyticAt.harmonicAt
          fun_prop
        · intro t
          simp only [add_sub_cancel_left, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr),
            fourier_apply, natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow]
      cases n with
      | ofNat n => exact hbase n
      | negSucc n =>
          obtain ⟨P,hP,hH,hf⟩ := hbase (n+1)
          refine ⟨fun z => conj (P z), ?_, ?_, ?_⟩
          · exact Complex.conjCLE.contDiff.comp hP
          · exact hH.comp_CLM Complex.conjCLE.toContinuousLinearMap
          · intro t
            change conj (P _) = fourier (-(↑(n+1):ℤ)) t
            rw [hf,fourier_neg]
  | zero =>
      exact ⟨0,contDiff_const,fun _ _ => harmonicAt_const 0,fun _ => rfl⟩
  | add f g hf hg ihf ihg =>
      obtain ⟨P,hP,hH,hf⟩ := ihf
      obtain ⟨Q,hQ,hJ,hg⟩ := ihg
      exact ⟨P+Q,hP.add hQ,hH.add hJ,fun t => by simpa only [Pi.add_apply,ContinuousMap.add_apply] using congrArg₂ (·+·) (hf t) (hg t)⟩
  | smul a f hf ih =>
      obtain ⟨P,hP,hH,hf⟩ := ih
      exact ⟨a • P,hP.const_smul a,hH.comp_CLM (ContinuousLinearMap.mul ℝ ℂ a),fun t => by simpa only [Pi.smul_apply,ContinuousMap.smul_apply] using congrArg (a • ·) (hf t)⟩

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

lemma exists_circle_param {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z∈Metric.sphere c r) :
    ∃ t : AddCircle (1:ℝ), z=c+(r:ℂ)*AddCircle.toCircle t := by
  have hnorm : ‖(z-c)/(r:ℂ)‖=1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    rw [← dist_eq_norm,Metric.mem_sphere.mp hz,div_self hr.ne']
  let w : Circle := ⟨(z-c)/(r:ℂ),mem_sphere_zero_iff_norm.mpr hnorm⟩
  obtain ⟨t,ht⟩ := (AddCircle.homeomorphCircle (T:=(1:ℝ)) one_ne_zero).surjective w
  refine ⟨t,?_⟩
  have ht' : (AddCircle.toCircle t : ℂ)=(z-c)/(r:ℂ) := by
    simpa only [AddCircle.homeomorphCircle_apply] using congrArg (fun z : Circle => (z:ℂ)) ht
  rw [ht',mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
  exact (add_sub_cancel c z).symm

lemma approximate_circle_by_harmonic {c : ℂ} {r ε : ℝ} (hr : 0 < r) (hε : 0<ε)
    {g : ℂ → ℝ} (hg : Continuous g) :
    ∃ P : ℂ → ℝ, ContDiff ℝ ∞ P ∧ HarmonicOnNhd P univ ∧
      ∀ z∈Metric.sphere c r, |P z-g z|<ε := by
  let f : C(AddCircle (1:ℝ),ℂ) := ⟨fun t => (g (c+(r:ℂ)*AddCircle.toCircle t):ℂ),by fun_prop⟩
  have hcl : f ∈ closure (Submodule.span ℂ (Set.range (@fourier (1:ℝ))) : Set C(AddCircle (1:ℝ),ℂ)) := by
    change f ∈ (Submodule.span ℂ (Set.range (@fourier (1:ℝ)))).topologicalClosure
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨q,hq,hfq⟩ := Metric.mem_closure_iff.mp hcl ε hε
  obtain ⟨P,hP,hH,hbdry⟩ := harmonic_extension_fourier_span (c:=c) hr.ne' hq
  refine ⟨fun z => (P z).re, Complex.reCLM.contDiff.comp hP,hH.comp_CLM Complex.reCLM,?_⟩
  intro z hz
  obtain ⟨t,rfl⟩ := exists_circle_param hr hz
  change |(P (c+(r:ℂ)*AddCircle.toCircle t)).re-g (c+(r:ℂ)*AddCircle.toCircle t)|<ε
  rw [hbdry]
  have hqt := (ContinuousMap.dist_apply_le_dist (f:=f) (g:=q) t).trans_lt hfq
  have h := (Complex.abs_re_le_norm (q t-f t)).trans_lt (by
    simpa only [dist_eq_norm,norm_sub_rev] using hqt)
  simpa only [Complex.sub_re,ContinuousMap.coe_mk, f,Complex.ofReal_re] using h

theorem submean_continuous_majorant {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (htop : ∀x∈Ω,V x≠⊤)
    (htest : FullTestProperty Ω V) {a : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r⊆Ω) {g : ℂ → ℝ} (hg : Continuous g)
    (hbdry : ∀ x∈Metric.sphere a r,V x≤(g (planeComplex x):EReal)) :
    V a≤((Real.circleAverage g (planeComplex a) r:ℝ):EReal) := by
  have ha : a∈Metric.closedBall a r := Metric.mem_closedBall_self hr.le
  by_cases hbot : V a=⊥
  · simp [hbot]
  have hcoe := EReal.coe_toReal (htop a (hball ha)) hbot
  rw [← hcoe,EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨P,hP,hH,happrox⟩ := approximate_circle_by_harmonic (c:=planeComplex a) hr (half_pos hε) hg
  let H : ℂ → ℝ := fun z => P z+ε/2
  have hHs : ContDiff ℝ ∞ H := hP.add contDiff_const
  have hHh : HarmonicOnNhd H univ := hH.add (fun _ _ => harmonicAt_const (ε/2))
  have hle : V a≤(H (planeComplex a):EReal) := by
    apply compare_complex_harmonic hV htop htest hHs (fun z => (hHh z (mem_univ _)).2.self_of_nhds) hr hball _ a ha
    intro x hx
    have hx' : planeComplex x∈Metric.sphere (planeComplex a) r := by
      simpa only [Metric.mem_sphere,planeComplex.isometry.dist_eq] using hx
    apply (hbdry x hx).trans
    apply EReal.coe_le_coe_iff.mpr
    exact le_of_lt (by have := (abs_lt.mp (happrox _ hx')).1; dsimp [H]; linarith)
  have hmean : H (planeComplex a)≤Real.circleAverage g (planeComplex a) r+ε := by
    rw [← hHh.mono (subset_univ _) |>.circleAverage_eq]
    have hcomp := Real.circleAverage_mono (c:=planeComplex a) (R:=r) hHs.continuous.continuousOn.circleIntegrable'
      (hg.add continuous_const).continuousOn.circleIntegrable' (f₂:=fun z => g z+ε) ?_
    · simpa only [show (fun z => g z+ε)=g+(fun _ => ε) from rfl,
        Real.circleAverage_add hg.continuousOn.circleIntegrable' continuous_const.continuousOn.circleIntegrable',
        Real.circleAverage_const] using hcomp
    · intro z hz
      have := (abs_lt.mp (happrox z (by simpa [abs_of_pos hr] using hz))).2
      dsimp [H]
      linarith
  exact (EReal.coe_le_coe_iff.mp (hcoe ▸ hle)).trans hmean
end SharpNodal.Profiles

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Regularization
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory

namespace SharpNodal.Profiles

variable {X : Type*} [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
lemma coe_truncBelow {V : X → EReal} {n : ℕ} {x : X} (hx : V x≤0) :
    (truncBelow V n x:EReal)=max (V x) ((-(n:ℝ):ℝ):EReal) := by
  apply EReal.coe_toReal
  · apply ne_of_lt
    exact max_lt (hx.trans_lt (by simp)) (EReal.coe_lt_top _)
  · exact ne_of_gt ((EReal.bot_lt_coe (-(n:ℝ))).trans_le (le_max_right _ _))

omit [PseudoMetricSpace X] in
lemma truncBelow_nonpos {V : X → EReal} {n : ℕ} {x : X} (hx : V x≤0) :
    truncBelow V n x≤0 := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncBelow hx]
  exact max_le hx (by exact_mod_cast (neg_nonpos.mpr (Nat.cast_nonneg n):-(n:ℝ)≤0))

omit [PseudoMetricSpace X] in
lemma truncBelow_antitone {V : X → EReal} {x : X} (hx : V x≤0) :
    Antitone (fun n => truncBelow V n x) := by
  intro m n hmn
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncBelow hx,coe_truncBelow hx]
  exact max_le_max_left _ (EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hmn)))

lemma regularize_bdd {K : Set X} {V : X → EReal} (hV : ∀x∈K,V x≤0) (n : ℕ) (x : X) :
    BddAbove (Set.range fun y : K => truncBelow V n y-(n:ℝ)*dist x y) := by
  refine ⟨0,?_⟩
  rintro _ ⟨y,rfl⟩
  exact sub_nonpos.mpr ((truncBelow_nonpos (hV y y.2)).trans (mul_nonneg (Nat.cast_nonneg n) dist_nonneg))

lemma supRegularize_nonpos {K : Set X} {V : X → EReal} (hK : K.Nonempty)
    (hV : ∀x∈K,V x≤0) (n : ℕ) (x : X) : supRegularize K V n x≤0 := by
  let : Nonempty K := hK.to_subtype
  exact ciSup_le (fun y => sub_nonpos.mpr ((truncBelow_nonpos (hV y y.2)).trans
    (mul_nonneg (Nat.cast_nonneg n) dist_nonneg)))

lemma supRegularize_majorant {K : Set X} {V : X → EReal}
    (hV : ∀x∈K,V x≤0) (n : ℕ) {x : X} (hx : x∈K) : V x≤(supRegularize K V n x:EReal) := by
  apply (le_max_left (V x) ((-(n:ℝ):ℝ):EReal)).trans
  rw [← coe_truncBelow (hV x hx)]
  apply EReal.coe_le_coe_iff.mpr
  have := le_ciSup (regularize_bdd hV n x) (⟨x,hx⟩:K)
  simpa only [supRegularize,Subtype.coe_mk,dist_self,mul_zero,sub_zero] using this

lemma supRegularize_antitone {K : Set X} {V : X → EReal} (hK : K.Nonempty)
    (hV : ∀x∈K,V x≤0) (x : X) : Antitone (fun n => supRegularize K V n x) := by
  let : Nonempty K := hK.to_subtype
  intro m n hmn
  apply ciSup_le
  intro y
  apply le_trans _ (le_ciSup (regularize_bdd hV m x) y)
  exact sub_le_sub (truncBelow_antitone (hV y y.2) hmn)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmn) dist_nonneg)

lemma supRegularize_lipschitz {K : Set X} {V : X → EReal} (hK : K.Nonempty)
    (hV : ∀x∈K,V x≤0) (n : ℕ) : LipschitzWith (n:ℝ≥0) (supRegularize K V n) := by
  let : Nonempty K := hK.to_subtype
  have hdiff (x y : X) : supRegularize K V n x≤ supRegularize K V n y+(n:ℝ)*dist x y := by
    apply ciSup_le
    intro z
    have hle := le_ciSup (regularize_bdd hV n y) z
    change truncBelow V n z-(n:ℝ)*dist y z≤ supRegularize K V n y at hle
    have hd := dist_triangle_right y z x
    have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
    have hm := mul_le_mul_of_nonneg_left hd hn
    simp only [dist_comm y x,dist_comm (z:X) x] at hm
    linarith
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq,abs_le]
  have hxy := hdiff x y
  have hyx := hdiff y x
  simp only [dist_comm y x,NNReal.coe_natCast] at hyx ⊢
  constructor <;> linarith

lemma supRegularize_eventually_below {K : Set X} {V : X → EReal}
    (hV : ∀ x∈K,V x≤0) {x : X} (hx : x∈K)
    (husc : UpperSemicontinuousWithinAt V K x) {a : ℝ} (ha : V x<(a:EReal)) :
    ∃ n : ℕ, supRegularize K V n x≤a := by
  let : Nonempty K := ⟨⟨x,hx⟩⟩
  obtain ⟨δ,hδ,hnear⟩ := Metric.mem_nhdsWithin_iff.mp (husc a ha)
  obtain ⟨n,hn⟩ := exists_nat_gt (max (-a) (-a/δ))
  have hna : -(n:ℝ)≤a := by have := (le_max_left (-a) (-a/δ)).trans_lt hn; linarith
  have hnδ : -a<(n:ℝ)*δ := (div_lt_iff₀ hδ).mp ((le_max_right (-a) (-a/δ)).trans_lt hn)
  refine ⟨n,?_⟩
  apply ciSup_le
  intro y
  by_cases hd : dist x y<δ
  · have hy : V y<(a:EReal) := hnear ⟨by simpa only [Metric.mem_ball,dist_comm] using hd,y.2⟩
    have htr : truncBelow V n y≤a := by
      apply EReal.coe_le_coe_iff.mp
      rw [coe_truncBelow (hV y y.2)]
      exact max_le hy.le (EReal.coe_le_coe_iff.mpr hna)
    exact (sub_le_self _ (mul_nonneg (Nat.cast_nonneg n) dist_nonneg)).trans htr
  · have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hd) (Nat.cast_nonneg n : 0≤(n:ℝ))
    have ht := truncBelow_nonpos (n:=n) (hV y y.2)
    linarith

lemma iInf_supRegularize {K : Set X} {V : X → EReal}
    (hV : ∀x∈K,V x≤0) {x : X} (hx : x∈K)
    (husc : UpperSemicontinuousWithinAt V K x) :
    (⨅ n : ℕ, (supRegularize K V n x:EReal))=V x := by
  apply le_antisymm
  · by_contra h
    obtain ⟨a,ha,ha'⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge h)
    obtain ⟨n,hn⟩ := supRegularize_eventually_below hV hx husc ha
    exact (not_le_of_gt ha') ((iInf_le (fun n => (supRegularize K V n x:EReal)) n).trans (EReal.coe_le_coe_iff.mpr hn))
  · exact le_iInf (fun n => supRegularize_majorant hV n hx)

lemma tendsto_supRegularize {K : Set X} {V : X → EReal}
    (hV : ∀x∈K,V x≤0) {x : X} (hx : x∈K)
    (husc : UpperSemicontinuousWithinAt V K x) :
    Tendsto (fun n => (supRegularize K V n x:EReal)) atTop (𝓝 (V x)) := by
  rw [← iInf_supRegularize hV hx husc]
  exact tendsto_atTop_iInf (EReal.coe_strictMono.monotone.comp_antitone
    (supRegularize_antitone ⟨x,hx⟩ hV x))

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma toENNReal_coe_real (x : ℝ) : (x:EReal).toENNReal=ENNReal.ofReal x := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top x),EReal.toReal_coe]

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma circleAverage_eq_integral_polar (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    Real.circleAverage f c r=∫ t, f (circleMap c r t) ∂polarParameterMeasure := by
  have heq := ((periodic_circleMap c r).comp f).intervalIntegral_add_eq 0 (-Real.pi)
  simp only [Function.comp_def,zero_add, show -Real.pi+2*Real.pi=Real.pi by ring] at heq
  rw [polarParameterMeasure,integral_smul_measure,Real.circleAverage,heq,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),integral_Ioc_eq_integral_Ioo]
  simp only [ENNReal.toReal_ofReal (by positivity : 0≤(2*Real.pi)⁻¹)]

lemma polarParameter_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f polarParameterMeasure := by
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [restrict_Ioo_eq_restrict_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi)).mp
    (hf.intervalIntegrable (-Real.pi) Real.pi)

theorem circle_submean_polar {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r⊆Ω) :
    (∫⁻ t, (-V (planeComplex.symm (circleMap (planeComplex a) r t))).toENNReal
      ∂polarParameterMeasure) ≤ (-V a).toENNReal := by
  let K := Metric.sphere a r
  have hK : K.Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hKΩ : K⊆Ω := Metric.sphere_subset_closedBall.trans hball
  have hnegK : ∀ x∈K,V x≤0 := fun x hx => hneg x (hKΩ hx)
  let g : ℕ → ℂ → ℝ := fun n z => supRegularize K V n (planeComplex.symm z)
  have hg (n : ℕ) : Continuous (g n) :=
    (supRegularize_lipschitz hK hnegK n).continuous.comp planeComplex.symm.continuous
  let p : ℝ → Plane := fun t => planeComplex.symm (circleMap (planeComplex a) r t)
  have hpK (t : ℝ) : p t∈K := by
    change dist (planeComplex.symm (circleMap (planeComplex a) r t)) a=r
    rw [← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
    simpa only [planeComplex.apply_symm_apply] using Metric.mem_sphere.mp (circleMap_mem_sphere (planeComplex a) hr.le t)
  have hlim (t : ℝ) : Tendsto (fun n => ENNReal.ofReal (-g n (circleMap (planeComplex a) r t)))
      atTop (𝓝 ((-V (p t)).toENNReal)) := by
    have h := (tendsto_supRegularize hnegK (hpK t)
      ((hV _ (hKΩ (hpK t))).mono hKΩ)).neg
    have h' := EReal.continuous_toENNReal.continuousAt.tendsto.comp h
    simpa only [Function.comp_def,← EReal.coe_neg,toENNReal_coe_real,g,p] using h'
  let f : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (-g n (circleMap (planeComplex a) r t))
  have hf (n : ℕ) : Measurable (f n) := by
    exact ENNReal.continuous_ofReal.measurable.comp ((hg n).comp (continuous_circleMap _ _)).neg.measurable
  have hmono : Monotone f := by
    intro m n hmn t
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (supRegularize_antitone hK hnegK (p t) hmn))
  have hiSup (t : ℝ) : (⨆ n,f n t)=(-V (p t)).toENNReal :=
    tendsto_nhds_unique (tendsto_atTop_iSup (fun m n hmn => hmono hmn t)) (hlim t)
  change (∫⁻ t,(-V (p t)).toENNReal ∂polarParameterMeasure)≤_
  simp_rw [← hiSup]
  rw [lintegral_iSup hf hmono]
  apply iSup_le
  intro n
  have hfn : Continuous (fun t => -g n (circleMap (planeComplex a) r t)) :=
    ((hg n).comp (continuous_circleMap _ _)).neg
  have hfnpos : ∀t,0≤ -g n (circleMap (planeComplex a) r t) :=
    fun t => neg_nonneg.mpr (supRegularize_nonpos hK hnegK n (p t))
  rw [← ofReal_integral_eq_lintegral_ofReal (polarParameter_integrable hfn) (Filter.Eventually.of_forall hfnpos)]
  rw [integral_neg,← circleAverage_eq_integral_polar]
  rw [← toENNReal_coe_real, EReal.coe_neg]
  apply EReal.toENNReal_le_toENNReal
  apply EReal.neg_le_neg_iff.mpr
  apply submean_continuous_majorant hV (fun x hx => ne_of_lt ((hneg x hx).trans_lt (by simp))) htest hr hball (hg n)
  intro x hx
  simpa only [g,planeComplex.symm_apply_apply] using supRegularize_majorant hnegK n hx
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Set MeasureTheory Filter
namespace SharpNodal.Profiles
open Carleman

lemma polarCoord_eq_circleMap (r t : ℝ) : Complex.polarCoord.symm (r,t)=circleMap 0 r t := by
  simp only [Complex.polarCoord_symm_apply,circleMap,zero_add]
  rw [Complex.exp_mul_I]
  simp only [Complex.ofReal_cos,Complex.ofReal_sin]

lemma lintegral_radius {R : ℝ} (hR : 0≤R) :
    (∫⁻ r in Ioo 0 R, ENNReal.ofReal r)=ENNReal.ofReal (R^2/2) := by
  have hi : IntegrableOn (fun r : ℝ => r) (Ioo 0 R) := by
    rw [IntegrableOn,restrict_Ioo_eq_restrict_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp (continuous_id.intervalIntegrable 0 R)
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hR,integral_id]
    simp only [zero_pow (by decide : (2:ℕ)≠0),sub_zero]
  · exact ae_restrict_of_forall_mem measurableSet_Ioo (fun _ hr => hr.1.le)

lemma lintegral_ball_le_of_angular {f : ℂ → ℝ≥0∞} {R : ℝ} (hR : 0<R) {C : ℝ≥0∞}
    (hcircle : ∀ r∈Ioo 0 R, (∫⁻ t in Ioo (-Real.pi) Real.pi,f (circleMap 0 r t))≤C) :
    (∫⁻ z in Metric.ball (0:ℂ) R,f z)≤ENNReal.ofReal (R^2/2)*C := by
  by_cases hC : C=⊤
  · simp [hC,ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0<R^2/2)]
  let g := (Metric.ball (0:ℂ) R).indicator f
  rw [← lintegral_indicator measurableSet_ball,← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1*g (Complex.polarCoord.symm p))≤_
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  apply (lintegral_prod_le _).trans
  calc
    (∫⁻ r in Ioi (0:ℝ), ∫⁻ t in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal r*g (Complex.polarCoord.symm (r,t)))
      ≤ ∫⁻ r in Ioi (0:ℝ), (Iio R).indicator (fun r => ENNReal.ofReal r*C) r := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        by_cases hrR : r<R
        · rw [indicator_of_mem (show r∈Iio R from hrR)]
          have heq (t : ℝ) : g (Complex.polarCoord.symm (r,t))=f (circleMap 0 r t) := by
            dsimp [g]
            rw [indicator_of_mem,polarCoord_eq_circleMap]
            simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos (show 0 < r from hr)] using hrR
          simp_rw [heq]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact mul_le_mul' le_rfl (hcircle r ⟨hr,hrR⟩)
        · rw [indicator_of_notMem (show r∉Iio R from hrR)]
          have heq (t : ℝ) : g (Complex.polarCoord.symm (r,t))=0 := by
            apply indicator_of_notMem
            simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos (show 0 < r from hr)] using hrR
          simp only [heq,mul_zero,lintegral_zero,le_refl]
    _ = ∫⁻ r in Ioo 0 R, ENNReal.ofReal r*C := by
      have hset : Iio R∩Ioi (0:ℝ)=Ioo 0 R := by
        ext r
        exact and_comm
      rw [setLIntegral_indicator measurableSet_Iio,hset]
    _ = ENNReal.ofReal (R^2/2)*C := by
      rw [lintegral_mul_const' _ _ hC,lintegral_radius hR.le]

lemma lintegral_ball_center_le_of_angular {f : ℂ → ℝ≥0∞} {c : ℂ} {R : ℝ}
    (hR : 0<R) {C : ℝ≥0∞}
    (hcircle : ∀ r∈Ioo 0 R, (∫⁻ t in Ioo (-Real.pi) Real.pi,f (circleMap c r t))≤C) :
    (∫⁻ z in Metric.ball c R,f z)≤ENNReal.ofReal (R^2/2)*C := by
  have heq : (∫⁻ z in Metric.ball c R,f z)=(∫⁻ z in Metric.ball (0:ℂ) R,f (c+z)) := by
    rw [← lintegral_indicator measurableSet_ball,← lintegral_indicator measurableSet_ball,
      ← lintegral_add_left_eq_self _ c]
    apply lintegral_congr
    intro z
    by_cases hz : z∈Metric.ball (0:ℂ) R
    · rw [indicator_of_mem hz,indicator_of_mem]
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
    · rw [indicator_of_notMem hz,indicator_of_notMem]
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
  rw [heq]
  apply lintegral_ball_le_of_angular hR
  intro r hr
  simpa only [circleMap,zero_add] using hcircle r hr
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma lintegral_plane_ball_complex (f : Plane → ℝ≥0∞) (a : Plane) (r : ℝ) :
    (∫⁻x in Metric.ball a r,f x)=
      ∫⁻z in Metric.ball (planeComplex a) r,f (planeComplex.symm z) := by
  rw [← lintegral_indicator measurableSet_ball,← lintegral_indicator measurableSet_ball,
    ← planeComplex.symm.measurePreserving.lintegral_comp_emb planeComplex.symm.toHomeomorph.measurableEmbedding]
  apply lintegral_congr
  intro z
  have heq : planeComplex.symm z∈Metric.ball a r ↔ z∈Metric.ball (planeComplex a) r := by
    simp only [Metric.mem_ball,← planeComplex.isometry.dist_eq,planeComplex.apply_symm_apply]
  by_cases hz : z∈Metric.ball (planeComplex a) r
  · rw [indicator_of_mem hz,indicator_of_mem (heq.mpr hz)]
  · rw [indicator_of_notMem hz,indicator_of_notMem (heq.not.mpr hz)]
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem disk_submean {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {R : ℝ} (hR : 0<R)
    (hball : Metric.ball a R⊆Ω) :
    (∫⁻ x in Metric.ball a R, (-V x).toENNReal) ≤
      ENNReal.ofReal (Real.pi*R^2)*(-V a).toENNReal := by
  rw [lintegral_plane_ball_complex]
  have hc : ∀ r∈Ioo 0 R,
      (∫⁻ t in Ioo (-Real.pi) Real.pi,
        (-V (planeComplex.symm (circleMap (planeComplex a) r t))).toENNReal)
      ≤ ENNReal.ofReal (2*Real.pi)*(-V a).toENNReal := by
    intro r hr
    have hbr : Metric.closedBall a r⊆Ω := by
      apply Subset.trans _ hball
      intro x hx
      exact lt_of_le_of_lt hx hr.2
    have hs := circle_submean_polar hV hneg htest hr.1 hbr
    rw [polarParameterMeasure,lintegral_smul_measure] at hs
    have hh := mul_le_mul' (le_refl (ENNReal.ofReal (2*Real.pi))) hs
    simpa only [smul_eq_mul,← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0≤2*Real.pi),
      mul_inv_cancel₀ (by positivity : 2*Real.pi≠0),ENNReal.ofReal_one,one_mul] using hh
  apply (lintegral_ball_center_le_of_angular hR hc).trans_eq
  rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0≤R^2/2)]
  congr 2
  ring

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma usc_neg_toENNReal_aemeasurable {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : MeasurableSet Ω) (hV : UpperSemicontinuousOn V Ω) :
    AEMeasurable (fun x => (-V x).toENNReal) (volume.restrict Ω) := by
  apply aemeasurable_restrict_of_measurable_subtype hΩ
  exact EReal.continuous_toENNReal.measurable.comp
    (upperSemicontinuousOn_iff_restrict.mpr hV).measurable.neg

end SharpNodal.Profiles

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
-- module Solutions.OAIQ4_Nl.NodalLength_Subdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma profile_zero_on_ball {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuous V) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball a r⊆Ω) (ha : V a=0) :
    ∀x∈Metric.ball a r,V x=0 := by
  have hint := disk_submean (hV.upperSemicontinuousOn _) hneg htest hr hball
  rw [ha,neg_zero,EReal.toENNReal_zero,mul_zero] at hint
  have hz := (lintegral_eq_zero_iff'
    (usc_neg_toENNReal_aemeasurable measurableSet_ball (hV.upperSemicontinuousOn _))).mp
      (le_antisymm hint (bot_le))
  have hle : ∀ᵐx ∂(volume.restrict (Metric.ball a r)),0≤V x := by
    filter_upwards [hz] with x hx
    have := EReal.toENNReal_eq_zero_iff.mp hx
    simpa only [EReal.neg_le_zero] using this
  have ht0 : volume (Metric.ball a r ∩ V ⁻¹' Iio 0)=0 := by
    have hh := ae_imp_of_ae_restrict hle
    simpa only [ae_iff,Classical.not_imp,not_le,Set.inter_def,Set.preimage,Set.mem_Iio,Set.mem_ofPred_eq] using hh
  have ht := (Metric.isOpen_ball.inter (hV.isOpen_preimage 0)).eq_empty_of_measure_zero ht0
  intro x hx
  refine le_antisymm (hneg x (hball hx)) ?_
  by_contra hn
  have hx' : x∈Metric.ball a r ∩ V ⁻¹' Iio 0 := ⟨hx,lt_of_not_ge hn⟩
  rw [ht] at hx'
  exact hx'

theorem profile_strong_maximum {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hV : UpperSemicontinuous V)
    (hneg : ∀x∈Ω,V x≤0) (htest : FullTestProperty Ω V)
    {a : Plane} (haΩ : a∈Ω) (ha : V a=0) : ∀x∈Ω,V x=0 := by
  let Z : Set Plane := Ω ∩ {x | V x=0}
  have hZ : IsOpen Z := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hΩ x hx.1
    refine ⟨r,hr,fun y hy =>⟨hball hy,?_⟩⟩
    exact profile_zero_on_ball hV hneg htest hr hball hx.2 y hy
  have hd : Disjoint Z (V ⁻¹' Iio 0) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact (not_lt_of_ge (ge_of_eq hx.2)) hx'
  have hcover : Ω⊆Z ∪ V ⁻¹' Iio 0 := by
    intro x hx
    rcases (hneg x hx).eq_or_lt with hz | hn
    · exact Or.inl ⟨hx,hz⟩
    · exact Or.inr hn
  have hs := hconn.subset_left_of_subset_union hZ (hV.isOpen_preimage 0) hd
    hcover ⟨a,haΩ,haΩ,ha⟩
  exact fun _ hx =>(hs hx).2

end SharpNodal.Profiles

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_MetricFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric

namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

lemma smoothAt_partial {f : Plane → ℝ} {x : Plane} (hf : ContDiffAt ℝ ∞ f x) (i : Fin 2) :
    ContDiffAt ℝ ∞ (coordPartial f i) x :=
  (hf.fderiv_right (by simp)).clm_apply contDiffAt_const
lemma partial_congr_nhds {f g : Plane → ℝ} {x : Plane} (h : f=ᶠ[𝓝 x]g) (i : Fin 2) :
    coordPartial f i x=coordPartial g i x := by unfold coordPartial; rw [h.fderiv_eq]

end SharpNodal.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_NormalizedCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

namespace SharpNodal.Geometry
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

lemma smoothOn_pullback_metric {f : Plane → M} {s : Set Plane} (hs : IsOpen s)
    (hf : ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ f s) (v w : Plane) :
    ContDiffOn ℝ ∞ (fun y=>inner ℝ
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y v)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y w)) s := by
  have hc (a : Plane) : ContMDiff 𝓘(ℝ,Plane) (𝓘(ℝ,Plane)).tangent ∞
      (fun y:Plane=>(⟨y,a⟩ : TangentBundle 𝓘(ℝ,Plane) Plane)) := by
    intro y
    exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  have ht:=hf.contMDiffOn_tangentMapWithin (m:=∞) (by simp) hs.uniqueMDiffOn
  have hv (a : Plane) : ContMDiffOn 𝓘(ℝ,Plane) (𝓘(ℝ,Plane)).tangent ∞
      (fun y=> (⟨f y,mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y a⟩ : TangentBundle 𝓘(ℝ,Plane) M)) s := by
    have hh:=ht.comp (hc a).contMDiffOn (show MapsTo (fun y:Plane=>(⟨y,a⟩ : TangentBundle 𝓘(ℝ,Plane) Plane)) s (Bundle.TotalSpace.proj ⁻¹' s) from fun _ hy=>hy)
    apply hh.congr
    intro y hy
    simp only [Function.comp_apply,tangentMapWithin,
      mfderivWithin_of_mem_nhds (I:=𝓘(ℝ,Plane)) (I':=𝓘(ℝ,Plane)) (f:=f) (hs.mem_nhds hy)]
  exact ((hv v).inner_bundle (hv w)).contDiffOn

lemma ChartSmooth.metric_smooth {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e)
    (i j : Fin 2) : ContDiffOn ℝ ∞ (fun y=>pullMetric (e.symm : Plane → M) y i j) e.target :=
  smoothOn_pullback_metric e.open_target he.2 _ _

end SharpNodal.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Isothermal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma IsConformal.factor {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
    {y : Plane} (hy : y∈e.target) :
    0 < conformalFactor e y ∧ pullMetric (e.symm : Plane → M) y=
      conformalFactor e y • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨p,hp,hG⟩:=he.2 y hy
  have hf : conformalFactor e y=p:=by simp [conformalFactor,hG]
  exact ⟨hf.symm ▸ hp,by rwa [hf]⟩

lemma IsConformal.factor_smooth {e : OpenPartialHomeomorph M Plane} (he : IsConformal e) :
    ContDiffOn ℝ ∞ (conformalFactor e) e.target:=he.1.metric_smooth 0 0

lemma IsConformal.laplace {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
    {U : M → ℝ} (hU : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ U) {y : Plane} (hy : y∈e.target) :
    laplaceBeltrami U (e.symm y)=euclideanLaplacian (U ∘ e.symm) y/conformalFactor e y := by
  rw [laplaceBeltrami_in_chart he.1 (e.map_target hy) hU,e.right_inv hy]
  let a:=fun z=>pullMetric (e.symm : Plane → M) z 0 0
  let b:=fun z=>pullMetric (e.symm : Plane → M) z 0 1
  let c:=fun z=>pullMetric (e.symm : Plane → M) z 1 1
  have hf0 : scalarFlux0 a b c (U ∘ e.symm)=ᶠ[𝓝 y]coordPartial (U ∘ e.symm) 0 := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    have hpos:=(he.factor hz).1
    have hG:=(he.factor hz).2
    dsimp [scalarFlux0,scalarDensity,a,b,c]
    rw [hG]
    norm_num [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    rw [← pow_two,Real.sqrt_sq hpos.le]
    exact mul_div_cancel_left₀ _ hpos.ne'
  have hf1 : scalarFlux1 a b c (U ∘ e.symm)=ᶠ[𝓝 y]coordPartial (U ∘ e.symm) 1 := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    have hpos:=(he.factor hz).1
    have hG:=(he.factor hz).2
    dsimp [scalarFlux1,scalarDensity,a,b,c]
    rw [hG]
    norm_num [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    rw [← pow_two,Real.sqrt_sq hpos.le]
    exact mul_div_cancel_left₀ _ hpos.ne'
  have hρ : scalarDensity a b c y=conformalFactor e y := by
    dsimp [scalarDensity,a,b,c]
    rw [(he.factor hy).2]
    norm_num [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    rw [← pow_two,Real.sqrt_sq (he.factor hy).1.le]
  change scalarLaplace a b c (U ∘ e.symm) y=_
  rw [scalarLaplace,partial_congr_nhds hf0,partial_congr_nhds hf1,hρ]
  simp only [euclideanLaplacian,Fin.sum_univ_two]

lemma IsConformal.eigenfunction {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
    {U : M → ℝ} (hU : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ U) {lam : ℝ}
    (hPDE : ∀x,-laplaceBeltrami U x=lam*U x) :
    ContDiffOn ℝ ∞ (U ∘ e.symm) e.target ∧
      ∀y∈e.target,euclideanLaplacian (U ∘ e.symm) y+lam*conformalFactor e y*(U ∘ e.symm) y=0 := by
  refine ⟨(hU.comp_contMDiffOn he.1.2).contDiffOn,?_⟩
  intro y hy
  have h:=hPDE (e.symm y)
  rw [he.laplace hU hy] at h
  have hn:=(he.factor hy).1.ne'
  change -(euclideanLaplacian (U ∘ e.symm) y/conformalFactor e y)=lam*(U ∘ e.symm) y at h
  field_simp at h
  nlinarith

end SharpNodal.Geometry

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_InteriorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace

namespace SharpNodal.Profiles

variable {X : Type*}

lemma supMass_mono (u : X → ℝ) {s t : Set X} (h : s⊆t) : supMass u s≤ supMass u t := by
  exact iSup₂_mono' fun x hx=>⟨x,h hx,le_rfl⟩

lemma supMass_le {u : X → ℝ} {s : Set X} {a : ℝ≥0∞} :
    supMass u s≤a ↔ ∀x∈s,ENNReal.ofReal ((u x)^2)≤a := by
  simp only [supMass,iSup_le_iff]

variable [TopologicalSpace X] [SecondCountableTopology X]

lemma extract_sup_rates (u : ℕ → X → ℝ) (S : ℕ → ℝ) :
    ∃(ell : countableBasis X → EReal) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀i : countableBasis X,Tendsto (fun j=>logRate (S (φ j)) (supMass (u (φ j)) i.val)) atTop (𝓝 (ell i)) := by
  let z : ℕ → (countableBasis X → EReal):=fun j i=>logRate (S j) (supMass (u j) i.val)
  obtain ⟨ell,φ,hφ,hz⟩:=CompactSpace.tendsto_subseq z
  exact ⟨ell,φ,hφ,fun i=>(continuous_apply i).tendsto ell |>.comp hz⟩

lemma sup_open_lower {u : ℕ → X → ℝ} {S : ℕ → ℝ} {ell : countableBasis X → EReal}
    (hS : ∀j,0<S j)
    (hlim : ∀i : countableBasis X,Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i)))
    {G : Set X} (hG : IsOpen G) :
    (⨆x∈G,basisProfile ell x)≤liminf (fun j=>logRate (S j) (supMass (u j) G)) atTop := by
  refine iSup_le fun x=>iSup_le fun hx=>?_
  obtain ⟨U,hU,hxU,hUG⟩:=(isBasis_countableBasis X).exists_subset_of_mem_open hx hG
  let i : countableBasis X:=⟨U,hU⟩
  apply (basisProfile_le ell i hxU).trans
  rw [←(hlim i).liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun j=>logRate_mono (hS j) (supMass_mono _ hUG))

lemma sup_compact_upper {u : ℕ → X → ℝ} {S : ℕ → ℝ} {ell : countableBasis X → EReal}
    (hS : ∀j,0<S j)
    (hlim : ∀i : countableBasis X,Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i)))
    {F : Set X} (hF : IsCompact F) :
    limsup (fun j=>logRate (S j) (supMass (u j) F)) atTop≤⨆x∈F,basisProfile ell x := by
  classical
  by_contra hn
  obtain ⟨a,hVa,haL⟩:=EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  let I:={i : countableBasis X // ell i<(a:EReal)}
  let U : I → Set X:=fun i=>i.val.val
  have hcover : F⊆⋃i,U i := by
    intro x hx
    have hxa : basisProfile ell x<(a:EReal):=(le_iSup₂_of_le x hx le_rfl).trans_lt hVa
    obtain ⟨i,hxi,hia⟩:=(basisProfile_lt_iff ell x a).mp hxa
    exact mem_iUnion.mpr ⟨⟨i,hia⟩,hxi⟩
  obtain ⟨t,ht⟩:=hF.elim_finite_subcover U (fun i=>isOpen_of_mem_countableBasis i.val.property) hcover
  have hb : ∀ᶠj in atTop,∀i∈t,supMass (u j) (U i)≤ENNReal.ofReal (Real.exp (2*S j*a)) := by
    apply (eventually_all_finset t).mpr
    intro i hi
    filter_upwards [(hlim i.val).eventually (gt_mem_nhds i.property)] with j hj
    exact ((logRate_lt_iff (hS j) _).mp hj).le
  have he : ∀ᶠj in atTop,logRate (S j) (supMass (u j) F)≤(a:EReal) := by
    filter_upwards [hb] with j hj
    apply (logRate_le_iff (hS j) _).mpr
    apply supMass_le.mpr
    intro x hx
    obtain ⟨i,hit,hxi⟩:=mem_iUnion₂.mp (ht hx)
    exact (le_iSup₂_of_le x hxi le_rfl).trans (hj i hit)
  exact (not_le_of_gt haL) (limsup_le_of_le (by isBoundedDefault) he)

lemma supProfile_lt_local {u : ℕ → X → ℝ} {S : ℕ → ℝ} {ell : countableBasis X → EReal}
    (hS : ∀j,0<S j)
    (hlim : ∀i : countableBasis X,Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i)))
    {x : X} {a : ℝ} (h : basisProfile ell x<(a:EReal)) : SupLocalBound u S x a := by
  obtain ⟨i,hxi,hia⟩:=(basisProfile_lt_iff ell x a).mp h
  refine ⟨i.val,isOpen_of_mem_countableBasis i.property,hxi,?_⟩
  filter_upwards [(hlim i).eventually (gt_mem_nhds hia)] with j hj
  exact ((logRate_lt_iff (hS j) _).mp hj).le

lemma normalized_supProfile {u : ℕ → X → ℝ} {S : ℕ → ℝ} {ell : countableBasis X → EReal}
    (hS : ∀j,0<S j) (hu : ∀j x,|u j x|≤1)
    (hlim : ∀i : countableBasis X,Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i))) :
    ∀x,basisProfile ell x≤0 := by
  apply basisProfile_nonpos
  intro i
  apply le_of_tendsto (hlim i)
  filter_upwards [] with j
  change logRate (S j) (supMass (u j) i.val)≤(0:ℝ)
  apply (logRate_le_iff (hS j) _).mpr
  simp only [mul_zero,Real.exp_zero,ENNReal.ofReal_one]
  apply supMass_le.mpr
  intro x hx
  have hsq : (u j x)^2≤1:=(sq_le_one_iff_abs_le_one _).mpr (hu j x)
  exact (ENNReal.ofReal_le_ofReal hsq).trans_eq ENNReal.ofReal_one

lemma normalized_supProfile_max [CompactSpace X] [Nonempty X]
    {u : ℕ → X → ℝ} {S : ℕ → ℝ} {ell : countableBasis X → EReal}
    (hS : ∀j,0<S j) (hu : ∀j x,|u j x|≤1) (hmax : ∀j,∃x,|u j x|=1)
    (hlim : ∀i : countableBasis X,Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i))) :
    ∃x,basisProfile ell x=0 := by
  have hneg:=normalized_supProfile hS hu hlim
  have hm (j : ℕ) : supMass (u j) univ=1 := by
    apply le_antisymm
    · apply supMass_le.mpr
      intro x hx
      exact (ENNReal.ofReal_le_ofReal ((sq_le_one_iff_abs_le_one _).mpr (hu j x))).trans_eq ENNReal.ofReal_one
    · obtain ⟨x,hx⟩:=hmax j
      have hs : (u j x)^2=1:=by nlinarith [sq_abs (u j x)]
      simpa only [supMass,hs,ENNReal.ofReal_one] using (le_iSup₂_of_le x (mem_univ x) le_rfl : ENNReal.ofReal ((u j x)^2)≤ supMass (u j) univ)
  have hupper:=sup_compact_upper hS hlim (F:=univ) isCompact_univ
  simp only [hm,logRate,ENNReal.log_one,mul_zero,limsup_const] at hupper
  obtain ⟨x,hx,hmax'⟩:=(upperSemicontinuous_basisProfile ell).upperSemicontinuousOn univ |>.exists_isMaxOn Set.univ_nonempty isCompact_univ
  refine ⟨x,le_antisymm (hneg x) ?_⟩
  exact hupper.trans (iSup_le fun y=>iSup_le fun hy=>hmax' hy)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
namespace SharpNodal.Profiles
open Carleman

lemma plainMass_tilted (U : Plane → ℝ) (S : ℝ) (E : Set Plane) :
    plainMass U E=tiltedMass S 0 U 1 0 E := by simp [plainMass,tiltedMass,tiltedWeight]
lemma plainMass_le_sup (U : Plane → ℝ) (E : Set Plane) (hE : MeasurableSet E) :
    plainMass U E≤volume E*supMass U E := by
  calc
    _ ≤ ∫⁻x in E,supMass U E:=setLIntegral_mono' hE (fun x hx=>le_iSup₂_of_le x hx le_rfl)
    _ = _ := by simp [mul_comm]

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_GlobalProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric TopologicalSpace

namespace SharpNodal.Profiles
open Carleman

lemma WeightedProfileBounds.plain_lower {Ω : Set Plane} {S : ℕ → ℝ} {U : ℕ → Plane → ℝ} {W : Plane → EReal}
    (h : WeightedProfileBounds Ω S 0 U 1 W) {G : Set Plane} (hG : IsOpen G) (hGΩ : G⊆Ω) :
    (⨆x∈G,W x)≤liminf (fun j=>logRate (S j) (plainMass (U j) G)) atTop := by
  simpa only [Pi.zero_apply,Pi.one_apply,EReal.coe_zero,add_zero,←plainMass_tilted] using
    h.lower 0 continuousOn_const G hG hGΩ

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
lemma local_profile_le_sup {Ω : Set Plane} (hΩ : IsOpen Ω)
    {e : OpenPartialHomeomorph X Plane} (hΩe : Ω⊆e.target)
    {u : ℕ → X → ℝ} {S : ℕ → ℝ} {ell : countableBasis X → EReal} {W : Plane → EReal}
    (hSpos : ∀j,0<S j) (hS : Tendsto S atTop atTop)
    (hlim : ∀i : countableBasis X,Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i)))
    (hprofile : WeightedProfileBounds Ω S 0 (fun j=>u j ∘ e.symm) 1 W)
    {y : Plane} (hy : y∈Ω) : W y≤basisProfile ell (e.symm y) := by
  by_contra hn
  obtain ⟨a,hVa,haW⟩:=EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  obtain ⟨b,hab,hbW⟩:=EReal.lt_iff_exists_real_btwn.mp haW
  obtain ⟨G,hG,hxG,hbound⟩:=supProfile_lt_local hSpos hlim hVa
  have hopen : IsOpen (Ω∩(e.target∩e.symm ⁻¹' G)):=hΩ.inter (e.isOpen_inter_preimage_symm hG)
  have hyH : y∈Ω∩(e.target∩e.symm ⁻¹' G):=⟨hy,hΩe hy,hxG⟩
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp hopen y hyH
  have hlower:=hprofile.plain_lower isOpen_ball (fun z hz=>(hball hz).1)
  have hbmass := eventually_lt_of_lt_liminf (hbW.trans_le ((le_iSup₂_of_le y (mem_ball_self hr) le_rfl).trans hlower))
  let C:=1+volume.real (ball y r)
  have hC : 0<C:=by dsimp [C]; positivity
  have hvol : volume (ball y r)≤ENNReal.ofReal C := by
    rw [←ENNReal.ofReal_toReal (measure_ball_ne_top (μ:=volume) (x:=y) (r:=r))]
    apply ENNReal.ofReal_le_ofReal
    dsimp [C,measureReal_def]; linarith
  have hcomp : ∀j,plainMass (u j ∘ e.symm) (ball y r)≤ENNReal.ofReal C*supMass (u j) G := by
    intro j
    calc
      _ ≤ ∫⁻z in ball y r,supMass (u j) G := setLIntegral_mono' measurableSet_ball (fun z hz=>le_iSup₂_of_le (e.symm z) (hball hz).2.2 le_rfl)
      _ = volume (ball y r)*supMass (u j) G := by simp [mul_comm]
      _ ≤ _ := mul_le_mul' hvol le_rfl
  apply no_exponential_gap hS (EReal.coe_lt_coe_iff.mp hab) hC hbound _ (Eventually.of_forall hcomp)
  filter_upwards [hbmass] with j hj
  exact ((lt_logRate_iff (hSpos j) _).mp hj).le

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

lemma IsConformal.exists_profile_ball {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
    {y : Plane} (hy : y∈e.target) : ∃r Cp : ℝ,0 < r ∧ 0≤Cp ∧
      closedBall y r⊆e.target ∧ volume (ball y r)≤1 ∧
      (∀z∈ball y r,|conformalFactor e z|≤Cp) ∧
      (∀i z,z∈ball y r → |coordPartial (conformalFactor e) i z|≤Cp) := by
  obtain ⟨t,ht,hball⟩:=Metric.isOpen_iff.mp e.open_target y hy
  let r:=min (t/2) (1/4)
  have hr : 0 < r:=lt_min (by positivity) (by norm_num)
  have hrt : r<t:=lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr4 : r≤1/4:=min_le_right _ _
  have hc : closedBall y r⊆e.target:=(closedBall_subset_ball hrt).trans hball
  have hp:=he.factor_smooth
  have hpi (i : Fin 2) : ContinuousOn (coordPartial (conformalFactor e) i) e.target := by
    intro z hz
    exact (smoothAt_partial (hp.contDiffAt (e.open_target.mem_nhds hz)) i).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩:=(isCompact_closedBall y r).exists_bound_of_continuousOn (hp.continuousOn.mono hc)
  obtain ⟨B0,hB0⟩:=(isCompact_closedBall y r).exists_bound_of_continuousOn ((hpi 0).mono hc)
  obtain ⟨B1,hB1⟩:=(isCompact_closedBall y r).exists_bound_of_continuousOn ((hpi 1).mono hc)
  let Cp:=|B|+|B0|+|B1|
  refine ⟨r,Cp,hr,by dsimp [Cp]; positivity,hc,?_,?_,?_⟩
  · rw [EuclideanSpace.volume_ball_fin_two,←ENNReal.ofReal_pow hr.le,←ENNReal.ofReal_mul (sq_nonneg r)]
    apply ENNReal.ofReal_le_one.mpr
    have hh:=Real.pi_lt_four
    nlinarith
  · intro z hz
    have hb:=hB z (ball_subset_closedBall hz)
    rw [Real.norm_eq_abs] at hb
    dsimp [Cp]; linarith [le_abs_self B,abs_nonneg B0,abs_nonneg B1]
  · intro i z hz
    fin_cases i
    · have hb:=hB0 z (ball_subset_closedBall hz)
      rw [Real.norm_eq_abs] at hb
      dsimp [Cp]; linarith [le_abs_self B0,abs_nonneg B,abs_nonneg B1]
    · have hb:=hB1 z (ball_subset_closedBall hz)
      rw [Real.norm_eq_abs] at hb
      dsimp [Cp]; linarith [le_abs_self B1,abs_nonneg B,abs_nonneg B0]

variable [SecondCountableTopology M]
lemma sup_profile_local_zero {u : ℕ → M → ℝ} {K S : ℕ → ℝ}
    {ell : TopologicalSpace.countableBasis M → EReal}
    (hu : ∀j,ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ (u j))
    (hPDE : ∀j x,-laplaceBeltrami (u j) x=(K j)^2*u j x)
    (hnorm : ∀j x,|u j x|≤1)
    (hSpos : ∀j,0<S j) (hS : Tendsto S atTop atTop)
    (hKS : Tendsto (fun j=>K j/S j) atTop (𝓝 0))
    (hlim : ∀i : TopologicalSpace.countableBasis M,
      Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i)))
    {x : M} (hx : basisProfile ell x=0) :
    ∃G : Set M,IsOpen G ∧ x∈G ∧ ∀z∈G,basisProfile ell z=0 := by
  obtain ⟨e,hxE,he⟩:=exists_isothermal_chart x
  let y:=e x
  have hy : y∈e.target:=e.map_source hxE
  obtain ⟨r,Cp,hr,hCp,hclose,hvol,hpbound,hgrad⟩:=he.exists_profile_ball hy
  let Ω:=ball y r
  have hΩe : Ω⊆e.target:=ball_subset_closedBall.trans hclose
  let U:=fun j=>u j ∘ e.symm
  let p:=conformalFactor e
  have hU (j : ℕ) : ContDiffOn ℝ ∞ (U j) Ω:= (he.eigenfunction (hu j) (hPDE j)).1.mono hΩe
  have hp : ContDiffOn ℝ ∞ p Ω:=he.factor_smooth.mono hΩe
  have heq (j : ℕ) (z : Plane) (hz:z∈Ω) : euclideanLaplacian (U j) z+(K j)^2*p z*U j z=0 :=
    (he.eigenfunction (hu j) (hPDE j)).2 z (hΩe hz)
  have hnorm' (j : ℕ) : tiltedMass (S j) 0 (U j) 1 0 Ω≤1 := by
    rw [←plainMass_tilted]
    apply (plainMass_le_sup _ _ measurableSet_ball).trans
    have hs : supMass (U j) Ω≤1 := supMass_le.mpr (fun z _=>
      (ENNReal.ofReal_le_ofReal ((sq_le_one_iff_abs_le_one _).mpr (hnorm j (e.symm z)))).trans_eq ENNReal.ofReal_one)
    simpa only [mul_one] using mul_le_mul' hvol hs
  obtain ⟨W,φ,hφ,hW,hWneg,hprofile⟩:=extract_tilted_profile isOpen_ball S 0 U 1 hSpos hS
    (fun j=>(hU j).continuousOn) hnorm'
  have hprofile' : WeightedProfileBounds Ω (S∘φ) 0 (U∘φ) 1 W := by
    convert hprofile using 1 <;> funext j <;> rfl
  have hφSpos (j : ℕ) : 0<(S∘φ) j:=hSpos (φ j)
  have hφS : Tendsto (S∘φ) atTop atTop:=hS.comp hφ.tendsto_atTop
  have hφlim (i : TopologicalSpace.countableBasis M) :
      Tendsto (fun j=>logRate ((S∘φ) j) (supMass (u (φ j)) i.val)) atTop (𝓝 (ell i)) :=
    (hlim i).comp hφ.tendsto_atTop
  have hKle : ∀ᶠj in atTop,|K (φ j)|≤S (φ j) := by
    have hh:=((hKS.abs).comp hφ.tendsto_atTop).eventually_le_const (by norm_num : |(0:ℝ)|<1)
    filter_upwards [hh] with j hj
    change |K (φ j)/S (φ j)|≤1 at hj
    rw [abs_div,abs_of_pos (hSpos (φ j)),div_le_one (hSpos (φ j))] at hj
    exact hj
  have hEq (z : Plane) (hz:z∈Ω) : W z=basisProfile ell (e.symm z) := by
    apply le_antisymm
    · exact local_profile_le_sup isOpen_ball hΩe hφSpos hφS hφlim hprofile' hz
    · exact sup_profile_le_local isOpen_ball hΩe hφSpos hφS hKle hCp
        (fun j=>hU (φ j)) (fun _=>hp) (fun j=>heq (φ j)) (fun _=>hpbound)
        hφlim hW hprofile' hz
  have herror : Tendsto (fun j=>Cp*(K (φ j)/S (φ j))^2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((hKS.comp hφ.tendsto_atTop).pow 2))
  have htest : FullTestProperty Ω W := by
    apply full_test_of_profile (B:=0) (c:=1) isOpen_ball (fun _=>hp) (fun j=>hU (φ j)) hφSpos hφS (fun _=>by norm_num)
      (K:=K∘φ) (e:=fun j=>Cp*(K (φ j)/S (φ j))^2)
    · simp only [Pi.zero_apply,norm_zero,add_zero]
      exact hKS.comp hφ.tendsto_atTop
    · exact fun _=>hpbound
    · exact herror
    · intro j i z hz
      simp only [Pi.zero_apply,norm_zero,add_zero,Function.comp_apply]
      rw [abs_div,abs_mul,abs_sq,abs_of_pos (mul_pos (hSpos (φ j)) (hSpos (φ j)))]
      have hg:=hgrad i z hz
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg (sq_nonneg _)) (mul_nonneg (hSpos (φ j)).le (hSpos (φ j)).le)).trans_eq
      ring
    · exact fun j=>heq (φ j)
    · exact hW.upperSemicontinuousOn _
    · exact hprofile'
  have hWy : W y=0:=by rw [hEq y (mem_ball_self hr),e.left_inv hxE,hx]
  have hzero:=profile_strong_maximum isOpen_ball (convex_ball y r).isPreconnected hW (fun z _=>hWneg z)
    htest (mem_ball_self hr) hWy
  refine ⟨e.source∩e ⁻¹' Ω,e.isOpen_inter_preimage isOpen_ball,⟨hxE,mem_ball_self hr⟩,?_⟩
  intro z hz
  have ht:=hzero (e z) hz.2
  rw [hEq (e z) hz.2,e.left_inv hz.1] at ht
  exact ht

lemma global_sup_profile_zero [CompactSpace M] [ConnectedSpace M]
    {u : ℕ → M → ℝ} {K S : ℕ → ℝ} {ell : TopologicalSpace.countableBasis M → EReal}
    (hu : ∀j,ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ (u j))
    (hPDE : ∀j x,-laplaceBeltrami (u j) x=(K j)^2*u j x)
    (hnorm : ∀j x,|u j x|≤1) (hmax : ∀j,∃x,|u j x|=1)
    (hSpos : ∀j,0<S j) (hS : Tendsto S atTop atTop)
    (hKS : Tendsto (fun j=>K j/S j) atTop (𝓝 0))
    (hlim : ∀i : TopologicalSpace.countableBasis M,
      Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i))) :
    ∀x,basisProfile ell x=0 := by
  let Z:={x:M|basisProfile ell x=0}
  have hZ : IsOpen Z := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨G,hG,hxG,hzero⟩:=sup_profile_local_zero hu hPDE hnorm hSpos hS hKS hlim hx
    exact ⟨G,hzero,hG,hxG⟩
  have hneg:=normalized_supProfile hSpos hnorm hlim
  have hcomp : Zᶜ=(basisProfile ell) ⁻¹' Iio 0 := by
    ext x
    simp only [Z,mem_compl_iff,mem_ofPred_eq,mem_preimage,mem_Iio]
    exact ⟨fun h=>(hneg x).lt_of_ne h,ne_of_lt⟩
  have hclosed : IsClosed Z:=isOpen_compl_iff.mp (hcomp ▸ (upperSemicontinuous_basisProfile ell).isOpen_preimage 0)
  obtain ⟨x,hx⟩:=normalized_supProfile_max hSpos hnorm hmax hlim
  have hUniv : Z=univ:=IsClopen.eq_univ ⟨hclosed,hZ⟩ ⟨x,hx⟩
  intro z
  have : z∈Z:=hUniv ▸ mem_univ z
  exact this

end SharpNodal.Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Eigenfunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric TopologicalSpace
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold

namespace SharpNodal.Geometry
open Carleman Profiles
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

variable [CompactSpace M] [ConnectedSpace M]
lemma uniform_local_sup_lower_oai {G : Set M} (hG : IsOpen G) (hGne : G.Nonempty) :
    ∃C : ℝ,0<C ∧ ∀K : ℝ,∀u : M → ℝ,NormalizedEigen K u →
      ENNReal.ofReal (Real.exp (-C*(1+|K|)))≤ supMass u G := by
  by_contra hn
  push Not at hn
  have hf (j : ℕ):=hn (2*((j:ℝ)+1)^2) (by positivity)
  choose K u hu hf using hf
  let S:=fun j : ℕ=>((j:ℝ)+1)*(1+|K j|)
  have hSpos (j : ℕ) : 0<S j := by dsimp [S]; positivity
  have hT : Tendsto (fun j : ℕ=>(j:ℝ)+1) atTop atTop:=
    tendsto_atTop_mono (fun _=>le_add_of_nonneg_right (by norm_num)) tendsto_natCast_atTop_atTop
  have hS : Tendsto S atTop atTop:=tendsto_atTop_mono (fun j=>by
    change (j:ℝ)+1≤((j:ℝ)+1)*(1+|K j|)
    nlinarith [abs_nonneg (K j),Nat.cast_nonneg (α:=ℝ) j]) hT
  have hKS : Tendsto (fun j=>K j/S j) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (tendsto_inv_atTop_zero.comp hT)
    intro j
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (hSpos j)]
    apply (div_le_iff₀ (hSpos j)).mpr
    dsimp [S]
    have hj : (j:ℝ)+1≠0:=ne_of_gt (by positivity)
    rw [←mul_assoc,inv_mul_cancel₀ hj,one_mul]
    linarith
  obtain ⟨ell,φ,hφ,hlim⟩:=extract_sup_rates u S
  have hzero:=global_sup_profile_zero (fun j=>(hu (φ j)).smooth)
    (fun j=>(hu (φ j)).equation) (fun j=>(hu (φ j)).bound) (fun j=>(hu (φ j)).maximum)
    (fun j=>hSpos (φ j)) (hS.comp hφ.tendsto_atTop) (hKS.comp hφ.tendsto_atTop) hlim
  have hlower:=sup_open_lower (fun j=>hSpos (φ j)) hlim hG
  obtain ⟨x,hx⟩:=hGne
  have h0 : (0:EReal)≤liminf (fun j=>logRate (S (φ j)) (supMass (u (φ j)) G)) atTop :=
    (show (0:EReal)≤⨆z∈G,basisProfile ell z from by rw [←hzero x]; exact le_iSup₂_of_le x hx le_rfl).trans hlower
  have hle : ∀j,logRate (S j) (supMass (u j) G)≤(-1:EReal) := by
    intro j
    apply le_of_lt
    change logRate (S j) (supMass (u j) G)<((-1:ℝ):EReal)
    apply (logRate_lt_iff (hSpos j) _).mpr
    apply (hf j).trans_le
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    dsimp [S]
    have hj : (1:ℝ)≤(j:ℝ)+1:=by linarith [Nat.cast_nonneg (α:=ℝ) j]
    have hs : (j:ℝ)+1≤((j:ℝ)+1)^2:=by nlinarith
    have hh:=mul_le_mul_of_nonneg_right hs (show 0≤1+|K j| by positivity)
    nlinarith only [hh]
  have h1 : liminf (fun j=>logRate (S (φ j)) (supMass (u (φ j)) G)) atTop≤-1 :=
    (liminf_le_limsup).trans (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun j=>hle (φ j)))
  have hh : ((0:ℝ):EReal)≤((-1:ℝ):EReal):=h0.trans h1
  have := EReal.coe_le_coe_iff.mp hh
  norm_num at this

end SharpNodal.Geometry

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpNodal.Geometry.uniform_local_sup_lower_oai.{u_1} := @OAI.SharpNodal.Geometry.uniform_local_sup_lower_oai.{u_1}
