-- Prove2me | solution 1 for OAI.SharpNodal.Profiles.uniform_persistence_alternative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:25:37.388555+00:00
-- url     : https://prove2.me/submissions/1fd1bc86-c90a-4c77-913c-3e47532171af

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000
import Theorems.Thm_OAI_SharpNodal_Profiles_full_test_of_profile
import Theorems.Thm_OAI_SharpNodal_Profiles_profile_small_affine_grid_gap

section
-- module Solutions.OAIQ4_Nl.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

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
namespace SharpNodal.Profiles
open Carleman

lemma WeightedProfileBounds.subseq {Ω : Set Plane} {S c : ℕ → ℝ} {B : ℕ → Plane}
    {U : ℕ → Plane → ℝ} {V : Plane → EReal}
    (h : WeightedProfileBounds Ω S B U c V) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    WeightedProfileBounds Ω (S∘φ) (B∘φ) (U∘φ) (c∘φ) V := by
  constructor
  · intro f hf F hF hFΩ
    exact hφ.limsup_comp_le_limsup.trans (h.upper f hf F hF hFΩ)
  · intro f hf G hG hGΩ
    exact (h.lower f hf G hG hGΩ).trans hφ.liminf_le_liminf_comp

end SharpNodal.Profiles

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

theorem disk_lintegral_le_of_anchor {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {R C : ℝ} (hR : 0<R)
    (hball : Metric.ball a R⊆Ω) (hanchor : (-(C:ℝ):EReal)≤V a) :
    (∫⁻ x in Metric.ball a R, (-V x).toENNReal) ≤ ENNReal.ofReal (Real.pi*R^2)*ENNReal.ofReal C := by
  apply (disk_submean hV hneg htest hR hball).trans
  apply mul_le_mul' le_rfl
  rw [← toENNReal_coe_real]
  apply EReal.toENNReal_le_toENNReal
  simpa only [← EReal.coe_neg,neg_neg] using EReal.neg_le_neg_iff.mpr hanchor

theorem profile_lintegral_D8 {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    {a : Plane} (ha : a∈Metric.closedBall 0 1) (hanchor : (-1:EReal)≤V a) :
    (∫⁻x in Metric.ball (0:Plane) 8,(-V x).toENNReal)≤ ENNReal.ofReal (100*Real.pi) := by
  have hsubset : Metric.ball (0:Plane) 8⊆Metric.ball a 10 := by
    intro x hx
    have hd := dist_triangle x 0 a
    have ha' : dist (0:Plane) a≤1 := by simpa only [dist_comm] using Metric.mem_closedBall.mp ha
    change dist x a<10
    change dist x 0<8 at hx
    linarith
  have hball : Metric.ball a 10⊆Metric.ball (0:Plane) 1000 := by
    intro x hx
    have hd := dist_triangle x a 0
    change dist a 0≤1 at ha
    change dist x a<10 at hx
    change dist x 0<1000
    linarith
  apply (lintegral_mono' (Measure.restrict_mono hsubset (le_refl volume)) (le_refl (fun x => (-V x).toENNReal))).trans
  have hh := disk_lintegral_le_of_anchor hV hneg htest (by norm_num : (0:ℝ)<10) hball (C:=1) (by simpa using hanchor)
  simpa only [show Real.pi*(10:ℝ)^2=100*Real.pi by ring,ENNReal.ofReal_one,mul_one] using hh
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

lemma profile_integrable_of_lintegral_ne_top {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : MeasurableSet Ω) (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (hfin : (∫⁻ x in Ω, (-V x).toENNReal)≠⊤) :
    IntegrableOn (fun x => (V x).toReal) Ω ∧ (∀ᵐx ∂volume.restrict Ω,V x≠⊥) := by
  have hm := usc_neg_toENNReal_aemeasurable hΩ hV
  have hi := integrable_toReal_of_lintegral_ne_top hm hfin
  have heq : (fun x => (V x).toReal)=ᵐ[volume.restrict Ω]
      (fun x => -((-V x).toENNReal.toReal)) := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    rw [EReal.toReal_toENNReal (by simpa using EReal.neg_le_neg_iff.mpr (hneg x hx)),
      EReal.toReal_neg_eq,neg_neg]
  refine ⟨hi.neg.congr heq.symm,?_⟩
  filter_upwards [ae_lt_top' hm hfin] with x hx
  simpa only [EReal.toENNReal_ne_top_iff,ne_eq,EReal.neg_eq_top_iff] using ne_of_lt hx

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
-- module Solutions.OAIQ4_Nl.NodalLength_AffineError
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

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma profile_finite_ae_D3 {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) :
    ∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → V x≠⊥ ∧ V x≠⊤ := by
  obtain ⟨a,ha,hVa⟩ := hanchor
  have hb : Metric.ball (0:Plane) 8⊆Metric.ball (0:Plane) 1000 := Metric.ball_subset_ball (by norm_num)
  have hi := (profile_integrable_of_lintegral_ne_top measurableSet_ball (hV.mono hb)
    (fun x hx => hneg x (hb hx))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (profile_lintegral_D8 hV hneg htest ha hVa))).2
  have hj := (ae_restrict_iff' measurableSet_ball).mp hi
  filter_upwards [hj] with x hx hm
  exact ⟨hx (Metric.ball_subset_ball (by norm_num : (3:ℝ)≤8) hm),
    ne_top_of_le_ne_top (by simp) (hneg x (Metric.ball_subset_ball (by norm_num : (3:ℝ)≤1000) hm))⟩

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
-- module Solutions.OAIQ4_Nl.NodalLength_GridImprovement
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

namespace SharpNodal.Profiles

lemma gridCenters_norm {A : ℕ} (hA : 0<A) : ∀y∈gridCenters A,‖y‖≤1 := by
  intro y hy
  obtain ⟨p,_hp,rfl⟩ := Finset.mem_image.mp hy
  exact gridCenter_norm hA p

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma profile_weighted_sup_real {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a)
    {E : Set Plane} (hE : E⊆Metric.ball (0:Plane) 3) (hpos : volume E≠0)
    {f : Plane → ℝ} {C : ℝ} (hf : ∀x∈E,f x≤C) :
    ∃a : ℝ,(⨆x∈E,V x+(f x:EReal))=(a:EReal) := by
  let a := ⨆x∈E,V x+(f x:EReal)
  have hu : a≤(C:EReal) := by
    refine iSup₂_le (fun x hx => ?_)
    calc
      _ ≤ (0:EReal)+(f x:EReal) := add_le_add (hneg x ((Metric.ball_subset_ball (by norm_num : (3:ℝ)≤1000)) (hE hx))) le_rfl
      _ ≤ _ := by simpa using (EReal.coe_le_coe_iff.mpr (hf x hx))
  have htop : a≠⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top C) hu
  have hae := profile_finite_ae_D3 hV hneg htest hanchor
  obtain ⟨x,hx,hfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hae)
  have hfx := hfin (hE hx)
  have hbot : a≠⊥ := by
    have he := EReal.coe_toReal hfx.2 hfx.1
    have hl : (((V x).toReal+f x:ℝ):EReal)≤a := by
      rw [EReal.coe_add,he]
      exact le_iSup₂_of_le x hx le_rfl
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hl
  exact ⟨a.toReal,(EReal.coe_toReal htop hbot).symm⟩

lemma logRate_real {S : ℝ} {m : ℝ≥0∞} (hm0 : m≠0) (hmt : m≠⊤) :
    logRate S m=((Real.log m.toReal/(2*S):ℝ):EReal) := by
  rw [logRate,ENNReal.log_pos_real hm0 hmt,← EReal.coe_mul]
  congr 1
  ring

lemma massExcess_div {S : ℝ} {a b : ℝ≥0∞} (hS : S≠0)
    (ha0 : a≠0) (hat : a≠⊤) (hb0 : b≠0) (hbt : b≠⊤) :
    massExcess a b/S=Real.log a.toReal/(2*S)-Real.log b.toReal/(2*S) := by
  unfold massExcess
  rw [Real.log_div (ENNReal.toReal_ne_zero.mpr ⟨ha0,hat⟩) (ENNReal.toReal_ne_zero.mpr ⟨hb0,hbt⟩)]
  field_simp

lemma eventual_massExcess_bound {S : ℕ → ℝ} (hS : ∀j,0<S j)
    {A B : ℕ → ℝ≥0∞} (hBA : ∀j,B j≤A j) {a e ε : ℝ} (hε : 0<ε)
    (hu : limsup (fun j =>logRate (S j) (A j)) atTop≤((a+e:ℝ):EReal))
    (hl : (a:EReal)≤liminf (fun j =>logRate (S j) (B j)) atTop) :
    ∀ᶠj in atTop,B j≠0 ∧ A j≠⊤ ∧ massExcess (A j) (B j)/S j<e+ε := by
  have huu := eventually_lt_of_limsup_lt (hu.trans_lt (EReal.coe_lt_coe_iff.mpr
    (show a+e<a+e+ε/2 by linarith)))
  have hll := eventually_lt_of_lt_liminf ((EReal.coe_lt_coe_iff.mpr
    (show a-ε/2<a by linarith)).trans_le hl)
  filter_upwards [huu,hll] with j hjh hjl
  have hat : A j≠⊤ := ne_top_of_lt ((logRate_lt_iff (hS j) _).mp hjh)
  have hb0 : B j≠0 := ne_of_gt (lt_trans (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    ((lt_logRate_iff (hS j) _).mp hjl))
  have ha0 : A j≠0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hb0) (hBA j))
  have hbt : B j≠⊤ := ne_top_of_le_ne_top hat (hBA j)
  rw [logRate_real ha0 hat] at hjh
  rw [logRate_real hb0 hbt] at hjl
  have hh := EReal.coe_lt_coe_iff.mp hjh
  have hh' := EReal.coe_lt_coe_iff.mp hjl
  refine ⟨hb0,hat,?_⟩
  rw [massExcess_div (ne_of_gt (hS j)) ha0 hat hb0 hbt]
  linarith

lemma tiltedMass_mono_set (S : ℝ) (B : Plane) (U : Plane → ℝ) (c : ℝ) (f : Plane → ℝ)
    {E F : Set Plane} (hEF : E⊆F) : tiltedMass S B U c f E≤tiltedMass S B U c f F := by
  exact lintegral_mono_set hEF

lemma profile_massExcess_transfer {Ω : Set Plane} {V : Plane → EReal}
    {S c : ℕ → ℝ} {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hp : WeightedProfileBounds Ω S B U c V) (hS : ∀j,0<S j)
    {f : Plane → ℝ} (hf : ContinuousOn f Ω) {F G E : Set Plane}
    (hF : IsCompact F) (hFΩ : F⊆Ω) (hG : IsOpen G) (hGΩ : G⊆Ω)
    (hGE : G⊆E) (hEF : E⊆F) {a e ε : ℝ} (hε : 0<ε)
    (hinner : (⨆x∈G,V x+(f x:EReal))=(a:EReal))
    (hgap : (⨆x∈F,V x+(f x:EReal))≤((a+e:ℝ):EReal)) :
    ∀ᶠj in atTop,tiltedMass (S j) (B j) (U j) (c j) f G≠0 ∧
      tiltedMass (S j) (B j) (U j) (c j) f E≠⊤ ∧
      massExcess (tiltedMass (S j) (B j) (U j) (c j) f E)
        (tiltedMass (S j) (B j) (U j) (c j) f G)/S j<e+ε := by
  apply eventual_massExcess_bound hS (fun j =>tiltedMass_mono_set _ _ _ _ _ hGE) hε
  · have hm : limsup (fun j =>logRate (S j) (tiltedMass (S j) (B j) (U j) (c j) f E)) atTop≤
        limsup (fun j =>logRate (S j) (tiltedMass (S j) (B j) (U j) (c j) f F)) atTop := by
      exact limsup_le_limsup (Eventually.of_forall (fun j =>logRate_mono (hS j) (tiltedMass_mono_set _ _ _ _ _ hEF)))
    exact hm.trans ((hp.upper f hf F hF hFΩ).trans hgap)
  · rw [← hinner]
    exact hp.lower f hf G hG hGΩ

end SharpNodal.Profiles

noncomputable section
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma tiltedMass_const_mul (S : ℝ) (B : Plane) (U : Plane → ℝ) (c d : ℝ)
    (hc : 0 ≤ c) (f : Plane → ℝ) (E : Set Plane) :
    tiltedMass S B U (c*d) f E=ENNReal.ofReal c*tiltedMass S B U d f E := by
  unfold tiltedMass
  simp_rw [mul_assoc,ENNReal.ofReal_mul hc]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma massExcess_mul_left (c a b : ℝ≥0∞) (hc0 : c≠0) (hct : c≠⊤) :
    massExcess (c*a) (c*b)=massExcess a b := by
  unfold massExcess
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,mul_div_mul_left]
  exact ENNReal.toReal_ne_zero.mpr ⟨hc0,hct⟩

lemma tiltedMass_normalized {S : ℝ} {B : Plane} {U : Plane → ℝ} {Ω : Set Plane}
    (hm0 : tiltedMass S B U 1 0 Ω≠0) (hmt : tiltedMass S B U 1 0 Ω≠⊤) :
    let c := (tiltedMass S B U 1 0 Ω).toReal⁻¹
    0 < c ∧ tiltedMass S B U c 0 Ω=1 := by
  dsimp only
  have hm : 0<(tiltedMass S B U 1 0 Ω).toReal := ENNReal.toReal_pos hm0 hmt
  refine ⟨inv_pos.mpr hm,?_⟩
  rw [← mul_one (tiltedMass S B U 1 0 Ω).toReal⁻¹,
    tiltedMass_const_mul _ _ _ _ 1 (inv_pos.mpr hm).le,ENNReal.ofReal_inv_of_pos hm,
    ENNReal.ofReal_toReal hmt,ENNReal.inv_mul_cancel hm0 hmt]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma profile_anchor_from_mass {V : Plane → EReal} {S c : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U c V)
    (hS : ∀j,0<S j)
    (hinner : ∀j,(-1:EReal)≤logRate (S j)
      (tiltedMass (S j) (B j) (U j) (c j) 0 (Metric.ball 0 1))) :
    ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a := by
  have hsub : Metric.closedBall (0:Plane) 1⊆Metric.ball 0 1000 :=
    Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨a,ha,hmax⟩ := (hV.mono hsub).exists_isMaxOn
    ⟨0,Metric.mem_closedBall_self (by norm_num)⟩ (isCompact_closedBall 0 1)
  refine ⟨a,ha,?_⟩
  have hl : (-1:EReal)≤limsup (fun j =>logRate (S j)
      (tiltedMass (S j) (B j) (U j) (c j) 0 (Metric.closedBall 0 1))) atTop := by
    apply le_limsup_of_frequently_le'
    exact Filter.Eventually.frequently (Eventually.of_forall (fun j => (hinner j).trans
      (logRate_mono (hS j) (tiltedMass_mono_set _ _ _ _ _ Metric.ball_subset_closedBall))))
  have hu := hp.upper 0 continuousOn_const _ (isCompact_closedBall 0 1) hsub
  have hm : (⨆x∈Metric.closedBall (0:Plane) 1,V x+(0:EReal))≤V a := by
    exact iSup₂_le (fun x hx => by simpa using hmax hx)
  exact hl.trans (hu.trans (by simpa using hm))

end SharpNodal.Profiles

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
namespace SharpNodal.Profiles
open Carleman

lemma centeredMass_mono (T : Plane) (U : Plane → ℝ) (y : Plane) {r R : ℝ}
    (hrR : r≤R) : centeredMass T U y r ≤ centeredMass T U y R :=
  lintegral_mono_set (Metric.ball_subset_ball hrR)

lemma tiltedMass_centered (S : ℝ) (B c : Plane) (U : Plane → ℝ) (d : ℝ)
    (hd : 0≤d) (y : Plane) (r : ℝ) :
    tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y r)=
      ENNReal.ofReal (d*Real.exp (-2*inner ℝ B y))*centeredMass (B+S • c) U y r := by
  unfold tiltedMass centeredMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (mul_nonneg hd (Real.exp_pos _).le)]
  congr 1
  have hw : tiltedWeight B S (fun x =>-(-inner ℝ c (x-y))) x=
      -inner ℝ B y-inner ℝ (B+S • c) (x-y) := by
    simp only [tiltedWeight,neg_neg,inner_add_left,real_inner_smul_left,inner_sub_right]
    ring
  rw [hw,sub_eq_add_neg,Real.exp_add]
  simp only [mul_pow]
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show 2*(-inner ℝ B y)= -2*inner ℝ B y by ring]
  ring

lemma tilted_excess_centered (S : ℝ) (B c : Plane) (U : Plane → ℝ) (d : ℝ)
    (hd : 0<d) (y : Plane) (R r : ℝ) :
    massExcess (tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y R))
      (tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y r))=
    massExcess (centeredMass (B+S • c) U y R) (centeredMass (B+S • c) U y r) := by
  rw [tiltedMass_centered _ _ _ _ _ hd.le,tiltedMass_centered _ _ _ _ _ hd.le]
  apply massExcess_mul_left
  · exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hd (Real.exp_pos _))
  · exact ENNReal.ofReal_ne_top

lemma tilted_finite_centered {S : ℝ} {B c : Plane} {U : Plane → ℝ} {d : ℝ}
    (hd : 0<d) {y : Plane} {R r : ℝ}
    (hinner : tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y r)≠0)
    (houter : tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y R)≠⊤) :
    centeredMass (B+S • c) U y r≠0 ∧ centeredMass (B+S • c) U y R≠⊤ := by
  rw [tiltedMass_centered _ _ _ _ _ hd.le] at hinner houter
  refine ⟨fun h =>hinner (by simp [h]),?_⟩
  intro h
  apply houter
  rw [h,ENNReal.mul_top]
  exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hd (Real.exp_pos _))

lemma centeredMass_weight_bound (T T' : Plane) (U : Plane → ℝ) (y : Plane) {r : ℝ}
    : centeredMass T U y r≤
      ENNReal.ofReal (Real.exp (2*‖T-T'‖*r))*centeredMass T' U y r := by
  unfold centeredMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_pow,mul_pow,← Real.exp_nat_mul,← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  rw [← mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have hnorm : ‖x-y‖ ≤ r := by simpa [dist_eq_norm] using (Metric.mem_ball.mp hx).le
  have hi : -inner ℝ (T-T') (x-y)≤‖T-T'‖*r :=
    (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)))
  rw [inner_sub_left] at hi
  linarith

lemma massExcess_log_sub {a b : ℝ≥0∞} (ha0 : a≠0) (hat : a≠⊤) (hb0 : b≠0) (hbt : b≠⊤) :
    massExcess a b=(Real.log a.toReal-Real.log b.toReal)/2 := by
  unfold massExcess
  rw [Real.log_div (ENNReal.toReal_ne_zero.mpr ⟨ha0,hat⟩) (ENNReal.toReal_ne_zero.mpr ⟨hb0,hbt⟩)]

lemma massExcess_weight_bound {a b c d : ℝ≥0∞} {α β : ℝ}
    (ha0 : a≠0) (hat : a≠⊤) (hb0 : b≠0) (hbt : b≠⊤)
    (hc0 : c≠0) (hct : c≠⊤) (hd0 : d≠0) (hdt : d≠⊤)
    (hac : a≤ENNReal.ofReal (Real.exp (2*α))*c)
    (hdb : d≤ENNReal.ofReal (Real.exp (2*β))*b) :
    massExcess a b≤ massExcess c d+α+β := by
  have haa := (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct) hac)
  have hdd := (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbt) hdb)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le] at haa hdd
  have hal := Real.log_le_log (ENNReal.toReal_pos ha0 hat) haa
  have hdl := Real.log_le_log (ENNReal.toReal_pos hd0 hdt) hdd
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ENNReal.toReal_ne_zero.mpr ⟨hc0,hct⟩),Real.log_exp] at hal
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ENNReal.toReal_ne_zero.mpr ⟨hb0,hbt⟩),Real.log_exp] at hdl
  rw [massExcess_log_sub ha0 hat hb0 hbt,massExcess_log_sub hc0 hct hd0 hdt]
  linarith

end SharpNodal.Profiles

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

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma centeredMass_ne_zero_of {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r : ℝ}
    (h : centeredMass T U y r≠0) : centeredMass T' U y r≠0 := by
  intro hz
  have hh := centeredMass_weight_bound T T' U y (r:=r)
  rw [hz,mul_zero] at hh
  exact h (le_antisymm hh bot_le)

lemma centeredMass_ne_top_of {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r : ℝ}
    (h : centeredMass T U y r≠⊤) : centeredMass T' U y r≠⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h)
    (centeredMass_weight_bound T' T U y)

lemma centered_excess_nonneg {T : Plane} {U : Plane → ℝ} {y : Plane} {r R : ℝ}
    (hrR : r ≤ R) (hm0 : centeredMass T U y r≠0) (hmt : centeredMass T U y R≠⊤) :
    0 ≤ massExcess (centeredMass T U y R) (centeredMass T U y r) := by
  have hmono := centeredMass_mono T U y hrR
  have hrt := ne_top_of_le_ne_top hmt hmono
  have hrpos := ENNReal.toReal_pos hm0 hrt
  have hm := ENNReal.toReal_mono hmt hmono
  unfold massExcess
  apply div_nonneg _ (by norm_num)
  apply Real.log_nonneg
  exact (le_div_iff₀ hrpos).mpr (by simpa using hm)

lemma centered_excess_weight_bound {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r R : ℝ}
    (hrR : r ≤ R) (hm0 : centeredMass T U y r≠0) (hmt : centeredMass T U y R≠⊤) :
    massExcess (centeredMass T U y R) (centeredMass T U y r) ≤
      massExcess (centeredMass T' U y R) (centeredMass T' U y r)+(R+r)*‖T-T'‖ := by
  have hmono := centeredMass_mono T U y hrR
  have hmono' := centeredMass_mono T' U y hrR
  have hm0' : centeredMass T' U y r≠0 := centeredMass_ne_zero_of hm0
  have hmt' : centeredMass T' U y R≠⊤ := centeredMass_ne_top_of hmt
  have hR0 := ne_of_gt ((pos_iff_ne_zero.mpr hm0).trans_le hmono)
  have hR0' := ne_of_gt ((pos_iff_ne_zero.mpr hm0').trans_le hmono')
  have hrt := ne_top_of_le_ne_top hmt hmono
  have hrt' := ne_top_of_le_ne_top hmt' hmono'
  have hh := massExcess_weight_bound (α:=‖T-T'‖*R) (β:=‖T-T'‖*r)
    hR0 hmt hm0 hrt hR0' hmt' hm0' hrt'
    (by simpa only [mul_assoc] using centeredMass_weight_bound T T' U y (r:=R))
    (by simpa only [norm_sub_rev,mul_assoc] using centeredMass_weight_bound T' T U y (r:=r))
  nlinarith only [hh]

lemma normalized_inner_rate_eq {S : ℝ} {B : Plane} {U : Plane → ℝ} {Ω G : Set Plane}
    (hGΩ : G⊆Ω) (hm0 : tiltedMass S B U 1 0 G≠0) (hmt : tiltedMass S B U 1 0 Ω≠⊤) :
    logRate S (tiltedMass S B U (tiltedMass S B U 1 0 Ω).toReal⁻¹ 0 G)=
      ((-massExcess (tiltedMass S B U 1 0 Ω) (tiltedMass S B U 1 0 G)/S:ℝ):EReal) := by
  let a := tiltedMass S B U 1 0 Ω
  let b := tiltedMass S B U 1 0 G
  have hba : b ≤ a := tiltedMass_mono_set _ _ _ _ _ hGΩ
  have ha0 : a≠0 := ne_of_gt ((pos_iff_ne_zero.mpr hm0).trans_le hba)
  have hbt : b≠⊤ := ne_top_of_le_ne_top hmt hba
  have ha : 0<a.toReal := ENNReal.toReal_pos ha0 hmt
  have hb : 0<b.toReal := ENNReal.toReal_pos hm0 hbt
  have heq : tiltedMass S B U a.toReal⁻¹ 0 G=ENNReal.ofReal a.toReal⁻¹*b := by
    simpa using tiltedMass_const_mul S B U a.toReal⁻¹ 1 (inv_pos.mpr ha).le 0 G
  rw [heq,logRate_real (mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ha)) hm0)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbt),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_pos.mpr ha).le]
  congr 1
  change Real.log (a.toReal⁻¹*b.toReal)/(2*S)= -massExcess a b/S
  rw [massExcess_log_sub ha0 hmt hm0 hbt,Real.log_mul (inv_ne_zero (ne_of_gt ha)) (ne_of_gt hb),Real.log_inv]
  ring

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma tiltedMass_zero_center (S : ℝ) (B : Plane) (U : Plane → ℝ) (d r : ℝ)
    (hd : 0≤d) :
    tiltedMass S B U d 0 (Metric.ball 0 r)=ENNReal.ofReal d*centeredMass B U 0 r := by
  change tiltedMass S B U d (fun _ => 0) (Metric.ball 0 r)=_
  simpa using tiltedMass_centered S B 0 U d hd 0 r

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Descent
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

namespace SharpNodal.Profiles
open Carleman

lemma profile_zero_of_inner_rate {V : Plane → EReal} {S d : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hV : UpperSemicontinuous V) (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x ≤ 0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hS : ∀j,0<S j)
    (hinner : Tendsto (fun j =>logRate (S j)
      (tiltedMass (S j) (B j) (U j) (d j) 0 (Metric.ball 0 1))) atTop (𝓝 0)) :
    ∀x∈Metric.ball (0:Plane) 1000,V x=0 := by
  have hsub : Metric.closedBall (0:Plane) 1 ⊆ Metric.ball 0 1000 :=
    Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨a,ha,hmax⟩ := (hV.upperSemicontinuousOn (Metric.closedBall 0 1)).exists_isMaxOn
    ⟨0,Metric.mem_closedBall_self (by norm_num)⟩ (isCompact_closedBall 0 1)
  have hu := hp.upper 0 continuousOn_const _ (isCompact_closedBall 0 1) hsub
  have hl := limsup_le_limsup (f := atTop) (Eventually.of_forall (fun j =>
    logRate_mono (hS j) (tiltedMass_mono_set (S j) (B j) (U j) (d j) 0 (Metric.ball_subset_closedBall (x := (0:Plane)) (ε := 1)))))
  rw [hinner.limsup_eq] at hl
  have hmax' : (⨆x∈Metric.closedBall (0:Plane) 1,V x+(0:EReal)) ≤ V a :=
    iSup₂_le (fun x hx =>by simpa using hmax hx)
  have ha0 : V a=0 := le_antisymm (hneg a (hsub ha)) (hl.trans (hu.trans (by simpa using hmax')))
  exact profile_strong_maximum Metric.isOpen_ball (convex_ball (0:Plane) 1000).isPreconnected
    hV hneg htest (hsub ha) ha0

lemma tiltedMass_linear_centered (S : ℝ) (B e : Plane) (U : Plane → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (r : ℝ) :
    tiltedMass S B U d (fun x =>inner ℝ e x) (Metric.ball 0 r)=
      ENNReal.ofReal d*centeredMass (B-S • e) U 0 r := by
  simpa only [sub_zero,inner_neg_left,neg_neg,inner_zero_right,mul_zero,neg_zero,
    Real.exp_zero,mul_one,smul_neg,← sub_eq_add_neg] using
    tiltedMass_centered S B (-e) U d hd 0 r

lemma zero_profile_forces_growth {V : Plane → EReal} {S d : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hzero : ∀x∈Metric.ball (0:Plane) 1000,V x=0)
    (hS : ∀j,0<S j) (hd : ∀j,0<d j)
    (hm0 : ∀j,centeredMass (B j) (U j) 0 1≠0)
    (hmt : ∀j,centeredMass (B j) (U j) 0 1000≠⊤)
    {e : Plane} (he : ‖e‖=1) :
    ∀ᶠj in atTop, 1 <
      massExcess (centeredMass (B j-S j • e) (U j) 0 1000)
        (centeredMass (B j-S j • e) (U j) 0 1)/S j := by
  let f : Plane → ℝ := fun x => inner ℝ e x
  have hf : Continuous f := continuous_const.inner continuous_id
  have hF : Metric.closedBall (0:Plane) 1 ⊆ Metric.ball 0 1000 :=
    Metric.closedBall_subset_ball (by norm_num)
  have hG : Metric.ball (0:Plane) 4 ⊆ Metric.ball 0 1000 :=
    Metric.ball_subset_ball (by norm_num)
  have hu := hp.upper f hf.continuousOn _ (isCompact_closedBall 0 1) hF
  have hl := hp.lower f hf.continuousOn _ Metric.isOpen_ball hG
  have hup : (⨆x∈Metric.closedBall (0:Plane) 1,V x+(f x:EReal)) ≤ (1:EReal) := by
    apply iSup₂_le
    intro x hx
    rw [hzero x (hF hx),zero_add]
    apply EReal.coe_le_coe_iff.mpr
    have hh : ‖x‖ ≤ 1 := by simpa using hx
    calc
      inner ℝ e x ≤ ‖e‖*‖x‖ := real_inner_le_norm _ _
      _ ≤ 1 := by simpa [he] using hh
  have hlow : (3:EReal) ≤ (⨆x∈Metric.ball (0:Plane) 4,V x+(f x:EReal)) := by
    have hx : (3:ℝ) • e∈Metric.ball (0:Plane) 4 := by
      norm_num [Metric.mem_ball,norm_smul,dist_zero_right,he]
    apply le_iSup₂_of_le ((3:ℝ) • e) hx
    rw [hzero _ (hG hx),zero_add]
    have hval : f ((3:ℝ) • e)=3 := by
      simp only [f,inner_smul_right,real_inner_self_eq_norm_sq,he,one_pow,mul_one]
    rw [hval]
    rfl
  have huu := eventually_lt_of_limsup_lt ((hu.trans hup).trans_lt (EReal.coe_lt_coe_iff.mpr (by norm_num : (1:ℝ) < 3/2)))
  have hll := eventually_lt_of_lt_liminf ((EReal.coe_lt_coe_iff.mpr (by norm_num : (5/2:ℝ) < 3)).trans_le (hlow.trans hl))
  filter_upwards [huu,hll] with j hjU hjL
  let T : Plane := B j-S j • e
  let a := tiltedMass (S j) (B j) (U j) (d j) f (Metric.ball 0 1000)
  let b := tiltedMass (S j) (B j) (U j) (d j) f (Metric.ball 0 1)
  have hbU : logRate (S j) b<((3/2:ℝ):EReal) :=
    (logRate_mono (hS j) (tiltedMass_mono_set _ _ _ _ _ Metric.ball_subset_closedBall)).trans_lt hjU
  have haL : ((5/2:ℝ):EReal)<logRate (S j) a := hjL.trans_le
    (logRate_mono (hS j) (tiltedMass_mono_set _ _ _ _ _ (Metric.ball_subset_ball (by norm_num))))
  have hT0 : centeredMass T (U j) 0 1≠0 := centeredMass_ne_zero_of (hm0 j)
  have hTt : centeredMass T (U j) 0 1000≠⊤ := centeredMass_ne_top_of (hmt j)
  have hab := centeredMass_mono T (U j) 0 (show (1:ℝ) ≤ 1000 by norm_num)
  have ha0 : a≠0 := by
    rw [show a=ENNReal.ofReal (d j)*centeredMass T (U j) 0 1000 from
      tiltedMass_linear_centered _ _ _ _ (hd j).le _]
    exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (hd j))
      (ne_of_gt ((pos_iff_ne_zero.mpr hT0).trans_le hab))
  have hat : a≠⊤ := by
    rw [show a=ENNReal.ofReal (d j)*centeredMass T (U j) 0 1000 from
      tiltedMass_linear_centered _ _ _ _ (hd j).le _]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTt
  have hb0 : b≠0 := by
    rw [show b=ENNReal.ofReal (d j)*centeredMass T (U j) 0 1 from
      tiltedMass_linear_centered _ _ _ _ (hd j).le _]
    exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (hd j)) hT0
  have hbt : b≠⊤ := ne_top_of_le_ne_top hat
    (tiltedMass_mono_set _ _ _ _ _ (Metric.ball_subset_ball (by norm_num)))
  rw [logRate_real ha0 hat] at haL
  rw [logRate_real hb0 hbt] at hbU
  have hexc : 1 < massExcess a b/S j := by
    rw [massExcess_div (hS j).ne' ha0 hat hb0 hbt]
    have h1 := EReal.coe_lt_coe_iff.mp haL
    have h2 := EReal.coe_lt_coe_iff.mp hbU
    linarith
  have heq : massExcess a b=massExcess (centeredMass T (U j) 0 1000) (centeredMass T (U j) 0 1) := by
    dsimp only [a,b,f]
    rw [tiltedMass_linear_centered _ _ _ _ (hd j).le,tiltedMass_linear_centered _ _ _ _ (hd j).le]
    exact massExcess_mul_left _ _ _ (ENNReal.ofReal_ne_zero_iff.mpr (hd j)) ENNReal.ofReal_ne_top
  rw [heq] at hexc
  exact hexc

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma zero_profile_tilt_contradiction {V : Plane → EReal} {S d : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hzero : ∀x∈Metric.ball (0:Plane) 1000,V x=0)
    (hS : ∀j,0<S j) (hd : ∀j,0<d j) (hB : ∀j,‖B j‖=S j)
    (hm0 : ∀j,centeredMass (B j) (U j) 0 1≠0)
    (hmt : ∀j,centeredMass (B j) (U j) 0 1000≠⊤)
    (hsmall : Tendsto (fun j =>massExcess (centeredMass 0 (U j) 0 1000)
      (centeredMass 0 (U j) 0 1)/S j) atTop (𝓝 0)) : False := by
  let e : ℕ → Plane := fun j =>(S j)⁻¹ • B j
  have henorm (j : ℕ) : ‖e j‖=1 := by
    simp [e,norm_smul,Real.norm_eq_abs,abs_of_pos (hS j),hB,inv_mul_cancel₀ (hS j).ne']
  obtain ⟨v,_hv,φ,hφ,hlim⟩ := (isCompact_closedBall (0:Plane) 1).tendsto_subseq
    (fun j =>show e j∈Metric.closedBall (0:Plane) 1 by simp [Metric.mem_closedBall,dist_zero_right,henorm])
  have hvnorm : ‖v‖=1 := tendsto_nhds_unique hlim.norm
    (by simpa only [Function.comp_apply,henorm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ =>(1:ℝ)) atTop (𝓝 1)))
  have hgrowth := zero_profile_forces_growth (hp.subseq hφ.tendsto_atTop) hzero
    (fun j =>hS (φ j)) (fun j =>hd (φ j)) (fun j =>hm0 (φ j)) (fun j =>hmt (φ j)) hvnorm
  have hres (j : ℕ) : ‖B (φ j)-S (φ j) • v‖=S (φ j)*‖e (φ j)-v‖ := by
    rw [show B (φ j)-S (φ j) • v=S (φ j) • (e (φ j)-v) by
      simp [e,smul_sub,smul_inv_smul₀ (hS (φ j)).ne'],norm_smul,
      Real.norm_eq_abs,abs_of_pos (hS (φ j))]
  have hupper (j : ℕ) :
      massExcess (centeredMass (B (φ j)-S (φ j) • v) (U (φ j)) 0 1000)
        (centeredMass (B (φ j)-S (φ j) • v) (U (φ j)) 0 1)/S (φ j) ≤
      massExcess (centeredMass 0 (U (φ j)) 0 1000)
        (centeredMass 0 (U (φ j)) 0 1)/S (φ j)+1001*‖e (φ j)-v‖ := by
    have hh := centered_excess_weight_bound (T:=B (φ j)-S (φ j) • v) (T':=0)
      (show (1:ℝ) ≤ 1000 by norm_num) (centeredMass_ne_zero_of (hm0 (φ j)))
      (centeredMass_ne_top_of (hmt (φ j)))
    simp only [sub_zero,hres] at hh
    have hh' := div_le_div_of_nonneg_right hh (hS (φ j)).le
    convert hh' using 1 <;> first | rfl | (field_simp [(hS (φ j)).ne']; ring)
  have hright : Tendsto (fun j =>massExcess (centeredMass 0 (U (φ j)) 0 1000)
      (centeredMass 0 (U (φ j)) 0 1)/S (φ j)+1001*‖e (φ j)-v‖) atTop (𝓝 0) := by
    simpa using (hsmall.comp hφ.tendsto_atTop).add
      ((tendsto_const_nhds (x:=(1001:ℝ))).mul (hlim.sub (tendsto_const_nhds (x:=v))).norm)
  have hlt := hright.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨j,hjG,hjU⟩ := (hgrowth.and hlt).exists
  have := hupper j
  exact (not_lt_of_ge (this.trans hjU.le)) hjG

theorem sequence_large_slope_impossible
    (p U : ℕ → Plane → ℝ) (B : ℕ → Plane) (S K err : ℕ → ℝ) (Cp : ℝ)
    (hp : ∀j,ContDiffOn ℝ ∞ (p j) (Metric.ball 0 1000))
    (hU : ∀j,ContDiffOn ℝ ∞ (U j) (Metric.ball 0 1000))
    (hS : ∀j,0<S j) (hSinf : Tendsto S atTop atTop) (hB : ∀j,‖B j‖=S j)
    (hK : Tendsto (fun j =>K j/(S j+‖B j‖)) atTop (𝓝 0))
    (hpb : ∀j x,x∈Metric.ball (0:Plane) 1000 → |p j x|≤Cp)
    (herr : Tendsto err atTop (𝓝 0))
    (hpd : ∀j i x,x∈Metric.ball (0:Plane) 1000 →
      |(K j)^2*coordPartial (p j) i x/(S j*(S j+‖B j‖))|≤err j)
    (hPDE : ∀j x,x∈Metric.ball (0:Plane) 1000 →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (hm0 : ∀j,centeredMass (B j) (U j) 0 1≠0)
    (hmt : ∀j,centeredMass (B j) (U j) 0 1000≠⊤)
    (htilt : Tendsto (fun j =>massExcess (centeredMass (B j) (U j) 0 1000)
      (centeredMass (B j) (U j) 0 1)/S j) atTop (𝓝 0))
    (hsmall : Tendsto (fun j =>massExcess (centeredMass 0 (U j) 0 1000)
      (centeredMass 0 (U j) 0 1)/S j) atTop (𝓝 0)) : False := by
  let d : ℕ → ℝ := fun j =>(tiltedMass (S j) (B j) (U j) 1 0 (Metric.ball 0 1000)).toReal⁻¹
  have hmass (j : ℕ) (r : ℝ) : tiltedMass (S j) (B j) (U j) 1 0 (Metric.ball 0 r)=
      centeredMass (B j) (U j) 0 r := by
    simpa using tiltedMass_zero_center (S j) (B j) (U j) 1 r (by norm_num)
  have hnorm (j : ℕ) : 0<d j ∧ tiltedMass (S j) (B j) (U j) (d j) 0 (Metric.ball 0 1000)=1 := by
    apply tiltedMass_normalized
    · rw [hmass]
      exact ne_of_gt ((pos_iff_ne_zero.mpr (hm0 j)).trans_le
        (centeredMass_mono _ _ _ (by norm_num : (1:ℝ)≤1000)))
    · simpa only [hmass] using hmt j
  obtain ⟨V,φ,hφ,hV,hneg,hprof⟩ := extract_tilted_profile Metric.isOpen_ball S B U d
    hS hSinf (fun j =>(hU j).continuousOn) (fun j =>(hnorm j).2.le)
  have htest := full_test_of_profile Metric.isOpen_ball (fun j =>hp (φ j))
    (fun j =>hU (φ j)) (fun j =>hS (φ j)) (hSinf.comp hφ.tendsto_atTop)
    (fun j =>(hnorm (φ j)).1) (hK.comp hφ.tendsto_atTop) (fun j =>hpb (φ j))
    (herr.comp hφ.tendsto_atTop) (fun j =>hpd (φ j)) (fun j =>hPDE (φ j))
    (hV.upperSemicontinuousOn _) hprof
  have hinner : Tendsto (fun j =>logRate (S j)
      (tiltedMass (S j) (B j) (U j) (d j) 0 (Metric.ball 0 1))) atTop (𝓝 0) := by
    have heq (j : ℕ) := normalized_inner_rate_eq (S:=S j) (B:=B j) (U:=U j)
      (Metric.ball_subset_ball (x:=(0:Plane)) (by norm_num : (1:ℝ)≤1000))
      (by simpa only [hmass] using hm0 j) (by simpa only [hmass] using hmt j)
    simp only [hmass,neg_div] at heq
    simp_rw [show ∀j,logRate (S j) (tiltedMass (S j) (B j) (U j) (d j) 0 (Metric.ball 0 1))=
      ((-(massExcess (centeredMass (B j) (U j) 0 1000) (centeredMass (B j) (U j) 0 1)/S j):ℝ):EReal)
      from fun j =>by simpa only [d,hmass] using heq j]
    simpa using EReal.tendsto_coe.mpr htilt.neg
  have hzero := profile_zero_of_inner_rate hV (fun x _ =>hneg x) htest hprof
    (fun j =>hS (φ j)) (hinner.comp hφ.tendsto_atTop)
  exact zero_profile_tilt_contradiction hprof hzero (fun j =>hS (φ j))
    (fun j =>(hnorm (φ j)).1) (fun j =>hB (φ j)) (fun j =>hm0 (φ j))
    (fun j =>hmt (φ j)) (hsmall.comp hφ.tendsto_atTop)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma UnitWave.excess_nonneg {Cp a₀ : ℝ} (D : UnitWave Cp a₀) (b : Plane) :
    0≤D.excess b :=
  centered_excess_nonneg (by norm_num) (centeredMass_ne_zero_of D.inner_nonzero)
    (centeredMass_ne_top_of D.outer_finite)

theorem large_slope_forces_growth {Cp a₀ : ℝ} (hCp : 0≤Cp) (ha₀ : 0<a₀)
    (L : ℝ) (hL : 0≤L) :
    ∃Bstar η : ℝ,1≤Bstar ∧ 0<η ∧ ∀(D : UnitWave Cp a₀) (b : Plane),
      Bstar≤‖b‖ → D.growth b≤η*‖b‖ → L<D.growth 0 := by
  by_contra hn
  push Not at hn
  have hf (j : ℕ) := hn ((j:ℝ)+1) ((j:ℝ)+1)⁻¹ (by have := Nat.cast_nonneg (α:=ℝ) j; linarith) (by positivity)
  choose D b hb hg hbad using hf
  let n : ℕ → ℝ := fun j =>(j:ℝ)+1
  let S : ℕ → ℝ := fun j =>(D j).K*‖b j‖
  let B : ℕ → Plane := fun j =>(D j).K • b j
  have hnpos (j : ℕ) : 0<n j := by dsimp [n]; positivity
  have hn1 (j : ℕ) : 1≤n j := by dsimp [n]; have := Nat.cast_nonneg (α:=ℝ) j; linarith
  have hKpos (j : ℕ) : 0<(D j).K := ha₀.trans_le (D j).frequency_lower
  have hbpos (j : ℕ) : 0<‖b j‖ := (hnpos j).trans_le (hb j)
  have hSpos (j : ℕ) : 0<S j := mul_pos (hKpos j) (hbpos j)
  have hB (j : ℕ) : ‖B j‖=S j := by
    simp only [B,S,norm_smul,Real.norm_eq_abs,abs_of_pos (hKpos j)]
  have hT : Tendsto n atTop atTop :=
    tendsto_atTop_mono (fun _ =>le_add_of_nonneg_right (by norm_num)) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun j =>(n j)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hT
  have hSinf : Tendsto S atTop atTop := by
    apply tendsto_atTop_mono _ (hT.const_mul_atTop ha₀)
    intro j
    exact mul_le_mul (D j).frequency_lower (hb j) (hnpos j).le (hKpos j).le
  have hratio (j : ℕ) : (D j).K/(S j+‖B j‖)=1/(2*‖b j‖) := by
    rw [hB]
    dsimp [S]
    field_simp [(hKpos j).ne', (hbpos j).ne']
    ring
  have hratioBound (j : ℕ) : |(D j).K/(S j+‖B j‖)|≤(n j)⁻¹ := by
    rw [hratio,abs_of_pos (one_div_pos.mpr (mul_pos (by norm_num) (hbpos j))),one_div]
    exact inv_anti₀ (hnpos j) (by linarith [hb j])
  have hratioLim : Tendsto (fun j =>(D j).K/(S j+‖B j‖)) atTop (𝓝 0) :=
    squeeze_zero_norm (by simpa only [Real.norm_eq_abs] using hratioBound) hinv
  have herrLim : Tendsto (fun j =>Cp*(n j)⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul Cp
  have hgrad (j : ℕ) (i : Fin 2) (x : Plane) (hx : x∈Metric.ball (0:Plane) 1000) :
      |(D j).K^2*coordPartial (D j).p i x/(S j*(S j+‖B j‖))|≤Cp*(n j)⁻¹ := by
    have heq : (D j).K^2*coordPartial (D j).p i x/(S j*(S j+‖B j‖))=
        coordPartial (D j).p i x/(2*‖b j‖^2) := by
      rw [hB]
      dsimp [S]
      field_simp [(hKpos j).ne', (hbpos j).ne']
      ring
    rw [heq,abs_div,abs_of_pos (mul_pos (by norm_num) (sq_pos_of_pos (hbpos j)))]
    calc
      _ ≤ Cp/(2*‖b j‖^2) := div_le_div_of_nonneg_right ((D j).derivative_bound i x hx) (by positivity)
      _ ≤ Cp/(n j) := div_le_div_of_nonneg_left hCp (hnpos j) (by nlinarith [hb j,hn1 j])
      _ = _ := div_eq_mul_inv _ _
  have htilt : Tendsto (fun j =>(D j).excess (b j)/S j) atTop (𝓝 0) := by
    apply squeeze_zero _ _ hinv
    · intro j
      exact div_nonneg ((D j).excess_nonneg _) (hSpos j).le
    · intro j
      have hh := (div_le_iff₀ (hbpos j)).mpr (hg j)
      change (D j).excess (b j)/((D j).K*‖b j‖)≤(n j)⁻¹
      simpa only [UnitWave.growth,div_div] using hh
  have huntilt : Tendsto (fun j =>(D j).excess 0/S j) atTop (𝓝 0) := by
    have hlim : Tendsto (fun j =>L*(n j)⁻¹) atTop (𝓝 0) := by simpa using hinv.const_mul L
    apply squeeze_zero _ _ hlim
    · intro j
      exact div_nonneg ((D j).excess_nonneg _) (hSpos j).le
    · intro j
      change (D j).excess 0/((D j).K*‖b j‖)≤_
      rw [← div_div]
      exact (div_le_div_of_nonneg_right (hbad j) (hbpos j).le).trans
        (by simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_left hL (hnpos j) (hb j))
  apply sequence_large_slope_impossible (fun j =>(D j).p) (fun j =>(D j).U) B S
    (fun j =>(D j).K) (fun j =>Cp*(n j)⁻¹) Cp
    (fun j =>(D j).smooth_p) (fun j =>(D j).smooth_U) hSpos hSinf hB hratioLim
    (fun j =>(D j).coefficient_bound) herrLim hgrad (fun j =>(D j).equation)
    (fun j =>centeredMass_ne_zero_of (T':=B j) (D j).inner_nonzero)
    (fun j =>centeredMass_ne_top_of (T':=B j) (D j).outer_finite) htilt
  simpa only [UnitWave.excess,smul_zero] using huntilt

end SharpNodal.Profiles
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_StoppedTrees
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

namespace SharpNodal.Descent

namespace Tree
variable {ι : Type*} [Fintype ι]

lemma mass_nonneg {C : ℝ} {t : Tree ι} (h : Valid C t) : 0 ≤ t.root.mass := by
  cases t <;> exact h.1

lemma cost_nonneg {C : ℝ} {t : Tree ι} (h : Valid C t) :
    0 ≤ t.massCost ∧ 0 ≤ t.tiltCost ∧ 0 ≤ t.floorCost := by
  induction t with
  | stop a => exact ⟨h.1,le_rfl,le_rfl⟩
  | step a t ih =>
    refine ⟨add_nonneg h.1 (Finset.expect_nonneg (fun i _ =>(ih i (h.2.2.2.2 i)).1)),?_,?_⟩
    · exact Finset.expect_nonneg (fun i _ =>add_nonneg (norm_nonneg _) (ih i (h.2.2.2.2 i)).2.1)
    · exact add_nonneg h.2.1 (Finset.expect_nonneg (fun i _ =>(ih i (h.2.2.2.2 i)).2.2))

theorem stopped_descent {C : ℝ} (hC : 0 ≤ C) {t : Tree ι} (h : Valid C t) :
    t.massCost ≤ 2*t.root.mass+t.floorCost ∧
    t.tiltCost ≤ 2*C*t.root.mass+2*C*t.floorCost := by
  induction t with
  | stop a =>
    dsimp [massCost,tiltCost,floorCost,root]
    constructor
    · linarith [h.1]
    · have hm := h.1
      positivity
  | step a t ih =>
    have hm := Finset.expect_le_expect (fun i (_ : i∈(Finset.univ : Finset ι)) =>
      (ih i (h.2.2.2.2 i)).1)
    have ht := Finset.expect_le_expect (fun i (_ : i∈(Finset.univ : Finset ι)) =>
      (ih i (h.2.2.2.2 i)).2)
    simp only [Finset.expect_add_distrib,← Finset.mul_expect] at hm ht
    have hs := h.2.2.1
    have hi := h.2.2.2.1
    change a.mass + (𝔼 i, massCost (t i)) ≤ 2*a.mass+(a.floor+(𝔼 i, floorCost (t i))) ∧
      (𝔼 i, (‖(root (t i)).tilt-a.tilt‖+tiltCost (t i))) ≤
        2*C*a.mass+2*C*(a.floor+(𝔼 i, floorCost (t i)))
    rw [Finset.expect_add_distrib]
    constructor
    · linarith
    · nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ)≤2) hC)]

lemma stopped_total_cost {C F : ℝ} (hC : 0 ≤ C) {t : Tree ι} (h : Valid C t)
    (hF : t.floorCost ≤ F) :
    t.massCost+t.tiltCost ≤ 2*(1+C)*t.root.mass+(1+2*C)*F := by
  obtain ⟨hm,ht⟩ := stopped_descent hC h
  nlinarith [mul_le_mul_of_nonneg_left hF (by positivity : (0:ℝ)≤1+2*C)]

lemma stopped_total_uniform {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    {t : Tree ι} (h : Valid C t) (hfloor : t.floorCost ≤ F) :
    t.massCost+t.tiltCost ≤ (2*(1+C)+(1+2*C)*F)*(t.root.mass+1) := by
  have hh := stopped_total_cost hC h hfloor
  have hm := mass_nonneg h
  nlinarith [mul_nonneg (mul_nonneg (show 0≤1+2*C by positivity) hF) hm]

end Tree
end SharpNodal.Descent

noncomputable section
open scoped BigOperators
namespace SharpNodal.Descent.Tree
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem failure_cost {C δ : ℝ} (_hδ : 0<δ) (b₀ : Plane) {t : Tree ι}
    (h : Valid C t) :
    δ*(1-goodProb (fun a => a.mass<δ ∧ ‖a.tilt-b₀‖<δ) t) ≤
      t.massCost+t.tiltCost+‖t.root.tilt-b₀‖ := by
  classical
  induction t with
  | stop a =>
    change δ*(1-(if a.mass<δ ∧ ‖a.tilt-b₀‖<δ then 1 else 0)) ≤ a.mass+0+‖a.tilt-b₀‖
    split
    · have hm := h.1
      simp only [sub_self,mul_zero,add_zero]
      positivity
    · rename_i hn
      push Not at hn
      have hn' : δ≤a.mass ∨ δ≤‖a.tilt-b₀‖ := by
        by_cases hm : δ≤a.mass
        · exact Or.inl hm
        · exact Or.inr (hn (lt_of_not_ge hm))
      simp only [sub_zero,mul_one,add_zero]
      rcases hn' with hh|hh <;> linarith [h.1,norm_nonneg (a.tilt-b₀)]
  | step a t ih =>
    change δ*(1-(if a.mass<δ ∧ ‖a.tilt-b₀‖<δ then
      𝔼 i, goodProb (fun a => a.mass<δ ∧ ‖a.tilt-b₀‖<δ) (t i) else 0)) ≤ _
    split
    · have hb (i : ι) := ih i (h.2.2.2.2 i)
      have hn (i : ι) : ‖(t i).root.tilt-b₀‖ ≤ ‖(t i).root.tilt-a.tilt‖+‖a.tilt-b₀‖ :=
        calc
          _ = ‖((t i).root.tilt-a.tilt)+(a.tilt-b₀)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have hh := Finset.expect_le_expect (s:=Finset.univ) (fun i _ =>
        show δ*(1-goodProb (fun a => a.mass<δ ∧ ‖a.tilt-b₀‖<δ) (t i)) ≤
          (t i).massCost+(t i).tiltCost+(‖(t i).root.tilt-a.tilt‖+‖a.tilt-b₀‖) by
            linarith [hb i,hn i])
      simp only [mul_sub,Finset.expect_sub_distrib,Finset.expect_add_distrib,
        ←Finset.mul_expect,Fintype.expect_const] at hh
      change _ ≤ a.mass+(𝔼 i, massCost (t i))+
        (𝔼 i, (‖(t i).root.tilt-a.tilt‖+tiltCost (t i)))+‖a.tilt-b₀‖
      rw [Finset.expect_add_distrib]
      linarith [h.1]
    · rename_i hn
      push Not at hn
      have hn' : δ≤a.mass ∨ δ≤‖a.tilt-b₀‖ := by
        by_cases hm : δ≤a.mass
        · exact Or.inl hm
        · exact Or.inr (hn (lt_of_not_ge hm))
      have hc := cost_nonneg h
      have hm : a.mass ≤ massCost (Tree.step a t) := by
        change a.mass≤a.mass+(𝔼 i, massCost (t i))
        exact le_add_of_nonneg_right (Finset.expect_nonneg (fun i _ =>(cost_nonneg (h.2.2.2.2 i)).1))
      change δ*(1-0) ≤ _
      simp only [sub_zero,mul_one]
      change _ ≤ _+_+‖a.tilt-b₀‖
      rcases hn' with hh|hh <;> linarith [norm_nonneg (a.tilt-b₀)]

theorem stable_probability {C F γ B σ : ℝ} (hC : 0≤C) (hF : 0≤F)
    (hγ : 0<γ) (hB : 0<B) (hσ : 0≤σ) {t : Tree ι} (h : Valid C t)
    (hfloor : t.floorCost≤F) (hm : t.root.mass≤σ*B)
    (hsmall : (2*(1+C)+(1+2*C)*F)*(σ+1/B)≤γ/4) :
    (3:ℝ)/4 ≤ goodProb (fun a => a.mass<γ*B ∧ ‖a.tilt-t.root.tilt‖<γ*B) t := by
  classical
  have hc := stopped_total_uniform hC hF h hfloor
  have hf := failure_cost (mul_pos hγ hB) t.root.tilt h
  rw [sub_self,norm_zero,add_zero] at hf
  have hCt : 0≤2*(1+C)+(1+2*C)*F := by positivity
  have hh := mul_le_mul_of_nonneg_left hm hCt
  have hs := mul_le_mul_of_nonneg_right hsmall hB.le
  have hs' : (2*(1+C)+(1+2*C)*F)*(σ*B+1)≤γ/4*B := by
    calc
      _ = (2*(1+C)+(1+2*C)*F)*(σ+1/B)*B := by field_simp
      _ ≤ _ := hs
  have hpos : 0<γ*B := mul_pos hγ hB
  nlinarith only [hc,hf,hh,hs',hpos]

end SharpNodal.Descent.Tree

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Persistence
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

noncomputable section
open scoped Topology
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma profile_nonconstant_of_positive_gap {V : Plane → EReal} {S d : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (_hV : UpperSemicontinuous V) (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤ V a)
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hS : ∀j,0< S j) {F G E : Set Plane}
    (hF : IsCompact F) (hF2 : F⊆Metric.ball (0:Plane) 2)
    (hG : IsOpen G) (hGn : G.Nonempty) (hGE : G⊆E) (hEF : E⊆F)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀j,δ≤ massExcess (tiltedMass (S j) (B j) (U j) (d j) 0 E)
      (tiltedMass (S j) (B j) (U j) (d j) 0 G)/S j) :
    ∃x∈Metric.ball (0:Plane) 2,∃y∈Metric.ball (0:Plane) 2,V x≠V y := by
  by_contra hn
  push Not at hn
  obtain ⟨a,ha,hVa⟩ := hanchor
  have ha2 : a∈Metric.ball (0:Plane) 2 := Metric.closedBall_subset_ball (by norm_num) ha
  have h21000 : Metric.ball (0:Plane) 2⊆Metric.ball 0 1000 := Metric.ball_subset_ball (by norm_num)
  have hfin : V a≠⊤ ∧ V a≠⊥ := ⟨ne_top_of_le_ne_top (by simp) (hneg a (h21000 ha2)),
    ne_bot_of_le_ne_bot (by exact EReal.coe_ne_bot (-1)) hVa⟩
  let c := (V a).toReal
  have hea : V a=(c:EReal) := (EReal.coe_toReal hfin.1 hfin.2).symm
  have he (x : Plane) (hx : x∈Metric.ball (0:Plane) 2) : V x=(c:EReal) := (hn x hx a ha2).trans hea
  have hG2 := (hGE.trans hEF).trans hF2
  have hsup : (⨆x∈G,V x+((0:ℝ):EReal))=(c:EReal) := by
    apply le_antisymm
    · exact iSup₂_le (fun x hx => by simp only [he x (hG2 hx),EReal.coe_zero,add_zero,le_refl])
    · obtain ⟨x,hx⟩ := hGn
      exact le_iSup₂_of_le x hx (by simp only [he x (hG2 hx),EReal.coe_zero,add_zero,le_refl])
  have hsupF : (⨆x∈F,V x+((0:ℝ):EReal))≤((c+(0:ℝ):ℝ):EReal) :=
    iSup₂_le (fun x hx => by simp only [he x (hF2 hx),EReal.coe_zero,add_zero,le_refl])
  have ht := profile_massExcess_transfer hp hS continuousOn_const hF (hF2.trans h21000)
    hG (hG2.trans h21000) hGE hEF (half_pos hδ) hsup hsupF
  obtain ⟨j,hj⟩ := ht.exists
  have hlow := hgap j
  have hupper := hj.2.2
  change massExcess (tiltedMass (S j) (B j) (U j) (d j) 0 E)
    (tiltedMass (S j) (B j) (U j) (d j) 0 G)/S j<0+δ/2 at hupper
  linarith

lemma local_affine_profile_transfer {V : Plane → EReal} {S d : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤ V a)
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hS : ∀j,0< S j) (hd : ∀j,0< d j)
    {R r σ e : ℝ} {y c : Plane} (hR : 1≤ R) (hr : 0< r) (hc : 0<‖c‖)
    (hsmall : ‖y‖+2*R*r<3) (he : e<σ*r*‖c‖)
    (hgap : (⨆x∈Metric.closedBall y (R*r),V x-(inner ℝ c (x-y):EReal))≤
      (⨆x∈Metric.ball y r,V x-(inner ℝ c (x-y):EReal))+(e:EReal)) :
    ∀ᶠj in atTop,
      centeredMass (B j+S j • c) (U j) y r≠0 ∧
      centeredMass (B j+S j • c) (U j) y (R*r)≠⊤ ∧
      massExcess (centeredMass (B j+S j • c) (U j) y (R*r))
        (centeredMass (B j+S j • c) (U j) y r)/(S j*r*‖c‖)<σ := by
  have hrR : r≤ R*r := by nlinarith
  have hF3 : Metric.closedBall y (R*r)⊆Metric.ball (0:Plane) 3 := by
    intro x hx
    have hx' : ‖x-y‖≤ R*r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have hn : ‖x‖≤‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
    simp only [Metric.mem_ball,dist_zero_right]
    nlinarith
  have hG3 := ((Metric.ball_subset_ball hrR).trans Metric.ball_subset_closedBall).trans hF3
  have h3R : Metric.ball (0:Plane) 3⊆Metric.ball 0 1000 := Metric.ball_subset_ball (by norm_num)
  let f : Plane → ℝ := fun x =>-inner ℝ c (x-y)
  have hf : Continuous f := (continuous_const.inner (continuous_id.sub continuous_const)).neg
  have hfbd : ∀x∈Metric.ball y r,f x≤‖c‖*r := by
    intro x hx
    have hh : ‖x-y‖< r := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    exact (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hh.le (norm_nonneg _)))
  obtain ⟨a,ha⟩ := profile_weighted_sup_real hV hneg htest hanchor hG3
    (ne_of_gt (Metric.measure_ball_pos volume y hr)) hfbd
  have ha' : (⨆x∈Metric.ball y r,V x-(inner ℝ c (x-y):EReal))=(a:EReal) := by
    simpa only [f,EReal.coe_neg,← sub_eq_add_neg] using ha
  have hgap' : (⨆x∈Metric.closedBall y (R*r),V x+(f x:EReal))≤((a+e:ℝ):EReal) := by
    simpa only [f,EReal.coe_neg,← sub_eq_add_neg,ha',← EReal.coe_add] using hgap
  have ht := profile_massExcess_transfer hp hS hf.continuousOn (isCompact_closedBall y (R*r))
    (hF3.trans h3R) Metric.isOpen_ball (hG3.trans h3R) (Metric.ball_subset_ball hrR)
    Metric.ball_subset_closedBall (half_pos (sub_pos.mpr he)) ha hgap'
  filter_upwards [ht] with j hj
  obtain ⟨hfin,hfout⟩ := tilted_finite_centered (hd j) hj.1 hj.2.1
  refine ⟨hfin,hfout,?_⟩
  have hratio := hj.2.2
  change massExcess (tiltedMass (S j) (B j) (U j) (d j) (fun x =>-inner ℝ c (x-y)) (Metric.ball y (R*r)))
    (tiltedMass (S j) (B j) (U j) (d j) (fun x =>-inner ℝ c (x-y)) (Metric.ball y r))/S j<_ at hratio
  rw [tilted_excess_centered _ _ _ _ _ (hd j) y (R*r) r] at hratio
  have hless : massExcess (centeredMass (B j+S j • c) (U j) y (R*r))
      (centeredMass (B j+S j • c) (U j) y r)/S j<σ*r*‖c‖ := by
    linarith
  apply (div_lt_iff₀ (mul_pos (mul_pos (hS j) hr) hc)).mpr
  have hmul := (div_lt_iff₀ (hS j)).mp hless
  nlinarith only [hmul]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma zero_tiltedMass_centered (S : ℝ) (U : Plane → ℝ) {d : ℝ} (hd : 0≤ d) (y : Plane) (r : ℝ) :
    tiltedMass S 0 U d 0 (Metric.ball y r)=ENNReal.ofReal d*centeredMass 0 U y r := by
  simpa only [inner_zero_left,neg_zero,smul_zero,add_zero,mul_zero,Real.exp_zero,mul_one,Pi.zero_apply,Pi.zero_def]
    using tiltedMass_centered S 0 0 U d hd y r

lemma zero_tilted_excess_centered (S : ℝ) (U : Plane → ℝ) {d : ℝ} (hd : 0< d) (y : Plane) (R r : ℝ) :
    massExcess (tiltedMass S 0 U d 0 (Metric.ball y R))
      (tiltedMass S 0 U d 0 (Metric.ball y r))=
    massExcess (centeredMass 0 U y R) (centeredMass 0 U y r) := by
  rw [zero_tiltedMass_centered _ _ hd.le,zero_tiltedMass_centered _ _ hd.le]
  exact massExcess_mul_left _ _ _ (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top

lemma grid_child_closedBall_subset_two {A : ℕ} (hA : 10000< A) {y : Plane} (hy : y∈gridCenters A) :
    Metric.closedBall y (1000*(A:ℝ)⁻¹)⊆Metric.ball (0:Plane) 2 := by
  have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr (by omega)
  have hr : 1000*(A:ℝ)⁻¹<1 := by
    rw [← div_eq_mul_inv,div_lt_one hAr]
    exact_mod_cast (show 1000< A by omega)
  intro x hx
  rw [Metric.mem_ball,dist_zero_right]
  have hd : ‖x-y‖≤1000*(A:ℝ)⁻¹ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
  have hn := gridCenters_norm (by omega : 0< A) y hy
  have ht : ‖x‖≤‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
  linarith

theorem sequence_persistence_square {Cp a₀ : ℝ} (_hCp : 0≤ Cp) (ha₀ : 0< a₀)
    {A : ℕ} (hA : 10000< A) {yₑ : Plane} (hyₑ : yₑ∈gridCenters A)
    (D : ℕ → UnitWave Cp a₀) (H : ℕ → ℝ) (hH : ∀j,0< H j) (hHlim : Tendsto H atTop atTop)
    (hparent : ∀j,(D j).growth 0≤ H j)
    (hchild : ∀j,H j< massExcess (centeredMass 0 (D j).U yₑ (1000*(A:ℝ)⁻¹))
      (centeredMass 0 (D j).U yₑ ((A:ℝ)⁻¹))/((D j).K*(A:ℝ)⁻¹))
    {σ : ℝ} (hσ : 0<σ) (P : ℝ) (m₀ : ℕ) :
    ∃φ : ℕ → ℕ,StrictMono φ ∧ ∃m≥ m₀,∃p : Fin 2 → ℤ,∃c : Plane,
      let r := ((A:ℝ)⁻¹)^m
      let y := extendedGridCenter r p
      0<‖c‖ ∧ ‖y‖+2000*r<3 ∧ 1000*r<1/4 ∧
      ∀ᶠj in atTop,P≤‖H (φ j) • c‖ ∧
        centeredMass (((D (φ j)).K*H (φ j)) • c) (D (φ j)).U y r≠0 ∧
        centeredMass (((D (φ j)).K*H (φ j)) • c) (D (φ j)).U y (1000*r)≠⊤ ∧
        massExcess (centeredMass (((D (φ j)).K*H (φ j)) • c) (D (φ j)).U y (1000*r))
          (centeredMass (((D (φ j)).K*H (φ j)) • c) (D (φ j)).U y r)/
          ((D (φ j)).K*r)<σ*‖H (φ j) • c‖ := by
  have hK (j : ℕ) : 0<(D j).K := ha₀.trans_le (D j).frequency_lower
  let S : ℕ → ℝ := fun j =>(D j).K*H j
  have hS (j : ℕ) : 0< S j := mul_pos (hK j) (hH j)
  have hSinf : Tendsto S atTop atTop := by
    apply tendsto_atTop_mono (fun j => mul_le_mul_of_nonneg_right (D j).frequency_lower (hH j).le)
    exact hHlim.const_mul_atTop ha₀
  let d : ℕ → ℝ := fun j =>(tiltedMass (S j) 0 (D j).U 1 0 (Metric.ball 0 1000)).toReal⁻¹
  have hmass (j : ℕ) (r : ℝ) : tiltedMass (S j) 0 (D j).U 1 0 (Metric.ball 0 r)=centeredMass 0 (D j).U 0 r := by
    simpa using zero_tiltedMass_centered (S j) (D j).U (by norm_num : (0:ℝ)≤1) 0 r
  have hnorm (j : ℕ) : 0< d j ∧ tiltedMass (S j) 0 (D j).U (d j) 0 (Metric.ball 0 1000)=1 := by
    apply tiltedMass_normalized
    · rw [hmass]
      exact ne_of_gt ((pos_iff_ne_zero.mpr (D j).inner_nonzero).trans_le
        (centeredMass_mono _ _ _ (by norm_num : (1:ℝ)≤1000)))
    · rw [hmass]
      exact (D j).outer_finite
  have hinner (j : ℕ) : (-1:EReal)≤ logRate (S j)
      (tiltedMass (S j) 0 (D j).U (d j) 0 (Metric.ball 0 1)) := by
    have heq := normalized_inner_rate_eq (S:=S j) (B:=0) (U:=(D j).U)
      (Metric.ball_subset_ball (x:=(0:Plane)) (by norm_num : (1:ℝ)≤1000))
      (by simpa only [hmass] using (D j).inner_nonzero) (by simpa only [hmass] using (D j).outer_finite)
    change (-1:EReal)≤_
    change logRate (S j) (tiltedMass (S j) 0 (D j).U (d j) 0 (Metric.ball 0 1))=
      ((-massExcess (tiltedMass (S j) 0 (D j).U 1 0 (Metric.ball 0 1000))
        (tiltedMass (S j) 0 (D j).U 1 0 (Metric.ball 0 1))/S j:ℝ):EReal) at heq
    rw [heq,hmass,hmass]
    apply EReal.coe_le_coe_iff.mpr
    have hp := hparent j
    simp only [UnitWave.growth,UnitWave.excess,smul_zero] at hp
    have hp' := (div_le_iff₀ (hK j)).mp hp
    apply (le_div_iff₀ (hS j)).mpr
    dsimp only [S]
    nlinarith only [hp']
  have hinv : Tendsto (fun j =>(H j)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hHlim
  have hratio : Tendsto (fun j =>(D j).K/(S j+‖(0:Plane)‖)) atTop (𝓝 0) := by
    have he (j : ℕ) : (D j).K/(S j+‖(0:Plane)‖)=(H j)⁻¹ := by
      dsimp only [S]
      rw [norm_zero,add_zero]
      field_simp [(hK j).ne', (hH j).ne']
    simpa only [he] using hinv
  let err : ℕ → ℝ := fun j => Cp*((H j)⁻¹)^2
  have herr : Tendsto err atTop (𝓝 0) := by simpa [err] using (hinv.pow 2).const_mul Cp
  have hpd (j : ℕ) (i : Fin 2) (x : Plane) (hx : x∈Metric.ball (0:Plane) 1000) :
      |(D j).K^2*coordPartial (D j).p i x/(S j*(S j+‖(0:Plane)‖))|≤ err j := by
    have he : (D j).K^2*coordPartial (D j).p i x/(S j*(S j+‖(0:Plane)‖))=
        coordPartial (D j).p i x*((H j)⁻¹)^2 := by
      dsimp only [S]
      rw [norm_zero,add_zero]
      field_simp [(hK j).ne', (hH j).ne']
    rw [he,abs_mul,abs_of_nonneg (sq_nonneg ((H j)⁻¹))]
    exact mul_le_mul_of_nonneg_right ((D j).derivative_bound i x hx) (sq_nonneg _)
  obtain ⟨V,φ,hφ,hV,hneg,hprof⟩ := extract_tilted_profile Metric.isOpen_ball S (fun _ =>0)
    (fun j =>(D j).U) d hS hSinf (fun j =>(D j).smooth_U.continuousOn) (fun j =>(hnorm j).2.le)
  have htest := full_test_of_profile Metric.isOpen_ball (fun j =>(D (φ j)).smooth_p)
    (fun j =>(D (φ j)).smooth_U) (fun j => hS (φ j)) (hSinf.comp hφ.tendsto_atTop)
    (fun j =>(hnorm (φ j)).1) (hratio.comp hφ.tendsto_atTop) (fun j =>(D (φ j)).coefficient_bound)
    (herr.comp hφ.tendsto_atTop) (fun j => hpd (φ j)) (fun j =>(D (φ j)).equation)
    (hV.upperSemicontinuousOn _) hprof
  have hanchor := profile_anchor_from_mass (hV.upperSemicontinuousOn _) hprof
    (fun j => hS (φ j)) (fun j => hinner (φ j))
  have hrA : 0<(A:ℝ)⁻¹ := by positivity
  have hnonconstant := profile_nonconstant_of_positive_gap hV (fun x _ => hneg x) hanchor hprof
    (fun j => hS (φ j)) (isCompact_closedBall yₑ (1000*(A:ℝ)⁻¹))
    (grid_child_closedBall_subset_two hA hyₑ) Metric.isOpen_ball
    (Metric.nonempty_ball.mpr hrA) (Metric.ball_subset_ball (by nlinarith : (A:ℝ)⁻¹≤1000*(A:ℝ)⁻¹))
    Metric.ball_subset_closedBall hrA (fun j =>?_)
  · obtain ⟨m,hm,p,c,e,hc,hsmall,hmargin,herr',hgap⟩ := profile_small_affine_grid_gap
      (by omega : 1< A) (by norm_num : (1:ℝ)≤1000) hσ hV (fun x _ => hneg x) htest hanchor hnonconstant m₀
    refine ⟨φ,hφ,m,hm,p,c,hc,?_,hmargin,?_⟩
    · simpa only [show (2:ℝ)*1000=2000 by norm_num] using hsmall
    · let r := ((A:ℝ)⁻¹)^m
      let y := extendedGridCenter r p
      have hr : 0< r := pow_pos hrA m
      have ht := local_affine_profile_transfer (hV.upperSemicontinuousOn _) (fun x _ => hneg x) htest hanchor
        hprof (fun j => hS (φ j)) (fun j =>(hnorm (φ j)).1) (by norm_num : (1:ℝ)≤1000) hr hc hsmall herr' hgap
      have hlarge : ∀ᶠj in atTop,P≤‖H (φ j) • c‖ := by
        have ht : Tendsto (fun j => H (φ j)*‖c‖) atTop atTop :=
          (hHlim.comp hφ.tendsto_atTop).atTop_mul_const hc
        have he (j : ℕ) : ‖H (φ j) • c‖=H (φ j)*‖c‖ := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hH (φ j))]
        simpa only [he] using ht.eventually_ge_atTop P
      filter_upwards [ht,hlarge] with j hj hbig
      simp only [Function.comp_apply,zero_add] at hj
      refine ⟨hbig,hj.1,hj.2.1,?_⟩
      have hh := (div_lt_iff₀ (mul_pos (mul_pos (hS (φ j)) hr) hc)).mp hj.2.2
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hH (φ j))]
      apply (div_lt_iff₀ (mul_pos (hK (φ j)) hr)).mpr
      dsimp only [S] at hh
      nlinarith only [hh]
  · simp only [Function.comp_apply]
    rw [zero_tilted_excess_centered _ _ (hnorm (φ j)).1]
    apply (le_div_iff₀ (hS (φ j))).mpr
    have hh := (lt_div_iff₀ (mul_pos (hK (φ j)) hrA)).mp (hchild (φ j))
    dsimp only [S]
    nlinarith only [hh]

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ScaledWaves
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

namespace SharpNodal.Profiles
open Carleman

lemma centered_excess_rescale (T : Plane) (U : Plane → ℝ) (y z : Plane) {s : ℝ}
    (hs : 0 < s) (R r : ℝ) :
    massExcess (centeredMass (s • T) (U ∘ rescaleMap y s) z R)
      (centeredMass (s • T) (U ∘ rescaleMap y s) z r)=
      massExcess (centeredMass T U (rescaleMap y s z) (s*R))
      (centeredMass T U (rescaleMap y s z) (s*r)) := by
  rw [centeredMass_rescale _ _ _ _ hs,centeredMass_rescale _ _ _ _ hs]
  exact massExcess_mul_left _ _ _ (by simp [hs.ne'])
    (by simp)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace SharpNodal.Descent.Tree
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma scaled_floor_bound {A C₀ : ℝ} (hA : 2≤A) (hC : 0≤C₀) (n : ℕ)
    {K s : ℝ} (hK : 0 < K) (hs : 0 ≤ s) (t : Tree ι) (ht : ScaledFloors A C₀ K s n t) :
    t.floorCost≤(2*A^n-1)*C₀/K+2*s := by
  have hApos : 0<A := by linarith
  have hAp : 1≤A^n := one_le_pow₀ (by linarith : (1:ℝ)≤A)
  induction n generalizing K s t with
  | zero =>
    cases t with
    | stop a => simp only [floorCost,pow_zero]; positivity
    | step a t => exact ht.elim
  | succ n ih =>
    cases t with
    | stop a =>
      change 0≤_
      have hh : 0≤2*A^(n+1)-1 := by linarith
      positivity
    | step a t =>
      have hb (i : ι) := ih (div_pos hK hApos) (div_nonneg hs hApos.le) (t i) (ht.2 i) (one_le_pow₀ (by linarith : (1:ℝ)≤A))
      have he := Finset.expect_le Finset.univ_nonempty (fun i _ => hb i)
      change a.floor+(𝔼 i,floorCost (t i))≤_
      rw [ht.1]
      apply le_trans (show C₀/K+s+(𝔼 i,floorCost (t i)) ≤
        C₀/K+s+((2*A^n-1)*C₀/(K/A)+2*(s/A)) from by linarith only [he])
      have hCs : 0≤C₀/K := div_nonneg hC hK.le
      have hsA : s / A ≤ s / 2 := div_le_div_of_nonneg_left hs (by norm_num) hA
      have hCA : C₀/K*2≤C₀/K*A := mul_le_mul_of_nonneg_left hA hCs
      have heq : (2*A^n-1)*C₀/(K/A)=(2*A^(n+1)-A)*(C₀/K) := by
        rw [pow_succ]
        field_simp
      rw [heq]
      change C₀/K+s+((2*A^(n+1)-A)*(C₀/K)+2*(s/A))≤(2*A^(n+1)-1)*C₀/K+2*s
      rw [mul_div_assoc]
      nlinarith only [hsA,hCA]

lemma physical_floor_bound {A C₀ a₀ K s : ℝ} (hA : 2≤A) (hC : 0≤C₀) (ha : 0<a₀)
    (hK : 0 < K) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ)
    (hbottom : a₀≤K/A^n) {t : Tree ι} (ht : ScaledFloors A C₀ K s n t) :
    t.floorCost≤2*(C₀/a₀+1) := by
  have hAp : 0<A^n := pow_pos (by linarith : (0:ℝ)<A) n
  have hkbottom := (le_div_iff₀ hAp).mp hbottom
  have hratio : C₀*A^n/K≤C₀/a₀ := by
    apply (div_le_div_iff₀ hK ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left hkbottom hC]
  have hb := scaled_floor_bound hA hC n hK hs t ht
  have hCK : 0≤C₀/K := div_nonneg hC hK.le
  have he : (2*A^n-1)*C₀/K=2*(C₀*A^n/K)-C₀/K := by ring
  rw [he] at hb
  linarith

end SharpNodal.Descent.Tree

noncomputable section
open scoped BigOperators
open Set MeasureTheory
namespace SharpNodal.Profiles

namespace WaveTree
variable {A : ℕ} {Cp a₀ : ℝ}

lemma numerical_root (C₀ : ℝ) (t : WaveTree A Cp a₀) :
    (t.numerical C₀).root=label C₀ t.rootWave t.rootTilt := by cases t <;> rfl

lemma coherent_floors (C₀ : ℝ) {n : ℕ} {t : WaveTree A Cp a₀} (ht : Coherent n t) :
    Descent.Tree.ScaledFloors (A:ℝ) C₀ t.rootWave.K t.rootWave.side n (t.numerical C₀) := by
  induction n generalizing t with
  | zero => cases t with
    | stop D b => trivial
    | step D b t => exact ht.elim
  | succ n ih => cases t with
    | stop D b => trivial
    | step D b t =>
      refine ⟨rfl,fun i =>?_⟩
      have hh := ih (ht i).2
      rw [(ht i).1.2.2.1,(ht i).1.2.2.2] at hh
      exact hh

lemma label_nonnegative (ha₀ : 0<a₀) {C₀ : ℝ} (hC₀ : 0≤C₀)
    (D : ScaledWave Cp a₀) (b : Plane) :
    0≤(label C₀ D b).mass ∧ 0≤(label C₀ D b).floor := by
  have hK : 0<D.K := ha₀.trans_le D.frequency_lower
  exact ⟨div_nonneg (D.excess_nonneg b) hK.le,add_nonneg (div_nonneg hC₀ hK.le) D.side_pos.le⟩

theorem build_stopped {C₀ C₁ L : ℝ} (hA : 2≤A) (ha₀ : 0<a₀) (hC₀ : 0≤C₀)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L) (P : Descent.Label → Prop)
    (hcontinue : ∀(D : ScaledWave Cp a₀) (b : Plane),P (label C₀ D b) → L<D.growth 0 ∨ L<‖b‖)
    (n : ℕ) (D : ScaledWave Cp a₀) (b : Plane) (hbottom : a₀≤D.K/(A:ℝ)^n) :
    ∃t : WaveTree A Cp a₀,t.rootWave=D ∧ t.rootTilt=b ∧ Coherent n t ∧
      Descent.Tree.Valid C₁ (t.numerical C₀) ∧ Stopped C₀ P n t := by
  classical
  have hAr : 2≤(A:ℝ) := by exact_mod_cast hA
  have hArpos : 0<(A:ℝ) := by linarith
  induction n generalizing D b with
  | zero =>
    exact ⟨.stop D b,rfl,rfl,trivial,label_nonnegative ha₀ hC₀ D b,trivial⟩
  | succ n ih =>
    by_cases hP : P (label C₀ D b)
    · have hid : (D.K/(A:ℝ))/(A:ℝ)^n=D.K/(A:ℝ)^(n+1) := by rw [pow_succ]; ring
      have hnext : a₀≤D.K/(A:ℝ) := by
        have hpow : 1≤(A:ℝ)^n := one_le_pow₀ (by linarith)
        have hh := (le_div_iff₀ (pow_pos hArpos n)).mp (hid.symm ▸ hbottom)
        calc
          a₀ ≤ a₀*(A:ℝ)^n := le_mul_of_one_le_right ha₀.le hpow
          _ ≤ _ := hh
      obtain ⟨E,b',hchild,hinc,hdec⟩ := hrule D b hnext (hcontinue D b hP)
      have hbot (i : GridIndex A) : a₀≤(E i).K/(A:ℝ)^n := by rw [(hchild i).2.2.1,hid]; exact hbottom
      choose t hroot htilt hcoh hvalid hstop using (fun i =>ih (E i) (b' i) (hbot i))
      refine ⟨.step D b t,rfl,rfl,?_,?_,⟨hP,hstop⟩⟩
      · intro i
        rw [hroot i]
        exact ⟨hchild i,hcoh i⟩
      · refine ⟨(label_nonnegative ha₀ hC₀ D b).1,(label_nonnegative ha₀ hC₀ D b).2,?_,?_,hvalid⟩
        · simpa only [numerical_root,hroot,htilt,label] using hdec
        · simpa only [numerical_root,hroot,htilt,label] using hinc
    · exact ⟨.stop D b,rfl,rfl,trivial,label_nonnegative ha₀ hC₀ D b,hP⟩

end WaveTree
end SharpNodal.Profiles

noncomputable section
open scoped BigOperators
namespace SharpNodal.Profiles
open WaveTree

lemma stable_band_large_slope {Cp a₀ L Bstar η γ : ℝ} (hη : 0<η)
    (hγhalf : γ≤1/2) (hγη : γ≤η/2)
    (hlarge : ∀(D : UnitWave Cp a₀) (b : Plane),Bstar≤‖b‖ →
      D.growth b≤η*‖b‖ → L<D.growth 0)
    {b₀ : Plane} (hB : 0<‖b₀‖) (hBstar : 2*Bstar≤‖b₀‖)
    (D : ScaledWave Cp a₀) (b : Plane)
    (hgood : D.growth b<γ*‖b₀‖ ∧ ‖b-b₀‖<γ*‖b₀‖) : L<D.growth 0 := by
  have htri : ‖b₀‖≤‖b-b₀‖+‖b‖ := by
    calc
      ‖b₀‖=‖(b₀-b)+b‖ := by rw [sub_add_cancel]
      _ ≤ ‖b₀-b‖+‖b‖ := norm_add_le _ _
      _ = ‖b-b₀‖+‖b‖ := by rw [norm_sub_rev]
  have hc : ‖b₀‖/2≤‖b‖ := by nlinarith only [htri,hgood.2,hγhalf,hB]
  apply hlarge D.toUnitWave b (by linarith only [hc,hBstar])
  calc
    D.growth b ≤ γ*‖b₀‖ := hgood.1.le
    _ ≤ (η/2)*‖b₀‖ := mul_le_mul_of_nonneg_right hγη hB.le
    _ ≤ η*‖b‖ := by nlinarith only [hc,hη]

theorem actual_tree_stability {A : ℕ} {Cp a₀ C₀ C₁ L : ℝ} (hA : 2≤A)
    (hCp : 0≤Cp) (ha₀ : 0<a₀) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (hL : 0≤L)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L) :
    ∃P σ γ : ℝ,1≤P ∧ 0<σ ∧ 0<γ ∧
    ∀(D : ScaledWave Cp a₀) (b : Plane) (n : ℕ),
      a₀≤D.K/(A:ℝ)^n → P≤‖b‖ → D.growth b≤σ*‖b‖ →
      ∃t : WaveTree A Cp a₀,t.rootWave=D ∧ t.rootTilt=b ∧ t.Coherent n ∧
        Descent.Tree.Valid C₁ (t.numerical C₀) ∧
        t.Stopped C₀ (fun a => a.mass<γ*‖b‖ ∧ ‖a.tilt-b‖<γ*‖b‖) n ∧
        (3:ℝ)/4≤Descent.Tree.goodProb (fun a => a.mass<γ*‖b‖ ∧ ‖a.tilt-b‖<γ*‖b‖) (t.numerical C₀) ∧
        ∀(E : ScaledWave Cp a₀) (c : Plane),
          E.growth c<γ*‖b‖ ∧ ‖c-b‖<γ*‖b‖ → L<E.growth 0 := by
  classical
  have : NeZero A := ⟨by omega⟩
  obtain ⟨Bstar,η,hBstar,hη,hlarge⟩ := large_slope_forces_growth hCp ha₀ L hL
  let γ := min (1/4) (η/4)
  have hγ : 0<γ := lt_min (by norm_num) (by positivity)
  have hγhalf : γ≤1/2 := (min_le_left _ _).trans (by norm_num)
  have hγη : γ≤η/2 := (min_le_right _ _).trans (by linarith)
  let F := 2*(C₀/a₀+1)
  have hF : 0≤F := by dsimp [F]; positivity
  let Cst := 2*(1+C₁)+(1+2*C₁)*F
  have hCst : 0<Cst := by dsimp [Cst]; positivity
  let σ := γ/(16*Cst)
  let P := max 1 (max (2*Bstar) (16*Cst/γ))
  have hP1 : 1≤P := le_max_left _ _
  have hσ : 0<σ := div_pos hγ (by positivity)
  refine ⟨P,σ,γ,hP1,hσ,hγ,?_⟩
  intro D b n hbottom hPb hm
  have hB : 0<‖b‖ := (by norm_num : (0:ℝ)<1).trans_le (hP1.trans hPb)
  have hBP : 2*Bstar≤‖b‖ := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hPb
  have hBlower : 16*Cst/γ≤‖b‖ := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hPb
  have hgood (E : ScaledWave Cp a₀) (c : Plane)
      (hc : E.growth c<γ*‖b‖ ∧ ‖c-b‖<γ*‖b‖) : L<E.growth 0 :=
    stable_band_large_slope hη hγhalf hγη hlarge hB hBP E c hc
  obtain ⟨t,hroot,htilt,hcoh,hvalid,hstop⟩ := WaveTree.build_stopped hA ha₀ hC₀ hrule
    (fun a =>a.mass<γ*‖b‖ ∧ ‖a.tilt-b‖<γ*‖b‖)
    (fun E c hc => Or.inl (hgood E c hc)) n D b hbottom
  refine ⟨t,hroot,htilt,hcoh,hvalid,hstop,?_,hgood⟩
  have hfloor := Descent.Tree.physical_floor_bound (by exact_mod_cast hA) hC₀ ha₀
    (ha₀.trans_le D.frequency_lower) D.side_pos.le D.side_le_one n hbottom
    (by simpa only [hroot] using WaveTree.coherent_floors C₀ hcoh)
  have hinv : 1/‖b‖≤γ/(16*Cst) := by
    apply (div_le_div_iff₀ hB (by positivity)).mpr
    have hh := (div_le_iff₀ hγ).mp hBlower
    nlinarith only [hh]
  have hσid : Cst*σ=γ/16 := by dsimp [σ]; field_simp
  have hsmall : Cst*(σ+1/‖b‖)≤γ/4 := by
    have hh := mul_le_mul_of_nonneg_left hinv hCst.le
    change Cst*(1/‖b‖)≤Cst*σ at hh
    rw [hσid] at hh
    nlinarith only [hh,hσid,hγ]
  have hh := Descent.Tree.stable_probability hC₁ hF hγ hB hσ.le hvalid hfloor
    (by simpa only [numerical_root,hroot,htilt,label] using hm) hsmall
  simpa only [numerical_root,hroot,htilt,label] using hh

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
-- module Solutions.OAIQ4_Nl.NodalLength_GridPaths
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

namespace SharpNodal.Profiles

lemma expect_word_succ {α : Type*} [Fintype α] (n : ℕ) (f : (Fin (n+1) → α) → ℝ) :
    (𝔼 w,f w)=𝔼 a,𝔼 v : Fin n → α,f (Fin.cons a v) := by
  have he := Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α))
    (fun p : α × (Fin n → α) => f (Fin.cons p.1 p.2)) f (fun _ =>rfl)
  rw [← he]
  exact Finset.expect_product _ _ _

end SharpNodal.Profiles

noncomputable section
open scoped BigOperators
namespace SharpNodal.Profiles
namespace WaveTree
variable {A : ℕ} {Cp a₀ : ℝ}

lemma expect_pathGood (hA : 0<A) (C₀ : ℝ) (P : Descent.Label → Prop) [DecidablePred P]
    (n : ℕ) (t : WaveTree A Cp a₀) (ht : t.Coherent n) :
    (𝔼 w : GridWord A n, if PathGood C₀ P n t w then (1:ℝ) else 0)=
      Descent.Tree.goodProb P (t.numerical C₀) := by
  classical
  have : NeZero A := ⟨hA.ne'⟩
  induction n generalizing t with
  | zero => cases t with
    | stop D b =>
      by_cases hh : P (label C₀ D b) <;> simp [PathGood,numerical,Descent.Tree.goodProb,rootWave,rootTilt,hh]
    | step D b t => exact ht.elim
  | succ n ih => cases t with
    | stop D b =>
      by_cases hh : P (label C₀ D b) <;> simp [PathGood,numerical,Descent.Tree.goodProb,hh]
    | step D b t =>
      rw [expect_word_succ]
      by_cases hP : P (label C₀ D b)
      · simp only [PathGood,Fin.cons_zero,Fin.tail_cons,hP,true_and]
        rw [numerical,Descent.Tree.goodProb,ite_eq_left hP]
        exact Finset.expect_congr rfl (fun i _ => ih (t i) (ht i).2)
      · simp [PathGood,hP,numerical,Descent.Tree.goodProb]

end WaveTree

lemma WaveTree.highPath_of_good {A : ℕ} {Cp a₀ C₀ L : ℝ}
    {P : Descent.Label → Prop}
    (hlarge : ∀(D : ScaledWave Cp a₀) (b : Plane),P (WaveTree.label C₀ D b) → L<D.growth 0)
    {n : ℕ} {t : WaveTree A Cp a₀} (hcoh : t.Coherent n) (hstop : t.Stopped C₀ P n)
    {w : GridWord A n} (hw : t.PathGood C₀ P n w) : HighWavePath A L n t.rootWave w := by
  induction n generalizing t with
  | zero => exact hlarge t.rootWave t.rootTilt hw
  | succ n ih => cases t with
    | stop D b => exact (hstop hw).elim
    | step D b t =>
      exact ⟨hlarge D b hw.1, (t (w 0)).rootWave, (hcoh (w 0)).1,
        ih (hcoh (w 0)).2 (hstop.2 (w 0)) hw.2⟩

theorem actual_path_stability {A : ℕ} {Cp a₀ C₀ C₁ L : ℝ} (hA : 2≤A)
    (hCp : 0≤Cp) (ha₀ : 0<a₀) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (hL : 0≤L)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L) :
    ∃P σ : ℝ,1≤P ∧ 0<σ ∧ ∀(D : ScaledWave Cp a₀) (b : Plane) (n : ℕ),
      a₀≤D.K/(A:ℝ)^n → P≤‖b‖ → D.growth b≤σ*‖b‖ →
      (3:ℝ)/4 ≤ 𝔼 w : GridWord A n, if HighWavePath A L n D w then (1:ℝ) else 0 := by
  classical
  obtain ⟨P,σ,γ,hP,hσ,_hγ,hmain⟩ := actual_tree_stability hA hCp ha₀ hC₀ hC₁ hL hrule
  refine ⟨P,σ,hP,hσ,?_⟩
  intro D b n hbottom hPb hm
  obtain ⟨t,hroot,_htilt,hcoh,_hvalid,hstop,hprob,hlarge⟩ := hmain D b n hbottom hPb hm
  rw [← WaveTree.expect_pathGood (by omega : 0<A) C₀ _ n t hcoh] at hprob
  apply hprob.trans
  apply Finset.expect_le_expect
  intro w _
  split_ifs with hw hh hh
  · rfl
  · exact (hh (hroot ▸ WaveTree.highPath_of_good hlarge hcoh hstop hw)).elim
  · norm_num
  · rfl

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma ScaledWave.rebase_growth {Cp a₀ : ℝ} (D : ScaledWave Cp a₀) (y : Plane) (r : ℝ)
    (hr : 0 < r) (hr1 : r≤1) (hmargin : ‖y‖+1000*r≤1000)
    (hbottom : a₀≤D.K*r) (hm0 : centeredMass 0 D.U y r≠0)
    (hmt : centeredMass 0 D.U y (1000*r)≠⊤) (b : Plane) :
    (D.rebase y r hr hr1 hmargin hbottom hm0 hmt).growth b=
      massExcess (centeredMass (D.K • b) D.U y (1000*r))
        (centeredMass (D.K • b) D.U y r)/(D.K*r) := by
  have he := centered_excess_rescale (D.K • b) D.U y 0 hr 1000 1
  have hs : r • (D.K • b)=(D.K*r) • b := by rw [smul_smul,mul_comm]
  simp only [hs,rescaleMap,smul_zero,add_zero,mul_one] at he
  dsimp only [UnitWave.growth,UnitWave.excess,ScaledWave.rebase]
  rw [he,mul_comm r 1000]

end SharpNodal.Profiles
noncomputable section
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
namespace SharpNodal.Profiles

lemma frequency_at_earlier_scale {A m n : ℕ} (hA : 1≤A) (hmn : m≤n)
    {K a₀ : ℝ} (ha₀ : 0<a₀) (hbottom : a₀≤K/(A:ℝ)^n) :
    a₀≤K*((A:ℝ)⁻¹)^m := by
  have hAr : (1:ℝ)≤A := by exact_mod_cast hA
  have hAp : 0<(A:ℝ) := by linarith
  have hpow : (A:ℝ)^n=(A:ℝ)^m*(A:ℝ)^(n-m) := by rw [←pow_add,Nat.add_sub_of_le hmn]
  have hb := (le_div_iff₀ (pow_pos hAp n)).mp hbottom
  have hlast : 1≤(A:ℝ)^(n-m) := one_le_pow₀ hAr
  rw [inv_pow,←div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hAp m)).mpr
  rw [hpow] at hb
  have hh := mul_le_mul_of_nonneg_left hlast (mul_nonneg ha₀.le (pow_nonneg hAp.le m))
  nlinarith only [hb,hh]

lemma frequency_rebase_bottom {A m n : ℕ} (hmn : m≤n) (K : ℝ) :
    (K*((A:ℝ)⁻¹)^m)/(A:ℝ)^(n-m)=K/(A:ℝ)^n := by
  rw [inv_pow,←div_eq_mul_inv,div_div,←pow_add,Nat.add_sub_of_le hmn]

theorem sequence_persistent_paths {Cp a₀ C₀ C₁ L : ℝ}
    (hCp : 0≤Cp) (ha₀ : 0<a₀) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (hL : 0≤L)
    {A : ℕ} (hA : 10000<A) (hrule : DescentRule A Cp a₀ C₀ C₁ L)
    {yₑ : Plane} (hyₑ : yₑ∈gridCenters A)
    (D : ℕ → UnitWave Cp a₀) (H : ℕ → ℝ) (hH : ∀j,0<H j) (hHlim : Tendsto H atTop atTop)
    (hparent : ∀j,(D j).growth 0≤H j)
    (hchild : ∀j,H j< massExcess (centeredMass 0 (D j).U yₑ (1000*(A:ℝ)⁻¹))
      (centeredMass 0 (D j).U yₑ ((A:ℝ)⁻¹))/((D j).K*(A:ℝ)⁻¹))
    (depth : ℕ → ℕ) (hdepth : Tendsto depth atTop atTop)
    (hbottom : ∀j,a₀≤(D j).K/(A:ℝ)^(depth j)) (m₀ : ℕ) :
    ∃φ : ℕ → ℕ,StrictMono φ ∧ ∃m≥m₀,∃p : Fin 2 → ℤ,
      let r:=((A:ℝ)⁻¹)^m
      let y:=extendedGridCenter r p
      ‖y‖+2000*r<3 ∧ 1000*r<1/4 ∧ ∀ᶠj in atTop,
        m≤depth (φ j) ∧ ∃E : ScaledWave Cp a₀,
          E.U=(D (φ j)).U ∘ rescaleMap y r ∧ E.K=(D (φ j)).K*r ∧ E.side=r ∧
          (3:ℝ)/4≤𝔼 w : GridWord A (depth (φ j)-m),
            if HighWavePath A L (depth (φ j)-m) E w then (1:ℝ) else 0 := by
  obtain ⟨P,σ,hP,hσ,hstable⟩ := actual_path_stability (by omega) hCp ha₀ hC₀ hC₁ hL hrule
  obtain ⟨φ,hφ,m,hm,p,c,hc,hmargin,hrtiny,htransfer⟩ :=
    sequence_persistence_square hCp ha₀ hA hyₑ D H hH hHlim hparent hchild hσ P m₀
  let r:=((A:ℝ)⁻¹)^m
  let y:=extendedGridCenter r p
  have hAr : (1:ℝ)≤A := by exact_mod_cast (show 1≤A by omega)
  have hAp : 0<(A:ℝ) := by linarith
  have hr : 0 < r := pow_pos (inv_pos.mpr hAp) m
  have hr1 : r≤1 := pow_le_one₀ (inv_nonneg.mpr hAp.le) ((inv_le_one₀ hAp).mpr hAr)
  have hmap : ‖y‖+1000*r≤1000 := by change ‖y‖+2000*r<3 at hmargin; linarith
  have hdep : ∀ᶠj in atTop,m≤depth (φ j) := (hdepth.comp hφ.tendsto_atTop).eventually_ge_atTop m
  refine ⟨φ,hφ,m,hm,p,hmargin,hrtiny,?_⟩
  filter_upwards [hdep,htransfer] with j hj ht
  rcases ht with ⟨hPb,hi,ho,hgrowth⟩
  have hfreq := frequency_at_earlier_scale (by omega : 1≤A) hj ha₀ (hbottom (φ j))
  have hinner : centeredMass 0 (D (φ j)).U y r≠0 := centeredMass_ne_zero_of hi
  have houter : centeredMass 0 (D (φ j)).U y (1000*r)≠⊤ := centeredMass_ne_top_of ho
  let E := (D (φ j)).scaled.rebase y r hr hr1 hmap hfreq hinner houter
  refine ⟨hj,E,rfl,rfl,by dsimp [E,ScaledWave.rebase,UnitWave.scaled]; ring,?_⟩
  refine hstable E (H (φ j) • c) (depth (φ j)-m) ?_ hPb ?_
  · change a₀≤((D (φ j)).K*r)/(A:ℝ)^(depth (φ j)-m)
    rw [frequency_rebase_bottom hj]
    exact hbottom (φ j)
  · rw [show E.growth (H (φ j) • c)=_ from ScaledWave.rebase_growth _ _ _ hr hr1 hmap hfreq hinner houter _]
    simpa only [UnitWave.scaled,smul_smul] using hgrowth.le

end SharpNodal.Profiles

noncomputable section
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
namespace SharpNodal.Profiles

lemma finite_constant_subsequence {ι : Type*} [Finite ι] (f : ℕ → ι) :
    ∃φ : ℕ → ℕ,StrictMono φ ∧ ∃i : ι,∀n,f (φ n)=i := by
  obtain ⟨i,hi⟩ := Finite.exists_infinite_fiber f
  let := hi
  let φ := Nat.orderEmbeddingOfSet (f ⁻¹' {i})
  refine ⟨φ,φ.strictMono,i,?_⟩
  intro n
  exact (Nat.Subtype.ofNat (f ⁻¹' {i}) n).property

theorem uniform_persistence_alternative_oai {Cp a₀ C₀ C₁ L : ℝ}
    (hCp : 0≤Cp) (ha₀ : 0<a₀) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (hL : 0≤L)
    {A : ℕ} (hA : 10000<A) (hrule : DescentRule A Cp a₀ C₀ C₁ L)
    (Hmin : ℝ) : ∃H : ℝ,max 1 Hmin<H ∧ ∃M : ℕ,
    ∀(D : UnitWave Cp a₀) (i : GridIndex A) (depth : ℕ),
      a₀≤D.K/(A:ℝ)^depth → D.growth 0≤H →
      H < massExcess (centeredMass 0 D.U (gridCenter A i) (1000*(A:ℝ)⁻¹))
        (centeredMass 0 D.U (gridCenter A i) ((A:ℝ)⁻¹))/(D.K*(A:ℝ)⁻¹) →
      depth≤M ∨ PersistentSquare A L D depth M := by
  classical
  by_contra! hfail
  let H : ℕ → ℝ := fun j =>max 1 Hmin+(j:ℝ)+1
  have hH (j : ℕ) : max 1 Hmin<H j := by dsimp [H]; have hn : (0:ℝ)≤j := Nat.cast_nonneg j; linarith
  have hHpos (j : ℕ) : 0<H j := lt_trans (by linarith [le_max_left (1:ℝ) Hmin]) (hH j)
  have hHlim : Tendsto H atTop atTop := by
    apply tendsto_atTop_mono (f:=fun j : ℕ =>(j:ℝ))
    · intro j
      dsimp [H]
      linarith [le_max_left (1:ℝ) Hmin]
    · exact tendsto_natCast_atTop_atTop
  choose D i depth hbottom hparent hchild hdepth hbad using (fun j =>hfail (H j) (hH j) j)
  obtain ⟨φ,hφ,i₀,hi₀⟩ := finite_constant_subsequence i
  have hdep : Tendsto (depth ∘ φ) atTop atTop :=
    tendsto_atTop_mono (fun j =>le_of_lt (hdepth (φ j))) hφ.tendsto_atTop
  have hparents (j : ℕ) : (D (φ j)).growth 0≤H (φ j) := hparent (φ j)
  have hchildren (j : ℕ) : H (φ j)<
      massExcess (centeredMass 0 (D (φ j)).U (gridCenter A i₀) (1000*(A:ℝ)⁻¹))
      (centeredMass 0 (D (φ j)).U (gridCenter A i₀) ((A:ℝ)⁻¹))/((D (φ j)).K*(A:ℝ)⁻¹) := by
    simpa only [hi₀ j] using hchild (φ j)
  obtain ⟨ψ,hψ,m,hm,p,hmargin,hrtiny,hpaths⟩ := sequence_persistent_paths hCp ha₀ hC₀ hC₁ hL
    hA hrule (Finset.mem_image.mpr ⟨i₀,Finset.mem_univ _,rfl⟩)
    (D ∘ φ) (H ∘ φ) (fun j =>hHpos (φ j)) (hHlim.comp hφ.tendsto_atTop)
    hparents hchildren (depth ∘ φ) hdep (fun j =>hbottom (φ j)) 2
  have hmle : ∀ᶠj in atTop,m≤φ (ψ j) := (hφ.comp hψ).tendsto_atTop.eventually_ge_atTop m
  obtain ⟨j,hj,hjpaths⟩ := (hmle.and hpaths).exists
  rcases hjpaths with ⟨hmd,E,hU,hK,hs,hprob⟩
  exact hbad (φ (ψ j)) ⟨m,hm,hj,hmd,p,hmargin,hrtiny,E,hU,hK,hs,hprob⟩

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpNodal.Profiles.uniform_persistence_alternative_oai := @OAI.SharpNodal.Profiles.uniform_persistence_alternative_oai
