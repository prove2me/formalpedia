-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_zero_of_active_norm_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T05:15:23.437879+00:00
-- url     : https://prove2.me/submissions/366ce866-eafa-4d5e-9478-b82dc05a8d92

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1384
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPathLiftDensity_cap_lipschitz_v2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPathLiftDensity_law_probability

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem positiveUnitBox_measurable : MeasurableSet (positiveUnitBox ι) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem unitBoxMeasure_ae : ∀ᵐ x ∂unitBoxMeasure ι, ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1 := by
  filter_upwards [ae_restrict_mem (μ := volume) (positiveUnitBox_measurable (ι := ι))] with x hx
  exact fun i => hx i (Set.mem_univ i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem realDensityMeasure_indicator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S) :
    realDensityMeasure μ (S.indicator f) = (realDensityMeasure μ f).restrict S := by
  have he : (fun x => ENNReal.ofReal (S.indicator f x)) =
      S.indicator (fun x => ENNReal.ofReal (f x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  unfold realDensityMeasure
  rw [he, withDensity_indicator hS, restrict_withDensity hS]

theorem realDensityMeasure_eq_indicator_of_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S)
    (hf : ∀ᵐ x ∂realDensityMeasure μ f, x ∈ S) :
    realDensityMeasure μ f = realDensityMeasure μ (S.indicator f) := by
  rw [realDensityMeasure_indicator μ f hS, Measure.restrict_eq_self_of_ae_mem hf]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set


end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem continuousDensity_zero_off_closed {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [SigmaFinite μ] [μ.IsOpenPosMeasure]
    (f : X → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    {S : Set X} (hS : IsClosed S) (hs : ∀ᵐ x ∂realDensityMeasure μ f, x ∈ S) :
    ∀ x ∉ S, f x = 0 := by
  have hm := realDensityMeasure_eq_indicator_of_ae μ f hS.measurableSet hs
  have hi : Measurable (S.indicator f) := hf.measurable.indicator hS.measurableSet
  have h := (withDensity_eq_iff_of_sigmaFinite
    hf.measurable.ennreal_ofReal.aemeasurable hi.ennreal_ofReal.aemeasurable).mp hm
  have he : f =ᵐ[μ.restrict Sᶜ] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hS.measurableSet.compl] with x hx hxS
    rw [Set.indicator_of_notMem hxS, ENNReal.ofReal_zero] at hx
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (hf0 x)
  have hall := Measure.eqOn_open_of_ae_eq he hS.isOpen_compl hf.continuousOn continuousOn_const
  exact fun x hx => hall hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set


end Erdos3

end

section

namespace Erdos3

open scoped BigOperators


end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ}

variable {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem layerContinuousPrincipalSlots_card (j : Fin m) (i : I j) :
    (layerContinuousPrincipalSlots (G := G) B j i).card = Fintype.card (B ⟨j, Sum.inl i⟩) :=
  principalCoefficientSlots_card _ _ (Nat.zero_lt_succ _)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule


end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule


end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanStability
namespace OAI

section

namespace Erdos3


end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F]

theorem principalSliceValue_abs_le (c : B → ℝ) (lower width : B × F → ℝ)
    (hwidth : ∀ p, |lower p| + |width p| ≤ 1)
    (x : B × F → ℝ) (hx : ∀ p, |x p| ≤ 1) :
    |principalSliceValue c lower width x| ≤ ∑ b, |c b| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul, Finset.abs_prod]
  have hp : (∏ i : F, |lower (b,i) + width (b,i) * x (b,i)|) ≤ 1 := by
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro i _
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact (add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) (hx _))).trans (hwidth _)
  exact mul_le_of_le_one_right (abs_nonneg _) hp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators


end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators


end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

theorem principalProfileSize_mul (R S : ℝ) (b : ℕ) :
    principalProfileSize (R * S) b = R * principalProfileSize S b := by
  unfold principalProfileSize
  ring

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators


end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators


end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

omit [Fintype D] in
theorem unitProfilePrincipalSize_pos (d : D) : 0 < unitProfilePrincipalSize (B := B) d :=
  principalProfileSize_pos zero_lt_one _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators


end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal


end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPartitionedProfileJet
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAxisProfilePolynomial_eq (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) :
    allocatedAxisProfilePolynomial B R σ a r =
      monomialArrayPolynomial Subtype.val (fun e =>
        coefficientProfileCenter (principalCoefficientSlots (layerSamplerDegree I n) a)
          (principalProfileSize (R a.1) (Fintype.card (B a))) e +
        coefficientProfileWidth (principalCoefficientSlots (layerSamplerDegree I n) a)
          (constantCoefficientSlot _ _) (R a.1 / 4)
          (principalProfileSize (R a.1) (Fintype.card (B a)))
          (tailProfileSize (R a.1) (σ a.1)
            (Fintype.card (SamplerCoefficientSlot G B (layerSamplerDegree I n) a))) e * r e) := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i =>
    simp only [allocatedAxisProfilePolynomial, allocatedContinuousProfileCenters,
      allocatedContinuousProfileWidths, layerContinuousPrincipalSlots_card]
    rfl
  | inr i =>
    simp only [allocatedAxisProfilePolynomial, allocatedIntegerProfileCenters,
      allocatedIntegerProfileWidths, layerIntegerPrincipalSlots_card]
    rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedEndpointIdentity
namespace OAI

section

namespace Erdos3

open MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

variable {D G E : Type*} [Fintype D] [Fintype G] [Fintype E]
variable {B : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (axis : E → D)


omit [Fintype D] [Fintype G] [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfilePrincipal_unit_bounds
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ) (hr : ∀ e j, |r e j| ≤ 1)
    (e : E) (b : B (axis e)) :
    unitProfilePrincipalSize (B := B) (axis e) ≤
      |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b| ∧
    |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b| ≤
      2 * unitProfilePrincipalSize (B := B) (axis e) := by
  have hγ := unitProfilePrincipalSize_pos (B := B) (axis e)
  obtain ⟨hl, hu⟩ := abs_le.mp (hr e (principalCoefficientSlot h (axis e) b))
  have hlo : unitProfilePrincipalSize (B := B) (axis e) ≤
      jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b := by
    unfold jointSlicedProfilePrincipal
    nlinarith
  rw [abs_of_nonneg (hγ.le.trans hlo)]
  refine ⟨hlo, ?_⟩
  unfold jointSlicedProfilePrincipal
  nlinarith

omit [Fintype D] [Fintype G] [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfilePrincipal_unit_mass
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ) (hr : ∀ e j, |r e j| ≤ 1)
    (e : E) :
    (∑ b, |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b|) ≤ 1 := by
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl
    (Fintype.card (B (axis e))) 0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  calc
    _ ≤ ∑ _b : B (axis e), 2 * unitProfilePrincipalSize (B := B) (axis e) :=
      Finset.sum_le_sum (fun b _ => (jointSlicedProfilePrincipal_unit_bounds h axis r hr e b).2)
    _ = 2 * principalProfileSize 1 (Fintype.card (B (axis e))) * Fintype.card (B (axis e)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unitProfilePrincipalSize]
      ring
    _ ≤ 1 := by linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators



end Erdos3

end

section

namespace Erdos3

open scoped BigOperators


end Erdos3

end

section

namespace Erdos3

open MeasureTheory


end Erdos3

end

section

namespace Erdos3
open scoped NNReal


end Erdos3

end

section

namespace Erdos3

open scoped NNReal


end Erdos3

end

section

namespace Erdos3
open scoped NNReal


end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical



end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSlicedIdealDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal


end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAxisProfilePolynomial_principal_coeff
    (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) (b : B a) :
    (allocatedAxisProfilePolynomial B R σ a r).coeff
        (canonicalPrincipalExponent (layerSamplerDegree I n) a b) =
      3 * principalProfileSize (R a.1) (Fintype.card (B a)) / 2 +
        principalProfileSize (R a.1) (Fintype.card (B a)) / 2 *
          r (principalCoefficientSlot (layerSamplerDegree I n) a b) := by
  rw [allocatedAxisProfilePolynomial_eq]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (principalCoefficientSlot (layerSamplerDegree I n) a b).val = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
  have hp : principalCoefficientSlot (layerSamplerDegree I n) a b ∈
      principalCoefficientSlots (G := G) (layerSamplerDegree I n) a :=
    (mem_principalCoefficientSlots _ _ _).mpr ⟨b, rfl⟩
  have hz : principalCoefficientSlot (G := G) (layerSamplerDegree I n) a b ≠
      constantCoefficientSlot _ _ := by
    intro hz
    exact constantCoefficientSlot_not_principal (layerSamplerDegree I n) a
      (Nat.zero_lt_succ _) (hz ▸ hp)
  simp only [coefficientProfileCenter, coefficientProfileWidth, hp, hz, ite_true, ite_false]

theorem allocatedAxisProfilePolynomial_constant_coeff
    (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) :
    (allocatedAxisProfilePolynomial B R σ a r).coeff 0 =
      R a.1 / 4 * r (constantCoefficientSlot _ _) := by
  rw [allocatedAxisProfilePolynomial_eq]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (constantCoefficientSlot (LayerSamplerVariables G I n B) (layerSamplerDegree I n a)).val = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
  simp only [coefficientProfileCenter, coefficientProfileWidth,
    constantCoefficientSlot_not_principal (layerSamplerDegree I n) a (Nat.zero_lt_succ _),
    ite_false, ite_true, zero_add]

variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P

omit [∀ a, DecidableEq (B a)] [DecidablePred P] in
theorem allocatedFixedPathPrincipal_eq (hR : ∀ j, R j ≠ 0) (r : Coeff → ℝ) :
    allocatedFixedPathPrincipal B P R σ r =
      jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
        (fun a e => r ⟨a, e⟩) := by
  funext a b
  rw [allocatedFixedPathPrincipal, allocatedAxisProfilePolynomial_principal_coeff]
  have hs : principalProfileSize (R a.val.1) (Fintype.card (B a.val)) =
      R a.val.1 * unitProfilePrincipalSize (B := B) a.val := by
    simpa only [unitProfilePrincipalSize, mul_one] using
      principalProfileSize_mul (R a.val.1) 1 (Fintype.card (B a.val))
  rw [hs]
  unfold jointSlicedProfilePrincipal
  field_simp [hR]

omit [∀ a, DecidableEq (B a)] [DecidablePred P] in
theorem allocatedFixedPathShift_eq (hR : ∀ j, R j ≠ 0) (r : Coeff → ℝ) :
    allocatedFixedPathShift B P R σ r =
      fun a => (1 / 4 : ℝ) * r ⟨a, constantCoefficientSlot _ _⟩ := by
  funext a
  rw [allocatedFixedPathShift, allocatedAxisProfilePolynomial_constant_coeff]
  field_simp [hR]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal



end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFixedPathLiftSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬P a},
  B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)

omit [∀ a, DecidableEq (B a)] in
theorem allocatedFixedPathLiftMap_measurable
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ) (r : Coeff → ℝ) :
    Measurable (allocatedFixedPathLiftMap B P R σ lower width r) := by
  unfold allocatedFixedPathLiftMap jointSlicedPrincipal sigmaAxisSampler
    principalSliceSingleton principalSliceValue
  fun_prop

omit [∀ a, DecidableEq (B a)] in
theorem allocatedFixedPathLiftMap_norm_le (hR : ∀ j, R j ≠ 0)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (x : Input → ℝ) (hx : ∀ p, |x p| ≤ 1) :
    ‖allocatedFixedPathLiftMap B P R σ lower width r x‖ ≤ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro o
  have hp := principalSliceValue_abs_le
    (jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
      (fun a e => r ⟨a,e⟩) o.1)
    (lower o.1) (width o.1) (hwidth o.1) (fun p => x ⟨o.1,p⟩) (fun p => hx _)
  have hm := jointSlicedProfilePrincipal_unit_mass degree Subtype.val
    (fun a e => r ⟨a,e⟩) (fun _ _ => hr _) o.1
  have hc : |(1 / 4 : ℝ) * r ⟨o.1, constantCoefficientSlot _ _⟩| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    exact mul_le_of_le_one_right (by norm_num) (hr _)
  simp only [allocatedFixedPathLiftMap, allocatedFixedPathPrincipal_eq B P R σ hR,
    allocatedFixedPathShift_eq B P R σ hR, Pi.add_apply]
  change |(1 / 4 : ℝ) * r ⟨o.1, constantCoefficientSlot _ _⟩ +
    principalSliceValue _ _ _ _| ≤ 2
  exact (abs_add_le _ _).trans ((add_le_add hc (hp.trans hm)).trans (by norm_num))

theorem allocatedFixedPathLiftDensity_zero_off_ball
    (hR : ∀ j, R j ≠ 0) (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : Active, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (z : Output → ℝ) (hz : 2 < ‖z‖) :
    allocatedFixedPathLiftDensity B P R σ hB lower width r z = 0 := by
  have hd := allocatedFixedPathLiftDensity_law_probability B P R σ hR hB lower width
    ha hδ hprincipal hw hl r hr
  have hb := allocatedFixedPathLiftDensity_cap_lipschitz_v2 B P R σ hR hB lower width
    ha hδ hprincipal hw hl r hr
  have hm := allocatedFixedPathLiftMap_measurable B P R σ lower width r
  apply continuousDensity_zero_off_closed volume _ hb.2.continuous hd.2.1
    (S := Metric.closedBall 0 2) Metric.isClosed_closedBall ?_ z
    (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz)
  rw [← hd.1]
  apply (ae_map_iff hm.aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
  filter_upwards [unitBoxMeasure_ae] with x hx
  simpa only [dist_zero_right] using
    allocatedFixedPathLiftMap_norm_le B P R σ hR lower width hwidth r hr x
    (fun p => by rw [abs_of_nonneg (hx p).1.le]; exact (hx p).2)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedSpatialKernelProgressionForecastIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal






end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal






end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal







end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "density" => fixedSpatialKernelOriginalForecastDensity B U basis S e W L z h0 h1 hB lower width

variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_zero_of_active_norm_gt_two
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (y : Domain) (hy : 2 < ‖y.2‖) : density sample y = 0 := by
  classical
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hg := allocatedFixedPathLiftDensity_zero_off_ball B short R σ
    (fun j => (hR j).ne') hB lower width hwidth hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr y.2 hy
  change _ * allocatedFixedPathLiftDensity B short R σ hB lower width (noise sample) y.2 = 0
  rw [hg, mul_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hwG : ∀ g, widthG g ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "frame" => fixedSpatialKernelSliceFrame W L z lowerG widthG
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG false h0 hwG
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG true h1 hwG

local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z
  lowerG widthG h0 h1 hwG hB lowerP widthP

variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_zero_of_active_norm_gt_two_oai
    (hwidthP : ∀ a p, |lowerP a p| + |widthP a p| ≤ 1)
    (y : Domain) (hy : 2 < ‖y.2‖) : density sample y = 0 :=
  fixedSpatialKernelOriginalForecastDensity_zero_of_active_norm_gt_two B U basis hR hσ S
    e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs hwidthP y hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

end Erdos3

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal







end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_zero_of_active_norm_gt_two_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.fixedSpatialKernelSliceOriginalForecastDensity_zero_of_active_norm_gt_two_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
