-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/35db8498-11e4-5f4e-aeb0-df15e1ea375a

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply
import Theorems.Thm_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact
import Theorems.Thm_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one
import Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles
import Theorems.Thm_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory"

open scoped Classical FourierTransform nonZeroDivisors NNReal ENNReal

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing RingOfIntegers mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing RingOfIntegers.coe_ne_zero_iff"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "fourierIntegral fourierIntegral_def fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply setIntegral_addChar_mul_eq_ite_of_isCompact measure_setOf_forall_addChar_finitePart_mul_eq_one forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one"
namespace Ws25FinInv
p2m_open "NumberField.AdelicFourier NumberField"

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "𝒪" => integralFiniteAdeles (𝓞 F) F
local notation "ι" => algebraMap F (FiniteAdeleRing (𝓞 F) F)

section Algebra

variable (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)

theorem addChar_neg_eq_one_iff (x : 𝔸f) : ψf (-x) = 1 ↔ ψf x = 1 := by
  have key : ψf (-x) * ψf x = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  constructor
  · intro h
    rw [h, one_mul] at key
    exact key
  · intro h
    rw [h, mul_one] at key
    exact key

def annSubgroup (a : 𝔸f) : AddSubgroup 𝔸f where
  carrier := {w | ∀ z ∈ 𝒪, ψf (a * w * z) = 1}
  zero_mem' := by
    intro z _
    rw [mul_zero, zero_mul, AddChar.map_zero_eq_one]
  add_mem' := by
    intro x y hx hy z hz
    rw [mul_add, add_mul, AddChar.map_add_eq_mul, hx z hz, hy z hz, one_mul]
  neg_mem' := by
    intro x hx z hz
    rw [mul_neg, neg_mul, addChar_neg_eq_one_iff]
    exact hx z hz

theorem mem_annSubgroup (a w : 𝔸f) :
    w ∈ annSubgroup ψf a ↔ ∀ z ∈ 𝒪, ψf (a * w * z) = 1 := Iff.rfl

theorem coe_annSubgroup (a : 𝔸f) :
    (annSubgroup ψf a : Set 𝔸f) = (fun x => a * x) ⁻¹' {w | ∀ z ∈ 𝒪, ψf (w * z) = 1} := rfl

theorem coe_annSubgroup_one :
    (annSubgroup ψf 1 : Set 𝔸f) = {w | ∀ z ∈ 𝒪, ψf (w * z) = 1} := by
  ext w
  simp only [SetLike.mem_coe, mem_annSubgroup, one_mul, Set.mem_setOf_eq]

theorem preimage_mul_eq_image_mul {a b : 𝔸f} (hab : a * b = 1) (E : Set 𝔸f) :
    (fun x => a * x) ⁻¹' E = (fun x => b * x) '' E := by
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hx
    exact ⟨a * x, hx, by rw [← mul_assoc, hba, one_mul]⟩
  · rintro ⟨w, hw, rfl⟩
    rwa [← mul_assoc, hab, one_mul]

theorem mul_right_injective_of_mul_eq_one {a b : 𝔸f} (hab : a * b = 1) :
    Function.Injective (fun x : 𝔸f => a * x) := by
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  intro x y hxy
  have h := congrArg (fun t => b * t) hxy
  simp only [← mul_assoc, hba, one_mul] at h
  exact h

end Algebra

section Measure

variable [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] [ν.IsAddHaarMeasure] in

theorem fourierIntegral_finset_sum_smul (s : Finset F) (c : F → ℂ) (g : F → 𝔸f → ℂ) (w : 𝔸f)
    (hint : ∀ k ∈ s, Integrable (fun v => ψf (-(v * w)) * g k v) ν) :
    fourierIntegral ψf ν (∑ k ∈ s, c k • g k) w = ∑ k ∈ s, c k * fourierIntegral ψf ν (g k) w := by
  simp only [fourierIntegral_def]
  have hpt : (fun v => ψf (-(v * w)) * (∑ k ∈ s, c k • g k) v)
      = fun v => ∑ k ∈ s, c k * (ψf (-(v * w)) * g k v) := by
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hpt, integral_finsetSum s (fun k hk => (hint k hk).const_mul (c k))]
  exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)

theorem integrable_kernel_mul_indicator (hcont : Continuous ψf) {E : Set 𝔸f} (hE : IsCompact E)
    {φ : 𝔸f → ℂ} (hφ : Continuous φ) (w : 𝔸f) :
    Integrable (fun v => ψf (-(v * w)) * E.indicator φ v) ν := by
  have hrw : (fun v => ψf (-(v * w)) * E.indicator φ v)
      = E.indicator (fun v => ψf (-(v * w)) * φ v) := by
    funext v
    exact (Set.indicator_mul_right E (fun v => ψf (-(v * w))) φ).symm
  rw [hrw, integrable_indicator_iff hE.isClosed.measurableSet]
  have hk : Continuous fun v : 𝔸f => ψf (-(v * w)) :=
    hcont.comp ((continuous_id.mul continuous_const).neg)
  exact ContinuousOn.integrableOn_compact hE (hk.mul hφ).continuousOn

def mulEquiv (a b : 𝔸f) (hab : a * b = 1) : 𝔸f ≃+ 𝔸f where
  toFun x := a * x
  invFun x := b * x
  left_inv x := by
    show b * (a * x) = x
    rw [← mul_assoc, mul_comm b a, hab, one_mul]
  right_inv x := by
    show a * (b * x) = x
    rw [← mul_assoc, hab, one_mul]
  map_add' x y := mul_add a x y

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem coe_mulEquiv (a b : 𝔸f) (hab : a * b = 1) : ⇑(mulEquiv a b hab) = fun x => a * x := rfl

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem coe_mulEquiv_symm (a b : 𝔸f) (hab : a * b = 1) :
    ⇑(mulEquiv a b hab).symm = fun x => b * x := rfl

theorem exists_measure_preimage_mul (a b : 𝔸f) (hab : a * b = 1) :
    ∃ c : ℝ≥0∞, ∀ E : Set 𝔸f, IsCompact E → ν ((fun x => a * x) ⁻¹' E) = c * ν E := by
  have he : Continuous (mulEquiv a b hab) := by
    rw [coe_mulEquiv]; exact continuous_const.mul continuous_id
  have hes : Continuous (mulEquiv a b hab).symm := by
    rw [coe_mulEquiv_symm]; exact continuous_const.mul continuous_id
  haveI := AddEquiv.isAddHaarMeasure_map ν (mulEquiv a b hab) he hes
  refine ⟨Measure.addHaarScalarFactor (Measure.map (mulEquiv a b hab) ν) ν, fun E hE => ?_⟩
  have h := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure
    (Measure.map (mulEquiv a b hab) ν) ν (s := E) (by rw [hE.isClosed.closure_eq]; exact hE)
  rw [Measure.map_apply he.measurable hE.isClosed.measurableSet, ENNReal.smul_def, smul_eq_mul] at h
  exact h

end Measure

section Main

variable [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)

local notation "Sk⟮" k ", " d "⟯" =>
  (fun z : FiniteAdeleRing (𝓞 F) F => algebraMap F (FiniteAdeleRing (𝓞 F) F) k
    + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F

theorem fourierIntegral_indicator_coset_eq_indicator (hcont : Continuous ψf)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    fourierIntegral ψf ν (Sk⟮k, d⟯.indicator 1)
      = (annSubgroup ψf (ι (d : F)) : Set 𝔸f).indicator
          (fun w => ((ν Sk⟮k, d⟯).toReal : ℂ) * ψf (-(ι k * w))) := by
  funext w
  rw [fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply F ν hcont d hd k w]
  by_cases hw : ∀ z ∈ 𝒪, ψf (ι (d : F) * w * z) = 1
  · rw [if_pos hw, mul_one, mul_comm,
      Set.indicator_of_mem (show w ∈ (annSubgroup ψf (ι (d : F)) : Set 𝔸f) from hw)]
  · rw [if_neg hw, mul_zero,
      Set.indicator_of_notMem (show w ∉ (annSubgroup ψf (ι (d : F)) : Set 𝔸f) from hw)]

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

theorem isCompact_annSubgroup (hAc : IsCompact {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1})
    {a b : 𝔸f} (hab : a * b = 1) : IsCompact (annSubgroup ψf a : Set 𝔸f) := by
  rw [coe_annSubgroup, preimage_mul_eq_image_mul hab]
  exact hAc.image (continuous_const.mul continuous_id)

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

theorem forall_annSubgroup_iff_neg_mem
    (hbi : ∀ u : 𝔸f, (∀ w : 𝔸f, (∀ z ∈ 𝒪, ψf (w * z) = 1) → ψf (u * w) = 1) ↔ u ∈ 𝒪)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) (y : 𝔸f) :
    (∀ w ∈ annSubgroup ψf (ι (d : F)), ψf (-(ι k + y) * w) = 1) ↔ -y ∈ Sk⟮k, d⟯ := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : ι (d : F) * ι (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  have hba : ι (d : F)⁻¹ * ι (d : F) = 1 := by rw [mul_comm]; exact hab

  have h1 : (∀ w ∈ annSubgroup ψf (ι (d : F)), ψf (-(ι k + y) * w) = 1)
      ↔ (∀ w : 𝔸f, (∀ z ∈ 𝒪, ψf (w * z) = 1) → ψf ((ι k + y) * ι (d : F)⁻¹ * w) = 1) := by
    constructor
    · intro h w hw
      have hmem : ι (d : F)⁻¹ * w ∈ annSubgroup ψf (ι (d : F)) := by
        rw [mem_annSubgroup]
        intro z hz
        rw [← mul_assoc, hab, one_mul]
        exact hw z hz
      have h' := h _ hmem
      rw [neg_mul, addChar_neg_eq_one_iff, ← mul_assoc] at h'
      exact h'
    · intro h w hw
      rw [mem_annSubgroup] at hw
      have h' := h (ι (d : F) * w) hw
      rw [neg_mul, addChar_neg_eq_one_iff]
      have e : (ι k + y) * ι (d : F)⁻¹ * (ι (d : F) * w) = (ι k + y) * w := by
        rw [mul_assoc, ← mul_assoc (ι (d : F)⁻¹), hba, one_mul]
      rw [e] at h'
      exact h'
  rw [h1, hbi]

  constructor
  · intro hu
    refine ⟨-((ι k + y) * ι (d : F)⁻¹), fun v => neg_mem (hu v), ?_⟩
    show ι k + ι (d : F) * -((ι k + y) * ι (d : F)⁻¹) = -y
    have e : ι (d : F) * ((ι k + y) * ι (d : F)⁻¹) = ι k + y := by
      rw [mul_comm (ι k + y), ← mul_assoc, hab, one_mul]
    rw [mul_neg, e]
    ring
  · rintro ⟨z, hz, hzy⟩
    have e : (ι k + y) * ι (d : F)⁻¹ = -z := by
      have hzy' : ι k + ι (d : F) * z = -y := hzy
      have hy : y = -(ι k + ι (d : F) * z) := by rw [hzy', neg_neg]
      rw [hy]
      have : (ι k + -(ι k + ι (d : F) * z)) = -(ι (d : F) * z) := by ring
      rw [this, neg_mul, mul_comm (ι (d : F)) z, mul_assoc, hab, mul_one]
    rw [e]
    exact fun v => neg_mem (hz v)

theorem measure_coset_mul_measure_annSubgroup
    (hAc : IsCompact {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1})
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    ν Sk⟮k, d⟯ * ν (annSubgroup ψf (ι (d : F)) : Set 𝔸f)
      = ν 𝒪 * ν {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1} := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : ι (d : F) * ι (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  obtain ⟨c, hc⟩ := exists_measure_preimage_mul ν (ι (d : F)) (ι (d : F)⁻¹) hab
  have hO_cpt : IsCompact 𝒪 := isCompact_integralFiniteAdeles (K := F)

  have hB_cpt : IsCompact ((fun z => ι (d : F) * z) '' 𝒪) :=
    hO_cpt.image (continuous_const.mul continuous_id)
  have hS_eq : Sk⟮k, d⟯ = (fun b => ι k + b) '' ((fun z => ι (d : F) * z) '' 𝒪) :=
    (Set.image_image (fun b => ι k + b) (fun z => ι (d : F) * z) 𝒪).symm
  have hS : ν Sk⟮k, d⟯ = ν ((fun z => ι (d : F) * z) '' 𝒪) := by
    rw [hS_eq, Set.image_add_left, measure_preimage_add]

  have hO : ν 𝒪 = c * ν ((fun z => ι (d : F) * z) '' 𝒪) := by
    have h := hc _ hB_cpt
    rwa [Set.preimage_image_eq _ (mul_right_injective_of_mul_eq_one hab)] at h

  have hA : ν (annSubgroup ψf (ι (d : F)) : Set 𝔸f)
      = c * ν {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1} := by
    rw [coe_annSubgroup]
    exact hc _ hAc
  rw [hS, hA, hO]
  ring

theorem fourierIntegral_fourierIntegral_indicator_coset (hcont : Continuous ψf)
    (hAc : IsCompact {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1})
    (hbi : ∀ u : 𝔸f, (∀ w : 𝔸f, (∀ z ∈ 𝒪, ψf (w * z) = 1) → ψf (u * w) = 1) ↔ u ∈ 𝒪)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) (y : 𝔸f) :
    fourierIntegral ψf ν (fourierIntegral ψf ν (Sk⟮k, d⟯.indicator 1)) y
      = ((ν 𝒪).toReal : ℂ) * ((ν {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1}).toReal : ℂ)
          * Sk⟮k, d⟯.indicator 1 (-y) := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : ι (d : F) * ι (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  have hKc : IsCompact (annSubgroup ψf (ι (d : F)) : Set 𝔸f) :=
    isCompact_annSubgroup ψf hAc hab
  have hKm : MeasurableSet (annSubgroup ψf (ι (d : F)) : Set 𝔸f) :=
    hKc.isClosed.measurableSet

  have h1 : fourierIntegral ψf ν (fourierIntegral ψf ν (Sk⟮k, d⟯.indicator 1)) y
      = ((ν Sk⟮k, d⟯).toReal : ℂ)
        * ∫ w in (annSubgroup ψf (ι (d : F)) : Set 𝔸f), ψf (-(ι k + y) * w) ∂ν := by
    rw [fourierIntegral_indicator_coset_eq_indicator ν ψf hcont d hd k, fourierIntegral_def,
      ← integral_const_mul, ← integral_indicator hKm]
    congr 1
    funext w
    by_cases hw : w ∈ (annSubgroup ψf (ι (d : F)) : Set 𝔸f)
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, mul_left_comm, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero]

  have h2 := setIntegral_addChar_mul_eq_ite_of_isCompact F ν ψf (annSubgroup ψf (ι (d : F))) hKc
    (-(ι k + y))

  have h3 : ((ν Sk⟮k, d⟯).toReal : ℂ) * ((ν (annSubgroup ψf (ι (d : F)) : Set 𝔸f)).toReal : ℂ)
      = ((ν 𝒪).toReal : ℂ) * ((ν {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1}).toReal : ℂ) := by
    have h := congrArg (fun t : ℝ≥0∞ => ((t.toReal : ℝ) : ℂ))
      (measure_coset_mul_measure_annSubgroup ν ψf hAc d hd k)
    simp only [ENNReal.toReal_mul, Complex.ofReal_mul] at h
    exact h
  rw [h1, h2]
  by_cases hy : -y ∈ Sk⟮k, d⟯
  · rw [if_pos ((forall_annSubgroup_iff_neg_mem ψf hbi d hd k y).mpr hy),
      Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    exact h3
  · rw [if_neg (fun h => hy ((forall_annSubgroup_iff_neg_mem ψf hbi d hd k y).mp h)),
      Set.indicator_of_notMem hy, mul_zero, mul_zero]

theorem fourierIntegral_fourierIntegral_eq (hcont : Continuous ψf)
    (hAc : IsCompact {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1})
    (hbi : ∀ u : 𝔸f, (∀ w : 𝔸f, (∀ z ∈ 𝒪, ψf (w * z) = 1) → ψf (u * w) = 1) ↔ u ∈ 𝒪)
    {h : 𝔸f → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) (y : 𝔸f) :
    fourierIntegral ψf ν (fourierIntegral ψf ν h) y
      = ((ν 𝒪).toReal : ℂ) * ((ν {w : 𝔸f | ∀ z ∈ 𝒪, ψf (w * z) = 1}).toReal : ℂ) * h (-y) := by
  obtain ⟨d, hd, s, c, rfl⟩ := exists_eq_sum_indicator_image_integralFiniteAdeles F hlc hcs
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hab : ι (d : F) * ι (d : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd', map_one]
  have hO_cpt : IsCompact 𝒪 := isCompact_integralFiniteAdeles (K := F)
  have hS_cpt : ∀ k : F, IsCompact Sk⟮k, d⟯ := fun k =>
    hO_cpt.image (continuous_const.add (continuous_const.mul continuous_id))

  have hinner : fourierIntegral ψf ν (∑ k ∈ s, c k • Sk⟮k, d⟯.indicator 1)
      = ∑ k ∈ s, c k • fourierIntegral ψf ν (Sk⟮k, d⟯.indicator 1) := by
    funext w
    rw [fourierIntegral_finset_sum_smul ν ψf s c _ w
      (fun k _ => integrable_kernel_mul_indicator ν ψf hcont (hS_cpt k) continuous_one w)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

  have hKc : IsCompact (annSubgroup ψf (ι (d : F)) : Set 𝔸f) :=
    isCompact_annSubgroup ψf hAc hab
  have hint : ∀ k ∈ s, Integrable
      (fun w => ψf (-(w * y)) * fourierIntegral ψf ν (Sk⟮k, d⟯.indicator 1) w) ν := by
    intro k _
    rw [fourierIntegral_indicator_coset_eq_indicator ν ψf hcont d hd k]
    exact integrable_kernel_mul_indicator ν ψf hcont hKc
      (continuous_const.mul (hcont.comp ((continuous_const.mul continuous_id).neg))) y
  rw [hinner, fourierIntegral_finset_sum_smul ν ψf s c _ y hint]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [fourierIntegral_fourierIntegral_indicator_coset ν ψf hcont hAc hbi d hd k y]
  ring

end Main

end NumberField.AdelicFourier.Ws25FinInv

end

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq.NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory"
open scoped Classical FourierTransform nonZeroDivisors

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (y : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν
        (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h) y
      = ((Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℂ)
          * ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) ^ 2) * h (-y) := by

  have happly : ∀ w : FiniteAdeleRing (𝓞 F) F,
      (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) w
        = ψ (0, w) := fun w => rfl
  have hcont : Continuous
      (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) :=
    (continuous_congr happly).mpr (hψ.continuous.comp (continuous_const.prodMk continuous_id))
  have hset : {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
        (w * z) = 1}
      = {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} := by
    simp only [happly]
  have hAc := (isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one F hψ hψ_inf).1
  have hvol := measure_setOf_forall_addChar_finitePart_mul_eq_one F ν hψ hψ_inf
  have hbi := forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles F hψ hψ_inf
  have hmain := NumberField.AdelicFourier.Ws25FinInv.fourierIntegral_fourierIntegral_eq ν
    (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
    hcont (by rw [hset]; exact hAc) (by simpa only [happly] using hbi) hlc hcs y
  rw [hmain, hset, hvol, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  push_cast
  ring

end S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq (solution)
