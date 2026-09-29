-- Prove2me | solution 1 for NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2ee4500e-2ec3-5a7d-8688-f4f0d6bbfa6a

import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar
import Theorems.Thm_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap

set_option autoImplicit false

open NumberField MeasureTheory

noncomputable section

namespace FltWs24
namespace BoxChangeOfVariables

section Core
variable {G : Type*} [AddGroup G] [Countable G] {α : Type*} [AddAction G α] [MeasurableSpace α]
  [MeasurableConstVAdd G α] {μ : Measure α} [VAddInvariantMeasure G α μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem setIntegral_comp_eq_of_isAddFundamentalDomain
    {s t : Set α} (hs : IsAddFundamentalDomain G s μ) (ht : IsAddFundamentalDomain G t μ)
    {T : α → α} (hT : MeasurePreserving T μ μ) (hTe : MeasurableEmbedding T) (hst : T ⁻¹' t = s)
    {f : α → E} (hf : ∀ (g : G) (x : α), f (g +ᵥ x) = f x) :
    ∫ x in s, f (T x) ∂μ = ∫ x in s, f x ∂μ := by
  calc ∫ x in s, f (T x) ∂μ = ∫ x in T ⁻¹' t, f (T x) ∂μ := by rw [hst]
    _ = ∫ y in t, f y ∂μ := hT.setIntegral_preimage_emb hTe f t
    _ = ∫ x in s, f x ∂μ := ht.setIntegral_eq hs hf

theorem integral_cond_comp_eq_of_isAddFundamentalDomain
    {s t : Set α} (hs : IsAddFundamentalDomain G s μ) (ht : IsAddFundamentalDomain G t μ)
    {T : α → α} (hT : MeasurePreserving T μ μ) (hTe : MeasurableEmbedding T) (hst : T ⁻¹' t = s)
    {f : α → E} (hf : ∀ (g : G) (x : α), f (g +ᵥ x) = f x) :
    ∫ x, f (T x) ∂(ProbabilityTheory.cond μ s) = ∫ x, f x ∂(ProbabilityTheory.cond μ s) := by
  simp only [ProbabilityTheory.cond, integral_smul_measure]
  rw [setIntegral_comp_eq_of_isAddFundamentalDomain hs ht hT hTe hst hf]

end Core

section Adelic
variable (F : Type) [Field F] [NumberField F]

theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  refine Function.Surjective.countable
    (f := fun k : F => (⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) ?_
  rintro ⟨x, k, rfl⟩
  exact ⟨k, rfl⟩

theorem preimage_mul_algebraMap_preimage_inv (a : F) (ha : a ≠ 0) (B : Set (AdeleRing (𝓞 F) F)) :
    (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) ⁻¹'
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x) ⁻¹' B) = B := by
  ext x
  simp only [Set.mem_preimage, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]

def mulAlgebraMapMeasurableEquiv
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [MeasurableMul (AdeleRing (𝓞 F) F)]
    (a : F) (ha : a ≠ 0) : AdeleRing (𝓞 F) F ≃ᵐ AdeleRing (𝓞 F) F where
  toFun x := algebraMap F (AdeleRing (𝓞 F) F) a * x
  invFun x := algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x
  left_inv x := by
    show algebraMap F _ a⁻¹ * (algebraMap F _ a * x) = x
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  right_inv x := by
    show algebraMap F _ a * (algebraMap F _ a⁻¹ * x) = x
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  measurable_toFun := measurable_const_mul _
  measurable_invFun := measurable_const_mul _

theorem integral_cond_comp_mul_algebraMap_of_isAddFundamentalDomain
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddLeftInvariant]
    (B : Set (AdeleRing (𝓞 F) F)) (a : F) (ha : a ≠ 0)
    (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) B μ)
    (hBinv : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x) ⁻¹' B) μ)
    (hT : MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) μ μ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AdeleRing (𝓞 F) F → E}
    (hf : ∀ (k : F) (x : AdeleRing (𝓞 F) F), f (algebraMap F (AdeleRing (𝓞 F) F) k + x) = f x) :
    ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) a * x) ∂(ProbabilityTheory.cond μ B)
      = ∫ x, f x ∂(ProbabilityTheory.cond μ B) := by
  haveI := countable_principalSubgroup F
  haveI : MeasurableConstVAdd (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F) :=
    ⟨fun c => measurable_const_add (c : AdeleRing (𝓞 F) F)⟩
  haveI : VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F) μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : AdeleRing (𝓞 F) F) s⟩
  have hf' : ∀ (g : AdeleRing.principalSubgroup (𝓞 F) F) (x : AdeleRing (𝓞 F) F), f (g +ᵥ x) = f x := by
    rintro ⟨_, k, rfl⟩ x
    exact hf k x
  exact integral_cond_comp_eq_of_isAddFundamentalDomain hB hBinv hT
    (mulAlgebraMapMeasurableEquiv F a ha).measurableEmbedding
    (preimage_mul_algebraMap_preimage_inv F a ha B) hf'

end Adelic

end FltWs24.BoxChangeOfVariables

end

open NumberField
attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AdeleRing (𝓞 F) F → E}
    (hf : ∀ (k : F) (x : AdeleRing (𝓞 F) F), f (algebraMap F (AdeleRing (𝓞 F) F) k + x) = f x)
    (a : F) (ha : a ≠ 0) :
    ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) a * x)
        ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F))
      = ∫ x, f x ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) := by
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  exact FltWs24.BoxChangeOfVariables.integral_cond_comp_mul_algebraMap_of_isAddFundamentalDomain F
    (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F) a ha
    (AdelicBox.isAddFundamentalDomain_adelicBox F _)
    (NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox F _ a⁻¹ (inv_ne_zero ha))
    (NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar F a ha)
    hf

end S_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap
end P2MW
export P2MW.S_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap (solution)
