-- Prove2me | solution 1 for GlobalTheory.LatticeMean.mean_prod_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:59:23.897459+00:00
-- url     : https://prove2.me/submissions/f7b1bd9f-9687-4a1e-857a-34c21a746802

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SetAverageProdFundamentalDomainPlaneLatticePow
import Theorems.Thm_GlobalTheory_LatticeMean_exists_strict_domain
import Theorems.Thm_GlobalTheory_LatticeMean_setAverage_eq_of_domain
import Theorems.Thm_GlobalTheory_LatticeMean_setAverage_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
open GlobalTheory GlobalTheory.LatticeMean
namespace GlobalTheory.LatticeMean
theorem _root_.solution : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ (f : ℂ → ℝ), (∀ ω ∈ Λ, ∀ z, f (ω + z) = f z) → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (r : ℕ) (e : V ≃ₗ[ℝ] (Fin r → ℂ)) (A : AddSubgroup V), (∀ x, x ∈ A ↔ ∀ k, e x k ∈ Λ) → ⨍ z in Classical.epsilon (fun Fd : Set V => MeasureTheory.IsAddFundamentalDomain A Fd μ), ∏ k, f (e z k) ∂μ = (⨍ z in Classical.epsilon (fun Fd : Set ℂ => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume), f z) ^ r := by
  intro Λ hΛ f hf V _ _ _ _ _ μ _ r e A hA
  obtain ⟨hc, F, hFm, hF⟩ := exists_strict_domain Λ hΛ
  let ec : V ≃L[ℝ] (Fin r → ℂ) := e.toContinuousLinearEquiv
  let em : V ≃ᵐ (Fin r → ℂ) := ec.toHomeomorph.toMeasurableEquiv
  have hem : ∀ x, em x = e x := fun _ => rfl
  have hAc : Countable A := by
    refine Function.Injective.countable
      (f := fun (a : A) (k : Fin r) => (⟨e a k, (hA a).1 a.2 k⟩ : Λ)) ?_
    intro a b hab
    apply Subtype.ext
    apply e.injective
    funext k
    exact congrArg Subtype.val (congrFun hab k)
  have hQm : MeasurableSet (Set.univ.pi (fun _ : Fin r => F)) :=
    MeasurableSet.univ_pi fun _ => hFm
  have hP : IsAddFundamentalDomain A (em ⁻¹' Set.univ.pi (fun _ : Fin r => F)) μ := by
    refine IsAddFundamentalDomain.mk' (em.measurable hQm).nullMeasurableSet fun x => ?_
    choose g hg hu using fun k => hF (e x k)
    refine ⟨⟨e.symm fun k => (g k : ℂ), (hA _).2 fun k => by simp⟩, ?_, ?_⟩
    · intro k _
      show e (e.symm (fun k => (g k : ℂ)) + x) k ∈ F
      simpa using hg k
    · intro a ha
      apply Subtype.ext
      apply e.injective
      funext k
      have h1 : e ((a : V) + x) k ∈ F := ha k (Set.mem_univ k)
      have h2 := hu k ⟨e a k, (hA a).1 a.2 k⟩ (by simpa using h1)
      simpa using congrArg Subtype.val h2
  have hF' : IsAddFundamentalDomain Λ F volume :=
    IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hF
  rw [setAverage_eq_of_domain μ A (fun z => ∏ k, f (e z k)) ?_ _ hP,
    setAverage_eq_of_domain volume Λ f hf F hF', ← setAverage_pi]
  swap
  · intro a ha z
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_add, Pi.add_apply, hf _ ((hA a).1 ha k)]
  haveI : (μ.map em).IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  have hs := Measure.isAddLeftInvariant_eq_smul (μ.map em) (volume : Measure (Fin r → ℂ))
  have hc0 : Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have h1 : ⨍ z in em ⁻¹' Set.univ.pi (fun _ : Fin r => F), ∏ k, f (e z k) ∂μ
      = ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) ∂(μ.map em) := by
    rw [setAverage_eq, setAverage_eq, setIntegral_map_equiv, measureReal_def, measureReal_def,
      em.map_apply]
    rfl
  rw [h1, hs, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply]
  have hc1 : ((Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast hc0
  rw [NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]
  field_simp
end GlobalTheory.LatticeMean
