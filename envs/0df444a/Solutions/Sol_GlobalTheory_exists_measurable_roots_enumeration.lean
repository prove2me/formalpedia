-- Prove2me | solution 1 for GlobalTheory.exists_measurable_roots_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:33.698931+00:00
-- url     : https://prove2.me/submissions/6a02b61c-b597-4ebc-a94b-ae21710af175

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsProdXSubCOfMonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMeasurableRootsEnumeration
import Theorems.Thm_GlobalTheory_continuous_coeff_prod_X_sub_C
import Theorems.Thm_GlobalTheory_prod_X_sub_C_eq_X_pow_add_sum
import Theorems.Thm_GlobalTheory_exists_prod_X_sub_C_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution :
    ∀ δ : ℕ, ∃ ρ : (Fin δ → ℂ) → (Fin δ → ℂ), Measurable ρ ∧ ∀ c : Fin δ → ℂ,
      ∏ i, (Polynomial.X - Polynomial.C (ρ c i)) =
        Polynomial.X ^ δ + ∑ i : Fin δ, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) := by
  intro δ
  let e : ℂ ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable
    (fun _ => not_countable_iff.mpr (inferInstance : Uncountable ℝ)
      Complex.ofReal_injective.countable) (not_countable_iff.mpr inferInstance)
  let S : Set (Fin δ → ℂ) := {r | Monotone (e ∘ r)}
  have hS : MeasurableSet S := by
    have : S = ⋂ i, ⋂ j, ⋂ _ : i ≤ j, {r : Fin δ → ℂ | e (r i) ≤ e (r j)} := by
      ext r
      simp only [S, Set.mem_setOf_eq, Set.mem_iInter, Monotone, Function.comp]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_le ?_ ?_
    · exact e.measurable.comp (measurable_pi_apply i)
    · exact e.measurable.comp (measurable_pi_apply j)
  let V : (Fin δ → ℂ) → (Fin δ → ℂ) := fun r i => (∏ j, (X - C (r j))).coeff i
  have hV : Measurable V :=
    (continuous_pi fun i => continuous_coeff_prod_X_sub_C _ _).measurable
  haveI : StandardBorelSpace S := hS.standardBorel
  have hinj : Function.Injective fun x : S => V x := by
    rintro ⟨r, hr⟩ ⟨s, hs⟩ h
    have h1 : (∏ j, (X - C (r j)) : ℂ[X]) = ∏ j, (X - C (s j)) := by
      refine (prod_X_sub_C_eq_X_pow_add_sum r).trans
        (Eq.trans ?_ (prod_X_sub_C_eq_X_pow_add_sum s).symm)
      refine congrArg (X ^ δ + ·) (Finset.sum_congr rfl fun i _ => ?_)
      exact congrArg (fun a => C a * X ^ (i : ℕ)) (congrFun h i)
    have h2 : Finset.univ.val.map r = Finset.univ.val.map s := by
      rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map r),
        ← roots_multiset_prod_X_sub_C (Finset.univ.val.map s), Multiset.map_map,
        Multiset.map_map]
      exact congrArg roots h1
    have h3 : Finset.univ.val.map (e ∘ r) = Finset.univ.val.map (e ∘ s) := by
      rw [← Multiset.map_map, ← Multiset.map_map, h2]
    rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h3
    have h4 := List.ofFn_injective
      (h3.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hr) (List.sortedLE_ofFn_iff.mpr hs))
    ext i
    exact e.injective (congrFun h4 i)
  have hemb : MeasurableEmbedding fun x : S => V x :=
    (hV.comp measurable_subtype_coe).measurableEmbedding hinj
  obtain ⟨ρ, hρ, hρV⟩ := hemb.exists_measurable_extend (g := fun x : S => (x : Fin δ → ℂ))
    measurable_subtype_coe fun _ => inferInstance
  refine ⟨ρ, hρ, fun c => ?_⟩
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_eq c
  have hrS : r ∘ Tuple.sort (e ∘ r) ∈ S := Tuple.monotone_sort (e ∘ r)
  have hp : (∏ j, (X - C ((r ∘ Tuple.sort (e ∘ r)) j)) : ℂ[X])
      = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
    rw [← hr]
    exact Equiv.prod_comp (Tuple.sort (e ∘ r)) fun j => X - C (r j)
  have hc : V (r ∘ Tuple.sort (e ∘ r)) = c := by
    funext i
    simp only [V]
    rw [hp, coeff_add, coeff_X_pow, if_neg i.2.ne, zero_add, finset_sum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      exact if_neg fun h => hj (Fin.ext h.symm)
    · simp
  have : ρ c = r ∘ Tuple.sort (e ∘ r) := by
    rw [← hc]
    exact congrFun hρV ⟨_, hrS⟩
  rw [this, hp]
end GlobalTheory
