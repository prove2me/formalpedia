-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_evalForm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:52.670085+00:00
-- url     : https://prove2.me/submissions/d9288a31-ed2e-461c-b0b2-1a33392978ef

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_evalForm_tprod
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isRestricted_extend
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_finiteEmbed_tprod
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_mem_range_finiteEmbed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open PiTensorProduct Filter Function Module Set
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ξ : ∀ v, V v} (hξ : ∀ᶠ v in cofinite, ξ v ≠ 0)
    {t : ⨂[ℂ] v, V v} (ht : t ∈ restrictedTensor ξ) (ht0 : t ≠ 0) :
    ∃ (l : ∀ v, Dual ℂ (V v)) (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1), evalForm ξ l hl t ≠ 0 := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_mem_range_finiteEmbed ht
  set T : Finset ι := T₀ ∪ (Filter.eventually_cofinite.1 hξ).toFinset
  have hξT : ∀ v ∉ T, ξ v ≠ 0 := fun v hv h => hv (Finset.mem_union_right _ (by simpa using h))
  obtain ⟨s, rfl⟩ := hT₀ T Finset.subset_union_left
  have hs0 : s ≠ 0 := by rintro rfl; exact ht0 (map_zero _)
  let b : ∀ v : T, Basis (Basis.ofVectorSpaceIndex ℂ (V v)) ℂ (V v) :=
    fun v => Basis.ofVectorSpace ℂ (V v)
  let B := Basis.piTensorProduct b
  obtain ⟨k, hk⟩ : ∃ k, B.repr s k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hs0 (B.repr.injective (Finsupp.ext fun k => by simp [hcon k]))
  have hex : ∀ v, ∃ f : Dual ℂ (V v), v ∉ T → f (ξ v) = 1 := by
    intro v
    by_cases hv : v ∈ T
    · exact ⟨0, fun h => absurd hv h⟩
    · obtain ⟨f, hf⟩ : ∃ f : Dual ℂ (V v), f (ξ v) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hξT v hv ((Module.forall_dual_apply_eq_zero_iff ℂ (ξ v)).1 hcon)
      exact ⟨(f (ξ v))⁻¹ • f, fun _ => by simp [hf]⟩
  choose f hf using hex
  let l : ∀ v, Dual ℂ (V v) := fun v => if hv : v ∈ T then (b ⟨v, hv⟩).coord (k ⟨v, hv⟩) else f v
  have hl : ∀ᶠ v in cofinite, l v (ξ v) = 1 :=
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra hvT
      have hvT' : v ∉ T := by simpa using hvT
      exact hv (by simp [l, hvT', hf v hvT']))
  refine ⟨l, hl, ?_⟩
  have key : evalForm ξ l hl ∘ₗ finiteEmbed ξ T = B.coord k := by
    refine B.ext fun k' => ?_
    rw [Basis.coord_apply, Basis.repr_self, LinearMap.comp_apply, Basis.piTensorProduct_apply,
      finiteEmbed_tprod, evalForm_tprod (isRestricted_extend ξ T _),
      finprod_eq_prod_of_mulSupport_subset (s := T)]
    · rw [← Finset.prod_coe_sort T]
      have hterm : ∀ v : T, l v (extend ξ T (fun i => b i (k' i)) v) =
          if k' v = k v then 1 else 0 := by
        intro v
        simp only [l, extend, Finset.coe_mem, dif_pos, Basis.coord_apply,
          Basis.repr_self, Finsupp.single_apply]
      simp only [hterm, Finsupp.single_apply]
      by_cases hkk : k' = k
      · subst hkk; simp
      · rw [if_neg hkk]
        obtain ⟨v, hv⟩ : ∃ v, k' v ≠ k v := by
          by_contra hcon
          push Not at hcon
          exact hkk (funext hcon)
        exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])
    · intro v hv
      by_contra hvT
      have hvT' : v ∉ T := by simpa using hvT
      apply hv
      simp [l, extend, hvT', hf v hvT']
  have := congrArg (fun F => F s) key
  simp only [LinearMap.comp_apply, Basis.coord_apply] at this
  rw [this]
  exact hk
end GroundTheory.Automorphic.RestrictedTensor
