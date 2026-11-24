-- Prove2me | solution 1 for GlobalTheory.multilinear_sum_eq_of_prod_fun_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:40.723646+00:00
-- url     : https://prove2.me/submissions/b53a2cc6-58e6-4e2d-ad42-93827c4f53a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FinsetFunctionsRecoveredFromValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MultilinearSumEqOfProdFunEq
import Theorems.Thm_GlobalTheory_T_exists_finset_eq_sum_smul_of_mem_submodule


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
namespace GlobalTheory
theorem _root_.solution
    {ι κ : Type} [Fintype ι] {X : ι → Type} (V : ∀ l, Submodule ℂ (X l → ℂ))
    (Φ : MultilinearMap ℂ (fun l => V l) ℂ) (a : κ →₀ ℂ) (f g : κ → ∀ l, V l) :
    (∀ z : ∀ l, X l, (a.sum fun c b => b * ∏ l, (f c l : X l → ℂ) (z l)) =
        a.sum fun c b => b * ∏ l, (g c l : X l → ℂ) (z l)) →
    (a.sum fun c b => b * Φ (f c)) = a.sum fun c b => b * Φ (g c) := by
  classical
  intro h
  have hkey : ∀ l, ∃ (s : Finset (X l)) (E : X l → X l → ℂ), (∀ x, E x ∈ V l) ∧
      ∀ u ∈ (a.support.image (fun c => (f c l : X l → ℂ)) ∪
        a.support.image (fun c => (g c l : X l → ℂ))), u = ∑ x ∈ s, u x • E x := fun l =>
    GlobalTheory.T.exists_finset_eq_sum_smul_of_mem_submodule (V l) _ (by
      intro u hu
      simp only [Finset.mem_union, Finset.mem_image] at hu
      rcases hu with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (f c l).2
      · exact (g c l).2)
  choose s E hEV hE using hkey
  let e : ∀ l, X l → V l := fun l x => ⟨E l x, hEV l x⟩
  have expand : ∀ (u : ∀ l, V l),
      (∀ l, (u l : X l → ℂ) = ∑ x ∈ s l, (u l : X l → ℂ) x • E l x) →
      Φ u = ∑ ξ ∈ Fintype.piFinset s, (∏ l, (u l : X l → ℂ) (ξ l)) * Φ (fun l => e l (ξ l)) := by
    intro u hu
    have hu' : u = fun l => ∑ x ∈ s l, (u l : X l → ℂ) x • e l x := by
      funext l
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hu l
    conv_lhs => rw [hu', MultilinearMap.map_sum_finset]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  have gen : ∀ f' : κ → ∀ l, V l,
      (∀ c ∈ a.support, ∀ l, (f' c l : X l → ℂ) = ∑ x ∈ s l, (f' c l : X l → ℂ) x • E l x) →
      (a.sum fun c b => b * Φ (f' c)) = ∑ ξ ∈ Fintype.piFinset s,
        (a.sum fun c b => b * ∏ l, (f' c l : X l → ℂ) (ξ l)) * Φ (fun l => e l (ξ l)) := by
    intro f' hf'
    calc (a.sum fun c b => b * Φ (f' c))
        = ∑ c ∈ a.support, a c * ∑ ξ ∈ Fintype.piFinset s,
            (∏ l, (f' c l : X l → ℂ) (ξ l)) * Φ (fun l => e l (ξ l)) := by
          unfold Finsupp.sum
          refine Finset.sum_congr rfl fun c hc => ?_
          show a c * Φ (f' c) = _
          rw [expand (f' c) (hf' c hc)]
      _ = _ := by
          simp only [Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun c _ => ?_
          ring
  rw [gen f (fun c hc l => hE l _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))),
    gen g (fun c hc l => hE l _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)))]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [h ξ]
end GlobalTheory
