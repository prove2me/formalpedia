-- Prove2me | solution 1 for GlobalTheory.exists_natForm_norm_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:47.60043+00:00
-- url     : https://prove2.me/submissions/7cbd2d70-fa6c-4132-97e8-63deb93dc29c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEmbeddingsOverInjective

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
namespace GlobalTheory
theorem _root_.solution {ι J : Type*} [Fintype ι] [DecidableEq ι] (T : Finset J) (n : ℕ)
    (hn : T.card ≤ n) (v : J → ι → ℂ) (ε : ℝ) (hv : ∀ j ∈ T, ∃ a, ε ≤ ‖v j a‖) :
    ∃ c : ι → Fin (n + 1), ∀ j ∈ T, ε / 2 ≤ ‖∑ a, ((c a : ℕ) : ℂ) * v j a‖ := by
  classical
  by_contra hcon
  push Not at hcon
  set bad : J → Finset (ι → Fin (n + 1)) := fun j =>
    Finset.univ.filter fun c => ‖∑ a, ((c a : ℕ) : ℂ) * v j a‖ < ε / 2 with hbad
  set N := Fintype.card (ι → Fin (n + 1)) with hN
  have hNpos : 0 < N := Fintype.card_pos
  have h1 : ∀ j ∈ T, (bad j).card * (n + 1) ≤ N := by
    intro j hj
    obtain ⟨a, ha⟩ := hv j hj
    have hinj : Set.InjOn (fun p : (ι → Fin (n + 1)) × Fin (n + 1) => Function.update p.1 a p.2)
        ((bad j ×ˢ (Finset.univ : Finset (Fin (n + 1))) : Finset _) : Set _) := by
      rintro ⟨c, k⟩ hc ⟨c', k'⟩ hc' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hbad, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.coe_univ, Set.mem_univ, and_true] at hc hc'
      have hk : k = k' := by simpa using congrFun h a
      have hoff : ∀ b, b ≠ a → c b = c' b := fun b hb => by
        simpa [Function.update_of_ne hb] using congrFun h b
      have hsum : (∑ b, ((c b : ℕ) : ℂ) * v j b) - ∑ b, ((c' b : ℕ) : ℂ) * v j b
          = ((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ) * v j a := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
        · push_cast; ring
        · intro b _ hb; rw [hoff b hb]; ring
        · simp
      have hlt : ‖((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ) * v j a‖ < ε := by
        rw [← hsum]
        have := norm_sub_le (∑ b, ((c b : ℕ) : ℂ) * v j b) (∑ b, ((c' b : ℕ) : ℂ) * v j b)
        linarith
      have hca : c a = c' a := by
        by_contra hne
        have hz : (((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) ≠ 0 := by
          intro h0
          apply hne
          apply Fin.ext
          omega
        have h1 : (1 : ℝ) ≤ ‖((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ)‖ := by
          rw [Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs hz
        rw [norm_mul] at hlt
        nlinarith [norm_nonneg (v j a)]
      refine Prod.ext ?_ hk
      funext b
      by_cases hb : b = a
      · subst hb; exact hca
      · exact hoff b hb
    have := Finset.card_le_card_of_injOn _ (t := Finset.univ) (fun _ _ => by simp) hinj
    simpa [hN] using this
  have h2 : (Finset.univ : Finset (ι → Fin (n + 1))) ⊆ T.biUnion bad := by
    intro c _
    obtain ⟨j, hj, h⟩ := hcon c
    exact Finset.mem_biUnion.2 ⟨j, hj, by simpa [hbad] using h⟩
  have h3 : N ≤ ∑ j ∈ T, (bad j).card := (Finset.card_le_card h2).trans Finset.card_biUnion_le
  have h4 : N * (n + 1) ≤ T.card * N := by
    calc N * (n + 1) ≤ (∑ j ∈ T, (bad j).card) * (n + 1) := Nat.mul_le_mul_right _ h3
      _ = ∑ j ∈ T, (bad j).card * (n + 1) := Finset.sum_mul ..
      _ ≤ ∑ j ∈ T, N := Finset.sum_le_sum h1
      _ = T.card * N := by simp
  nlinarith
end GlobalTheory
