-- Prove2me | solution 1 for GlobalTheory.exists_finset_boundedBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:48.201204+00:00
-- url     : https://prove2.me/submissions/81facb54-850a-4d3f-8e50-c7de4c5b467b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_exists_finset_boundedBasis_of_gram
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PackingSeparation_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
theorem _root_.solution (X : DataX E r) {B : ℝ} (hB : 0 ≤ B) :
    ∃ V : Finset (Fin r → Fin r → E), (∀ v ∈ V, IsBoundedBasis X B v) ∧
      (∀ v, IsBoundedBasis X B v →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i) ∧
      (V.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
        ((X.NA : ℝ) * X.NC * r * B) ^ (2 * fdeg E * r ^ 2) * (X.g : ℝ) ^ (2 * fdeg E * r ^ 2) := by
  classical
  obtain ⟨hfin, hc⟩ := PackingSeparation.count (E := E) B hB
  rw [Set.ncard_eq_toFinset_card _ hfin] at hc
  choose V hV₁ hV₂ hV₃ using exists_finset_boundedBasis_of_gram X hB
  let T : Finset (Fin r → Fin r → 𝓞 E) :=
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => hfin.toFinset
  have hT : (T.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) := by
    rw [Fintype.card_piFinset_const, Fintype.card_piFinset_const]
    push_cast
    calc ((hfin.toFinset.card : ℝ) ^ r) ^ r ≤ (((1 + 2 * B) ^ (2 * fdeg E)) ^ r) ^ r := by gcongr
      _ = _ := by rw [← pow_mul, ← pow_mul, sq]
  refine ⟨T.biUnion fun A => V (Matrix.of A), fun v hv => ?_, fun v hv => ?_, ?_⟩
  · obtain ⟨A, -, h⟩ := Finset.mem_biUnion.1 hv
    exact hV₁ _ v h
  · let A : Fin r → Fin r → 𝓞 E := fun i k =>
      ⟨herm X.Gm (v i) (v k), X.L'_int _ (hv.1 i) _ (hv.1 k)⟩
    obtain ⟨γ, hγ, w, hw, h⟩ := hV₂ (Matrix.of A) v hv rfl
    refine ⟨γ, hγ, w, Finset.mem_biUnion.2 ⟨A, ?_, hw⟩, h⟩
    simp only [T, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun i k τ => hv.2.2 τ i k
  · calc ((T.biUnion fun A => V (Matrix.of A)).card : ℝ)
        ≤ ∑ A ∈ T, ((V (Matrix.of A)).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ T, ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) :=
          Finset.sum_le_sum fun A _ => hV₃ _
      _ = T.card * ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
          ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) := by gcongr
      _ = _ := by
          simp only [mul_pow]
          ring
end GlobalTheory
