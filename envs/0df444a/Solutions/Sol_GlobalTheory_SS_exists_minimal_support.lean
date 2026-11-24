-- Prove2me | solution 1 for GlobalTheory.SS.exists_minimal_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:17.915374+00:00
-- url     : https://prove2.me/submissions/1f0c27da-4717-45f8-a866-0d2fa814f740

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightedRelationOfMinimalSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution {F J : Type} [Field F] (A : Finset J) (M : (J → F) → Prop)
    (L : (J → F) → F) (hM : ∀ v w (a : F), M v → M w → M (fun i => v i - a * w i))
    (hL : ∀ v w (a : F), L (fun i => v i - a * w i) = L v - a * L w)
    (v : J → F) (hv : M v) (hLv : L v ≠ 0) :
    ∃ v', M v' ∧ L v' ≠ 0 ∧ ∀ w, M w → (∀ i ∈ A, v' i = 0 → w i = 0) →
      ∀ i₀ ∈ A, v' i₀ ≠ 0 → w i₀ = 0 → ∀ i ∈ A, w i = 0 := by
  classical
  let s : (J → F) → Finset J := fun u => A.filter (fun i => u i ≠ 0)
  have hex : ∃ n, ∃ u, M u ∧ L u ≠ 0 ∧ (s u).card = n := ⟨_, v, hv, hLv, rfl⟩
  obtain ⟨v', hMv', hLv', hcard⟩ := Nat.find_spec hex
  refine ⟨v', hMv', hLv', ?_⟩
  have hmin : ∀ u, M u → L u ≠ 0 → s u ⊆ s v' → s u ≠ s v' → False := by
    intro u hMu hLu hsub hne
    have hlt : (s u).card < (s v').card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    rw [hcard] at hlt
    exact Nat.find_min hex hlt ⟨u, hMu, hLu, rfl⟩
  intro w hMw hsupp i₀ hi₀ hv'i₀ hwi₀ j hj
  by_contra hwj
  have hv'j : v' j ≠ 0 := fun h => hwj (hsupp j hj h)
  by_cases hLw : L w = 0
  · have hMu : M (fun i => v' i - v' j / w j * w i) := hM v' w _ hMv' hMw
    have hLu : L (fun i => v' i - v' j / w j * w i) ≠ 0 := by
      rw [hL v' w, hLw, mul_zero, sub_zero]
      exact hLv'
    apply hmin _ hMu hLu
    · intro i hi
      simp only [s, Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, fun h => hi.2 ?_⟩
      rw [h, hsupp i hi.1 h, mul_zero, sub_zero]
    · intro heq
      have hjs : j ∈ s v' := by simp [s, hj, hv'j]
      rw [← heq] at hjs
      simp only [s, Finset.mem_filter] at hjs
      exact hjs.2 (by rw [div_mul_cancel₀ _ hwj, sub_self])
  · apply hmin w hMw hLw
    · intro i hi
      simp only [s, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, fun h => hi.2 (hsupp i hi.1 h)⟩
    · intro heq
      have hi₀s : i₀ ∈ s v' := by simp [s, hi₀, hv'i₀]
      rw [← heq] at hi₀s
      simp [s, hwi₀] at hi₀s
end GlobalTheory.SS
