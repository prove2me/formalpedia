-- Prove2me | solution 1 for GlobalTheory.exists_discreteValuationSubring_dominating_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:03.572582+00:00
-- url     : https://prove2.me/submissions/0b4ad118-2aab-4f85-97cb-f07dde23be9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {R L : Type*} [CommRing R] [IsLocalRing R] [Field L]
variable [IsNoetherianRing R] [Algebra R L]
namespace GlobalTheory
theorem _root_.solution [Algebra.EssFiniteType R L] {x : L}
    (hx : ¬ IsIntegral R x) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring ∧ x ∉ V := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx isIntegral_zero
  letI := invertibleOfNonzero (inv_ne_zero hx0)
  let B := Algebra.adjoin R {x⁻¹}
  let xinv : B := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
  have hne : (maximalIdeal R).map (algebraMap R B) ⊔ Ideal.span {xinv} ≠ ⊤ := by
    intro heq
    obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
      x⁻¹ _ (maximalIdeal.isMaximal R).ne_top heq
    have H : IsUnit p.leadingCoeff := of_not_not fun h ↦ by simpa using sub_mem h hp
    refine hx ⟨Polynomial.C H.unit⁻¹.1 * p,
      Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by simp), ?_⟩
    rw [invOf_eq_inv, inv_inv] at hpx
    rw [← Polynomial.aeval_def, map_mul, hpx, mul_zero]
  obtain ⟨W, hW, hW'⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ hne
  have hWd : LocalSubring.range (algebraMap R L) ≤ W.toLocalSubring := by
    rw [localSubring_range_le_valuationSubring_iff]
    exact ⟨fun r => hW (B.algebraMap_mem r), fun r hr =>
      hW' ⟨_, Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hr), rfl⟩⟩
  have hxW : x⁻¹ ∈ W.nonunits := hW' ⟨xinv, Ideal.mem_sup_right (Ideal.subset_span rfl), rfl⟩
  obtain ⟨V, h1, h2, -, h3⟩ := exists_discreteValuationSubring_dominating_of_le W hWd
    Set.finite_empty (Set.finite_singleton x⁻¹) (by simp) (by simpa using hxW)
    (Or.inr ⟨_, rfl, inv_ne_zero hx0⟩)
  exact ⟨V, h1, h2, (V.inv_mem_nonunits_iff.mp (h3 _ rfl)).resolve_left hx0⟩
end GlobalTheory
