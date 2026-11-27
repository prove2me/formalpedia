-- Prove2me | solution 1 for GlobalTheory.exists_eq_algebraMap_add_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:18.640271+00:00
-- url     : https://prove2.me/submissions/94683753-ceb0-4c3b-bb67-a823656af65d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure

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
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R R' : Type} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] {ϖ : R}
    (hϖ : IsLocalRing.maximalIdeal R' = Ideal.span {algebraMap R R' ϖ})
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R'))) (n : ℕ)
    (r' : R') : ∃ (r : R) (s : R'), r' = algebraMap R R' r + algebraMap R R' ϖ ^ n * s := by
  have h1 : ∀ r' : R', ∃ (r : R) (s : R'), r' = algebraMap R R' r + algebraMap R R' ϖ * s := by
    intro r'
    obtain ⟨a, ha⟩ := hres (IsLocalRing.residue R' r')
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
    rw [IsLocalRing.ResidueField.map_residue] at ha
    have hm : r' - algebraMap R R' r ∈ IsLocalRing.maximalIdeal R' := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ha, sub_self]
    rw [hϖ, Ideal.mem_span_singleton] at hm
    obtain ⟨s, hs⟩ := hm
    exact ⟨r, s, by rw [← hs]; ring⟩
  induction n with
  | zero => exact ⟨0, r', by simp⟩
  | succ n ih =>
    obtain ⟨r, s, hs⟩ := ih
    obtain ⟨r₁, s₁, hs₁⟩ := h1 s
    refine ⟨r + ϖ ^ n * r₁, s₁, ?_⟩
    rw [hs, hs₁, map_add, map_mul, map_pow]
    ring
end GlobalTheory
