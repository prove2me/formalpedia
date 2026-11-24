-- Prove2me | solution 1 for GlobalTheory.SS.Ord.exists_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:53.618546+00:00
-- url     : https://prove2.me/submissions/86cb9241-e502-4fb3-a531-aa41b19ad802

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder

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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
namespace GlobalTheory.SS.Ord
theorem _root_.solution {R B L I : Type} [CommRing R] [CommRing B] [CommRing L] [Fintype I]
    (c : R →+* B) (hc : c.FiniteType) (φ : B →+* L) (p : B) (δ : I → L →+ L)
    (hδ : ∀ i a b, δ i (a * b) = a * δ i b + b * δ i a) (h0 : ∀ i r, δ i (φ (c r)) = 0)
    (hloc : ∀ x : L, ∃ (k : ℕ) (b : B), φ b = φ p ^ k * x) :
    ∃ N : ℕ, ∀ i b, ∃ s, φ s = φ p ^ N * δ i (φ b) := by
  letI := c.toAlgebra
  obtain ⟨T, hT⟩ := (show Algebra.FiniteType R B from hc).1
  choose k a hk using hloc
  refine ⟨(Finset.univ ×ˢ T).sup fun q : I × B => k (δ q.1 (φ q.2)), fun i b => ?_⟩
  have hb : b ∈ Algebra.adjoin R (T : Set B) := hT ▸ trivial
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    have : k (δ i (φ x)) ≤ (Finset.univ ×ˢ T).sup fun q : I × B => k (δ q.1 (φ q.2)) :=
      Finset.le_sup (f := fun q : I × B => k (δ q.1 (φ q.2))) (b := (i, x)) (by simpa using hx)
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le this
    exact ⟨p ^ m * a (δ i (φ x)), by rw [hm, map_mul, hk, map_pow]; ring⟩
  | algebraMap r => exact ⟨0, by rw [show algebraMap R B r = c r from rfl, h0]; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    exact ⟨s + s', by simp only [map_add, hs, hs']; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    exact ⟨x * s' + y * s, by simp only [map_add, map_mul, hδ, hs, hs']; ring⟩
end GlobalTheory.SS.Ord
