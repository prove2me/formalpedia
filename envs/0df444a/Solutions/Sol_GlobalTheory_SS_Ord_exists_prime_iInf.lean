-- Prove2me | solution 1 for GlobalTheory.SS.Ord.exists_prime_iInf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:54.98884+00:00
-- url     : https://prove2.me/submissions/e3649e4e-3b40-45f1-b062-ae49d8a36945

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
theorem _root_.solution {B : Type} [CommRing B] {p : B} (hp : Prime p) (h0 : p ∈ nonZeroDivisors B) :
    ∃ J : Ideal B, J.IsPrime ∧ p ∉ J ∧ ∀ b, (∀ n : ℕ, p ^ n ∣ b) → b ∈ J := by
  classical
  have hcan : ∀ (n : ℕ) (a b : B), p ^ n * a = p ^ n * b → a = b := fun n a b h =>
    (mul_cancel_left_mem_nonZeroDivisors (pow_mem h0 n)).1 h
  have hmem : ∀ b, b ∈ (⨅ n : ℕ, Ideal.span {p ^ n}) ↔ ∀ n : ℕ, p ^ n ∣ b := fun b => by
    simp [Ideal.mem_iInf, Ideal.mem_span_singleton]
  have hnot : p ∉ (⨅ n : ℕ, Ideal.span {p ^ n}) := fun h => by
    obtain ⟨c, hc⟩ := (hmem p).1 h 2
    exact hp.not_dvd_one ⟨c, hcan 1 _ _ (by linear_combination hc)⟩
  have hdec : ∀ b, b ∉ (⨅ n : ℕ, Ideal.span {p ^ n}) → ∃ (n : ℕ) (a : B), b = p ^ n * a ∧ ¬ p ∣ a := by
    intro b hb
    rw [hmem, not_forall] at hb
    have h1 : Nat.find hb ≠ 0 := fun e => by simpa [e] using Nat.find_spec hb
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h1
    obtain ⟨a, ha⟩ := not_not.1 (Nat.find_min hb (m := m) (by omega))
    refine ⟨m, a, ha, fun ⟨e, he⟩ => Nat.find_spec hb ⟨e, ?_⟩⟩
    rw [hm, ha, he, pow_succ, _root_.mul_assoc]
  refine ⟨⨅ n : ℕ, Ideal.span {p ^ n}, ⟨fun e => hnot (e ▸ trivial), fun {x y} hxy => ?_⟩, hnot,
    fun b hb => (hmem b).2 hb⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨m, a, ha, ha'⟩ := hdec x hcon.1
  obtain ⟨n, b, hb, hb'⟩ := hdec y hcon.2
  obtain ⟨c, hc⟩ := (hmem _).1 hxy (m + n + 1)
  have : a * b = p * c := hcan (m + n) _ _ (by rw [ha, hb] at hc; linear_combination hc)
  exact (hp.dvd_or_dvd ⟨c, this⟩).elim ha' hb'
end GlobalTheory.SS.Ord
