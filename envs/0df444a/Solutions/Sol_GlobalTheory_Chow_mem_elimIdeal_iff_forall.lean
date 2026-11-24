-- Prove2me | solution 1 for GlobalTheory.Chow.mem_elimIdeal_iff_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:55.151582+00:00
-- url     : https://prove2.me/submissions/4424cb9b-a79b-48ec-b571-acf9870ee005

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [CommRing K] {σ β β' : Type*} [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution {p : Ideal (MvPolynomial σ K)} {f : MvPolynomial (β × σ) K} :
    f ∈ elimIdeal β p ↔ ∀ j, ∃ m : ℕ, map C f * C (X j ^ m) ∈ incidenceIdeal β p := by
  refine ⟨fun ⟨m, hm⟩ j => ⟨m, hm j⟩, fun h => ?_⟩
  choose m hm using h
  refine ⟨∑ j, m j, fun j => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  rw [hk, pow_add, C_mul, ← mul_assoc]
  exact Ideal.mul_mem_right _ _ (hm j)
end GlobalTheory.Chow
