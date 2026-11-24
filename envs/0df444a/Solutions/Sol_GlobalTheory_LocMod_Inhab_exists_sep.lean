-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:08:43.322796+00:00
-- url     : https://prove2.me/submissions/c0136f98-abec-45a4-a64f-f40068dd7c07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Theorems.Thm_GlobalTheory_LocMod_Inhab_pairing_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.LocMod.Inhab
theorem _root_.solution {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) (a : kˣ) {u : Matrix Y Y' k}
    (hu : u ∉ box Y Y' a) : ∃ y ∈ box Y Y' (d / a), pairing ψ u y ≠ 1 := by
  obtain ⟨r, q, h⟩ : ∃ r q, valuation k (a : k) < valuation k (u r q) := by
    by_contra hh
    push Not at hh
    exact hu hh
  have ha : 0 < valuation k (a : k) := zero_lt_iff.2 (by simp)
  have hd0 : 0 < valuation k (d : k) := zero_lt_iff.2 (by simp)
  have hu0 : 0 < valuation k (u r q) := ha.trans h
  have hne : u r q ≠ 0 := fun e => by simp [e] at hu0
  have : ¬ ∀ z : k, valuation k z ≤ valuation k (u r q * (d / a)) → ψ z = 1 := fun hh => by
    have := (hd _).1 hh
    rw [map_mul, map_div₀, mul_div_left_comm, mul_le_iff_le_one_right hd0, div_le_one₀ ha] at this
    exact absurd h (not_lt.2 this)
  push Not at this
  obtain ⟨z, hz, hz1⟩ := this
  refine ⟨Matrix.single r q (z / u r q), fun r' q' => ?_, ?_⟩
  · rw [Matrix.single_apply]
    split_ifs
    · rw [map_div₀, div_le_iff₀ hu0, mul_comm, ← map_mul]
      simpa using hz
    · simp
  · rw [pairing_single, div_mul_cancel₀ _ hne]
    exact fun e => hz1 (Subtype.ext e)
end GlobalTheory.LocMod.Inhab
