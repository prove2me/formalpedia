-- Prove2me | solution 1 for GlobalTheory.AdicCompl.finite_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:55:32.966888+00:00
-- url     : https://prove2.me/submissions/bbf4bbce-b04e-4bd3-a382-737ed9b0ec87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
import Theorems.Thm_GlobalTheory_AdicCompl_v_algebraMap
import Theorems.Thm_GlobalTheory_AdicCompl_mem_max_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open Formalism.L2.Pj Formalism.L2.PjFree
open IsDedekindDomain NumberField HeightOneSpectrum Filter
open scoped WithZero Topology
open GlobalTheory.AdicCompl
variable {R : Type} [CommRing R] [IsDedekindDomain R] {L : Type} [Field L] [Algebra R L]
  [IsFractionRing R L] (w : HeightOneSpectrum R)
local notation "Lw" => adicCompletion L w
local notation "Ow" => adicCompletionIntegers L w
namespace GlobalTheory.AdicCompl
theorem _root_.solution [Finite (R ⧸ w.asIdeal)] : Finite (IsLocalRing.ResidueField Ow) := by
  let φ : R →+* IsLocalRing.ResidueField Ow := (IsLocalRing.residue Ow).comp (algebraMap R Ow)
  have h0 : ∀ a ∈ w.asIdeal, φ a = 0 := by
    intro a ha
    show IsLocalRing.residue Ow (algebraMap R Ow a) = 0
    rw [IsLocalRing.residue_eq_zero_iff, mem_max_iff, algebraMap_adicCompletionIntegers_apply,
      valuedAdicCompletion_eq_valuation', valuation_lt_one_iff_mem]
    exact ha
  refine Finite.of_surjective (Ideal.Quotient.lift w.asIdeal φ h0) ?_
  apply Ideal.Quotient.lift_surjective_of_surjective
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hU : {y : Lw | (Valued.v : Valuation Lw ℤᵐ⁰).restrict (y - (x : Lw)) < 1} ∈ 𝓝 (x : Lw) := by
    rw [Valued.mem_nhds]
    exact ⟨1, subset_rfl⟩
  obtain ⟨l, hl⟩ := (denseRange_algebraMap L w).mem_nhds hU
  have hl' : Valued.v (algebraMap L Lw l - (x : Lw)) < 1 := by
    have : (Valued.v : Valuation Lw ℤᵐ⁰).restrict (algebraMap L Lw l - (x : Lw)) < 1 := hl
    rwa [Valuation.restrict_lt_iff_lt_embedding, map_one] at this
  have hl1 : w.valuation L l ≤ 1 := by
    rw [← v_algebraMap]
    have e : algebraMap L Lw l = (algebraMap L Lw l - (x : Lw)) + (x : Lw) := by ring
    rw [e]
    exact Valuation.map_add_le _ hl'.le ((mem_adicCompletionIntegers R L w).1 x.2)
  obtain ⟨a, ha⟩ := w.exists_valuation_sub_lt_of_integer hl1 1
  refine ⟨a, ?_⟩
  show IsLocalRing.residue Ow (algebraMap R Ow a) = IsLocalRing.residue Ow x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  have e : ((algebraMap R Ow a - x : Ow) : Lw) =
      algebraMap L Lw (algebraMap R L a - l) + (algebraMap L Lw l - (x : Lw)) := by
    have h1 : ((algebraMap R Ow a : Ow) : Lw) = algebraMap L Lw (algebraMap R L a) := by
      rw [algebraMap_adicCompletionIntegers_apply]
      rfl
    rw [AddSubgroupClass.coe_sub, h1, map_sub]
    ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ hl'
  rw [v_algebraMap]
  simpa using ha
end GlobalTheory.AdicCompl
