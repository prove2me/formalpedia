-- Prove2me | solution 1 for GlobalTheory.AdicCompl.exists_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:55:31.06789+00:00
-- url     : https://prove2.me/submissions/9a1047cd-f355-4e6b-8b10-98ba1d51597c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
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
theorem _root_.solution : ∃ e : ℕ, 0 < e ∧ ∀ x : L, valV Ow (kMap w x) = w.valuation L x ^ e := by
  let : Algebra L (FractionRing Ow) := (kMap w).toAlgebra
  have : IsScalarTower R L (FractionRing Ow) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R Ow (FractionRing Ow)]
    show _ = (FractionRing.algEquiv Ow Lw).symm (algebraMap L Lw (algebraMap R L r))
    have : algebraMap L Lw (algebraMap R L r) = algebraMap Ow Lw (algebraMap R Ow r) := by
      show _ = ((algebraMap R Ow r : Ow) : Lw)
      rw [algebraMap_adicCompletionIntegers_apply]
      rfl
    rw [this, AlgEquiv.commutes]
  let m : HeightOneSpectrum Ow := IsDiscreteValuationRing.maximalIdeal Ow
  have : m.asIdeal.LiesOver w.asIdeal := ⟨by
    ext a
    rw [Ideal.mem_comap]
    show _ ↔ algebraMap R Ow a ∈ IsLocalRing.maximalIdeal Ow
    rw [mem_max_iff, algebraMap_adicCompletionIntegers_apply,
      valuedAdicCompletion_eq_valuation', valuation_lt_one_iff_mem]⟩
  exact ⟨w.asIdeal.ramificationIdx' m.asIdeal,
    Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver m.asIdeal w.ne_bot),
    fun x => (valuation_liesOver (FractionRing Ow) w m x).symm⟩
end GlobalTheory.AdicCompl
