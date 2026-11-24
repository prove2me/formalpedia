-- Prove2me | solution 1 for GlobalTheory.AdicCompl.mem_max_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:39.758816+00:00
-- url     : https://prove2.me/submissions/fdd01237-c478-4d56-a08e-c91e0cfe96ba

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
import Theorems.Thm_GlobalTheory_AdicCompl_max_eq_span

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
theorem _root_.solution {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) (x : Ow) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal Ow ^ n ↔ Valued.v (x : Lw) ≤ Valued.v (π : Lw) ^ n := by
  rw [max_eq_span w hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have := (adicCompletionIntegers.integers L w).le_iff_dvd (x := x) (y := π ^ n)
  rw [map_pow, map_pow] at this
  exact this.symm
end GlobalTheory.AdicCompl
