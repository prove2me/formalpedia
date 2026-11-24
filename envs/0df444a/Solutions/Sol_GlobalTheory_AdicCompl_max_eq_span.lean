-- Prove2me | solution 1 for GlobalTheory.AdicCompl.max_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:55:33.769673+00:00
-- url     : https://prove2.me/submissions/b50de3a7-223d-458d-8c67-fb76957091b1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
import Theorems.Thm_GlobalTheory_AdicCompl_lt_one_iff_le
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
theorem _root_.solution {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal Ow = Ideal.span {π} := by
  ext x
  rw [mem_max_iff, Ideal.mem_span_singleton, lt_one_iff_le, ← hπ]
  exact (adicCompletionIntegers.integers L w).le_iff_dvd
end GlobalTheory.AdicCompl
