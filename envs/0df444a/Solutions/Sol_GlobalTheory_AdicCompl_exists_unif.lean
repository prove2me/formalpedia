-- Prove2me | solution 1 for GlobalTheory.AdicCompl.exists_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:55:31.991989+00:00
-- url     : https://prove2.me/submissions/53c9451e-4844-4972-9a13-6ee76db69082

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
import Theorems.Thm_GlobalTheory_AdicCompl_lt_one_iff_le
import Theorems.Thm_GlobalTheory_AdicCompl_v_algebraMap

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
theorem _root_.solution : ∃ π : Ow, Valued.v (π : Lw) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  have h : Valued.v (algebraMap L Lw π) = WithZero.exp (-1 : ℤ) := by
    rw [v_algebraMap, hπ]
  refine ⟨⟨algebraMap L Lw π, ?_⟩, h⟩
  rw [mem_adicCompletionIntegers, h]
  exact ((lt_one_iff_le _).2 le_rfl).le
end GlobalTheory.AdicCompl
