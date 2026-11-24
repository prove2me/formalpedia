-- Prove2me | solution 1 for GlobalTheory.UnRep.Nakayama.valuation_natCast_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:57.762181+00:00
-- url     : https://prove2.me/submissions/25997698-62c9-47b2-924c-7f387a37b5e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletion
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Nakayama
variable (F : Type) [Field F] [NumberField F]
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable (F : Type) [Field F] [NumberField F]
namespace GlobalTheory.UnRep.Nakayama
namespace _root_.GlobalTheory.UnRep.Nakayama
theorem _root_.solution (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : (N : 𝓞 F) ∈ v.asIdeal) :
    Valued.v ((N : ℕ) : v.adicCompletion F) < 1 := by
  have h := (v.valuation_lt_one_iff_mem (K := F) (N : 𝓞 F)).mpr hv
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (N : 𝓞 F)
  rw [← h2] at h
  convert h using 2
  first
  | simp
  | norm_cast
  | (push_cast; rfl)
end _root_.GlobalTheory.UnRep.Nakayama
end GlobalTheory.UnRep.Nakayama
