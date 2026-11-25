-- Prove2me | solution 1 for GlobalTheory.prod_add_ite_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:56:13.626882+00:00
-- url     : https://prove2.me/submissions/a22a27db-b561-413f-aa0c-646ea1f6ce67

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliLeftComatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliDetMulVectorTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorPolyMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorIntertwiningApplyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsEigenSplitOfResolventIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QuantumDetVectorMultiplierShiftPlus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (ν : Fin n → ℂ) (s : Fin n) (u : ℂ) :
    (∏ t, (u + ν t + if t = s then 1 else 0)) =
      (∏ t, (u + ν t)) + ∏ t ∈ Finset.univ.erase s, (u + ν t) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s),
    ← Finset.mul_prod_erase Finset.univ (fun t => u + ν t) (Finset.mem_univ s)]
  have : ∏ t ∈ Finset.univ.erase s, (u + ν t + if t = s then 1 else 0) =
      ∏ t ∈ Finset.univ.erase s, (u + ν t) :=
    Finset.prod_congr rfl fun t ht => by simp [Finset.ne_of_mem_erase ht]
  rw [this]; simp only [if_true]; ring
end GlobalTheory
