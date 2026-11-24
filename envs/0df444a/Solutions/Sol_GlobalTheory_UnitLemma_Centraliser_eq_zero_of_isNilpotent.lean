-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Centraliser.eq_zero_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:20.996683+00:00
-- url     : https://prove2.me/submissions/b24e24da-18cd-403d-bb72-e36da4ae961a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_P_dvd_of_aeval_eq_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_aeval_g_P
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_exists_aeval_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Centraliser
namespace GlobalTheory.UnitLemma.Centraliser
theorem _root_.solution {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (a : B.A)
    (ha : IsNilpotent a) : a = 0 := by
  obtain ⟨p, rfl⟩ := exists_aeval_eq B hsep a
  obtain ⟨m, hm⟩ := ha
  have h1 : B.P ∣ p ^ m := P_dvd_of_aeval_eq_zero B hsep _ (by rw [map_pow, hm])
  obtain ⟨q, rfl⟩ := hsep.squarefree.isRadical m p h1
  rw [map_mul, aeval_g_P, zero_mul]
end GlobalTheory.UnitLemma.Centraliser
