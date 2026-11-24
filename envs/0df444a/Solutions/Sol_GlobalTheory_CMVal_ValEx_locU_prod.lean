-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.locU_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:56.885245+00:00
-- url     : https://prove2.me/submissions/3c1d1f63-e69e-4348-81a8-566990251cf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_locU_of_supp
import Theorems.Thm_GlobalTheory_CMVal_ValEx_locU_single
import Theorems.Thm_GlobalTheory_CMVal_suppAt_single


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
open Classical
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 E))) (k : Eˣ) (Q : HeightOneSpectrum (𝓞 E)) :
    locU Q (∏ P ∈ S, single P (toLoc P k)) = if Q ∈ S then toLoc Q k else 1 := by
  rw [map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem Q h fun P _ hP => locU_of_supp (suppAt_single P _) hP.symm, locU_single]
  · exact Finset.prod_eq_one fun P hP => locU_of_supp (suppAt_single P _) (fun e => h (e ▸ hP))
end GlobalTheory.CMVal.ValEx
