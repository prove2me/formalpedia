-- Prove2me | solution 1 for GlobalTheory.QNorm.div_mem_normSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:47.670816+00:00
-- url     : https://prove2.me/submissions/d80c9792-7fc4-4a86-b3cb-8005813e58fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNorm
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
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (z t : Fˣ)
    (a b : L) (h : φ (z : F) = φ (t : F) * (a ^ 2 - φ δ * b ^ 2)) : z / t ∈ normSub φ δ := by
  refine ⟨a, b, ?_⟩
  have ht : φ (t : F) ≠ 0 := by simp
  rw [Units.val_div_eq_div_val, map_div₀, h]
  field_simp
end GlobalTheory.QNorm
