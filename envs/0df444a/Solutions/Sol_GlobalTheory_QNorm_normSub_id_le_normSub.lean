-- Prove2me | solution 1 for GlobalTheory.QNorm.normSub_id_le_normSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:43:49.439389+00:00
-- url     : https://prove2.me/submissions/4f78a605-7443-4592-a8a5-4ba3f3b0205a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_QNorm_mem_normSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) :
    normSub (RingHom.id F) δ ≤ normSub φ δ := by
  intro x hx
  obtain ⟨a, b, hab⟩ := (mem_normSub _ _ x).1 hx
  refine (mem_normSub _ _ x).2 ⟨φ a, φ b, ?_⟩
  have hab' : (x : F) = a ^ 2 - δ * b ^ 2 := hab
  rw [hab']
  simp [map_sub, map_mul, map_pow]
end GlobalTheory.QNorm
