-- Prove2me | solution 1 for GlobalTheory.KernelComm.FF_KK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:40:17.21805+00:00
-- url     : https://prove2.me/submissions/4caef072-e6b3-4486-be8c-21d3467c1e22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_KernelComm_KK_ram
import Theorems.Thm_GlobalTheory_KernelComm_FFStar_KK
import Theorems.Thm_GlobalTheory_KernelComm_scal_mul_scal
import Theorems.Thm_GlobalTheory_LatPair_FF_mem_EqForm
import Theorems.Thm_GlobalTheory_LatPair_Model_FF_dia
import Theorems.Thm_GlobalTheory_PairOp_FFStar_FF_ram
import Theorems.Thm_GlobalTheory_PairOp_FF_FFStar_ram
import Theorems.Thm_GlobalTheory_PairOp_FF_dia
import Theorems.Thm_GlobalTheory_PairOp_mem_ram
import Theorems.Thm_GlobalTheory_PairOp_resCard_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
  (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)
namespace GlobalTheory.KernelComm
theorem _root_.solution {t : ℕ} (ht : Fintype.card n = Fintype.card n' + (t + 1)) (q : Unif k) {χ : AddChar 𝓀[k] ℂ}
    (hχ : χ ≠ 1) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (h : φ ∈ Mram k n' V') :
    FF q χ (KK hμ hθ P₀ Q₀ φ) = scal k t • KK hμ hθ P₀ Q₀ (FF q χ φ) := by
  have h1 := mem_ram (FF_dia q χ) h
  have h2 := FF_mem_EqForm q χ hφ
  have h3 := congrArg (FF q χ) (FFStar_KK hμ hθ P₀ Q₀ ht q χ h2 h1)
  rw [FF_FFStar_ram q hχ (KK_ram hμ hθ P₀ Q₀ h2 h1), FFStar_FF_ram q hχ h, map_smul, map_smul, map_smul, ht,
    pow_add, ← scal_mul_scal, smul_smul] at h3
  have hs : scal k t ≠ 0 := fun h0 => by
    have := scal_mul_scal (k := k) t
    rw [h0, mul_zero] at this
    exact pow_ne_zero _ resCard_ne_zero this.symm
  refine smul_right_injective _ (mul_ne_zero hs (pow_ne_zero (Fintype.card n') (resCard_ne_zero (k := k)))) ?_
  simp only
  rw [← h3, smul_smul]
  congr 1
  ring
end GlobalTheory.KernelComm
