-- Prove2me | solution 1 for GlobalTheory.KernelComm.KK_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:29:34.030809+00:00
-- url     : https://prove2.me/submissions/a0130ec6-f8e0-4eb1-ada8-5f9d7b16a437

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_KernelComm_KK_smul
import Theorems.Thm_GlobalTheory_LatPair_phiOne_smul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_iff
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos


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
theorem _root_.solution {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (u : kˣ) (g : GL n' k) (h : GL n k)
    (hg : valuation k ((Matrix.GeneralLinearGroup.det g * u : kˣ) : k) = 1)
    (hh : valuation k ((Matrix.GeneralLinearGroup.det h * u : kˣ) : k) = 1) :
    KK hμ hθ P₀ Q₀ φ (h • Q₀) =
      (((nabs k u)⁻¹ ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) •
        θ (φ (g • P₀)) (phiOneSB (g • P₀) (h • Q₀)) := by
  rw [KK_smul, hφ g, ← map_smul]
  refine (hθ g h _ _ _ ?_).symm
  ext x
  have m : ∀ z : kˣ, valuation k ((z * u : kˣ) : k) = 1 → μ z = (μ u)⁻¹ ∧ nabs k z = (nabs k u)⁻¹ := fun z hz =>
    ⟨eq_inv_of_mul_eq_one_left (by rw [← map_mul, hμ _ hz]),
      eq_inv_of_mul_eq_one_left (by rw [← nabs_mul, (nabs_eq_one_iff _).2 hz])⟩
  have hp : 0 < (nabs k u)⁻¹ := inv_pos.2 (nabs_pos k u)
  simp only [om, (m _ hg).1, (m _ hg).2, (m _ hh).1, (m _ hh).2, phiOneSB, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, phiOne_smul, Units.mul_inv, one_mul]
  rw [← Complex.ofReal_mul, ← Real.rpow_add hp]
  congr 3
  ring
end GlobalTheory.KernelComm
