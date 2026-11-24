-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwContract.val_pw_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:22.026359+00:00
-- url     : https://prove2.me/submissions/70176ac0-2c25-4381-baa4-c94182b45c0d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.IwContract
theorem _root_.solution {ϖ : Fˣ} (hϖ : valuation F (ϖ : F) < 1) {a : Fin n → ℤ} (ha : StrictlyDominant a)
    {i j : Fin n} (hij : i < j) :
    valuation F ((ϖ ^ (a i - a j) : Fˣ) : F) ≤ valuation F (ϖ : F) := by
  have hlt : a j < a i := ha hij
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a i - a j = ((k + 1 : ℕ) : ℤ) := ⟨(a i - a j - 1).toNat, by omega⟩
  rw [hk, zpow_natCast, Units.val_pow_eq_pow_val, map_pow, pow_succ]
  exact mul_le_of_le_one_left' (pow_le_one' hϖ.le k)
end GlobalTheory.CompanionTheory.IwContract
