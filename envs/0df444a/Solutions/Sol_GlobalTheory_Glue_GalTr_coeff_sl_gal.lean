-- Prove2me | solution 1 for GlobalTheory.Glue.GalTr.coeff_sl_gal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:05.530846+00:00
-- url     : https://prove2.me/submissions/4fb6534a-5b07-4858-bded-640b0f365fe1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open GlobalTheory GlobalTheory.Glue
open GlobalTheory.KZ GlobalTheory.K5
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl}
  {io : KT X (p ^ n) →+* Ωl}
namespace GlobalTheory.Glue
namespace GalTr
theorem _root_.solution (X : GlobalTheory.KZ.Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (b : ℕ) (y : X.K) (r : ℚ) :
    (X.exp (X.sl (ofSL (ModularGroup.T ^ b)) (X.gal s y))).coeff r = eOm ε (r * b) * s ((X.exp y).coeff r) := by
  have he : ∀ i k, ent (ofSL (ModularGroup.T ^ b)) i k = ((!![1, (b : ℤ); 0, 1] i k : ℤ) : ℚ) := fun i k => by
    rw [← ModularGroup.coe_T_zpow, zpow_natCast]; rfl
  have h := X.exp_upper (ofSL (ModularGroup.T ^ b)) (by rw [he]; simp) (X.gal s y) r
  rw [he, he, he, X.gal_exp] at h
  simpa using h
end GalTr
end GlobalTheory.Glue
