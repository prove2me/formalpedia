-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLift.snd_tsz_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:44:42.624801+00:00
-- url     : https://prove2.me/submissions/7ed9b86f-37a7-4e86-a738-c1b11316c0b8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_pr_val_self
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLift
variable {R P B M : Type} [CommRing R] [CommRing P] [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] {α : R →+* P} {ε : P →+* R}
namespace GlobalTheory.CompanionTheory.CotLift
theorem _root_.solution (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0)
    (u : KerW α ε →ₗ[R] M) (w : KerW α ε) : ((tsz (B := B) u).comp (theta h hsq) w.val).snd = u w := by
  change (TrivSqZeroExt.inl (algebraMap R B (theta h hsq w.val).fst) +
    TrivSqZeroExt.inr (u (theta h hsq w.val).snd) : TrivSqZeroExt B M).snd = _
  simp [pr_val_self]
end GlobalTheory.CompanionTheory.CotLift
