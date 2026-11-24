-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLift.tsz_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:25:55.71129+00:00
-- url     : https://prove2.me/submissions/e08f9978-2fb1-4ba0-afa3-4035497470ce

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZero
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
    (φ : P →+* TrivSqZeroExt B M) (hα : φ.comp α = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B))
    (hf : ∀ a, (φ a).fst = algebraMap R B (ε a)) :
    (tsz (uOf φ hα hf)).comp (theta h hsq) = φ := by
  refine RingHom.ext fun a ↦ ?_
  have e : φ (α (ε a)) = TrivSqZeroExt.inl (algebraMap R B (ε a)) := congrArg (fun f ↦ f (ε a)) hα
  have s : (uOf φ hα hf) (pr h a) = (φ a).snd := by
    change (φ (a - α (ε a))).snd = _
    simp [e]
  apply TrivSqZeroExt.ext
  · change (TrivSqZeroExt.inl (algebraMap R B (theta h hsq a).fst) +
      TrivSqZeroExt.inr ((uOf φ hα hf) (theta h hsq a).snd) : TrivSqZeroExt B M).fst = _
    simp [hf]
  · change (TrivSqZeroExt.inl (algebraMap R B (theta h hsq a).fst) +
      TrivSqZeroExt.inr ((uOf φ hα hf) (theta h hsq a).snd) : TrivSqZeroExt B M).snd = _
    simp [s]
end GlobalTheory.CompanionTheory.CotLift
