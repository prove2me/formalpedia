-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.exists_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:47:50.429988+00:00
-- url     : https://prove2.me/submissions/5a71341b-404b-44c1-93c8-586ce8fbebd5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R V W V' W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (P Q : V →ₗ[R] W) (hb : Function.Bijective fun x : V × V ↦ P x.1 + Q x.2) :
    ∃ r s : W →ₗ[R] V, (∀ x, r (P x) = x) ∧ (∀ x, r (Q x) = 0) ∧ (∀ x, s (P x) = 0) ∧ ∀ x, s (Q x) = x := by
  let e : (V × V) ≃ₗ[R] W := LinearEquiv.ofBijective (P.coprod Q) hb
  have hP : ∀ x, e.symm (P x) = (x, 0) := fun x ↦ e.symm_apply_eq.2 (by
    change P x = P x + Q 0; simp)
  have hQ : ∀ x, e.symm (Q x) = (0, x) := fun x ↦ e.symm_apply_eq.2 (by
    change Q x = P 0 + Q x; simp)
  refine ⟨LinearMap.fst R V V ∘ₗ e.symm.toLinearMap, LinearMap.snd R V V ∘ₗ e.symm.toLinearMap, ?_, ?_, ?_, ?_⟩ <;>
    intro x <;> simp [hP, hQ]
end GlobalTheory.CompanionTheory.Hodge.LiftO
