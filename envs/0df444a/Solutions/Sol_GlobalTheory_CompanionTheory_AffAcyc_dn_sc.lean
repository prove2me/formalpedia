-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.dn_sc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:38:10.37995+00:00
-- url     : https://prove2.me/submissions/f606935d-9bbd-4df4-9334-a719a5249069

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution (F : C ⥤ CommAlgCat.{0} R) (g : ∀ T, F.obj T)
    (hg : ∀ (T T' : C) (φ : T ⟶ T'), mp F φ (g T) = g T') (n : ℕ) (z : Cn F n) :
    dn F n (sc F g n z) = sc F g (n + 1) (dn F n z) := by
  funext c
  simp only [sc, dn_apply, Finset.mul_sum, mul_smul_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  refine (map_mul _ _ _).trans ?_
  exact congrArg₂ (· * ·) (hg _ _ _) rfl
end GlobalTheory.CompanionTheory.AffAcyc
