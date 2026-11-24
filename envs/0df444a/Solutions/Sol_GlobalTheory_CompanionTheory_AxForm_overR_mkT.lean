-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.overR_mkT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:11.062799+00:00
-- url     : https://prove2.me/submissions/645d26a5-260f-40fe-90c4-15af82a5275f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
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
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R S S' B M N : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S'] [CommRing B]
  [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
  [AddCommGroup N] [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N]
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution (ε : S →+* B) (l : Ω[S⁄R] →+ M) (hl : ∀ a ω, l (a • ω) = ε a • l ω)
    (he : ε.comp (algebraMap R S) = algebraMap R B) : OverR R (mkT ε l hl) := by
  ext r
  · simpa [mkT] using congrArg (fun q ↦ q r) he
  · simp [mkT]
end GlobalTheory.CompanionTheory.AxForm
