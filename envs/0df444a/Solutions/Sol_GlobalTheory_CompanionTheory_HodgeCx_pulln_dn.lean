-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeCx.pulln_dn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:37:07.064818+00:00
-- url     : https://prove2.me/submissions/eebb6cd5-25f3-42fc-a7d4-4f9079067906

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DnCompDn
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeCx_pulln_cof
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
open CategoryTheory GlobalTheory.CatCoh MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeCx
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
namespace GlobalTheory.CompanionTheory.HodgeCx
theorem _root_.solution {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (n : ℕ) :
    pulln m (n + 1) ∘ₗ dn F n = dn G n ∘ₗ pulln m n := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, MainStatements.Hodge.dn, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, map_zsmul, GlobalTheory.CompanionTheory.HodgeCx.pulln_cof]
end GlobalTheory.CompanionTheory.HodgeCx
