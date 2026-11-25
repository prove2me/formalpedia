-- Prove2me | solution 1 for GlobalTheory.GroupRingConst.eq_prod_powChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:02:18.704821+00:00
-- url     : https://prove2.me/submissions/b437e70e-c2e2-4a8b-a211-94779b4e7b95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Theorems.Thm_GlobalTheory_GroupRingConst_pt_single
import Theorems.Thm_GlobalTheory_GroupRingConst_powChar_apply
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val


attribute [local simp] GlobalTheory.GroupRingConst.pt_single
attribute [local simp] GlobalTheory.GroupRingConst.powChar_apply

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GroupRingConst
namespace GlobalTheory.GroupRingConst
theorem _root_.solution {G X I : Type} [CommGroup G] [AddCommGroup X] [Fintype I]
    (b : Module.Basis I ℤ X) (c : Multiplicative X →* G) :
    c = ∏ i, powChar (b.coord i).toAddMonoidHom (c (Multiplicative.ofAdd (b i))) := by
  refine MonoidHom.ext fun m => ?_
  obtain ⟨a, rfl⟩ : ∃ a, Multiplicative.ofAdd a = m := ⟨Multiplicative.toAdd m, rfl⟩
  rw [MonoidHom.finsetProd_apply]
  simp only [powChar_apply]
  conv_lhs => rw [← b.sum_repr a]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  simp [Module.Basis.coord_apply]
end GlobalTheory.GroupRingConst
