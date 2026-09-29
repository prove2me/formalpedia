-- Prove2me | solution 1 for MvFormalGroup.CartierModule.verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/53f33cf0-4293-56d3-8148-7a63788b006e

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
p2m_attr_erase "instance" "MvFormalGroup.instIsCommMapRingHom MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R]
    [Algebra (PadicInt p) R]
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Injective
        (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)) ∧
      Function.Surjective
        (MvFormalGroup.CartierModule.tangent : MvFormalGroup.CartierModule p Φ → Fin d → R) ∧
      (∀ f : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.tangent f = 0 ↔
          ∃ g : MvFormalGroup.CartierModule p Φ,
            MvFormalGroup.CartierModule.verschiebungInt g = f) ∧
      (∀ x : ℕ → MvFormalGroup.CartierModule p Φ,
        ∃! s : MvFormalGroup.CartierModule p Φ, ∀ N : ℕ, ∃ t : MvFormalGroup.CartierModule p Φ,
          s = (∑ m ∈ Finset.range N,
                (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m] (x m)) +
              (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] t) :=
  ⟨MvFormalGroup.CartierModule.verschiebungInt_injective_of_algebra_padicInt p Φ,
   MvFormalGroup.CartierModule.tangent_surjective_of_algebra_padicInt p Φ,
   fun f => ⟨fun hf => MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt p Φ f hf,
     fun ⟨g, hg⟩ => hg ▸ MvFormalGroup.CartierModule.tangent_verschiebungInt g⟩,
   fun x => MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p Φ x⟩

#print axioms solution

end S_MvFormalGroup_CartierModule_verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt (solution)
