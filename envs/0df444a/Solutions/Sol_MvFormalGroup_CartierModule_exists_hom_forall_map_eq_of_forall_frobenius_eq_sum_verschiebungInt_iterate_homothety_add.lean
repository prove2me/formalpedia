-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/22596264-f491-5250-891e-e1f97d7bf891

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R] {d d' : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (Ψ : MvFormalGroup d' R) [Ψ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i j, MvFormalGroup.CartierModule.tangent (f i) j = if i = j then 1 else 0)
    (c : ℕ → Fin d → Fin d → R)
    (h : ℕ → Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (g : Fin d → MvFormalGroup.CartierModule p Ψ)
    (h' : ℕ → Fin d → MvFormalGroup.CartierModule p Ψ)
    (hexp' : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (g i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Ψ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (g l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Ψ)))^[N] (h' N i)) :
    ∃ φ : Φ.Hom Ψ, ∀ l, MvFormalGroup.CartierModule.map φ (f l) = g l := by
  refine MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul
    p Φ Ψ f hf (fun m i l => WittVector.teichmuller p (c m i l)) h (fun N i => ?_) g h' (fun N i => ?_)
  · simpa only [MvFormalGroup.CartierModule.teichmuller_smul] using hexp N i
  · simpa only [MvFormalGroup.CartierModule.teichmuller_smul] using hexp' N i

end S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add (solution)
