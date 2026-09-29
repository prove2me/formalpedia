-- Prove2me | solution 1 for MvFormalGroup.CartierModule.presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a4f14e48-01d8-5b8d-adc0-5e3f616750fa

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_WittPointFamily
import Definitions.Def_MvFormalGroup_WittPointFamilyInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate

set_option autoImplicit false

universe u v

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ) (N : ℕ)
    (w : Fin N → Fin d → Fin d → WittVector p R)
    (h : Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ i, MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
          (∑ l : Fin d, w m i l • f l)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h i))
    {τ : Type v} (u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ) :
    MvFormalGroup.CartierModule.presPi f
        (fun l => MvFormalGroup.WittLaw.verPt (u l) -
          ∑ i : Fin d, ∑ m : Fin N, MvFormalGroup.WittLaw.wittSMulPt (w m i l)
            ((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[(m : ℕ)] (u i))) =
      MvFormalGroup.CartierModule.presPi h
        (fun i => (⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] (u i)) := by
  classical
  have hV : ∀ l, MvFormalGroup.CartierModule.evalPt (f l) (MvFormalGroup.WittLaw.verPt (u l)) =
      MvFormalGroup.CartierModule.evalPt (MvFormalGroup.CartierModule.frobenius (f l)) (u l) :=
    fun l => MvFormalGroup.CartierModule.evalPt_verPt _ _
  have hW : ∀ l i (m : Fin N), MvFormalGroup.CartierModule.evalPt (f l) (MvFormalGroup.WittLaw.wittSMulPt (w m i l)
      ((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[(m : ℕ)] (u i))) =
      MvFormalGroup.CartierModule.evalPt
        ((⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)] (w m i l • f l)) (u i) := by
    intro l i m
    rw [MvFormalGroup.CartierModule.evalPt_wittSMulPt, MvFormalGroup.CartierModule.evalPt_frobIntPt_iterate]
  have hiter : ∀ (m : ℕ) (g : Fin d → MvFormalGroup.CartierModule p Φ),
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m] (∑ l : Fin d, g l) =
        ∑ l : Fin d, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m] (g l) := by
    intro m
    induction m with
    | zero => intro g; rfl
    | succ m ih =>
      intro g
      rw [Function.iterate_succ_apply', ih, map_sum]
      exact Finset.sum_congr rfl fun l _ => (Function.iterate_succ_apply' _ m (g l)).symm
  have lhs : MvFormalGroup.CartierModule.presPi f
      (fun l => MvFormalGroup.WittLaw.verPt (u l) -
        ∑ i : Fin d, ∑ m : Fin N, MvFormalGroup.WittLaw.wittSMulPt (w m i l)
          ((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[(m : ℕ)] (u i))) =
      (∑ l : Fin d, MvFormalGroup.CartierModule.evalPt (MvFormalGroup.CartierModule.frobenius (f l)) (u l)) -
        ∑ l : Fin d, ∑ i : Fin d, ∑ m : Fin N, MvFormalGroup.CartierModule.evalPt
          ((⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)] (w m i l • f l)) (u i) := by
    rw [MvFormalGroup.CartierModule.presPi_def]
    simp only [map_sub, map_sum, hV, hW, Finset.sum_sub_distrib]
  have rhs : MvFormalGroup.CartierModule.presPi h
      (fun i => (⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] (u i)) =
      (∑ i : Fin d, MvFormalGroup.CartierModule.evalPt (MvFormalGroup.CartierModule.frobenius (f i)) (u i)) -
        ∑ i : Fin d, ∑ m : Fin N, ∑ l : Fin d, MvFormalGroup.CartierModule.evalPt
          ((⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)] (w m i l • f l)) (u i) := by
    rw [MvFormalGroup.CartierModule.presPi_def, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h i) =
        MvFormalGroup.CartierModule.frobenius (f i) -
          ∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
            (∑ l : Fin d, w m i l • f l) := eq_sub_of_add_eq' (hexp i).symm
    rw [MvFormalGroup.CartierModule.evalPt_frobIntPt_iterate, e, map_sub, AddMonoidHom.sub_apply, map_sum,
      AddMonoidHom.finsetSum_apply]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hiter, map_sum, AddMonoidHom.finsetSum_apply]
  rw [lhs, rhs]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end S_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate (solution)
