-- Prove2me | solution 1 for KatzModularForm.toFun_tateBase_eq_qExpand_coeffMap_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7ec50551-9b75-582b-9161-9494c41df398

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KatzModularForm_toFun_tateBase_eq_qExpand_coeffMap_qExpansion

set_option autoImplicit false

universe u

open ModularCurve HahnSeries

namespace KatzModularForm
p2m_export "KatzModularForm" "ext qExpansion toFun map_toFun"
namespace TateBaseGlue
p2m_open "KatzModularForm"

variable (R₀ : Type u) [CommRing R₀] (R : Type u) [CommRing R] [Algebra R₀ R]

noncomputable def coeffMapₐ : LaurentSeries R₀ →ₐ[R₀] LaurentSeries R :=
  { coeffMap (algebraMap R₀ R) with
    commutes' := fun r => by
      show coeffMap (algebraMap R₀ R) (algebraMap R₀ (LaurentSeries R₀) r) =
        algebraMap R₀ (LaurentSeries R) r
      rw [algebraMap_laurentSeries_apply, algebraMap_laurentSeries_apply, Algebra.algebraMap_self,
        RingHom.id_apply, HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single] }

theorem coe_coeffMapₐ :
    ((coeffMapₐ R₀ R : LaurentSeries R₀ →ₐ[R₀] LaurentSeries R) : LaurentSeries R₀ →+* LaurentSeries R)
      = coeffMap (algebraMap R₀ R) :=
  RingHom.ext fun _ => rfl

variable (p : ℕ) [NeZero p]

noncomputable def qExpandₐ : LaurentSeries R →ₐ[R₀] LaurentSeries R :=
  { qExpand R p with
    commutes' := fun r => by
      show qExpand R p (algebraMap R₀ (LaurentSeries R) r) = algebraMap R₀ (LaurentSeries R) r
      rw [algebraMap_laurentSeries_apply, qExpand_C] }

theorem coe_qExpandₐ :
    ((qExpandₐ R₀ R p : LaurentSeries R →ₐ[R₀] LaurentSeries R) : LaurentSeries R →+* LaurentSeries R)
      = qExpand R p :=
  RingHom.ext fun _ => rfl

variable {R₀ R}

theorem coeffMap_laurentOfInt {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : PowerSeries ℤ) :
    coeffMap f (laurentOfInt A g) = laurentOfInt B g := by
  ext n
  rw [coeffMap_coeff, laurentOfInt_apply, laurentOfInt_apply, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero f
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]

theorem tateLaurent_map_coeffMap {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    (tateLaurent A).map (coeffMap f) = tateLaurent B := by
  simp only [tateLaurent, WeierstrassCurve.map, coeffMap_laurentOfInt]

theorem tateBase_eq :
    tateBase R p =
      ((tateLaurent R₀).map
          ((coeffMapₐ R₀ R : LaurentSeries R₀ →ₐ[R₀] LaurentSeries R) : LaurentSeries R₀ →+* LaurentSeries R)).map
        ((qExpandₐ R₀ R p : LaurentSeries R →ₐ[R₀] LaurentSeries R) : LaurentSeries R →+* LaurentSeries R) := by
  rw [coe_coeffMapₐ, coe_qExpandₐ, tateLaurent_map_coeffMap, tateBase]

variable {k : ℤ} (g : KatzModularForm R₀ k)

theorem toFun_congr {A : Type u} [CommRing A] [Algebra R₀ A] {W W' : WeierstrassCurve A}
    (h : W = W') (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) : g.toFun W hW = g.toFun W' hW' := by
  subst h; rfl

theorem main :
    g.toFun (tateBase R p) (isUnit_Δ_tateBase R p)
      = qExpand R p (coeffMap (algebraMap R₀ R) g.qExpansion) := by
  have hW1 : IsUnit ((tateLaurent R₀).map
      ((coeffMapₐ R₀ R : LaurentSeries R₀ →ₐ[R₀] LaurentSeries R) : LaurentSeries R₀ →+* LaurentSeries R)).Δ := by
    rw [coe_coeffMapₐ, tateLaurent_map_coeffMap]; exact (tateLaurent R).isUnit_Δ
  have hW2 : IsUnit (((tateLaurent R₀).map
      ((coeffMapₐ R₀ R : LaurentSeries R₀ →ₐ[R₀] LaurentSeries R) : LaurentSeries R₀ →+* LaurentSeries R)).map
        ((qExpandₐ R₀ R p : LaurentSeries R →ₐ[R₀] LaurentSeries R) : LaurentSeries R →+* LaurentSeries R)).Δ := by
    rw [← tateBase_eq]; exact isUnit_Δ_tateBase R p
  rw [toFun_congr g (tateBase_eq p) (isUnit_Δ_tateBase R p) hW2,
    g.map_toFun (qExpandₐ R₀ R p) _ hW1 hW2,
    g.map_toFun (coeffMapₐ R₀ R) (tateLaurent R₀) (tateLaurent R₀).isUnit_Δ hW1]
  rfl

end KatzModularForm.TateBaseGlue

theorem solution
    {R₀ : Type u} [CommRing R₀] {k : ℤ} (g : KatzModularForm R₀ k)
    (R : Type u) [CommRing R] [Algebra R₀ R] (p : ℕ) [NeZero p] :
    g.toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p)
      = ModularCurve.qExpand R p (ModularCurve.coeffMap (algebraMap R₀ R) g.qExpansion) :=
  KatzModularForm.TateBaseGlue.main p g

end S_KatzModularForm_toFun_tateBase_eq_qExpand_coeffMap_qExpansion
end P2MW
export P2MW.S_KatzModularForm_toFun_tateBase_eq_qExpand_coeffMap_qExpansion (solution)
