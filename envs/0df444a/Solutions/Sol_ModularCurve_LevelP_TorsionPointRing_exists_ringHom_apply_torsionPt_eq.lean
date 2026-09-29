-- Prove2me | solution 1 for ModularCurve.LevelP.TorsionPointRing.exists_ringHom_apply_torsionPt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a25e96f6-e3c5-57e3-9626-e0a9d1777163

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq

set_option autoImplicit false

universe u v

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "LevelP.TorsionPointRing LevelP.TorsionPointRing.ofBase LevelP.torsionPtX LevelP.torsionPtY indepElt_map LevelPData IsLevelPStructure"
namespace LevelP
p2m_export "ModularCurve.LevelP" "PsiRoot PsiRoot.ofBase psiRootX torsionQuadratic TorsionPointRing TorsionPointRing.ofPsiRoot TorsionPointRing.ofBase torsionPtX torsionPtY torsionPtCurve TwoPointRing TwoPointRing.ofOnePoint TwoPointRing.ofBase twoPointCurve TwoPointRing.xP TwoPointRing.yP TwoPointRing.xQ TwoPointRing.yQ indepDenom BasisRing BasisRing.ofTwoPoint BasisRing.ofBase basisCurve basisData"
p2m_open "ModularCurve.LevelP ModularCurve"

open Polynomial WeierstrassCurve

section Lift

variable {B : Type u} {A : Type v} [CommRing B] [CommRing A] (W : WeierstrassCurve B) (p : ℕ)

namespace PsiRoot p2m_export "ModularCurve.LevelP.PsiRoot" "ofBase" end PsiRoot
namespace PsiRoot
p2m_open_scoped "ModularCurve.LevelP.PsiRoot" in

private def _root_.ModularCurve.LevelP.PsiRoot.lift (φ : B →+* A) (x : A) (hx : ((W.map φ).preΨ p).eval x = 0) :
    PsiRoot W p →+* A :=
  AdjoinRoot.lift φ x (by rwa [WeierstrassCurve.map_preΨ, Polynomial.eval_map] at hx)

end PsiRoot
p2m_export "ModularCurve.LevelP" "PsiRoot.lift"
namespace PsiRoot
p2m_open_scoped "ModularCurve.LevelP.PsiRoot" in
@[scoped simp] private theorem _root_.ModularCurve.LevelP.PsiRoot.lift_ofBase (φ : B →+* A) (x : A) (hx) (b : B) :
    PsiRoot.lift W p φ x hx (PsiRoot.ofBase W p b) = φ b := by
  rw [PsiRoot.lift, PsiRoot.ofBase]
  erw [AdjoinRoot.lift_of]

end PsiRoot
p2m_export "ModularCurve.LevelP" "PsiRoot.lift_ofBase"
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot"
p2m_open_scoped "ModularCurve.LevelP.PsiRoot" in
@[scoped simp] theorem PsiRoot.lift_psiRootX (φ : B →+* A) (x : A) (hx) :
    PsiRoot.lift W p φ x hx (psiRootX W p) = x := by
  rw [PsiRoot.lift, psiRootX]
  erw [AdjoinRoot.lift_root]

p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot"
theorem torsionQuadratic_eval₂_eq_zero (φ : B →+* A) (x y : A)
    (hxy : (W.map φ).toAffine.Equation x y) (hx : ((W.map φ).preΨ p).eval x = 0) :
    (torsionQuadratic W p).eval₂ (PsiRoot.lift W p φ x hx) y = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hxy
  rw [torsionQuadratic, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_C,
    map_add, map_mul, map_add, map_add, map_add, map_mul, map_mul, map_pow, map_pow,
    PsiRoot.lift_ofBase, PsiRoot.lift_ofBase, PsiRoot.lift_ofBase, PsiRoot.lift_ofBase,
    PsiRoot.lift_ofBase, PsiRoot.lift_psiRootX]
  linear_combination hxy

namespace TorsionPointRing p2m_export "ModularCurve.LevelP.TorsionPointRing" "ofPsiRoot ofBase" end TorsionPointRing
namespace TorsionPointRing
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in

private def _root_.ModularCurve.LevelP.TorsionPointRing.lift (φ : B →+* A) (x y : A) (hxy : (W.map φ).toAffine.Equation x y)
    (hx : ((W.map φ).preΨ p).eval x = 0) : TorsionPointRing W p →+* A :=
  AdjoinRoot.lift (PsiRoot.lift W p φ x hx) y (torsionQuadratic_eval₂_eq_zero W p φ x y hxy hx)

end TorsionPointRing
p2m_export "ModularCurve.LevelP" "TorsionPointRing.lift"
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
theorem TorsionPointRing.lift_ofPsiRoot (φ : B →+* A) (x y : A) (hxy) (hx) (z : PsiRoot W p) :
    TorsionPointRing.lift W p φ x y hxy hx (TorsionPointRing.ofPsiRoot W p z) =
      PsiRoot.lift W p φ x hx z := by
  rw [TorsionPointRing.lift, TorsionPointRing.ofPsiRoot]
  erw [AdjoinRoot.lift_of]

namespace TorsionPointRing
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
@[scoped simp] private theorem _root_.ModularCurve.LevelP.TorsionPointRing.lift_ofBase (φ : B →+* A) (x y : A) (hxy) (hx) (b : B) :
    TorsionPointRing.lift W p φ x y hxy hx (TorsionPointRing.ofBase W p b) = φ b := by
  rw [TorsionPointRing.ofBase, RingHom.comp_apply, TorsionPointRing.lift_ofPsiRoot,
    PsiRoot.lift_ofBase]

end TorsionPointRing
p2m_export "ModularCurve.LevelP" "TorsionPointRing.lift_ofBase"
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing"
namespace TorsionPointRing
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
private theorem _root_.ModularCurve.LevelP.TorsionPointRing.lift_comp_ofBase (φ : B →+* A) (x y : A) (hxy) (hx) :
    (TorsionPointRing.lift W p φ x y hxy hx).comp (TorsionPointRing.ofBase W p) = φ :=
  RingHom.ext (TorsionPointRing.lift_ofBase W p φ x y hxy hx)

end TorsionPointRing
p2m_export "ModularCurve.LevelP" "TorsionPointRing.lift_comp_ofBase"
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
@[scoped simp] theorem TorsionPointRing.lift_torsionPtX (φ : B →+* A) (x y : A) (hxy) (hx) :
    TorsionPointRing.lift W p φ x y hxy hx (torsionPtX W p) = x := by
  rw [torsionPtX, TorsionPointRing.lift_ofPsiRoot, PsiRoot.lift_psiRootX]

p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing"
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
@[scoped simp] theorem TorsionPointRing.lift_torsionPtY (φ : B →+* A) (x y : A) (hxy) (hx) :
    TorsionPointRing.lift W p φ x y hxy hx (torsionPtY W p) = y := by
  rw [TorsionPointRing.lift, torsionPtY]
  erw [AdjoinRoot.lift_root]

p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing"
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
theorem TorsionPointRing.torsionPtCurve_map_lift (φ : B →+* A) (x y : A) (hxy) (hx) :
    (torsionPtCurve W p).map (TorsionPointRing.lift W p φ x y hxy hx) = W.map φ := by
  rw [torsionPtCurve, WeierstrassCurve.map_map, TorsionPointRing.lift_comp_ofBase]

section Basis

variable (φ : B →+* A) (D : LevelPData A) (hD : IsLevelPStructure (W.map φ) p D)
include hD

namespace BasisRing p2m_export "ModularCurve.LevelP.BasisRing" "ofTwoPoint ofBase" end BasisRing
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in

def BasisRing.liftOne : TorsionPointRing W p →+* A :=
  TorsionPointRing.lift W p φ D.xP D.yP hD.equation_P hD.preΨ_P

p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
theorem BasisRing.torsionPtCurve_map_liftOne :
    (torsionPtCurve W p).map (BasisRing.liftOne W p φ D hD) = W.map φ :=
  TorsionPointRing.torsionPtCurve_map_lift W p φ _ _ _ _

p2m_open_scoped "ModularCurve.LevelP.BasisRing" in

def BasisRing.liftTwo : TwoPointRing W p →+* A :=
  TorsionPointRing.lift (torsionPtCurve W p) p (BasisRing.liftOne W p φ D hD) D.xQ D.yQ
    (by rw [BasisRing.torsionPtCurve_map_liftOne]; exact hD.equation_Q)
    (by rw [BasisRing.torsionPtCurve_map_liftOne]; exact hD.preΨ_Q)

p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
theorem BasisRing.liftTwo_comp_ofBase :
    (BasisRing.liftTwo W p φ D hD).comp (TwoPointRing.ofBase W p) = φ := by
  rw [TwoPointRing.ofBase, ← RingHom.comp_assoc, BasisRing.liftTwo, TwoPointRing.ofOnePoint,
    TorsionPointRing.lift_comp_ofBase, BasisRing.liftOne, TorsionPointRing.lift_comp_ofBase]

p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
theorem BasisRing.twoPointCurve_map_liftTwo :
    (twoPointCurve W p).map (BasisRing.liftTwo W p φ D hD) = W.map φ := by
  rw [twoPointCurve, BasisRing.liftTwo, TorsionPointRing.torsionPtCurve_map_lift,
    BasisRing.torsionPtCurve_map_liftOne]

p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
@[scoped simp] theorem BasisRing.liftTwo_xP : BasisRing.liftTwo W p φ D hD (TwoPointRing.xP W p) = D.xP := by
  rw [TwoPointRing.xP, BasisRing.liftTwo, TwoPointRing.ofOnePoint, TorsionPointRing.lift_ofBase,
    BasisRing.liftOne, TorsionPointRing.lift_torsionPtX]

p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.BasisRing"
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
@[scoped simp] theorem BasisRing.liftTwo_yP : BasisRing.liftTwo W p φ D hD (TwoPointRing.yP W p) = D.yP := by
  rw [TwoPointRing.yP, BasisRing.liftTwo, TwoPointRing.ofOnePoint, TorsionPointRing.lift_ofBase,
    BasisRing.liftOne, TorsionPointRing.lift_torsionPtY]

p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.BasisRing"
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
@[scoped simp] theorem BasisRing.liftTwo_xQ : BasisRing.liftTwo W p φ D hD (TwoPointRing.xQ W p) = D.xQ := by
  rw [TwoPointRing.xQ, BasisRing.liftTwo, TorsionPointRing.lift_torsionPtX]

p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.BasisRing"
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
@[scoped simp] theorem BasisRing.liftTwo_yQ : BasisRing.liftTwo W p φ D hD (TwoPointRing.yQ W p) = D.yQ := by
  rw [TwoPointRing.yQ, BasisRing.liftTwo, TorsionPointRing.lift_torsionPtY]

p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.BasisRing"
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
theorem BasisRing.isUnit_liftTwo_indepDenom :
    IsUnit (BasisRing.liftTwo W p φ D hD (indepDenom W p)) := by
  rw [indepDenom, map_mul, ← indepElt_map, ← indepElt_map, BasisRing.twoPointCurve_map_liftTwo,
    BasisRing.liftTwo_xP, BasisRing.liftTwo_xQ]
  exact hD.isUnit_indepElt_PQ.mul hD.isUnit_indepElt_QP

namespace BasisRing
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in

private noncomputable def _root_.ModularCurve.LevelP.BasisRing.lift : BasisRing W p →+* A :=
  IsLocalization.Away.lift (indepDenom W p) (BasisRing.isUnit_liftTwo_indepDenom W p φ D hD)

end BasisRing
p2m_export "ModularCurve.LevelP" "BasisRing.lift"
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
theorem BasisRing.lift_ofTwoPoint (z : TwoPointRing W p) :
    BasisRing.lift W p φ D hD (BasisRing.ofTwoPoint W p z) = BasisRing.liftTwo W p φ D hD z := by
  rw [BasisRing.lift, BasisRing.ofTwoPoint]
  exact IsLocalization.Away.lift_eq _ _ _

p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
theorem BasisRing.lift_comp_ofTwoPoint :
    (BasisRing.lift W p φ D hD).comp (BasisRing.ofTwoPoint W p) = BasisRing.liftTwo W p φ D hD :=
  RingHom.ext (BasisRing.lift_ofTwoPoint W p φ D hD)

namespace BasisRing
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
@[scoped simp] private theorem _root_.ModularCurve.LevelP.BasisRing.lift_ofBase (b : B) :
    BasisRing.lift W p φ D hD (BasisRing.ofBase W p b) = φ b := by
  rw [BasisRing.ofBase, RingHom.comp_apply, BasisRing.lift_ofTwoPoint, ← RingHom.comp_apply,
    BasisRing.liftTwo_comp_ofBase]

end BasisRing
p2m_export "ModularCurve.LevelP" "BasisRing.lift_ofBase"
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.BasisRing"
namespace BasisRing
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
private theorem _root_.ModularCurve.LevelP.BasisRing.lift_comp_ofBase :
    (BasisRing.lift W p φ D hD).comp (BasisRing.ofBase W p) = φ :=
  RingHom.ext (BasisRing.lift_ofBase W p φ D hD)

end BasisRing
p2m_export "ModularCurve.LevelP" "BasisRing.lift_comp_ofBase"
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
theorem BasisRing.basisData_map_lift :
    (basisData W p).map (BasisRing.lift W p φ D hD) = D := by
  ext
  · show BasisRing.lift W p φ D hD (BasisRing.ofTwoPoint W p (TwoPointRing.xP W p)) = D.xP
    rw [BasisRing.lift_ofTwoPoint, BasisRing.liftTwo_xP]
  · show BasisRing.lift W p φ D hD (BasisRing.ofTwoPoint W p (TwoPointRing.yP W p)) = D.yP
    rw [BasisRing.lift_ofTwoPoint, BasisRing.liftTwo_yP]
  · show BasisRing.lift W p φ D hD (BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p)) = D.xQ
    rw [BasisRing.lift_ofTwoPoint, BasisRing.liftTwo_xQ]
  · show BasisRing.lift W p φ D hD (BasisRing.ofTwoPoint W p (TwoPointRing.yQ W p)) = D.yQ
    rw [BasisRing.lift_ofTwoPoint, BasisRing.liftTwo_yQ]

p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
theorem BasisRing.basisCurve_map_lift :
    (basisCurve W p).map (BasisRing.lift W p φ D hD) = W.map φ := by
  rw [basisCurve, WeierstrassCurve.map_map, BasisRing.lift_comp_ofBase]

end Basis
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.BasisRing"

namespace TorsionPointRing
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in

private theorem _root_.ModularCurve.LevelP.TorsionPointRing.exists_ringHom (φ : B →+* A) (x y : A)
    (hxy : (W.map φ).toAffine.Equation x y) (hx : ((W.map φ).preΨ p).eval x = 0) :
    ∃ ψ : TorsionPointRing W p →+* A, ψ.comp (TorsionPointRing.ofBase W p) = φ ∧
      ψ (torsionPtX W p) = x ∧ ψ (torsionPtY W p) = y :=
  ⟨_, TorsionPointRing.lift_comp_ofBase W p φ x y hxy hx,
    TorsionPointRing.lift_torsionPtX W p φ x y hxy hx,
    TorsionPointRing.lift_torsionPtY W p φ x y hxy hx⟩

end TorsionPointRing
p2m_export "ModularCurve.LevelP" "TorsionPointRing.exists_ringHom"
namespace BasisRing
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in

private theorem _root_.ModularCurve.LevelP.BasisRing.exists_ringHom (φ : B →+* A) (D : LevelPData A)
    (hD : IsLevelPStructure (W.map φ) p D) :
    ∃ ψ : BasisRing W p →+* A, ψ.comp (BasisRing.ofBase W p) = φ ∧ (basisData W p).map ψ = D :=
  ⟨_, BasisRing.lift_comp_ofBase W p φ D hD, BasisRing.basisData_map_lift W p φ D hD⟩

end BasisRing
p2m_export "ModularCurve.LevelP" "BasisRing.exists_ringHom"
end Lift
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.BasisRing"

end ModularCurve.LevelP
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.BasisRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP"
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.BasisRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.PsiRoot P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.TorsionPointRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP.BasisRing P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.ModularCurve.LevelP"

theorem solution
    {B : Type u} {A : Type v} [CommRing B] [CommRing A] (W : WeierstrassCurve B) (p : ℕ)
    (φ : B →+* A) (x y : A) (hxy : (W.map φ).toAffine.Equation x y)
    (hx : ((W.map φ).preΨ p).eval x = 0) :
    ∃ ψ : ModularCurve.LevelP.TorsionPointRing W p →+* A,
      ψ.comp (ModularCurve.LevelP.TorsionPointRing.ofBase W p) = φ ∧
        ψ (ModularCurve.LevelP.torsionPtX W p) = x ∧ ψ (ModularCurve.LevelP.torsionPtY W p) = y :=
  ModularCurve.LevelP.TorsionPointRing.exists_ringHom W p φ x y hxy hx

end S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq
end P2MW
export P2MW.S_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq (solution)
