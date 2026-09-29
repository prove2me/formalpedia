-- Prove2me | solution 1 for ModularCurve.LevelRelabelling.relabel_smul_variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9f0cc0ed-3eb3-5ae1-ae6f-369999ed3301

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelRelabelling_relabel_smul_variableChange

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve ModularCurve.LevelRelabelling

namespace P2MmfTateAddVC

variable {T : Type} [Field T] [DecidableEq T]

noncomputable def ψ (W : WeierstrassCurve T) (C : VariableChange T) : W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := Point.vcInvFun C W.toAffine
  map_zero' := rfl
  map_add' := Point.vcInvFun_add C W.toAffine

theorem ψ_apply (W : WeierstrassCurve T) (C : VariableChange T) (P : W.toAffine.Point) :
    ψ W C P = Point.vcInvFun C W.toAffine P := rfl

theorem some_congr {V : WeierstrassCurve.Affine T} {x₁ y₁ x₂ y₂ : T} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

theorem toPoint_variableChange (W : WeierstrassCurve T) [W.IsElliptic] (C : VariableChange T) (x y : T)
    (h : W.toAffine.Equation x y) :
    toPoint (C • W) (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)) (((C.u⁻¹ : Tˣ) : T) ^ 3 * (y - C.s * (x - C.r) - C.t)) =
      ψ W C (toPoint W x y) := by
  have hn : W.toAffine.Nonsingular x y := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp h
  have hx' : ((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r) = vcXInv C x := rfl
  have hy' : ((C.u⁻¹ : Tˣ) : T) ^ 3 * (y - C.s * (x - C.r) - C.t) = vcYInv C x y := by
    unfold vcYInv; ring
  have hn' : (C • W).toAffine.Nonsingular (vcXInv C x) (vcYInv C x y) :=
    (nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr (by rwa [vcX_vcXInv, vcY_vcYInv])
  have hn'' : (C • W).toAffine.Nonsingular (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r))
      (((C.u⁻¹ : Tˣ) : T) ^ 3 * (y - C.s * (x - C.r) - C.t)) := by rw [hx', hy']; exact hn'
  rw [toPoint, dif_pos hn'', toPoint, dif_pos hn, ψ_apply]
  show _ = Point.some (vcXInv C x) (vcYInv C x y) _
  exact some_congr hx' hy'

theorem ofPoint_ψ (W : WeierstrassCurve T) (C : VariableChange T) (R : W.toAffine.Point) (hR : R ≠ 0) :
    (ofPoint (C • W) (ψ W C R)).1 = ((C.u⁻¹ : Tˣ) : T) ^ 2 * ((ofPoint W R).1 - C.r) ∧
    (ofPoint (C • W) (ψ W C R)).2 =
      ((C.u⁻¹ : Tˣ) : T) ^ 3 * ((ofPoint W R).2 - C.s * ((ofPoint W R).1 - C.r) - C.t) := by
  rcases R with _ | ⟨x, y, h⟩
  · exact absurd rfl hR
  · refine ⟨rfl, ?_⟩
    change vcYInv C x y = ((C.u⁻¹ : Tˣ) : T) ^ 3 * (y - C.s * (x - C.r) - C.t)
    unfold vcYInv; ring

end P2MmfTateAddVC

open P2MmfTateAddVC in
open scoped Classical in
theorem solution
    {T : Type} [Field T] (W : WeierstrassCurve T) [W.IsElliptic] (C : WeierstrassCurve.VariableChange T)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T)
    (hP : W.toAffine.Equation D.xP D.yP) (hQ : W.toAffine.Equation D.xQ D.yQ)
    (h₁ : g 0 0 • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + g 1 0 • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ ≠ 0)
    (h₂ : g 0 1 • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + g 1 1 • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ ≠ 0) :
    ModularCurve.LevelRelabelling.LevelPData.relabel (C • W) g (D.variableChange C) =
      (ModularCurve.LevelRelabelling.LevelPData.relabel W g D).variableChange C := by
  classical

  have hPt : toPoint (C • W) (D.variableChange C).xP (D.variableChange C).yP = ψ W C (toPoint W D.xP D.yP) :=
    toPoint_variableChange W C D.xP D.yP hP
  have hQt : toPoint (C • W) (D.variableChange C).xQ (D.variableChange C).yQ = ψ W C (toPoint W D.xQ D.yQ) :=
    toPoint_variableChange W C D.xQ D.yQ hQ

  have hc1 : g 0 0 • toPoint (C • W) (D.variableChange C).xP (D.variableChange C).yP +
      g 1 0 • toPoint (C • W) (D.variableChange C).xQ (D.variableChange C).yQ =
        ψ W C (g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ) := by
    rw [hPt, hQt, map_add, map_zsmul, map_zsmul]
  have hc2 : g 0 1 • toPoint (C • W) (D.variableChange C).xP (D.variableChange C).yP +
      g 1 1 • toPoint (C • W) (D.variableChange C).xQ (D.variableChange C).yQ =
        ψ W C (g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ) := by
    rw [hPt, hQt, map_add, map_zsmul, map_zsmul]
  obtain ⟨e1x, e1y⟩ := ofPoint_ψ W C _ h₁
  obtain ⟨e2x, e2y⟩ := ofPoint_ψ W C _ h₂
  unfold LevelPData.relabel
  simp only []
  ext
  · show (ofPoint (C • W) _).1 = _
    rw [hc1, e1x]; rfl
  · show (ofPoint (C • W) _).2 = _
    rw [hc1, e1y]; rfl
  · show (ofPoint (C • W) _).1 = _
    rw [hc2, e2x]; rfl
  · show (ofPoint (C • W) _).2 = _
    rw [hc2, e2y]; rfl

end S_ModularCurve_LevelRelabelling_relabel_smul_variableChange
end P2MW
export P2MW.S_ModularCurve_LevelRelabelling_relabel_smul_variableChange (solution)
