-- Prove2me | solution 1 for N25.Endgame.rational_place_geometric_lift25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:57.171201+00:00
-- url     : https://prove2.me/submissions/8d922ab6-bb3e-4ba0-988b-34e765cd0af6

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_N25_Endgame_rational_geometric_constant_extension25
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_N25_Endgame_rational_algebraic_constants25
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

namespace N25.Endgame

/-- Every rational closed place lifts to the actual geometric field. -/
theorem _root_.solution (P : QPlace) :
    ∃ W : GPlace, W.toValuationSubring.comap emb25.toRingHom = P.toValuationSubring := by
  letI : Algebra FQ FG := emb25.toRingHom.toAlgebra
  letI : Module FQ FG := Algebra.toModule
  letI : MulAction FQ FG := (inferInstance : Module FQ FG).toDistribMulAction.toMulAction
  have he := rational_geometric_constant_extension25
  letI : IsScalarTower ℚ FQ FG := he.1
  letI : Algebra.IsIntegral FQ FG := he.2.1
  letI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  obtain ⟨W, hW⟩ := Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
    (K := ℚ) (K' := Qbar) (F := FQ) (F' := FG) (M := FQ)
    he.2.2 rational_algebraic_constants25 P
  refine ⟨W, ?_⟩
  have h := congrArg Place.toValuationSubring hW
  simp only [Place.restrict_toValuationSubring, Place.forgetConstants_toValuationSubring] at h
  have hmap : algebraMap FQ FG = emb25.toRingHom := rfl
  rw [hmap] at h
  exact h

end N25.Endgame
