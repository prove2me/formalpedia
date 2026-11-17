-- Prove2me | solution 1 for N25.Endgame.cusp_constant_fibre_degree25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:53.660555+00:00
-- url     : https://prove2.me/submissions/2a3aa33e-2c5b-475a-aa60-eb627026f83c

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Theorems.Thm_N25_Endgame_rational_geometric_constant_extension25
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_N25_Endgame_rational_algebraic_constants25
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_N25_GammaH25_finiteIndex
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

namespace N25.Endgame

/-- The actual geometric constant-extension fibre of a rational closed place
is finite, with cardinality equal to its residue degree. -/
theorem _root_.solution (Q : QPlace) :
    {P : GPlace | P.toValuationSubring.comap emb25.toRingHom = Q.toValuationSubring}.Finite ∧
    Nat.card {P : GPlace |
      P.toValuationSubring.comap emb25.toRingHom = Q.toValuationSubring} = Q.deg := by
  classical
  let : Algebra ℚ FQ := DivisionRing.toRatAlgebra
  let : Algebra FQ FG := emb25.toRingHom.toAlgebra
  let : Module FQ FG := Algebra.toModule
  let : MulAction FQ FG := (inferInstance : Module FQ FG).toDistribMulAction.toMulAction
  have he := rational_geometric_constant_extension25
  let : IsScalarTower ℚ FQ FG := he.1
  let : Algebra.IsIntegral FQ FG := he.2.1
  let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  let : Γ25.FiniteIndex := N25.GammaH25_finiteIndex
  obtain ⟨x, hx, hfd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
      Γ25 (ModularCurve.translation_mem_GammaH 25 N25.H25)
  let : IsCurveOver ℚ FQ := isCurveOver_of_transcendental_of_perfectField hx hfd
  let : Algebra.EssFiniteType ℚ FQ := essFiniteType_of_transcendental_of_finiteDimensional hx hfd
  let : IsCurveOver Qbar FG :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
      Qbar 25 N25.H25).1
  let S := Place.fiberConstants Qbar FG Q
  have hiff (P : GPlace) : P ∈ S ↔
      P.toValuationSubring.comap emb25.toRingHom = Q.toValuationSubring := by
    rw [Place.mem_fiberConstants]
    constructor
    · intro h
      exact congrArg Place.toValuationSubring h
    · intro h
      exact Place.ext h
  have hset : {P : GPlace |
      P.toValuationSubring.comap emb25.toRingHom = Q.toValuationSubring} = (S : Set GPlace) := by
    ext P
    exact (hiff P).symm
  constructor
  · rw [hset]
    exact S.finite_toSet
  · have hsum := Place.sum_deg_fiberConstants_eq_deg_of_isCurveOver
      (K := ℚ) (K' := Qbar) (F := FQ) (F' := FG)
      he.2.2 rational_algebraic_constants25 Q
    have hones : (∑ P ∈ S, (P.deg : ℤ)) = (S.card : ℤ) := by
      calc
        _ = ∑ _P ∈ S, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro P _
          simp only [IsCurveOver.deg_eq_one_of_isAlgClosed P, Nat.cast_one]
        _ = _ := by simp
    have hsum' : (∑ P ∈ S, (P.deg : ℤ)) = (Q.deg : ℤ) := hsum
    have hcard : S.card = Q.deg := by
      exact_mod_cast hones.symm.trans hsum'
    let e : {P : GPlace |
        P.toValuationSubring.comap emb25.toRingHom = Q.toValuationSubring} ≃ ↥S :=
      { toFun := fun P => ⟨P.1, (hiff P.1).mpr P.2⟩
        invFun := fun P => ⟨P.1, (hiff P.1).mp P.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hcard

end N25.Endgame
