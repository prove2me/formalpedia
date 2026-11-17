-- Prove2me | solution 1 for N25.cusp_contraction_order
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:56.402612+00:00
-- url     : https://prove2.me/submissions/ec0d5276-fb08-48b3-8344-ac62bc414282

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Theorems.Thm_N25_Endgame_rational_geometric_constant_extension25
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_N25_Endgame_rational_algebraic_constants25
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve

namespace N25

open Endgame

/-- Normalized orders are unchanged on contracting the actual algebraic constant extension. -/
theorem _root_.solution (Q : QPlace) (P : GPlace)
    (hQ : Q.toValuationSubring = P.toValuationSubring.comap emb25.toRingHom) (f : FQ) :
    P.ord (emb25 f) = Q.ord f := by
  let : Algebra FQ FG := emb25.toRingHom.toAlgebra
  obtain ⟨ht,hi,hgen⟩ := rational_geometric_constant_extension25
  have := ht
  have := hi
  let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  have hr := Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
    hgen rational_algebraic_constants25 P
  have hres : P.restrictConstants FQ = Q := Place.ext hQ.symm
  have ho := Place.ord_restrictConstants (K := ℚ) P f
  simp only [hr,Nat.cast_one,one_mul,hres] at ho
  exact ho

end N25
