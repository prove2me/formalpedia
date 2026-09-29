-- Prove2me | solution 1 for ModularCurve.pointEval_kroneckerRemainder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/414716d7-8bc0-5959-8c4e-939953cca1ac

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_pointEval_kroneckerRemainder
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (R : Polynomial (Polynomial ℤ)) (a b : k) :
    NodeLocalized.pointEval A.toSubring red a b
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
        (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)
      = ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C b)).eval a := by
  set ψ := NodeLocalized.pointEval A.toSubring red a b with hψ

  rw [Polynomial.hom_eval₂]
  have hX1 : ψ (MvPolynomial.X 1) = b := by
    rw [hψ, NodeLocalized.pointEval, MvPolynomial.eval₂Hom_X']; rfl
  have hcomp : ψ.comp (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
      = Polynomial.eval₂RingHom (Int.castRingHom k) a := by
    apply Polynomial.ringHom_ext
    · intro n
      rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.coe_comp, Function.comp_apply, hψ,
        NodeLocalized.pointEval, MvPolynomial.eval₂Hom_C, eq_intCast, eq_intCast, map_intCast]
    · rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hψ, NodeLocalized.pointEval, MvPolynomial.eval₂Hom_X']
      rfl
  rw [hX1, hcomp]

  rw [Polynomial.eval_map, ← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂, Polynomial.coe_evalRingHom,
    Polynomial.eval_C]
  congr 1
  apply Polynomial.ringHom_ext
  · intro n
    rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_evalRingHom,
      Polynomial.eval_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

end S_ModularCurve_pointEval_kroneckerRemainder
end P2MW
export P2MW.S_ModularCurve_pointEval_kroneckerRemainder (solution)
