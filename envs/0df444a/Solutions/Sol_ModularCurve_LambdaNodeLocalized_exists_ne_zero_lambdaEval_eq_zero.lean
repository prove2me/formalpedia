-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_ne_zero_lambdaEval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e59ca7a6-0158-5d99-87b5-42bb738eb37e

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero.ModularCurve ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero.ModularCurve.LambdaNodeLocalized MvPolynomial"

namespace ModularCurve
p2m_export "ModularCurve" "lambdaModC lambdaNModC evalAtLambdaInt evalAtLambdaInt_X laurentMap laurentMap_qExpand laurentMap_laurentMap LambdaModularPolynomialData"
p2m_open "ModularCurve"
namespace LambdaNodeLocalized
p2m_export "ModularCurve.LambdaNodeLocalized" "lambdaEval"
p2m_open "ModularCurve.LambdaNodeLocalized"
namespace PsiT

variable {q : ℕ} [Fact q.Prime] {L : Type*} [Field L] [Algebra ℚ L] (A : Subring L)
  (data : LambdaModularPolynomialData q)

def psiT : MvPolynomial (Fin 2) A :=
  Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom _)) (MvPolynomial.X 0))
    (MvPolynomial.X 1) data.Ψ

theorem lambdaEval_psiT : lambdaEval q A (psiT A data) = 0 := by
  set mE := lambdaEval q A with hmE
  set θ : Polynomial ℤ →+* LaurentSeries L := Polynomial.eval₂RingHom (Int.castRingHom _) (lambdaModC L) with hθ
  have hgen0 : mE (MvPolynomial.X 0) = lambdaModC L := by
    rw [hmE, lambdaEval, MvPolynomial.eval₂Hom_X']; rfl
  have hgen1 : mE (MvPolynomial.X 1) = lambdaNModC L q := by
    rw [hmE, lambdaEval, MvPolynomial.eval₂Hom_X']; rfl
  have hLHS : mE (psiT A data) = data.Ψ.eval₂ θ (lambdaNModC L q) := by
    rw [psiT, Polynomial.hom_eval₂, hgen1]
    congr 1
    apply Polynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, hθ,
        map_intCast, eq_intCast]
    · rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hθ,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hgen0]
  set E : LaurentSeries ℚ →+* LaurentSeries L := laurentMap (algebraMap ℚ L) with hE
  have hZ : (algebraMap ℚ L).comp (Int.castRingHom ℚ) = Int.castRingHom L := RingHom.ext_int _ _
  have hE1 : E (lambdaNModC ℚ q) = lambdaNModC L q := by
    rw [hE, lambdaNModC, laurentMap_qExpand, lambdaNModC, lambdaModC, lambdaModC, laurentMap_laurentMap, hZ]
  have hEθ : E.comp ((laurentMap (Int.castRingHom ℚ)).comp evalAtLambdaInt) = θ := by
    apply Polynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        map_intCast, eq_intCast, evalAtLambdaInt]
    · rw [RingHom.coe_comp, Function.comp_apply, RingHom.coe_comp, Function.comp_apply, evalAtLambdaInt_X, hE,
        laurentMap_laurentMap, hZ, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, lambdaModC]
  have hΨ : data.Ψ.eval₂ θ (lambdaNModC L q) = 0 := by
    have h := congrArg E data.eval_eq_zero
    rw [map_zero, Polynomial.hom_eval₂, hEθ, hE1] at h
    exact h
  rw [hLHS, hΨ]

theorem psiT_ne_zero : psiT A data ≠ 0 := by
  intro h

  let τ : MvPolynomial (Fin 2) A →+* Polynomial A := eval₂Hom Polynomial.C ![0, Polynomial.X]
  have hτ : τ (psiT A data) = data.Ψ.map ((Polynomial.eval₂RingHom (Int.castRingHom A) 0)) := by
    rw [psiT, Polynomial.hom_eval₂]
    have hX : τ (MvPolynomial.X 1) = Polynomial.X := by
      show eval₂Hom Polynomial.C ![0, Polynomial.X] (MvPolynomial.X 1) = Polynomial.X
      rw [eval₂Hom_X']; rfl
    rw [hX]
    have hc : τ.comp (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom _)) (MvPolynomial.X 0))
        = Polynomial.C.comp (Polynomial.eval₂RingHom (Int.castRingHom A) 0) := by
      apply Polynomial.ringHom_ext
      · intro n
        simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
          map_intCast, eq_intCast]
      · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        show eval₂Hom Polynomial.C ![0, Polynomial.X] (MvPolynomial.X 0) = Polynomial.C 0
        rw [eval₂Hom_X', map_zero]; rfl
    rw [hc]; rfl
  have hm : (data.Ψ.map (Polynomial.eval₂RingHom (Int.castRingHom A) 0)).Monic := data.monic.map _
  have h0 : τ (psiT A data) = 0 := by rw [h, map_zero]
  rw [hτ] at h0
  exact hm.ne_zero h0

end PsiT
end LambdaNodeLocalized
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero.ModularCurve _root_.ModularCurve.LambdaNodeLocalized _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero.ModularCurve.LambdaNodeLocalized in
theorem solution
    {q : ℕ} [Fact q.Prime] (data : LambdaModularPolynomialData q)
    {L : Type*} [Field L] [Algebra ℚ L] (A : Subring L) :
    ∃ P : MvPolynomial (Fin 2) A, P ≠ 0 ∧ lambdaEval q A P = 0 :=
  ⟨PsiT.psiT A data, PsiT.psiT_ne_zero A data, PsiT.lambdaEval_psiT A data⟩

end

end S_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero (solution)
