-- Prove2me | solution 1 for GlobalTheory.AlgWtMul.evM_ratPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:44.604812+00:00
-- url     : https://prove2.me/submissions/2aad11d9-f75f-430f-a60e-5fbcfa6c7a11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
noncomputable section
open GlobalTheory GlobalTheory.AlgWtMul
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
namespace GlobalTheory.AlgWtMul
theorem _root_.solution (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (hA : Agrees a b P)
    (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b b (a.ρ γ) := by
  rw [hA γ γ₀ h]
  ext i j
  rfl
end GlobalTheory.AlgWtMul
