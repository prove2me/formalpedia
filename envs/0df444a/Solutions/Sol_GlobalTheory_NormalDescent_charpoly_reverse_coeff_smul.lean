-- Prove2me | solution 1 for GlobalTheory.NormalDescent.charpoly_reverse_coeff_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:11.243007+00:00
-- url     : https://prove2.me/submissions/0eaae5f5-dd10-417a-9274-185fbc9f6d5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffInDomainMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Polynomial TensorProduct
open GlobalTheory GlobalTheory.NormalDescent
namespace GlobalTheory.NormalDescent
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (c : K) (k : ℕ) :
    (c • f).charpoly.reverse.coeff k = c ^ k * f.charpoly.reverse.coeff k := by
  classical
  let e := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix _ e, ← LinearMap.charpoly_toMatrix _ e, Matrix.reverse_charpoly,
    Matrix.reverse_charpoly, map_smul, mul_comm, ← comp_C_mul_X_coeff]
  generalize LinearMap.toMatrix e e f = M
  congr 1
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_compRingHom_apply, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j <;> simp [hij] <;> ring
end GlobalTheory.NormalDescent
