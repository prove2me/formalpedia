-- Prove2me | solution 1 for GlobalTheory.CompactHowe.substF_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:57:01.023547+00:00
-- url     : https://prove2.me/submissions/c3031e24-c781-4964-a274-507751a72319

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionCompEqMul
import Theorems.Thm_GlobalTheory_CompactHowe_substF_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe
namespace GlobalTheory.CompactHowe
theorem _root_.solution {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    substF h g (substF h' g' P) = substF (h * h') (g * g') P := by
  have key : (substF h g).comp (substF h' g') = substF (h * h') (g * g') := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, substF_X, substF_X]
    simp only [map_sum, map_mul, substF_X, algHom_C, algebraMap_eq, Pi.mul_apply, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  exact congrArg (fun f => f P) key
end GlobalTheory.CompactHowe
