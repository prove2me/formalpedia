-- Prove2me | solution 1 for GlobalTheory.CommSep.eq_aeval_of_commute_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:29:58.302235+00:00
-- url     : https://prove2.me/submissions/67313d8b-f106-4aa8-b851-11274e5587ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
import Theorems.Thm_GlobalTheory_CommSep_commute_aeval_of_commute
import Theorems.Thm_GlobalTheory_CommSep_aeval_mulVec_eq_krylov
import Theorems.Thm_GlobalTheory_ClassParam_exists_cyclic_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.CommSep
namespace GlobalTheory.CommSep
theorem _root_.solution {E : Type} [Field E] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) E) (hs : A.charpoly.Separable) (n : Matrix (Fin r) (Fin r) E)
    (hn : n * A = A * n) : ∃ q : E[X], n = aeval A q := by
  classical
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field A hs
  set K := GlobalTheory.ClassParam.krylov A v with hK
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.2 hv
  let c := K⁻¹ *ᵥ (n *ᵥ v)
  refine ⟨∑ j : Fin r, monomial (j : ℕ) (c j), ?_⟩
  set p := aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) with hp
  have hpv : p *ᵥ v = n *ᵥ v := by
    rw [hp, aeval_mulVec_eq_krylov, ← hK]
    simp only [c, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.one_mul]
  have hpA : Commute p A := (commute_aeval_of_commute (Commute.refl A) _).symm
  have hnA : Commute n A := hn
  have hcol : n * K = p * K := by
    ext i j
    have e1 : ∀ M : Matrix (Fin r) (Fin r) E, Commute M A →
        (M * K) i j = (A ^ (j : ℕ) *ᵥ (M *ᵥ v)) i := by
      intro M hM
      have : (M * K) i j = (M *ᵥ (A ^ (j : ℕ) *ᵥ v)) i := by
        simp [hK, GlobalTheory.ClassParam.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hM.pow_right _).eq]
    rw [e1 n hnA, e1 p hpA, hpv]
  have := congrArg (· * K⁻¹) hcol
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu] using this
end GlobalTheory.CommSep
