-- Prove2me | solution 1 for GlobalTheory.CombMinor.cMat_rowShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:00.750032+00:00
-- url     : https://prove2.me/submissions/f3e695d9-9ed7-42f1-998c-8493fa08e54a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdDetMemHaO
import Theorems.Thm_Formalism_L2_Pj_Crude_crSig_iff
import Theorems.Thm_Formalism_L2_Pj_Crude_crSig_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MvPolynomial Formalism.L2.Pj Formalism.L2.Pj.Crude
open GlobalTheory GlobalTheory.CombMinor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.CombMinor
theorem _root_.solution [Fintype Ty] (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k)
    (σ : Ty) (i i' : Fin (r σ)) (hii : i' < i) (t : k) :
    rowShift r n k σ i i' t (cMat τ s hs B).det = (cMat τ s hs B).det := by
  rw [AlgHom.map_det]
  by_cases hτ : τ = σ
  · subst hτ
    by_cases hin : i.val < s
    · have hin' : i'.val < s := lt_trans hii hin
      let i0 : Fin s := ⟨i.val, hin⟩
      let i1 : Fin s := ⟨i'.val, hin'⟩
      have hne : i0 ≠ i1 := by
        intro h
        have := congrArg Fin.val h
        simp only [i0, i1] at this
        exact (ne_of_gt hii) (Fin.ext this)
      have hmat : (rowShift r n k τ i i' t).mapMatrix (cMat τ s hs B) =
          (cMat τ s hs B).updateCol i0 (fun p => cMat τ s hs B p i0 +
            (C t : MvPolynomial (Letter Ty r n) k) • cMat τ s hs B p i1) := by
        refine Matrix.ext fun p q => ?_
        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
          algHom_C, algebraMap_eq, rowShift, aeval_X, Matrix.updateCol_apply, crSig_iff]
        by_cases hp : q = i0
        · subst hp
          have hc : Fin.castLE hs i0 = i := Fin.ext rfl
          have hc1 : Fin.castLE hs i1 = i' := Fin.ext rfl
          simp only [hc, hc1, if_true, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun b _ => by ring
        · rw [if_neg hp]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [if_neg]
          intro h
          apply hp
          apply Fin.ext
          have := congrArg Fin.val h
          simp only [Fin.val_castLE] at this
          exact this
      rw [hmat]
      exact Matrix.det_updateCol_add_smul_self _ hne (C t)
    · have hmat : (rowShift r n k τ i i' t).mapMatrix (cMat τ s hs B) = cMat τ s hs B := by
        refine Matrix.ext fun p q => ?_
        simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
          algHom_C, algebraMap_eq, rowShift, aeval_X, crSig_iff]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [if_neg]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castLE] at this
        omega
      rw [hmat]
  · have hmat : (rowShift r n k σ i i' t).mapMatrix (cMat τ s hs B) = cMat τ s hs B := by
      refine Matrix.ext fun p q => ?_
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, cMat, Matrix.of_apply, map_sum, map_mul,
        algHom_C, algebraMap_eq, rowShift, aeval_X]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [if_neg (crSig_ne hτ)]
    rw [hmat]
end GlobalTheory.CombMinor
