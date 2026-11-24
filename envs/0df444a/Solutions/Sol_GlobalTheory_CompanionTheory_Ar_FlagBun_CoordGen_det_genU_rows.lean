-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.det_genU_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:54.977265+00:00
-- url     : https://prove2.me/submissions/1d04b513-e965-4ce3-aa53-6e0b81a93941

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_genU_of_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_CoordGen_genU_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
variable {Ω : Type} [Field Ω] {S : Type} {r : S → ℕ}
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
theorem _root_.solution (s : S) (k l : Fin (r s)) (hkl : k ≤ l) :
    ((genU Ω r s).submatrix
      (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then l else Fin.castLE k.2 i) (Fin.castLE k.2)).det
      = genU Ω r s l k := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    have h1 : ∀ i : Fin (k : ℕ), (genU Ω r s).submatrix
        (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then l else Fin.castLE k.2 i) (Fin.castLE k.2)
        i.castSucc i.castSucc = 1 := by
      intro i
      have : ((i.castSucc : Fin ((k : ℕ) + 1)) : ℕ) ≠ k := by simpa using i.2.ne
      simp only [Matrix.submatrix_apply, if_neg this]
      exact genU_self s _
    simp only [h1, Finset.prod_const_one, one_mul, Matrix.submatrix_apply, Fin.val_last, if_true]
    congr 1
  · intro i j hij
    have hij' : i < j := hij
    have hi : (i : ℕ) ≠ k := by
      have := j.2
      have : (i : ℕ) < j := hij'
      omega
    simp only [Matrix.submatrix_apply, if_neg hi]
    exact genU_of_lt s (show Fin.castLE k.2 i < Fin.castLE k.2 j from hij')
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
