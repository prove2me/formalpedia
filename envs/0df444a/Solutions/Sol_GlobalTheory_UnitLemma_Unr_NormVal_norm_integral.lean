-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.NormVal.norm_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:41:31.77999+00:00
-- url     : https://prove2.me/submissions/cbe26d35-db2f-48cb-b967-29e72b78647a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMul
import Theorems.Thm_GlobalTheory_T_exists_integral_basis_unramifiedInvolutionExt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.NormVal
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
namespace GlobalTheory.UnitLemma.Unr.NormVal
theorem _root_.solution (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hφ : IsUnrExt K K' d φ) (hd : 0 < d) (z : K'.O) :
    ∃ a : K.O, algebraMap K.O K.E a = @Algebra.norm K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E z) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt K K' d φ hφ hd
  have hwj : ∀ j, ∃ c : K'.O, algebraMap K'.O K'.E c = w j := by
    intro j
    refine (hw (w j)).2 fun k => ?_
    rw [w.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  have hM : ∀ i j, ∃ m : K.O, algebraMap K.O K.E m = Algebra.leftMulMatrix w (algebraMap K'.O K'.E z) i j := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    obtain ⟨c, hc⟩ := hwj j
    refine (hw _).1 ⟨z * c, ?_⟩ i
    rw [map_mul, hc]
  choose M hM using hM
  refine ⟨(Matrix.of M).det, ?_⟩
  rw [Algebra.norm_eq_matrix_det w, RingHom.map_det]
  congr 1
  ext i j
  simp [hM]
end GlobalTheory.UnitLemma.Unr.NormVal
