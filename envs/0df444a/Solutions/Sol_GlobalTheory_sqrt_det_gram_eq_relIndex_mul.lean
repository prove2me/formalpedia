-- Prove2me | solution 1 for GlobalTheory.sqrt_det_gram_eq_relIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:54.70639+00:00
-- url     : https://prove2.me/submissions/8f787c78-0316-4cf1-8c9a-c748d0626793

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Theorems.Thm_GlobalTheory_det_gram_real_sum_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {L' L : Submodule ℤ E} (h : L' ≤ L) (b' : Basis ι ℤ L')
    (b : Basis ι ℤ L) :
    √(gram ℝ fun i => (b' i : E)).det =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * √(gram ℝ fun i => (b i : E)).det := by
  let w : ι → L := fun j => ⟨b' j, h (b' j).2⟩
  have h1 : L'.toAddSubgroup.relIndex L.toAddSubgroup = (b.det w).natAbs :=
    AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b
  have h2 : (fun j => (b' j : E)) =
      fun j => ∑ i, ((b.toMatrix w).map (Int.cast : ℤ → ℝ)) i j • (b i : E) := by
    funext j
    have := congrArg (fun x : L => (x : E)) (b.sum_repr (w j))
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at this
    simp only [map_apply, Basis.toMatrix_apply, Int.cast_smul_eq_zsmul]
    exact this.symm
  rw [h2, det_gram_real_sum_smul, h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    ← Int.cast_det, Nat.cast_natAbs, Int.cast_abs, Basis.det_apply]
end GlobalTheory
