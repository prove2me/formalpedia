-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.nF_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:43.252708+00:00
-- url     : https://prove2.me/submissions/fe760095-9c54-45e9-8f1f-aa17ab44a615

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_exists_minor_eq_nF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution (hM : MulF) [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ K) : nF A ≠ 0 ↔ LinearIndependent K Aᵀ := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := exists_minor_eq_nF A h
    have hdet : ((A.submatrix s id)ᵀ).det ≠ 0 := by
      rw [det_transpose]
      intro h0
      rw [h0, norm_zero] at hs
      exact h hs.symm
    have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
    refine LinearIndependent.of_comp (LinearMap.funLeft K K s) ?_
    exact hli
  · intro h h0
    have hinj : Function.Injective A.mulVecLin := by
      have := (Matrix.vecMul_injective_iff (M := Aᵀ)).2 h
      intro x y hxy
      apply this
      simpa [vecMul_transpose] using hxy
    obtain ⟨g, hg⟩ := A.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
    have hL : LinearMap.toMatrix' g * A = 1 := by
      have : LinearMap.toMatrix' (g ∘ₗ A.mulVecLin) = 1 := by
        rw [hg, LinearMap.toMatrix'_id]
      rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
      exact this
    have h1 := (hM K ι κ κ A).1 (LinearMap.toMatrix' g)
    rw [hL, h0, mul_zero, (hM K κ κ κ 1).2.2 1, det_one, norm_one] at h1
    exact absurd h1 (by norm_num)
end GlobalTheory.CompanionTheory.Wedge
