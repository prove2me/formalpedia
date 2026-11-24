-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.eq_blockOne_of_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:36:12.455517+00:00
-- url     : https://prove2.me/submissions/155c280d-56f7-46a8-bdea-c20bb87f8a42

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {K : Type} [CommRing K] {M : ℕ}
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) {s : K} (hs : IsUnit s)
    {h : Matrix (Fin (M + 1)) (Fin (M + 1)) K} (hm : cT σ h * blockOne s J * h = blockOne s J)
    (h00 : h 0 0 = 1) (hi0 : ∀ i : Fin M, h i.succ 0 = 0) :
    h = blockOne 1 (h.submatrix Fin.succ Fin.succ) := by
  have h1 : ∀ k, (cT σ h * blockOne s J) 0 k = blockOne s J 0 k := by
    intro k
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [cT, h00, hi0]
  have h2 : ∀ j : Fin M, h 0 j.succ = 0 := by
    intro j
    have e := congrFun (congrFun hm 0) j.succ
    rw [Matrix.mul_apply] at e
    simp only [h1] at e
    rw [Fin.sum_univ_succ] at e
    simp at e
    exact (hs.mul_right_eq_zero).1 e
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [h00, hi0, h2]
end GlobalTheory.CompanionTheory.SW.StabFirst
