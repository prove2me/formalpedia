-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:08:26.498492+00:00
-- url     : https://prove2.me/submissions/eadaacd8-23fb-4059-9276-11210b0a7555

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_isUnit_det_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_mem_of_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.StableRangeOne
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.Adelic.StableRangeOne
theorem _root_.solution :
    ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : Matrix ι ι R → Prop),
        (∀ (i j : ι) (c : R), i ≠ j → p (Matrix.transvection i j c)) →
        (∀ D : ι → R, (∀ i, IsUnit (D i)) → p (Matrix.diagonal D)) →
        (∀ A B, IsUnit A.det → IsUnit B.det → p A → p B → p (A * B)) →
        ∀ A : Matrix ι ι R, IsUnit A.det → p A := by
  intro R _ hR ι _ _ p ht hd hm A hA
  have hmem : A ∈ elem R ι :=
    mem_of_fixed hR Finset.univ A hA (fun i j h => by simp at h)
  have key : ∀ B ∈ elem R ι, p B := by
    intro B hB
    induction hB using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i, j, c, h, rfl⟩ | ⟨D, hD, rfl⟩
      · exact ht i j c h
      · exact hd D hD
    | one =>
      have := hd (fun _ => 1) (fun _ => isUnit_one)
      simpa using this
    | mul x y hx hy px py =>
      exact hm x y (isUnit_det_of_mem hx) (isUnit_det_of_mem hy) px py
  exact key A hmem
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
