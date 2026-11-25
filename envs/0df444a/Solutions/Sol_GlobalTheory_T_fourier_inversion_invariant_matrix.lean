-- Prove2me | solution 1 for GlobalTheory.T.fourier_inversion_invariant_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:33.303639+00:00
-- url     : https://prove2.me/submissions/8ecfc433-1ec7-4c50-abb3-c0361628ee93

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionInvariantMatrix
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionInvariantMatrixStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_BigCell_fourier_prod_symm_preserving


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [MeasurableSpace A] (ν : Measure A) [SigmaFinite ν] (ψ : AddChar A ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (Bm : Matrix ι ι A), Bm.IsSymm → MeasurableEmbedding (fun x : ι → A => Bm.mulVec x) → (Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x) = (Measure.pi fun _ : ι => ν) → ∀ (t f : A → ℂ), (∀ y, f y = ∫ x, t x * ψ (x * y) ∂ν) → Integrable f ν → (∀ z, ∫ b, f b * ψ (b * z) ∂ν = t (-z)) → (∀ y, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x (Bm.mulVec y)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (Bm.mulVec y i)) ∧ Integrable (fun y : ι → A => ∏ i, f (Bm.mulVec y i)) (Measure.pi fun _ : ι => ν) ∧ ∀ z : ι → A, ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, t (-(z i)) := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving | exact GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving | (intros; apply GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving <;> assumption)
end _root_.GlobalTheory.T
