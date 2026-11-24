-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.jG_mem_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:07.620289+00:00
-- url     : https://prove2.me/submissions/7fe34ee1-a1c6-4f48-8cdc-ddc1feb5340c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_i_tau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (A : Ad E R) (hi : Function.Injective A.i) (h : ∀ x, ∃ y, A.σ (A.i x) = A.i y) (m : GL ι R)
    (hm : m ∈ A.ratGL ι) : jG A.σ m ∈ A.ratGL (ι ⊕ ι) := by
  obtain ⟨y, rfl⟩ := hm
  refine ⟨jG (tau A hi h) y, Units.ext ?_⟩
  have hinv : ∀ a b, (((Matrix.GeneralLinearGroup.map A.i y)⁻¹ : GL ι R) : Matrix ι ι R) a b = A.i (((y⁻¹ : GL ι E) : Matrix ι ι E) a b) := fun a b => by
    rw [← map_inv]; rfl
  ext r c
  rcases r with r | r <;> rcases c with c | c
  · rfl
  · show A.i 0 = 0
    exact map_zero _
  · show A.i 0 = 0
    exact map_zero _
  · show A.i (tau A hi h (((y⁻¹ : GL ι E) : Matrix ι ι E) c r)) = A.σ ((((Matrix.GeneralLinearGroup.map A.i y)⁻¹ : GL ι R) : Matrix ι ι R) c r)
    rw [i_tau, hinv]
end GlobalTheory.CompanionTheory.RgEisLevi
