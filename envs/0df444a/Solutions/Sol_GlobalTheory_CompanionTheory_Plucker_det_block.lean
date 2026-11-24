-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.det_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:17:16.82825+00:00
-- url     : https://prove2.me/submissions/c31436cc-73cf-412b-b107-810d420402cc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution (t₀ : Sub ι m) (s : Set ι) (hs : s = (t₀.1 : Set ι)) [Fintype s] [DecidableEq s]
    (M : Matrix ι ι R) : (M.submatrix (Subtype.val : s → ι) Subtype.val).det = cmp M t₀ t₀ := by
  subst hs
  let φ : m ≃ ((t₀.1 : Set ι) : Set ι) :=
    Equiv.ofBijective (fun i => ⟨en t₀ i, en_mem t₀ i⟩)
      ⟨fun a b h => en_injective t₀ (congrArg Subtype.val h), fun x => by
        have h1 : x.1 ∈ Set.range (en t₀) := by rw [range_en]; exact x.2
        obtain ⟨i, hi⟩ := h1
        exact ⟨i, Subtype.ext hi⟩⟩
  rw [← det_submatrix_equiv_self φ]
  rfl
end GlobalTheory.CompanionTheory.Plucker
