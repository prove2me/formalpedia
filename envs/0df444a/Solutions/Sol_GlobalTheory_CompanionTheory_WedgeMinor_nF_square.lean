-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeMinor.nF_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:54:54.748096+00:00
-- url     : https://prove2.me/submissions/8c0fb465-4188-43c2-88ac-f586eb8cccbf

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_le_nF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeMinor
namespace GlobalTheory.CompanionTheory.WedgeMinor
theorem _root_.solution {K κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) : nF s = ‖s.det‖ := by
  refine le_antisymm (Real.iSup_le (fun t => ?_) (norm_nonneg _)) ?_
  · by_cases ht : Function.Injective t
    · have hb : Function.Bijective t := Finite.injective_iff_bijective.mp ht
      have h := Matrix.det_permute (Equiv.ofBijective t hb) s
      have h' : (s.submatrix t id).det = _ := h
      rw [h', norm_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective t hb)) with h1 | h1 <;>
        simp [h1]
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, t i = t j ∧ i ≠ j := by
        simpa [Function.Injective] using ht
      rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij])]
      simp
  · simpa using le_nF s id
end GlobalTheory.CompanionTheory.WedgeMinor
