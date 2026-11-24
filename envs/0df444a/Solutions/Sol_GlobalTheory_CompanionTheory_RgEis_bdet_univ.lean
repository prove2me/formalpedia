-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.bdet_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:24.418799+00:00
-- url     : https://prove2.me/submissions/18d5c62f-52c0-4dd7-8b12-1959b7b1cc8c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_val

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
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (g : GL ι R) : bdet (Set.univ : Set ι) g = Matrix.GeneralLinearGroup.det g := by
  classical
  have hs : g ∈ stab R (Set.univ : Set ι) := fun r hr => absurd (Set.mem_univ r) hr
  apply Units.ext
  rw [bdet_val _ hs]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  convert Matrix.det_submatrix_equiv_self (Equiv.Set.univ ι) (g : Matrix ι ι R)
  all_goals (funext x; rfl)
end GlobalTheory.CompanionTheory.RgEis
