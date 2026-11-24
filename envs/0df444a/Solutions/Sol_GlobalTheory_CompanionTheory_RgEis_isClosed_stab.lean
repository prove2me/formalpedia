-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.isClosed_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:03:31.212455+00:00
-- url     : https://prove2.me/submissions/aa09719b-496a-4c4c-8521-bbdd2728040c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw

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
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution [T2Space R] (s : Set ι) : IsClosed (stab R s : Set (GL ι R)) := by
  have e : (stab R s : Set (GL ι R)) = ⋂ (r : ι) (_ : r ∉ s) (c : ι) (_ : c ∈ s),
      ({g : GL ι R | (g : Matrix ι ι R) r c = 0} ∩
        {g : GL ι R | ((g⁻¹ : GL ι R) : Matrix ι ι R) r c = 0}) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun c =>
    isClosed_iInter fun _ => IsClosed.inter ?_ ?_
  · exact isClosed_eq (Units.continuous_val.matrix_elem r c) continuous_const
  · exact isClosed_eq ((Units.continuous_val.comp continuous_inv).matrix_elem r c) continuous_const
end GlobalTheory.CompanionTheory.RgEis
