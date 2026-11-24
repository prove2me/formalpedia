-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Unitary.eq_one_of_upper_lowerUni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:17.561978+00:00
-- url     : https://prove2.me/submissions/30c28de5-a422-4529-a1d0-d5479b5945d1

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Unitary
variable {E ι : Type} [Ring E] [Fintype ι]
namespace GlobalTheory.CompanionTheory.Iwahori.Unitary
theorem _root_.solution {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P)
    (hw : Function.Injective wt) {c : E} (hu : IsUpper wt P c) (hl : IsLowerUni wt P c) :
    c = 1 := by
  have h : c = ∑ i, ∑ j, P i * c * P j := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hP.sum, mul_one, one_mul]
  rw [h, ← hP.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_eq_single i (fun j _ hj => ?_)
    (fun h => absurd (Finset.mem_univ i) h)).trans (hl.2 i)
  rcases lt_trichotomy (wt i) (wt j) with h | h | h
  · exact hl.1 i j h
  · exact absurd (hw h).symm hj
  · exact hu i j h
end GlobalTheory.CompanionTheory.Iwahori.Unitary
