-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.not_coordTie_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:13.403353+00:00
-- url     : https://prove2.me/submissions/30ccc1ff-5796-400b-879b-ca5eb62e8532

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_algebraMap_mem_regAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
variable [IsDomain A] [IsFractionRing A Ω]
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
theorem _root_.solution : ¬ CoordTie ℤ (gen ℚ ℚ) (fun _ : Unit => (1 : ℚ)) := by
  intro h
  have h2 := (h.ring () one_ne_zero (1 / 2)).2 fun p _ => algebraMap_mem_regAt ℚ ℚ p (1 / 2)
  have hle : Algebra.adjoin ℤ (Set.range fun _ : Unit => (1 : ℚ) / 1) ≤ ⊥ := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨_, rfl⟩
    simpa using Subalgebra.one_mem _
  obtain ⟨n, hn⟩ := Algebra.mem_bot.1 (hle h2)
  have : (2 * n : ℤ) = 1 := by
    have h' : (n : ℚ) = 1 / 2 := by simpa using hn
    have : ((2 * n : ℤ) : ℚ) = 1 := by push_cast; rw [h']; norm_num
    exact_mod_cast this
  omega
end GlobalTheory.CompanionTheory.Ar.CoordModel
