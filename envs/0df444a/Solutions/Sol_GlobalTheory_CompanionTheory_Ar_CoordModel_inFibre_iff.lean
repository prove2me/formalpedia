-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.inFibre_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:07.482196+00:00
-- url     : https://prove2.me/submissions/4858c982-f815-40a9-8c52-34395d245607

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_mem_regAt
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
theorem _root_.solution (p : ℕ) (q : Cpt (gen A Ω)) : InFibre (gen A Ω) p q ↔ (p : A) ∈ (pr A q.1).asIdeal := by
  have hp : (p : Ω) = algebraMap A Ω p := by simp
  unfold InFibre unitAt
  rw [hp, ← not_iff_not, not_not]
  constructor
  · rintro ⟨h0, -, h⟩ hc
    obtain ⟨r, s, hs, e⟩ := (mem_regAt A Ω q _).1 h
    have : s = p * r := by
      apply IsFractionRing.injective A Ω
      rw [map_mul, ← e]; field_simp
    exact hs (this ▸ Ideal.mul_mem_right _ _ hc)
  · intro hc
    have h0 : algebraMap A Ω p ≠ 0 := by
      intro h
      have : (p : A) = 0 := IsFractionRing.injective A Ω (by rw [h, map_zero])
      exact hc (this ▸ Ideal.zero_mem _)
    exact ⟨h0, algebraMap_mem_regAt A Ω q _, (mem_regAt A Ω q _).2 ⟨1, p, hc, by rw [map_one]; field_simp⟩⟩
end GlobalTheory.CompanionTheory.Ar.CoordModel
