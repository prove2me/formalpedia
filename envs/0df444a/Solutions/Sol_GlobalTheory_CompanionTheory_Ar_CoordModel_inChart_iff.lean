-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.inChart_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:26.726308+00:00
-- url     : https://prove2.me/submissions/1115c9c7-31d8-4cdf-adf5-9d96114c04e2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_mem_regAt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_inv_mem
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
theorem _root_.solution {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤) (c : κ) (p : Cpt (gen A Ω)) :
    InChart (gen A Ω) (fun j => algebraMap A Ω (x j)) c p ↔ x c ∉ (pr A p.1).asIdeal := by
  constructor
  · rintro ⟨h0, h⟩ hc
    obtain ⟨r, s, hs, e⟩ := (mem_regAt A Ω p _).1 (inv_mem A Ω hx c _ (algebraMap_mem_regAt A Ω p) h)
    have : s = x c * r := by
      apply IsFractionRing.injective A Ω
      rw [map_mul, ← e]; field_simp
    exact hs (this ▸ Ideal.mul_mem_right _ _ hc)
  · intro hc
    have h0 : algebraMap A Ω (x c) ≠ 0 := by
      intro h
      have : x c = 0 := by simpa using h
      exact hc (this ▸ Ideal.zero_mem _)
    exact ⟨h0, fun j => (mem_regAt A Ω p _).2 ⟨x j, x c, hc, by field_simp⟩⟩
end GlobalTheory.CompanionTheory.Ar.CoordModel
