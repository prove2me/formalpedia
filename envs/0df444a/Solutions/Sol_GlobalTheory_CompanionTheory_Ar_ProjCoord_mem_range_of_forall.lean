-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.mem_range_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:34:22.837994+00:00
-- url     : https://prove2.me/submissions/dbc746d7-26f0-41d7-952a-d5313e313bbc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]
namespace GlobalTheory.CompanionTheory.Ar.ProjCoord
theorem _root_.solution (φ : A →+* Ω) (c : Ω)
    (h : ∀ q : PrimeSpectrum A, ∃ a s : A, s ∉ q.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a) :
    c ∈ φ.range := by
  let I : Ideal A :=
    { carrier := {s | c * φ s ∈ φ.range}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, mul_add] at *
        exact add_mem ha hb
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun a b hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        rw [mul_left_comm]
        exact mul_mem ⟨a, rfl⟩ hb }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨a, s, hs, -, e⟩ := h ⟨m, hm.isPrime⟩
    exact hs (hle (show c * φ s ∈ φ.range from ⟨a, e.symm⟩))
  have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
  have h2 : c * φ 1 ∈ φ.range := h1
  simpa using h2
end GlobalTheory.CompanionTheory.Ar.ProjCoord
