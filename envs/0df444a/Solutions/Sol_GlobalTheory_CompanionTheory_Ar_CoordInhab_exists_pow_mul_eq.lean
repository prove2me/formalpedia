-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordInhab.exists_pow_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:24.802711+00:00
-- url     : https://prove2.me/submissions/e3cbb929-70a7-4bd5-9dc7-c46a2b1665cc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_genPt_specializes
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_mem_regAt_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory CptModel
open GlobalTheory.CompanionTheory.Ar.CoordInhab
variable {o K : Type} [CommRing o] [Field K] [Algebra o K]
variable [IsFractionRing o K]
namespace GlobalTheory.CompanionTheory.Ar.CoordInhab
theorem _root_.solution (t : o) (a : K)
    (h : ∀ p : Cpt (pt (algebraMap o K)), t ∉ p.1.asIdeal → a ∈ regAt (pt (algebraMap o K)) p) :
    ∃ (n : ℕ) (b : o), a * algebraMap o K t ^ n = algebraMap o K b := by
  let J : Ideal o :=
    { carrier := {s | ∃ b : o, a * algebraMap o K s = algebraMap o K b}
      add_mem' := by
        rintro u v ⟨b, hb⟩ ⟨b', hb'⟩
        exact ⟨b + b', by rw [map_add, map_add, mul_add, hb, hb']⟩
      zero_mem' := ⟨0, by rw [map_zero, mul_zero]⟩
      smul_mem' := by
        rintro r u ⟨b, hb⟩
        exact ⟨r * b, by rw [smul_eq_mul, map_mul, map_mul, ← hb]; ring⟩ }
  have hJ : ∀ s, s ∈ J ↔ ∃ b : o, a * algebraMap o K s = algebraMap o K b := fun s => Iff.rfl
  have ht : t ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra htP
    let q : Spec (CommRingCat.of o) := (⟨P, hP⟩ : PrimeSpectrum o)
    obtain ⟨a', s, hs, -, hs'⟩ := (mem_regAt_iff (algebraMap o K) ⟨q, genPt_specializes q⟩ a).1
      (h ⟨q, genPt_specializes q⟩ htP)
    exact hs (hJP ((hJ s).2 ⟨a', hs'⟩))
  obtain ⟨n, hn⟩ := ht
  obtain ⟨b, hb⟩ := (hJ _).1 hn
  exact ⟨n, b, by rw [← map_pow]; exact hb⟩
end GlobalTheory.CompanionTheory.Ar.CoordInhab
