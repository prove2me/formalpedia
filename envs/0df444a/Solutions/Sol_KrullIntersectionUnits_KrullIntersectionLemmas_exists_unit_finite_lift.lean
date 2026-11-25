-- Prove2me | solution 1 for KrullIntersectionUnits.KrullIntersectionLemmas.exists_unit_finite_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:46.829885+00:00
-- url     : https://prove2.me/submissions/4ac5d231-8581-4dbd-8799-39b24cfcd0dc

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KrullIntersectionUnits KrullIntersectionUnits.KrullIntersectionLemmas
namespace KrullIntersectionUnits.KrullIntersectionLemmas
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hf : φ.Finite)
    (J : Ideal A) (hsurj : ∀ b : B, ∃ a : A, b - φ a ∈ Ideal.map φ J) :
    ∃ s : A, s - 1 ∈ J ∧ ∀ b : B, ∃ a : A, φ s * b = φ a := by
  letI : Algebra A B := φ.toAlgebra
  haveI : Module.Finite A B := hf
  let Nr : Submodule A B := LinearMap.range (Algebra.linearMap A B)
  have hfg : (⊤ : Submodule A (B ⧸ Nr)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule A (B ⧸ Nr)) ≤ J • (⊤ : Submodule A (B ⧸ Nr)) := by
    intro q _
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective Nr q
    obtain ⟨a, ha⟩ := hsurj b
    have hy : b - φ a ∈ J • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]
      exact ha
    have h0 : Nr.mkQ (φ a) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨a, rfl⟩
    have e : Nr.mkQ b = Nr.mkQ (b - φ a) := by
      rw [map_sub, h0, sub_zero]
    rw [e]
    have hm := Submodule.mem_map_of_mem (f := Nr.mkQ) hy
    rw [Submodule.map_smul''] at hm
    exact Submodule.smul_mono le_rfl le_top hm
  obtain ⟨s, hsJ, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J _ hfg hle
  refine ⟨s, hsJ, fun b => ?_⟩
  have h1 : Nr.mkQ (s • b) = 0 := by
    rw [map_smul]
    exact hs _ Submodule.mem_top
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨a, ha⟩ := h1
  exact ⟨a, ha.symm⟩
end KrullIntersectionUnits.KrullIntersectionLemmas
