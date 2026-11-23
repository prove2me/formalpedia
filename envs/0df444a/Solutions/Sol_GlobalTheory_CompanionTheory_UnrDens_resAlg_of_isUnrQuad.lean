-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:01.125202+00:00
-- url     : https://prove2.me/submissions/8a230d7e-b9ec-4153-873f-3493c1f78f4b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by
  intro R _ σ ϖ q ε h
  have hτ : ∀ a : R, barσ σ ϖ h.fix_ϖ 1 (Ideal.Quotient.mk (lev ϖ 1) a) =
      Ideal.Quotient.mk (lev ϖ 1) (σ a) := fun a => Ideal.Quotient.lift_mk _ _ _
  obtain ⟨u, hu, hdec⟩ := h.basis
  refine ⟨?_, ?_, ?_, h.one_lt, h.card, h.eps⟩
  · intro e
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    rw [hτ a, hτ (σ a), h.inv]
  · intro e he hne
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
    rw [hτ] at he
    have hy0 : Ideal.Quotient.mk (lev ϖ 1) y = 0 := by
      have h1 : Ideal.Quotient.mk (lev ϖ 1) (y * (u - σ u)) = 0 := by
        have hxy : y * (u - σ u) = (x + y * u) - σ (x + y * u) := by
          rw [map_add, map_mul, hx, hy]
          ring
        rw [hxy, map_sub, he, sub_self]
      rw [map_mul] at h1
      exact (IsUnit.mul_left_eq_zero (hu.map (Ideal.Quotient.mk (lev ϖ 1)))).mp h1
    have hxe : Ideal.Quotient.mk (lev ϖ 1) (x + y * u) = Ideal.Quotient.mk (lev ϖ 1) x := by
      rw [map_add, map_mul, hy0, zero_mul, add_zero]
    rw [hxe] at hne ⊢
    exact (h.fixLocal x hx fun hmem => hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)).map _
  · refine ⟨Ideal.Quotient.mk (lev ϖ 1) u, ?_, ?_⟩
    · have hm := hu.map (Ideal.Quotient.mk (lev ϖ 1))
      rwa [map_sub, ← hτ] at hm
    · intro e
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
      obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
      refine ⟨Ideal.Quotient.mk (lev ϖ 1) x, Ideal.Quotient.mk (lev ϖ 1) y, ?_, ?_, ?_⟩
      · rw [hτ, hx]
      · rw [hτ, hy]
      · rw [map_add, map_mul]
end GlobalTheory.CompanionTheory.UnrDens
