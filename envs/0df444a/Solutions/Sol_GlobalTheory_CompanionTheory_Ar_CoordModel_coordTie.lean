-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.coordTie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:52.276491+00:00
-- url     : https://prove2.me/submissions/eb741404-aaa4-4201-b584-ccf8ae4e567f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_mem_regAt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_spec_all
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_isCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_inv_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_algebraMap_mem_regAt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_inChart_iff

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
theorem _root_.solution (o : Type) [CommRing o] [Algebra o A] [Algebra o Ω] [IsScalarTower o A Ω]
    {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤)
    (hA : ∀ c, x c ≠ 0 → ∀ a : A, algebraMap A Ω a ∈
      Algebra.adjoin o (Set.range fun j => algebraMap A Ω (x j) / algebraMap A Ω (x c))) :
    CoordTie o (gen A Ω) (fun j => algebraMap A Ω (x j)) where
  gen := isCptGen A Ω
  cover p := by
    by_contra h
    push Not at h
    refine (pr A p.1).isPrime.ne_top (top_le_iff.1 (hx ▸ Ideal.span_le.2 ?_))
    rintro _ ⟨c, rfl⟩
    by_contra hc
    exact h c ((inChart_iff A Ω hx c p).2 hc)
  affine c _ := by
    refine ⟨_, IsAffineOpen.Spec_basicOpen (R := CommRingCat.of A) (x c), fun q => ?_⟩
    exact ⟨fun hq => ⟨spec_all A Ω q, (inChart_iff A Ω hx c _).2 hq⟩,
      fun ⟨h, hq⟩ => (inChart_iff A Ω hx c ⟨q, h⟩).1 hq⟩
  ring c hc a := by
    have hc' : x c ≠ 0 := fun h => hc (by simp [h])
    constructor
    · intro ha p hp
      induction ha using Algebra.adjoin_induction with
      | mem a h => obtain ⟨j, rfl⟩ := h; exact hp.2 j
      | algebraMap r => rw [IsScalarTower.algebraMap_apply o A Ω]; exact algebraMap_mem_regAt A Ω p _
      | add a b _ _ ha hb => exact Subring.add_mem _ ha hb
      | mul a b _ _ ha hb => exact Subring.mul_mem _ ha hb
    · intro h
      let I : Ideal A :=
        { carrier := {s | ∃ r, a * algebraMap A Ω s = algebraMap A Ω r}
          add_mem' := by
            rintro s t ⟨r, hr⟩ ⟨r', hr'⟩
            exact ⟨r + r', by rw [map_add, map_add, mul_add, hr, hr']⟩
          zero_mem' := ⟨0, by simp⟩
          smul_mem' := by
            rintro t s ⟨r, hr⟩
            exact ⟨t * r, by rw [smul_eq_mul, map_mul, map_mul, ← hr]; ring⟩ }
      have hrad : x c ∈ I.radical := by
        rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
        rintro J ⟨hIJ, hJ⟩
        by_contra hxc
        let q : Spec (CommRingCat.of A) := (⟨J, hJ⟩ : PrimeSpectrum A)
        obtain ⟨r, s, hs, e⟩ := (mem_regAt A Ω ⟨q, spec_all A Ω q⟩ a).1
          (h _ ((inChart_iff A Ω hx c _).2 hxc))
        exact hs (hIJ ⟨r, e⟩)
      obtain ⟨n, r, e⟩ := hrad
      have hi := inv_mem A Ω hx c (Algebra.adjoin o
        (Set.range fun j => algebraMap A Ω (x j) / algebraMap A Ω (x c))).toSubring (hA c hc')
        (fun j => Algebra.subset_adjoin ⟨j, rfl⟩)
      have : a = algebraMap A Ω r * (algebraMap A Ω (x c))⁻¹ ^ n := by
        rw [← e, map_pow, mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, mul_one]
      rw [this]
      exact Subalgebra.mul_mem _ (hA c hc' r) (Subalgebra.pow_mem _ hi n)
end GlobalTheory.CompanionTheory.Ar.CoordModel
