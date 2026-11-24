-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.coordTie_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:33:09.596351+00:00
-- url     : https://prove2.me/submissions/73db9be7-444b-418f-9f3b-15d71355ed94

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_inv_mem_of_span_eq_top
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_algebraMap_mem_regAt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_genPt_specializes
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_inChart_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_exists_pow_mul_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_isCptGen_fractionRing


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
open CoordInhab
namespace GlobalTheory.CompanionTheory.Ar
theorem _root_.solution (o K : Type) [CommRing o] [IsDomain o] [Field K] [Algebra o K] [IsFractionRing o K]
    {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) :
    CoordTie o (Spec.map (CommRingCat.ofHom (algebraMap o K))) (fun j => algebraMap o K (x j)) := by
  refine ⟨isCptGen_fractionRing, ?_, ?_, ?_⟩
  · intro p
    by_contra hall
    push Not at hall
    have hsub : Ideal.span (Set.range x) ≤ p.1.asIdeal := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      by_contra hj
      exact hall j ((inChart_iff x hx j p).2 hj)
    rw [hx] at hsub
    exact p.1.isPrime.ne_top (top_le_iff.1 hsub)
  · intro c _
    refine ⟨(Spec (CommRingCat.of o)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of o)).inv (x c)),
      (isAffineOpen_top _).basicOpen _, fun q => ?_⟩
    have hmem : q ∈ (Spec (CommRingCat.of o)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of o)).inv (x c)) ↔ x c ∉ q.asIdeal := by
      rw [basicOpen_eq_of_affine]
      exact PrimeSpectrum.mem_basicOpen _ _
    rw [hmem]
    constructor
    · intro hq
      exact ⟨genPt_specializes q, (inChart_iff x hx c _).2 hq⟩
    · rintro ⟨h, hch⟩
      exact (inChart_iff x hx c _).1 hch
  · intro c hc a
    constructor
    · intro ha p hp
      obtain ⟨-, hrat⟩ := hp
      induction ha using Algebra.adjoin_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact hrat j
      | algebraMap r => exact algebraMap_mem_regAt p r
      | add y z _ _ hy hz => exact add_mem hy hz
      | mul y z _ _ hy hz => exact mul_mem hy hz
    · intro ha
      have hinv : (algebraMap o K (x c))⁻¹ ∈ (Algebra.adjoin o
          (Set.range fun j => algebraMap o K (x j) / algebraMap o K (x c))).toSubring :=
        inv_mem_of_span_eq_top x hx c _
          (fun r => Subalgebra.algebraMap_mem
            (Algebra.adjoin o (Set.range fun j => algebraMap o K (x j) / algebraMap o K (x c))) r)
          (fun j => Algebra.subset_adjoin ⟨j, rfl⟩)
      have hinv' : (algebraMap o K (x c))⁻¹ ∈ Algebra.adjoin o
          (Set.range fun j => algebraMap o K (x j) / algebraMap o K (x c)) := hinv
      obtain ⟨n, b, hb⟩ := exists_pow_mul_eq (x c) a (fun p hp => ha p ((inChart_iff x hx c p).2 hp))
      have hc' : algebraMap o K (x c) ≠ 0 := hc
      have hab : a = algebraMap o K b * ((algebraMap o K (x c))⁻¹) ^ n := by
        rw [← hb, mul_assoc, ← mul_pow, mul_inv_cancel₀ hc', one_pow, mul_one]
      rw [hab]
      exact mul_mem (Subalgebra.algebraMap_mem _ b) (pow_mem hinv' n)
end GlobalTheory.CompanionTheory.Ar
