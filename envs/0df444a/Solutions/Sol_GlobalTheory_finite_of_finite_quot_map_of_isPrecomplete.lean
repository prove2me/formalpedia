-- Prove2me | solution 1 for GlobalTheory.finite_of_finite_quot_map_of_isPrecomplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:33.930958+00:00
-- url     : https://prove2.me/submissions/6e9f1680-8708-4177-99bc-cce0e5136b23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteOfFiniteQuotMapOfIsPrecomplete
import Theorems.Thm_GlobalTheory_nak_isPrecomplete_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O A : Type) [CommRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A]
      (J : Ideal O) [IsPrecomplete J O], J.map (algebraMap O A) ≠ ⊤ →
      Module.Finite O (A ⧸ J.map (algebraMap O A)) → Module.Finite O A := by
  intro O A _ _ _ _ _ J _ hJ hfin
  have hsm : ∀ n : ℕ, (J ^ n • (⊤ : Submodule O A)) =
      Submodule.restrictScalars O ((J.map (algebraMap O A)) ^ n) := by
    intro n
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
  have hH : IsHausdorff J A := by
    refine ⟨fun x hx => ?_⟩
    have : x ∈ ⨅ n : ℕ, (J.map (algebraMap O A)) ^ n := by
      rw [Submodule.mem_iInf]
      intro n
      have h1 := SModEq.sub_mem.1 (hx n)
      rw [sub_zero, hsm n] at h1
      exact h1
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ] at this
    exact this
  set I := J.map (algebraMap O A) with hI
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := A ⧸ I)
  choose s' hs' using fun i => Ideal.Quotient.mk_surjective (s i)
  have : IsPrecomplete J (Fin r → O) := nak_isPrecomplete_pi _
  have hsurj : Function.Surjective ((J • (⊤ : Submodule O A)).mkQ ∘ₗ
      Fintype.linearCombination O s') := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx : (Ideal.Quotient.mk I x) ∈ Submodule.span O (Set.range s) := by
      rw [hs]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    refine ⟨c, ?_⟩
    have hq : Ideal.Quotient.mk I (Fintype.linearCombination O s' c) = Ideal.Quotient.mk I x := by
      rw [Fintype.linearCombination_apply, map_sum, ← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, ← hs' i, Algebra.smul_def]
      rfl
    have hmem : Fintype.linearCombination O s' c - x ∈ I := by
      rw [← Ideal.Quotient.eq]; exact hq
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have h1 := hsm 1
    simp only [pow_one] at h1
    rw [h1]
    exact hmem
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)
end GlobalTheory
