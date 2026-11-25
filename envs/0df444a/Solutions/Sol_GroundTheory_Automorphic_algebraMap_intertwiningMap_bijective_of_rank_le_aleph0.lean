-- Prove2me | solution 1 for GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_rank_le_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:40.915915+00:00
-- url     : https://prove2.me/submissions/46a93459-205a-4d63-97ff-9d6c17946119

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Theorems.Thm_GroundTheory_Automorphic_exists_ne_zero_of_isIrreducible
import Theorems.Thm_GroundTheory_Automorphic_injective_of_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_exists_eq_algebraMap_of_aeval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Polynomial Cardinal
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
theorem _root_.solution [ρ.IsIrreducible]
    (hV : Module.rank ℂ V ≤ ℵ₀) :
    Function.Bijective (algebraMap ℂ (Representation.IntertwiningMap ρ ρ)) := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  constructor
  · intro a b hab
    have h1 : a • v = b • v :=
      congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hab
    exact smul_left_injective ℂ hv h1
  · intro φ
    by_contra hne
    push Not at hne
    have hsub : ∀ c : ℂ, φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c ≠ 0 :=
      fun c h => hne c (sub_eq_zero.1 h).symm
    have htr : ∀ p : ℂ[X], p ≠ 0 → aeval φ p ≠ 0 := fun p hp h => by
      obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_aeval_eq_zero φ hp h
      exact hne c hc.symm
    have hsurj : ∀ c : ℂ,
        Function.Surjective (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c) :=
      fun c => ((Representation.IsIrreducible.bijective_or_eq_zero _).resolve_right (hsub c)).2
    choose w hw using fun c => hsurj c v
    have sum_apply : ∀ (s : Finset ℂ) (f : ℂ → Representation.IntertwiningMap ρ ρ) (x : V),
        (∑ j ∈ s, f j) x = ∑ j ∈ s, f j x := by
      intro s f x
      have h1 := congrFun (map_sum (Representation.IntertwiningMap.coeFnAddMonoidHom ρ ρ) f s) x
      rw [Finset.sum_apply] at h1
      exact h1
    have hli : LinearIndependent ℂ w := by
      rw [linearIndependent_iff']
      intro s a hsum i hi
      have key : ∀ j ∈ s, aeval φ (∏ k ∈ s, (X - C k)) (w j) =
          aeval φ (∏ k ∈ s.erase j, (X - C k)) v := by
        intro j hj
        rw [← Finset.prod_erase_mul _ _ hj, map_mul]
        change (aeval φ (∏ k ∈ s.erase j, (X - C k))) ((aeval φ (X - C j)) (w j)) = _
        rw [map_sub, aeval_X, aeval_C, hw j]
      set P : ℂ[X] := ∑ j ∈ s, a j • ∏ k ∈ s.erase j, (X - C k) with hPdef
      have hP : aeval φ P v = 0 := by
        have h0 := congrArg (aeval φ (∏ k ∈ s, (X - C k))) hsum
        rw [map_sum, map_zero] at h0
        rw [hPdef, map_sum, sum_apply]
        rw [← h0]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [map_smul, map_smul, key j hj]
        rfl
      have hP0 : P = 0 := by
        by_contra hP0
        exact hv (injective_of_ne_zero (htr P hP0) (hP.trans (map_zero _).symm))
      have h1 := congrArg (Polynomial.eval i) hP0
      rw [hPdef, eval_finsetSum, eval_zero, Finset.sum_eq_single i] at h1
      · rw [eval_smul, eval_prod, smul_eq_mul] at h1
        refine (mul_eq_zero.1 h1).resolve_right ?_
        refine Finset.prod_ne_zero_iff.2 fun k hk => ?_
        rw [eval_sub, eval_X, eval_C]
        exact sub_ne_zero.2 (Finset.ne_of_mem_erase hk).symm
      · intro j _ hji
        rw [eval_smul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨Ne.symm hji, hi⟩)
          (by rw [eval_sub, eval_X, eval_C, sub_self]), smul_zero]
      · intro h
        exact absurd hi h
    have h1 := hli.cardinal_lift_le_rank
    rw [Cardinal.mk_complex, Cardinal.lift_continuum] at h1
    have h2 : Cardinal.lift.{0} (Module.rank ℂ V) ≤ ℵ₀ := Cardinal.lift_le_aleph0.2 hV
    exact (not_le.2 Cardinal.aleph0_lt_continuum) (h1.trans h2)
end GroundTheory.Automorphic
