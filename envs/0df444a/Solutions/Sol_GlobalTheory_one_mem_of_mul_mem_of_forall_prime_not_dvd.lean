-- Prove2me | solution 1 for GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:07.892618+00:00
-- url     : https://prove2.me/submissions/f9007bba-7d25-4a1b-a502-daec22caa40c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemOfMulMemOfForallPrimeNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (X : Type) [Finite X]
    (S : AddSubgroup (X → ℤ)) (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hp : ∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) : (1 : X → ℤ) ∈ S := by
  classical
  have h1 : ∀ x : X, ∃ f ∈ S, f x = 1 := by
    intro x
    obtain ⟨d, hd⟩ := Int.subgroup_cyclic (S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x))
    rw [← AddSubgroup.zmultiples_eq_closure] at hd
    have hd1 : d.natAbs = 1 := by
      rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro p pp hpd
      obtain ⟨f, hf, hnd⟩ := hp x p pp
      apply hnd
      have hmem : f x ∈ AddSubgroup.zmultiples d := by
        rw [← hd]
        exact ⟨f, hf, rfl⟩
      exact (Int.natCast_dvd.mpr hpd).trans (Int.mem_zmultiples_iff.mp hmem)
    have : (1 : ℤ) ∈ AddSubgroup.zmultiples d := by
      rw [Int.mem_zmultiples_iff]
      exact isUnit_iff_dvd_one.mp (Int.isUnit_iff_natAbs_eq.mpr hd1)
    rw [← hd] at this
    obtain ⟨f, hf, hfx⟩ := this
    exact ⟨f, hf, hfx⟩
  choose f hfS hf1 using h1
  have key : ∀ s : Finset X, 1 - ∏ x ∈ s, (1 - f x) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have e : 1 - (1 - f a) * ∏ x ∈ s, (1 - f x)
          = f a + (1 - ∏ x ∈ s, (1 - f x)) - f a * (1 - ∏ x ∈ s, (1 - f x)) := by ring
      rw [e]
      exact S.sub_mem (S.add_mem (hfS a) ih) (hmul _ (hfS a) _ ih)
  haveI := Fintype.ofFinite X
  have h0 : ∏ x : X, (1 - f x) = 0 := by
    funext y
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp [hf1])
  simpa [h0] using key Finset.univ
end GlobalTheory
