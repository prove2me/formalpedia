-- Prove2me | solution 1 for N25.LocalFive.exists_fully_invariant_surjective_nsmul_range
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:16.61728+00:00
-- url     : https://prove2.me/submissions/62fb9d01-21b0-46fb-bfc3-a2ddcd2ca7fa

import Mathlib
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

noncomputable section

namespace N25.LocalFive

private theorem exists_stable_range
    (F : Type*) [AddCommGroup F] [Finite F] (n : ℕ) :
    ∃ r : ℕ, (nsmulAddMonoidHom (α := F) (n ^ (r + 1))).range =
      (nsmulAddMonoidHom (α := F) (n ^ r)).range := by
  classical
  letI := Fintype.ofFinite F
  have hit (r : ℕ) (x : F) : (fun y : F => n • y)^[r] x = n ^ r • x := by
    induction r with
    | zero => simp
    | succ r ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  obtain ⟨r, _, hr⟩ := Finset.image_iterate_stabilises_lt_card
    (f := fun x : F => n • x) (s := Finset.univ)
    (fun _ _ => Finset.mem_univ _) (Finset.univ_nonempty)
  refine ⟨r, ?_⟩
  apply AddSubgroup.ext
  intro x
  have hx := Finset.ext_iff.mp (hr (r + 1) (Nat.le_succ r)) x
  simpa only [Finset.mem_image, Finset.mem_univ, true_and, hit,
    AddMonoidHom.mem_range, nsmulAddMonoidHom_apply] using hx

/-- A stabilized scalar image contains the divisible subgroup and is fully invariant. -/
theorem _root_.solution
    {M : Type*} [AddCommGroup M]
    (n : ℕ) (U : AddSubgroup M)
    (hfin : Finite (M ⧸ U))
    (hU : Function.Surjective (fun u : U => n • u)) :
    ∃ r : ℕ,
      let D := (nsmulAddMonoidHom (α := M) (n ^ r)).range
      U ≤ D ∧
        Finite (M ⧸ D) ∧
        Function.Surjective (fun x : D => n • x) ∧
        ∀ (f : M →+ M) (x : M), x ∈ D → f x ∈ D := by
  letI := hfin
  obtain ⟨r, hr⟩ := exists_stable_range (M ⧸ U) n
  let D := (nsmulAddMonoidHom (α := M) (n ^ r)).range
  have hp (s : ℕ) : Function.Surjective (fun u : U => n ^ s • u) := by
    induction s with
    | zero => intro u; exact ⟨u, by simp⟩
    | succ s ih =>
      intro u
      obtain ⟨v, hv⟩ := hU u
      obtain ⟨w, hw⟩ := ih v
      refine ⟨w, ?_⟩
      change n ^ (s + 1) • w = u
      rw [pow_succ', mul_smul]
      exact (congrArg (fun v : U => n • v) hw).trans hv
  have hUD : U ≤ D := by
    intro u hu
    obtain ⟨v, hv⟩ := hp r ⟨u, hu⟩
    exact ⟨v, congrArg Subtype.val hv⟩
  have hqfin : Finite (M ⧸ D) := by
    let q := QuotientAddGroup.map U D (AddMonoidHom.id M) hUD
    have hq : Function.Surjective q := by
      intro x
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective D x
      exact ⟨QuotientAddGroup.mk' U x, rfl⟩
    exact Finite.of_surjective q hq
  refine ⟨r, hUD, hqfin, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := x.property
    let q := QuotientAddGroup.mk' U
    have hx : q x ∈ (nsmulAddMonoidHom (α := M ⧸ U) (n ^ r)).range := by
      refine ⟨q a, ?_⟩
      change n ^ r • q a = q (x : M)
      rw [← map_nsmul]
      exact congrArg q ha
    rw [← hr] at hx
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective U b
    have herr : (x : M) - n ^ (r + 1) • b ∈ U := by
      apply QuotientAddGroup.eq_iff_sub_mem.mp
      change q (x : M) = q (n ^ (r + 1) • b)
      rw [map_nsmul]
      exact hb.symm
    obtain ⟨u, hu⟩ := hU ⟨(x : M) - n ^ (r + 1) • b, herr⟩
    have hz : n ^ r • b + (u : M) ∈ D := D.add_mem ⟨b, rfl⟩ (hUD u.property)
    refine ⟨⟨n ^ r • b + (u : M), hz⟩, Subtype.ext ?_⟩
    change n • (n ^ r • b + (u : M)) = (x : M)
    rw [nsmul_add, ← mul_smul, ← pow_succ',
      show n • (u : M) = (x : M) - n ^ (r + 1) • b from congrArg Subtype.val hu]
    abel
  · intro f x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨f y, (map_nsmul f (n ^ r) y).symm⟩

end N25.LocalFive
