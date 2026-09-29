-- Prove2me | solution 1 for HopfAlgebra.exists_subalgebra_pow_char_pow_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6df8853c-a7da-52bc-9ea9-9d894968f775

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem solution
    {k : Type u} [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) (hfg : K.FG) :
    ∃ (r : ℕ) (K' : Subalgebra k H), K' ≤ K ∧ K'.FG ∧ IsReduced ↥K' ∧
      (K' : Set H) = {y : H | ∃ x ∈ K, y = x ^ p ^ r} ∧
      (∀ x ∈ K', Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) ∧
      (∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') := by
  classical
  have hp : p.Prime := Fact.out

  haveI : Algebra.FiniteType k ↥K := ⟨(Subalgebra.fg_top K).mpr hfg⟩
  haveI : IsNoetherianRing ↥K := Algebra.FiniteType.isNoetherianRing k ↥K
  obtain ⟨m, hm⟩ := IsNoetherianRing.isNilpotent_nilradical ↥K
  obtain ⟨r, hr⟩ : ∃ r : ℕ, m ≤ p ^ r := ⟨m, (Nat.lt_pow_self hp.one_lt).le⟩
  have hq0 : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero

  have hadd : ∀ x y : H, (x + y) ^ p ^ r = x ^ p ^ r + y ^ p ^ r := by
    rcases subsingleton_or_nontrivial H with hH | hH
    · intro x y; exact Subsingleton.elim _ _
    · haveI : CharP H p := charP_of_injective_algebraMap (algebraMap k H).injective p
      intro x y; exact add_pow_char_pow x y p r
  have hadd₂ : ∀ x y : H ⊗[k] H, (x + y) ^ p ^ r = x ^ p ^ r + y ^ p ^ r := by
    rcases subsingleton_or_nontrivial (H ⊗[k] H) with hH | hH
    · intro x y; exact Subsingleton.elim _ _
    · haveI : CharP (H ⊗[k] H) p := charP_of_injective_algebraMap (algebraMap k (H ⊗[k] H)).injective p
      intro x y; exact add_pow_char_pow x y p r

  have hroot' : ∀ (n : ℕ) (c : k), ∃ d : k, d ^ p ^ n = c := by
    intro n
    induction n with
    | zero => intro c; exact ⟨c, by rw [pow_zero, pow_one]⟩
    | succ n ih =>
        intro c
        obtain ⟨d, hd⟩ := ih c
        obtain ⟨e, he⟩ := (bijective_frobenius k p).2 d
        have he' : e ^ p = d := by rw [← frobenius_def]; exact he
        exact ⟨e, by rw [pow_succ', pow_mul, he', hd]⟩
  have hroot : ∀ c : k, ∃ d : k, d ^ p ^ r = c := hroot' r

  have hSpow : ∀ (x : H) (n : ℕ), HopfAlgebra.antipode k (x ^ n) = (HopfAlgebra.antipode k x) ^ n := by
    intro x n
    induction n with
    | zero => rw [pow_zero, pow_zero, HopfAlgebra.antipode_one]
    | succ n ih => rw [pow_succ, HopfAlgebra.antipode_mul, ih, ← pow_succ']

  let K' : Subalgebra k H :=
    { carrier := {y : H | ∃ x ∈ K, y = x ^ p ^ r}
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, K.mul_mem hx hy, (mul_pow x y _).symm⟩
      one_mem' := ⟨1, K.one_mem, (one_pow _).symm⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, K.add_mem hx hy, (hadd x y).symm⟩
      zero_mem' := ⟨0, K.zero_mem, (zero_pow hq0).symm⟩
      algebraMap_mem' := fun c => by
        obtain ⟨d, hd⟩ := hroot c
        exact ⟨algebraMap k H d, K.algebraMap_mem d, by rw [← map_pow, hd]⟩ }
  have memK' : ∀ y : H, y ∈ K' ↔ ∃ x ∈ K, y = x ^ p ^ r := fun _ => Iff.rfl
  have hpowK' : ∀ x ∈ K, x ^ p ^ r ∈ K' := fun x hx => ⟨x, hx, rfl⟩
  refine ⟨r, K', ?_, ?_, ?_, rfl, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact K.pow_mem hx _
  ·
    obtain ⟨t, ht⟩ := hfg
    refine ⟨t.image fun x => x ^ p ^ r, le_antisymm ?_ ?_⟩
    · apply Algebra.adjoin_le
      intro y hy
      rw [Finset.coe_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hpowK' x (ht ▸ Algebra.subset_adjoin hx)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← ht] at hx
      induction hx using Algebra.adjoin_induction with
      | mem y hy =>
          apply Algebra.subset_adjoin
          rw [Finset.coe_image]
          exact ⟨y, hy, rfl⟩
      | algebraMap c => rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _
      | add y z _ _ hy hz => rw [hadd]; exact Subalgebra.add_mem _ hy hz
      | mul y z _ _ hy hz => rw [mul_pow]; exact Subalgebra.mul_mem _ hy hz
  ·
    refine ⟨fun y hy => ?_⟩
    obtain ⟨n, hn⟩ := hy
    obtain ⟨x, hx, hxq⟩ := (memK' y).mp y.2
    have hyn : (y : H) ^ n = 0 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hxn : (⟨x, hx⟩ : ↥K) ∈ nilradical ↥K := by
      refine ⟨p ^ r * n, Subtype.ext ?_⟩
      show x ^ (p ^ r * n) = 0
      rw [pow_mul, ← hxq]
      exact hyn
    have hxm : x ^ m = 0 := by
      have h1 := Ideal.pow_mem_pow hxn m
      rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at h1
      simpa using congrArg Subtype.val h1
    apply Subtype.ext
    show (y : H) = 0
    rw [hxq, ← Nat.add_sub_cancel' hr, pow_add, hxm, zero_mul]
  ·
    rintro _ ⟨x, hx, rfl⟩
    have hpow : ∀ t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b},
        t ^ p ^ r ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b} := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem s hs =>
          obtain ⟨a, ha, b, hb, rfl⟩ := hs
          rw [Algebra.TensorProduct.tmul_pow]
          exact Submodule.subset_span ⟨_, hpowK' a ha, _, hpowK' b hb, rfl⟩
      | zero => rw [zero_pow hq0]; exact Submodule.zero_mem _
      | add s t _ _ hs ht => rw [hadd₂]; exact Submodule.add_mem _ hs ht
      | smul c s _ hs => rw [smul_pow]; exact Submodule.smul_mem _ _ hs
    have : Coalgebra.comul (R := k) (x ^ p ^ r) = (Coalgebra.comul (R := k) x) ^ p ^ r := by
      rw [← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]
    rw [this]
    exact hpow _ (hΔ x hx)
  ·
    rintro _ ⟨x, hx, rfl⟩
    rw [hSpow]
    exact hpowK' _ (hS x hx)

end S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced
end P2MW
export P2MW.S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced (solution)
