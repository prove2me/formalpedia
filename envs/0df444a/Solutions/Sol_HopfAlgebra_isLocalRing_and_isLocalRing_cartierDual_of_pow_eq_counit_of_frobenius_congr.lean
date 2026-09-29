-- Prove2me | solution 1 for HopfAlgebra.isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/48d163dd-10f5-5e7b-946d-ac8bf974789b

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr

set_option autoImplicit false

universe u v

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk"
namespace LocalLocalCriterion
p2m_open "HopfAlgebra"

open IsLocalRing

theorem isLocalRing_of_retraction {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (ev : S →+ R) (hev : ∀ r : R, ev (algebraMap R S r) = r)
    (hnil : ∀ b : S, ev b = 0 → ∃ n : ℕ, b ^ n ∈ (maximalIdeal R).map (algebraMap R S)) :
    IsLocalRing S := by

  have hmax : ∀ N : Ideal S, N.IsMaximal → (maximalIdeal R).map (algebraMap R S) ≤ N := by
    intro N hN
    rw [Ideal.map_le_iff_le_comap]
    haveI := hN
    have hc : (N.comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal N
    rw [IsLocalRing.eq_maximalIdeal hc]

  have hjac : ∀ b : S, (∃ n : ℕ, b ^ n ∈ (maximalIdeal R).map (algebraMap R S)) →
      b ∈ Ideal.jacobson (⊥ : Ideal S) := by
    rintro b ⟨n, hn⟩
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro N ⟨-, hN⟩
    exact hN.isPrime.mem_of_pow_mem n (hmax N hN hn)
  haveI hnt : Nontrivial S := by
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have h1 : ev 1 = (1 : R) := by rw [← map_one (algebraMap R S)]; exact hev 1
    rw [h, map_zero] at h1
    exact zero_ne_one h1

  have key : ∀ a : S, IsUnit (ev a) → IsUnit a := by
    intro a hu
    set b : S := a - algebraMap R S (ev a) with hb
    have hb0 : ev b = 0 := by rw [hb, map_sub, hev, sub_self]
    have hbj : b ∈ Ideal.jacobson (⊥ : Ideal S) := hjac b (hnil b hb0)
    have hU : IsUnit (algebraMap R S (ev a)) := hu.map (algebraMap R S)
    obtain ⟨Uinv, hUinv⟩ := hU.exists_left_inv
    have hmem : Uinv * b ∈ Ideal.jacobson (⊥ : Ideal S) := Ideal.mul_mem_left _ _ hbj
    have h1 : IsUnit (Uinv * b * 1 + 1) := Ideal.mem_jacobson_bot.mp hmem 1
    have hEq : algebraMap R S (ev a) * (Uinv * b * 1 + 1) = a := by
      rw [mul_one, mul_add, mul_one, ← mul_assoc, mul_comm _ Uinv, hUinv, one_mul, hb,
        sub_add_cancel]
    rw [← hEq]
    exact hU.mul h1
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (ev a) with h | h
  · exact Or.inl (key a h)
  · refine Or.inr (key (1 - a) ?_)
    have h1 : ev 1 = (1 : R) := by rw [← map_one (algebraMap R S)]; exact hev 1
    rwa [map_sub, h1]

section Main

variable {R : Type u} [CommRing R] (p : ℕ) {H : Type v} [CommRing H] [HopfAlgebra R H]

theorem mk_pow_apply_pow_eq (t : H →ₐc[R] H)
    (hF : ∀ a : H, (p : H) ∣ t a ^ p - a ^ (p ^ 2)) (k : ℕ) (a : H) :
    Ideal.Quotient.mk (Ideal.span {(p : H)}) ((t ^ k) a) ^ p =
      Ideal.Quotient.mk (Ideal.span {(p : H)}) a ^ (p ^ (k + 1)) := by
  have hQF : ∀ b : H, Ideal.Quotient.mk (Ideal.span {(p : H)}) (t b) ^ p =
      Ideal.Quotient.mk (Ideal.span {(p : H)}) b ^ (p ^ 2) := by
    intro b
    have h : Ideal.Quotient.mk (Ideal.span {(p : H)}) (t b ^ p) =
        Ideal.Quotient.mk (Ideal.span {(p : H)}) (b ^ (p ^ 2)) := by
      rw [Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton.mpr (hF b)
    rwa [map_pow, map_pow] at h
  induction k generalizing a with
  | zero => rw [pow_zero, BialgHom.one_apply, zero_add, pow_one]
  | succ k ih =>
    rw [pow_succ, BialgHom.mul_apply]
    calc Ideal.Quotient.mk (Ideal.span {(p : H)}) ((t ^ k) (t a)) ^ p
        = Ideal.Quotient.mk (Ideal.span {(p : H)}) (t a) ^ (p ^ (k + 1)) := ih (t a)
      _ = (Ideal.Quotient.mk (Ideal.span {(p : H)}) (t a) ^ p) ^ (p ^ k) := by
          rw [← pow_mul, ← pow_succ']
      _ = (Ideal.Quotient.mk (Ideal.span {(p : H)}) a ^ (p ^ 2)) ^ (p ^ k) := by rw [hQF a]
      _ = Ideal.Quotient.mk (Ideal.span {(p : H)}) a ^ (p ^ (k + 1 + 1)) := by
          rw [← pow_mul, ← pow_add]
          congr 2
          ring

end Main

end HopfAlgebra.LocalLocalCriterion

open HopfAlgebra.LocalLocalCriterion in
theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (H : Type*) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    [Coalgebra.IsCocomm R H]
    (t : H →ₐc[R] H)
    (ht : ∃ m : ℕ, ∀ a : H, (t ^ m) a = algebraMap R H (Coalgebra.counit a))
    (hF : ∀ a : H, (p : H) ∣ t a ^ p - a ^ (p ^ 2))
    (hV : ∀ φ : H →ₗ[R] R, (p : WithConv (H →ₗ[R] R)) ∣
        WithConv.toConv (φ ∘ₗ (t : H →ₗ[R] H)) ^ p - WithConv.toConv φ ^ (p ^ 2)) :
    IsLocalRing H ∧ IsLocalRing (CartierDual R H) := by
  obtain ⟨m, hm⟩ := ht
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  constructor
  ·
    refine isLocalRing_of_retraction (R := R) (S := H)
      (Coalgebra.counit (R := R) (A := H)).toAddMonoidHom
      (fun r => Bialgebra.counit_algebraMap r) ?_
    intro b hb
    change Coalgebra.counit (R := R) b = 0 at hb
    refine ⟨p ^ (m + 1), ?_⟩
    have hbI : b ^ (p ^ (m + 1)) ∈ Ideal.span {(p : H)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← mk_pow_apply_pow_eq p t hF m b, hm b, hb,
        map_zero, map_zero]
      exact zero_pow hp0
    refine Ideal.span_le.mpr ?_ hbI
    rintro _ ⟨rfl⟩
    rw [SetLike.mem_coe, ← map_natCast (algebraMap R H) p]
    exact Ideal.mem_map_of_mem _ hp
  ·

    let W := WithConv (H →ₗ[R] R)
    let Φ : CartierDual R H ≃+* W :=
      { toFun := fun φ => WithConv.toConv (CartierDual.toDual R H φ)
        invFun := fun w => CartierDual.ofDual R H w.ofConv
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun φ ψ => by
          show WithConv.toConv (CartierDual.toDual R H (φ * ψ)) =
            WithConv.toConv (CartierDual.toDual R H φ) * WithConv.toConv (CartierDual.toDual R H ψ)
          rw [CartierDual.mul_eq_convMul]
        map_add' := fun _ _ => rfl }

    let ev : CartierDual R H →+ R :=
      { toFun := fun φ => φ 1
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hev : ∀ r : R, ev (algebraMap R (CartierDual R H) r) = r := by
      intro r
      change algebraMap R (CartierDual R H) r 1 = r
      rw [CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul]

    have hQV : ∀ φ : H →ₗ[R] R,
        Ideal.Quotient.mk (Ideal.span {(p : W)}) (WithConv.toConv (φ ∘ₗ (t : H →ₗ[R] H))) ^ p =
          Ideal.Quotient.mk (Ideal.span {(p : W)}) (WithConv.toConv φ) ^ (p ^ 2) := by
      intro φ
      have h : Ideal.Quotient.mk (Ideal.span {(p : W)})
            (WithConv.toConv (φ ∘ₗ (t : H →ₗ[R] H)) ^ p) =
          Ideal.Quotient.mk (Ideal.span {(p : W)}) (WithConv.toConv φ ^ (p ^ 2)) := by
        rw [Ideal.Quotient.eq]
        exact Ideal.mem_span_singleton.mpr (hV φ)
      rwa [map_pow, map_pow] at h
    have hcomp : ∀ (k : ℕ) (φ : H →ₗ[R] R),
        φ ∘ₗ ((t ^ (k + 1) : H →ₐc[R] H) : H →ₗ[R] H) =
          (φ ∘ₗ ((t ^ k : H →ₐc[R] H) : H →ₗ[R] H)) ∘ₗ (t : H →ₗ[R] H) := by
      intro k φ
      refine LinearMap.ext fun a => ?_
      change φ ((t ^ (k + 1)) a) = φ ((t ^ k) (t a))
      rw [pow_succ, BialgHom.mul_apply]
    have hind : ∀ (k : ℕ) (φ : H →ₗ[R] R),
        Ideal.Quotient.mk (Ideal.span {(p : W)})
            (WithConv.toConv (φ ∘ₗ ((t ^ k : H →ₐc[R] H) : H →ₗ[R] H))) ^ p =
          Ideal.Quotient.mk (Ideal.span {(p : W)}) (WithConv.toConv φ) ^ (p ^ (k + 1)) := by
      intro k
      induction k with
      | zero =>
        intro φ
        have h0 : φ ∘ₗ ((t ^ 0 : H →ₐc[R] H) : H →ₗ[R] H) = φ := by
          refine LinearMap.ext fun a => ?_
          change φ ((t ^ 0) a) = φ a
          rw [pow_zero, BialgHom.one_apply]
        rw [h0, zero_add, pow_one]
      | succ k ih =>
        intro φ
        rw [hcomp k φ]
        calc Ideal.Quotient.mk (Ideal.span {(p : W)}) (WithConv.toConv
                ((φ ∘ₗ ((t ^ k : H →ₐc[R] H) : H →ₗ[R] H)) ∘ₗ (t : H →ₗ[R] H))) ^ p
            = Ideal.Quotient.mk (Ideal.span {(p : W)})
                (WithConv.toConv (φ ∘ₗ ((t ^ k : H →ₐc[R] H) : H →ₗ[R] H))) ^ (p ^ 2) := hQV _
          _ = (Ideal.Quotient.mk (Ideal.span {(p : W)})
                (WithConv.toConv (φ ∘ₗ ((t ^ k : H →ₐc[R] H) : H →ₗ[R] H))) ^ p) ^ p := by
              rw [← pow_mul, sq]
          _ = (Ideal.Quotient.mk (Ideal.span {(p : W)}) (WithConv.toConv φ) ^ (p ^ (k + 1))) ^ p := by
              rw [ih φ]
          _ = Ideal.Quotient.mk (Ideal.span {(p : W)}) (WithConv.toConv φ) ^ (p ^ (k + 1 + 1)) := by
              rw [← pow_mul, ← pow_succ]
    haveI : Algebra.IsIntegral R (CartierDual R H) := Algebra.IsIntegral.of_finite R _
    refine isLocalRing_of_retraction (R := R) (S := CartierDual R H) ev hev ?_
    intro ψ hψ
    change ψ 1 = 0 at hψ
    refine ⟨p ^ (m + 1), ?_⟩

    have hψm : (CartierDual.toDual R H ψ) ∘ₗ ((t ^ m : H →ₐc[R] H) : H →ₗ[R] H) = 0 := by
      refine LinearMap.ext fun a => ?_
      change CartierDual.toDual R H ψ ((t ^ m) a) = 0
      rw [hm a, Algebra.algebraMap_eq_smul_one, map_smul, CartierDual.toDual_apply, hψ, smul_zero]

    have hW : (Φ ψ) ^ (p ^ (m + 1)) ∈ Ideal.span {(p : W)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
      change Ideal.Quotient.mk _ (WithConv.toConv (CartierDual.toDual R H ψ)) ^ (p ^ (m + 1)) = 0
      rw [← hind m (CartierDual.toDual R H ψ), hψm, WithConv.toConv_zero, map_zero]
      exact zero_pow (M₀ := W ⧸ Ideal.span {(p : W)}) hp0

    have hD : ψ ^ (p ^ (m + 1)) ∈ Ideal.span {(p : CartierDual R H)} := by
      rw [Ideal.mem_span_singleton] at hW ⊢
      obtain ⟨c, hc⟩ := hW
      refine ⟨Φ.symm c, Φ.injective ?_⟩
      rw [map_pow, hc, map_mul, map_natCast, RingEquiv.apply_symm_apply]
    refine Ideal.span_le.mpr ?_ hD
    rintro _ ⟨rfl⟩
    rw [SetLike.mem_coe, ← map_natCast (algebraMap R (CartierDual R H)) p]
    exact Ideal.mem_map_of_mem _ hp

end S_HopfAlgebra_isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr
end P2MW
export P2MW.S_HopfAlgebra_isLocalRing_and_isLocalRing_cartierDual_of_pow_eq_counit_of_frobenius_congr (solution)
