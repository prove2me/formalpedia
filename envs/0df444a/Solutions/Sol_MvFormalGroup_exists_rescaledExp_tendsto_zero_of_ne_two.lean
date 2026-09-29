-- Prove2me | solution 1 for MvFormalGroup.exists_rescaledExp_tendsto_zero_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a83c77ae-40ce-5bcb-b495-42c747a8835d

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Theorems.Thm_MvFormalGroup_prod_factorial_mul_coeff_mem_span_pow_of_subst_eq_X
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_rescaledExp_tendsto_zero_of_ne_two
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast"

set_option autoImplicit false

open MvPowerSeries

universe u

namespace UnipExpOdd

private theorem sub_one_mul_padicValNat_prod_factorial_le (p : ℕ) [Fact p.Prime] {d : ℕ}
    (m : Fin d →₀ ℕ) (hm : m ≠ 0) :
    (p - 1) * padicValNat p (m.prod fun _ k => k.factorial) + 1 ≤ m.degree := by
  classical

  have key : ∀ s : Finset (Fin d), (∀ j ∈ s, m j ≠ 0) →
      (p - 1) * padicValNat p (∏ j ∈ s, (m j).factorial) + s.card ≤ ∑ j ∈ s, m j := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | @insert j s hj ih =>
      intro hs
      rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.card_insert_of_notMem hj,
        padicValNat.mul (Nat.factorial_ne_zero _) (Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _),
        mul_add]
      have h1 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (hs j (Finset.mem_insert_self j s))
      have h2 := ih fun i hi => hs i (Finset.mem_insert_of_mem hi)
      omega
  have hsupp : m.support.Nonempty := Finsupp.support_nonempty_iff.2 hm
  have h := key m.support fun j hj => Finsupp.mem_support_iff.1 hj
  rw [Finsupp.degree_apply]
  change (p - 1) * padicValNat p (∏ j ∈ m.support, (m j).factorial) + 1 ≤ ∑ j ∈ m.support, m j
  have hcard : 1 ≤ m.support.card := Finset.card_pos.2 hsupp
  omega

private theorem isUnit_natCast_of_coprime {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {n : ℕ} (hn : Nat.Coprime p n) : IsUnit (n : 𝓞) := by
  have hpJ : (p : 𝓞) ∈ (⊥ : Ideal 𝓞).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {(p : 𝓞)}) (Ideal.mem_span_singleton_self _)
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 hn
  have h1 : IsUnit ((p : 𝓞) * (-(u : 𝓞)) + 1) := Ideal.mem_jacobson_bot.1 hpJ _
  have h2 : (p : 𝓞) * (-(u : 𝓞)) + 1 = (v : 𝓞) * (n : 𝓞) := by
    have := congrArg (Int.cast : ℤ → 𝓞) huv
    push_cast at this
    linear_combination -this
  rw [h2] at h1
  exact isUnit_of_mul_isUnit_right h1

private theorem mem_span_pow_of_pow_mul_mem {𝓞 : Type u} [CommRing 𝓞] {p : 𝓞} (hp : p ∈ nonZeroDivisors 𝓞)
    {a e : ℕ} (hae : a ≤ e) {x : 𝓞} (hx : p ^ a * x ∈ Ideal.span {p ^ e}) :
    x ∈ Ideal.span {p ^ (e - a)} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
  refine Ideal.mem_span_singleton'.2 ⟨y, ?_⟩
  have h : p ^ a * (y * p ^ (e - a)) = p ^ a * x := by
    rw [← hy, mul_left_comm, ← pow_add, Nat.add_sub_cancel' hae]
  exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem hp a)).1 h

end UnipExpOdd

open UnipExpOdd in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hp2 : p ≠ 2)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) :
    ∃ ψ : Fin d → MvPowerSeries (Fin d) 𝓞,

      (∀ i, (ψ i).constantCoeff = 0) ∧

      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧

      (∀ i, subst φ (ψ i) = X i) ∧

      (∀ i, subst ψ (φ i) = X i) := by
  classical
  obtain ⟨ψ, hψ0, hψφ, hφψ⟩ := MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one φ hφ0 hφ1
  refine ⟨ψ, hψ0, fun N i => ?_, hψφ, hφψ⟩

  refine (Finsupp.finite_of_degree_le (σ := Fin d) (2 * N)).subset fun m hm => ?_
  rw [Set.mem_setOf_eq]
  by_contra hdeg
  apply hm
  rw [not_le] at hdeg
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero] at hdeg
    exact Nat.not_lt_zero _ hdeg

  have hC2 := MvFormalGroup.prod_factorial_mul_coeff_mem_span_pow_of_subst_eq_X p hp F Fp hFp hFp0 φ hφ0 hφ1
    hφF ψ hψ0 hψφ hφψ i m hm0

  set A : ℕ := m.prod fun _ k => k.factorial with hA
  have hA0 : A ≠ 0 := by
    rw [hA, Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun j _ => Nat.factorial_ne_zero _
  set a : ℕ := padicValNat p A with ha
  have hsplit : A = p ^ a * (A / p ^ a) := by
    have := Nat.ordProj_mul_ordCompl_eq_self A p
    rw [Nat.factorization_def A (Fact.out : p.Prime)] at this
    exact this.symm
  have hcop : Nat.Coprime p (A / p ^ a) := by
    have := Nat.coprime_ordCompl (Fact.out : p.Prime) hA0
    rwa [Nat.factorization_def A (Fact.out : p.Prime)] at this

  have hleg := sub_one_mul_padicValNat_prod_factorial_le p m hm0
  rw [← hA, ← ha] at hleg
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    omega
  have h2a : 2 * a + 1 ≤ m.degree := by
    have : 2 * a ≤ (p - 1) * a := Nat.mul_le_mul_right a (by omega)
    omega
  have hale : a ≤ m.degree - 1 := by omega

  have hx : (p : 𝓞) ^ a * (((A / p ^ a : ℕ) : 𝓞) * MvPowerSeries.coeff m (ψ i)) ∈
      Ideal.span {(p : 𝓞) ^ (m.degree - 1)} := by
    have : ((A : ℕ) : 𝓞) = (p : 𝓞) ^ a * ((A / p ^ a : ℕ) : 𝓞) := by
      conv_lhs => rw [hsplit]
      push_cast
      ring
    rw [← mul_assoc, ← this]
    exact hC2
  have hy := mem_span_pow_of_pow_mul_mem hp hale hx
  obtain ⟨w, hw⟩ := (isUnit_natCast_of_coprime (𝓞 := 𝓞) p hcop).exists_left_inv
  have hcoeff : MvPowerSeries.coeff m (ψ i) ∈ Ideal.span {(p : 𝓞) ^ (m.degree - 1 - a)} := by
    have := Ideal.mul_mem_left _ w hy
    rwa [← mul_assoc, hw, one_mul] at this

  have hN : N ≤ m.degree - 1 - a := by omega
  have hle : Ideal.span {(p : 𝓞) ^ (m.degree - 1 - a)} ≤ Ideal.span {(p : 𝓞) ^ N} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_le_pow_right hN
  exact hle hcoeff

end S_MvFormalGroup_exists_rescaledExp_tendsto_zero_of_ne_two
end P2MW
export P2MW.S_MvFormalGroup_exists_rescaledExp_tendsto_zero_of_ne_two (solution)
