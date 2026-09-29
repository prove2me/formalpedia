-- Prove2me | solution 1 for HopfAlgebra.point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4dbc4211-f2c3-538b-8c63-7bbac0abb40d

import Definitions.Def_GaloisRep_Flat
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal

namespace F2BDEngine

section Core

variable {O : Type*} [CommRing O] {H : Type*} [CommRing H] [HopfAlgebra O H]
  [Coalgebra.IsCocomm O H]

omit [Coalgebra.IsCocomm O H] in

theorem convMul_mem {I J : Ideal O} {f g : WithConv (H →ₗ[O] O)}
    (hf : ∀ h : H, f h ∈ I) (hg : ∀ h : H, g h ∈ J) (h : H) : (f * g) h ∈ I * J := by
  rw [(Coalgebra.Repr.arbitrary O h).convMul_apply]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (hf _) (hg _)

omit [Coalgebra.IsCocomm O H] in

theorem convMul_mul_mem {I J : Ideal O} {f g k : WithConv (H →ₗ[O] O)}
    (hf : ∀ h : H, f h ∈ I) (hg : ∀ h : H, g h ∈ J) (h : H) : (f * g * k) h ∈ I * J := by
  have h1 := convMul_mem (g := k) (J := (⊤ : Ideal O)) (convMul_mem hf hg)
    (fun _ => Submodule.mem_top) h
  rwa [Ideal.mul_top] at h1

theorem pow_sub_one_apply_mem {I : Ideal O} {u : WithConv (H →ₗ[O] O)}
    (hu : ∀ h : H, (u - 1) h ∈ I) (q : ℕ) (h : H) : (u ^ q - 1) h ∈ I := by
  have hgeo : u ^ q - 1 = (u - 1) * ∑ i ∈ Finset.range q, u ^ i := by
    rw [mul_comm]; exact (geom_sum_mul u q).symm
  rw [hgeo]
  have h3 := convMul_mem (g := ∑ i ∈ Finset.range q, u ^ i) (J := (⊤ : Ideal O)) hu
    (fun _ => Submodule.mem_top) h
  rwa [Ideal.mul_top] at h3

theorem exists_pow_one_add {R : Type*} [CommRing R] (d : R) (q : ℕ) :
    ∃ c : R, (1 + d) ^ q = 1 + q • d + d * d * c := by
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨q • (1 : R) + c + c * d, ?_⟩
    rw [pow_succ, hc, succ_nsmul]
    ring

omit [Coalgebra.IsCocomm O H] in

theorem nsmul_apply' (q : ℕ) (f : WithConv (H →ₗ[O] O)) (h : H) :
    (q • f) h = q • f h := rfl

omit [Coalgebra.IsCocomm O H] in

theorem sub_apply' (f g : WithConv (H →ₗ[O] O)) (h : H) :
    (f - g) h = f h - g h := rfl

omit [Coalgebra.IsCocomm O H] in

theorem neg_apply' (f : WithConv (H →ₗ[O] O)) (h : H) :
    (-f) h = -(f h) := rfl

theorem conv_eq_one_of_pow_eq_one_of_isUnit
    [IsDomain O] [IsDiscreteValuationRing O]
    {w : WithConv (H →ₗ[O] O)} {m : ℕ} (hm : IsUnit (m : O))
    (hw1 : ∀ h : H, (w - 1) h ∈ IsLocalRing.maximalIdeal O)
    (hwm : w ^ m = 1) : w = 1 := by
  have key : ∀ j : ℕ, 1 ≤ j → ∀ h : H, (w - 1) h ∈ IsLocalRing.maximalIdeal O ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => simpa using hw1
    | succ j hj ih =>
      intro h
      obtain ⟨c, hc⟩ := exists_pow_one_add (w - 1) m
      rw [show (1 : WithConv (H →ₗ[O] O)) + (w - 1) = w by ring, hwm] at hc
      have h0 : m • (w - 1) = -((w - 1) * (w - 1) * c) := by
        linear_combination -hc
      have hle : IsLocalRing.maximalIdeal O ^ j * IsLocalRing.maximalIdeal O ^ j ≤
          IsLocalRing.maximalIdeal O ^ (j + 1) := by
        rw [← pow_add]
        exact Ideal.pow_le_pow_right (by omega)
      have hX := convMul_mul_mem (k := c) ih ih
      have happ := congrArg (fun z : WithConv (H →ₗ[O] O) => z h) h0
      simp only [nsmul_apply', neg_apply'] at happ
      rw [nsmul_eq_mul] at happ
      have hmem : (m : O) * (w - 1) h ∈ IsLocalRing.maximalIdeal O ^ (j + 1) := by
        rw [happ]
        exact neg_mem (hle (hX h))
      exact (Ideal.unit_mul_mem_iff_mem _ hm).mp hmem
  have hbot : (⨅ i : ℕ, IsLocalRing.maximalIdeal O ^ i) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal O) Ideal.IsPrime.ne_top'
  have hzero : ∀ h : H, (w - 1) h = 0 := by
    intro h
    have hmem : (w - 1) h ∈ ⨅ i : ℕ, IsLocalRing.maximalIdeal O ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      cases i with
      | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
      | succ j => exact key (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) h
    rw [hbot] at hmem
    exact (Submodule.mem_bot O).mp hmem
  apply WithConv.ext
  apply LinearMap.ext
  intro h
  have := hzero h
  rw [sub_apply'] at this
  exact sub_eq_zero.mp this

theorem core [IsDomain O] [IsDiscreteValuationRing O]
    (u : WithConv (H →ₗ[O] O)) (hu : ∀ h : H, (u - 1) h ∈ IsLocalRing.maximalIdeal O)
    (j m : ℕ) (hm : IsUnit (m : O)) (hw : (u ^ j) ^ m = 1) : u ^ j = 1 :=
  conv_eq_one_of_pow_eq_one_of_isUnit hm (fun h => pow_sub_one_apply_mem hu j h) hw

end Core

end F2BDEngine

namespace F2BDN

open WithConv

theorem isUnit_natCast_of_not_dvd (O : Type*) [CommRing O] [IsLocalRing O] (ℓ : ℕ)
    [Fact ℓ.Prime] (hunif : Irreducible (ℓ : O)) {m : ℕ} (hm : ¬ ℓ ∣ m) : IsUnit (m : O) := by
  have hcop : Nat.Coprime ℓ m := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm
  obtain ⟨a, b, hab⟩ := hcop.cast (R := O)
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hunif.not_isUnit
  · exact isUnit_of_mul_isUnit_right h

section transfer
variable {O H : Type*} [CommRing O] [CommRing H] [HopfAlgebra O H]

theorem sub_one_apply (x : WithConv (H →ₐ[O] O)) (h : H) :
    (toConv x.ofConv.toLinearMap - 1 : WithConv (H →ₗ[O] O)) h
      = x h - algebraMap O O (Coalgebra.counit h) := rfl

theorem pow_eq_one_of_conv (x : WithConv (H →ₐ[O] O)) (j : ℕ)
    (hw : (toConv x.ofConv.toLinearMap : WithConv (H →ₗ[O] O)) ^ j = 1) : x ^ j = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convPow, AlgHom.toLinearMap_convOne]
  exact hw

theorem conv_pow_eq_one (x : WithConv (H →ₐ[O] O)) (j : ℕ) (hx : x ^ j = 1) :
    (toConv x.ofConv.toLinearMap : WithConv (H →ₗ[O] O)) ^ j = 1 := by
  rw [← AlgHom.toLinearMap_convPow, hx, AlgHom.toLinearMap_convOne]

end transfer

end F2BDN

theorem solution
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hunif : Irreducible (ℓ : O))
    (H : Type*) [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Flat O H]
    [Coalgebra.IsCocomm O H]
    (x : WithConv (H →ₐ[O] O))
    (hx1 : ∀ h : H, x h - algebraMap O O (Coalgebra.counit h) ∈ IsLocalRing.maximalIdeal O)
    (n : ℕ) (hn : 0 < n) (hxn : x ^ n = 1) :
    x = 1 := by
  obtain ⟨k, m, hℓm, rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hn.ne' ℓ (Fact.out : ℓ.Prime).ne_one
  have hum : IsUnit (m : O) := F2BDN.isUnit_natCast_of_not_dvd O ℓ hunif hℓm
  have hk : x ^ ℓ ^ k = 1 := by
    apply F2BDN.pow_eq_one_of_conv
    refine F2BDEngine.core _ (fun h => ?_) (ℓ ^ k) m hum ?_
    · rw [F2BDN.sub_one_apply]; exact hx1 h
    · rw [← pow_mul]; exact F2BDN.conv_pow_eq_one x _ hxn
  exact HopfAlgebra.point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal O ℓ hℓ2
    hunif H x hx1 k hk

end S_HopfAlgebra_point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal
end P2MW
export P2MW.S_HopfAlgebra_point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal (solution)
