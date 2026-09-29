-- Prove2me | solution 1 for MvFormalGroup.isNilpotent_hasseWittMatrix_nthSeries_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/312e793c-9483-5d3d-b2e8-7afa7f5f8d6f

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul
import Theorems.Thm_MvFormalGroup_isCocomm_of_comul_eq_adicEval_toPowerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_isNilpotent_hasseWittMatrix_nthSeries_of_isLocalRing_cartierDual

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm nthSeries toPowerSeries adicEval exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul isCocomm_of_comul_eq_adicEval_toPowerSeries"
namespace HNilpC12
p2m_open "MvFormalGroup"

private theorem sum_smul_pow_prime_pow
    (p : ℕ) [hp : Fact p.Prime] {Dl : Type*} [CommRing Dl] [Algebra (ZMod p) Dl] [CharP Dl p]
    {d : ℕ} (D : Fin d → Dl) (A : Matrix (Fin d) (Fin d) (ZMod p))
    (hD : ∀ i, D i ^ p = ∑ k, A k i • D k) :
    ∀ (n : ℕ) (c : Fin d → ZMod p), (∑ i, c i • D i) ^ (p ^ n) = ∑ k, (A ^ n).mulVec c k • D k := by
  intro n
  induction n with
  | zero => intro c; simp [Matrix.one_mulVec]
  | succ n ih =>
    intro c
    rw [pow_succ, pow_mul, ih, ← frobenius_def (R := Dl) (p := p), map_sum]
    simp_rw [Algebra.smul_def, map_mul, frobenius_def]
    have hfix : ∀ a : ZMod p, algebraMap (ZMod p) Dl a ^ p = algebraMap (ZMod p) Dl a := fun a => by
      rw [← map_pow, ZMod.pow_card]
    simp_rw [hfix, hD, Finset.mul_sum, ← Algebra.smul_def, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, mul_comm]

end MvFormalGroup.HNilpC12

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (v : ℕ) (hv : 0 < v)
    (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R))) :
    IsNilpotent (Matrix.of fun i j : Fin d =>
      algebraMap 𝓞 (ZMod p) ((F.nthSeries p i).coeff (Finsupp.single j p))) := by
  classical
  have hpp : p.Prime := Fact.out

  obtain ⟨D, hD1, hD2, hD3⟩ :=
    MvFormalGroup.exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul p hp hker F v hv R π hπ hπX hπeval
      hkerπ hπΔ

  haveI : Coalgebra.IsCocomm 𝓞 R :=
    MvFormalGroup.isCocomm_of_comul_eq_adicEval_toPowerSeries p hp hker F R π hπ hπX hπeval hπΔ
  set A : Matrix (Fin d) (Fin d) (ZMod p) :=
    Matrix.of fun i j : Fin d => algebraMap 𝓞 (ZMod p) ((F.nthSeries p i).coeff (Finsupp.single j p)) with hA
  have hA' : ∀ k i, A k i = algebraMap 𝓞 (ZMod p) ((F.nthSeries p k).coeff (Finsupp.single i p)) :=
    fun _ _ => rfl

  haveI := hunip
  haveI : IsArtinianRing (CartierDual (ZMod p) (ZMod p ⊗[𝓞] R)) :=
    IsArtinianRing.of_finite (ZMod p) (CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
  obtain ⟨m, hm⟩ : IsNilpotent (IsLocalRing.maximalIdeal (CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))) := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h

  have hD0 : ∀ i, D i 1 = 0 := by
    intro i
    have h := hD2 i 1 1
    rw [mul_one, Bialgebra.counit_one, mul_one, one_mul] at h
    have h' : D i 1 + D i 1 = D i 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hmem : ∀ i, D i ∈ IsLocalRing.maximalIdeal (CartierDual (ZMod p) (ZMod p ⊗[𝓞] R)) := by
    intro i
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨E, hE⟩ := hu.exists_right_inv
    have h := congrArg (fun φ : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R) => φ 1) hE
    rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def, TensorProduct.dualDistrib_apply,
      CartierDual.toDual_apply, CartierDual.toDual_apply, hD0, zero_mul, CartierDual.one_apply,
      Bialgebra.counit_one] at h
    exact zero_ne_one h

  haveI : CharP (CartierDual (ZMod p) (ZMod p ⊗[𝓞] R)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))).injective p
  have hD3' : ∀ i, D i ^ p = ∑ k, A k i • D k := fun i => by simp_rw [hA']; exact hD3 i
  have hfrob := MvFormalGroup.HNilpC12.sum_smul_pow_prime_pow p D A hD3'
  have hzero : ∀ c : Fin d → ZMod p, ∑ k, (A ^ m).mulVec c k • D k = 0 := by
    intro c
    rw [← hfrob m c]
    have hx : ∑ i, c i • D i ∈ IsLocalRing.maximalIdeal (CartierDual (ZMod p) (ZMod p ⊗[𝓞] R)) :=
      Ideal.sum_mem _ fun i _ => by rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hmem i)
    have hxm : (∑ i, c i • D i) ^ m = 0 := by
      have h := Ideal.pow_mem_pow hx m
      rwa [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at h
    exact pow_eq_zero_of_le (Nat.lt_pow_self hpp.one_lt).le hxm

  have hvec : ∀ c : Fin d → ZMod p, (A ^ m).mulVec c = 0 := by
    intro c
    funext j
    have h := congrArg (fun φ : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R) =>
      CartierDual.toDual (ZMod p) (ZMod p ⊗[𝓞] R) φ ((1 : ZMod p) ⊗ₜ[𝓞] π (X j))) (hzero c)
    simp only [map_sum, map_smul, map_zero, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      CartierDual.toDual_apply, hD1, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    exact h
  refine ⟨m, ?_⟩
  ext i j
  have h := congrFun (hvec (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h
  exact h

end S_MvFormalGroup_isNilpotent_hasseWittMatrix_nthSeries_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_MvFormalGroup_isNilpotent_hasseWittMatrix_nthSeries_of_isLocalRing_cartierDual (solution)
