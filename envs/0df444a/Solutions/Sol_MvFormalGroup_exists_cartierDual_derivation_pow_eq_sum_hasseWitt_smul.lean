-- Prove2me | solution 1 for MvFormalGroup.exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/08eb0fa6-d8ad-58a8-9b3f-4c15b6bd2c97

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_exists_cartierDual_apply_tmul_eq_and_map_mul_of_ker_eq_span_nthSeries
import Theorems.Thm_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul
import Theorems.Thm_MvFormalGroup_cartierDual_pow_apply_tmul_eq_algebraMap_constantCoeff_iterate
import Theorems.Thm_CartierDual_pow_char_apply_mul_of_apply_mul
import Theorems.Thm_MvFormalGroup_counit_apply_eq_zero_of_comul_eq_adicEval
import Theorems.Thm_MvFormalGroup_coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span
import Theorems.Thm_MvFormalGroup_coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace DerivFrob

private theorem eval_add {k : Type*} {B : Type*} [CommRing k] [CommRing B] [Bialgebra k B]
    (φ ψ : CartierDual k B) (a : B) : (φ + ψ) a = φ a + ψ a := by
  rw [← CartierDual.toDual_apply, map_add, LinearMap.add_apply, CartierDual.toDual_apply,
    CartierDual.toDual_apply]

private theorem eval_zero {k : Type*} {B : Type*} [CommRing k] [CommRing B] [Bialgebra k B]
    (a : B) : (0 : CartierDual k B) a = 0 := by
  rw [← CartierDual.toDual_apply, map_zero, LinearMap.zero_apply]

private theorem eval_smul {k : Type*} {B : Type*} [CommRing k] [CommRing B] [Bialgebra k B]
    (c : k) (φ : CartierDual k B) (a : B) : (c • φ) a = c * φ a := by
  rw [← CartierDual.toDual_apply, map_smul, LinearMap.smul_apply, CartierDual.toDual_apply, smul_eq_mul]

private theorem eval_sum {k : Type*} {B : Type*} [CommRing k] [CommRing B] [Bialgebra k B]
    {ι : Type*} (s : Finset ι) (φ : ι → CartierDual k B) (a : B) :
    (∑ t ∈ s, φ t) a = ∑ t ∈ s, φ t a := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, eval_zero]
  | insert x s hx IH => rw [Finset.sum_insert hx, Finset.sum_insert hx, eval_add, IH]

end DerivFrob

open DerivFrob in
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
    :
    ∃ D : Fin d → CartierDual (ZMod p) (ZMod p ⊗[𝓞] R),
      (∀ i j, D i ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = if i = j then 1 else 0) ∧
      (∀ i (a b : ZMod p ⊗[𝓞] R), D i (a * b) =
        D i a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * D i b) ∧
      (∀ i, D i ^ p = ∑ k, algebraMap 𝓞 (ZMod p) ((F.nthSeries p k).coeff (Finsupp.single i p)) • D k) := by
  classical

  haveI : IsAdicComplete (Ideal.span {(p : R)}) R :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p R
  haveI : IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R ⊗[𝓞] R)
  have hεR : ∀ j, Coalgebra.counit (R := 𝓞) (π (X j)) = 0 :=
    MvFormalGroup.counit_apply_eq_zero_of_comul_eq_adicEval p F R (fun j => π (X j)) hπX hπΔ
  have hε : ∀ j, Coalgebra.counit (R := ZMod p) ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = 0 := fun j => by
    rw [TensorProduct.counit_tmul, hεR, zero_smul]

  obtain ⟨D, hDi, hDii⟩ :=
    MvFormalGroup.exists_cartierDual_apply_tmul_eq_and_map_mul_of_ker_eq_span_nthSeries
      p hp hker F v hv R π hπ hπX hπeval hkerπ hπΔ
  refine ⟨D, hDi, hDii, fun i => ?_⟩

  let L : MvPowerSeries (Fin d) 𝓞 → MvPowerSeries (Fin d) 𝓞 := fun H =>
    fun a => coeff (a.sumElim (Finsupp.single i 1)) (subst F.toPowerSeries H)
  have hL : ∀ (H : MvPowerSeries (Fin d) 𝓞) (a : Fin d →₀ ℕ),
      (L H).coeff a = (subst F.toPowerSeries H).coeff (a.sumElim (Finsupp.single i 1)) := fun H a => rfl
  let G : (n : ℕ) → Fin d → MvPowerSeries (Fin n × Fin d) 𝓞 := fun n =>
    Nat.rec (motive := fun n => Fin d → MvPowerSeries (Fin n × Fin d) 𝓞) (fun _ => 0)
      (fun n Gn k => subst (Sum.elim
        (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (Gn j))
        (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
        (F.toPowerSeries k)) n
  have hGsucc : ∀ (n : ℕ) (k : Fin d), G (n + 1) k =
      subst (Sum.elim
        (fun j => subst (fun sj : Fin n × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)) (G n j))
        (fun j => (X (Fin.last n, j) : MvPowerSeries (Fin (n + 1) × Fin d) 𝓞)))
        (F.toPowerSeries k) := fun n k => rfl
  have hG1 : ∀ k, G 1 k = X ((0 : Fin 1), k) := by
    intro k
    refine (hGsucc 0 k).trans ?_
    have h0 : (fun j => subst (fun sj : Fin 0 × Fin d => (X (Fin.castSucc sj.1, sj.2) :
          MvPowerSeries (Fin (0 + 1) × Fin d) 𝓞)) (G 0 j)) = fun _ => 0 := by
      funext j
      show subst _ (0 : MvPowerSeries (Fin 0 × Fin d) 𝓞) = 0
      rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _), map_zero]
    rw [h0, MvFormalGroup.subst_elim_zero_left F (fun _ => constantCoeff_X _) k]
    rfl

  set δ : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R) := D i ^ p with hδdef
  set δ' : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R) :=
    ∑ k, algebraMap 𝓞 (ZMod p) ((F.nthSeries p k).coeff (Finsupp.single i p)) • D k with hδ'def
  have hδ : ∀ a b : ZMod p ⊗[𝓞] R, δ (a * b) =
      δ a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * δ b :=
    CartierDual.pow_char_apply_mul_of_apply_mul (ZMod p) p (ZMod p ⊗[𝓞] R) (D i) (hDii i)
  have hδ' : ∀ a b : ZMod p ⊗[𝓞] R, δ' (a * b) =
      δ' a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * δ' b := by
    intro a b
    simp only [hδ'def, DerivFrob.eval_sum, DerivFrob.eval_smul, hDii, mul_add, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;> ring

  have hval : ∀ j, δ ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = δ' ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) := by
    intro j

    have h1 := MvFormalGroup.cartierDual_pow_apply_tmul_eq_algebraMap_constantCoeff_iterate
      p F R π hπX hπeval hπΔ i (D i) (hDi i) (hDii i) L hL p (X j)
    have h2 := MvFormalGroup.coeff_subst_iterate_sum_single_eq_constantCoeff_invariantDerivation_iterate
      F G hG1 hGsucc i L hL p (Fact.out : p.Prime).one_lt.le (X j)
    have hGp0 : ∀ k, (G p k).constantCoeff = 0 := by
      have : ∀ n, 1 ≤ n → ∀ k, (G n k).constantCoeff = 0 := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => intro k; rw [hG1]; exact constantCoeff_X _
        | succ n hn IH =>
          intro k
          rw [hGsucc]
          refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_
            (F.constantCoeff_eq_zero k)
          all_goals
            rintro (j' | j')
            · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
                (fun _ => constantCoeff_X _) (IH j')
            · exact constantCoeff_X _
      exact this p (Fact.out : p.Prime).one_lt.le
    rw [subst_X (hasSubst_of_constantCoeff_zero hGp0)] at h2
    have h3 := MvFormalGroup.coeff_iterate_sum_single_sub_coeff_nthSeries_single_mem_span p F G hG1 hGsucc j i
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero] at h3
    rw [hδdef, h1, ← h2, h3]

    rw [hδ'def, DerivFrob.eval_sum]
    simp only [DerivFrob.eval_smul, hDi, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  exact MvFormalGroup.cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul p R π hπ hε δ δ' hδ hδ' hval

end S_MvFormalGroup_exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul
end P2MW
export P2MW.S_MvFormalGroup_exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul (solution)
