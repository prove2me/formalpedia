-- Prove2me | solution 1 for HopfAlgebra.withConv_mul_signTwist_of_formula_of_linearEquiv_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6b309634-1777-5502-8880-0e880ade3073

import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_antipode_antipode
import Theorems.Thm_HopfAlgebra_map_antipode_comul_of_isCocomm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_withConv_mul_signTwist_of_formula_of_linearEquiv_padicInt

open scoped NNReal TensorProduct
open Coalgebra HopfAlgebra

open scoped _root_.TensorProduct _root_.Coalgebra.TensorProduct in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (s : AlgebraicClosure ℚ_[p]) (hs0 : s ≠ 0)
    (d₀ : ℤ_[p]) (hd₀s : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) d₀ = s ^ 2) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    (H' : Type) [CommRing H'] [HopfAlgebra ℤ_[p] H']
    (e : H' ≃ₗ[ℤ_[p]] H)
    (hecomul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a : H', (TensorProduct.map (e : H' →ₗ[ℤ_[p]] H) (e : H' →ₗ[ℤ_[p]] H))
                  (Coalgebra.comul a)
            = Coalgebra.comul (e a)
              + (Ring.inverse d₀ - 1) •
                  (TensorProduct.map Pm Pm) (Coalgebra.comul (e a)))
    (β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
         WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
    (hβ : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ (φ' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])) (h : H),
        (β φ') h = φ' (e.symm (h - Pm h)) + s⁻¹ * φ' (e.symm (Pm h))) :
    ∀ f' g', β (f' * g') = β f' * β g' := by
  intro f' g'
  set Pm : H →ₗ[ℤ_[p]] H :=
    Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p]) with hPm_def
  simp only at hβ hecomul
  refine WithConv.ext (AlgHom.ext fun h => ?_)
  show (β (f' * g')) h = (β f' * β g') h

  have hp2' : ¬ p ∣ 2 :=
    fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  have h2u : IsUnit (2 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    have hstep : ‖(2:ℤ_[p])‖ = ‖((2:ℕ):ℚ_[p])‖ := by
      show ‖((2:ℤ_[p]):ℚ_[p])‖ = ‖((2:ℕ):ℚ_[p])‖; congr 1
    rw [hstep]
    have h2ne : ((2:ℕ):ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr two_ne_zero
    first
    | { rw [Padic.norm_eq_zpow_neg_valuation h2ne, Padic.valuation_natCast,
          padicValNat.eq_zero_of_not_dvd hp2']; simp }
    | { rw [Padic.norm_natCast]; simp [padicValNat.eq_zero_of_not_dvd hp2'] }
  have h21 : Ring.inverse (2:ℤ_[p]) * 2 = 1 := Ring.inverse_mul_cancel _ h2u

  have hS2 : ∀ x : H, antipode ℤ_[p] (antipode ℤ_[p] x) = x :=
    fun x => HopfAlgebra.antipode_antipode x
  have hPmS : ∀ x : H, Pm (antipode ℤ_[p] x) = - Pm x := by
    intro x
    simp only [hPm_def, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, hS2]
    rw [← smul_neg, neg_sub]
  have hSeq : ∀ x : H, antipode ℤ_[p] x = (x - Pm x) - Pm x := by
    intro x
    have h2Pm : (2:ℤ_[p]) • Pm x = x - antipode ℤ_[p] x := by
      rw [hPm_def, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
        smul_smul, mul_comm, h21, one_smul]
    rw [sub_sub, ← two_smul ℤ_[p] (Pm x), h2Pm, sub_sub_cancel]

  set rep := ℛ ℤ_[p] h

  have hΔSh : (comul (antipode ℤ_[p] h) : H ⊗[ℤ_[p]] H)
      = ∑ i ∈ rep.index, (antipode ℤ_[p] (rep.left i)) ⊗ₜ (antipode ℤ_[p] (rep.right i)) := by
    rw [← HopfAlgebra.map_antipode_comul_of_isCocomm hcocomm h, ← rep.eq, map_sum]
    simp only [TensorProduct.map_tmul]

  let ψf : H →ₗ[ℤ_[p]] AlgebraicClosure ℚ_[p] :=
    (WithConv.ofConv f').toLinearMap ∘ₗ e.symm.toLinearMap
  let ψg : H →ₗ[ℤ_[p]] AlgebraicClosure ℚ_[p] :=
    (WithConv.ofConv g').toLinearMap ∘ₗ e.symm.toLinearMap
  let F : H ⊗[ℤ_[p]] H →ₗ[ℤ_[p]] AlgebraicClosure ℚ_[p] :=
    (LinearMap.mul' ℤ_[p] (AlgebraicClosure ℚ_[p])) ∘ₗ (TensorProduct.map ψf ψg)
  have hF_tmul : ∀ x y : H, F (x ⊗ₜ y) = f' (e.symm x) * g' (e.symm y) := by
    intro x y
    simp only [F, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
      ψf, ψg, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap]

  have hfg'_raw : ∀ a' : H', (f' * g') a'
      = F ((TensorProduct.map (e : H' →ₗ[ℤ_[p]] H) (e : H' →ₗ[ℤ_[p]] H)) (comul a')) := by
    intro a'
    have hconv : (f' * g') a'
        = (Algebra.TensorProduct.lmul' ℤ_[p])
            ((Algebra.TensorProduct.map (WithConv.ofConv f') (WithConv.ofConv g'))
              (Bialgebra.comulAlgHom ℤ_[p] H' a')) := by
      simp only [AlgHom.convMul_def, AlgHom.coe_comp, Function.comp_apply,
        WithConv.ofConv_toConv]
    rw [hconv, Bialgebra.comulAlgHom_apply]
    induction (Coalgebra.comul (R := ℤ_[p]) a') using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
        simp only [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          Algebra.TensorProduct.lmul'_apply_tmul, hF_tmul, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply]
    | add u v hu hv => simp only [map_add, hu, hv]

  have hfg'_x : ∀ x : H, (f' * g') (e.symm x)
      = F (comul x) + (Ring.inverse d₀ - 1) • F ((TensorProduct.map Pm Pm) (comul x)) := by
    intro x
    rw [hfg'_raw, hecomul (e.symm x), LinearEquiv.apply_symm_apply, map_add, map_smul]

  set A : AlgebraicClosure ℚ_[p] :=
    ∑ i ∈ rep.index, f' (e.symm (rep.left i - Pm (rep.left i)))
        * g' (e.symm (rep.right i - Pm (rep.right i))) with hA
  set B : AlgebraicClosure ℚ_[p] :=
    ∑ i ∈ rep.index, f' (e.symm (rep.left i - Pm (rep.left i)))
        * g' (e.symm (Pm (rep.right i))) with hB
  set C : AlgebraicClosure ℚ_[p] :=
    ∑ i ∈ rep.index, f' (e.symm (Pm (rep.left i)))
        * g' (e.symm (rep.right i - Pm (rep.right i))) with hC
  set D : AlgebraicClosure ℚ_[p] :=
    ∑ i ∈ rep.index, f' (e.symm (Pm (rep.left i)))
        * g' (e.symm (Pm (rep.right i))) with hD

  have hψf_split : ∀ x : H,
      (f' (e.symm x) : AlgebraicClosure ℚ_[p])
        = f' (e.symm (x - Pm x)) + f' (e.symm (Pm x)) := by
    intro x; rw [map_sub, map_sub]; ring
  have hψg_split : ∀ x : H,
      (g' (e.symm x) : AlgebraicClosure ℚ_[p])
        = g' (e.symm (x - Pm x)) + g' (e.symm (Pm x)) := by
    intro x; rw [map_sub, map_sub]; ring
  have hψf_S : ∀ x : H,
      (f' (e.symm (antipode ℤ_[p] x)) : AlgebraicClosure ℚ_[p])
        = f' (e.symm (x - Pm x)) - f' (e.symm (Pm x)) := by
    intro x; rw [hSeq, map_sub, map_sub]
  have hψg_S : ∀ x : H,
      (g' (e.symm (antipode ℤ_[p] x)) : AlgebraicClosure ℚ_[p])
        = g' (e.symm (x - Pm x)) - g' (e.symm (Pm x)) := by
    intro x; rw [hSeq, map_sub, map_sub]

  have hF_Δh : F (comul h) = A + B + C + D := by
    rw [hA, hB, hC, hD, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, show (comul h : H ⊗[ℤ_[p]] H) = _ from rep.eq.symm, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hF_tmul, hψf_split (rep.left i), hψg_split (rep.right i)]; ring

  have hF_ΔSh : F (comul (antipode ℤ_[p] h)) = A - B - C + D := by
    rw [hΔSh, map_sum, hA, hB, hC, hD, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hF_tmul, hψf_S (rep.left i), hψg_S (rep.right i)]; ring

  have hF_PmPm_Δh : F ((TensorProduct.map Pm Pm) (comul h)) = D := by
    rw [show (comul h : H ⊗[ℤ_[p]] H) = _ from rep.eq.symm, map_sum, map_sum]
    simp only [TensorProduct.map_tmul, hF_tmul]
    exact hD.symm

  have hF_PmPm_ΔSh : F ((TensorProduct.map Pm Pm) (comul (antipode ℤ_[p] h))) = D := by
    rw [hΔSh, map_sum, map_sum]
    simp only [TensorProduct.map_tmul, hPmS, hF_tmul, map_neg, neg_mul, mul_neg, neg_neg]
    exact hD.symm

  have hcomul_Pm : (comul (Pm h) : H ⊗[ℤ_[p]] H)
      = Ring.inverse (2:ℤ_[p]) • (comul h - comul (antipode ℤ_[p] h)) := by
    rw [hPm_def, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_smul, map_sub]
  have hcomul_Pp : (comul (h - Pm h) : H ⊗[ℤ_[p]] H) = comul h - comul (Pm h) := by
    rw [map_sub]

  have h2L : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (Ring.inverse (2:ℤ_[p])) * 2 = 1 := by
    rw [show ((2:AlgebraicClosure ℚ_[p]) = algebraMap ℤ_[p] _ 2) from (map_ofNat _ 2).symm,
      ← map_mul, h21, map_one]

  have hF_comul_Pm : F (comul (Pm h)) = B + C := by
    rw [hcomul_Pm, map_smul, map_sub, hF_Δh, hF_ΔSh, Algebra.smul_def]
    have hh : (A + B + C + D) - (A - B - C + D) = 2 * (B + C) := by ring
    rw [hh, ← mul_assoc, h2L, one_mul]
  have hF_comul_Pp : F (comul (h - Pm h)) = A + D := by
    rw [hcomul_Pp, map_sub, hF_comul_Pm, hF_Δh]; ring

  have hF_PmPm_comul_Pm : F ((TensorProduct.map Pm Pm) (comul (Pm h))) = 0 := by
    rw [hcomul_Pm, map_smul, map_sub, map_smul, map_sub, hF_PmPm_Δh, hF_PmPm_ΔSh, sub_self,
      smul_zero]
  have hF_PmPm_comul_Pp : F ((TensorProduct.map Pm Pm) (comul (h - Pm h))) = D := by
    rw [hcomul_Pp, map_sub, map_sub, hF_PmPm_Δh, hF_PmPm_comul_Pm, sub_zero]

  have hd₀L : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (Ring.inverse d₀) = (s ^ 2)⁻¹ := by
    have h1 : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (Ring.inverse d₀) * s ^ 2 = 1 := by
      rw [← hd₀s, ← map_mul, Ring.inverse_mul_cancel _ hd₀, map_one]
    exact eq_inv_of_mul_eq_one_left h1

  have hRHS : (β f' * β g') h = A + s⁻¹ * B + s⁻¹ * C + (s ^ 2)⁻¹ * D := by
    have hconv : (β f' * β g') h
        = (Algebra.TensorProduct.lmul' ℤ_[p])
            ((Algebra.TensorProduct.map (WithConv.ofConv (β f')) (WithConv.ofConv (β g')))
              (Bialgebra.comulAlgHom ℤ_[p] H h)) := by
      simp only [AlgHom.convMul_def, AlgHom.coe_comp, Function.comp_apply,
        WithConv.ofConv_toConv]
    rw [hconv, Bialgebra.comulAlgHom_apply, ← rep.eq, map_sum, map_sum]
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
    rw [hA, hB, hC, hD, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (WithConv.ofConv (β f')) (rep.left i) = (β f').ofConv (rep.left i) from rfl,
      show (WithConv.ofConv (β g')) (rep.right i) = (β g').ofConv (rep.right i) from rfl,
      hβ f' (rep.left i), hβ g' (rep.right i)]
    field_simp
    ring

  have hLHS : (β (f' * g')) h = A + s⁻¹ * B + s⁻¹ * C + (s ^ 2)⁻¹ * D := by
    rw [hβ (f' * g') h, hfg'_x (h - Pm h), hfg'_x (Pm h),
      hF_comul_Pp, hF_comul_Pm, hF_PmPm_comul_Pp, hF_PmPm_comul_Pm,
      Algebra.smul_def, Algebra.smul_def, map_sub, map_one, hd₀L]
    ring
  rw [hLHS, hRHS]

end S_HopfAlgebra_withConv_mul_signTwist_of_formula_of_linearEquiv_padicInt
end P2MW
export P2MW.S_HopfAlgebra_withConv_mul_signTwist_of_formula_of_linearEquiv_padicInt (solution)
