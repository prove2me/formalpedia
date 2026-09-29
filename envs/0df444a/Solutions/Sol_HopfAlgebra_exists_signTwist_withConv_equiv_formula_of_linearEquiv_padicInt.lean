-- Prove2me | solution 1 for HopfAlgebra.exists_signTwist_withConv_equiv_formula_of_linearEquiv_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/362707cc-bdc5-5db2-a0c5-ec39adef14c9

import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_antipode_antipode
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_signTwist_withConv_equiv_formula_of_linearEquiv_padicInt

open scoped NNReal TensorProduct
open Coalgebra HopfAlgebra

open scoped _root_.TensorProduct _root_.Coalgebra.TensorProduct in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (s : AlgebraicClosure ℚ_[p]) (hs0 : s ≠ 0)
    (d₀ : ℤ_[p]) (hd₀s : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) d₀ = s ^ 2)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (H' : Type) [CommRing H'] [HopfAlgebra ℤ_[p] H']
    (e : H' ≃ₗ[ℤ_[p]] H)
    (he1 : e 1 = 1)
    (hemul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a b : H', e (a * b) = e a * e b + (d₀ - 1) • (Pm (e a) * Pm (e b)))
    (heant : ∀ a : H', e (HopfAlgebra.antipode ℤ_[p] a) = HopfAlgebra.antipode ℤ_[p] (e a)) :
    let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    ∃ β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
      ∀ (φ' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])) (h : H),
        (β φ') h = φ' (e.symm (h - Pm h)) + s⁻¹ * φ' (e.symm (Pm h)) := by
  set Pm : H →ₗ[ℤ_[p]] H :=
    Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p]) with hPm_def
  simp only at hemul
  simp only

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
  have h2cancel : ∀ a b : H, (2:ℤ_[p]) • a = (2:ℤ_[p]) • b → a = b := by
    intro a b hab
    have h := congrArg (Ring.inverse (2:ℤ_[p]) • ·) hab
    simpa only [smul_smul, h21, one_smul] using h
  have hS2 : ∀ x : H, antipode ℤ_[p] (antipode ℤ_[p] x) = x :=
    fun x => HopfAlgebra.antipode_antipode x
  have hSmul : ∀ x y : H, antipode ℤ_[p] (x * y) = antipode ℤ_[p] x * antipode ℤ_[p] y := by
    intro x y; rw [antipode_mul, mul_comm]
  have h2Pm : ∀ x : H, (2:ℤ_[p]) • Pm x = x - antipode ℤ_[p] x := by
    intro x
    rw [hPm_def, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
      smul_smul, mul_comm, h21, one_smul]
  have hSeq : ∀ x : H, antipode ℤ_[p] x = (x - Pm x) - Pm x := by
    intro x; rw [sub_sub, ← two_smul ℤ_[p] (Pm x), h2Pm, sub_sub_cancel]
  have hSPm : ∀ x : H, antipode ℤ_[p] (Pm x) = - Pm x := by
    intro x
    simp only [hPm_def, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_smul, map_sub, hS2]
    rw [← smul_neg, neg_sub]
  have hPm1 : Pm (1 : H) = 0 := by
    simp only [hPm_def, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
      antipode_one, sub_self, smul_zero]
  have hPmPm : ∀ x : H, Pm (Pm x) = Pm x := by
    intro x
    apply h2cancel
    rw [h2Pm (Pm x), hSPm, sub_neg_eq_add, ← two_smul ℤ_[p]]
  have hPmPp : ∀ x : H, Pm (x - Pm x) = 0 := by
    intro x; rw [map_sub, hPmPm, sub_self]
  have hPpPm : ∀ x : H, (Pm x) - Pm (Pm x) = 0 := by
    intro x; rw [hPmPm, sub_self]
  have he1' : e.symm (1 : H) = 1 := by rw [← he1, LinearEquiv.symm_apply_apply]
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0

  have hPm_mul : ∀ x y : H, Pm (x * y) = (x - Pm x) * Pm y + Pm x * (y - Pm y) := by
    intro x y
    apply h2cancel
    rw [h2Pm (x*y), hSmul, hSeq x, hSeq y, two_smul ℤ_[p]]
    ring
  have hPp_mul : ∀ x y : H,
      x * y - Pm (x * y) = (x - Pm x) * (y - Pm y) + Pm x * Pm y := by
    intro x y; rw [hPm_mul]; ring
  have hPm_PmPm : ∀ x y : H, Pm (Pm x * Pm y) = 0 := by
    intro x y; rw [hPm_mul, hPpPm, hPpPm, zero_mul, mul_zero, add_zero]

  have hψ_mul : ∀ (φ' : H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) (a b : H),
      φ' (e.symm a) * φ' (e.symm b)
        = φ' (e.symm (a * b)) + (s ^ 2 - 1) * φ' (e.symm (Pm a * Pm b)) := by
    intro φ' a b
    have hee : e (e.symm a * e.symm b) = a * b + (d₀ - 1) • (Pm a * Pm b) := by
      rw [hemul (e.symm a) (e.symm b), LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    have hee' : e.symm a * e.symm b = e.symm (a * b + (d₀ - 1) • (Pm a * Pm b)) := by
      rw [← hee, LinearEquiv.symm_apply_apply]
    rw [← map_mul, hee', map_add, map_smul, map_add, map_smul, Algebra.smul_def,
      ← hd₀s, map_sub, map_one]

  let Tlin : (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) → (H →ₗ[ℤ_[p]] AlgebraicClosure ℚ_[p]) :=
    fun φ' => (φ'.toLinearMap ∘ₗ e.symm.toLinearMap) ∘ₗ (LinearMap.id - Pm)
      + s⁻¹ • ((φ'.toLinearMap ∘ₗ e.symm.toLinearMap) ∘ₗ Pm)
  have hTlin_apply : ∀ (φ' : H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) (x : H),
      Tlin φ' x = φ' (e.symm (x - Pm x)) + s⁻¹ * φ' (e.symm (Pm x)) := by
    intro φ' x
    simp only [Tlin, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_toLinearMap, smul_eq_mul, map_sub]
  have hTlin_one : ∀ φ', Tlin φ' 1 = 1 := by
    intro φ'
    rw [hTlin_apply, hPm1, sub_zero, he1', map_one, map_zero, map_zero, mul_zero, add_zero]
  have hTlin_mul : ∀ φ' (x y : H), Tlin φ' (x * y) = Tlin φ' x * Tlin φ' y := by
    intro φ' x y
    rw [hTlin_apply, hTlin_apply, hTlin_apply, hPp_mul, hPm_mul, map_add, map_add,
      map_add, map_add]
    have h1 : φ' (e.symm ((x - Pm x) * (y - Pm y)))
        = φ' (e.symm (x - Pm x)) * φ' (e.symm (y - Pm y)) := by
      have := hψ_mul φ' (x - Pm x) (y - Pm y)
      rw [hPmPp, zero_mul, map_zero, map_zero, mul_zero, add_zero] at this
      exact this.symm
    have h2 : φ' (e.symm ((x - Pm x) * Pm y))
        = φ' (e.symm (x - Pm x)) * φ' (e.symm (Pm y)) := by
      have := hψ_mul φ' (x - Pm x) (Pm y)
      rw [hPmPp, zero_mul, map_zero, map_zero, mul_zero, add_zero] at this
      exact this.symm
    have h3 : φ' (e.symm (Pm x * (y - Pm y)))
        = φ' (e.symm (Pm x)) * φ' (e.symm (y - Pm y)) := by
      have := hψ_mul φ' (Pm x) (y - Pm y)
      rw [hPmPp, mul_zero, map_zero, map_zero, mul_zero, add_zero] at this
      exact this.symm
    have h4 : s ^ 2 * φ' (e.symm (Pm x * Pm y))
        = φ' (e.symm (Pm x)) * φ' (e.symm (Pm y)) := by
      have h := hψ_mul φ' (Pm x) (Pm y)
      rw [hPmPm, hPmPm] at h
      rw [h]; ring
    rw [h1, h2, h3]
    field_simp
    linear_combination h4
  let T : (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) → (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) :=
    fun φ' => AlgHom.ofLinearMap (Tlin φ') (hTlin_one φ') (hTlin_mul φ')
  have hT_apply : ∀ φ' x, T φ' x = φ' (e.symm (x - Pm x)) + s⁻¹ * φ' (e.symm (Pm x)) := by
    intro φ' x; exact hTlin_apply φ' x

  let Ulin : (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) → (H' →ₗ[ℤ_[p]] AlgebraicClosure ℚ_[p]) :=
    fun φ => (φ.toLinearMap ∘ₗ (LinearMap.id - Pm) ∘ₗ (e : H' →ₗ[ℤ_[p]] H))
      + s • (φ.toLinearMap ∘ₗ Pm ∘ₗ (e : H' →ₗ[ℤ_[p]] H))
  have hUlin_apply : ∀ (φ : H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) (h' : H'),
      Ulin φ h' = φ (e h' - Pm (e h')) + s * φ (Pm (e h')) := by
    intro φ h'
    simp only [Ulin, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_coe, smul_eq_mul, map_sub]
  have hUlin_one : ∀ φ, Ulin φ 1 = 1 := by
    intro φ
    rw [hUlin_apply, he1, hPm1, sub_zero, map_one, map_zero, mul_zero, add_zero]
  have hUlin_mul : ∀ φ (a b : H'), Ulin φ (a * b) = Ulin φ a * Ulin φ b := by
    intro φ a b
    rw [hUlin_apply, hUlin_apply, hUlin_apply]
    have heab : e (a * b) = e a * e b + (d₀ - 1) • (Pm (e a) * Pm (e b)) := hemul a b
    have hPm_eab : Pm (e (a * b))
        = (e a - Pm (e a)) * Pm (e b) + Pm (e a) * (e b - Pm (e b)) := by
      rw [heab, map_add, map_smul, hPm_mul (e a) (e b), hPm_PmPm, smul_zero, add_zero]
    have hPp_eab : e (a * b) - Pm (e (a * b))
        = (e a - Pm (e a)) * (e b - Pm (e b)) + d₀ • (Pm (e a) * Pm (e b)) := by
      rw [hPm_eab, heab, sub_smul, one_smul, Algebra.smul_def]
      ring
    rw [hPp_eab, hPm_eab]
    simp only [map_add, map_smul, map_mul]
    first
    | { rw [Algebra.smul_def, hd₀s]; ring }
    | { simp only [Algebra.smul_def, AlgHom.commutes, hd₀s]; ring }
    | { rw [show (d₀ • (φ (Pm (e a)) * φ (Pm (e b))) : AlgebraicClosure ℚ_[p])
          = s ^ 2 * (φ (Pm (e a)) * φ (Pm (e b))) from by rw [Algebra.smul_def, hd₀s]]
        ring }
  let U : (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) → (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) :=
    fun φ => AlgHom.ofLinearMap (Ulin φ) (hUlin_one φ) (hUlin_mul φ)
  have hU_apply : ∀ φ h', U φ h' = φ (e h' - Pm (e h')) + s * φ (Pm (e h')) := by
    intro φ h'; exact hUlin_apply φ h'

  have hUT : ∀ φ', U (T φ') = φ' := by
    intro φ'
    refine AlgHom.ext fun h' => ?_
    rw [hU_apply, hT_apply, hT_apply, hPmPp, hPpPm, sub_zero, map_zero, map_zero, mul_zero,
      add_zero, hPmPm, zero_add, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul,
      ← map_add, ← map_add, sub_add_cancel, LinearEquiv.symm_apply_apply]
  have hTU : ∀ φ, T (U φ) = φ := by
    intro φ
    refine AlgHom.ext fun h => ?_
    rw [hT_apply, hU_apply, hU_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, hPmPp, hPpPm, sub_zero, map_zero, mul_zero, add_zero,
      hPmPm, zero_add, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul,
      ← map_add, sub_add_cancel]

  refine ⟨{ toFun := fun φ' => WithConv.toConv (T (WithConv.ofConv φ'))
            invFun := fun φ => WithConv.toConv (U (WithConv.ofConv φ))
            left_inv := fun φ' => by
              simp only [WithConv.ofConv_toConv, hUT, WithConv.toConv_ofConv]
            right_inv := fun φ => by
              simp only [WithConv.ofConv_toConv, hTU, WithConv.toConv_ofConv] }, ?_⟩
  intro φ' h
  simp only [Equiv.coe_fn_mk, WithConv.ofConv_toConv]
  exact hT_apply (WithConv.ofConv φ') h

end S_HopfAlgebra_exists_signTwist_withConv_equiv_formula_of_linearEquiv_padicInt
end P2MW
export P2MW.S_HopfAlgebra_exists_signTwist_withConv_equiv_formula_of_linearEquiv_padicInt (solution)
