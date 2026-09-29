-- Prove2me | solution 1 for HopfAlgebra.nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cdcf09a7-c6cb-59c2-aee7-5f22b94c4ba1

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_basis_tateOort_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible

set_option autoImplicit false

universe u v

namespace S17OTgen

theorem main
    {R : Type u} [CommRing R] (h2 : Irreducible (2 : R))
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    (hrank : Module.finrank R H = 2) :
    Nonempty (H ≃ₐ[R] (Fin 2 → R)) ∨ Nonempty (H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod 2))) := by
  haveI : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact h2.not_isUnit (isUnit_of_subsingleton _)
  obtain ⟨e, a, b, he0, hab, hε, hxx, hΔ, hS⟩ :=
    HopfAlgebra.exists_basis_tateOort_two (H := H) hrank
  set x := e 1 with hxdef
  have hrepr : ∀ h : H, h = e.repr h 0 • (1 : H) + e.repr h 1 • x := fun h => by
    conv_lhs => rw [← e.sum_repr h]
    rw [Fin.sum_univ_two, he0]
  have hr1 : e.repr 1 = Finsupp.single 0 1 := by rw [← he0, e.repr_self]
  have hrx : e.repr x = Finsupp.single 1 1 := by rw [hxdef, e.repr_self]

  have hmul : ∀ h h' : H, h * h'
      = (e.repr h 0 * e.repr h' 0) • (1 : H)
        + (e.repr h 0 * e.repr h' 1 + e.repr h 1 * e.repr h' 0 + a * (e.repr h 1 * e.repr h' 1)) • x := by
    intro h h'
    conv_lhs => rw [hrepr h, hrepr h']
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hxx, smul_smul]
    module
  have hmul0 : ∀ h h' : H, e.repr (h * h') 0 = e.repr h 0 * e.repr h' 0 := by
    intro h h'
    have := congr(e.repr $(hmul h h') 0)
    simpa [hr1, hrx] using this
  have hmul1 : ∀ h h' : H, e.repr (h * h') 1
      = e.repr h 0 * e.repr h' 1 + e.repr h 1 * e.repr h' 0 + a * (e.repr h 1 * e.repr h' 1) := by
    intro h h'
    have := congr(e.repr $(hmul h h') 1)
    simpa [hr1, hrx] using this
  rcases h2.isUnit_or_isUnit hab.symm with ha | hb
  ·
    left
    obtain ⟨u, hu⟩ := ha
    let L : H →ₗ[R] (Fin 2 → R) :=
      LinearMap.pi ![e.coord 0, e.coord 0 + a • e.coord 1]
    have hL : ∀ h : H, L h = ![e.repr h 0, e.repr h 0 + a * e.repr h 1] := by
      intro h; ext i; fin_cases i <;> simp [L]
    have hL1 : L 1 = 1 := by
      rw [hL]; ext i; fin_cases i <;> simp [hr1]
    have hLmul : ∀ h h' : H, L (h * h') = L h * L h' := by
      intro h h'
      rw [hL, hL, hL]
      ext i; fin_cases i
      · simp [hmul0]
      · simp [hmul0, hmul1]; ring
    let φ : H →ₐ[R] (Fin 2 → R) := AlgHom.ofLinearMap L hL1 hLmul
    have hφ : ∀ h, φ h = ![e.repr h 0, e.repr h 0 + a * e.repr h 1] := hL
    refine ⟨AlgEquiv.ofBijective φ ⟨?_, ?_⟩⟩
    · intro h h' hh
      rw [hφ, hφ] at hh
      have h0 := congr_fun hh 0
      have h1 := congr_fun hh 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have h1' : e.repr h 1 = e.repr h' 1 := by
        have : a * (e.repr h 1 - e.repr h' 1) = 0 := by linear_combination h1 - h0
        rw [← hu] at this
        have := (Units.mul_right_eq_zero u).mp this
        linear_combination this
      rw [hrepr h, hrepr h', h0, h1']
    · intro r
      have hainv : a * ↑u⁻¹ = 1 := by rw [← hu, Units.mul_inv]
      set p : H := r 0 • (1 : H) + (↑u⁻¹ * (r 1 - r 0)) • x with hpdef
      have hp0 : e.repr p 0 = r 0 := by simp [hpdef, hr1, hrx]
      have hp1 : e.repr p 1 = ↑u⁻¹ * (r 1 - r 0) := by simp [hpdef, hr1, hrx]
      refine ⟨p, ?_⟩
      rw [hφ, hp0, hp1]
      funext i; fin_cases i
      · rfl
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linear_combination (r 1 - r 0) * hainv
  ·
    right
    obtain ⟨u, hu⟩ := hb
    set t : H := 1 - b • x with htdef
    have ht2 : t * t = 1 := by
      have h1 : t * t = 1 + (b * b * a - 2 * b) • x := by
        simp only [htdef, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hxx, smul_smul]
        module
      rw [h1, show b * b * a - 2 * b = 0 by linear_combination b * hab, zero_smul, add_zero]
    have hεt : Coalgebra.counit (R := R) t = 1 := by
      simp [htdef, Bialgebra.counit_one, hε]
    have hΔt : Coalgebra.comul (R := R) t = t ⊗ₜ[R] t := by
      simp only [htdef, map_sub, map_smul, Bialgebra.comul_one, hΔ, TensorProduct.tmul_sub, TensorProduct.sub_tmul,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul, ← Algebra.TensorProduct.one_def, smul_sub, smul_smul]
      module

    let G := Multiplicative (ZMod 2)
    have ht2' : t ^ 2 = 1 := by rw [sq, ht2]
    let ψG : G →* H :=
      { toFun := fun g => t ^ (Multiplicative.toAdd g).val
        map_one' := by simp
        map_mul' := by
          intro g h
          show t ^ (Multiplicative.toAdd (g * h)).val
            = t ^ (Multiplicative.toAdd g).val * t ^ (Multiplicative.toAdd h).val
          rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ ht2', pow_add] }
    have hψG0 : ψG (Multiplicative.ofAdd 0) = 1 := by
      change t ^ (Multiplicative.toAdd (Multiplicative.ofAdd (0 : ZMod 2))).val = 1
      rw [toAdd_ofAdd, ZMod.val_zero, pow_zero]
    have hψG1 : ψG (Multiplicative.ofAdd 1) = t := by
      change t ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = t
      rw [toAdd_ofAdd, ZMod.val_one, pow_one]
    have hψG_cases : ∀ g : G, ψG g = 1 ∨ ψG g = t := by
      intro g
      change t ^ (Multiplicative.toAdd g).val = 1 ∨ t ^ (Multiplicative.toAdd g).val = t
      have hlt : (Multiplicative.toAdd g).val < 2 := ZMod.val_lt _
      generalize (Multiplicative.toAdd g).val = n at hlt ⊢
      interval_cases n <;> simp
    have hψG_grouplike : ∀ g : G, Coalgebra.comul (R := R) (ψG g) = ψG g ⊗ₜ[R] ψG g ∧
        Coalgebra.counit (R := R) (ψG g) = 1 := by
      intro g
      rcases hψG_cases g with h | h <;> rw [h]
      · exact ⟨by rw [Bialgebra.comul_one, Algebra.TensorProduct.one_def], Bialgebra.counit_one⟩
      · exact ⟨hΔt, hεt⟩
    let Φ : MonoidAlgebra R G →ₐ[R] H := MonoidAlgebra.lift R H G ψG
    have hΦsingle : ∀ (g : G) (r : R), Φ (MonoidAlgebra.single g r) = r • ψG g := fun g r =>
      MonoidAlgebra.lift_single ψG g r

    have hcounit : Coalgebra.counit ∘ₗ Φ.toLinearMap = Coalgebra.counit := by
      refine MonoidAlgebra.lhom_ext' fun g => LinearMap.ext_ring ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply, AlgHom.toLinearMap_apply,
        hΦsingle, one_smul, (hψG_grouplike g).2, MonoidAlgebra.counit_single]
      simp
    have hcomul : TensorProduct.map Φ.toLinearMap Φ.toLinearMap ∘ₗ Coalgebra.comul
        = Coalgebra.comul ∘ₗ Φ.toLinearMap := by
      refine MonoidAlgebra.lhom_ext' fun g => LinearMap.ext_ring ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply, AlgHom.toLinearMap_apply,
        hΦsingle, one_smul, (hψG_grouplike g).1, MonoidAlgebra.comul_single]
      simp [CommSemiring.comul_apply, TensorProduct.map_tmul, hΦsingle]
    let Φc : MonoidAlgebra R G →ₐc[R] H :=
      { Φ with
        map_smul' := fun r z => by simp
        counit_comp := hcounit
        map_comp_comul := hcomul }
    have hΦc : ∀ z, Φc z = Φ z := fun z => rfl

    have hΦsurj : Function.Surjective Φc := by
      intro h
      refine ⟨MonoidAlgebra.single (Multiplicative.ofAdd 0) (e.repr h 0 + e.repr h 1 * ↑u⁻¹)
        - MonoidAlgebra.single (Multiplicative.ofAdd 1) (e.repr h 1 * ↑u⁻¹), ?_⟩
      rw [hΦc, map_sub, hΦsingle, hΦsingle, hψG0, hψG1, htdef]
      conv_rhs => rw [hrepr h]
      have hinv : e.repr h 1 * ↑u⁻¹ * b = e.repr h 1 := by
        rw [← hu, mul_assoc, Units.inv_mul, mul_one]
      simp only [smul_sub, smul_smul, hinv, add_smul]
      module

    haveI : Module.Free R (MonoidAlgebra R G) := .of_equiv (MonoidAlgebra.coeffLinearEquiv R).symm
    haveI : Module.Finite R (MonoidAlgebra R G) := .equiv (MonoidAlgebra.coeffLinearEquiv R).symm
    have hrankM : Module.finrank R (MonoidAlgebra R G) = 2 := by
      rw [(MonoidAlgebra.coeffLinearEquiv R).finrank_eq, Module.finrank_finsupp_self]; rfl
    have hΦinj : Function.Injective Φc := by
      let g : H ≃ₗ[R] MonoidAlgebra R G :=
        (Module.finBasisOfFinrankEq R H hrank).equiv (Module.finBasisOfFinrankEq R (MonoidAlgebra R G) hrankM)
          (Equiv.refl _)
      have hsurj' : Function.Surjective (Φ.toLinearMap ∘ₗ g.toLinearMap) := by
        exact hΦsurj.comp g.surjective
      have hinj' := OrzechProperty.injective_of_surjective_endomorphism (Φ.toLinearMap ∘ₗ g.toLinearMap) hsurj'
      intro p q hpq
      have := @hinj' (g.symm p) (g.symm q) (by simpa [hΦc] using hpq)
      simpa using this
    exact ⟨(BialgEquiv.ofBijective Φc ⟨hΦinj, hΦsurj⟩).symm⟩

end S17OTgen

theorem solution
    {R : Type u} [CommRing R] (h2 : Irreducible (2 : R))
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    (hrank : Module.finrank R H = 2) :
    Nonempty (H ≃ₐ[R] (Fin 2 → R)) ∨ Nonempty (H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod 2))) :=
  S17OTgen.main h2 H hrank

end S_HopfAlgebra_nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible
end P2MW
export P2MW.S_HopfAlgebra_nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible (solution)
