-- Prove2me | solution 1 for ModularCurve.IsGamma1Link.of_map_of_surjective_of_ker_pow_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/1290615c-8020-5b88-a8b4-6655282f9a44

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Theorems.Thm_ModularCurve_IsGamma0PowAt_exists_faithfullyFlat_map_eq_prod_X_sub_C_of_ne_two
import Theorems.Thm_Polynomial_dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero
import Theorems.Thm_exists_isIdempotentElem_mul_eq_of_mul_eq_zero_of_isCoprime
import Theorems.Thm_WeierstrassCurve_exists_smul_abscissa_prod_X_sub_C_dvd_prePsi
import Theorems.Thm_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

open Polynomial

namespace LinkLift

theorem hom_eval {R S : Type u} [CommRing R] [CommRing S] (χ : R →+* S) (p : R[X]) (a : R) :
    χ (p.eval a) = (p.map χ).eval (χ a) := by
  rw [eval_map, eval₂_at_apply]

theorem eval_prod_X_sub_C {S : Type u} [CommRing S] {ι : Type} (s : Finset ι) (r : ι → S) (z : S) :
    (∏ i ∈ s, (X - C (r i))).eval z = ∏ i ∈ s, (z - r i) := by
  rw [eval_prod]; simp only [eval_sub, eval_X, eval_C]

end LinkLift

open LinkLift in
theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (ℓ : ℕ) (hℓp : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓu : IsUnit ((ℓ : ℕ) : T))
    (M' : ℕ) [NeZero M'] (hM'u : IsUnit ((M' : ℕ) : T))
    (h : ↥M'.primeFactors → Polynomial T)
    (hh : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (h p))
    (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D)
    (hlk' : ModularCurve.IsGamma1Link (W.map π) ℓ M' (fun p => (h p).map π) (D.map π)) :
    ModularCurve.IsGamma1Link W ℓ M' h D := by
  classical
  intro hmem
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓ2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ := hℓp.odd_of_ne_two hℓ2
  obtain ⟨-, hℓM', hM'0⟩ := Nat.mem_primeFactors.mp hmem
  set k : ℕ := M'.factorization ℓ with hk
  have hk1 : 1 ≤ k := hℓp.factorization_pos_of_dvd hM'0 hℓM'
  set n : ℕ := ℓ ^ (k - 1) with hn
  set hl : Polynomial T := h ⟨ℓ, hmem⟩ with hhl
  set F : Polynomial T := ModularCurve.inLineMulPoly W ℓ n D.xP with hF
  show hl ∣ F
  have hhℓ : ModularCurve.IsGamma0PowAt W ℓ k hl := hh ⟨ℓ, hmem⟩
  have hpk2 : ℓ ^ k ≠ 2 := by
    intro h2; have : Odd (ℓ ^ k) := hodd.pow; rw [h2] at this; exact absurd this (by decide)
  have hcg : W.IsCyclicGenKernel ℓ k hl := (ModularCurve.isGamma0PowAt_of_pow_ne_two W hpk2 hl).mp hhℓ
  have hmon : hl.Monic := hcg.monic

  obtain ⟨S, instS, algS, ffS, ι, instι, decι, xs, ys, hEq, hsplit, hdiffS⟩ :=
    ModularCurve.IsGamma0PowAt.exists_faithfullyFlat_map_eq_prod_X_sub_C_of_ne_two W hΔ ℓ k hℓu hℓ2 hl hhℓ
  set f : T →+* S := algebraMap T S with hfdef
  have hinj : Function.Injective f := FaithfulSMul.algebraMap_injective T S
  set WS : WeierstrassCurve S := W.map f with hWS
  have hΔS : IsUnit WS.Δ := by rw [hWS, WeierstrassCurve.map_Δ]; exact hΔ.map f
  have hℓS : IsUnit ((ℓ : ℕ) : S) := by have := hℓu.map f; rwa [map_natCast] at this
  have hℓΔS : IsUnit ((ℓ : S) * WS.Δ) := hℓS.mul hΔS

  obtain ⟨c, hc⟩ := hcg.mul_preΨ_dvd
  set Λ : Polynomial T := hl * c with hΛdef
  have hΛ : W.preΨ (ℓ ^ k) = W.preΨ (ℓ ^ (k - 1)) * Λ := by rw [hc, hΛdef]; ring
  have hΛS : WS.preΨ (ℓ ^ k) = WS.preΨ (ℓ ^ (k - 1)) * Λ.map f := by
    rw [hWS, WeierstrassCurve.map_preΨ, WeierstrassCurve.map_preΨ, ← Polynomial.map_mul, ← hΛ]
  have hΛroot : ∀ i, (Λ.map f).eval (xs i) = 0 := by
    intro i
    rw [hΛdef, Polynomial.map_mul, eval_mul, hsplit, eval_prod_X_sub_C, Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _),
      zero_mul]

  have hQ : ∀ i, IsUnit ((WS.ΨSq (ℓ ^ (k - 1) : ℕ)).eval (xs i)) ∧
      (WS.preΨ ℓ).eval ((WS.Φ (ℓ ^ (k - 1) : ℕ)).eval (xs i) * Ring.inverse ((WS.ΨSq (ℓ ^ (k - 1) : ℕ)).eval (xs i))) = 0 :=
    fun i => WeierstrassCurve.isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero WS ℓ hℓ2 k hk1 hℓΔS hΛS (xs i) (ys i) (hEq i) (hΛroot i)

  have hxP : (WS.preΨ ℓ).eval (f D.xP) = 0 := by
    rw [hWS, WeierstrassCurve.map_preΨ, ← hom_eval, hD.preΨ_P, map_zero]
  obtain ⟨r, hr, hrdiff, hPdvd⟩ := WeierstrassCurve.exists_smul_abscissa_prod_X_sub_C_dvd_prePsi WS ℓ hℓ2 hℓΔS (f D.xP) hxP
  set I : Finset ℕ := Finset.Icc 1 ((ℓ - 1) / 2) with hI
  set hP : Polynomial S := ∏ a ∈ I, (X - C (r a)) with hhP
  obtain ⟨c', hc'⟩ := hPdvd

  have hsep : (WS.preΨ' ℓ).Separable := WeierstrassCurve.separable_prePsi_of_isUnit WS hodd hℓΔS
  have hcop : IsCoprime hP c' := by
    have : WS.preΨ (ℓ : ℕ) = hP * c' := hc'
    rw [WeierstrassCurve.preΨ_ofNat] at this
    rw [this] at hsep
    exact hsep.isCoprime

  set J : Ideal S := Ideal.map f (RingHom.ker π) with hJ
  obtain ⟨N, hN⟩ := hnil
  have hJN : J ^ N = ⊥ := by rw [hJ, ← Ideal.map_pow, hN, Ideal.map_bot]
  set q : S →+* S ⧸ J := Ideal.Quotient.mk J with hq
  have hle : ∀ a ∈ RingHom.ker π, (q.comp f) a = 0 := by
    intro a ha
    show Ideal.Quotient.mk J (f a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f ha)
  let ψ₀ : T ⧸ RingHom.ker π →+* S ⧸ J := Ideal.Quotient.lift (RingHom.ker π) (q.comp f) hle
  let ψ : T' →+* S ⧸ J := ψ₀.comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ψ.comp π = q.comp f := by
    ext a
    show ψ₀ ((RingHom.quotientKerEquivOfSurjective hπ).symm (π a)) = q (f a)
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
    rfl
  have hFJ : ∀ i, (F.map f).eval (xs i) ∈ J := by
    intro i
    have hdv := hlk' hmem

    have e1 : (fun p : ↥M'.primeFactors => (h p).map π) ⟨ℓ, hmem⟩ = hl.map π := rfl
    rw [e1, ModularCurve.LevelPData.map_xP, ModularCurve.inLineMulPoly_map] at hdv
    have hdv' := Polynomial.map_dvd ψ hdv
    rw [Polynomial.map_map, Polynomial.map_map, hψ, ← Polynomial.map_map, ← Polynomial.map_map, hsplit, Polynomial.map_prod] at hdv'
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at hdv'
    have hz : ((F.map f).map q).eval (q (xs i)) = 0 := by
      obtain ⟨g, hg⟩ := hdv'
      rw [show (ModularCurve.inLineMulPoly W ℓ n D.xP).map f = F.map f from rfl] at hg
      rw [hg, eval_mul, eval_prod_X_sub_C, Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _), zero_mul]
    rw [← hom_eval] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz

  have hFz : ∀ i, (F.map f).eval (xs i) = 0 := by
    intro i
    obtain ⟨hu, hroot⟩ := hQ i
    set u : S := (WS.ΨSq (ℓ ^ (k - 1) : ℕ)).eval (xs i) with hudef
    set xQ : S := (WS.Φ (ℓ ^ (k - 1) : ℕ)).eval (xs i) * Ring.inverse u with hxQ
    have huinv : u * Ring.inverse u = 1 := Ring.mul_inverse_cancel _ hu

    have hFeval : (F.map f).eval (xs i) = (∏ a ∈ I, u * (WS.ΨSq a).eval (f D.xP)) * hP.eval xQ := by
      rw [hF, ← ModularCurve.inLineMulPoly_map, ModularCurve.inLineMulPoly, eval_prod, hhP, eval_prod_X_sub_C, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun a ha => ?_)
      obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
      obtain ⟨-, hra⟩ := hr a ha1 ha2
      simp only [eval_sub, eval_mul, eval_C]
      rw [← hra, hxQ]
      simp only [hWS, hn] at hudef ⊢
      rw [← hudef]
      linear_combination (-(((W.map f).Φ ((ℓ ^ (k - 1) : ℕ) : ℤ)).eval (xs i) * ((W.map f).ΨSq (a : ℤ)).eval (f D.xP))) * huinv
    have hUnit : IsUnit (∏ a ∈ I, u * (WS.ΨSq a).eval (f D.xP)) := by
      refine Finset.prod_induction _ (fun t => IsUnit t) (fun _ _ h1 h2 => h1.mul h2) isUnit_one (fun a ha => ?_)
      obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
      exact hu.mul (hr a ha1 ha2).1

    have hprod0 : hP.eval xQ * c'.eval xQ = 0 := by rw [← eval_mul, ← hc']; exact hroot
    have hcop' : IsCoprime (hP.eval xQ) (c'.eval xQ) := by
      obtain ⟨a, b, hab⟩ := hcop
      exact ⟨a.eval xQ, b.eval xQ, by have := congrArg (eval xQ) hab; simpa only [eval_add, eval_mul, eval_one] using this⟩
    obtain ⟨e, w, he, hw, hew⟩ := exists_isIdempotentElem_mul_eq_of_mul_eq_zero_of_isCoprime hprod0 hcop'

    have heJ : e ∈ J := by
      have h1 : (F.map f).eval (xs i) = e * ((∏ a ∈ I, u * (WS.ΨSq a).eval (f D.xP)) * w) := by rw [hFeval, hew]; ring
      obtain ⟨v, hv⟩ := (hUnit.mul hw).exists_left_inv
      have : e = v * (F.map f).eval (xs i) := by rw [h1, mul_comm e, ← mul_assoc, hv, one_mul]
      rw [this]; exact Ideal.mul_mem_left J v (hFJ i)
    have he0 : e = 0 := by
      apply he.eq_zero_of_isNilpotent
      exact ⟨N, by have := Ideal.pow_mem_pow heJ N; rw [hJN] at this; exact (Submodule.mem_bot S).mp this⟩
    rw [hFeval, hew, he0, zero_mul, mul_zero]

  exact Polynomial.dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero f hinj hl hmon xs hsplit hdiffS F hFz

end S_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot
end P2MW
export P2MW.S_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot (solution)
