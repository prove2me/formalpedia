-- Prove2me | solution 1 for ModularCurve.IsGamma0PowAt.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/660f7985-6d42-51e3-9362-316951311523

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_Polynomial_existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
import Theorems.Thm_WeierstrassCurve_eval_Phi_div_PsiSq_eq_zero_of_prePsi_pow_eq_mul_of_eval_eq_zero
import Theorems.Thm_WeierstrassCurve_prePsi_dvd_prePsi_of_dvd
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit_of_even
import Theorems.Thm_WeierstrassCurve_IsTwoKernel_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsGamma0PowAt_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃"

set_option autoImplicit false

universe u

open Polynomial

namespace GenkerLift

variable {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T')

theorem isNilpotent_of_map_eq_zero (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥) {a : T}
    (ha : π a = 0) : IsNilpotent a := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have h : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow (by simpa [RingHom.mem_ker] using ha) n
  rw [hn] at h
  simpa using h

theorem map_eq_zero_iff_mem (p : T[X]) :
    p.map π = 0 ↔ p ∈ (RingHom.ker π).map (C : T →+* T[X]) := by
  rw [← Polynomial.coe_mapRingHom, ← RingHom.mem_ker, Polynomial.ker_mapRingHom]

theorem isNilpotent_poly_of_map_eq_zero (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥) {p : T[X]}
    (hp : p.map π = 0) : IsNilpotent p := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have hmem : p ∈ (RingHom.ker π).map (C : T →+* T[X]) := (map_eq_zero_iff_mem π p).mp hp
  have h : p ^ n ∈ ((RingHom.ker π).map (C : T →+* T[X])) ^ n := Ideal.pow_mem_pow hmem n
  rw [← Ideal.map_pow, hn, Ideal.map_bot] at h
  simpa using h

theorem isCoprime_of_isCoprime_map (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥) {p q : T[X]}
    (h : IsCoprime (p.map π) (q.map π)) : IsCoprime p q := by
  obtain ⟨u', v', huv⟩ := h
  obtain ⟨u, rfl⟩ := Polynomial.map_surjective π hπ u'
  obtain ⟨v, rfl⟩ := Polynomial.map_surjective π hπ v'
  have hz : (u * p + v * q - 1).map π = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, huv,
      sub_self]
  have hw : IsUnit (u * p + v * q - 1 + 1) := (isNilpotent_poly_of_map_eq_zero π hnil hz).isUnit_add_one
  rw [sub_add_cancel] at hw
  obtain ⟨w, hw⟩ := hw
  refine ⟨↑w⁻¹ * u, ↑w⁻¹ * v, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, ← hw, Units.inv_mul]

theorem eval_smulNumerator_of_isUnit {B : Type u} [CommRing B] (V : WeierstrassCurve B) (a d : ℕ)
    (h : B[X]) (hdeg : h.natDegree ≤ d) (ξ : B) (hu : IsUnit ((V.ΨSq a).eval ξ)) :
    (V.smulNumerator a d h).eval ξ =
      (V.ΨSq a).eval ξ ^ d * h.eval ((V.Φ a).eval ξ * Ring.inverse ((V.ΨSq a).eval ξ)) := by
  set Ψ : B := (V.ΨSq a).eval ξ with hΨ
  set Φ : B := (V.Φ a).eval ξ with hΦ
  have hinv : Ψ * Ring.inverse Ψ = 1 := Ring.mul_inverse_cancel Ψ hu
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.mul_sum]
  simp only [WeierstrassCurve.smulNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← hΨ, ← hΦ, mul_pow, show Ψ ^ d = Ψ ^ (d - i) * Ψ ^ i by rw [← pow_add, Nat.sub_add_cancel hi']]
  have : Ψ ^ i * Ring.inverse Ψ ^ i = 1 := by rw [← mul_pow, hinv, one_pow]
  calc h.coeff i * Φ ^ i * Ψ ^ (d - i)
      = h.coeff i * Φ ^ i * Ψ ^ (d - i) * (Ψ ^ i * Ring.inverse Ψ ^ i) := by rw [this, mul_one]
    _ = Ψ ^ (d - i) * Ψ ^ i * (h.coeff i * (Φ ^ i * Ring.inverse Ψ ^ i)) := by ring

theorem dvd_smulNumerator_of_isNilpotent_pow (W : WeierstrassCurve T) {p : ℕ} [Fact p.Prime] (k : ℕ)
    (hpΔ : IsUnit ((p : T) * W.Δ)) {Λ h g : T[X]}
    (hΛ : W.preΨ (p ^ k) = W.preΨ (p ^ (k - 1)) * Λ) (hfac : Λ = h * g) (hcop : IsCoprime h g)
    {a d : ℕ} (hdeg : h.natDegree ≤ d) (haZ : ¬ ((p : ℤ) ∣ (a : ℤ)))
    (hnil : IsNilpotent (AdjoinRoot.mk h (W.smulNumerator a d h))) :
    h ∣ W.smulNumerator a d h := by

  have hevalmk : ∀ q : T[X],
      (q.map (AdjoinRoot.of h)).eval (AdjoinRoot.root h) = AdjoinRoot.mk h q := by
    intro q
    rw [Polynomial.eval_map, ← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]
  have hhξ : (h.map (AdjoinRoot.of h)).eval (AdjoinRoot.root h) = 0 := by
    rw [hevalmk, AdjoinRoot.mk_self]
  set ι : T →+* AdjoinRoot h := AdjoinRoot.of h with hι
  set ξ : AdjoinRoot h := AdjoinRoot.root h with hξ
  set V : WeierstrassCurve (AdjoinRoot h) := W.map ι with hV
  have hΛξ : (Λ.map ι).eval ξ = 0 := by
    rw [hfac, Polynomial.map_mul, Polynomial.eval_mul, hhξ, zero_mul]
  have hΛV : V.preΨ (p ^ k) = V.preΨ (p ^ (k - 1)) * Λ.map ι := by
    rw [hV, WeierstrassCurve.map_preΨ, WeierstrassCurve.map_preΨ, hΛ, Polynomial.map_mul]
  have hpΔB : IsUnit ((p : AdjoinRoot h) * V.Δ) := by
    have := hpΔ.map ι
    rw [map_mul, map_natCast] at this
    rwa [hV, WeierstrassCurve.map_Δ]
  obtain ⟨hu, hroot⟩ :=
    WeierstrassCurve.eval_Phi_div_PsiSq_eq_zero_of_prePsi_pow_eq_mul_of_eval_eq_zero V k hpΔB hΛV hΛξ haZ
  set Ψ : AdjoinRoot h := (V.ΨSq (a : ℤ)).eval ξ with hΨ
  set xa : AdjoinRoot h := (V.Φ (a : ℤ)).eval ξ * Ring.inverse Ψ with hxa
  set α : AdjoinRoot h := (h.map ι).eval xa with hα
  set β : AdjoinRoot h := (g.map ι).eval xa with hβ

  have hαβ : α * β = 0 := by
    rw [hα, hβ, ← Polynomial.eval_mul, ← Polynomial.map_mul, ← hfac]
    exact hroot

  obtain ⟨U, V', hUV⟩ := hcop.map (Polynomial.mapRingHom ι)
  simp only [Polynomial.coe_mapRingHom] at hUV
  have hUV' : U.eval xa * α + V'.eval xa * β = 1 := by
    have := congrArg (Polynomial.eval xa) hUV
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] using this

  have hS : AdjoinRoot.mk h (W.smulNumerator a d h) = Ψ ^ d * α := by
    rw [← hevalmk, ← WeierstrassCurve.smulNumerator_map]
    have hdeg' : (h.map ι).natDegree ≤ d := (Polynomial.natDegree_map_le).trans hdeg
    have := eval_smulNumerator_of_isUnit V a d (h.map ι) hdeg' ξ hu
    rw [this]
  have hαnil : IsNilpotent α := by
    have h1 : IsNilpotent (Ring.inverse Ψ ^ d * (Ψ ^ d * α)) := by
      rw [← hS]; exact Commute.isNilpotent_mul_left (Commute.all _ _) hnil
    have h2 : Ring.inverse Ψ ^ d * (Ψ ^ d * α) = α := by
      rw [← mul_assoc, ← mul_pow, Ring.inverse_mul_cancel Ψ hu, one_pow, one_mul]
    rwa [h2] at h1

  have hβunit : IsUnit β := by
    have h1 : IsUnit (V'.eval xa * β) := by
      have h2 : V'.eval xa * β = 1 + -(U.eval xa * α) := by rw [← hUV']; ring
      rw [h2]
      exact (Commute.isNilpotent_mul_left (Commute.all _ _) hαnil).neg.isUnit_one_add
    exact isUnit_of_mul_isUnit_right h1
  have hα0 : α = 0 := by
    have := congrArg (· * Ring.inverse β) hαβ
    simpa only [mul_assoc, Ring.mul_inverse_cancel β hβunit, mul_one, zero_mul] using this
  rw [← AdjoinRoot.mk_eq_zero, hS, hα0, mul_zero]

end GenkerLift

open GenkerLift in
theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (p : ℕ) [Fact p.Prime] (k : ℕ) (hp : IsUnit ((p : ℕ) : T))
    (h' : Polynomial T') (hh' : ModularCurve.IsGamma0PowAt (W.map π) p k h') :
    ∃! h : Polynomial T, h.map π = h' ∧ ModularCurve.IsGamma0PowAt W p k h := by
  by_cases hpk : p ^ k = 2
  ·
    rw [ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk] at hh'
    simp_rw [ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk]
    have hp2 : p = 2 := by
      have hk : k ≠ 0 := by rintro rfl; simp at hpk
      exact (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime 2) p
        (hpk ▸ dvd_pow_self p hk)).elim (fun h1 => absurd h1 (Fact.out : p.Prime).one_lt.ne') id
    have h2 : IsUnit (2 : T) := by simpa [hp2] using hp
    exact WeierstrassCurve.IsTwoKernel.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
      π hπ hnil W hΔ h2 h' hh'
  ·
    rw [ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk] at hh'
    simp_rw [ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk]

    rcases subsingleton_or_nontrivial T with hT | hT
    · haveI := hT
      haveI : Subsingleton T[X] := inferInstance
      have hT' : Subsingleton T' := hπ.subsingleton
      haveI : Subsingleton T'[X] := inferInstance
      refine ⟨0, ⟨Subsingleton.elim _ _, ⟨by simp, Subsingleton.elim _ _, ⟨0, Subsingleton.elim _ _⟩,
        fun a _ _ _ => ⟨0, Subsingleton.elim _ _⟩⟩⟩, fun _ _ => Subsingleton.elim _ _⟩

    set d : ℕ := Nat.totient (p ^ k) / 2 with hd
    have hpΔ : IsUnit ((p : T) * W.Δ) := hp.mul hΔ
    have hΔ' : IsUnit (W.map π).Δ := by rw [WeierstrassCurve.map_Δ]; exact hΔ.map π
    have hp' : IsUnit ((p : ℕ) : T') := by simpa using hp.map π
    have hT' : Nontrivial T' := by
      by_contra htriv
      rw [not_nontrivial_iff_subsingleton] at htriv
      have h1 : IsNilpotent (1 : T) := isNilpotent_of_map_eq_zero π hnil (Subsingleton.elim _ _)
      exact (isUnit_one.not_isNilpotent) h1 |> fun h => h.elim

    obtain ⟨Λ, hΛ⟩ : W.preΨ (p ^ (k - 1)) ∣ W.preΨ (p ^ k) :=
      W.prePsi_dvd_prePsi_of_dvd (pow_dvd_pow (p : ℤ) (Nat.sub_le k 1))
    set P : T[X] := W.preΨ (p ^ (k - 1)) with hP
    have hΛmap : (W.map π).preΨ (p ^ k) = P.map π * Λ.map π := by
      rw [WeierstrassCurve.map_preΨ, hΛ, Polynomial.map_mul]
    have hPmap : (W.map π).preΨ (p ^ (k - 1)) = P.map π := by rw [WeierstrassCurve.map_preΨ]

    have hsepΨ : ((W.map π).preΨ (p ^ k)).Separable := by
      have hcast : ((p : ℤ) ^ k) = ((p ^ k : ℕ) : ℤ) := by push_cast; rfl
      rw [hcast, WeierstrassCurve.preΨ_ofNat]
      have hu : IsUnit (((p ^ k : ℕ) : T') * (W.map π).Δ) := by
        refine IsUnit.mul ?_ hΔ'
        rw [Nat.cast_pow]; exact hp'.pow k
      rcases Nat.even_or_odd (p ^ k) with hev | hodd
      · exact WeierstrassCurve.separable_prePsi_of_isUnit_of_even (W.map π) hev hu
      · exact WeierstrassCurve.separable_prePsi_of_isUnit (W.map π) hodd hu
    have hsepPΛ : (P.map π * Λ.map π).Separable := by rwa [hΛmap] at hsepΨ
    have hsep : (Λ.map π).Separable := Polynomial.Separable.of_dvd hsepPΛ (dvd_mul_left _ _)

    have hh'monic : h'.Monic := hh'.monic
    have hmul' : h' * P.map π ∣ P.map π * Λ.map π := by
      have := hh'.mul_preΨ_dvd
      rwa [hΛmap, hPmap] at this
    have hcopP' : IsCoprime h' (P.map π) := by
      obtain ⟨c, hc⟩ := hmul'
      have hs : (h' * (P.map π * c)).Separable := by rw [← mul_assoc, ← hc]; exact hsepPΛ
      exact (Polynomial.Separable.isCoprime hs).of_mul_right_left
    obtain ⟨g', hg'⟩ : h' ∣ Λ.map π :=
      hcopP'.dvd_of_dvd_mul_left ((dvd_mul_right h' (P.map π)).trans hmul')
    have hcop : IsCoprime h' g' := Polynomial.Separable.isCoprime (by rw [← hg']; exact hsep)
    have hh'deg : h'.natDegree = d := by
      refine le_antisymm hh'.natDegree_le ?_
      exact Polynomial.le_natDegree_of_ne_zero (by rw [hh'.coeff_eq_one]; exact one_ne_zero)

    obtain ⟨h, ⟨hhmonic, hhmap, hdvdΛ⟩, huniq⟩ :=
      Polynomial.existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot π hπ hnil Λ h' g' hh'monic hcop hg'
    obtain ⟨g, hfac⟩ := hdvdΛ
    have hgmap : g.map π = g' := by
      have h1 : h' * g.map π = h' * g' := by rw [← hg', ← hhmap, ← Polynomial.map_mul, ← hfac]
      exact hh'monic.isRegular.left h1
    have hhnat : h.natDegree = d := by
      rw [← hh'deg, ← hhmap]; exact (hhmonic.natDegree_map π).symm
    have hcopT : IsCoprime h g :=
      isCoprime_of_isCoprime_map π hπ hnil (by rw [hhmap, hgmap]; exact hcop)
    refine ⟨h, ⟨hhmap, ⟨hhnat.le, ?_, ?_, ?_⟩⟩, ?_⟩
    ·
      have := hhmonic.coeff_natDegree
      rwa [hhnat] at this
    ·
      exact ⟨g, by rw [hΛ, hfac, hP]; ring⟩
    ·
      intro a ha2 had hpa
      have haZ : ¬ ((p : ℤ) ∣ (a : ℤ)) := by
        intro hdvd; exact hpa (by exact_mod_cast hdvd)
      refine dvd_smulNumerator_of_isNilpotent_pow W k hpΔ hΛ hfac hcopT hhnat.le haZ ?_

      set S : T[X] := W.smulNumerator a d h with hS
      have hr : (S %ₘ h).map π = 0 := by
        rw [Polynomial.map_modByMonic _ hhmonic, hS, ← WeierstrassCurve.smulNumerator_map, hhmap,
          Polynomial.modByMonic_eq_zero_iff_dvd hh'monic]
        exact hh'.dvd_smulNumerator a ha2 had hpa
      have hrnil : IsNilpotent (S %ₘ h) := isNilpotent_poly_of_map_eq_zero π hnil hr
      have hmk : AdjoinRoot.mk h S = AdjoinRoot.mk h (S %ₘ h) := by
        rw [AdjoinRoot.mk_eq_mk]
        refine ⟨S /ₘ h, ?_⟩
        have := modByMonic_add_div S h
        linear_combination this.symm
      rw [hmk]
      exact hrnil.map (AdjoinRoot.mk h)
    ·
      rintro h₂ ⟨hh₂map, hh₂⟩
      have hm₂ : h₂.Monic := hh₂.monic
      have hcop₂ : IsCoprime h₂ P := by
        refine isCoprime_of_isCoprime_map π hπ hnil ?_
        rw [hh₂map]; exact hcopP'
      have hd₂ : h₂ ∣ Λ := by
        have h1 : h₂ ∣ P * Λ := by
          have := hh₂.mul_preΨ_dvd
          rw [hΛ] at this
          exact (dvd_mul_right h₂ _).trans this
        exact hcop₂.dvd_of_dvd_mul_left h1
      exact huniq h₂ ⟨hm₂, hh₂map, hd₂⟩

end S_ModularCurve_IsGamma0PowAt_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
end P2MW
export P2MW.S_ModularCurve_IsGamma0PowAt_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot (solution)
