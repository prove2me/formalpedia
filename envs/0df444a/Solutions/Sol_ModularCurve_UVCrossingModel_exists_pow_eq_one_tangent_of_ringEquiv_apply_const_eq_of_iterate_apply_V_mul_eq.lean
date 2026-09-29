-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a119e5c5-dd8e-5b9d-ab47-b79db76e5a17

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_isUnit_apply_V_eq_mul_V_of_ringEquiv_apply_const_eq_of_apply_U_not_mem_span
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_sub_const_mem_maximalIdeal
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Theorems.Thm_ModularCurve_UVCrossingModel_V_mem_nonZeroDivisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem solution
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    [IsLocalRing (UVCrossingModel W (ϖ ^ e))]
    (θ : UVCrossingModel W (ϖ ^ e) ≃+* UVCrossingModel W (ϖ ^ e))
    (hθc : ∀ w : W, θ (const (ϖ ^ e) w) = const (ϖ ^ e) w)
    (hθU : θ (U (ϖ ^ e)) ∉ Ideal.span {V (ϖ ^ e), const (ϖ ^ e) ϖ})
    (n : ℕ) (hn : 1 ≤ n) (hnW : IsUnit ((n : ℕ) : W))
    (β : UVCrossingModel W (ϖ ^ e)) (hβ : IsUnit β)

    (hfix : (θ ^ n) (V (ϖ ^ e) * β) = V (ϖ ^ e) * β)

    (c : ℕ → W)
    (hread : ∀ k : ℕ, 0 < k → k < n →
      (θ ^ k) (V (ϖ ^ e) * β) - const (ϖ ^ e) (c k) * (V (ϖ ^ e) * β) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2)
    (hfaith : ∀ k : ℕ, 0 < k → k < n → c k - 1 ∉ maximalIdeal W) :
    ∃ ζ ζ' : W, ζ ^ n = 1 ∧ (∀ k : ℕ, 0 < k → k < n → IsUnit (ζ ^ k - 1)) ∧ ζ * ζ' = 1 ∧
      θ (U (ϖ ^ e)) - const (ϖ ^ e) ζ * U (ϖ ^ e) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2 ∧
      θ (V (ϖ ^ e)) - const (ϖ ^ e) ζ' * V (ϖ ^ e) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2 ∧
      (∀ c' : W, θ (V (ϖ ^ e) * β) - const (ϖ ^ e) c' * (V (ϖ ^ e) * β) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2 →
        ζ' - c' ∈ maximalIdeal W) := by
  classical

  have hϖnu : ¬ IsUnit ϖ := hϖ.not_isUnit
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hmaxW : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hπnu : ¬ IsUnit (ϖ ^ e) := fun h => hϖnu ((isUnit_pow_iff (by omega)).mp h)
  have hπnzd : ϖ ^ e ∈ nonZeroDivisors W := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ0)
  have hVnzd : V (ϖ ^ e) ∈ nonZeroDivisors (UVCrossingModel W (ϖ ^ e)) := ModularCurve.UVCrossingModel.V_mem_nonZeroDivisors hπnzd
  have hVcancel : ∀ x : UVCrossingModel W (ϖ ^ e), x * V (ϖ ^ e) = 0 → x = 0 := fun x hx => (mem_nonZeroDivisors_iff.mp hVnzd).2 x hx
  have hUV : U (ϖ ^ e) * V (ϖ ^ e) = const (ϖ ^ e) (ϖ ^ e) := ModularCurve.UVCrossingModel.U_mul_V _
  have hconstHom : ∀ w : W, const (ϖ ^ e) w = constHom (ϖ ^ e) w := fun w => rfl
  have hconst_mul : ∀ a b : W, const (ϖ ^ e) (a * b) = const (ϖ ^ e) a * const (ϖ ^ e) b := by
    intro a b; rw [hconstHom, hconstHom, hconstHom, map_mul]
  have hconst_sub : ∀ a b : W, const (ϖ ^ e) (a - b) = const (ϖ ^ e) a - const (ϖ ^ e) b := by
    intro a b; rw [hconstHom, hconstHom, hconstHom, map_sub]
  have hconst_one : const (ϖ ^ e) (1 : W) = 1 := by rw [hconstHom, map_one]
  have hconst_pow : ∀ (a : W) (k : ℕ), const (ϖ ^ e) (a ^ k) = const (ϖ ^ e) a ^ k := by
    intro a k; rw [hconstHom, hconstHom, map_pow]

  obtain ⟨eU, heV, heU, heC⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries (W := W) (ϖ ^ e)
  have hle : Ideal.span {ϖ ^ e} ≤ maximalIdeal W := by
    rw [Ideal.span_singleton_le_iff_mem]; exact (IsLocalRing.mem_maximalIdeal _).mpr hπnu
  let red : (W ⧸ Ideal.span {ϖ ^ e}) →+* ResidueField W :=
    Ideal.Quotient.lift (Ideal.span {ϖ ^ e}) (IsLocalRing.residue W) (fun a ha => by
      rw [IsLocalRing.residue_eq_zero_iff]; exact hle ha)
  let ρ : UVCrossingModel W (ϖ ^ e) →+* PowerSeries (ResidueField W) :=
    (PowerSeries.map red).comp (((eU : (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {U (ϖ ^ e)}) ≃+* PowerSeries (W ⧸ Ideal.span {ϖ ^ e})) :
        (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {U (ϖ ^ e)}) →+* PowerSeries (W ⧸ Ideal.span {ϖ ^ e})).comp
      (Ideal.Quotient.mk (Ideal.span {U (ϖ ^ e)})))
  have hρV : ρ (V (ϖ ^ e)) = PowerSeries.X := by
    show PowerSeries.map red (eU (Ideal.Quotient.mk _ (V (ϖ ^ e)))) = PowerSeries.X
    rw [heV, PowerSeries.map_X]
  have hρU : ρ (U (ϖ ^ e)) = 0 := by
    show PowerSeries.map red (eU (Ideal.Quotient.mk _ (U (ϖ ^ e)))) = 0
    rw [heU, map_zero]
  have hρc : ∀ w : W, ρ (const (ϖ ^ e) w) = PowerSeries.C (IsLocalRing.residue W w) := by
    intro w
    show PowerSeries.map red (eU (Ideal.Quotient.mk _ (const (ϖ ^ e) w))) = _
    rw [heC, PowerSeries.map_C]
    rfl
  have hρsurj : Function.Surjective ρ := by
    have h1 : Function.Surjective red := by
      intro x
      obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective x
      exact ⟨Ideal.Quotient.mk _ w, rfl⟩
    exact (PowerSeries.map_surjective red h1).comp (eU.surjective.comp Ideal.Quotient.mk_surjective)
  have hXmax : (PowerSeries.X : PowerSeries (ResidueField W)) ∈ maximalIdeal (PowerSeries (ResidueField W)) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; exact Ideal.mem_span_singleton_self _

  have hVnu : ¬ IsUnit (V (ϖ ^ e)) := by
    intro h
    have := h.map ρ
    rw [hρV] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp hXmax this
  have hV𝔪 : V (ϖ ^ e) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := (IsLocalRing.mem_maximalIdeal _).mpr hVnu
  have hUnu : ¬ IsUnit (U (ϖ ^ e)) := by
    intro h
    have := h.map ρ
    rw [hρU] at this
    exact not_isUnit_zero this
  have hU𝔪 : U (ϖ ^ e) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := (IsLocalRing.mem_maximalIdeal _).mpr hUnu
  have hcϖnu : ¬ IsUnit (const (ϖ ^ e) ϖ) := by
    intro h
    have h2 : IsUnit (const (ϖ ^ e) ϖ ^ e) := h.pow e
    rw [← hconst_pow, ← hUV] at h2
    exact hUnu (isUnit_of_mul_isUnit_left h2)

  have hconst𝔪 : ∀ w : W, const (ϖ ^ e) w ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) ↔ w ∈ maximalIdeal W := by
    intro w
    constructor
    · intro hw
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hw ⊢
      intro hu; exact hw (by rw [hconstHom]; exact hu.map _)
    · intro hw
      rw [hmaxW, Ideal.mem_span_singleton] at hw
      obtain ⟨d, rfl⟩ := hw
      rw [hconst_mul]
      exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hcϖnu)

  have hρmax : ∀ x : UVCrossingModel W (ϖ ^ e), x ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) → ρ x ∈ Ideal.span {(PowerSeries.X : PowerSeries (ResidueField W))} := by
    intro x hx
    rw [← PowerSeries.maximalIdeal_eq_span_X]
    by_contra hρx
    have hu : IsUnit (ρ x) := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hρx
    obtain ⟨y, hy⟩ := hρsurj ((hu.unit⁻¹ : (PowerSeries (ResidueField W))ˣ) : PowerSeries (ResidueField W))
    have h1 : ρ (1 - x * y) = 0 := by
      rw [map_sub, map_one, map_mul, hy, IsUnit.mul_val_inv, sub_self]
    have h2 : (1 - x * y) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu'
      have := hu'.map ρ
      rw [h1] at this
      exact not_isUnit_zero this
    have h3 : (1 : UVCrossingModel W (ϖ ^ e)) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := by
      have : (1 : UVCrossingModel W (ϖ ^ e)) = (1 - x * y) + x * y := by ring
      rw [this]; exact add_mem h2 (Ideal.mul_mem_right _ _ hx)
    exact (IsLocalRing.maximalIdeal.isMaximal (UVCrossingModel W (ϖ ^ e))).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have hρsq : ∀ x : UVCrossingModel W (ϖ ^ e), x ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ 2 →
      ρ x ∈ Ideal.span {(PowerSeries.X : PowerSeries (ResidueField W)) ^ 2} := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [map_mul, pow_two, ← Ideal.span_singleton_mul_span_singleton]
      exact Ideal.mul_mem_mul (hρmax a ha) (hρmax b hb)
    · intro a b ha hb
      rw [map_add]; exact add_mem ha hb

  have hKEY : ∀ d : W, const (ϖ ^ e) d * V (ϖ ^ e) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ 2 → d ∈ maximalIdeal W := by
    intro d hd
    have h1 := hρsq _ hd
    rw [map_mul, hρc, hρV, Ideal.mem_span_singleton] at h1
    have h2 := (PowerSeries.X_pow_dvd_iff.mp h1) 1 (by norm_num)
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_one_X, mul_one] at h2
    exact (IsLocalRing.residue_eq_zero_iff _).mp h2

  have hθmax : ∀ (g : UVCrossingModel W (ϖ ^ e) ≃+* UVCrossingModel W (ϖ ^ e)) (x : UVCrossingModel W (ϖ ^ e)), x ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) → g x ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := by
    intro g x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu; apply hx
    have := hu.map g.symm
    rwa [RingEquiv.symm_apply_apply] at this
  have hpow_succ : ∀ (k : ℕ) (x : UVCrossingModel W (ϖ ^ e)), (θ ^ (k + 1)) x = θ ((θ ^ k) x) := by
    intro k x; rw [pow_succ']; rfl
  have hθkc : ∀ (k : ℕ) (w : W), (θ ^ k) (const (ϖ ^ e) w) = const (ϖ ^ e) w := by
    intro k w
    induction k with
    | zero => rfl
    | succ k ih => rw [hpow_succ, ih, hθc]
  have hθid : ∀ (k : ℕ) (x : UVCrossingModel W (ϖ ^ e)), (θ ^ k) x - x ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := by
    intro k x
    obtain ⟨w, hw⟩ := ModularCurve.UVCrossingModel.exists_sub_const_mem_maximalIdeal hπnu x
    have : (θ ^ k) x - x = (θ ^ k) (x - const (ϖ ^ e) w) - (x - const (ϖ ^ e) w) := by
      rw [map_sub, hθkc]; ring
    rw [this]
    exact sub_mem (hθmax _ _ hw) hw

  obtain ⟨t, ht, hθV⟩ := ModularCurve.UVCrossingModel.exists_isUnit_apply_V_eq_mul_V_of_ringEquiv_apply_const_eq_of_apply_U_not_mem_span
    W ϖ hϖ e he θ (hθc ϖ) hθU
  obtain ⟨lam, hlam⟩ := ModularCurve.UVCrossingModel.exists_sub_const_mem_maximalIdeal hπnu t

  have hiter : ∀ k : ℕ, ∃ s : UVCrossingModel W (ϖ ^ e), (θ ^ k) (V (ϖ ^ e)) = s * V (ϖ ^ e) ∧ s - const (ϖ ^ e) (lam ^ k) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨1, ?_, ?_⟩
      · rw [pow_zero, one_mul]; rfl
      · rw [pow_zero, hconst_one, sub_self]; exact zero_mem _
    | succ k ih =>
      obtain ⟨s, hs, hsl⟩ := ih
      refine ⟨θ s * t, ?_, ?_⟩
      · rw [hpow_succ, hs, map_mul, hθV]; ring
      · have : θ s * t - const (ϖ ^ e) (lam ^ (k + 1)) =
            (θ s - s) * t + (s - const (ϖ ^ e) (lam ^ k)) * t + const (ϖ ^ e) (lam ^ k) * (t - const (ϖ ^ e) lam) := by
          rw [pow_succ, hconst_mul]; ring
        rw [this]
        refine add_mem (add_mem (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_right _ _ hsl)) (Ideal.mul_mem_left _ _ hlam)
        have := hθid 1 s
        rwa [pow_one] at this

  obtain ⟨βu, rfl⟩ := hβ
  have hREAD : ∀ (k : ℕ) (c' : W),
      (θ ^ k) (V (ϖ ^ e) * (βu : UVCrossingModel W (ϖ ^ e))) - const (ϖ ^ e) c' * (V (ϖ ^ e) * (βu : UVCrossingModel W (ϖ ^ e))) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ 2 →
      lam ^ k - c' ∈ maximalIdeal W := by
    intro k c' hk
    obtain ⟨s, hs, hsl⟩ := hiter k
    apply hKEY
    have hE : (s - const (ϖ ^ e) (lam ^ k)) * (θ ^ k) (βu : UVCrossingModel W (ϖ ^ e)) +
        const (ϖ ^ e) (lam ^ k) * ((θ ^ k) (βu : UVCrossingModel W (ϖ ^ e)) - (βu : UVCrossingModel W (ϖ ^ e))) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) :=
      add_mem (Ideal.mul_mem_right _ _ hsl) (Ideal.mul_mem_left _ _ (hθid k _))
    have eq1 : const (ϖ ^ e) (lam ^ k - c') * V (ϖ ^ e) * (βu : UVCrossingModel W (ϖ ^ e)) =
        ((θ ^ k) (V (ϖ ^ e) * (βu : UVCrossingModel W (ϖ ^ e))) - const (ϖ ^ e) c' * (V (ϖ ^ e) * (βu : UVCrossingModel W (ϖ ^ e)))) -
          ((s - const (ϖ ^ e) (lam ^ k)) * (θ ^ k) (βu : UVCrossingModel W (ϖ ^ e)) +
            const (ϖ ^ e) (lam ^ k) * ((θ ^ k) (βu : UVCrossingModel W (ϖ ^ e)) - (βu : UVCrossingModel W (ϖ ^ e)))) * V (ϖ ^ e) := by
      rw [map_mul, hs, hconst_sub]; ring
    have hmem : const (ϖ ^ e) (lam ^ k - c') * V (ϖ ^ e) * (βu : UVCrossingModel W (ϖ ^ e)) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ 2 := by
      rw [eq1]
      refine sub_mem hk ?_
      rw [pow_two]; exact Ideal.mul_mem_mul hE hV𝔪
    rw [← Units.mul_inv_cancel_right (const (ϖ ^ e) (lam ^ k - c') * V (ϖ ^ e)) βu]
    exact Ideal.mul_mem_right _ _ hmem

  have hlamn : lam ^ n - 1 ∈ maximalIdeal W := by
    obtain ⟨s, hs, hsl⟩ := hiter n
    have h1 : (s * (θ ^ n) (βu : UVCrossingModel W (ϖ ^ e)) - (βu : UVCrossingModel W (ϖ ^ e))) * V (ϖ ^ e) = 0 := by
      have h0 := hfix
      rw [map_mul, hs] at h0
      rw [sub_mul, sub_eq_zero]
      calc s * (θ ^ n) (βu : UVCrossingModel W (ϖ ^ e)) * V (ϖ ^ e) = s * V (ϖ ^ e) * (θ ^ n) (βu : UVCrossingModel W (ϖ ^ e)) := by ring
        _ = V (ϖ ^ e) * (βu : UVCrossingModel W (ϖ ^ e)) := h0
        _ = (βu : UVCrossingModel W (ϖ ^ e)) * V (ϖ ^ e) := by ring
    have h2 := hVcancel _ h1
    rw [← hconst𝔪, hconst_sub, hconst_one]
    have e3 : (const (ϖ ^ e) (lam ^ n) - 1) * (βu : UVCrossingModel W (ϖ ^ e)) =
        (const (ϖ ^ e) (lam ^ n) - s) * (θ ^ n) (βu : UVCrossingModel W (ϖ ^ e)) - const (ϖ ^ e) (lam ^ n) * ((θ ^ n) (βu : UVCrossingModel W (ϖ ^ e)) - (βu : UVCrossingModel W (ϖ ^ e)))
          + (s * (θ ^ n) (βu : UVCrossingModel W (ϖ ^ e)) - (βu : UVCrossingModel W (ϖ ^ e))) := by ring
    rw [← Ideal.mul_unit_mem_iff_mem _ (Units.isUnit βu), e3, h2, add_zero]
    refine sub_mem (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ (hθid n _))
    have := neg_mem hsl
    rwa [neg_sub] at this
  have hlamu : IsUnit lam := by
    by_contra hu
    have hl : lam ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hu
    have hln : lam ^ n ∈ maximalIdeal W := Ideal.pow_mem_of_mem _ hl n (by omega)
    have : (1 : W) ∈ maximalIdeal W := by
      have := sub_mem hln hlamn
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hlamk : ∀ k : ℕ, 0 < k → k < n → lam ^ k - 1 ∉ maximalIdeal W := by
    intro k hk hkn hmem
    have h1 : lam ^ k - c k ∈ maximalIdeal W := hREAD k (c k) (hread k hk hkn)
    apply hfaith k hk hkn
    have : c k - 1 = (lam ^ k - 1) - (lam ^ k - c k) := by ring
    rw [this]; exact sub_mem hmem h1

  have hn0 : n ≠ 0 := by omega
  have hmonic : (Polynomial.X ^ n - 1 : Polynomial W).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : W) hn0
  have heval : (Polynomial.X ^ n - 1 : Polynomial W).eval lam ∈ maximalIdeal W := by
    simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] using hlamn
  have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal W) ((Polynomial.X ^ n - 1 : Polynomial W).derivative.eval lam)) := by
    have hd : (Polynomial.X ^ n - 1 : Polynomial W).derivative.eval lam = (n : W) * lam ^ (n - 1) := by
      simp [Polynomial.derivative_X_pow]
    rw [hd]
    exact (hnW.mul (hlamu.pow _)).map _
  obtain ⟨ζ', hζ'root, hζ'lam⟩ := HenselianRing.is_henselian (R := W) (I := maximalIdeal W)
    (Polynomial.X ^ n - 1) hmonic lam heval hderiv
  have hζ'n : ζ' ^ n = 1 := by
    have h := hζ'root
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, sub_eq_zero] at h
    exact h
  have hζ'k : ∀ k : ℕ, ζ' ^ k - lam ^ k ∈ maximalIdeal W := fun k =>
    Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow ζ' lam k) hζ'lam

  set ζ : W := ζ' ^ (n - 1) with hζdef
  have hζζ' : ζ * ζ' = 1 := by
    rw [hζdef, ← pow_succ, Nat.sub_add_cancel hn, hζ'n]

  obtain ⟨tu, rfl⟩ := ht
  have hθUt : θ (U (ϖ ^ e)) * (tu : UVCrossingModel W (ϖ ^ e)) = U (ϖ ^ e) := by
    have h0 : θ (U (ϖ ^ e)) * θ (V (ϖ ^ e)) = U (ϖ ^ e) * V (ϖ ^ e) := by
      rw [← map_mul, hUV, hθc]
    rw [hθV] at h0
    apply sub_eq_zero.mp
    apply hVcancel
    rw [sub_mul, sub_eq_zero, mul_assoc]
    exact h0
  have hθU' : θ (U (ϖ ^ e)) = U (ϖ ^ e) * ((tu⁻¹ : (UVCrossingModel W (ϖ ^ e))ˣ) : UVCrossingModel W (ϖ ^ e)) :=
    (Units.eq_mul_inv_iff_mul_eq tu).mpr hθUt

  have htζ' : (tu : UVCrossingModel W (ϖ ^ e)) - const (ϖ ^ e) ζ' ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := by
    have : (tu : UVCrossingModel W (ϖ ^ e)) - const (ϖ ^ e) ζ' = ((tu : UVCrossingModel W (ϖ ^ e)) - const (ϖ ^ e) lam) + const (ϖ ^ e) (lam - ζ') := by
      rw [hconst_sub]; ring
    rw [this]
    refine add_mem hlam ((hconst𝔪 _).mpr ?_)
    have := neg_mem hζ'lam
    rwa [neg_sub] at this
  have htinvζ : ((tu⁻¹ : (UVCrossingModel W (ϖ ^ e))ˣ) : UVCrossingModel W (ϖ ^ e)) - const (ϖ ^ e) ζ ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := by
    have e1 : ((tu⁻¹ : (UVCrossingModel W (ϖ ^ e))ˣ) : UVCrossingModel W (ϖ ^ e)) - const (ϖ ^ e) ζ =
        ((tu⁻¹ : (UVCrossingModel W (ϖ ^ e))ˣ) : UVCrossingModel W (ϖ ^ e)) * (const (ϖ ^ e) ζ' * const (ϖ ^ e) ζ - (tu : UVCrossingModel W (ϖ ^ e)) * const (ϖ ^ e) ζ) := by
      rw [← hconst_mul, mul_comm ζ' ζ, hζζ', hconst_one, mul_sub, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e1]
    refine Ideal.mul_mem_left _ _ ?_
    rw [← sub_mul]
    refine Ideal.mul_mem_right _ _ ?_
    have := neg_mem htζ'
    rwa [neg_sub] at this
  refine ⟨ζ, ζ', ?_, ?_, hζζ', ?_, ?_, ?_⟩
  ·
    rw [hζdef, ← pow_mul, mul_comm, pow_mul, hζ'n, one_pow]
  ·
    intro k hk hkn
    have hprod : ζ ^ k * ζ' ^ k = 1 := by rw [← mul_pow, hζζ', one_pow]
    have hζku : IsUnit (ζ ^ k) := isUnit_iff_exists_inv.mpr ⟨_, hprod⟩
    have e1 : ζ ^ k - 1 = -(ζ ^ k * (ζ' ^ k - 1)) := by rw [mul_sub, hprod]; ring
    rw [e1, IsUnit.neg_iff]
    refine hζku.mul ?_
    by_contra hnu
    have h1 : ζ' ^ k - 1 ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    apply hlamk k hk hkn
    have : lam ^ k - 1 = (ζ' ^ k - 1) - (ζ' ^ k - lam ^ k) := by ring
    rw [this]; exact sub_mem h1 (hζ'k k)
  ·
    rw [hθU', mul_comm, ← sub_mul, pow_two]
    exact Ideal.mul_mem_mul htinvζ hU𝔪
  ·
    rw [hθV, ← sub_mul, pow_two]
    exact Ideal.mul_mem_mul htζ' hV𝔪
  ·
    intro c' hc'
    have h1 : lam ^ 1 - c' ∈ maximalIdeal W := hREAD 1 c' (by rwa [pow_one])
    rw [pow_one] at h1
    have : ζ' - c' = (ζ' - lam) + (lam - c') := by ring
    rw [this]; exact add_mem hζ'lam h1

end S_ModularCurve_UVCrossingModel_exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq (solution)
