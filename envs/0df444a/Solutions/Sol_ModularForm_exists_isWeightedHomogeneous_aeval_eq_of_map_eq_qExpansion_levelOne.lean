-- Prove2me | solution 1 for ModularForm.exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b504b35a-0520-54fa-b7ea-f757a1a32818

import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Theorems.Thm_ModularCurve_qExpansion_E6_eq_map_mk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "UpperHalfPlane ModularForm P2MW.S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne.ModularForm ModularFormClass"

namespace ModularForm
p2m_export "ModularForm" "levelOne_odd_weight_eq_zero mk sub_apply pow IsGLPos.coe_smul coe_smul levelOne_weight_two_rank_zero toCuspForm discriminant_eq_E₄_cube_sub_E₆_sq one_coe_eq_one discriminant add ext smul_apply E₄ mcast qExpansion_eq_qExpansion_discriminant_mul E₆ coe_mcast coe_pow mul coe_sub"
namespace RationalLevelOneProof
p2m_open "ModularForm"

noncomputable section

def e4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3

def e6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

def e4Q : PowerSeries ℚ := e4.map (Int.castRingHom ℚ)

def e6Q : PowerSeries ℚ := e6.map (Int.castRingHom ℚ)

def dQ : PowerSeries ℚ := PowerSeries.C (1728⁻¹ : ℚ) * (e4Q ^ 3 - e6Q ^ 2)

local notation "ι" => algebraMap ℚ ℂ

lemma map_ι_injective : Function.Injective (PowerSeries.map ι) :=
  PowerSeries.map_injective _ (algebraMap ℚ ℂ).injective

lemma map_map_Q (D : PowerSeries ℤ) :
    (D.map (Int.castRingHom ℚ)).map ι = D.map (Int.castRingHom ℂ) := by
  have hc : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [← hc, PowerSeries.map_comp]; rfl

lemma qExpansion_E4 : qExpansion 1 ⇑ModularForm.E₄ = e4Q.map ι := by
  rw [e4Q, map_map_Q]; exact ModularCurve.qExpansion_E4_eq_map_eisenstein4

lemma qExpansion_E6 : qExpansion 1 ⇑ModularForm.E₆ = e6Q.map ι := by
  rw [e6Q, map_map_Q]; exact ModularCurve.qExpansion_E6_eq_map_mk

def G12 : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

lemma coe_G12 : ⇑G12 = fun z => E₄ z ^ 3 - E₆ z ^ 2 := by
  ext z
  simp only [G12, coe_mcast, coe_pow, sub_apply, Pi.pow_apply]

lemma qExpansion_G12 :
    qExpansion 1 ⇑G12 = qExpansion 1 ⇑E₄ ^ 3 - qExpansion 1 ⇑E₆ ^ 2 := by
  unfold G12
  rw [coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mcast, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

lemma coe_G12_eq_smul : ⇑G12 = ⇑((1728 : ℂ) • CuspForm.discriminant) := by
  rw [coe_G12, CuspForm.IsGLPos.coe_smul, CuspForm.coe_discriminant]
  ext z
  rw [Pi.smul_apply, discriminant_eq_E₄_cube_sub_E₆_sq, smul_eq_mul]
  field_simp

lemma qExpansion_discriminant :
    qExpansion 1 ModularForm.discriminant = dQ.map ι := by
  have h1 : (1728 : ℂ) • qExpansion 1 ModularForm.discriminant =
      qExpansion 1 ⇑E₄ ^ 3 - qExpansion 1 ⇑E₆ ^ 2 := by
    rw [← CuspForm.coe_discriminant,
      ← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      ← CuspForm.IsGLPos.coe_smul, ← coe_G12_eq_smul, qExpansion_G12]
  have h2 : qExpansion 1 ModularForm.discriminant =
      (1728 : ℂ)⁻¹ • (qExpansion 1 ⇑E₄ ^ 3 - qExpansion 1 ⇑E₆ ^ 2) := by
    rw [← h1, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  rw [h2, qExpansion_E4, qExpansion_E6, dQ, map_mul, PowerSeries.map_C, map_sub, map_pow, map_pow]
  ext n
  simp [PowerSeries.coeff_C_mul]

lemma coeff_zero_e4Q : PowerSeries.coeff 0 e4Q = 1 := by
  simp [e4Q, e4, PowerSeries.coeff_mk]

lemma coeff_zero_e6Q : PowerSeries.coeff 0 e6Q = 1 := by
  simp [e6Q, e6, PowerSeries.coeff_mk]

lemma coeff_one_e4Q : PowerSeries.coeff 1 e4Q = 240 := by
  simp [e4Q, e4, PowerSeries.coeff_mk]

lemma coeff_one_e6Q : PowerSeries.coeff 1 e6Q = -504 := by
  simp [e6Q, e6, PowerSeries.coeff_mk]

lemma constantCoeff_e4Q : PowerSeries.constantCoeff e4Q = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_e4Q

lemma constantCoeff_e6Q : PowerSeries.constantCoeff e6Q = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_e6Q

lemma constantCoeff_dQ : PowerSeries.constantCoeff dQ = 0 := by
  simp [dQ, constantCoeff_e4Q, constantCoeff_e6Q]

lemma coeff_one_dQ : PowerSeries.coeff 1 dQ = 1 := by
  have h3 : e4Q ^ 3 = e4Q * e4Q * e4Q := by ring
  have h2 : e6Q ^ 2 = e6Q * e6Q := by ring
  rw [dQ, PowerSeries.coeff_C_mul, map_sub, h3, h2]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, coeff_zero_e4Q, coeff_one_e4Q,
    coeff_zero_e6Q, coeff_one_e6Q]

def dQ' : PowerSeries ℚ := (PowerSeries.X_dvd_iff.mpr constantCoeff_dQ).choose

lemma dQ_eq : dQ = PowerSeries.X * dQ' := (PowerSeries.X_dvd_iff.mpr constantCoeff_dQ).choose_spec

lemma constantCoeff_dQ' : PowerSeries.constantCoeff dQ' = 1 := by
  have h := coeff_one_dQ
  rw [dQ_eq, ← pow_one PowerSeries.X, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  exact h

def dQ'inv : PowerSeries ℚ := dQ'.invOfUnit 1

lemma dQ'_mul_inv : dQ' * dQ'inv = 1 :=
  PowerSeries.mul_invOfUnit dQ' 1 (by rw [constantCoeff_dQ']; rfl)

section Poly

local notation "𝔴" => (![4, 6] : Fin 2 → ℕ)

lemma iso_monomial (r : ℚ) (a b : ℕ) :
    (MvPolynomial.C r * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) :
      MvPolynomial (Fin 2) ℚ).IsWeightedHomogeneous 𝔴 (4 * a + 6 * b) := by
  have h0 := (MvPolynomial.isWeightedHomogeneous_X ℚ 𝔴 (0 : Fin 2)).pow a
  have h1 := (MvPolynomial.isWeightedHomogeneous_X ℚ 𝔴 (1 : Fin 2)).pow b
  have h := (h0.mul h1).C_mul r
  convert h using 1
  simp [smul_eq_mul, mul_comm]

lemma iso_delta :
    (MvPolynomial.C ((1728 : ℚ)⁻¹) * (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2) :
      MvPolynomial (Fin 2) ℚ).IsWeightedHomogeneous 𝔴 12 := by
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  have h0 := (MvPolynomial.isWeightedHomogeneous_X ℚ 𝔴 (0 : Fin 2)).pow 3
  have h1 := (MvPolynomial.isWeightedHomogeneous_X ℚ 𝔴 (1 : Fin 2)).pow 2
  have h0' : (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) ℚ).IsWeightedHomogeneous 𝔴 12 := by
    convert h0 using 1
    rfl
  have h1' : (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) ℚ).IsWeightedHomogeneous 𝔴 12 := by
    convert h1 using 1
    rfl
  rw [← MvPolynomial.mem_weightedHomogeneousSubmodule] at h0' h1' ⊢
  exact Submodule.sub_mem _ h0' h1'

end Poly

section Main

local notation "𝔴" => (![4, 6] : Fin 2 → ℕ)

def ev : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] PowerSeries ℚ := MvPolynomial.aeval ![e4Q, e6Q]

lemma ev_X0 : ev (MvPolynomial.X 0) = e4Q := by simp [ev]

lemma ev_X1 : ev (MvPolynomial.X 1) = e6Q := by simp [ev]

lemma ev_C (r : ℚ) : ev (MvPolynomial.C r) = PowerSeries.C r := by simp [ev]

lemma ev_monomial (t : ℚ) (a b : ℕ) :
    ev (MvPolynomial.C t * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) =
      PowerSeries.C t * (e4Q ^ a * e6Q ^ b) := by
  rw [map_mul, map_mul, map_pow, map_pow, ev_C, ev_X0, ev_X1]

lemma ev_delta :
    ev (MvPolynomial.C ((1728 : ℚ)⁻¹) * (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)) = dQ := by
  rw [map_mul, map_sub, map_pow, map_pow, ev_C, ev_X0, ev_X1, dQ]

def Claim (k : ℕ) : Prop :=
  ∀ (f : ModularForm 𝒮ℒ (k : ℤ)) (T : PowerSeries ℚ), T.map ι = qExpansion 1 ⇑f →
    ∃ Φ : MvPolynomial (Fin 2) ℚ, Φ.IsWeightedHomogeneous 𝔴 k ∧ ev Φ = T

lemma eq_zero_of_coe_eq_zero {k : ℤ} {f : ModularForm 𝒮ℒ k} (hf : ⇑f = 0) {T : PowerSeries ℚ}
    (hT : T.map ι = qExpansion 1 ⇑f) : T = 0 := by
  apply map_ι_injective
  rw [hT, hf, qExpansion_zero, map_zero]

lemma claim_of_coe_zero {k : ℕ} {f : ModularForm 𝒮ℒ (k : ℤ)} (hf : ⇑f = 0)
    {T : PowerSeries ℚ} (hT : T.map ι = qExpansion 1 ⇑f) :
    ∃ Φ : MvPolynomial (Fin 2) ℚ, Φ.IsWeightedHomogeneous 𝔴 k ∧ ev Φ = T :=
  ⟨0, MvPolynomial.isWeightedHomogeneous_zero _ _ _, by
    rw [eq_zero_of_coe_eq_zero hf hT, map_zero]⟩

lemma claim_zero : Claim 0 := by
  intro f T hT
  obtain ⟨c, hc⟩ := levelOne_weight_zero_const f
  have hq : qExpansion 1 ⇑f = PowerSeries.C c := by
    have h1 : ⇑f = c • ⇑(1 : ModularForm 𝒮ℒ 0) := by
      rw [hc, one_coe_eq_one]; ext z; simp
    have h2 : qExpansion 1 ⇑f = c • qExpansion 1 ⇑(1 : ModularForm 𝒮ℒ 0) := by
      rw [h1]; exact ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c _
    rw [h2, ModularForm.qExpansion_one, PowerSeries.smul_eq_C_mul, mul_one]
  rw [hq] at hT
  have hT' : T = PowerSeries.C (PowerSeries.constantCoeff T) := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h := congrArg (PowerSeries.coeff n) hT
      rw [PowerSeries.coeff_map, PowerSeries.coeff_C, if_neg hn.ne'] at h
      rw [PowerSeries.coeff_C, if_neg hn.ne']
      exact (algebraMap ℚ ℂ).injective (by rw [h, map_zero])
  refine ⟨MvPolynomial.C (PowerSeries.constantCoeff T), MvPolynomial.isWeightedHomogeneous_C _ _, ?_⟩
  rw [ev_C, ← hT']

lemma claim_two : Claim 2 := by
  intro f T hT
  have hf : f = 0 := rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero f
  exact claim_of_coe_zero (by rw [hf]; rfl) hT

lemma claim_odd {k : ℕ} (hk : Odd k) : Claim k := by
  intro f T hT
  have hf : f = 0 := levelOne_odd_weight_eq_zero (by exact_mod_cast hk) f
  exact claim_of_coe_zero (by rw [hf]; rfl) hT

lemma claim_step {k : ℕ} (hk4 : 4 ≤ k) {a b : ℕ} (hab : 4 * a + 6 * b = k)
    (ih : 12 ≤ k → Claim (k - 12)) : Claim k := by
  intro f T hT

  let g : ModularForm 𝒮ℒ (k : ℤ) := ModularForm.mcast (by omega) ((E₄.pow a).mul (E₆.pow b))
  have hg : qExpansion 1 ⇑g = PowerSeries.map ι (e4Q ^ a * e6Q ^ b) := by
    simp only [g, ModularForm.qExpansion_mcast]
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, qExpansion_E4, qExpansion_E6,
      map_mul, map_pow, map_pow]
  set t₀ : ℚ := PowerSeries.constantCoeff T with ht₀

  let f₁ : ModularForm 𝒮ℒ (k : ℤ) := f - (ι t₀) • g
  set T₁ : PowerSeries ℚ := T - PowerSeries.C t₀ * (e4Q ^ a * e6Q ^ b) with hT₁def
  have hT₁ : PowerSeries.map ι T₁ = qExpansion 1 ⇑f₁ := by
    have e : ⇑f₁ = ⇑f - ⇑((ι t₀) • g) := rfl
    rw [e, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL f ((ι t₀) • g),
      ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hg,
      ← hT, hT₁def, map_sub, map_mul, PowerSeries.map_C, PowerSeries.smul_eq_C_mul]
  have hT₁0 : PowerSeries.constantCoeff T₁ = 0 := by
    simp [hT₁def, ht₀, constantCoeff_e4Q, constantCoeff_e6Q]
  have hcusp : PowerSeries.coeff 0 (qExpansion 1 ⇑f₁) = 0 := by
    rw [← hT₁, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hT₁0, map_zero]

  set h : ModularForm 𝒮ℒ ((k : ℤ) - 12) := CuspForm.discriminantEquiv (toCuspForm f₁ hcusp) with hh
  have hfac : qExpansion 1 ⇑f₁ = qExpansion 1 ModularForm.discriminant * qExpansion 1 ⇑h :=
    qExpansion_eq_qExpansion_discriminant_mul f₁ hcusp
  by_cases hk12 : 12 ≤ k
  ·
    obtain ⟨T₁', hT₁'⟩ := PowerSeries.X_dvd_iff.mpr hT₁0
    set T₂ : PowerSeries ℚ := dQ'inv * T₁' with hT₂
    have hT₂q : PowerSeries.map ι T₂ = qExpansion 1 ⇑h := by
      have e1 : PowerSeries.map ι PowerSeries.X * PowerSeries.map ι T₁' =
          PowerSeries.map ι PowerSeries.X * (PowerSeries.map ι dQ' * qExpansion 1 ⇑h) := by
        rw [← map_mul, ← hT₁', hT₁, hfac, qExpansion_discriminant, dQ_eq, map_mul, mul_assoc]
      rw [PowerSeries.map_X] at e1
      have e2 := mul_left_cancel₀ PowerSeries.X_ne_zero e1
      rw [hT₂, map_mul, e2, ← mul_assoc, ← map_mul, mul_comm dQ'inv, dQ'_mul_inv, map_one, one_mul]

    let h' : ModularForm 𝒮ℒ ((k - 12 : ℕ) : ℤ) := ModularForm.mcast (by omega) h
    have hh' : qExpansion 1 ⇑h' = qExpansion 1 ⇑h := rfl
    obtain ⟨Ψ, hΨiso, hΨ⟩ := ih hk12 h' T₂ (by rw [hh', hT₂q])
    refine ⟨MvPolynomial.C t₀ * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) +
      MvPolynomial.C ((1728 : ℚ)⁻¹) * (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2) * Ψ, ?_, ?_⟩
    · refine (hab ▸ iso_monomial t₀ a b).add ?_
      have := iso_delta.mul hΨiso
      rwa [Nat.add_sub_cancel' hk12] at this
    · have hTeq : T = PowerSeries.C t₀ * (e4Q ^ a * e6Q ^ b) + dQ * T₂ := by
        rw [hT₂, dQ_eq, mul_assoc, ← mul_assoc dQ', dQ'_mul_inv, one_mul, ← hT₁', hT₁def]
        ring
      rw [map_add, ev_monomial, map_mul ev _ Ψ, ev_delta, hΨ, hTeq]
  ·
    have hh0 : ⇑h = 0 := levelOne_neg_weight_eq_zero (by omega) h
    have hT₁z : T₁ = 0 := by
      apply map_ι_injective
      rw [hT₁, hfac, hh0, qExpansion_zero, mul_zero, map_zero]
    refine ⟨MvPolynomial.C t₀ * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b),
      hab ▸ iso_monomial t₀ a b, ?_⟩
    have hTeq : T = PowerSeries.C t₀ * (e4Q ^ a * e6Q ^ b) := by
      rw [← sub_eq_zero, ← hT₁def, hT₁z]
    rw [ev_monomial, ← hTeq]

theorem claim_all (k : ℕ) : Claim k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.even_or_odd k with hke | hko
    · by_cases hk4 : 4 ≤ k
      · have hmod : k % 4 = 0 ∨ k % 4 = 2 := by obtain ⟨r, hr⟩ := hke; omega
        rcases hmod with h0 | h2
        · exact claim_step hk4 (a := k / 4) (b := 0) (by omega)
            (fun hk12 => ih (k - 12) (by omega))
        · exact claim_step hk4 (a := (k - 6) / 4) (b := 1) (by omega)
            (fun hk12 => ih (k - 12) (by omega))
      · have hk : k = 0 ∨ k = 2 := by obtain ⟨r, hr⟩ := hke; omega
        rcases hk with rfl | rfl
        · exact claim_zero
        · exact claim_two
    · exact claim_odd hko

theorem main {k : ℤ} (f : ModularForm 𝒮ℒ k) {T : PowerSeries ℚ}
    (hT : T.map ι = qExpansion 1 ⇑f) :
    ∃ Φ : MvPolynomial (Fin 2) ℚ, Φ.IsWeightedHomogeneous 𝔴 k.toNat ∧ ev Φ = T := by
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [Int.toNat_natCast]
    exact claim_all n f T hT
  · have hf : ⇑f = 0 := levelOne_neg_weight_eq_zero (by omega) f
    exact ⟨0, MvPolynomial.isWeightedHomogeneous_zero _ _ _, by
      rw [eq_zero_of_coe_eq_zero hf hT, map_zero]⟩

end Main

end

end ModularForm.RationalLevelOneProof

open ModularForm.RationalLevelOneProof in
theorem solution {k : ℤ} (f : ModularForm 𝒮ℒ k) (T : PowerSeries ℚ)
    (hT : T.map (algebraMap ℚ ℂ) = UpperHalfPlane.qExpansion 1 ⇑f) :
    ∃ Φ : MvPolynomial (Fin 2) ℚ,
      Φ.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) k.toNat ∧
        MvPolynomial.aeval
            (![(PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3).map
                (Int.castRingHom ℚ),
              (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5).map
                (Int.castRingHom ℚ)] : Fin 2 → PowerSeries ℚ) Φ = T :=
  main f hT

#print axioms solution

end S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne
end P2MW
export P2MW.S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne (solution)
