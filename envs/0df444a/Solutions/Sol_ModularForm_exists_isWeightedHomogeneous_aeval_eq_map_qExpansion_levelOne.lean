-- Prove2me | solution 1 for ModularForm.exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5b4ad06d-b260-5dbc-add0-ba6796f4435d

import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_eisenstein4_cube_sub_mk_sq
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne

open scoped MatrixGroups
p2m_open "UpperHalfPlane ModularForm P2MW.S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne.ModularForm ModularFormClass EisensteinSeries"

namespace ModularForm
p2m_export "ModularForm" "levelOne_odd_weight_eq_zero mk sub_apply pow IsGLPos.coe_smul coe_smul levelOne_weight_two_rank_zero toCuspForm discriminant_eq_E₄_cube_sub_E₆_sq one_coe_eq_one discriminant add ext smul_apply E₄ mcast qExpansion_eq_qExpansion_discriminant_mul E₆ coe_mcast coe_pow mul coe_sub"
namespace IsobaricLevelOneProof
p2m_open "ModularForm"

noncomputable section

def e6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

def dd : PowerSeries ℤ := PowerSeries.X * ModularCurve.dedekindEtaUnit

local notation "e4" => ModularCurve.eisenstein4
local notation "ι" => Int.castRingHom ℂ

lemma constantCoeff_e6 : PowerSeries.constantCoeff e6 = 1 := by
  simp [e6, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]

lemma map_int_injective : Function.Injective (PowerSeries.map ι) :=
  PowerSeries.map_injective _ (RingHom.injective_int _)

lemma qExpansion_E4 : qExpansion 1 ⇑ModularForm.E₄ = PowerSeries.map ι e4 :=
  ModularCurve.qExpansion_E4_eq_map_eisenstein4

lemma qExpansion_E6 : qExpansion 1 ⇑ModularForm.E₆ = PowerSeries.map ι e6 := by
  ext n
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩ n, show bernoulli 6 = 1 / 42 by decide +kernel]
  simp only [PowerSeries.coeff_map, e6, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply, eq_intCast]
  split_ifs with h
  · simp
  · push_cast
    ring

lemma e4_cube_sub_e6_sq : e4 ^ 3 - e6 ^ 2 = 1728 * dd :=
  ModularCurve.eisenstein4_cube_sub_mk_sq

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
    qExpansion 1 ModularForm.discriminant = PowerSeries.map ι dd := by
  have h1 : (1728 : ℂ) • qExpansion 1 ModularForm.discriminant =
      (1728 : ℂ) • PowerSeries.map ι dd := by
    rw [← CuspForm.coe_discriminant,
      ← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      ← CuspForm.IsGLPos.coe_smul, ← coe_G12_eq_smul, qExpansion_G12, qExpansion_E4, qExpansion_E6,
      ← map_pow, ← map_pow, ← map_sub, e4_cube_sub_e6_sq, map_mul, PowerSeries.smul_eq_C_mul]
    rw [map_ofNat, map_ofNat]
  exact smul_right_injective _ (by norm_num : (1728 : ℂ) ≠ 0) h1

lemma eq_zero_of_coe_eq_zero {k : ℤ} {f : ModularForm 𝒮ℒ k} (hf : ⇑f = 0) {T : PowerSeries ℤ}
    (hT : PowerSeries.map ι T = qExpansion 1 ⇑f) : T = 0 := by
  apply map_int_injective
  rw [hT, hf, qExpansion_zero, map_zero]

lemma eq_C_of_map_eq_C {T : PowerSeries ℤ} {c : ℂ} (hT : PowerSeries.map ι T = PowerSeries.C c) :
    T = PowerSeries.C (PowerSeries.constantCoeff T) := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := congrArg (PowerSeries.coeff n) hT
    rw [PowerSeries.coeff_map, PowerSeries.coeff_C, if_neg hn.ne'] at h
    rw [PowerSeries.coeff_C, if_neg hn.ne']
    rw [eq_intCast] at h
    exact_mod_cast h

section Poly

variable {ℓ : ℕ}

local notation "𝔴" => (![4, 6] : Fin 2 → ℕ)

lemma iso_monomial (r : ZMod ℓ) (a b : ℕ) :
    (MvPolynomial.C r * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) :
      MvPolynomial (Fin 2) (ZMod ℓ)).IsWeightedHomogeneous 𝔴 (4 * a + 6 * b) := by
  have h0 := (MvPolynomial.isWeightedHomogeneous_X (ZMod ℓ) 𝔴 (0 : Fin 2)).pow a
  have h1 := (MvPolynomial.isWeightedHomogeneous_X (ZMod ℓ) 𝔴 (1 : Fin 2)).pow b
  have h := (h0.mul h1).C_mul r
  convert h using 1
  simp [smul_eq_mul, mul_comm]

lemma iso_delta :
    (MvPolynomial.C ((1728 : ZMod ℓ)⁻¹) * (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2) :
      MvPolynomial (Fin 2) (ZMod ℓ)).IsWeightedHomogeneous 𝔴 12 := by
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  have h0 := (MvPolynomial.isWeightedHomogeneous_X (ZMod ℓ) 𝔴 (0 : Fin 2)).pow 3
  have h1 := (MvPolynomial.isWeightedHomogeneous_X (ZMod ℓ) 𝔴 (1 : Fin 2)).pow 2
  have h0' : (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) (ZMod ℓ)).IsWeightedHomogeneous 𝔴 12 := by
    convert h0 using 1
    rfl
  have h1' : (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) (ZMod ℓ)).IsWeightedHomogeneous 𝔴 12 := by
    convert h1 using 1
    rfl
  rw [← MvPolynomial.mem_weightedHomogeneousSubmodule] at h0' h1' ⊢
  exact Submodule.sub_mem _ h0' h1'

end Poly

section Main

variable {ℓ : ℕ}

local notation "𝔴" => (![4, 6] : Fin 2 → ℕ)
local notation "ρ" => Int.castRingHom (ZMod ℓ)

def ev (ℓ : ℕ) : MvPolynomial (Fin 2) (ZMod ℓ) →ₐ[ZMod ℓ] PowerSeries (ZMod ℓ) :=
  MvPolynomial.aeval
    (![PowerSeries.map (Int.castRingHom (ZMod ℓ)) e4, PowerSeries.map (Int.castRingHom (ZMod ℓ)) e6])

lemma ev_X0 : ev ℓ (MvPolynomial.X 0) = PowerSeries.map ρ e4 := by
  simp [ev]

lemma ev_X1 : ev ℓ (MvPolynomial.X 1) = PowerSeries.map ρ e6 := by
  simp [ev]

lemma ev_C (r : ZMod ℓ) : ev ℓ (MvPolynomial.C r) = PowerSeries.C r := by
  simp [ev]

lemma ev_monomial (t : ℤ) (a b : ℕ) :
    ev ℓ (MvPolynomial.C (ρ t) * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) =
      PowerSeries.map ρ (PowerSeries.C t * (e4 ^ a * e6 ^ b)) := by
  rw [map_mul, map_mul, map_pow, map_pow, ev_C, ev_X0, ev_X1]
  simp only [map_mul, map_pow, PowerSeries.map_C]

lemma natCast_1728_ne_zero (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) : (1728 : ZMod ℓ) ≠ 0 := by
  have hnd : ¬ ℓ ∣ 1728 := by
    intro h
    have h' : ℓ ∣ 2 ^ 6 * 3 ^ 3 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hℓ).1 h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hℓ.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) (hℓ.dvd_of_dvd_pow h3); omega
  intro h
  apply hnd
  have h' : ((1728 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  exact (ZMod.natCast_eq_zero_iff 1728 ℓ).1 h'

lemma ev_delta (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) :
    ev ℓ (MvPolynomial.C ((1728 : ZMod ℓ)⁻¹) * (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)) =
      PowerSeries.map ρ dd := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have h := congrArg (PowerSeries.map ρ) e4_cube_sub_e6_sq
  rw [map_sub, map_pow, map_pow, map_mul] at h
  rw [map_mul, map_sub, map_pow, map_pow, ev_C, ev_X0, ev_X1, h, ← mul_assoc]
  have h1728 : PowerSeries.C ((1728 : ZMod ℓ)⁻¹) * PowerSeries.map ρ 1728 = 1 := by
    rw [map_ofNat, ← map_ofNat (PowerSeries.C (R := ZMod ℓ)) 1728, ← map_mul,
      inv_mul_cancel₀ (natCast_1728_ne_zero hℓ h5), map_one]
  rw [h1728, one_mul]

def Claim (ℓ k : ℕ) : Prop :=
  ∀ (f : ModularForm 𝒮ℒ (k : ℤ)) (T : PowerSeries ℤ),
    PowerSeries.map (Int.castRingHom ℂ) T = qExpansion 1 ⇑f →
      ∃ Φ : MvPolynomial (Fin 2) (ZMod ℓ), Φ.IsWeightedHomogeneous 𝔴 k ∧
        ev ℓ Φ = PowerSeries.map (Int.castRingHom (ZMod ℓ)) T

lemma claim_of_coe_zero {k : ℕ} {f : ModularForm 𝒮ℒ (k : ℤ)} (hf : ⇑f = 0)
    {T : PowerSeries ℤ} (hT : PowerSeries.map ι T = qExpansion 1 ⇑f) :
    ∃ Φ : MvPolynomial (Fin 2) (ZMod ℓ), Φ.IsWeightedHomogeneous 𝔴 k ∧
      ev ℓ Φ = PowerSeries.map ρ T :=
  ⟨0, MvPolynomial.isWeightedHomogeneous_zero _ _ _, by
    rw [eq_zero_of_coe_eq_zero hf hT, map_zero, map_zero]⟩

lemma claim_zero : Claim ℓ 0 := by
  intro f T hT
  obtain ⟨c, hc⟩ := levelOne_weight_zero_const f
  have hq : qExpansion 1 ⇑f = PowerSeries.C c := by
    have h1 : ⇑f = c • ⇑(1 : ModularForm 𝒮ℒ 0) := by
      rw [hc, one_coe_eq_one]; ext z; simp
    have h2 : qExpansion 1 ⇑f = c • qExpansion 1 ⇑(1 : ModularForm 𝒮ℒ 0) := by
      rw [h1]; exact ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c _
    rw [h2, ModularForm.qExpansion_one, PowerSeries.smul_eq_C_mul, mul_one]
  rw [hq] at hT
  refine ⟨MvPolynomial.C (ρ (PowerSeries.constantCoeff T)),
    MvPolynomial.isWeightedHomogeneous_C _ _, ?_⟩
  rw [ev_C, eq_C_of_map_eq_C hT, PowerSeries.map_C]
  simp

lemma claim_two : Claim ℓ 2 := by
  intro f T hT
  have hf : f = 0 := rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero f
  exact claim_of_coe_zero (by rw [hf]; rfl) hT

lemma claim_odd {k : ℕ} (hk : Odd k) : Claim ℓ k := by
  intro f T hT
  have hf : f = 0 := levelOne_odd_weight_eq_zero (by exact_mod_cast hk) f
  exact claim_of_coe_zero (by rw [hf]; rfl) hT

lemma claim_step (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {k : ℕ} (hk4 : 4 ≤ k) {a b : ℕ}
    (hab : 4 * a + 6 * b = k) (ih : 12 ≤ k → Claim ℓ (k - 12)) : Claim ℓ k := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  intro f T hT

  let g : ModularForm 𝒮ℒ (k : ℤ) := ModularForm.mcast (by omega) ((E₄.pow a).mul (E₆.pow b))
  have hg : qExpansion 1 ⇑g = PowerSeries.map ι (e4 ^ a * e6 ^ b) := by
    simp only [g, ModularForm.qExpansion_mcast]
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, qExpansion_E4, qExpansion_E6,
      map_mul, map_pow, map_pow]
  set t₀ : ℤ := PowerSeries.constantCoeff T with ht₀

  let f₁ : ModularForm 𝒮ℒ (k : ℤ) := f - (t₀ : ℂ) • g
  set T₁ : PowerSeries ℤ := T - PowerSeries.C t₀ * (e4 ^ a * e6 ^ b) with hT₁def
  have hT₁ : PowerSeries.map ι T₁ = qExpansion 1 ⇑f₁ := by
    have e : ⇑f₁ = ⇑f - ⇑((t₀ : ℂ) • g) := rfl
    rw [e, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL f ((t₀ : ℂ) • g),
      ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hg, ← hT,
      hT₁def, map_sub, map_mul, PowerSeries.map_C, PowerSeries.smul_eq_C_mul]
    simp
  have hT₁0 : PowerSeries.constantCoeff T₁ = 0 := by
    simp [hT₁def, ht₀, ModularCurve.constantCoeff_eisenstein4, constantCoeff_e6]
  have hcusp : PowerSeries.coeff 0 (qExpansion 1 ⇑f₁) = 0 := by
    rw [← hT₁, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hT₁0, map_zero]

  set h : ModularForm 𝒮ℒ ((k : ℤ) - 12) := CuspForm.discriminantEquiv (toCuspForm f₁ hcusp) with hh
  have hfac : qExpansion 1 ⇑f₁ = qExpansion 1 ModularForm.discriminant * qExpansion 1 ⇑h :=
    qExpansion_eq_qExpansion_discriminant_mul f₁ hcusp
  by_cases hk12 : 12 ≤ k
  ·
    obtain ⟨T₁', hT₁'⟩ := PowerSeries.X_dvd_iff.mpr hT₁0
    set T₂ : PowerSeries ℤ := ModularCurve.dedekindEtaUnitInv * T₁' with hT₂
    have hT₂q : PowerSeries.map ι T₂ = qExpansion 1 ⇑h := by
      have e1 : PowerSeries.map ι PowerSeries.X * PowerSeries.map ι T₁' =
          PowerSeries.map ι PowerSeries.X *
            (PowerSeries.map ι ModularCurve.dedekindEtaUnit * qExpansion 1 ⇑h) := by
        rw [← map_mul, ← hT₁', hT₁, hfac, qExpansion_discriminant, dd, map_mul, mul_assoc]
      rw [PowerSeries.map_X] at e1
      have e2 := mul_left_cancel₀ PowerSeries.X_ne_zero e1
      rw [hT₂, map_mul, e2, ← mul_assoc, ← map_mul, mul_comm ModularCurve.dedekindEtaUnitInv,
        ModularCurve.dedekindEtaUnit_mul_inv, map_one, one_mul]

    let h' : ModularForm 𝒮ℒ ((k - 12 : ℕ) : ℤ) := ModularForm.mcast (by omega) h
    have hh' : qExpansion 1 ⇑h' = qExpansion 1 ⇑h := rfl
    obtain ⟨Ψ, hΨiso, hΨ⟩ := ih hk12 h' T₂ (by rw [hh', hT₂q])
    refine ⟨MvPolynomial.C (ρ t₀) * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) +
      MvPolynomial.C ((1728 : ZMod ℓ)⁻¹) * (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2) * Ψ,
      ?_, ?_⟩
    · refine (hab ▸ iso_monomial (ρ t₀) a b).add ?_
      have := iso_delta.mul hΨiso
      rwa [Nat.add_sub_cancel' hk12] at this
    · have hTeq : T = PowerSeries.C t₀ * (e4 ^ a * e6 ^ b) + dd * T₂ := by
        rw [hT₂, dd, mul_assoc, ← mul_assoc ModularCurve.dedekindEtaUnit,
          ModularCurve.dedekindEtaUnit_mul_inv, one_mul, ← hT₁', hT₁def]
        ring
      rw [map_add, ev_monomial, map_mul (ev ℓ) _ Ψ, ev_delta hℓ h5, hΨ, hTeq]
      simp only [map_add, map_mul]
  ·
    have hh0 : ⇑h = 0 := levelOne_neg_weight_eq_zero (by omega) h
    have hT₁z : T₁ = 0 := by
      apply map_int_injective
      rw [hT₁, hfac, hh0, qExpansion_zero, mul_zero, map_zero]
    refine ⟨MvPolynomial.C (ρ t₀) * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b),
      hab ▸ iso_monomial (ρ t₀) a b, ?_⟩
    have hTeq : T = PowerSeries.C t₀ * (e4 ^ a * e6 ^ b) := by
      rw [← sub_eq_zero, ← hT₁def, hT₁z]
    rw [ev_monomial, ← hTeq]

theorem claim_all (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (k : ℕ) : Claim ℓ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.even_or_odd k with hke | hko
    · by_cases hk4 : 4 ≤ k
      · have hmod : k % 4 = 0 ∨ k % 4 = 2 := by obtain ⟨r, hr⟩ := hke; omega
        rcases hmod with h0 | h2
        · exact claim_step hℓ h5 hk4 (a := k / 4) (b := 0) (by omega)
            (fun hk12 => ih (k - 12) (by omega))
        · exact claim_step hℓ h5 hk4 (a := (k - 6) / 4) (b := 1) (by omega)
            (fun hk12 => ih (k - 12) (by omega))
      · have hk : k = 0 ∨ k = 2 := by obtain ⟨r, hr⟩ := hke; omega
        rcases hk with rfl | rfl
        · exact claim_zero
        · exact claim_two
    · exact claim_odd hko

theorem main (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {k : ℤ} (f : ModularForm 𝒮ℒ k) {T : PowerSeries ℤ}
    (hT : PowerSeries.map ι T = qExpansion 1 ⇑f) :
    ∃ Φ : MvPolynomial (Fin 2) (ZMod ℓ), Φ.IsWeightedHomogeneous 𝔴 k.toNat ∧
      ev ℓ Φ = PowerSeries.map ρ T := by
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [Int.toNat_natCast]
    exact claim_all hℓ h5 n f T hT
  · have hf : ⇑f = 0 := levelOne_neg_weight_eq_zero (by omega) f
    exact ⟨0, MvPolynomial.isWeightedHomogeneous_zero _ _ _, by
      rw [eq_zero_of_coe_eq_zero hf hT, map_zero, map_zero]⟩

end Main

end

end ModularForm.IsobaricLevelOneProof

open ModularForm.IsobaricLevelOneProof in
theorem solution {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {k : ℤ} (f : ModularForm 𝒮ℒ k) {T : PowerSeries ℤ}
    (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑f) :
    ∃ Φ : MvPolynomial (Fin 2) (ZMod ℓ),
      Φ.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) k.toNat ∧
        MvPolynomial.aeval
            (![(PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3).map
                (Int.castRingHom (ZMod ℓ)),
              (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5).map
                (Int.castRingHom (ZMod ℓ))] : Fin 2 → PowerSeries (ZMod ℓ)) Φ =
          T.map (Int.castRingHom (ZMod ℓ)) :=
  main hℓ h5 f hT

end S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne
end P2MW
export P2MW.S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne (solution)
