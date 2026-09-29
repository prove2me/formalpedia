-- Prove2me | solution 1 for ModularCurve.CupPairing.cuspSum_eq_sum_finsum_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/afebb53b-8d3c-5fb8-b5f1-cddcc8b18cae

import Mathlib
import Definitions.Def_ModularCurve_PDPairing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le

set_option autoImplicit false

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.Cusp PDPairing.cuspGen PDPairing.cuspSum"
namespace CupPairing
namespace CuspDecomp
p2m_open "ModularCurve"

open ModularCurve.PDPairing MulAction Function

section Abstract

variable {G : Type*} [Group G] (H : Subgroup G)

theorem exists_out_smul (g : G) (q : G ⧸ H) : ∃ κ : H, (g • q).out = g * q.out * κ := by
  have h : (g * q.out)⁻¹ * (g • q).out ∈ H := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← MulAction.Quotient.coe_smul_out, smul_eq_mul]
  exact ⟨⟨_, h⟩, by simp only [mul_inv_cancel_left]⟩

theorem minimalPeriod_zpow_smul [Finite (G ⧸ H)] (a : G) (k : ℤ) (x : G ⧸ H) :
    minimalPeriod (a • ·) (a ^ k • x) = minimalPeriod (a • ·) x := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  rw [MulAction.minimalPeriod_eq_card, MulAction.minimalPeriod_eq_card]
  refine Fintype.card_congr (Equiv.setCongr ?_)
  exact MulAction.orbit_smul (⟨a, Subgroup.mem_zpowers a⟩ ^ k : Subgroup.zpowers a) x

theorem minimalPeriod_conj_smul [Finite (G ⧸ H)] (a d : G) (x : G ⧸ H) :
    minimalPeriod ((d * a * d⁻¹) • ·) (d • x) = minimalPeriod (a • ·) x := by
  apply Nat.dvd_antisymm
  · rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, conj_pow, mul_smul, mul_smul, inv_smul_smul,
      (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr (dvd_refl _)]
  · rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd]
    have h := (MulAction.pow_smul_eq_iff_minimalPeriod_dvd (a := d * a * d⁻¹) (b := d • x)).mpr
      (dvd_refl _)
    rw [conj_pow, mul_smul, mul_smul, inv_smul_smul] at h
    exact smul_left_cancel d h

variable [H.FiniteIndex]

noncomputable scoped instance fintypeQuot : Fintype (G ⧸ H) := Fintype.ofFinite _

noncomputable scoped instance fintypeOrbitQuot (a : G) :
    Fintype (orbitRel.Quotient (Subgroup.zpowers a) (G ⧸ H)) := Fintype.ofFinite _

theorem sum_smul_eq {M : Type*} [AddCommMonoid M] (g : G) (f : G ⧸ H → M) :
    ∑ q : G ⧸ H, f (g • q) = ∑ q : G ⧸ H, f q :=
  Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)

theorem sum_orbit_eq_sum_div (a : G) (f : G ⧸ H → ℚ)
    (hf : ∀ (k : ℤ) (x : G ⧸ H), f (a ^ k • x) = f x) :
    ∑ O : orbitRel.Quotient (Subgroup.zpowers a) (G ⧸ H), f O.out =
      ∑ x : G ⧸ H, f x / (minimalPeriod (a • ·) x : ℚ) := by
  classical
  rw [← (Subgroup.quotientEquivSigmaZMod H a).symm.sum_comp, Fintype.sum_sigma]
  refine Fintype.sum_congr _ _ (fun O => ?_)
  simp only [Subgroup.quotientEquivSigmaZMod_symm_apply, hf, minimalPeriod_zpow_smul,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hℓ : (minimalPeriod (a • ·) O.out : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne _)
  field_simp

theorem finsum_orbit_eq_sum (a : G) (f : orbitRel.Quotient (Subgroup.zpowers a) (G ⧸ H) → ℚ) :
    ∑ᶠ O, f O = ∑ O, f O := finsum_eq_sum_of_fintype f

end Abstract

section Width

variable (Δ : Subgroup SL(2, ℤ))

noncomputable def width (ζ : SL(2, ℤ) ⧸ Δ) : ℕ := minimalPeriod (ModularGroup.T • ·) ζ

theorem conj_zpow_mem_iff (z : SL(2, ℤ)) (n : ℤ) :
    z⁻¹ * ModularGroup.T ^ n * z ∈ Δ ↔ (width Δ (z : SL(2, ℤ) ⧸ Δ) : ℤ) ∣ n := by
  rw [mul_assoc, ← QuotientGroup.eq, ← smul_eq_mul, ← MulAction.Quotient.smul_coe, eq_comm,
    zpow_smul_eq_iff_minimalPeriod_dvd]
  rfl

noncomputable def gen (z : SL(2, ℤ)) : SL(2, ℤ) :=
  z⁻¹ * ModularGroup.T ^ ((width Δ (z : SL(2, ℤ) ⧸ Δ) : ℕ) : ℤ) * z

theorem gen_mem (z : SL(2, ℤ)) : gen Δ z ∈ Δ :=
  (conj_zpow_mem_iff Δ z _).mpr (dvd_refl _)

noncomputable def genΔ (z : SL(2, ℤ)) : Δ := ⟨gen Δ z, gen_mem Δ z⟩

@[scoped simp] theorem coe_genΔ (z : SL(2, ℤ)) : (genΔ Δ z : SL(2, ℤ)) = gen Δ z := rfl

theorem cuspGen_eq (Q : Cusp Δ) : cuspGen Δ Q = genΔ Δ Q.out.out := by
  apply Subtype.ext
  simp only [cuspGen, coe_genΔ, gen, width, QuotientGroup.out_eq', zpow_natCast]

theorem conj_conj (z δ : SL(2, ℤ)) (n m : ℤ) :
    (ModularGroup.T ^ n * z * δ)⁻¹ * ModularGroup.T ^ m * (ModularGroup.T ^ n * z * δ) =
      δ⁻¹ * (z⁻¹ * ModularGroup.T ^ m * z) * δ := by
  have hc : ModularGroup.T ^ m * ModularGroup.T ^ n = ModularGroup.T ^ n * ModularGroup.T ^ m :=
    zpow_mul_comm _ _ _
  simp only [mul_inv_rev, mul_assoc]
  rw [← mul_assoc (ModularGroup.T ^ m) (ModularGroup.T ^ n), hc, mul_assoc (ModularGroup.T ^ n),
    inv_mul_cancel_left]

theorem width_T_zpow_mul (z δ : SL(2, ℤ)) (hδ : δ ∈ Δ) (n : ℤ) :
    width Δ ((ModularGroup.T ^ n * z * δ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ) =
      width Δ (z : SL(2, ℤ) ⧸ Δ) := by
  have key : ∀ m : ℤ, (ModularGroup.T ^ n * z * δ)⁻¹ * ModularGroup.T ^ m *
      (ModularGroup.T ^ n * z * δ) ∈ Δ ↔ z⁻¹ * ModularGroup.T ^ m * z ∈ Δ := by
    intro m
    rw [conj_conj, Subgroup.mul_mem_cancel_right _ hδ, Subgroup.mul_mem_cancel_left _ (Δ.inv_mem hδ)]
  apply Nat.dvd_antisymm
  · have := (conj_zpow_mem_iff Δ (ModularGroup.T ^ n * z * δ) (width Δ (z : SL(2, ℤ) ⧸ Δ))).mp
      ((key _).mpr ((conj_zpow_mem_iff Δ z _).mpr (dvd_refl _)))
    exact Int.natCast_dvd_natCast.mp this
  · have := (conj_zpow_mem_iff Δ z
      (width Δ ((ModularGroup.T ^ n * z * δ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ))).mp
      ((key _).mp ((conj_zpow_mem_iff Δ _ _).mpr (dvd_refl _)))
    exact Int.natCast_dvd_natCast.mp this

theorem gen_T_zpow_mul (z δ : SL(2, ℤ)) (hδ : δ ∈ Δ) (n : ℤ) :
    gen Δ (ModularGroup.T ^ n * z * δ) = δ⁻¹ * gen Δ z * δ := by
  simp only [gen, width_T_zpow_mul Δ z δ hδ n]
  exact conj_conj z δ n _

theorem gen_mul (z δ : SL(2, ℤ)) (hδ : δ ∈ Δ) : gen Δ (z * δ) = δ⁻¹ * gen Δ z * δ := by
  have h := gen_T_zpow_mul Δ z δ hδ 0
  rwa [zpow_zero, one_mul] at h

theorem exists_out_T_zpow_smul (k : ℤ) (ζ : SL(2, ℤ) ⧸ Δ) :
    ∃ δ : SL(2, ℤ), δ ∈ Δ ∧ (ModularGroup.T ^ k • ζ).out = ModularGroup.T ^ k * ζ.out * δ := by
  obtain ⟨κ, hκ⟩ := exists_out_smul Δ (ModularGroup.T ^ k) ζ
  exact ⟨κ, κ.2, hκ⟩

theorem trace_conj_T_zpow (z : SL(2, ℤ)) (n : ℤ) :
    ((z⁻¹ * ModularGroup.T ^ n * z : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul,
    ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
  ring

theorem trace_gen_sq (z : SL(2, ℤ)) : ((gen Δ z : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [gen, trace_conj_T_zpow]
  norm_num

theorem gen_pow (z : SL(2, ℤ)) (m : ℕ) :
    gen Δ z ^ m = z⁻¹ * ModularGroup.T ^ ((width Δ (z : SL(2, ℤ) ⧸ Δ) : ℤ) * m) * z := by
  have h := conj_pow (a := z⁻¹) (b := ModularGroup.T ^ ((width Δ (z : SL(2, ℤ) ⧸ Δ) : ℕ) : ℤ))
    (i := m)
  rw [inv_inv] at h
  rw [gen, h, ← zpow_natCast (ModularGroup.T ^ ((width Δ (z : SL(2, ℤ) ⧸ Δ) : ℕ) : ℤ)) m,
    ← zpow_mul]

end Width

section TwoLevels

variable (Γ' Γ : Subgroup SL(2, ℤ)) [Γ'.FiniteIndex] [Γ.FiniteIndex] (hle : Γ' ≤ Γ)

abbrev K' : Subgroup Γ := Γ'.subgroupOf Γ

noncomputable def piElt (u : Γ) (q : Γ ⧸ K' Γ' Γ) : Γ :=
  q.out⁻¹ * u ^ minimalPeriod (u • ·) q * q.out

omit [Γ'.FiniteIndex] [Γ.FiniteIndex] in
theorem piElt_mem (u : Γ) (q : Γ ⧸ K' Γ' Γ) : (piElt Γ' Γ u q : SL(2, ℤ)) ∈ Γ' :=
  Subgroup.mem_subgroupOf.mp (QuotientGroup.out_conj_pow_minimalPeriod_mem (K' Γ' Γ) u q)

include hle in

theorem width_mul (g : SL(2, ℤ)) (γ : Γ) :
    width Γ' ((g * γ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ') =
      width Γ (g : SL(2, ℤ) ⧸ Γ) * minimalPeriod ((genΔ Γ g) • ·) (γ : Γ ⧸ K' Γ' Γ) := by
  set w := width Γ (g : SL(2, ℤ) ⧸ Γ) with hw
  set ℓ := minimalPeriod ((genΔ Γ g) • ·) (γ : Γ ⧸ K' Γ' Γ) with hℓ
  have hw0 : w ≠ 0 := by rw [hw]; unfold width; exact NeZero.ne _
  have hℓ0 : ℓ ≠ 0 := by rw [hℓ]; exact NeZero.ne _

  have key : ∀ n : ℕ, (ModularGroup.T • ·)^[n] ((g * γ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ') =
      ((g * γ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ') ↔ w * ℓ ∣ n := by
    intro n
    rw [smul_iterate]
    change ModularGroup.T ^ n • ((g * γ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ') =
      ((g * γ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ') ↔ w * ℓ ∣ n
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, eq_comm, QuotientGroup.eq]
    have hrew : (g * (γ : SL(2, ℤ)))⁻¹ * (ModularGroup.T ^ n * (g * γ)) =
        (γ : SL(2, ℤ))⁻¹ * (g⁻¹ * ModularGroup.T ^ (n : ℤ) * g) * γ := by
      rw [zpow_natCast]; group
    rw [hrew]
    constructor
    · intro hmem

      have hΓ : g⁻¹ * ModularGroup.T ^ (n : ℤ) * g ∈ Γ := by
        have h1 : (γ : SL(2, ℤ))⁻¹ * (g⁻¹ * ModularGroup.T ^ (n : ℤ) * g) * γ ∈ Γ := hle hmem
        rwa [Subgroup.mul_mem_cancel_right _ γ.2, Subgroup.mul_mem_cancel_left _ (Γ.inv_mem γ.2)] at h1
      obtain ⟨m, hm⟩ := (conj_zpow_mem_iff Γ g n).mp hΓ
      rw [← hw] at hm
      have hm0 : 0 ≤ m := by
        have : (0 : ℤ) ≤ (w : ℤ) * m := by rw [← hm]; exact Int.natCast_nonneg n
        exact nonneg_of_mul_nonneg_right this (by exact_mod_cast Nat.pos_of_ne_zero hw0)
      lift m to ℕ using hm0
      have hn : n = w * m := by exact_mod_cast hm

      have hu : g⁻¹ * ModularGroup.T ^ (n : ℤ) * g = (genΔ Γ g : SL(2, ℤ)) ^ m := by
        rw [coe_genΔ, gen_pow, ← hw, hn, Nat.cast_mul]
      have hmem' : ((γ⁻¹ * genΔ Γ g ^ m * γ : Γ) : SL(2, ℤ)) ∈ Γ' := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, ← hu]
        exact hmem
      have hK : γ⁻¹ * genΔ Γ g ^ m * γ ∈ K' Γ' Γ := Subgroup.mem_subgroupOf.mpr hmem'
      have hfix : (genΔ Γ g) ^ m • (γ : Γ ⧸ K' Γ' Γ) = (γ : Γ ⧸ K' Γ' Γ) := by
        rw [MulAction.Quotient.smul_coe, smul_eq_mul, eq_comm, QuotientGroup.eq, ← mul_assoc]
        exact hK
      obtain ⟨t, ht⟩ := (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mp hfix
      refine ⟨t, ?_⟩
      rw [hn, ht, ← hℓ, mul_assoc]
    · rintro ⟨t, ht⟩
      have hcast : ((w * ℓ * t : ℕ) : ℤ) = (w : ℤ) * ((ℓ * t : ℕ) : ℤ) := by push_cast; ring
      have hu : g⁻¹ * ModularGroup.T ^ (n : ℤ) * g = (genΔ Γ g : SL(2, ℤ)) ^ (ℓ * t) := by
        rw [coe_genΔ, gen_pow, ← hw, ht, hcast]
      have hfix : (genΔ Γ g) ^ (ℓ * t) • (γ : Γ ⧸ K' Γ' Γ) = (γ : Γ ⧸ K' Γ' Γ) :=
        (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr ⟨t, rfl⟩
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, eq_comm, QuotientGroup.eq, ← mul_assoc] at hfix
      have hmem' := Subgroup.mem_subgroupOf.mp hfix
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at hmem'
      rwa [hu]

  have hpos : 0 < w * ℓ := Nat.pos_of_ne_zero (mul_ne_zero hw0 hℓ0)
  apply Nat.dvd_antisymm
  · exact IsPeriodicPt.minimalPeriod_dvd ((key (w * ℓ)).mpr (dvd_refl _))
  · exact (key _).mp (isPeriodicPt_minimalPeriod _ _)

include hle in

theorem gen_mul_eq (g : SL(2, ℤ)) (γ : Γ) :
    gen Γ' (g * γ) = ((γ⁻¹ * genΔ Γ g ^ minimalPeriod ((genΔ Γ g) • ·) (γ : Γ ⧸ K' Γ' Γ) * γ : Γ) :
      SL(2, ℤ)) := by
  rw [gen, width_mul Γ' Γ hle, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_pow, coe_genΔ, gen_pow, Nat.cast_mul]
  group

end TwoLevels

section Main

variable (Γ' Γ : Subgroup SL(2, ℤ)) [Γ'.FiniteIndex] [Γ.FiniteIndex] (hle : Γ' ≤ Γ)
  (F : SL(2, ℤ) → ℚ)
  (hF : ∀ p ∈ Γ', ∀ δ ∈ Γ', (p : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → F (δ * p * δ⁻¹) = F p)

include hF in
omit [Γ'.FiniteIndex] in

theorem hF' (p : SL(2, ℤ)) (hp : p ∈ Γ') (δ : SL(2, ℤ)) (hδ : δ ∈ Γ')
    (htr : (p : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) : F (δ⁻¹ * p * δ) = F p := by
  have h := hF p hp δ⁻¹ (Γ'.inv_mem hδ) htr
  rwa [inv_inv] at h

noncomputable def Φ (u : Γ) : ℚ :=
  ∑ q : Γ ⧸ K' Γ' Γ, F (piElt Γ' Γ u q : Γ) / (minimalPeriod (u • ·) q : ℚ)

include hF in
omit [Γ.FiniteIndex] in

theorem F_piElt_zpow_smul (g : SL(2, ℤ)) (k : ℤ) (q : Γ ⧸ K' Γ' Γ) :
    F (piElt Γ' Γ (genΔ Γ g) (genΔ Γ g ^ k • q) : Γ) = F (piElt Γ' Γ (genΔ Γ g) q : Γ) := by
  set u : Γ := genΔ Γ g with hu
  obtain ⟨κ, hκ⟩ := exists_out_smul (K' Γ' Γ) (u ^ k) q
  have hℓ := minimalPeriod_zpow_smul (K' Γ' Γ) u k q
  have hcalc : (piElt Γ' Γ u (u ^ k • q) : Γ) = (κ : Γ)⁻¹ * piElt Γ' Γ u q * κ := by
    unfold piElt
    rw [hℓ, hκ]
    simp only [mul_inv_rev]
    have hc : u ^ k * u ^ minimalPeriod (u • ·) q = u ^ minimalPeriod (u • ·) q * u ^ k := by
      rw [← zpow_natCast, ← zpow_add, ← zpow_add, add_comm]
    calc (κ : Γ)⁻¹ * ((q.out)⁻¹ * (u ^ k)⁻¹) * u ^ minimalPeriod (u • ·) q * (u ^ k * q.out * κ)
        = (κ : Γ)⁻¹ * (q.out)⁻¹ * ((u ^ k)⁻¹ * (u ^ minimalPeriod (u • ·) q * u ^ k)) * q.out * κ := by
          group
      _ = (κ : Γ)⁻¹ * (q.out)⁻¹ * u ^ minimalPeriod (u • ·) q * q.out * κ := by
          rw [← hc, inv_mul_cancel_left]
      _ = _ := by group
  rw [hcalc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  refine hF' Γ' F hF _ (piElt_mem Γ' Γ u q) _ (Subgroup.mem_subgroupOf.mp κ.2) ?_

  unfold piElt
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hu, coe_genΔ, gen_pow]
  have : ((q.out : Γ) : SL(2, ℤ))⁻¹ * (g⁻¹ * ModularGroup.T ^ ((width Γ (g : SL(2, ℤ) ⧸ Γ) : ℤ) *
      (minimalPeriod (u • ·) q : ℕ)) * g) * (q.out : Γ) =
      (g * (q.out : Γ))⁻¹ * ModularGroup.T ^ ((width Γ (g : SL(2, ℤ) ⧸ Γ) : ℤ) *
        (minimalPeriod (u • ·) q : ℕ)) * (g * (q.out : Γ)) := by group
  rw [this, trace_conj_T_zpow]
  norm_num

include hF in
omit [Γ.FiniteIndex] in

theorem finsum_orbit_eq_Φ (g : SL(2, ℤ)) :
    ∑ᶠ O : orbitRel.Quotient (Subgroup.zpowers (genΔ Γ g)) (Γ ⧸ K' Γ' Γ),
        F (piElt Γ' Γ (genΔ Γ g) O.out : Γ) = Φ Γ' Γ F (genΔ Γ g) := by
  rw [finsum_orbit_eq_sum, Φ]
  exact sum_orbit_eq_sum_div (K' Γ' Γ) (genΔ Γ g) (fun q => F (piElt Γ' Γ (genΔ Γ g) q : Γ))
    (F_piElt_zpow_smul Γ' Γ F hF g)

include hF in
omit [Γ.FiniteIndex] in

theorem Φ_conj (g : SL(2, ℤ)) (δ : Γ) :
    Φ Γ' Γ F (δ⁻¹ * genΔ Γ g * δ) = Φ Γ' Γ F (genΔ Γ g) := by
  set u : Γ := genΔ Γ g with hu
  unfold Φ
  rw [← sum_smul_eq (K' Γ' Γ) δ⁻¹ (fun q => F (piElt Γ' Γ (δ⁻¹ * u * δ) q : Γ) /
    (minimalPeriod ((δ⁻¹ * u * δ) • ·) q : ℚ))]
  refine Fintype.sum_congr _ _ (fun q => ?_)
  have hℓ : minimalPeriod ((δ⁻¹ * u * δ) • ·) (δ⁻¹ • q) = minimalPeriod (u • ·) q := by
    have := minimalPeriod_conj_smul (K' Γ' Γ) u δ⁻¹ q
    rwa [inv_inv] at this
  rw [hℓ]
  congr 1
  obtain ⟨κ, hκ⟩ := exists_out_smul (K' Γ' Γ) δ⁻¹ q
  have hcalc : (piElt Γ' Γ (δ⁻¹ * u * δ) (δ⁻¹ • q) : Γ) = (κ : Γ)⁻¹ * piElt Γ' Γ u q * κ := by
    unfold piElt
    rw [hℓ, hκ, show δ⁻¹ * u * δ = δ⁻¹ * u * δ⁻¹⁻¹ by rw [inv_inv], conj_pow]
    group
  rw [hcalc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  refine hF' Γ' F hF _ (piElt_mem Γ' Γ u q) _ (Subgroup.mem_subgroupOf.mp κ.2) ?_
  unfold piElt
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hu, coe_genΔ, gen_pow]
  have : ((q.out : Γ) : SL(2, ℤ))⁻¹ * (g⁻¹ * ModularGroup.T ^ ((width Γ (g : SL(2, ℤ) ⧸ Γ) : ℤ) *
      (minimalPeriod (u • ·) q : ℕ)) * g) * (q.out : Γ) =
      (g * (q.out : Γ))⁻¹ * ModularGroup.T ^ ((width Γ (g : SL(2, ℤ) ⧸ Γ) : ℤ) *
        (minimalPeriod (u • ·) q : ℕ)) * (g * (q.out : Γ)) := by group
  rw [this, trace_conj_T_zpow]
  norm_num

include hF in

theorem rhs_eq :
    ∑ Q : Cusp Γ, ∑ᶠ O : orbitRel.Quotient (Subgroup.zpowers (cuspGen Γ Q)) (Γ ⧸ K' Γ' Γ),
        F ((O.out.out⁻¹ * cuspGen Γ Q ^ minimalPeriod (cuspGen Γ Q • ·) O.out * O.out.out : Γ) :
          SL(2, ℤ)) =
      ∑ ζ : SL(2, ℤ) ⧸ Γ, Φ Γ' Γ F (genΔ Γ ζ.out) / (width Γ ζ : ℚ) := by
  have h1 : ∀ Q : Cusp Γ, (∑ᶠ O : orbitRel.Quotient (Subgroup.zpowers (cuspGen Γ Q)) (Γ ⧸ K' Γ' Γ),
      F ((O.out.out⁻¹ * cuspGen Γ Q ^ minimalPeriod (cuspGen Γ Q • ·) O.out * O.out.out : Γ) :
        SL(2, ℤ))) = Φ Γ' Γ F (genΔ Γ Q.out.out) := by
    intro Q
    rw [cuspGen_eq]
    exact finsum_orbit_eq_Φ Γ' Γ F hF Q.out.out
  simp only [h1]
  refine sum_orbit_eq_sum_div Γ ModularGroup.T (fun ζ => Φ Γ' Γ F (genΔ Γ ζ.out)) (fun k ζ => ?_)
  obtain ⟨δ, hδ, hout⟩ := exists_out_T_zpow_smul Γ k ζ
  have hgen : genΔ Γ (ModularGroup.T ^ k • ζ).out = (⟨δ, hδ⟩ : Γ)⁻¹ * genΔ Γ ζ.out * ⟨δ, hδ⟩ := by
    apply Subtype.ext
    simp only [coe_genΔ, Subgroup.coe_mul, Subgroup.coe_inv, hout]
    exact gen_T_zpow_mul Γ ζ.out δ hδ k
  rw [hgen, Φ_conj Γ' Γ F hF]

include hF in
omit [Γ.FiniteIndex] in

theorem lhs_eq :
    cuspSum Γ' (fun γ => F γ) =
      ∑ ζ' : SL(2, ℤ) ⧸ Γ', F (gen Γ' ζ'.out) / (width Γ' ζ' : ℚ) := by
  have h1 : cuspSum Γ' (fun γ => F γ) = ∑ Q' : Cusp Γ', F (gen Γ' Q'.out.out) := by
    unfold cuspSum
    exact Finset.sum_congr rfl (fun Q' _ => by rw [cuspGen_eq]; rfl)
  have h2 : ∀ (k : ℤ) (ζ' : SL(2, ℤ) ⧸ Γ'), F (gen Γ' (ModularGroup.T ^ k • ζ').out) =
      F (gen Γ' ζ'.out) := by
    intro k ζ'
    obtain ⟨δ, hδ, hout⟩ := exists_out_T_zpow_smul Γ' k ζ'
    rw [hout, gen_T_zpow_mul Γ' ζ'.out δ hδ k]
    exact hF' Γ' F hF _ (gen_mem Γ' _) δ hδ (trace_gen_sq Γ' _)
  rw [h1]
  exact sum_orbit_eq_sum_div Γ' ModularGroup.T (fun ζ' => F (gen Γ' ζ'.out)) h2

include hF hle in

theorem summand_eq (ζ : SL(2, ℤ) ⧸ Γ) (q : Γ ⧸ K' Γ' Γ) :
    F (gen Γ' ((Subgroup.quotientEquivProdOfLE hle).symm (ζ, q)).out) /
        (width Γ' ((Subgroup.quotientEquivProdOfLE hle).symm (ζ, q)) : ℚ) =
      F (piElt Γ' Γ (genΔ Γ ζ.out) q : Γ) / (minimalPeriod ((genΔ Γ ζ.out) • ·) q : ℚ) /
        (width Γ ζ : ℚ) := by
  have hsymm : (Subgroup.quotientEquivProdOfLE hle).symm (ζ, q) =
      ((ζ.out * (q.out : Γ) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ') := by
    rw [Subgroup.quotientEquivProdOfLE_symm_apply]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact Quotient.map'_mk'' _ _ (Quotient.out q)
  rw [hsymm]

  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul Γ' (ζ.out * (q.out : Γ) : SL(2, ℤ))
  have hval : F (gen Γ' (((ζ.out * (q.out : Γ) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ').out)) =
      F (gen Γ' (ζ.out * (q.out : Γ))) := by
    rw [hκ, gen_mul Γ' _ (κ : SL(2, ℤ)) κ.2]
    exact hF' Γ' F hF (gen Γ' (ζ.out * (q.out : Γ))) (gen_mem Γ' _) (κ : SL(2, ℤ)) κ.2
      (trace_gen_sq Γ' _)
  have hζ : ((ζ.out : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ) = ζ := QuotientGroup.out_eq' ζ
  have hq : ((q.out : Γ) : Γ ⧸ K' Γ' Γ) = q := QuotientGroup.out_eq' q
  have h3 : F (gen Γ' (ζ.out * (q.out : Γ))) = F (piElt Γ' Γ (genΔ Γ ζ.out) q : Γ) := by
    rw [gen_mul_eq Γ' Γ hle, hq]
    rfl
  have h4 : (width Γ' ((ζ.out * (q.out : Γ) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ') : ℚ) =
      (width Γ ζ : ℚ) * (minimalPeriod ((genΔ Γ ζ.out) • ·) q : ℚ) := by
    rw [width_mul Γ' Γ hle, hζ, hq, Nat.cast_mul]
  rw [hval, h3, h4, div_div, mul_comm ((width Γ ζ : ℕ) : ℚ)]

include hF hle in

theorem weighted_eq :
    ∑ ζ' : SL(2, ℤ) ⧸ Γ', F (gen Γ' ζ'.out) / (width Γ' ζ' : ℚ) =
      ∑ ζ : SL(2, ℤ) ⧸ Γ, Φ Γ' Γ F (genΔ Γ ζ.out) / (width Γ ζ : ℚ) := by
  rw [← (Subgroup.quotientEquivProdOfLE hle).symm.sum_comp, Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ (fun ζ => ?_)
  rw [Φ, Finset.sum_div]
  exact Fintype.sum_congr _ _ (fun q => summand_eq Γ' Γ hle F hF ζ q)

include hF hle in
theorem main :
    cuspSum Γ' (fun γ => F γ) =
      ∑ Q : Cusp Γ, ∑ᶠ O : orbitRel.Quotient (Subgroup.zpowers (cuspGen Γ Q)) (Γ ⧸ K' Γ' Γ),
        F ((O.out.out⁻¹ * cuspGen Γ Q ^ minimalPeriod (cuspGen Γ Q • ·) O.out * O.out.out : Γ) :
          SL(2, ℤ)) := by
  rw [lhs_eq Γ' F hF, weighted_eq Γ' Γ hle F hF, rhs_eq Γ' Γ F hF]

end Main

end ModularCurve.CupPairing.CuspDecomp
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le.ModularCurve P2MW.S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le.ModularCurve.CupPairing P2MW.S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le.ModularCurve.CupPairing.CuspDecomp"
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le.ModularCurve P2MW.S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le.ModularCurve.CupPairing"
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le.ModularCurve"

theorem solution (Γ' Γ : Subgroup SL(2, ℤ))
    [Γ'.FiniteIndex] [Γ.FiniteIndex] (hle : Γ' ≤ Γ) (F : SL(2, ℤ) → ℚ)
    (hF : ∀ p ∈ Γ', ∀ δ ∈ Γ', (p : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
      F (δ * p * δ⁻¹) = F p) :
    ModularCurve.PDPairing.cuspSum Γ' (fun γ => F γ) =
      ∑ Q : ModularCurve.PDPairing.Cusp Γ,
        ∑ᶠ O : MulAction.orbitRel.Quotient
            (Subgroup.zpowers (ModularCurve.PDPairing.cuspGen Γ Q)) (Γ ⧸ Γ'.subgroupOf Γ),
          F ((O.out.out⁻¹ * ModularCurve.PDPairing.cuspGen Γ Q ^
              Function.minimalPeriod (ModularCurve.PDPairing.cuspGen Γ Q • ·) O.out *
              O.out.out : Γ) : SL(2, ℤ)) :=
  ModularCurve.CupPairing.CuspDecomp.main Γ' Γ hle F hF

end S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le
end P2MW
export P2MW.S_ModularCurve_CupPairing_cuspSum_eq_sum_finsum_of_le (solution)
