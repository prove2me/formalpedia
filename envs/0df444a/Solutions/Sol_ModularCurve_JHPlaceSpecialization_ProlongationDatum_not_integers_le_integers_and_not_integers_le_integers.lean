-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.not_integers_le_integers_and_not_integers_le_integers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/7f036554-9063-545a-bc63-667b861e3a73

import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_Correspondence

import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_residue_alpha_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_not_integers_le_integers_and_not_integers_le_integers

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace Ws47
namespace OrderH1

open AlgebraicCurve IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem isUnit_mk_iff {K : Type*} [Field K] (S : ValuationSubring K) {y : K} (hy : y ∈ S) (hy0 : y ≠ 0) :
    IsUnit (⟨y, hy⟩ : S) ↔ y⁻¹ ∈ S := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have hb' : y * (b : K) = 1 := by
      have := congrArg (fun t : S => (t : K)) hb
      simpa using this
    have : (b : K) = y⁻¹ := eq_inv_of_mul_eq_one_right hb'
    rw [← this]; exact b.2
  · intro h
    exact isUnit_iff_exists_inv.mpr ⟨⟨y⁻¹, h⟩, Subtype.ext (by simp [mul_inv_cancel₀ hy0])⟩

theorem residue_eq_zero_iff (R : RegularProlongation A F Fb) (y : R.integers) :
    R.residue y = 0 ↔ ¬ IsUnit y := by
  constructor
  · intro h hu; exact R.residue_ne_zero_of_isUnit hu h
  · intro h; by_contra h0; exact h (R.isUnit_of_residue_ne_zero h0)

theorem integers_eq_of_le {Fb₂ : Type*} [Field Fb₂] [Algebra (ResidueField A) Fb₂]
    (S : RegularProlongation A F Fb) (T : RegularProlongation A F Fb₂)
    (h : S.integers ≤ T.integers) : S.integers = T.integers := by
  refine le_antisymm h ?_
  intro y hyT
  by_contra hyS
  have hy0 : y ≠ 0 := fun h0 => hyS (h0 ▸ zero_mem _)
  have hyiS : y⁻¹ ∈ S.integers := (S.integers.mem_or_inv_mem y).resolve_left hyS
  obtain ⟨c, hcy, hres⟩ := S.exists_smul_mem y hy0
  have hc0 : c ≠ 0 := S.smul_const_ne_zero hcy hres
  have hcy0 : c • y ≠ 0 := smul_ne_zero hc0 hy0
  have hunit : IsUnit (⟨c • y, hcy⟩ : S.integers) := S.isUnit_of_residue_ne_zero hres
  have hcyiS : (c • y)⁻¹ ∈ S.integers := (isUnit_mk_iff S.integers hcy hcy0).mp hunit
  have hcS : algebraMap L F c ∈ S.integers := by
    have e : algebraMap L F c = (c • y) * y⁻¹ := by
      rw [Algebra.smul_def, mul_assoc, mul_inv_cancel₀ hy0, mul_one]
    rw [e]; exact mul_mem hcy hyiS
  have hcA : c ∈ A := (S.algebraMap_mem_iff c).mp hcS
  have hciT : algebraMap L F c⁻¹ ∈ T.integers := by
    have e : algebraMap L F c⁻¹ = y * (c • y)⁻¹ := by
      rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_comm y, mul_assoc, mul_inv_cancel₀ hy0, mul_one, map_inv₀]
    rw [e]; exact mul_mem hyT (h hcyiS)
  have hciA : c⁻¹ ∈ A := (T.algebraMap_mem_iff c⁻¹).mp hciT
  have hciS : algebraMap L F c⁻¹ ∈ S.integers := (S.algebraMap_mem_iff c⁻¹).mpr hciA
  apply hyS
  have e : y = algebraMap L F c⁻¹ * (c • y) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  rw [e]; exact mul_mem hciS hcy

end Ws47.OrderH1

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))
    (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ¬ Rpd.R₁.integers ≤ Rpd.R₂.integers ∧ ¬ Rpd.R₂.integers ≤ Rpd.R₁.integers := by

  have hcoeαx : ((α x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hα_coe, hx]
  have hyA : coeffMap A.subtype (jqModC ↥A) = jqModC (AlgebraicClosure ℚ) := coeffMap_jqModC _
  have hymem : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by
    rw [hyA, ← hcoeαx]; exact (α x).2
  obtain ⟨hj₁', hres₁'⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hymem
  have heqαx : (⟨coeffMap A.subtype (jqModC ↥A), hymem⟩ : ↥(xHFunctionFieldBar M H)) = α x :=
    Subtype.ext (show coeffMap A.subtype (jqModC ↥A) = ((α x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) by
      rw [hyA, hcoeαx])
  have hj₁ : α x ∈ Rpd.R₁.integers := heqαx ▸ hj₁'
  have hres₁ser : ((Rpd.R₁.residue ⟨α x, hj₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
    have : (⟨α x, hj₁⟩ : ↥Rpd.R₁.integers) = ⟨_, hj₁'⟩ := Subtype.ext heqαx.symm
    rw [this, hres₁', coeffMap_jqModC]

  have hne : Rpd.R₁.integers ≠ Rpd.R₂.integers := by
    intro heqR
    have hsurj : Function.Surjective
        (qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) := by
      intro b
      obtain ⟨⟨y, hy₂⟩, rfl⟩ := Rpd.R₂.residue_surjective b
      have hy₁ : y ∈ Rpd.R₁.integers := heqR ▸ hy₂
      obtain ⟨v, hv₁, hva⟩ :=
        ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_residue_alpha_eq
          p M H hpM hpM2 A hA θ α hα_coe Psp Rpd (Rpd.R₁.residue ⟨y, hy₁⟩)
      have hv₂ : α v ∈ Rpd.R₂.integers := heqR ▸ hv₁
      refine ⟨Rpd.R₁.residue ⟨α v, hv₁⟩, ?_⟩
      rw [← hres₂α v hv₁ hv₂]

      have hd₁ : y - α v ∈ Rpd.R₁.integers := sub_mem hy₁ hv₁
      have hd₂ : y - α v ∈ Rpd.R₂.integers := sub_mem hy₂ hv₂
      have hresd₁ : Rpd.R₁.residue ⟨y - α v, hd₁⟩ = 0 := by
        have : (⟨y - α v, hd₁⟩ : ↥Rpd.R₁.integers) = ⟨y, hy₁⟩ - ⟨α v, hv₁⟩ := rfl
        rw [this, map_sub, hva, sub_self]
      have hresd₂ : Rpd.R₂.residue ⟨y - α v, hd₂⟩ = 0 := by
        by_cases hd0 : y - α v = 0
        · have : (⟨y - α v, hd₂⟩ : ↥Rpd.R₂.integers) = 0 := Subtype.ext hd0
          rw [this, map_zero]
        · have hnu₁ : ¬ IsUnit (⟨y - α v, hd₁⟩ : ↥Rpd.R₁.integers) :=
            (Ws47.OrderH1.residue_eq_zero_iff Rpd.R₁ _).mp hresd₁
          have hinv : (y - α v)⁻¹ ∉ Rpd.R₂.integers := by
            rw [← heqR]
            exact fun hmem => hnu₁ ((Ws47.OrderH1.isUnit_mk_iff Rpd.R₁.integers hd₁ hd0).mpr hmem)
          have hnu₂ : ¬ IsUnit (⟨y - α v, hd₂⟩ : ↥Rpd.R₂.integers) :=
            fun hu => hinv ((Ws47.OrderH1.isUnit_mk_iff Rpd.R₂.integers hd₂ hd0).mp hu)
          exact (Ws47.OrderH1.residue_eq_zero_iff Rpd.R₂ _).mpr hnu₂
      have : (⟨y, hy₂⟩ : ↥Rpd.R₂.integers) = ⟨y - α v, hd₂⟩ + ⟨α v, hv₂⟩ := Subtype.ext (by simp)
      rw [this, map_add, hresd₂, zero_add]

    obtain ⟨a, ha⟩ := hsurj (Rpd.R₁.residue ⟨α x, hj₁⟩)
    have hser := congrArg (fun t : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) => (t : LaurentSeries (ResidueField ↥A)).coeff (-1 : ℤ)) ha
    simp only [coe_qExpFrobeniusModL, hres₁ser] at hser
    rw [coeff_jqModC_neg_one, qExpand_coeff_of_not_dvd] at hser
    · exact zero_ne_one hser
    ·
      intro hdvd
      have h1 : (p : ℤ) ∣ 1 := (Int.dvd_neg).mp hdvd
      have hp : p = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le p)) h1
      exact (Fact.out : p.Prime).one_lt.ne' hp

  exact ⟨fun hle => hne (Ws47.OrderH1.integers_eq_of_le Rpd.R₁ Rpd.R₂ hle),
    fun hle => hne (Ws47.OrderH1.integers_eq_of_le Rpd.R₂ Rpd.R₁ hle).symm⟩

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_not_integers_le_integers_and_not_integers_le_integers
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_not_integers_le_integers_and_not_integers_le_integers (solution)
