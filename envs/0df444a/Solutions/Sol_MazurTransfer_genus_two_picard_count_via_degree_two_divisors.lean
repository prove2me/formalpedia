-- Prove2me | solution 1 for MazurTransfer.genus_two_picard_count_via_degree_two_divisors
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T00:09:30.07599+00:00
-- url     : https://prove2.me/submissions/410b7800-ed8a-422b-9258-a6aad0c47393

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Generic divisor and Riemann--Roch APIs reuse official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, with attribution retained.
Design boundary: a complete finite-field genus-two divisor-class count from
Riemann--Roch and the complete effective linear-equivalence fibres.
Named downstream consumer: the literal order-13 F3/F5 arithmetic Picard counts
and actual represented Picard point counts in the MazurTheorem campaign.
No algebraic closure, rational place, supplied Picard cardinality, or rational
rank hypothesis is used. Finiteness of the effective divisor set is explicit.
-/
import Mathlib.FieldTheory.Perfect
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_Divisor_degree_nonneg_of_nonneg
import Theorems.Thm_AlgebraicCurve_card_effective_sub_isPrincipal_of_finite
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_add
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

namespace MazurTransfer.PublicGenusTwoPicardCountingHelpers
noncomputable section
open AlgebraicCurve
namespace MazurTransfer.DegreeTwoEffectiveRepresentatives
universe u

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem effective_representative_of_ell_pos [HasPrincipalDivisors K F]
    (D : Divisor K F) [FiniteDimensional K ↥(LSpace D)] (h : 0 < ell D) :
    ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧ Divisor.degree E = Divisor.degree D ∧
      Divisor.IsPrincipal (E - D) := by
  obtain ⟨f, hf⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := ↥(LSpace D))).mp h
  have hf0 : (f : F) ≠ 0 := by
    intro hz
    apply hf
    exact Subtype.ext hz
  have horder := (mem_lSpace_iff_ord (D := D) (f := (f : F))).mp f.property
  have hbound : ∀ v : Place K F, -D v ≤ v.ord (f : F) := horder.resolve_left hf0
  obtain ⟨P, hP, hdegP⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) (f : F) hf0
  refine ⟨D + P, ?_, ?_, ?_⟩
  · intro v
    rw [Finsupp.add_apply, hP v]
    linarith [hbound v]
  · rw [map_add, hdegP, add_zero]
  · refine ⟨(f : F), hf0, ?_⟩
    intro v
    simpa only [add_sub_cancel_left] using hP v

theorem effective_representative_of_genus_two_riemannRoch [HasPrincipalDivisors K F]
    (D : Divisor K F) (hdeg : Divisor.degree D = 2)
    (hRR : FiniteDimensional K ↥(LSpace D) ∧ Module.Finite K (H1 D) ∧
      (ell D : ℤ) - (Module.finrank K (H1 D) : ℤ) = Divisor.degree D - 1) :
    ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧ Divisor.degree E = 2 ∧
      Divisor.IsPrincipal (E - D) := by
  let : FiniteDimensional K ↥(LSpace D) := hRR.1
  have hpos : 0 < ell D := by
    have heq := hRR.2.2
    rw [hdeg] at heq
    omega
  obtain ⟨E, heff, hE, heq⟩ := effective_representative_of_ell_pos D hpos
  exact ⟨E, heff, hE.trans hdeg, heq⟩

theorem effective_representative_of_canonical_genus_two
    {K F : Type u} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hconst : ConstantsAreBase K F) (hgen : genusFF K F = 2)
    (D : Divisor K F) (hdeg : Divisor.degree D = 2) :
    ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧ Divisor.degree E = 2 ∧ Divisor.IsPrincipal (E - D) := by
  obtain ⟨hp, hf, γ, D₀, hg⟩ := stichtenothGenusExists_of_isCurveOver hconst
  letI := hp
  letI := hf
  letI : FiniteDimensional K ↥(LSpace D) := _root_.AlgebraicCurve.finiteDimensional_lSpace D
  obtain ⟨W, hRR⟩ := exists_weilCanonical_riemannRoch K F hconst
  have h := hRR D
  rw [hgen, hdeg] at h
  obtain ⟨E, heff, hE, hp⟩ := effective_representative_of_ell_pos D (by omega)
  exact ⟨E, heff, hE.trans hdeg, hp⟩

end MazurTransfer.DegreeTwoEffectiveRepresentatives
end

noncomputable section
open AlgebraicCurve
namespace MazurTransfer.DegreeZeroDivisorSpaces
universe u
variable {K F : Type u} [Field K] [Field F] [Algebra K F]

-- This multiplication equivalence is the complete selected original FLT
-- ell_add_eq_of_ord_eq proof, with its namespace normalized.
theorem ell_add_eq_of_ord_eq {z : F} (hz : z ≠ 0) {P : Divisor K F}
    (hP : ∀ v, P v = v.ord z) (A : Divisor K F) : ell (A + P) = ell A := by
  have h1 : ∀ f : F, f ∈ LSpace (A + P) → f * z ∈ LSpace A := fun f hf => by
    have hzL : z ∈ LSpace (-P) := by
      rw [mem_lSpace_iff_ord]
      exact Or.inr fun v => by simp [hP v]
    have := mul_mem_lSpace_add hf hzL
    rwa [add_neg_cancel_right] at this
  have h2 : ∀ g : F, g ∈ LSpace A → g * z⁻¹ ∈ LSpace (A + P) := fun g hg => by
    have hzL : z⁻¹ ∈ LSpace P := by
      rw [mem_lSpace_iff_ord]
      exact Or.inr fun v => by simp [Place.ord_inv, hP v]
    exact mul_mem_lSpace_add hg hzL
  let e : LSpace (A + P) ≃ₗ[K] LSpace A :=
    { toFun := fun f => ⟨f.1 * z, h1 f.1 f.2⟩
      map_add' := fun f g => by ext; simp [add_mul]
      map_smul' := fun c f => by ext; simp
      invFun := fun g => ⟨g.1 * z⁻¹, h2 g.1 g.2⟩
      left_inv := fun f => by ext; simp [mul_inv_cancel_right₀ hz]
      right_inv := fun g => by ext; simp [inv_mul_cancel_right₀ hz] }
  exact e.finrank_eq

theorem effective_degree_zero_eq_zero [IsCurveOver K F] (E : Divisor K F)
    (hE : ∀ v, 0 ≤ E v) (hdeg : Divisor.degree E = 0) : E = 0 := by
  classical
  by_contra hE0
  obtain ⟨v, hv⟩ : ∃ v, E v ≠ 0 := by
    by_contra h
    push Not at h
    exact hE0 (Finsupp.ext h)
  have hEv : 1 ≤ E v := by have := hE v; omega
  have hsplit : E = Finsupp.single v (E v) + Finsupp.erase v E :=
    (Finsupp.single_add_erase v E).symm
  have herase : ∀ w, 0 ≤ Finsupp.erase v E w := by
    intro w
    rw [Finsupp.erase_apply]
    split_ifs
    · exact le_rfl
    · exact hE w
  have hrest := Divisor.degree_nonneg_of_nonneg herase
  let : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
  have hpos : 0 < v.deg := Module.finrank_pos
  have hcast : 1 ≤ (v.deg : ℤ) := by exact_mod_cast hpos
  rw [hsplit, map_add, Divisor.degree_single] at hdeg
  nlinarith

theorem ell_pos_principal [IsCurveOver K F] (D : Divisor K F)
    [FiniteDimensional K ↥(LSpace D)] (hdeg : Divisor.degree D = 0)
    (hpos : 0 < ell D) : Divisor.IsPrincipal D := by
  obtain ⟨E, heff, hE, hprincipal⟩ :=
    DegreeTwoEffectiveRepresentatives.effective_representative_of_ell_pos D hpos
  have hzero := effective_degree_zero_eq_zero E heff (hE.trans hdeg)
  rw [hzero, zero_sub] at hprincipal
  have hneg : -D ∈ Divisor.principal (K := K) (F := F) := hprincipal
  have h := (Divisor.principal (K := K) (F := F)).neg_mem hneg
  apply Divisor.mem_principal.mp
  simpa only [neg_neg] using h

theorem ell_principal (hC : ConstantsAreBase K F) (D : Divisor K F)
    (hD : Divisor.IsPrincipal D) : ell D = 1 := by
  obtain ⟨z, hz, hP⟩ := hD
  have h := ell_add_eq_of_ord_eq hz hP (0 : Divisor K F)
  simpa only [zero_add, ell_zero_eq_one_of_constantsAreBase hC] using h

theorem ell_zero_of_nonprincipal [IsCurveOver K F] (D : Divisor K F)
    [FiniteDimensional K ↥(LSpace D)] (hdeg : Divisor.degree D = 0)
    (hD : ¬Divisor.IsPrincipal D) : ell D = 0 := by
  by_contra h
  exact hD (ell_pos_principal D hdeg (Nat.pos_of_ne_zero h))


end MazurTransfer.DegreeZeroDivisorSpaces
end

noncomputable section
open AlgebraicCurve
namespace MazurTransfer.CanonicalDegreeTwoFibres
open DegreeZeroDivisorSpaces
universe u
variable {K F : Type u} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]

theorem all_lSpace_finite (hC : ConstantsAreBase K F) (D : Divisor K F) :
    FiniteDimensional K ↥(LSpace D) := by
  obtain ⟨hplaces, hfinite, γ, D₀, hgenus⟩ := stichtenothGenusExists_of_isCurveOver hC
  letI := hplaces
  letI := hfinite
  exact _root_.AlgebraicCurve.finiteDimensional_lSpace D

theorem genus_two_canonical_ell_dichotomy (hC : ConstantsAreBase K F)
    (hgen : genusFF K F = 2) :
    ∃ W : Divisor K F, Divisor.degree W = 2 ∧ ell W = 2 ∧
      ∀ D : Divisor K F, Divisor.degree D = 2 →
        (Divisor.IsPrincipal (W - D) → ell D = 2) ∧
        (¬Divisor.IsPrincipal (W - D) → ell D = 1) := by
  obtain ⟨W, hRR⟩ := exists_weilCanonical_riemannRoch K F hC
  have h0 := hRR 0
  have hW := hRR W
  have hconstant := ell_zero_eq_one_of_constantsAreBase hC
  rw [hgen, hconstant, sub_zero, map_zero] at h0
  have hellW : ell W = 2 := by omega
  rw [hgen, sub_self, hconstant, hellW] at hW
  have hdegW : Divisor.degree W = 2 := by omega
  refine ⟨W, hdegW, hellW, ?_⟩
  intro D hdegD
  have hdeg0 : Divisor.degree (W - D) = 0 := by rw [map_sub, hdegW, hdegD, sub_self]
  let : FiniteDimensional K ↥(LSpace (W - D)) := all_lSpace_finite hC _
  have h := hRR D
  rw [hgen, hdegD] at h
  constructor
  · intro hp
    have he := ell_principal hC (W - D) hp
    omega
  · intro hp
    have he := ell_zero_of_nonprincipal (W - D) hdeg0 hp
    omega

abbrev EffectiveClassFibre (D : Divisor K F) :=
  {E : Divisor K F // 0 ≤ E ∧ Divisor.IsPrincipal (E - D)}

theorem fibre_card_one [Finite K] (hC : ConstantsAreBase K F)
    (D : Divisor K F) (hD : ell D = 1) : Nat.card (EffectiveClassFibre D) = 1 := by
  have h := card_effective_sub_isPrincipal_of_finite K F hC D
  rw [hD, pow_one] at h
  have hq : 2 ≤ Nat.card K := by
    let : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Nat.succ_le_of_lt (Fintype.one_lt_card (α := K))
  change (Nat.card K - 1) * Nat.card (EffectiveClassFibre D) + 1 = Nat.card K at h
  nlinarith [Nat.sub_add_cancel (show 1 ≤ Nat.card K by omega)]

theorem fibre_card_canonical [Finite K] (hC : ConstantsAreBase K F)
    (D : Divisor K F) (hD : ell D = 2) :
    Nat.card (EffectiveClassFibre D) = Nat.card K + 1 := by
  have h := card_effective_sub_isPrincipal_of_finite K F hC D
  rw [hD, pow_two] at h
  have hq : 2 ≤ Nat.card K := by
    let : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Nat.succ_le_of_lt (Fintype.one_lt_card (α := K))
  change (Nat.card K - 1) * Nat.card (EffectiveClassFibre D) + 1 = Nat.card K * Nat.card K at h
  nlinarith [Nat.sub_add_cancel (show 1 ≤ Nat.card K by omega)]


end MazurTransfer.CanonicalDegreeTwoFibres
end

noncomputable section
open AlgebraicCurve
namespace MazurTransfer.Order13EffectiveDegreeTwoDivisorCounts
universe u
abbrev EffectiveDegreeTwo (K F : Type u) [Field K] [Field F] [Algebra K F] :=
  {D : Divisor K F // (∀ v, 0 ≤ D v) ∧ Divisor.degree D = 2}
end MazurTransfer.Order13EffectiveDegreeTwoDivisorCounts
end

noncomputable section
open AlgebraicCurve
namespace MazurTransfer.EffectiveDivisorPicardSurjection
open DegreeTwoEffectiveRepresentatives Order13EffectiveDegreeTwoDivisorCounts
universe u
variable {K F : Type u} [Field K] [Field F] [Algebra K F]

def effectiveToPic0 (B : Divisor K F) (hB : Divisor.degree B = 2)
    (E : EffectiveDegreeTwo K F) : Pic0 K F :=
  Pic0.mk ⟨E.val - B, by
    rw [Divisor.mem_degZero, map_sub, E.property.2, hB, sub_self]⟩

theorem effectiveToPic0_surjective (B : Divisor K F) (hB : Divisor.degree B = 2)
    (hrep : ∀ D : Divisor K F, Divisor.degree D = 2 →
      ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧ Divisor.degree E = 2 ∧
        Divisor.IsPrincipal (E - D)) :
    Function.Surjective (effectiveToPic0 B hB) := by
  intro z
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  have hdeg : Divisor.degree ((D : Divisor K F) + B) = 2 := by
    rw [map_add, (Divisor.mem_degZero.mp D.property), hB, zero_add]
  obtain ⟨E, heff, hE, hprincipal⟩ := hrep ((D : Divisor K F) + B) hdeg
  refine ⟨⟨E, heff, hE⟩, ?_⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change Divisor.IsPrincipal ((E - B) - (D : Divisor K F))
  convert hprincipal using 1 <;> abel

theorem pic0_card_le_effective_two [Finite (EffectiveDegreeTwo K F)]
    (B : Divisor K F) (hB : Divisor.degree B = 2)
    (hrep : ∀ D : Divisor K F, Divisor.degree D = 2 →
      ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧ Divisor.degree E = 2 ∧
        Divisor.IsPrincipal (E - D)) :
    Nat.card (Pic0 K F) ≤ Nat.card (EffectiveDegreeTwo K F) :=
  Nat.card_le_card_of_surjective _ (effectiveToPic0_surjective B hB hrep)


end MazurTransfer.EffectiveDivisorPicardSurjection
end

noncomputable section
open AlgebraicCurve
namespace MazurTransfer.PicardDegreeTwoFibreCardinality
open CanonicalDegreeTwoFibres Order13EffectiveDegreeTwoDivisorCounts EffectiveDivisorPicardSurjection
universe u
variable {K F : Type u} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]

theorem principal_degree_eq {D E : Divisor K F} (h : Divisor.IsPrincipal (D - E)) :
    Divisor.degree D = Divisor.degree E := by
  obtain ⟨f, hf, hord⟩ := h
  obtain ⟨P, hP, hdegP⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
  have hPE : P = D - E := Finsupp.ext fun v => (hP v).trans (hord v).symm
  rw [hPE, map_sub] at hdegP
  omega

def degreeTwoClass (W : Divisor K F) (hW : Divisor.degree W = 2)
    (C : Divisor K F) (hC : Divisor.degree C = 2) : Pic0 K F :=
  Pic0.mk ⟨C - W, by rw [Divisor.mem_degZero, map_sub, hC, hW, sub_self]⟩

theorem degreeTwoClass_eq_zero (W : Divisor K F) (hW : Divisor.degree W = 2)
    (C : Divisor K F) (hC : Divisor.degree C = 2) :
    degreeTwoClass W hW C hC = 0 ↔ Divisor.IsPrincipal (W - C) := by
  rw [degreeTwoClass, Pic0.mk, QuotientAddGroup.eq_zero_iff]
  change Divisor.IsPrincipal (C - W) ↔ Divisor.IsPrincipal (W - C)
  constructor <;> intro h
  · have hn := (Divisor.principal (K := K) (F := F)).neg_mem h
    apply Divisor.mem_principal.mp
    simpa only [neg_sub] using hn
  · have hn := (Divisor.principal (K := K) (F := F)).neg_mem h
    apply Divisor.mem_principal.mp
    simpa only [neg_sub] using hn

def effectiveFibreEquivClass (W : Divisor K F) (hW : Divisor.degree W = 2)
    (C : Divisor K F) (hC : Divisor.degree C = 2) :
    {E : EffectiveDegreeTwo K F // effectiveToPic0 W hW E = degreeTwoClass W hW C hC} ≃
      EffectiveClassFibre C where
  toFun E := ⟨E.val.val, Finsupp.le_def.mpr E.val.property.1, by
    have h := QuotientAddGroup.eq_iff_sub_mem.mp E.property
    change Divisor.IsPrincipal ((E.val.val - W) - (C - W)) at h
    convert h using 1 <;> abel⟩
  invFun E := by
    let e : EffectiveDegreeTwo K F :=
      ⟨E.val, Finsupp.le_def.mp E.property.1, (principal_degree_eq E.property.2).trans hC⟩
    refine ⟨e, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change Divisor.IsPrincipal ((E.val - W) - (C - W))
    convert E.property.2 using 1 <;> abel
  left_inv E := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv E := by apply Subtype.ext; rfl

theorem effective_card_eq_pic0_add_base_card [Finite K] [Finite (EffectiveDegreeTwo K F)]
    (hconst : ConstantsAreBase K F) (hgen : genusFF K F = 2)
    (hrep : ∀ D : Divisor K F, Divisor.degree D = 2 →
      ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧ Divisor.degree E = 2 ∧
        Divisor.IsPrincipal (E - D)) :
    Nat.card (EffectiveDegreeTwo K F) = Nat.card (Pic0 K F) + Nat.card K := by
  classical
  obtain ⟨W, hW, hellW, hdich⟩ := genus_two_canonical_ell_dichotomy hconst hgen
  let f := effectiveToPic0 W hW
  have hsurj : Function.Surjective f := effectiveToPic0_surjective W hW hrep
  let : Finite (Pic0 K F) := Finite.of_surjective f hsurj
  let : Fintype (Pic0 K F) := Fintype.ofFinite _
  let : Fintype (EffectiveDegreeTwo K F) := Fintype.ofFinite _
  let : ∀ z : Pic0 K F, Fintype {E : EffectiveDegreeTwo K F // f E = z} := fun _ => Fintype.ofFinite _
  have hfib : ∀ z : Pic0 K F,
      Nat.card {E : EffectiveDegreeTwo K F // f E = z} =
        1 + if z = 0 then Nat.card K else 0 := by
    intro z
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
    let C := (D : Divisor K F) + W
    have hC : Divisor.degree C = 2 := by
      rw [map_add, Divisor.mem_degZero.mp D.property, hW, zero_add]
    have hclass : degreeTwoClass W hW C hC = Pic0.mk D := by
      unfold degreeTwoClass C
      apply congrArg Pic0.mk
      apply Subtype.ext
      simp only [add_sub_cancel_right]
    have heq : Nat.card {E : EffectiveDegreeTwo K F // f E = Pic0.mk D} =
        Nat.card (EffectiveClassFibre C) := by
      rw [← hclass]
      exact Nat.card_congr (effectiveFibreEquivClass W hW C hC)
    rw [heq]
    by_cases hz : Pic0.mk D = 0
    · have hp : Divisor.IsPrincipal (W - C) := (degreeTwoClass_eq_zero W hW C hC).mp (hclass.trans hz)
      rw [fibre_card_canonical hconst C ((hdich C hC).1 hp), if_pos hz]
      omega
    · have hp : ¬Divisor.IsPrincipal (W - C) := by
        intro hp
        exact hz (hclass.symm.trans ((degreeTwoClass_eq_zero W hW C hC).mpr hp))
      rw [fibre_card_one hconst C ((hdich C hC).2 hp), if_neg hz, add_zero]
  calc
    Nat.card (EffectiveDegreeTwo K F) = ∑ z : Pic0 K F,
        Nat.card {E : EffectiveDegreeTwo K F // f E = z} := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp only [Nat.card_eq_fintype_card]
    _ = ∑ z : Pic0 K F, (1 + if z = 0 then Nat.card K else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hfib z
    _ = Nat.card (Pic0 K F) + Nat.card K := by
      simp [Finset.sum_add_distrib, Nat.card_eq_fintype_card]


end MazurTransfer.PicardDegreeTwoFibreCardinality
end

end MazurTransfer.PublicGenusTwoPicardCountingHelpers

open AlgebraicCurve
universe u
theorem solution
    (K F : Type u) [Field K] [Finite K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    [Finite {D : AlgebraicCurve.Divisor K F //
      (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2}]
    (hconst : AlgebraicCurve.ConstantsAreBase K F)
    (hgen : AlgebraicCurve.genusFF K F = 2) :
    Finite (AlgebraicCurve.Pic0 K F) ∧
      Nat.card {D : AlgebraicCurve.Divisor K F //
        (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2} =
        Nat.card (AlgebraicCurve.Pic0 K F) + Nat.card K := by
  have hrep :=
    MazurTransfer.PublicGenusTwoPicardCountingHelpers.MazurTransfer.DegreeTwoEffectiveRepresentatives.effective_representative_of_canonical_genus_two
      hconst hgen
  obtain ⟨W, hW, _, _⟩ :=
    MazurTransfer.PublicGenusTwoPicardCountingHelpers.MazurTransfer.CanonicalDegreeTwoFibres.genus_two_canonical_ell_dichotomy
      hconst hgen
  let f :=
    MazurTransfer.PublicGenusTwoPicardCountingHelpers.MazurTransfer.EffectiveDivisorPicardSurjection.effectiveToPic0 W hW
  have hsurj : Function.Surjective f :=
    MazurTransfer.PublicGenusTwoPicardCountingHelpers.MazurTransfer.EffectiveDivisorPicardSurjection.effectiveToPic0_surjective
      W hW hrep
  have hfinite : Finite (AlgebraicCurve.Pic0 K F) := Finite.of_surjective f hsurj
  exact ⟨hfinite,
    MazurTransfer.PublicGenusTwoPicardCountingHelpers.MazurTransfer.PicardDegreeTwoFibreCardinality.effective_card_eq_pic0_add_base_card
      hconst hgen hrep⟩

#print axioms solution
