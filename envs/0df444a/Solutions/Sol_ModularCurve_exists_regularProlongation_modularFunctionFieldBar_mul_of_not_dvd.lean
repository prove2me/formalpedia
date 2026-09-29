-- Prove2me | solution 1 for ModularCurve.exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/17def9c1-3691-5558-b965-96355701c72e

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_exists_algEquiv_modularFunctionFieldBar_atkinLehner
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical
open IntermediateField AlgebraicCurve ModularCurve Polynomial

namespace W7NQG

section Coeff

variable {L : Type*} [Field L] (A : ValuationSubring L)

abbrev ι : LaurentSeries A →+* LaurentSeries L := coeffMap A.subtype

abbrev ϖ : LaurentSeries A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
  coeffMap (IsLocalRing.residue A)

theorem ι_injective : Function.Injective (ι A) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries L => s.coeff n) h
  simp only [coeffMap_coeff] at h1
  exact h1

theorem ι_eq_zero_iff (x : LaurentSeries A) : ι A x = 0 ↔ x = 0 := by
  rw [← map_zero (ι A)]; exact (ι_injective A).eq_iff

theorem ϖ_eq_zero_iff (y : LaurentSeries A) :
    ϖ A y = 0 ↔ ∀ n, y.coeff n ∈ IsLocalRing.maximalIdeal A := by
  constructor
  · intro h n
    have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    exact (IsLocalRing.residue_eq_zero_iff _).mp h1
  · intro h
    ext n
    simp only [coeffMap_coeff, HahnSeries.coeff_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (h n)

theorem ι_C (a : A) : ι A (HahnSeries.C a) = algebraMap L (LaurentSeries L) (a : L) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]; rfl

theorem ϖ_C (a : A) : ϖ A (HahnSeries.C a) =
    algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
      (IsLocalRing.residue A a) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]

def IsInt (f : LaurentSeries L) : Prop :=
  ∃ x y : LaurentSeries A, ϖ A y ≠ 0 ∧ f * ι A y = ι A x

variable {A}

theorem ϖ_ne_zero_ne_zero {y : LaurentSeries A} (hy : ϖ A y ≠ 0) : y ≠ 0 := by
  rintro rfl; exact hy (map_zero _)

theorem IsInt.zero : IsInt A (0 : LaurentSeries L) := ⟨0, 1, by simp, by simp⟩

theorem IsInt.one : IsInt A (1 : LaurentSeries L) := ⟨1, 1, by simp, by simp⟩

theorem IsInt.mul {f g : LaurentSeries L} (hf : IsInt A f) (hg : IsInt A g) : IsInt A (f * g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * x', y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.add {f g : LaurentSeries L} (hf : IsInt A f) (hg : IsInt A g) : IsInt A (f + g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * y' + x' * y, y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_add, map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.neg {f : LaurentSeries L} (hf : IsInt A f) : IsInt A (-f) := by
  obtain ⟨x, y, hy, h⟩ := hf
  exact ⟨-x, y, hy, by rw [map_neg, ← h]; ring⟩

theorem IsInt.cross {f : LaurentSeries L} {x y x' y' : LaurentSeries A}
    (h : f * ι A y = ι A x) (h' : f * ι A y' = ι A x') : x * y' = x' * y := by
  apply ι_injective A
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.inv_of {f : LaurentSeries L} {x y : LaurentSeries A} (hx : ϖ A x ≠ 0)
    (h : f * ι A y = ι A x) : f⁻¹ * ι A x = ι A y := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_mul, eq_comm, ι_eq_zero_iff] at h
    exact hx (by rw [h, map_zero])
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]

end Coeff

section Scaling

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem exists_coeffMap_subtype_eq (x : LaurentSeries L) (hx : ∀ n, x.coeff n ∈ A) :
    ∃ y : LaurentSeries A, ι A y = x := by
  refine ⟨⟨fun n => ⟨x.coeff n, hx n⟩, ?_⟩, ?_⟩
  · convert x.isPWO_support' using 1
    ext n
    simp only [Function.mem_support, ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero]
  · ext n
    rfl

theorem valuation_le_of_mem_span (T : Finset L) (c : L) (hc : ∀ t ∈ T, A.valuation t ≤ A.valuation c)
    {x : L} (hx : x ∈ Submodule.span ℤ (T : Set L)) : A.valuation x ≤ A.valuation c := by
  induction hx using Submodule.span_induction with
  | mem x h => exact hc x h
  | zero => simp
  | add x y _ _ hx hy => exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul m x _ hx =>
      rw [zsmul_eq_mul, map_mul]
      calc A.valuation (m : L) * A.valuation x ≤ 1 * A.valuation c :=
            mul_le_mul' ((A.valuation_le_one_iff _).mpr (intCast_mem A m)) hx
        _ = A.valuation c := one_mul _

theorem exists_primitive_scaling {x : LaurentSeries L} (hx : x ≠ 0) (M : Submodule ℤ L) (hM : M.FG)
    (hxM : ∀ n, x.coeff n ∈ M) :
    ∃ c : L, c ≠ 0 ∧ (∀ n, c⁻¹ * x.coeff n ∈ A) ∧ ∃ n₀, c⁻¹ * x.coeff n₀ = 1 := by
  set N' : Submodule ℤ L := Submodule.span ℤ (Set.range x.coeff) with hN'
  have hle : N' ≤ M := Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact hxM n)
  have hfg : N'.FG := (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian M hM)) N' hle
  obtain ⟨T, hTsub, hTspan⟩ : ∃ T : Finset L, (↑T ⊆ Set.range x.coeff) ∧
      Submodule.span ℤ (T : Set L) = N' := by
    obtain ⟨S, hS⟩ := hfg
    have hmem : ∀ s ∈ S, ∃ T : Finset L, ↑T ⊆ Set.range x.coeff ∧
        s ∈ Submodule.span ℤ (T : Set L) := fun s hs =>
      Submodule.mem_span_finite_of_mem_span (by rw [← hN', ← hS]; exact Submodule.subset_span hs)
    choose! Tf hTf₁ hTf₂ using hmem
    refine ⟨S.biUnion Tf, ?_, le_antisymm ?_ ?_⟩
    · simp only [Finset.coe_biUnion, Set.iUnion_subset_iff]
      exact fun s hs => hTf₁ s hs
    · exact Submodule.span_le.mpr fun t ht => by
        obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp ht
        exact Submodule.subset_span (hTf₁ s hs hts)
    · rw [← hS]
      refine Submodule.span_le.mpr fun s hs => ?_
      have h := hTf₂ s hs
      exact Submodule.span_mono (by
        intro t ht
        exact Finset.mem_biUnion.mpr ⟨s, hs, ht⟩) h
  obtain ⟨n₁, hn₁⟩ : ∃ n, x.coeff n ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by ext n; simpa using h n)
  have hcoeffN' : ∀ n, x.coeff n ∈ Submodule.span ℤ (T : Set L) := fun n => by
    rw [hTspan]; exact Submodule.subset_span ⟨n, rfl⟩
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hn₁
    simpa using hcoeffN' n₁
  obtain ⟨c, hcT, hcmax⟩ := Finset.exists_max_image T A.valuation hTne
  have hvx : ∀ n, A.valuation (x.coeff n) ≤ A.valuation c := fun n =>
    valuation_le_of_mem_span A T c hcmax (hcoeffN' n)
  have hc0 : c ≠ 0 := by
    intro hc
    have h := hvx n₁
    rw [hc, map_zero, le_zero_iff, map_eq_zero] at h
    exact hn₁ h
  obtain ⟨n₀, hn₀⟩ := hTsub hcT
  refine ⟨c, hc0, fun n => ?_, n₀, by rw [hn₀, inv_mul_cancel₀ hc0]⟩
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  have hc' : A.valuation c ≠ 0 := by simpa using hc0
  rw [inv_mul_le_one₀ (zero_lt_iff.mpr hc')]
  exact hvx n

theorem exists_primitive_form {x : LaurentSeries L} (hx : x ≠ 0) (M : Submodule ℤ L) (hM : M.FG)
    (hxM : ∀ n, x.coeff n ∈ M) :
    ∃ c : L, c ≠ 0 ∧ ∃ x₀ : LaurentSeries A, ϖ A x₀ ≠ 0 ∧
      x = algebraMap L (LaurentSeries L) c * ι A x₀ := by
  obtain ⟨c, hc0, hcA, n₀, hn₀⟩ := exists_primitive_scaling A hx M hM hxM
  have hcoeff : ∀ n, (algebraMap L (LaurentSeries L) c⁻¹ * x).coeff n = c⁻¹ * x.coeff n := fun n => by
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
  obtain ⟨y, hy⟩ := exists_coeffMap_subtype_eq A (algebraMap L (LaurentSeries L) c⁻¹ * x) fun n => by
    rw [hcoeff]; exact hcA n
  refine ⟨c, hc0, y, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n₀) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    have h2 : (y.coeff n₀ : L) = 1 := by
      have := congrArg (fun s : LaurentSeries L => s.coeff n₀) hy
      simp only [coeffMap_coeff, hcoeff] at this
      rw [← hn₀]; exact this
    have h3 : y.coeff n₀ = 1 := Subtype.ext (by simpa using h2)
    rw [h3, map_one] at h1
    exact one_ne_zero h1
  · rw [hy, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

end Scaling

section Generators

variable (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]

def gens : Set (LaurentSeries L) := ⇑(coeffEmb L) '' divisorExpansions N

theorem adjoin_gens_le : adjoin L (gens L N) ≤ laurentBaseChange L (modularFunctionFieldFull N) := by
  change adjoin L (gens L N) ≤ adjoin L _
  refine adjoin.mono L _ _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, IntermediateField.subset_adjoin ℚ _ hx, rfl⟩

theorem laurentBaseChange_le_adjoin_gens :
    laurentBaseChange L (modularFunctionFieldFull N) ≤ adjoin L (gens L N) := by
  change adjoin L _ ≤ adjoin L (gens L N)
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N) :=
    hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N)).map (coeffEmb L) :=
    ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨z, hz | hz, rfl⟩
  · obtain ⟨c, rfl⟩ := hz
    rw [algebraMap_apply_eq_single]
    change coeffMap (algebraMap ℚ L) (HahnSeries.single 0 c) ∈ adjoin L (gens L N)
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (adjoin L (gens L N)).algebraMap_mem _
  · exact IntermediateField.subset_adjoin L _ ⟨z, hz, rfl⟩

theorem laurentBaseChange_eq_adjoin_gens :
    laurentBaseChange L (modularFunctionFieldFull N) = adjoin L (gens L N) :=
  le_antisymm (laurentBaseChange_le_adjoin_gens L N) (adjoin_gens_le L N)

theorem exists_fg_coeff_mem {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (gens L N)) :
    ∃ M : Submodule ℤ L, M.FG ∧ ∀ n, x.coeff n ∈ M := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨_, ⟨d, hd, hdN, rfl⟩, rfl⟩ := hx
      refine ⟨Submodule.span ℤ {(1 : L)}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      obtain ⟨m, hm⟩ : ∃ m : ℤ, (coeffEmb L (qExpand ℚ d jq)).coeff n = (m : L) := by
        rw [coeffEmb_coeff]
        by_cases hdn : (d : ℤ) ∣ n
        · obtain ⟨n', rfl⟩ := hdn
          refine ⟨(jqModC ℤ).coeff n', ?_⟩
          rw [qExpand_coeff_mul, ← jqModC_rat, coeff_jqModC_eq_intCast, map_intCast]
        · exact ⟨0, by rw [qExpand_coeff_of_not_dvd _ _ hdn, map_zero, Int.cast_zero]⟩
      rw [hm, ← zsmul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  | algebraMap a =>
      refine ⟨Submodule.span ℤ {a}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
      split_ifs
      · exact Submodule.subset_span rfl
      · exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ ⊔ M₂, hM₁.sup hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (h₁ n)) (Submodule.mem_sup_right (h₂ n))
  | mul x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ * M₂, hM₁.mul hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_mul]
      exact Submodule.sum_mem _ fun ij _ => Submodule.mul_mem_mul (h₁ _) (h₂ _)

theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb L (qExpand ℚ d jq) = qExpand L d (jqModC L) := by
  rw [coeffEmb, ← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]

end Generators

section Gauss

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem ι_qExpand_jqModC (d : ℕ) [NeZero d] :
    ι A (qExpand A d (jqModC A)) = qExpand L d (jqModC L) := by
  rw [coeffMap_qExpand, coeffMap_jqModC]

theorem ϖ_qExpand_jqModC (d : ℕ) [NeZero d] :
    ϖ A (qExpand A d (jqModC A)) = qExpand kk d (jqModC kk) := by
  rw [coeffMap_qExpand, coeffMap_jqModC]

theorem qExpand_jqModC_ne_zero (K : Type*) [Field K] (d : ℕ) [NeZero d] :
    qExpand K d (jqModC K) ≠ 0 := fun h =>
  jqModC_ne_zero_of_nontrivial K (qExpand_injective (R := K) (N := d) (by rw [h, map_zero]))

theorem exists_frac_form (f : FF) (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ x₀ y₀ : LaurentSeries A, ϖ A x₀ ≠ 0 ∧ ϖ A y₀ ≠ 0 ∧
      (f : LaurentSeries L) * ι A y₀ = algebraMap L (LaurentSeries L) c * ι A x₀ := by
  have hfF : (f : LaurentSeries L) ∈ adjoin L (gens L N) := laurentBaseChange_le_adjoin_gens L N f.2
  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_adjoin_iff_div (F := L)).mp hfF
  have hf0' : (f : LaurentSeries L) ≠ 0 := fun h => hf (Subtype.ext h)
  have hr0 : r ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, zero_div])
  have hs0 : s ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, div_zero])
  obtain ⟨Mr, hMr, hrM⟩ := exists_fg_coeff_mem L N hr
  obtain ⟨Ms, hMs, hsM⟩ := exists_fg_coeff_mem L N hs
  obtain ⟨cr, hcr, r₀, hr₀, hr'⟩ := exists_primitive_form A hr0 Mr hMr hrM
  obtain ⟨cs, hcs, s₀, hs₀, hs'⟩ := exists_primitive_form A hs0 Ms hMs hsM
  have hιs : ι A s₀ ≠ 0 := by rw [Ne, ι_eq_zero_iff]; exact ϖ_ne_zero_ne_zero hs₀
  refine ⟨cr / cs, div_ne_zero hcr hcs, r₀, s₀, hr₀, hs₀, ?_⟩
  rw [hrs, hr', hs', map_div₀]
  field_simp

def gaussRing : ValuationSubring FF where
  carrier := {f | IsInt A (f : LaurentSeries L)}
  mul_mem' {f g} hf hg := by
    change IsInt A ((f * g : FF) : LaurentSeries L)
    rw [IntermediateField.coe_mul]; exact hf.mul hg
  one_mem' := by change IsInt A ((1 : FF) : LaurentSeries L); exact IsInt.one
  add_mem' {f g} hf hg := by
    change IsInt A ((f + g : FF) : LaurentSeries L)
    rw [IntermediateField.coe_add]; exact hf.add hg
  zero_mem' := by change IsInt A ((0 : FF) : LaurentSeries L); exact IsInt.zero
  neg_mem' {f} hf := by
    change IsInt A ((-f : FF) : LaurentSeries L)
    rw [IntermediateField.coe_neg]; exact hf.neg
  mem_or_inv_mem' f := by
    by_cases hf : f = 0
    · left; subst hf; change IsInt A ((0 : FF) : LaurentSeries L); exact IsInt.zero
    obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h⟩ := exists_frac_form A N f hf
    rcases A.mem_or_inv_mem c with hc | hc
    · left
      refine ⟨HahnSeries.C ⟨c, hc⟩ * x₀, y₀, hy₀, ?_⟩
      rw [h, map_mul, ι_C]
    · right
      change IsInt A ((f⁻¹ : FF) : LaurentSeries L)
      refine ⟨HahnSeries.C ⟨c⁻¹, hc⟩ * y₀, x₀, hx₀, ?_⟩
      have hf' : (f : LaurentSeries L) ≠ 0 := fun h' => hf (Subtype.ext h')
      rw [IntermediateField.coe_inv, map_mul, ι_C]
      have hcC : algebraMap L (LaurentSeries L) c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
      calc (f : LaurentSeries L)⁻¹ * ι A x₀
          = (f : LaurentSeries L)⁻¹ * (algebraMap L (LaurentSeries L) c)⁻¹ *
              ((f : LaurentSeries L) * ι A y₀) := by rw [h]; field_simp
        _ = algebraMap L (LaurentSeries L) (↑(⟨c⁻¹, hc⟩ : A) : L) * ι A y₀ := by
              rw [map_inv₀]; field_simp

theorem mem_gaussRing_iff (f : FF) : f ∈ gaussRing A N ↔ IsInt A (f : LaurentSeries L) := Iff.rfl

end Gauss

section Residue

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem gens_eq_divisorExpansionsC : gens L N = divisorExpansionsC L N := by
  ext x
  constructor
  · rintro ⟨_, ⟨d, hd, hdN, rfl⟩, rfl⟩
    exact ⟨d, hd, hdN, coeffEmb_qExpand_jq L d⟩
  · rintro ⟨d, hd, hdN, rfl⟩
    exact ⟨_, ⟨d, hd, hdN, rfl⟩, coeffEmb_qExpand_jq L d⟩

theorem laurentBaseChange_eq_fullC :
    laurentBaseChange L (modularFunctionFieldFull N) = modularFunctionFieldFullC L N := by
  rw [laurentBaseChange_eq_adjoin_gens, gens_eq_divisorExpansionsC]; rfl

theorem exists_witness (f : gaussRing A N) :
    ∃ p : LaurentSeries A × LaurentSeries A,
      ϖ A p.2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A p.2 = ι A p.1 := by
  obtain ⟨x, y, hy, h⟩ := f.2
  exact ⟨(x, y), hy, h⟩

def wit (f : gaussRing A N) : LaurentSeries A × LaurentSeries A :=
  Classical.choose (exists_witness A N f)

theorem wit_spec (f : gaussRing A N) :
    ϖ A (wit A N f).2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A (wit A N f).2 = ι A (wit A N f).1 :=
  Classical.choose_spec (exists_witness A N f)

def resL (f : gaussRing A N) : LaurentSeries kk :=
  ϖ A (wit A N f).1 / ϖ A (wit A N f).2

theorem resL_eq {f : gaussRing A N} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resL A N f = ϖ A x / ϖ A y := by
  obtain ⟨hy', h'⟩ := wit_spec A N f
  have hc := IsInt.cross (A := A) h' h
  rw [resL, div_eq_div_iff hy' hy, ← map_mul, ← map_mul, hc]

def resHom : gaussRing A N →+* LaurentSeries kk where
  toFun := resL A N
  map_one' := by
    rw [resL_eq A N (x := 1) (y := 1) (by simp) (by simp)]; simp
  map_mul' f g := by
    obtain ⟨hf, hf'⟩ := wit_spec A N f
    obtain ⟨hg, hg'⟩ := wit_spec A N g
    have h : (((f * g : gaussRing A N) : FF) : LaurentSeries L) * ι A ((wit A N f).2 * (wit A N g).2)
        = ι A ((wit A N f).1 * (wit A N g).1) := by
      rw [map_mul, map_mul, ← hf', ← hg']; push_cast; ring
    rw [resL_eq A N (by rw [map_mul]; exact mul_ne_zero hf hg) h]
    change _ = resL A N f * resL A N g
    rw [resL, resL, map_mul, map_mul, mul_div_mul_comm]
  map_zero' := by
    rw [resL_eq A N (x := 0) (y := 1) (by simp) (by simp)]; simp
  map_add' f g := by
    obtain ⟨hf, hf'⟩ := wit_spec A N f
    obtain ⟨hg, hg'⟩ := wit_spec A N g
    have h : (((f + g : gaussRing A N) : FF) : LaurentSeries L) * ι A ((wit A N f).2 * (wit A N g).2)
        = ι A ((wit A N f).1 * (wit A N g).2 + (wit A N g).1 * (wit A N f).2) := by
      rw [map_add, map_mul, map_mul, map_mul, ← hf', ← hg']; push_cast; ring
    rw [resL_eq A N (by rw [map_mul]; exact mul_ne_zero hf hg) h]
    change _ = resL A N f + resL A N g
    rw [resL, resL, div_add_div _ _ hf hg, map_add, map_mul, map_mul, map_mul]
    ring

theorem resHom_apply (f : gaussRing A N) : resHom A N f = resL A N f := rfl

theorem resHom_eq {f : gaussRing A N} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resHom A N f = ϖ A x / ϖ A y :=
  resL_eq A N hy h

theorem ι_mem_gaussRing {y : LaurentSeries A} (hyF : ι A y ∈ FF) : (⟨ι A y, hyF⟩ : FF) ∈ gaussRing A N :=
  ⟨y, 1, by simp, by simp⟩

theorem resHom_ι {y : LaurentSeries A} (hyF : ι A y ∈ FF) :
    resHom A N ⟨⟨ι A y, hyF⟩, ι_mem_gaussRing A N hyF⟩ = ϖ A y := by
  rw [resHom_eq A N (x := y) (y := 1) (by simp) (by simp)]; simp

theorem resHom_eq_zero_iff (f : gaussRing A N) :
    resHom A N f = 0 ↔ f ∈ IsLocalRing.maximalIdeal (gaussRing A N) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨hy, h⟩ := wit_spec A N f
  constructor
  · rintro h0 ⟨u, rfl⟩
    have := congrArg (resHom A N) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  · intro hu
    by_contra h0
    apply hu
    rw [resHom_eq A N hy h, div_eq_zero_iff, or_iff_left hy] at h0
    have hf0 : ((f : FF) : LaurentSeries L) ≠ 0 := by
      intro hf
      rw [hf, zero_mul, eq_comm, ι_eq_zero_iff] at h
      exact h0 (by rw [h, map_zero])
    have hf0' : (f : FF) ≠ 0 := fun h' => hf0 (by rw [h']; rfl)
    have hinv : (f : FF)⁻¹ ∈ gaussRing A N := by
      refine ⟨(wit A N f).2, (wit A N f).1, h0, ?_⟩
      rw [IntermediateField.coe_inv]
      exact IsInt.inv_of (A := A) h0 h
    exact ⟨⟨f, ⟨(f : FF)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0'),
      Subtype.ext (inv_mul_cancel₀ hf0')⟩, rfl⟩

theorem coe_algebraMap (c : L) :
    ((algebraMap L FF c : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c := rfl

theorem algebraMap_mem_gaussRing_iff (c : L) : algebraMap L FF c ∈ gaussRing A N ↔ c ∈ A := by
  constructor
  · rintro ⟨x, y, hy, h⟩
    rw [coe_algebraMap] at h
    by_contra hc
    have hc0 : c ≠ 0 := by rintro rfl; exact hc A.zero_mem
    have hci : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hc
    have hcm : (⟨c⁻¹, hci⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      apply hc
      have h1 : ((↑(u⁻¹ : Aˣ) : A) : L) * c⁻¹ = 1 := by
        have := congrArg (fun a : A => (a : L)) u.inv_val
        simpa [hu] using this
      rw [mul_inv_eq_one₀ hc0] at h1
      rw [← h1]; exact SetLike.coe_mem _
    have hyx : y = HahnSeries.C ⟨c⁻¹, hci⟩ * x := by
      apply ι_injective A
      rw [map_mul, ι_C, ← h, ← mul_assoc, ← map_mul]
      simp [inv_mul_cancel₀ hc0]
    apply hy
    rw [ϖ_eq_zero_iff]
    intro n
    rw [hyx, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hcm
  · intro hc
    refine ⟨HahnSeries.C ⟨c, hc⟩, 1, by simp, ?_⟩
    rw [coe_algebraMap, ι_C, map_one, mul_one]

theorem resHom_algebraMap (a : A) (h : algebraMap L FF a ∈ gaussRing A N) :
    resHom A N ⟨algebraMap L FF a, h⟩ = algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A a) := by
  rw [resHom_eq A N (x := HahnSeries.C a) (y := 1) (by simp)
    (by rw [map_one, mul_one]; change algebraMap L (LaurentSeries L) (a : L) = _; rw [ι_C]),
    ϖ_C, map_one, div_one]

theorem coe_smul' (c : L) (f : FF) :
    ((c • f : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c * (f : LaurentSeries L) := by
  rw [IntermediateField.coe_smul, Algebra.smul_def]

theorem exists_smul_mem_gaussRing (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A N, resHom A N ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h⟩ := exists_frac_form A N f hf
  have key : ((c⁻¹ • f : FF) : LaurentSeries L) * ι A y₀ = ι A x₀ := by
    rw [coe_smul', mul_assoc, h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  have hmem : c⁻¹ • f ∈ gaussRing A N := (mem_gaussRing_iff A N _).mpr ⟨x₀, y₀, hy₀, key⟩
  refine ⟨c⁻¹, hmem, ?_⟩
  rw [Ne, resHom_eq A N (f := ⟨_, hmem⟩) hy₀ key]
  exact div_ne_zero hx₀ hy₀

end Residue

section PolyJ

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

def jF : FF := ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (modularFunctionField_le_full N (jq_mem N))⟩

theorem coe_jF : ((jF N : FF) : LaurentSeries L) = jqModC L := coeffMap_jqModC _

theorem coe_jF' : ((jF N : FF) : LaurentSeries L) = ι A (jqModC A) := by
  rw [coe_jF, coeffMap_jqModC]

theorem exists_resHom_eq {z : LaurentSeries kk} (hz : z ∈ modularFunctionFieldFullC kk N) :
    ∃ f : gaussRing A N, resHom A N f = z := by
  let S : Subfield (LaurentSeries kk) :=
    { carrier := Set.range (resHom A N)
      mul_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f * g, map_mul _ _ _⟩
      one_mem' := ⟨1, map_one _⟩
      add_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f + g, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      neg_mem' := by rintro _ ⟨f, rfl⟩; exact ⟨-f, map_neg _ _⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        by_cases h0 : resHom A N f = 0
        · exact ⟨0, by rw [h0, inv_zero, map_zero]⟩
        · have hu : IsUnit f := by
            by_contra hu
            exact h0 ((resHom_eq_zero_iff A N f).mpr
              ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)))
          obtain ⟨u, rfl⟩ := hu
          refine ⟨↑u⁻¹, ?_⟩
          exact (inv_eq_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])).symm }
  have hle : Subfield.closure (Set.range (algebraMap kk (LaurentSeries kk)) ∪ divisorExpansionsC kk N)
      ≤ S := by
    rw [Subfield.closure_le]
    rintro z (⟨t, rfl⟩ | ⟨d, hd, hdN, rfl⟩)
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
      exact ⟨⟨_, (algebraMap_mem_gaussRing_iff A N (a : L)).mpr a.2⟩, resHom_algebraMap A N a _⟩
    · have hmem : ι A (qExpand A d (jqModC A)) ∈ FF := by
        rw [ι_qExpand_jqModC, ← coeffEmb_qExpand_jq]
        exact coeffEmb_mem_laurentBaseChange L (jqd_mem_full N hdN)
      exact ⟨_, (resHom_ι A N hmem).trans (ϖ_qExpand_jqModC A d)⟩
  obtain ⟨f, hf⟩ := hle (show z ∈ Subfield.closure _ from hz)
  exact ⟨f, hf⟩

end PolyJ

section Helpers

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem dedekindPsi_pos : 0 < dedekindPsi N := by
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, NeZero.ne N]
  calc 0 < N / 1 := by simpa using Nat.pos_of_ne_zero (NeZero.ne N)
    _ ≤ dedekindPsi N := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1

theorem jF_mem_gaussRing : (jF N : FF) ∈ gaussRing A N :=
  (mem_gaussRing_iff A N _).mpr ⟨jqModC A, 1, by rw [map_one]; exact one_ne_zero,
    by rw [map_one, mul_one, coe_jF']⟩

theorem resHom_jF : resHom A N ⟨jF N, jF_mem_gaussRing A N⟩ = jqModC kk := by
  rw [resHom_eq A N (f := ⟨jF N, jF_mem_gaussRing A N⟩) (x := jqModC A) (y := 1)
    (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact coe_jF' A N),
    map_one, div_one, coeffMap_jqModC]

theorem finrank_adjoin_transport {E E' : IntermediateField L (LaurentSeries L)} (h : E = E')
    {x : LaurentSeries L} (hx : x ∈ E) (hx' : x ∈ E') :
    Module.finrank (IntermediateField.adjoin L ({⟨x, hx⟩} : Set E)) E =
      Module.finrank (IntermediateField.adjoin L ({⟨x, hx'⟩} : Set E')) E' := by
  subst h; rfl

theorem finrank_adjoin_jF (hN : (N : L) ≠ 0) :
    Module.finrank (IntermediateField.adjoin L {(jF N : FF)}) FF = dedekindPsi N := by
  have hj : (jF N : FF) = ⟨jqModC L, (laurentBaseChange_eq_fullC (L := L) N) ▸ jqModC_mem_full L N⟩ :=
    Subtype.ext (coe_jF N)
  rw [hj, finrank_adjoin_transport (laurentBaseChange_eq_fullC (L := L) N) _ (jqModC_mem_full L N)]
  exact ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi L N hN

theorem natCast_residueField_ne_zero {ℓ : ℕ} [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ) {m : ℕ}
    (hm : ¬ ℓ ∣ m) : (m : IsLocalRing.ResidueField A) ≠ 0 := by
  intro h0
  have hℓ : ((ℓ : A) : L) ∈ A.nonunits := by simpa [ValuationSubring.LiesOverPrime] using hA
  rw [ValuationSubring.coe_mem_nonunits_iff] at hℓ
  have hmA : (m : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]; exact h0
  have hcop : IsCoprime (ℓ : A) (m : A) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓ) (Ideal.mul_mem_left _ _ hmA)

end Helpers

section Orders

variable (K : Type*) [Field K]

theorem order_jqModC_pow (b : ℕ) : ((jqModC K) ^ b).order = -(b : ℤ) := by
  have h1 : ((jqModC K) ^ b).coeff (-(b : ℤ)) ≠ 0 := by
    rw [coeff_jqModC_pow_self]; exact one_ne_zero
  have hne : (jqModC K) ^ b ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  push Not at hlt
  exact (HahnSeries.coeff_order_eq_zero.not.mpr) hne (coeff_jqModC_pow_of_lt K hlt)

theorem jqModC_pow_ne_zero (b : ℕ) : (jqModC K) ^ b ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero (by rw [coeff_jqModC_pow_self]; exact one_ne_zero)

variable (p : ℕ) [Fact p.Prime]

theorem order_qExpand {x : LaurentSeries K} (hx : x ≠ 0) :
    (qExpand K p x).order = (p : ℤ) * x.order := by
  have hq0 : qExpand K p x ≠ 0 := fun h => hx (qExpand_injective (R := K) (N := p) (by rw [h, map_zero]))
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [qExpand_coeff_mul]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) hx
  · by_contra hlt
    push Not at hlt
    have hc := (HahnSeries.coeff_order_eq_zero.not.mpr) hq0
    by_cases hdvd : (p : ℤ) ∣ (qExpand K p x).order
    · obtain ⟨k, hk⟩ := hdvd
      rw [hk, qExpand_coeff_mul] at hc
      have hle := HahnSeries.order_le_of_coeff_ne_zero hc
      rw [hk] at hlt
      have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      nlinarith
    · exact hc (qExpand_coeff_of_not_dvd p x hdvd)

theorem eq_zero_of_sum_eq_zero_of_order_injOn {ι : Type*} [Fintype ι] (t : ι → LaurentSeries K)
    (hdist : ∀ i j, t i ≠ 0 → t j ≠ 0 → (t i).order = (t j).order → i = j)
    (hsum : ∑ i, t i = 0) : ∀ i, t i = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  set s : Finset ι := Finset.univ.filter fun i => t i ≠ 0 with hs
  have hsne : s.Nonempty := ⟨i₁, by simp [hs, hi₁]⟩
  obtain ⟨i₀, hi₀s, hmin⟩ := Finset.exists_min_image s (fun i => (t i).order) hsne
  have hi₀ : t i₀ ≠ 0 := by simpa [hs] using hi₀s
  have hcoeff : (∑ i, t i).coeff (t i₀).order = (t i₀).coeff (t i₀).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ _) h)
    by_cases hti : t i = 0
    · rw [hti, HahnSeries.coeff_zero]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      have hle := hmin i (by simp [hs, hti])
      exact lt_of_le_of_ne hle fun h => hi (hdist i i₀ hti hi₀ h.symm)
  rw [hsum, HahnSeries.coeff_zero] at hcoeff
  exact (HahnSeries.coeff_order_eq_zero.not.mpr) hi₀ hcoeff.symm

variable [CharP K p]

theorem adjoin_pow_le :
    IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K))
      ≤ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
    (pow_mem (mem_adjoin_simple_self K (jqModC K)) p))

theorem exists_qExpand_eq_of_mem_adjoin_pow {c : LaurentSeries K}
    (hc : c ∈ IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K))) :
    ∃ d : LaurentSeries K, qExpand K p d = c := by
  have hle : Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ {(jqModC K) ^ p})
      ≤ (qExpand K p).fieldRange := by
    rw [Subfield.closure_le]
    rintro z (⟨t, rfl⟩ | rfl)
    · refine ⟨algebraMap K (LaurentSeries K) t, ?_⟩
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
    · exact ⟨jqModC K, qExpand_jqModC_eq_pow_unconditional K⟩
  obtain ⟨d, hd⟩ := hle (show c ∈ Subfield.closure _ from hc)
  exact ⟨d, hd⟩

theorem le_finrank_adjoin_pow
    [Module.Finite (IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K)))
      (extendScalars (adjoin_pow_le K p))] :
    p ≤ Module.finrank (IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K)))
      (extendScalars (adjoin_pow_le K p)) := by
  set K₀ := IntermediateField.adjoin K ({(jqModC K) ^ p} : Set (LaurentSeries K)) with hK₀
  let v : Fin p → extendScalars (adjoin_pow_le K p) := fun i =>
    ⟨(jqModC K) ^ (i : ℕ), (mem_extendScalars _).mpr
      (pow_mem (mem_adjoin_simple_self K (jqModC K)) _)⟩
  have hli : LinearIndependent K₀ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i

    have hsum : ∑ i, ((g i : K₀) : LaurentSeries K) * (jqModC K) ^ (i : ℕ) = 0 := by
      have := congrArg (fun z : extendScalars (adjoin_pow_le K p) => (z : LaurentSeries K)) hg
      first
        | simpa only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] using this
        | (simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at this; exact this)
    have hd : ∀ i, ∃ d : LaurentSeries K, qExpand K p d = ((g i : K₀) : LaurentSeries K) :=
      fun i => exists_qExpand_eq_of_mem_adjoin_pow K p (g i).2
    choose d hd using hd
    have hall := eq_zero_of_sum_eq_zero_of_order_injOn K
      (fun i : Fin p => ((g i : K₀) : LaurentSeries K) * (jqModC K) ^ (i : ℕ)) ?_ hsum
    · have hi := hall i
      rcases mul_eq_zero.mp hi with h0 | h0
      · exact Subtype.ext (by simpa using h0)
      · exact absurd h0 (jqModC_pow_ne_zero K _)
    · intro i j hi hj hij
      have hgi : ((g i : K₀) : LaurentSeries K) ≠ 0 := left_ne_zero_of_mul hi
      have hgj : ((g j : K₀) : LaurentSeries K) ≠ 0 := left_ne_zero_of_mul hj
      have hdi : d i ≠ 0 := by rintro h; apply hgi; rw [← hd i, h, map_zero]
      have hdj : d j ≠ 0 := by rintro h; apply hgj; rw [← hd j, h, map_zero]
      rw [HahnSeries.order_mul hgi (jqModC_pow_ne_zero K _),
        HahnSeries.order_mul hgj (jqModC_pow_ne_zero K _), ← hd i, ← hd j,
        order_qExpand K p hdi, order_qExpand K p hdj, order_jqModC_pow, order_jqModC_pow] at hij

      have hdvd : (p : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) :=
        ⟨(d j).order - (d i).order, by linarith⟩
      have habs : |((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)| < p := by
        rw [abs_sub_lt_iff]; constructor <;> omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact Fin.ext (by omega)
  simpa using hli.fintype_card_le_finrank

end Orders

section Transport

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]

theorem mem_comap_iff (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) (x : F) :
    x ∈ R.integers.comap (w : F →+* F) ↔ w x ∈ R.integers := Iff.rfl

def comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    R.integers.comap (w : F →+* F) →+* R.integers :=
  (w : F →+* F).restrict _ _ (fun _ hx => (mem_comap_iff A R w _).mp hx)

@[scoped simp] theorem coe_comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers.comap (w : F →+* F)) : (comapHom A R w x : F) = w x := rfl

def symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    R.integers →+* R.integers.comap (w : F →+* F) :=
  (w.symm : F →+* F).restrict _ _ (fun x hx => by
    rw [mem_comap_iff]
    change w (w.symm x) ∈ R.integers
    rw [AlgEquiv.apply_symm_apply]; exact hx)

@[scoped simp] theorem coe_symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers) : (symmHom A R w x : F) = w.symm x := rfl

theorem comapHom_symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) (x : R.integers) :
    comapHom A R w (symmHom A R w x) = x :=
  Subtype.ext (by simp)

theorem symmHom_comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers.comap (w : F →+* F)) : symmHom A R w (comapHom A R w x) = x :=
  Subtype.ext (by simp)

def transport (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) : RegularProlongation A F Fb where
  integers := R.integers.comap (w : F →+* F)
  residue := R.residue.comp (comapHom A R w)
  algebraMap_mem_iff x := by
    rw [mem_comap_iff, AlgEquiv.commutes]
    exact R.algebraMap_mem_iff x
  residue_surjective z := by
    obtain ⟨f, hf⟩ := R.residue_surjective z
    exact ⟨symmHom A R w f, by rw [RingHom.comp_apply, comapHom_symmHom, hf]⟩
  ker_residue := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, R.ker_residue,
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, not_iff_not]
    constructor
    · intro hu; simpa [symmHom_comapHom] using hu.map (symmHom A R w)
    · intro hu; exact hu.map (comapHom A R w)
  residue_algebraMap a := by
    rw [RingHom.comp_apply]
    convert R.residue_algebraMap a using 2
    exact Subtype.ext (by simp)
  exists_smul_mem f hf := by
    have hwf : w f ≠ 0 := (map_ne_zero_iff _ w.injective).mpr hf
    obtain ⟨c, hc, hne⟩ := R.exists_smul_mem (w f) hwf
    have hmem : c • f ∈ R.integers.comap (w : F →+* F) := by
      rw [mem_comap_iff, map_smul]; exact hc
    refine ⟨c, hmem, ?_⟩
    rw [RingHom.comp_apply]
    have h : comapHom A R w ⟨c • f, hmem⟩ = ⟨c • w f, hc⟩ := Subtype.ext (by simp)
    rwa [h]

@[scoped simp] theorem transport_integers (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    (transport A R w).integers = R.integers.comap (w : F →+* F) := rfl

end Transport

section ResidueRange

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (M : ℕ) [NeZero M]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull M)
local notation "kk" => IsLocalRing.ResidueField A

theorem isUnit_of_resHom_ne_zero {f : gaussRing A M} (hf : resHom A M f ≠ 0) : IsUnit f := by
  by_contra hu
  exact hf ((resHom_eq_zero_iff A M f).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)))

def resField : IntermediateField kk (LaurentSeries kk) :=
  Subfield.toIntermediateField
    { carrier := Set.range (resHom A M)
      mul_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f * g, map_mul _ _ _⟩
      one_mem' := ⟨1, map_one _⟩
      add_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f + g, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      neg_mem' := by rintro _ ⟨f, rfl⟩; exact ⟨-f, map_neg _ _⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        by_cases h0 : resHom A M f = 0
        · exact ⟨0, by rw [h0, inv_zero, map_zero]⟩
        · obtain ⟨u, rfl⟩ := isUnit_of_resHom_ne_zero A M h0
          refine ⟨↑u⁻¹, ?_⟩
          exact (inv_eq_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])).symm }
    (fun t => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
      exact ⟨⟨_, (algebraMap_mem_gaussRing_iff A M (a : L)).mpr a.2⟩, resHom_algebraMap A M a _⟩)

theorem resHom_mem_resField (f : gaussRing A M) : resHom A M f ∈ resField A M := ⟨f, rfl⟩

theorem fullC_le_resField : modularFunctionFieldFullC kk M ≤ resField A M :=
  fun _ hz => exists_resHom_eq A M hz

def resE : gaussRing A M →+* resField A M := (resHom A M).codRestrict (resField A M) (resHom_mem_resField A M)

@[scoped simp] theorem coe_resE (f : gaussRing A M) : ((resE A M f : resField A M) : LaurentSeries kk) = resHom A M f := rfl

def gaussRP : RegularProlongation A FF (resField A M) where
  integers := gaussRing A M
  residue := resE A M
  algebraMap_mem_iff := algebraMap_mem_gaussRing_iff A M
  residue_surjective z := by obtain ⟨f, hf⟩ := z.2; exact ⟨f, Subtype.ext hf⟩
  ker_residue := by
    ext f
    rw [RingHom.mem_ker, ← resHom_eq_zero_iff, ← coe_resE, ZeroMemClass.coe_eq_zero]
  residue_algebraMap a := Subtype.ext (resHom_algebraMap A M a _)
  exists_smul_mem f hf := by
    obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A M f hf
    exact ⟨c, h, fun h0 => hne (by rw [← coe_resE, h0]; rfl)⟩

end ResidueRange

section TwoProlongations

variable (N q : ℕ) [NeZero N] [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))
local notation "kk" => IsLocalRing.ResidueField A
local notation "𝒪" => gaussRing A (N * q)

theorem jQ_mem : ι A (qExpand A q (jqModC A)) ∈ FF := by
  rw [ι_qExpand_jqModC, ← coeffEmb_qExpand_jq]
  exact coeffEmb_mem_laurentBaseChange _ (jqd_mem_full (N * q) (dvd_mul_left q N))

def jQF : FF := ⟨ι A (qExpand A q (jqModC A)), jQ_mem N q A⟩

theorem coe_jQF : ((jQF N q A : FF) : LaurentSeries ℚ̄) = ι A (qExpand A q (jqModC A)) := rfl

theorem exists_atkinLehner (hqN : ¬ q ∣ N) :
    ∃ w : FF ≃ₐ[ℚ̄] FF, w (jF (N * q)) = jQF N q A ∧ w (jQF N q A) = jF (N * q) := by
  obtain ⟨w, hw⟩ := ModularCurve.exists_algEquiv_modularFunctionFieldBar_atkinLehner N q
    (Fact.out : q.Prime) hqN
  have h1 : coeffEmb ℚ̄ (qExpand ℚ 1 jq) = jqModC ℚ̄ := by
    rw [qExpand_one_apply]; exact coeffMap_jqModC _
  have h2 : qExpand ℚ̄ q (coeffEmb ℚ̄ (qExpand ℚ 1 jq)) = ι A (qExpand A q (jqModC A)) := by
    rw [h1, ι_qExpand_jqModC]
  have hx := hw 1 (one_dvd N)
  refine ⟨w, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [coe_jQF, ← h2]
    exact (hx (jF (N * q))).1 (by rw [coe_jF, h1])
  · rw [coe_jF, ← h1]
    exact (hx (jQF N q A)).2 (by rw [coe_jQF, h2])

variable {N q A}

theorem charP_kk (hA : A.LiesOverPrime q) : CharP kk q :=
  ValuationSubring.charP_residueField_of_liesOverPrime q A hA

theorem ϖ_qExpand_jqModC_eq_pow (hA : A.LiesOverPrime q) :
    ϖ A (qExpand A q (jqModC A)) = (jqModC kk) ^ q := by
  haveI := charP_kk hA
  rw [ϖ_qExpand_jqModC]; exact qExpand_jqModC_eq_pow_unconditional kk

theorem coe_jF_pow (n : ℕ) : (((jF (N * q)) ^ n : FF) : LaurentSeries ℚ̄) = ι A ((jqModC A) ^ n) := by
  rw [map_pow, ← coe_jF' A (N * q)]; rfl

theorem gaussRing_ne_comap (hA : A.LiesOverPrime q) (w : FF ≃ₐ[ℚ̄] FF)
    (hw₁ : w (jF (N * q)) = jQF N q A) (hw₂ : w (jQF N q A) = jF (N * q)) :
    (𝒪 : ValuationSubring FF) ≠ (𝒪).comap (w : FF →+* FF) := by
  haveI := charP_kk hA
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hjk : (jqModC kk) ≠ 0 := jqModC_ne_zero_of_nontrivial kk

  set t : FF := jQF N q A / (jF (N * q)) ^ q with ht
  set t' : FF := jF (N * q) / (jQF N q A) ^ q with ht'
  have hwt : w t = t' := by rw [ht, map_div₀, map_pow, hw₁, hw₂]

  have hιy : ι A ((jqModC A) ^ q) ≠ 0 := by
    rw [Ne, ι_eq_zero_iff]; exact pow_ne_zero _ (ϖ_ne_zero_ne_zero (by
      rw [coeffMap_jqModC]; exact hjk))
  have ht_int : (t : LaurentSeries ℚ̄) * ι A ((jqModC A) ^ q) = ι A (qExpand A q (jqModC A)) := by
    rw [ht, IntermediateField.coe_div, coe_jF_pow, coe_jQF, div_mul_cancel₀ _ hιy]
  have hϖy : ϖ A ((jqModC A) ^ q) ≠ 0 := by
    rw [map_pow, coeffMap_jqModC]; exact pow_ne_zero _ hjk
  have ht_mem : t ∈ 𝒪 := ⟨_, _, hϖy, ht_int⟩
  have hres_t : resHom A (N * q) ⟨t, ht_mem⟩ = 1 := by
    rw [resHom_eq A (N * q) (f := ⟨t, ht_mem⟩) hϖy ht_int, ϖ_qExpand_jqModC_eq_pow hA, map_pow,
      coeffMap_jqModC, div_self (pow_ne_zero _ hjk)]

  have hιy' : ι A ((qExpand A q (jqModC A)) ^ q) ≠ 0 := by
    rw [Ne, ι_eq_zero_iff]
    refine pow_ne_zero _ (ϖ_ne_zero_ne_zero ?_)
    rw [ϖ_qExpand_jqModC_eq_pow hA]; exact pow_ne_zero _ hjk
  have ht'_int : (t' : LaurentSeries ℚ̄) * ι A ((qExpand A q (jqModC A)) ^ q) = ι A (jqModC A) := by
    rw [ht', IntermediateField.coe_div, coe_jF' A (N * q), IntermediateField.coe_pow, coe_jQF, ← map_pow,
      div_mul_cancel₀ _ hιy']
  have hϖy' : ϖ A ((qExpand A q (jqModC A)) ^ q) ≠ 0 := by
    rw [map_pow, ϖ_qExpand_jqModC_eq_pow hA]; exact pow_ne_zero _ (pow_ne_zero _ hjk)
  have ht'_mem : t' ∈ 𝒪 := ⟨_, _, hϖy', ht'_int⟩
  have hres_t' : resHom A (N * q) ⟨t', ht'_mem⟩ ≠ 1 := by
    rw [resHom_eq A (N * q) (f := ⟨t', ht'_mem⟩) hϖy' ht'_int, map_pow, ϖ_qExpand_jqModC_eq_pow hA,
      coeffMap_jqModC, Ne, div_eq_one_iff_eq (pow_ne_zero _ (pow_ne_zero _ hjk)), ← pow_mul]
    intro h
    have h1 : ((jqModC kk) ^ 1).order = ((jqModC kk) ^ (q * q)).order := by
      rw [pow_one]; exact congrArg HahnSeries.order h
    rw [order_jqModC_pow, order_jqModC_pow] at h1
    have h2 : ((q * q : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by linarith
    have h3 : q * q = 1 := by exact_mod_cast h2
    nlinarith

  set h : FF := t - 1 with hh
  have hh_mem : h ∈ 𝒪 := sub_mem ht_mem (one_mem _)
  have hres_h : resHom A (N * q) ⟨h, hh_mem⟩ = 0 := by
    have : (⟨h, hh_mem⟩ : 𝒪) = ⟨t, ht_mem⟩ - 1 := Subtype.ext rfl
    rw [this, map_sub, map_one, hres_t, sub_self]
  have hwh : w h = t' - 1 := by rw [hh, map_sub, map_one, hwt]
  have hwh_mem : w h ∈ 𝒪 := by rw [hwh]; exact sub_mem ht'_mem (one_mem _)
  have hres_wh : resHom A (N * q) ⟨w h, hwh_mem⟩ ≠ 0 := by
    have : (⟨w h, hwh_mem⟩ : 𝒪) = ⟨t', ht'_mem⟩ - 1 := Subtype.ext hwh
    rw [this, map_sub, map_one, sub_ne_zero]; exact hres_t'
  have hh0 : h ≠ 0 := by
    intro h0; apply hres_wh
    have : (⟨w h, hwh_mem⟩ : 𝒪) = 0 := Subtype.ext (by change w h = 0; rw [h0, map_zero])
    rw [this, map_zero]
  have hwh0 : w h ≠ 0 := (map_ne_zero_iff _ w.injective).mpr hh0

  intro heq
  obtain ⟨u, hu⟩ := isUnit_of_resHom_ne_zero A (N * q) hres_wh
  have hinv_mem : (w h)⁻¹ ∈ 𝒪 := by
    have hmul : ((↑u⁻¹ : 𝒪) : FF) * w h = 1 := by
      have := congrArg (fun y : 𝒪 => (y : FF)) u.inv_mul
      simpa [hu] using this
    rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _
  have hinv_comap : h⁻¹ ∈ (𝒪).comap (w : FF →+* FF) := by
    change w h⁻¹ ∈ 𝒪
    rw [map_inv₀]; exact hinv_mem
  rw [← heq] at hinv_comap

  have hunit : IsUnit (⟨h, hh_mem⟩ : 𝒪) :=
    ⟨⟨⟨h, hh_mem⟩, ⟨h⁻¹, hinv_comap⟩, Subtype.ext (mul_inv_cancel₀ hh0),
      Subtype.ext (inv_mul_cancel₀ hh0)⟩, rfl⟩
  have := (resHom_eq_zero_iff A (N * q) ⟨h, hh_mem⟩).mp hres_h
  exact ((IsLocalRing.mem_maximalIdeal _).mp this) hunit

theorem finrank_adjoin_eq_relfinrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (x : K) :
    Module.finrank (IntermediateField.adjoin F ({x} : Set K)) K =
      IntermediateField.relfinrank (IntermediateField.adjoin F ({(x : E)} : Set E)) K := by
  have h1 := IntermediateField.relfinrank_map_map (IntermediateField.adjoin F ({x} : Set K)) ⊤ K.val
  rw [IntermediateField.relfinrank_top_right] at h1
  rw [← h1]
  change IntermediateField.relfinrank (IntermediateField.lift _) (IntermediateField.lift _) = _
  rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]

theorem jQF_mem_gaussRing : (jQF N q A : FF) ∈ 𝒪 :=
  ⟨qExpand A q (jqModC A), 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one, coe_jQF]⟩

theorem resHom_jQF (hA : A.LiesOverPrime q) :
    resHom A (N * q) ⟨jQF N q A, jQF_mem_gaussRing⟩ = (jqModC kk) ^ q := by
  rw [resHom_eq A (N * q) (f := ⟨jQF N q A, jQF_mem_gaussRing⟩) (x := qExpand A q (jqModC A))
    (y := 1) (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one, coe_jQF]), map_one, div_one,
    ϖ_qExpand_jqModC_eq_pow hA]

set_option maxHeartbeats 12800000 in

theorem resField_le_fullC (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q) :
    resField A (N * q) ≤ modularFunctionFieldFullC kk N := by
  haveI := charP_kk hA

  set E : IntermediateField kk (LaurentSeries kk) := resField A (N * q)
  set F₁ : IntermediateField kk (LaurentSeries kk) := modularFunctionFieldFullC kk N
  set K₁ : IntermediateField kk (LaurentSeries kk) :=
    IntermediateField.adjoin kk ({jqModC kk} : Set (LaurentSeries kk))
  set K₀ : IntermediateField kk (LaurentSeries kk) :=
    IntermediateField.adjoin kk ({(jqModC kk) ^ q} : Set (LaurentSeries kk))
  have hK₀K₁ : K₀ ≤ K₁ := adjoin_pow_le kk q
  have hK₁F : K₁ ≤ F₁ := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem_full kk N))
  have hFE : F₁ ≤ E := (full_degeneracyC_le (K := kk) (dvd_mul_right N q)).trans
    (fullC_le_resField A (N * q))
  have hK₁E : K₁ ≤ E := hK₁F.trans hFE

  obtain ⟨w, hw₁, hw₂⟩ := exists_atkinLehner N q A hqN
  have hne := gaussRing_ne_comap hA w hw₁ hw₂
  let R₁ : RegularProlongation A FF E := gaussRP A (N * q)
  let R₂ : RegularProlongation A FF E := transport A (gaussRP A (N * q)) w
  let R : Fin 2 → RegularProlongation A FF E := ![R₁, R₂]
  have hR0 : R 0 = R₁ := rfl
  have hR1 : R 1 = R₂ := rfl
  have hR : Function.Injective fun i => (R i).integers := by
    have key : ∀ i j : Fin 2, (R i).integers = (R j).integers → i = j :=
      Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨fun _ => rfl, fun h => absurd h hne⟩,
        Fin.forall_fin_two.mpr ⟨fun h => absurd h.symm hne, fun _ => rfl⟩⟩
    exact fun i j h => key i j h
  have hjO : (jF (N * q) : FF) ∈ 𝒪 := jF_mem_gaussRing A (N * q)
  have hjQO : (jQF N q A : FF) ∈ 𝒪 := jQF_mem_gaussRing
  have hjO' : (jF (N * q) : FF) ∈ (𝒪).comap (w : FF →+* FF) := by
    change w (jF (N * q)) ∈ 𝒪; rw [hw₁]; exact hjQO
  have hf : ∀ i, (jF (N * q) : FF) ∈ (R i).integers := Fin.forall_fin_two.mpr ⟨hjO, hjO'⟩

  have hres₁ : (((R 0).residue ⟨jF (N * q), hf 0⟩ : E) : LaurentSeries kk) = jqModC kk := by
    change ((resE A (N * q) ⟨jF (N * q), hjO⟩ : E) : LaurentSeries kk) = _
    rw [coe_resE, resHom_jF]
  have hres₂ : (((R 1).residue ⟨jF (N * q), hf 1⟩ : E) : LaurentSeries kk) = (jqModC kk) ^ q := by
    change ((resE A (N * q) (comapHom A (gaussRP A (N * q)) w ⟨jF (N * q), hjO'⟩) : E) :
      LaurentSeries kk) = _
    rw [coe_resE]
    have : comapHom A (gaussRP A (N * q)) w ⟨jF (N * q), hjO'⟩ = ⟨jQF N q A, hjQO⟩ :=
      Subtype.ext (by rw [coe_comapHom, hw₁])
    rw [this]; exact resHom_jQF hA
  have htr₁ : Transcendental kk (jqModC kk) := ModularCurve.transcendental_jqModC kk
  have htr₂ : Transcendental kk ((jqModC kk) ^ q) := by
    rw [← qExpand_jqModC_eq_pow_unconditional kk]
    exact fun h => htr₁ ((isAlgebraic_algHom_iff (qExpandAlgHomC kk q)
      (qExpand_injective (R := kk) (N := q))).mp h)
  have htr : ∀ i, Transcendental kk ((R i).residue ⟨jF (N * q), hf i⟩) := by
    refine Fin.forall_fin_two.mpr ⟨fun h => htr₁ ?_, fun h => htr₂ ?_⟩
    · rw [← hres₁]; exact (isAlgebraic_algHom_iff E.val Subtype.val_injective).mpr h
    · rw [← hres₂]; exact (isAlgebraic_algHom_iff E.val Subtype.val_injective).mpr h

  have hψ : Module.finrank (IntermediateField.adjoin ℚ̄ {(jF (N * q) : FF)}) FF =
      dedekindPsi N * (q + 1) := by
    rw [finrank_adjoin_jF (L := ℚ̄) (N * q) (Nat.cast_ne_zero.mpr (NeZero.ne (N * q))),
      dedekindPsi_mul_of_coprime N q ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqN).symm,
      dedekindPsi_prime (Fact.out : q.Prime)]
  haveI : FiniteDimensional (IntermediateField.adjoin ℚ̄ {(jF (N * q) : FF)}) FF :=
    Module.finite_of_finrank_pos (by rw [hψ]; exact Nat.mul_pos (dedekindPsi_pos N) (Nat.succ_pos q))

  obtain ⟨hfin, hsum₀⟩ := AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le A
    (fun _ : Fin 2 => (E : Type _)) R hR (jF (N * q)) hf htr
  have hfin0 := hfin 0
  have hfin1 := hfin 1
  try dsimp only at hfin0 hfin1 hsum₀
  simp only [Fin.sum_univ_two] at hsum₀

  have hconv₁ : Module.finrank (IntermediateField.adjoin kk {(R 0).residue ⟨jF (N * q), hf 0⟩}) E
      = IntermediateField.relfinrank K₁ E :=
    (finrank_adjoin_eq_relfinrank E ((R 0).residue ⟨jF (N * q), hf 0⟩)).trans (by rw [hres₁])
  have hconv₂ : Module.finrank (IntermediateField.adjoin kk {(R 1).residue ⟨jF (N * q), hf 1⟩}) E
      = IntermediateField.relfinrank K₀ E :=
    (finrank_adjoin_eq_relfinrank E ((R 1).residue ⟨jF (N * q), hf 1⟩)).trans (by rw [hres₂])
  have hpos₁ : 0 < IntermediateField.relfinrank K₁ E := by
    rw [← hconv₁]; haveI := hfin0; exact Module.finrank_pos
  have hpos₂ : 0 < IntermediateField.relfinrank K₀ E := by
    rw [← hconv₂]; haveI := hfin1; exact Module.finrank_pos
  have hsum : IntermediateField.relfinrank K₁ E + IntermediateField.relfinrank K₀ E
      ≤ dedekindPsi N * (q + 1) := by
    rw [← hconv₁, ← hconv₂, ← hψ]; exact hsum₀

  have hψN : IntermediateField.relfinrank K₁ F₁ = dedekindPsi N := by
    have h := ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi kk N
      (natCast_residueField_ne_zero A hA hqN)
    have h' := finrank_adjoin_eq_relfinrank (modularFunctionFieldFullC kk N)
      (⟨jqModC kk, jqModC_mem_full kk N⟩ : modularFunctionFieldFullC kk N)
    exact h'.symm.trans h

  have htow₁ := IntermediateField.relfinrank_mul_relfinrank hK₁F hFE
  have htow₂ := IntermediateField.relfinrank_mul_relfinrank hK₀K₁ hK₁E
  rw [hψN] at htow₁

  have he0 : IntermediateField.relfinrank K₀ K₁ ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at htow₂; omega
  have hqe : q ≤ IntermediateField.relfinrank K₀ K₁ := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hK₀K₁]
    haveI : Module.Finite K₀ (extendScalars hK₀K₁) := Module.finite_of_finrank_pos (by
      rw [← IntermediateField.relfinrank_eq_finrank_of_le hK₀K₁]; exact Nat.pos_of_ne_zero he0)
    exact le_finrank_adjoin_pow kk q

  have hψpos := dedekindPsi_pos N
  have hdpos : 0 < IntermediateField.relfinrank F₁ E := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at htow₁; omega
  have h1 : dedekindPsi N * (IntermediateField.relfinrank F₁ E * (1 + IntermediateField.relfinrank K₀ K₁))
      ≤ dedekindPsi N * (q + 1) := by
    calc dedekindPsi N * (IntermediateField.relfinrank F₁ E * (1 + IntermediateField.relfinrank K₀ K₁))
        = dedekindPsi N * IntermediateField.relfinrank F₁ E +
            IntermediateField.relfinrank K₀ K₁ * (dedekindPsi N * IntermediateField.relfinrank F₁ E) := by
          ring
      _ = IntermediateField.relfinrank K₁ E + IntermediateField.relfinrank K₀ E := by rw [htow₁, htow₂]
      _ ≤ dedekindPsi N * (q + 1) := hsum
  have h2 : IntermediateField.relfinrank F₁ E * (1 + IntermediateField.relfinrank K₀ K₁) ≤ q + 1 :=
    Nat.le_of_mul_le_mul_left h1 hψpos
  have hd1 : IntermediateField.relfinrank F₁ E = 1 := by
    by_contra hne1
    have h3 : 2 ≤ IntermediateField.relfinrank F₁ E := by omega
    have h4 : 2 * (1 + q) ≤ IntermediateField.relfinrank F₁ E * (1 + IntermediateField.relfinrank K₀ K₁) :=
      Nat.mul_le_mul h3 (by omega)
    omega
  exact IntermediateField.relfinrank_eq_one_iff.mp hd1

end TwoProlongations

section Assembly

variable (N q : ℕ) [NeZero N] [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

theorem resHom_mem_fullC_N (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q) (f : gaussRing A (N * q)) :
    resHom A (N * q) f ∈ modularFunctionFieldFullC kk N :=
  resField_le_fullC hqN hA (resHom_mem_resField A (N * q) f)

def resN (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q) : gaussRing A (N * q) →+* Fb :=
  (resHom A (N * q)).codRestrict (modularFunctionFieldFullC kk N) (resHom_mem_fullC_N N q A hqN hA)

theorem coe_resN (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q) (f : gaussRing A (N * q)) :
    ((resN N q A hqN hA f : Fb) : LaurentSeries kk) = resHom A (N * q) f := rfl

set_option maxHeartbeats 6400000 in

theorem main (hqN : ¬ q ∣ N) (hA : A.LiesOverPrime q) :
    ∃ R : AlgebraicCurve.RegularProlongation A (modularFunctionFieldBar (N * q))
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      (∀ f : modularFunctionFieldBar (N * q), f ∈ R.integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A)
        (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q)),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y := by
  have hmem := resHom_mem_fullC_N N q A hqN hA
  refine ⟨{ integers := gaussRing A (N * q)
            residue := resN N q A hqN hA
            algebraMap_mem_iff := algebraMap_mem_gaussRing_iff A (N * q)
            residue_surjective := fun z => ?_
            ker_residue := ?_
            residue_algebraMap := fun a => Subtype.ext (resHom_algebraMap A (N * q) a _)
            exists_smul_mem := fun f hf => ?_ }, fun f => Iff.rfl, fun y hy => ?_⟩
  · obtain ⟨f, hf⟩ := exists_resHom_eq A (N * q)
      (full_degeneracyC_le (K := kk) (dvd_mul_right N q) z.2)
    exact ⟨f, Subtype.ext hf⟩
  · ext f
    rw [RingHom.mem_ker, ← resHom_eq_zero_iff, ← coe_resN N q A hqN hA f, ZeroMemClass.coe_eq_zero]
  · obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A (N * q) f hf
    exact ⟨c, h, fun h0 => hne (by rw [← coe_resN N q A hqN hA, h0]; rfl)⟩
  · exact ⟨ι_mem_gaussRing A (N * q) hy, by rw [coe_resN]; exact resHom_ι A (N * q) hy⟩

end Assembly

end W7NQG
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd.W7NQG"

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ R : AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar (N * q))
        (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      (∀ f : ModularCurve.modularFunctionFieldBar (N * q), f ∈ R.integers ↔
        ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A.subtype y
            = ModularCurve.coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar (N * q)),
        ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ : ModularCurve.modularFunctionFieldBar (N * q)) ∈
            R.integers,
          ((R.residue ⟨_, hint⟩ :
              ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y :=
  W7NQG.main N q A hqN hA

end
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd.W7NQG"

end S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd (solution)
