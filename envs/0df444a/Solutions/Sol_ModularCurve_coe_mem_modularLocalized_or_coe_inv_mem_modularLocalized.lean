-- Prove2me | solution 1 for ModularCurve.coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/cb773855-f844-5b74-93c2-756b8ce97a0d

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open scoped Classical
p2m_open "IntermediateField AlgebraicCurve ModularCurve~dedekindPsi_prime Polynomial"

namespace Ws25
namespace GaussE

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

theorem exists_primitive_poly {r : L[X]} (hr : r ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ r₀ : A[X], r = C c * r₀.map A.subtype ∧ r₀.map (IsLocalRing.residue A) ≠ 0 := by
  have hne : (r.support.image r.coeff).Nonempty := by
    rw [Finset.image_nonempty, Polynomial.nonempty_support_iff]; exact hr
  obtain ⟨c, hcT, hcmax⟩ := Finset.exists_max_image _ A.valuation hne
  obtain ⟨n₀, hn₀, rfl⟩ := Finset.mem_image.mp hcT
  have hc0 : r.coeff n₀ ≠ 0 := Polynomial.mem_support_iff.mp hn₀
  have hvx : ∀ n, A.valuation (r.coeff n) ≤ A.valuation (r.coeff n₀) := fun n => by
    by_cases hn : n ∈ r.support
    · exact hcmax _ (Finset.mem_image_of_mem _ hn)
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]; exact zero_le'
  have hcA : ∀ n, (r.coeff n₀)⁻¹ * r.coeff n ∈ A := fun n => by
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
    have hc' : A.valuation (r.coeff n₀) ≠ 0 := by simpa using hc0
    rw [inv_mul_le_one₀ (zero_lt_iff.mpr hc')]
    exact hvx n
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : A[X], r₀.map A.subtype = C (r.coeff n₀)⁻¹ * r := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul]
    exact ⟨⟨_, hcA n⟩, rfl⟩
  refine ⟨r.coeff n₀, hc0, r₀, ?_, ?_⟩
  · rw [hr₀, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]
  · intro h
    have h1 := congrArg (fun p : (IsLocalRing.ResidueField A)[X] => p.coeff n₀) h
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
    have h2 : (r₀.coeff n₀ : L) = 1 := by
      have := congrArg (fun p : L[X] => p.coeff n₀) hr₀
      simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul, inv_mul_cancel₀ hc0] at this
      exact this
    have h3 : r₀.coeff n₀ = 1 := Subtype.ext (by simpa using h2)
    rw [h3, map_one] at h1
    exact one_ne_zero h1

theorem algebraMap_laurentSeries_A (a : A) : algebraMap A (LaurentSeries A) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap A (PowerSeries A) a = PowerSeries.C a := by simp
  rw [h1, HahnSeries.ofPowerSeries_C]

theorem ι_aeval (p : A[X]) : ι A (aeval (jqModC A) p) = aeval (jqModC L) (p.map A.subtype) := by
  rw [aeval_def, aeval_def, hom_eval₂, eval₂_map, coeffMap_jqModC]
  congr 1
  refine RingHom.ext fun a => ?_
  change ι A (algebraMap A (LaurentSeries A) a) = algebraMap L (LaurentSeries L) (a : L)
  rw [algebraMap_laurentSeries_A]
  exact ι_C A a

theorem ϖ_aeval (p : A[X]) :
    ϖ A (aeval (jqModC A) p) = aeval (jqModC kk) (p.map (IsLocalRing.residue A)) := by
  rw [aeval_def, aeval_def, hom_eval₂, eval₂_map, coeffMap_jqModC]
  congr 1
  refine RingHom.ext fun a => ?_
  change ϖ A (algebraMap A (LaurentSeries A) a) =
    algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A a)
  rw [algebraMap_laurentSeries_A]
  exact ϖ_C A a

theorem aeval_jqModC_ne_zero {K : Type*} [Field K] {p : K[X]} (hp : p ≠ 0) :
    aeval (jqModC K) p ≠ 0 := fun h =>
  hp ((transcendental_iff.mp (ModularCurve.transcendental_jqModC K)) p h)

def jF : FF := ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (modularFunctionField_le_full N (jq_mem N))⟩

theorem coe_jF : ((jF N : FF) : LaurentSeries L) = jqModC L := coeffMap_jqModC _

theorem coe_jF' : ((jF N : FF) : LaurentSeries L) = ι A (jqModC A) := by
  rw [coe_jF, coeffMap_jqModC]

def jbar (K : Type*) [Field K] : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

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

section Assembly

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

theorem dedekindPsi_pos : 0 < dedekindPsi N := by
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, NeZero.ne N]
  calc 0 < N / 1 := by simpa using Nat.pos_of_ne_zero (NeZero.ne N)
    _ ≤ dedekindPsi N := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1

def resF (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) :
    gaussRing A N →+* Fb :=
  (resHom A N).codRestrict (modularFunctionFieldFullC kk N) hmem

theorem coe_resF (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) (f : gaussRing A N) : ((resF A N hmem f : Fb) : LaurentSeries kk) = resHom A N f := rfl

theorem resF_ne_zero_iff (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) (f : gaussRing A N) : resF A N hmem f ≠ 0 ↔ resHom A N f ≠ 0 := by
  rw [Ne, Ne, ← coe_resF A N hmem f, ZeroMemClass.coe_eq_zero]

theorem resF_surjective (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) : Function.Surjective (resF A N hmem) := fun z => by
  obtain ⟨f, hf⟩ := exists_resHom_eq A N z.2
  exact ⟨f, Subtype.ext hf⟩

theorem ker_resF (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) : RingHom.ker (resF A N hmem) = IsLocalRing.maximalIdeal (gaussRing A N) := by
  ext f
  rw [RingHom.mem_ker, ← resHom_eq_zero_iff, ← coe_resF A N hmem f, ZeroMemClass.coe_eq_zero]

theorem resF_algebraMap (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) (a : A) (h : algebraMap L FF a ∈ gaussRing A N) :
    resF A N hmem ⟨algebraMap L FF a, h⟩ = algebraMap kk Fb (IsLocalRing.residue A a) :=
  Subtype.ext (resHom_algebraMap A N a h)

theorem exists_smul_mem_resF (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A N, resF A N hmem ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A N f hf
  exact ⟨c, h, (resF_ne_zero_iff A N hmem _).mpr hne⟩

theorem jF_mem_gaussRing : (jF N : FF) ∈ gaussRing A N :=
  (mem_gaussRing_iff A N _).mpr ⟨jqModC A, 1, by rw [map_one]; exact one_ne_zero,
    by rw [map_one, mul_one, coe_jF']⟩

theorem resHom_jF : resHom A N ⟨jF N, jF_mem_gaussRing A N⟩ = jqModC kk := by
  rw [resHom_eq A N (f := ⟨jF N, jF_mem_gaussRing A N⟩) (x := jqModC A) (y := 1)
    (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact coe_jF' A N),
    map_one, div_one, coeffMap_jqModC]

theorem resF_jF (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) : resF A N hmem ⟨jF N, jF_mem_gaussRing A N⟩ = jbar N kk :=
  Subtype.ext (resHom_jF A N)

theorem transcendental_jbar (K : Type*) [Field K] : Transcendental K (jbar N K : modularFunctionFieldFullC K N) :=
  fun h => transcendental_jqModC K
    ((isAlgebraic_algHom_iff (modularFunctionFieldFullC K N).val Subtype.val_injective).mpr h)

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

end Assembly

section ResField

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem isUnit_of_resHom_ne_zero {f : gaussRing A N} (h0 : resHom A N f ≠ 0) : IsUnit f := by
  by_contra hu
  exact h0 ((resHom_eq_zero_iff A N f).mpr
    ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)))

theorem resHom_ne_zero_of_isUnit {f : gaussRing A N} (hu : IsUnit f) : resHom A N f ≠ 0 := by
  intro h0
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
    ((resHom_eq_zero_iff A N f).mp h0))) hu

def resField : IntermediateField kk (LaurentSeries kk) where
  carrier := Set.range (resHom A N)
  mul_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f * g, map_mul _ _ _⟩
  one_mem' := ⟨1, map_one _⟩
  add_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f + g, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  algebraMap_mem' t := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
    exact ⟨⟨_, (algebraMap_mem_gaussRing_iff A N (a : L)).mpr a.2⟩, resHom_algebraMap A N a _⟩
  inv_mem' := by
    rintro _ ⟨f, rfl⟩
    by_cases h0 : resHom A N f = 0
    · exact ⟨0, by rw [h0, inv_zero, map_zero]⟩
    · obtain ⟨u, rfl⟩ := isUnit_of_resHom_ne_zero A N h0
      refine ⟨↑u⁻¹, ?_⟩
      exact (inv_eq_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])).symm

theorem mem_resField_iff {z : LaurentSeries kk} : z ∈ resField A N ↔ ∃ f, resHom A N f = z :=
  Iff.rfl

def resR : gaussRing A N →+* resField A N where
  toFun f := ⟨resHom A N f, f, rfl⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' f g := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' f g := Subtype.ext (map_add _ _ _)

theorem coe_resR (f : gaussRing A N) : ((resR A N f : resField A N) : LaurentSeries kk) = resHom A N f :=
  rfl

theorem resR_surjective : Function.Surjective (resR A N) := by
  rintro ⟨_, f, rfl⟩; exact ⟨f, rfl⟩

theorem resR_eq_zero_iff (f : gaussRing A N) : resR A N f = 0 ↔ resHom A N f = 0 := by
  rw [← coe_resR A N f, ZeroMemClass.coe_eq_zero]

theorem ker_resR : RingHom.ker (resR A N) = IsLocalRing.maximalIdeal (gaussRing A N) := by
  ext f
  rw [RingHom.mem_ker, resR_eq_zero_iff, resHom_eq_zero_iff]

theorem resR_algebraMap (a : A) (h : algebraMap L FF a ∈ gaussRing A N) :
    resR A N ⟨algebraMap L FF a, h⟩ = algebraMap kk (resField A N) (IsLocalRing.residue A a) :=
  Subtype.ext (resHom_algebraMap A N a h)

def Rgauss : RegularProlongation A FF (resField A N) where
  integers := gaussRing A N
  residue := resR A N
  algebraMap_mem_iff := algebraMap_mem_gaussRing_iff A N
  residue_surjective := resR_surjective A N
  ker_residue := ker_resR A N
  residue_algebraMap a := resR_algebraMap A N a _
  exists_smul_mem f hf := by
    obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A N f hf
    exact ⟨c, h, fun h0 => hne ((resR_eq_zero_iff A N _).mp h0)⟩

def gaussComap (σ : FF ≃ₐ[L] FF) : ValuationSubring FF := (gaussRing A N).comap (σ : FF →+* FF)

theorem mem_gaussComap (σ : FF ≃ₐ[L] FF) {x : FF} : x ∈ gaussComap A N σ ↔ σ x ∈ gaussRing A N := Iff.rfl

def sigmaRes (σ : FF ≃ₐ[L] FF) : gaussComap A N σ →+* gaussRing A N where
  toFun x := ⟨σ x, x.2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' x y := Subtype.ext (map_mul σ _ _)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' x y := Subtype.ext (map_add σ _ _)

theorem coe_sigmaRes (σ : FF ≃ₐ[L] FF) (x : gaussComap A N σ) : ((sigmaRes A N σ x : gaussRing A N) : FF) = σ x := rfl

theorem isUnit_sigmaRes_iff (σ : FF ≃ₐ[L] FF) (x : gaussComap A N σ) : IsUnit (sigmaRes A N σ x) ↔ IsUnit x := by
  constructor
  · rintro ⟨u, hu⟩
    have hv : σ.symm ((↑u⁻¹ : gaussRing A N) : FF) ∈ gaussComap A N σ := by
      rw [mem_gaussComap, AlgEquiv.apply_symm_apply]; exact (↑u⁻¹ : gaussRing A N).2
    refine ⟨⟨x, ⟨_, hv⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · apply σ.injective
      show σ ((x : FF) * σ.symm ((↑u⁻¹ : gaussRing A N) : FF)) = σ 1
      rw [map_mul, AlgEquiv.apply_symm_apply, map_one]
      have := congrArg (fun w : gaussRing A N => (w : FF)) u.mul_inv
      simpa [hu, coe_sigmaRes] using this
    · apply σ.injective
      show σ (σ.symm ((↑u⁻¹ : gaussRing A N) : FF) * (x : FF)) = σ 1
      rw [map_mul, AlgEquiv.apply_symm_apply, map_one]
      have := congrArg (fun w : gaussRing A N => (w : FF)) u.inv_mul
      simpa [hu, coe_sigmaRes] using this
  · intro hx
    exact hx.map (sigmaRes A N σ)

def Rsigma (σ : FF ≃ₐ[L] FF) : RegularProlongation A FF (resField A N) where
  integers := gaussComap A N σ
  residue := (resR A N).comp (sigmaRes A N σ)
  algebraMap_mem_iff x := by
    rw [mem_gaussComap, AlgEquiv.commutes]; exact algebraMap_mem_gaussRing_iff A N x
  residue_surjective := by
    intro z
    obtain ⟨f, rfl⟩ := resR_surjective A N z
    have hmem : σ.symm (f : FF) ∈ gaussComap A N σ := by
      rw [mem_gaussComap, AlgEquiv.apply_symm_apply]; exact f.2
    refine ⟨⟨σ.symm (f : FF), hmem⟩, ?_⟩
    rw [RingHom.comp_apply]
    congr 1
    exact Subtype.ext (σ.apply_symm_apply (f : FF))
  ker_residue := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, resR_eq_zero_iff, resHom_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_sigmaRes_iff]
  residue_algebraMap a := by
    rw [RingHom.comp_apply]
    convert resR_algebraMap A N a ((algebraMap_mem_gaussRing_iff A N a).mpr a.2) using 2
    exact Subtype.ext (σ.commutes a)
  exists_smul_mem f hf := by
    obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A N (σ f) ((map_ne_zero σ).mpr hf)
    have hσ : σ (c • f) = c • σ f := map_smul σ c f
    have hmem : c • f ∈ gaussComap A N σ := by rw [mem_gaussComap, hσ]; exact h
    refine ⟨c, hmem, fun h0 => hne ?_⟩
    rw [RingHom.comp_apply, resR_eq_zero_iff] at h0
    have : sigmaRes A N σ ⟨c • f, hmem⟩ = ⟨c • σ f, h⟩ := Subtype.ext hσ
    rwa [this] at h0

end ResField

section Orders

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem dvd_order_of_mem_range_qExpand {x : LaurentSeries K}
    (hx : x ∈ Set.range (qExpand K N)) (h0 : x ≠ 0) : (N : ℤ) ∣ x.order := by
  by_contra hnd
  obtain ⟨y, rfl⟩ := hx
  exact (HahnSeries.coeff_order_eq_zero.not.mpr h0) (qExpand_coeff_of_not_dvd (R := K) (N := N) y hnd)

theorem order_jqModC_pow (b : ℕ) : (jqModC K ^ b).order = -(b : ℤ) := by
  have h1 : (jqModC K ^ b).coeff (-(b : ℤ)) ≠ 0 := by
    rw [ModularCurve.coeff_jqModC_pow_self]; exact one_ne_zero
  have h0 : jqModC K ^ b ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  have hle : (jqModC K ^ b).order ≤ -(b : ℤ) := HahnSeries.order_le_of_coeff_ne_zero h1
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd (ModularCurve.coeff_jqModC_pow_of_lt K hlt) (HahnSeries.coeff_order_eq_zero.not.mpr h0)
  · exact heq

theorem order_mul_pow_jqModC {c : LaurentSeries K} (hc : c ≠ 0) (b : ℕ) :
    (c * jqModC K ^ b).order = c.order - b := by
  have h0 : jqModC K ^ b ≠ 0 := pow_ne_zero _ (jqModC_ne_zero_of_nontrivial K)
  rw [HahnSeries.order_mul_of_ne_zero (mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hc)
    (HahnSeries.leadingCoeff_ne_zero.mpr h0)), order_jqModC_pow, sub_eq_add_neg]

theorem eq_zero_of_sum_mul_pow_jqModC_eq_zero (c : Fin N → LaurentSeries K)
    (hc : ∀ i, c i ∈ Set.range (qExpand K N))
    (h : ∑ i, c i * jqModC K ^ (i : ℕ) = 0) : ∀ i, c i = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  classical

  have hTne : (Finset.univ.filter fun i : Fin N => c i ≠ 0).Nonempty :=
    ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₁⟩⟩

  have hinj : ∀ i i' : Fin N, c i ≠ 0 → c i' ≠ 0 →
      (c i * jqModC K ^ (i : ℕ)).order = (c i' * jqModC K ^ (i' : ℕ)).order → i = i' := by
    intro i i' hi hi' he
    rw [order_mul_pow_jqModC K hi, order_mul_pow_jqModC K hi'] at he
    obtain ⟨a, ha⟩ := dvd_order_of_mem_range_qExpand K N (hc i) hi
    obtain ⟨a', ha'⟩ := dvd_order_of_mem_range_qExpand K N (hc i') hi'
    rw [ha, ha'] at he
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hmod : ((i : ℕ) : ℤ) % N = ((i' : ℕ) : ℤ) % N := by
      have : ((i : ℕ) : ℤ) = ((i' : ℕ) : ℤ) + N * (a - a') := by linear_combination -he
      rw [this, Int.add_mul_emod_self_left]
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.2),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i'.2)] at hmod
    exact Fin.ext (by exact_mod_cast hmod)

  obtain ⟨i₀, hi₀T, hmin⟩ := (Finset.univ.filter fun i : Fin N => c i ≠ 0).exists_min_image
    (fun i => (c i * jqModC K ^ (i : ℕ)).order) hTne
  have hi₀ : c i₀ ≠ 0 := (Finset.mem_filter.mp hi₀T).2
  have ht₀ : c i₀ * jqModC K ^ (i₀ : ℕ) ≠ 0 :=
    mul_ne_zero hi₀ (pow_ne_zero _ (jqModC_ne_zero_of_nontrivial K))

  have hcoeff : (∑ i, c i * jqModC K ^ (i : ℕ)).coeff (c i₀ * jqModC K ^ (i₀ : ℕ)).order
      = (c i₀ * jqModC K ^ (i₀ : ℕ)).coeff (c i₀ * jqModC K ^ (i₀ : ℕ)).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ _) h)
    by_cases hci : c i = 0
    · rw [hci, zero_mul, HahnSeries.coeff_zero]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      have hle := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩)
      exact lt_of_le_of_ne hle fun he => hi (hinj i i₀ hci hi₀ he.symm)
  rw [h, HahnSeries.coeff_zero] at hcoeff
  exact (HahnSeries.coeff_order_eq_zero.not.mpr ht₀) hcoeff.symm

end Orders

section Count

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by
  rw [dedekindPsi, Nat.Prime.divisors hp]
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  rw [Finset.filter_insert, if_pos squarefree_one, Finset.filter_singleton,
    if_pos hp.squarefree, Finset.sum_insert (by simpa using h1p), Finset.sum_singleton,
    Nat.div_one, Nat.div_self hp.pos, add_comm]

def jNF : FF := ⟨ι A (qExpand A N (jqModC A)), by
  rw [ι_qExpand_jqModC, ← coeffEmb_qExpand_jq]
  exact coeffEmb_mem_laurentBaseChange L (jqd_mem_full N (dvd_refl N))⟩

theorem coe_jNF : ((jNF A N : FF) : LaurentSeries L) = qExpand L N (jqModC L) := ι_qExpand_jqModC A N

theorem jNF_mem_gaussRing : (jNF A N : FF) ∈ gaussRing A N := ι_mem_gaussRing A N _

theorem resHom_jNF : resHom A N ⟨jNF A N, jNF_mem_gaussRing A N⟩ = qExpand kk N (jqModC kk) :=
  (resHom_ι A N _).trans (ϖ_qExpand_jqModC A N)

def twoR (σ : FF ≃ₐ[L] FF) : Bool → RegularProlongation A FF (resField A N)
  | true => Rgauss A N
  | false => Rsigma A N σ

theorem twoR_integers_true (σ : FF ≃ₐ[L] FF) : (twoR A N σ true).integers = gaussRing A N := rfl
theorem twoR_integers_false (σ : FF ≃ₐ[L] FF) : (twoR A N σ false).integers = gaussComap A N σ := rfl

theorem twoR_injective (σ : FF ≃ₐ[L] FF) (hσO : gaussComap A N σ ≠ gaussRing A N) :
    Function.Injective fun b : Bool => (twoR A N σ b).integers := by
  intro b b' h
  cases b <;> cases b'
  · rfl
  · exact absurd h hσO
  · exact absurd h.symm hσO
  · rfl

theorem jF_mem_twoR (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N) : ∀ b, (jF N : FF) ∈ (twoR A N σ b).integers
  | true => jF_mem_gaussRing A N
  | false => by
      show σ (jF N) ∈ gaussRing A N
      rw [hσj]; exact jNF_mem_gaussRing A N

theorem coe_residue_twoR_true (σ : FF ≃ₐ[L] FF) (h : (jF N : FF) ∈ (twoR A N σ true).integers) :
    (((twoR A N σ true).residue ⟨jF N, h⟩ : resField A N) : LaurentSeries kk) = jqModC kk :=
  resHom_jF A N

theorem coe_residue_twoR_false (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N) (h : (jF N : FF) ∈ (twoR A N σ false).integers) :
    (((twoR A N σ false).residue ⟨jF N, h⟩ : resField A N) : LaurentSeries kk) = qExpand kk N (jqModC kk) := by
  show resHom A N (sigmaRes A N σ ⟨jF N, h⟩) = _
  have : sigmaRes A N σ ⟨jF N, h⟩ = ⟨jNF A N, jNF_mem_gaussRing A N⟩ := Subtype.ext hσj
  rw [this, resHom_jNF]

theorem transcendental_of_coe {x : resField A N}
    (hx : Transcendental kk ((x : resField A N) : LaurentSeries kk)) : Transcendental kk x :=
  fun h => hx (h.algHom (resField A N).val)

theorem transcendental_qExpand_jqModC : Transcendental kk (qExpand kk N (jqModC kk)) := fun h =>
  ModularCurve.transcendental_jqModC kk
    ((isAlgebraic_algHom_iff (qExpandAlgHomC kk N) (qExpand_injective (R := kk) (N := N))).mp h)

def preIF (E : IntermediateField kk (LaurentSeries kk)) : IntermediateField kk (resField A N) where
  toSubalgebra := E.toSubalgebra.comap (resField A N).val
  inv_mem' x hx := by
    have hx' : (resField A N).val x ∈ E := hx
    have h : (resField A N).val x⁻¹ ∈ E := by rw [map_inv₀]; exact E.inv_mem hx'
    exact h

theorem mem_preIF {E : IntermediateField kk (LaurentSeries kk)} {x : resField A N} :
    x ∈ preIF A N E ↔ ((x : resField A N) : LaurentSeries kk) ∈ E := Iff.rfl

theorem linearIndependent_pow_jres (jres jNres : resField A N)
    (hj : (jres : LaurentSeries kk) = jqModC kk) (hjN : (jNres : LaurentSeries kk) = qExpand kk N (jqModC kk)) :
    LinearIndependent (IntermediateField.adjoin kk ({jNres} : Set (resField A N)))
      (fun i : Fin N => jres ^ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i

  have hS : ∀ i, (((g i : resField A N) : LaurentSeries kk)) ∈ Set.range (qExpand kk N) := by
    intro i
    have hle : IntermediateField.adjoin kk ({jNres} : Set (resField A N))
        ≤ preIF A N (qExpandAlgHomC kk N).fieldRange := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      show jNres ∈ preIF A N (qExpandAlgHomC kk N).fieldRange
      rw [mem_preIF, hjN]
      exact ⟨jqModC kk, rfl⟩
    obtain ⟨y, hy⟩ := (mem_preIF A N).mp (hle (g i).2)
    exact ⟨y, hy⟩
  have hrel : ∑ i, ((g i : resField A N) : LaurentSeries kk) * jqModC kk ^ (i : ℕ) = 0 := by
    have h1 := congrArg (resField A N).val hg
    rw [map_sum, map_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.smul_def, smul_eq_mul, map_mul, map_pow, ← hj]
    rfl
  have h0 := eq_zero_of_sum_mul_pow_jqModC_eq_zero kk N _ hS hrel i
  exact Subtype.ext (Subtype.ext h0)

theorem mem_adjoin_of_count (jres jNres : resField A N)
    (hj : (jres : LaurentSeries kk) = jqModC kk)
    (hjN : (jNres : LaurentSeries kk) = qExpand kk N (jqModC kk))
    (hfinT : FiniteDimensional (IntermediateField.adjoin kk ({jres} : Set (resField A N))) (resField A N))
    (hfinF : FiniteDimensional (IntermediateField.adjoin kk ({jNres} : Set (resField A N))) (resField A N))
    (hsum : Module.finrank (IntermediateField.adjoin kk ({jres} : Set (resField A N))) (resField A N)
      + Module.finrank (IntermediateField.adjoin kk ({jNres} : Set (resField A N))) (resField A N) ≤ N + 1)
    (y : resField A N) : y ∈ IntermediateField.adjoin kk ({jres} : Set (resField A N)) := by
  haveI := hfinT
  haveI := hfinF

  have hlow : N ≤ Module.finrank (IntermediateField.adjoin kk ({jNres} : Set (resField A N))) (resField A N) := by
    have := (linearIndependent_pow_jres A N jres jNres hj hjN).fintype_card_le_finrank
    rwa [Fintype.card_fin] at this

  have hle1 : Module.finrank (IntermediateField.adjoin kk ({jres} : Set (resField A N))) (resField A N) ≤ 1 := by
    omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hle1
  obtain ⟨c₁, hc₁⟩ := hv 1
  obtain ⟨c, hc⟩ := hv y
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₁
    exact one_ne_zero hc₁.symm
  have hvE : v = ((c₁⁻¹ : IntermediateField.adjoin kk ({jres} : Set (resField A N))) : resField A N) := by
    have h2 : (c₁⁻¹ * c₁) • v = c₁⁻¹ • (1 : resField A N) := by rw [mul_smul, hc₁]
    rwa [inv_mul_cancel₀ hc₁0, one_smul, IntermediateField.smul_def, smul_eq_mul, mul_one] at h2
  rw [← hc, hvE, IntermediateField.smul_def, smul_eq_mul]
  exact mul_mem c.2 (c₁⁻¹).2

theorem resHom_mem_fullC_of_sigma (σ : FF ≃ₐ[L] FF) (hσO : gaussComap A N σ ≠ gaussRing A N)
    (hN : (N : L) ≠ 0) (hp : N.Prime) (hσj : σ (jF N) = jNF A N)
    (f : gaussRing A N) : resHom A N f ∈ modularFunctionFieldFullC kk N := by

  haveI : FiniteDimensional (IntermediateField.adjoin L ({(jF N : FF)} : Set FF)) FF :=
    Module.finite_of_finrank_pos (by rw [finrank_adjoin_jF N hN]; exact dedekindPsi_pos N)
  have hf := jF_mem_twoR A N σ hσj
  have htr : ∀ b, Transcendental kk ((twoR A N σ b).residue ⟨jF N, hf b⟩) := by
    intro b; cases b
    · exact transcendental_of_coe A N (by rw [coe_residue_twoR_false A N σ hσj]; exact transcendental_qExpand_jqModC A N)
    · exact transcendental_of_coe A N (by rw [coe_residue_twoR_true A N σ]; exact ModularCurve.transcendental_jqModC kk)
  obtain ⟨hfin, hsum⟩ := AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le A
    (fun _ : Bool => resField A N) (twoR A N σ) (twoR_injective A N σ hσO) (jF N : FF) hf htr
  rw [Fintype.sum_bool, finrank_adjoin_jF N hN, dedekindPsi_prime hp] at hsum
  have hj : (((twoR A N σ true).residue ⟨jF N, hf true⟩ : resField A N) : LaurentSeries kk) = jqModC kk :=
    coe_residue_twoR_true A N σ (hf true)
  have hjN : (((twoR A N σ false).residue ⟨jF N, hf false⟩ : resField A N) : LaurentSeries kk)
      = qExpand kk N (jqModC kk) := coe_residue_twoR_false A N σ hσj (hf false)
  have htop := mem_adjoin_of_count A N _ _ hj hjN (hfin true) (hfin false) hsum

  have hle : IntermediateField.adjoin kk ({(twoR A N σ true).residue ⟨jF N, hf true⟩} : Set (resField A N))
      ≤ preIF A N (modularFunctionFieldFullC kk N) := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    show (twoR A N σ true).residue ⟨jF N, hf true⟩ ∈ preIF A N (modularFunctionFieldFullC kk N)
    rw [mem_preIF, hj]
    exact jqModC_mem_full kk N
  exact (mem_preIF A N).mp (hle (htop (resR A N f)))

theorem exists_regularProlongation_of_sigma (σ : FF ≃ₐ[L] FF) (hσO : gaussComap A N σ ≠ gaussRing A N)
    (hN : (N : L) ≠ 0) (hp : N.Prime) (hσj : σ (jF N) = jNF A N) :
    ∃ R : AlgebraicCurve.RegularProlongation A FF (modularFunctionFieldFullC kk N),
      R.integers = gaussRing A N ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : modularFunctionFieldFullC kk N) : LaurentSeries kk) =
            coeffMap (IsLocalRing.residue A) y := by
  have hmem := resHom_mem_fullC_of_sigma A N σ hσO hN hp hσj
  refine ⟨{ integers := gaussRing A N
            residue := resF A N hmem
            algebraMap_mem_iff := algebraMap_mem_gaussRing_iff A N
            residue_surjective := resF_surjective A N hmem
            ker_residue := ker_resF A N hmem
            residue_algebraMap := fun a => resF_algebraMap A N hmem a _
            exists_smul_mem := exists_smul_mem_resF A N hmem }, rfl, fun y hy => ?_⟩
  exact ⟨ι_mem_gaussRing A N hy, by rw [coe_resF]; exact resHom_ι A N hy⟩

end Count

section MapResidue

variable {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
  {Fbar Fbar' : Type*} [Field Fbar] [Field Fbar'] [Algebra (IsLocalRing.ResidueField A) Fbar]
  [Algebra (IsLocalRing.ResidueField A) Fbar']

private def _root_.AlgebraicCurve.RegularProlongation.mapResidue (R : RegularProlongation A F Fbar)
    (e : Fbar ≃ₐ[IsLocalRing.ResidueField A] Fbar') : RegularProlongation A F Fbar' where
  integers := R.integers
  residue := (e : Fbar →+* Fbar').comp R.residue
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := e.surjective.comp R.residue_surjective
  ker_residue := by
    rw [← R.ker_residue]; ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, RingHom.coe_coe, map_eq_zero_iff e e.injective]
  residue_algebraMap a := by
    rw [RingHom.comp_apply, RingHom.coe_coe, R.residue_algebraMap, AlgEquiv.commutes]
  exists_smul_mem f hf := by
    obtain ⟨c, h, hne⟩ := R.exists_smul_mem f hf
    exact ⟨c, h, by rw [RingHom.comp_apply, RingHom.coe_coe, map_ne_zero_iff e e.injective]; exact hne⟩

p2m_alias "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.AlgebraicCurve.RegularProlongation.mapResidue" "AlgebraicCurve.RegularProlongation.mapResidue"
@[scoped simp] private theorem _root_.AlgebraicCurve.RegularProlongation.mapResidue_integers (R : RegularProlongation A F Fbar)
    (e : Fbar ≃ₐ[IsLocalRing.ResidueField A] Fbar') : (R.mapResidue A e).integers = R.integers := rfl

p2m_alias "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.AlgebraicCurve.RegularProlongation.mapResidue_integers" "AlgebraicCurve.RegularProlongation.mapResidue_integers"
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"
private theorem _root_.AlgebraicCurve.RegularProlongation.mapResidue_residue (R : RegularProlongation A F Fbar)
    (e : Fbar ≃ₐ[IsLocalRing.ResidueField A] Fbar') (x : R.integers) :
    (R.mapResidue A e).residue x = e (R.residue x) := rfl

p2m_alias "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.AlgebraicCurve.RegularProlongation.mapResidue_residue" "AlgebraicCurve.RegularProlongation.mapResidue_residue"
end MapResidue
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Transport

variable {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

def comapRes (O : ValuationSubring F) (σ : F ≃ₐ[L] F) : O.comap (σ : F →+* F) →+* O where
  toFun x := ⟨σ x, x.2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' x y := Subtype.ext (map_mul σ _ _)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' x y := Subtype.ext (map_add σ _ _)

theorem coe_comapRes (O : ValuationSubring F) (σ : F ≃ₐ[L] F) (x : O.comap (σ : F →+* F)) :
    ((comapRes (L := L) O σ x : O) : F) = σ x := rfl

theorem isUnit_comapRes_iff (O : ValuationSubring F) (σ : F ≃ₐ[L] F) (x : O.comap (σ : F →+* F)) :
    IsUnit (comapRes (L := L) O σ x) ↔ IsUnit x := by
  constructor
  · rintro ⟨u, hu⟩
    have hv : σ.symm ((↑u⁻¹ : O) : F) ∈ O.comap (σ : F →+* F) := by
      show σ (σ.symm _) ∈ O
      rw [AlgEquiv.apply_symm_apply]; exact (↑u⁻¹ : O).2
    refine ⟨⟨x, ⟨_, hv⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · apply σ.injective
      show σ ((x : F) * σ.symm ((↑u⁻¹ : O) : F)) = σ 1
      rw [map_mul, AlgEquiv.apply_symm_apply, map_one]
      have := congrArg (fun w : O => (w : F)) u.mul_inv
      simpa [hu, coe_comapRes] using this
    · apply σ.injective
      show σ (σ.symm ((↑u⁻¹ : O) : F) * (x : F)) = σ 1
      rw [map_mul, AlgEquiv.apply_symm_apply, map_one]
      have := congrArg (fun w : O => (w : F)) u.inv_mul
      simpa [hu, coe_comapRes] using this
  · intro hx
    exact hx.map (comapRes (L := L) O σ)

private def _root_.AlgebraicCurve.RegularProlongation.transport (R : RegularProlongation A F Fbar) (σ : F ≃ₐ[L] F) :
    RegularProlongation A F Fbar where
  integers := R.integers.comap (σ : F →+* F)
  residue := R.residue.comp (comapRes (L := L) R.integers σ)
  algebraMap_mem_iff x := by
    show σ (algebraMap L F x) ∈ R.integers ↔ x ∈ A
    rw [AlgEquiv.commutes]; exact R.algebraMap_mem_iff x
  residue_surjective := by
    intro z
    obtain ⟨f, rfl⟩ := R.residue_surjective z
    have hmem : σ.symm (f : F) ∈ R.integers.comap (σ : F →+* F) := by
      show σ (σ.symm _) ∈ R.integers
      rw [AlgEquiv.apply_symm_apply]; exact f.2
    refine ⟨⟨σ.symm (f : F), hmem⟩, ?_⟩
    rw [RingHom.comp_apply]
    congr 1
    exact Subtype.ext (σ.apply_symm_apply (f : F))
  ker_residue := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, R.ker_residue,
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_comapRes_iff]
  residue_algebraMap a := by
    rw [RingHom.comp_apply]
    convert R.residue_algebraMap a using 2
    exact Subtype.ext (σ.commutes a)
  exists_smul_mem f hf := by
    obtain ⟨c, h, hne⟩ := R.exists_smul_mem (σ f) ((map_ne_zero σ).mpr hf)
    have hσ : σ (c • f) = c • σ f := map_smul σ c f
    have hmem : c • f ∈ R.integers.comap (σ : F →+* F) := by
      show σ (c • f) ∈ R.integers
      rw [hσ]; exact h
    refine ⟨c, hmem, fun h0 => hne ?_⟩
    rw [RingHom.comp_apply] at h0
    have : comapRes (L := L) R.integers σ ⟨c • f, hmem⟩ = ⟨c • σ f, h⟩ := Subtype.ext hσ
    rwa [this] at h0

p2m_alias "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.AlgebraicCurve.RegularProlongation.transport" "AlgebraicCurve.RegularProlongation.transport"
private theorem _root_.AlgebraicCurve.RegularProlongation.mem_transport_integers_iff (R : RegularProlongation A F Fbar)
    (σ : F ≃ₐ[L] F) (f : F) : f ∈ (R.transport A σ).integers ↔ σ f ∈ R.integers := Iff.rfl

p2m_alias "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.AlgebraicCurve.RegularProlongation.mem_transport_integers_iff" "AlgebraicCurve.RegularProlongation.mem_transport_integers_iff"
private theorem _root_.AlgebraicCurve.RegularProlongation.transport_residue (R : RegularProlongation A F Fbar)
    (σ : F ≃ₐ[L] F) (f : F) (h : f ∈ (R.transport A σ).integers) :
    (R.transport A σ).residue ⟨f, h⟩ = R.residue ⟨σ f, h⟩ := rfl

p2m_alias "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.AlgebraicCurve.RegularProlongation.transport_residue" "AlgebraicCurve.RegularProlongation.transport_residue"
end Transport
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Rfull

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

def Rfull (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) :
    RegularProlongation A FF (modularFunctionFieldFullC kk N) where
  integers := gaussRing A N
  residue := resF A N hmem
  algebraMap_mem_iff := algebraMap_mem_gaussRing_iff A N
  residue_surjective := resF_surjective A N hmem
  ker_residue := ker_resF A N hmem
  residue_algebraMap a := resF_algebraMap A N hmem a _
  exists_smul_mem := exists_smul_mem_resF A N hmem

theorem Rfull_integers (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) :
    (Rfull A N hmem).integers = gaussRing A N := rfl

theorem coe_Rfull_residue (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N)
    (f : gaussRing A N) :
    (((Rfull A N hmem).residue f : modularFunctionFieldFullC kk N) : LaurentSeries kk) = resHom A N f := rfl

end Rfull
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section SigmaQExpand

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem coe_sigma_eq_qExpand_of_mem_adjoin (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N)
    {x : FF} (hx : x ∈ IntermediateField.adjoin L ({(jF N : FF)} : Set FF)) :
    ((σ x : FF) : LaurentSeries L) = qExpand L N (x : LaurentSeries L) := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [hσj, coe_jNF, coe_jF]
  | algebraMap c =>
      rw [AlgEquiv.commutes, coe_algebraMap, algebraMap_laurentSeries_eq_single, qExpand_single,
        mul_zero]
  | add x y _ _ hx hy =>
      rw [map_add, IntermediateField.coe_add, IntermediateField.coe_add, map_add, hx, hy]
  | inv x _ hx =>
      rw [map_inv₀, IntermediateField.coe_inv, IntermediateField.coe_inv, map_inv₀, hx]
  | mul x y _ _ hx hy =>
      rw [map_mul, IntermediateField.coe_mul, IntermediateField.coe_mul, map_mul, hx, hy]

theorem isInt_qExpand {f : LaurentSeries L} (hf : IsInt A f) : IsInt A (qExpand L N f) := by
  obtain ⟨x, y, hy, h⟩ := hf
  refine ⟨ModularCurve.qExpand A N x, ModularCurve.qExpand A N y, ?_, ?_⟩
  · rw [coeffMap_qExpand]
    exact fun h0 => hy (qExpand_injective (R := kk) (N := N) (by rw [h0, map_zero]))
  · show qExpand L N f * ι A (ModularCurve.qExpand A N y) = ι A (ModularCurve.qExpand A N x)
    rw [coeffMap_qExpand, coeffMap_qExpand, ← map_mul, h]

theorem mem_gaussRing_of_coe_eq_qExpand {f g : FF} (hf : f ∈ gaussRing A N)
    (h : (g : LaurentSeries L) = qExpand L N (f : LaurentSeries L)) : g ∈ gaussRing A N := by
  show IsInt A (g : LaurentSeries L)
  rw [h]; exact isInt_qExpand A N hf

theorem resHom_eq_qExpand_resHom (f g : gaussRing A N)
    (h : ((g : FF) : LaurentSeries L) = qExpand L N ((f : FF) : LaurentSeries L)) :
    resHom A N g = qExpand kk N (resHom A N f) := by
  obtain ⟨hy, hf⟩ := wit_spec A N f
  have hg : ((g : FF) : LaurentSeries L) * ι A (ModularCurve.qExpand A N (wit A N f).2)
      = ι A (ModularCurve.qExpand A N (wit A N f).1) := by
    rw [h, coeffMap_qExpand, coeffMap_qExpand, ← map_mul, hf]
  have hy' : ϖ A (ModularCurve.qExpand A N (wit A N f).2) ≠ 0 := by
    rw [coeffMap_qExpand]
    exact fun h0 => hy (qExpand_injective (R := kk) (N := N) (by rw [h0, map_zero]))
  rw [resHom_eq A N hy' hg, resHom_eq A N hy hf, coeffMap_qExpand, coeffMap_qExpand, map_div₀]

theorem mem_gaussComap_of_mem_adjoin (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N)
    {x : FF} (hx : x ∈ IntermediateField.adjoin L ({(jF N : FF)} : Set FF))
    (hxO : x ∈ gaussRing A N) : x ∈ gaussComap A N σ := by
  rw [mem_gaussComap]
  exact mem_gaussRing_of_coe_eq_qExpand A N hxO (coe_sigma_eq_qExpand_of_mem_adjoin A N σ hσj hx)

theorem resHom_sigmaRes_of_mem_adjoin (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N)
    {x : FF} (hx : x ∈ IntermediateField.adjoin L ({(jF N : FF)} : Set FF))
    (hxO : x ∈ gaussRing A N) :
    resHom A N (sigmaRes A N σ ⟨x, mem_gaussComap_of_mem_adjoin A N σ hσj hx hxO⟩)
      = qExpand kk N (resHom A N ⟨x, hxO⟩) :=
  resHom_eq_qExpand_resHom A N ⟨x, hxO⟩ _ (coe_sigma_eq_qExpand_of_mem_adjoin A N σ hσj hx)

end SigmaQExpand
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Archimedean

open Polynomial

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem exists_ne_val_eq_of_sum_eq_zero {ι : Type*} (s : Finset ι) (t : ι → K)
    (hsum : ∑ i ∈ s, t i = 0) {i₁ : ι} (hi₁ : i₁ ∈ s) (ht₁ : t i₁ ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ t i ≠ 0 ∧ t j ≠ 0 ∧ v (t i) = v (t j) := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image (fun i => v (t i)) ⟨i₁, hi₁⟩
  have hpos₁ : 0 < v (t i₁) := (Valuation.pos_iff v).mpr ht₁
  have ht₀ : t i₀ ≠ 0 := (Valuation.pos_iff v).mp (lt_of_lt_of_le hpos₁ (hmax i₁ hi₁))
  by_contra hne
  push_neg at hne
  have hlt : ∀ j ∈ s.erase i₀, v (t j) < v (t i₀) := by
    intro j hj
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
    by_cases htj : t j = 0
    · rw [htj, map_zero]; exact (Valuation.pos_iff v).mpr ht₀
    · exact lt_of_le_of_ne (hmax j hjs) fun h => hne j hjs i₀ hi₀ hji htj ht₀ h
  have h1 : v (∑ j ∈ s.erase i₀, t j) < v (t i₀) :=
    v.map_sum_lt ((Valuation.ne_zero_iff v).mpr ht₀) hlt
  have h2 : v (t i₀ + ∑ j ∈ s.erase i₀, t j) = v (t i₀) := v.map_add_eq_of_lt_left h1
  rw [Finset.add_sum_erase s t hi₀, hsum, map_zero] at h2
  exact ht₀ ((Valuation.zero_iff v).mp h2.symm)

variable (A : ValuationSubring K) {q : ℕ} [hq : Fact q.Prime]

local notation "w" => ValuationSubring.valuation A

theorem valuation_natCast_eq_one_of_not_dvd (hqA : (q : K) ∈ A.nonunits) {n : ℕ} (hn : ¬ q ∣ n) :
    w (n : K) = 1 := by
  have hcop : IsCoprime (q : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr
    ((Nat.Prime.coprime_iff_not_dvd hq.out).mpr hn)
  obtain ⟨a, b, hab⟩ := hcop
  have habK : (a : K) * q + (b : K) * n = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : K)) hab
  have hq1 : w (q : K) < 1 := (A.mem_nonunits_iff).mp hqA
  have ha : w (a : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A a)
  have hb : w (b : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A b)
  have hn1 : w (n : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A n)
  have haq : w ((a : K) * q) < 1 := by
    rw [map_mul]
    calc w (a : K) * w (q : K) ≤ 1 * w (q : K) := mul_le_mul_left ha _
      _ < 1 := by rw [one_mul]; exact hq1

  by_contra hne
  have hnlt : w (n : K) < 1 := lt_of_le_of_ne hn1 hne
  have hbn : w ((b : K) * n) < 1 := by
    rw [map_mul]
    calc w (b : K) * w (n : K) ≤ 1 * w (n : K) := mul_le_mul_left hb _
      _ < 1 := by rw [one_mul]; exact hnlt
  have := Valuation.map_add_lt (w) haq hbn
  rw [habK, map_one] at this
  exact lt_irrefl _ this

theorem exists_valuation_natCast_eq (hqA : (q : K) ∈ A.nonunits) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, w (n : K) = w (q : K) ^ e := by
  obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.out.one_lt.ne'
  refine ⟨e, ?_⟩
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, valuation_natCast_eq_one_of_not_dvd A hqA hn',
    mul_one]

theorem exists_valuation_ratCast_eq (hqA : (q : K) ∈ A.nonunits) [CharZero K] {r : ℚ} (hr : r ≠ 0) :
    ∃ a b : ℕ, w (r : K) * w (q : K) ^ a = w (q : K) ^ b := by
  have hnum : r.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hr)
  obtain ⟨b, hb⟩ := exists_valuation_natCast_eq A hqA hnum
  obtain ⟨a, ha⟩ := exists_valuation_natCast_eq A hqA r.den_nz
  refine ⟨a, b, ?_⟩
  have hden : (r.den : K) ≠ 0 := by exact_mod_cast r.den_nz
  have hnumK : w (r.num : K) = w (r.num.natAbs : K) := by
    rcases Int.natAbs_eq r.num with h | h
    · have this : w (r.num : K) = w ((r.num.natAbs : ℤ) : K) := congrArg (fun z : ℤ => w (z : K)) h
      rwa [Int.cast_natCast] at this
    · have this : w (r.num : K) = w ((-(r.num.natAbs : ℤ) : ℤ) : K) :=
        congrArg (fun z : ℤ => w (z : K)) h
      rwa [Int.cast_neg, Int.cast_natCast, Valuation.map_neg] at this
  rw [Rat.cast_def, map_div₀, ← ha, hnumK, hb, div_mul_cancel₀]
  exact (Valuation.ne_zero_iff _).mpr hden

theorem exists_pow_valuation_eq [CharZero K] [Algebra ℚ K] (hqA : (q : K) ∈ A.nonunits) {x : K}
    (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ ∃ a b : ℕ, w x ^ k * w (q : K) ^ a = w (q : K) ^ b := by
  obtain ⟨p, hp0, hpx⟩ := hx

  set t : ℕ → K := fun i => (p.coeff i : K) * x ^ i with ht
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1), t i = 0 := by
    rw [← hpx, aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht, Algebra.smul_def, eq_ratCast]
  have hlead : t p.natDegree ≠ 0 := by
    rw [ht]
    exact mul_ne_zero (by exact_mod_cast (leadingCoeff_ne_zero.mpr hp0)) (pow_ne_zero _ hx0)
  obtain ⟨i, hi, j, hj, hij, hti, htj, hv⟩ := exists_ne_val_eq_of_sum_eq_zero (w)
    (Finset.range (p.natDegree + 1)) t hsum (Finset.self_mem_range_succ _) hlead

  have hci : p.coeff i ≠ 0 := by
    intro h; apply hti; rw [ht]; simp only [h, Rat.cast_zero, zero_mul]
  have hcj : p.coeff j ≠ 0 := by
    intro h; apply htj; rw [ht]; simp only [h, Rat.cast_zero, zero_mul]

  wlog hlt : i < j generalizing i j
  · exact this j hj i hi hij.symm htj hti hv.symm hcj hci (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  obtain ⟨ai, bi, hei⟩ := exists_valuation_ratCast_eq A hqA hci
  obtain ⟨aj, bj, hej⟩ := exists_valuation_ratCast_eq A hqA hcj
  refine ⟨j - i, Nat.sub_pos_of_lt hlt, bj + ai, bi + aj, ?_⟩

  have hx' : w x ^ i ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hx0)
  have hkey : w x ^ (j - i) * w (p.coeff j : K) = w (p.coeff i : K) := by
    have h := hv
    rw [ht] at h
    simp only [map_mul, map_pow] at h

    rw [← pow_sub_mul_pow (w x) hlt.le] at h
    have h' : w (p.coeff i : K) * w x ^ i = (w x ^ (j - i) * w (p.coeff j : K)) * w x ^ i := by
      rw [h]; ac_rfl
    exact (mul_right_cancel₀ hx' h').symm
  rw [pow_add, pow_add, ← hej, ← hei, ← hkey]
  ac_rfl

theorem exists_pow_eq_mul_of_mem_maximalIdeal [CharZero K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (hqA : (q : K) ∈ A.nonunits) (c : A) (hc0 : c ≠ 0) (c' : A)
    (hc' : c' ∈ IsLocalRing.maximalIdeal A) (hc'0 : c' ≠ 0) :
    ∃ M : ℕ, ∃ a : A, (c' : K) ^ M = c * a := by
  have hcK : (c : K) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hc'K : (c' : K) ≠ 0 := fun h => hc'0 (Subtype.ext h)
  have hq1 : w (q : K) ≤ 1 := le_of_lt ((A.mem_nonunits_iff).mp hqA)
  obtain ⟨k, hk, a, b, he⟩ := exists_pow_valuation_eq A hqA (Algebra.IsAlgebraic.isAlgebraic _) hcK
  obtain ⟨k', hk', a', b', he'⟩ := exists_pow_valuation_eq A hqA (Algebra.IsAlgebraic.isAlgebraic _) hc'K
  have hvc : w (c : K) ≤ 1 := A.valuation_le_one c
  have hvc' : w (c' : K) < 1 := (A.valuation_lt_one_iff c').mp hc'
  have hqpos : ∀ n : ℕ, 0 < w (q : K) ^ n := fun n =>
    pow_pos ((Valuation.pos_iff _).mpr (by exact_mod_cast hq.out.ne_zero)) n

  have hcb : w (q : K) ^ b ≤ w (c : K) := by
    calc w (q : K) ^ b = w (c : K) ^ k * w (q : K) ^ a := he.symm
      _ ≤ w (c : K) ^ k * 1 := mul_le_mul_right (pow_le_one' hq1 a) _
      _ = w (c : K) ^ k := mul_one _
      _ ≤ w (c : K) := pow_le_of_le_one zero_le' hvc hk.ne'

  have hlt' : a' < b' := by
    by_contra hge
    push_neg at hge
    have h1 : w (c' : K) ^ k' < 1 := pow_lt_one' hvc' hk'.ne'
    have : w (q : K) ^ b' < w (q : K) ^ a' := by
      calc w (q : K) ^ b' = w (c' : K) ^ k' * w (q : K) ^ a' := he'.symm
        _ < 1 * w (q : K) ^ a' := mul_lt_mul_of_pos_right h1 (hqpos a')
        _ = w (q : K) ^ a' := one_mul _
    exact absurd (pow_le_pow_right_of_le_one' hq1 hge) (not_le.mpr this)
  have hc'q : w (c' : K) ^ k' ≤ w (q : K) := by
    have h : w (c' : K) ^ k' * w (q : K) ^ a' = (w (q : K) ^ (b' - a' - 1) * w (q : K)) * w (q : K) ^ a' := by
      rw [he', ← pow_succ, ← pow_add]; congr 1; omega
    have h2 := mul_right_cancel₀ (hqpos a').ne' h
    rw [h2]
    calc w (q : K) ^ (b' - a' - 1) * w (q : K) ≤ 1 * w (q : K) :=
          mul_le_mul_left (pow_le_one' hq1 _) _
      _ = w (q : K) := one_mul _

  refine ⟨k' * b, ⟨(c' : K) ^ (k' * b) * (c : K)⁻¹, ?_⟩, ?_⟩
  · rw [← A.valuation_le_one_iff, map_mul, map_inv₀, map_pow, pow_mul]
    calc (w (c' : K) ^ k') ^ b * (w (c : K))⁻¹ ≤ w (q : K) ^ b * (w (c : K))⁻¹ :=
          mul_le_mul_left (pow_le_pow_left' hc'q b) _
      _ ≤ w (c : K) * (w (c : K))⁻¹ := mul_le_mul_left hcb _
      _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr hcK)
  · show (c' : K) ^ (k' * b) = c * ((c' : K) ^ (k' * b) * (c : K)⁻¹)
    rw [mul_comm (c : K), mul_assoc, inv_mul_cancel₀ hcK, mul_one]

theorem map_eq_zero_of_mem_maximalIdeal [CharZero K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (hqA : (q : K) ∈ A.nonunits) {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  by_cases ha0 : a = 0
  · rw [ha0, map_zero]
  have hqmem : (q : K) ∈ A := natCast_mem A q
  have hq0 : (⟨(q : K), hqmem⟩ : A) ≠ 0 := by
    intro h
    have := congrArg (fun z : A => (z : K)) h
    simp only [ZeroMemClass.coe_zero, Nat.cast_eq_zero] at this
    exact hq.out.ne_zero this
  obtain ⟨M, b, hMb⟩ := exists_pow_eq_mul_of_mem_maximalIdeal A hqA ⟨(q : K), hqmem⟩ hq0 a ha ha0
  have hA : a ^ M = ⟨(q : K), hqmem⟩ * b := Subtype.ext (by simpa using hMb)
  have hred : red a ^ M = 0 := by
    rw [← map_pow, hA, map_mul, show red ⟨(q : K), hqmem⟩ = (q : k) from ?_, CharP.cast_eq_zero,
      zero_mul]
    rw [← map_natCast red q]
    congr 1
  by_cases hM : M = 0
  · rw [hM, pow_zero] at hred; exact absurd hred one_ne_zero
  · exact pow_eq_zero_iff hM |>.mp hred

theorem exists_pow_eq_mul_of_mem_maximalIdeal_algebraicClosure
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hqA : (q : AlgebraicClosure ℚ) ∈ A.nonunits)
    (c : A) (hc0 : c ≠ 0) (c' : A) (hc' : c' ∈ IsLocalRing.maximalIdeal A) (hc'0 : c' ≠ 0) :
    ∃ M : ℕ, ∃ a : A, (c' : AlgebraicClosure ℚ) ^ M = c * a :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  exists_pow_eq_mul_of_mem_maximalIdeal A hqA c hc0 c' hc' hc'0

theorem map_eq_zero_of_mem_maximalIdeal_algebraicClosure
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hqA : (q : AlgebraicClosure ℚ) ∈ A.nonunits)
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  map_eq_zero_of_mem_maximalIdeal A hqA red a ha

end Archimedean
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Fricke

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem mem_nonunits_comap_iff' {K K' : Type*} [Field K] [Field K'] (O : ValuationSubring K')
    (f : K →+* K') (x : K) : x ∈ (O.comap f).nonunits ↔ f x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem frickeInvolutionBar_jF : frickeInvolutionBar N (jF N) = jNF A N := by
  have hFr : IsFrickeAutFull N (frickeInvolutionFull N) :=
    isFrickeAutFull_frickeInvolutionFull N (exists_isFrickeAutFull_of_neZero N)
  have h := frickeInvolutionBar_coeffEmb_qExpand N hFr 1 N (one_mul N)
  have h1 : (jF N : FF) = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full N (Dvd.intro N (one_mul N)))⟩ :=
    Subtype.ext (by
      show coeffEmb (AlgebraicClosure ℚ) jq = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq)
      rw [qExpand_one_apply])
  rw [h1, h]
  exact Subtype.ext (by rw [coe_jNF]; exact coeffEmb_qExpand_jq _ N)

variable {N} in

theorem charP_residueField_of_liesOverPrime (hp : N.Prime) (hA : A.LiesOverPrime N) :
    CharP kk N := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hA
  have h0 : (N : kk) = 0 := by
    have hNA : (⟨(N : AlgebraicClosure ℚ), hmem⟩ : A) = (N : A) :=
      Subtype.ext (map_natCast A.subtype N).symm
    rw [← map_natCast (IsLocalRing.residue A) N, ← hNA, IsLocalRing.residue_eq_zero_iff]
    exact hmax
  exact (CharP.charP_iff_prime_eq_zero hp).mpr h0

def dG : gaussRing A N :=
  (⟨jNF A N, jNF_mem_gaussRing A N⟩ : gaussRing A N) - ⟨jF N, jF_mem_gaussRing A N⟩ ^ N

def τG : gaussRing A N :=
  (⟨jF N, jF_mem_gaussRing A N⟩ : gaussRing A N) - ⟨jNF A N, jNF_mem_gaussRing A N⟩ ^ N

theorem coe_dG : ((dG A N : gaussRing A N) : FF) = jNF A N - jF N ^ N := by simp [dG]

theorem coe_τG : ((τG A N : gaussRing A N) : FF) = jF N - jNF A N ^ N := by simp [τG]

theorem resHom_dG [Fact N.Prime] [CharP kk N] : resHom A N (dG A N) = 0 := by
  rw [dG, map_sub, map_pow, resHom_jNF, resHom_jF,
    show qExpand kk N (jqModC kk) = jqNModC kk N from rfl,
    frobenius_identity_geom_unconditional kk, sub_self]

theorem resHom_τG_ne_zero [Fact N.Prime] [CharP kk N] (hp : N.Prime) : resHom A N (τG A N) ≠ 0 := by
  rw [τG, map_sub, map_pow, resHom_jNF, resHom_jF,
    show qExpand kk N (jqModC kk) = jqNModC kk N from rfl,
    frobenius_identity_geom_unconditional kk, ← pow_mul, sub_ne_zero]
  intro h
  have ho := congrArg HahnSeries.order h
  have h1 : (jqModC kk).order = -1 := by
    have := order_jqModC_pow kk 1
    rwa [pow_one, Nat.cast_one] at this
  rw [h1, order_jqModC_pow] at ho
  have h2 : (2 : ℤ) ≤ N := by exact_mod_cast hp.two_le
  push_cast at ho
  nlinarith

theorem frickeInvolutionBar_coe_τG :
    frickeInvolutionBar N ((τG A N : gaussRing A N) : FF) = ((dG A N : gaussRing A N) : FF) := by
  have hσj := frickeInvolutionBar_jF A N
  have hσjN : frickeInvolutionBar N (jNF A N) = jF N := by
    rw [← hσj]; exact frickeInvolutionBar_frickeInvolutionBar N _
  rw [coe_τG, coe_dG, map_sub, map_pow, hσj, hσjN]

theorem frickeInvolutionBar_coe_dG :
    frickeInvolutionBar N ((dG A N : gaussRing A N) : FF) = ((τG A N : gaussRing A N) : FF) := by
  rw [← frickeInvolutionBar_coe_τG A N, frickeInvolutionBar_frickeInvolutionBar]

theorem coe_τG_mem_nonunits_gaussComap [Fact N.Prime] [CharP kk N] :
    ((τG A N : gaussRing A N) : FF) ∈ (gaussComap A N (frickeInvolutionBar N)).nonunits := by
  rw [show gaussComap A N (frickeInvolutionBar N)
      = (gaussRing A N).comap ((frickeInvolutionBar N : FF ≃ₐ[AlgebraicClosure ℚ] FF) : FF →+* FF)
      from rfl, mem_nonunits_comap_iff']
  show frickeInvolutionBar N ((τG A N : gaussRing A N) : FF) ∈ (gaussRing A N).nonunits
  rw [frickeInvolutionBar_coe_τG]
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨(dG A N).2, by simpa using (resHom_eq_zero_iff A N (dG A N)).mp (resHom_dG A N)⟩

theorem coe_τG_not_mem_nonunits [Fact N.Prime] [CharP kk N] (hp : N.Prime) :
    ((τG A N : gaussRing A N) : FF) ∉ (gaussRing A N).nonunits := fun h => by
  obtain ⟨hm, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
  have hmax' : τG A N ∈ IsLocalRing.maximalIdeal (gaussRing A N) := by simpa using hmax
  exact (IsLocalRing.mem_maximalIdeal _).mp hmax'
    (isUnit_of_resHom_ne_zero A N (resHom_τG_ne_zero A N hp))

theorem gaussComap_frickeInvolutionBar_ne (hp : N.Prime) (hA : A.LiesOverPrime N) :
    gaussComap A N (frickeInvolutionBar N) ≠ gaussRing A N := by
  haveI : Fact N.Prime := ⟨hp⟩
  haveI : CharP kk N := charP_residueField_of_liesOverPrime A hp hA
  intro heq
  have h := coe_τG_mem_nonunits_gaussComap A N
  rw [heq] at h
  exact coe_τG_not_mem_nonunits A N hp h

end Fricke
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Dict

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

open ModularCurve.CharPReduction

theorem coeffRed_eq_ϖ (x : integralCoeffs A.toSubring) (y : LaurentSeries A)
    (hxy : (x : LaurentSeries L) = ι A y) :
    coeffRed A.toSubring (IsLocalRing.residue A) x = ϖ A y := by
  ext n
  rw [coeffRed_coeff]
  have hc : (x : LaurentSeries L).coeff n = ((y.coeff n : A) : L) := by
    rw [hxy]; exact coeffMap_coeff _ _ _
  have hsub : (⟨(x : LaurentSeries L).coeff n, x.2 n⟩ : A.toSubring) = y.coeff n := Subtype.ext hc
  rw [hsub]
  exact (coeffMap_coeff _ _ _).symm

theorem isInt_of_mem_modularLocalized {f : LaurentSeries L}
    (hf : f ∈ modularLocalized N A.toSubring (IsLocalRing.residue A)) : IsInt A f := by
  obtain ⟨r, s, hs, hfs⟩ := (mem_localizedAtKer _ _ _ _).mp hf
  obtain ⟨r₀, hr₀⟩ := exists_coeffMap_subtype_eq A (r : LaurentSeries L)
    (fun n => modularRing_le_integralCoeffs N A.toSubring r.2 n)
  obtain ⟨s₀, hs₀⟩ := exists_coeffMap_subtype_eq A (s : LaurentSeries L)
    (fun n => modularRing_le_integralCoeffs N A.toSubring s.2 n)
  refine ⟨r₀, s₀, fun h0 => (notMem_redKer_iff _ _ _ _).mp hs ?_, ?_⟩
  · rw [redRes_apply, coeffRed_eq_ϖ A _ s₀ hs₀.symm, h0]
  · show f * ι A s₀ = ι A r₀
    rw [show ι A s₀ = s from hs₀, show ι A r₀ = r from hr₀]
    exact hfs

theorem mem_gaussRing_of_mem_modularLocalized {f : LaurentSeries L}
    (hf : f ∈ modularLocalized N A.toSubring (IsLocalRing.residue A)) (hF : f ∈ FF) :
    (⟨f, hF⟩ : FF) ∈ gaussRing A N :=
  isInt_of_mem_modularLocalized A N hf

theorem resHom_eq_modularRedLocHom {f : LaurentSeries L}
    (hO : f ∈ modularLocalized N A.toSubring (IsLocalRing.residue A)) (hF : f ∈ FF)
    (hG : (⟨f, hF⟩ : FF) ∈ gaussRing A N) :
    resHom A N ⟨⟨f, hF⟩, hG⟩
      = modularRedLocHom N A.toSubring (IsLocalRing.residue A) ⟨f, hO⟩ := by
  obtain ⟨r, s, hs, hfs⟩ := (mem_localizedAtKer _ _ _ _).mp hO
  obtain ⟨r₀, hr₀⟩ := exists_coeffMap_subtype_eq A (r : LaurentSeries L)
    (fun n => modularRing_le_integralCoeffs N A.toSubring r.2 n)
  obtain ⟨s₀, hs₀⟩ := exists_coeffMap_subtype_eq A (s : LaurentSeries L)
    (fun n => modularRing_le_integralCoeffs N A.toSubring s.2 n)
  have hϖs : ϖ A s₀ ≠ 0 := fun h0 => (notMem_redKer_iff _ _ _ _).mp hs
    (by rw [redRes_apply, coeffRed_eq_ϖ A _ s₀ hs₀.symm, h0])
  have hwit : (((⟨⟨f, hF⟩, hG⟩ : gaussRing A N) : FF) : LaurentSeries L) * ι A s₀ = ι A r₀ := by
    show f * ι A s₀ = ι A r₀
    rw [show ι A s₀ = s from hs₀, show ι A r₀ = r from hr₀]
    exact hfs
  rw [resHom_eq A N hϖs hwit]
  have hspec := redLoc_spec (A := A.toSubring) (red := IsLocalRing.residue A)
    (R := modularRing N A.toSubring) (hR := modularRing_le_integralCoeffs N A.toSubring)
    ⟨f, hO⟩ (r := r) (s := s) hfs
  rw [redRes_apply, redRes_apply, coeffRed_eq_ϖ A _ s₀ hs₀.symm,
    coeffRed_eq_ϖ A _ r₀ hr₀.symm] at hspec
  rw [show modularRedLocHom N A.toSubring (IsLocalRing.residue A) ⟨f, hO⟩ = redLoc ⟨f, hO⟩ from rfl,
    div_eq_iff hϖs]
  exact hspec.symm

theorem modularLocalized_le_laurentBaseChange {f : LaurentSeries L}
    (hf : f ∈ modularLocalized N A.toSubring (IsLocalRing.residue A)) : f ∈ FF := by
  have hR : ∀ g : LaurentSeries L, g ∈ modularRing N A.toSubring → g ∈ FF := by
    intro g hg
    refine Subring.closure_induction (fun x hx => ?_) (zero_mem _) (one_mem _)
      (fun _ _ _ _ hx hy => add_mem hx hy) (fun _ _ hx => neg_mem hx)
      (fun _ _ _ _ hx hy => mul_mem hx hy) hg
    rcases hx with ⟨a, rfl⟩ | rfl | rfl
    · exact (laurentBaseChange L (modularFunctionFieldFull N)).algebraMap_mem (a : L)
    · rw [← coe_jF (L := L) N]; exact (jF N).2
    · rw [show jqNModC L N = ((jNF A N : FF) : LaurentSeries L) from (coe_jNF A N).symm]
      exact (jNF A N).2
  obtain ⟨r, s, hs, hfs⟩ := (mem_localizedAtKer _ _ _ _).mp hf
  have hs0 : (s : LaurentSeries L) ≠ 0 := by
    intro h0
    apply (notMem_redKer_iff _ _ _ _).mp hs
    rw [redRes_apply]
    have : (⟨(s : LaurentSeries L), modularRing_le_integralCoeffs N A.toSubring s.2⟩ :
        integralCoeffs A.toSubring) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hf' : f = (r : LaurentSeries L) * (s : LaurentSeries L)⁻¹ := by
    rw [← hfs, mul_inv_cancel_right₀ hs0]
  rw [hf']
  exact mul_mem (hR _ r.2) (inv_mem (hR _ s.2))

end Dict
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section DictGeneric

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]
variable {k : Type*} [Field k] (red : A →+* k)
  (redBar : IsLocalRing.ResidueField A →+* k)
  (hred : ∀ a : A, redBar (IsLocalRing.residue A a) = red a)

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

open ModularCurve.CharPReduction

include hred in

theorem coeffRed_eq_coeffMap_ϖ (x : integralCoeffs A.toSubring) (y : LaurentSeries A)
    (hxy : (x : LaurentSeries L) = ι A y) :
    coeffRed A.toSubring red x = coeffMap redBar (ϖ A y) := by
  ext n
  rw [coeffRed_coeff, coeffMap_coeff]
  have hc : (x : LaurentSeries L).coeff n = ((y.coeff n : A) : L) := by
    rw [hxy]; exact coeffMap_coeff _ _ _
  have hsub : (⟨(x : LaurentSeries L).coeff n, x.2 n⟩ : A.toSubring) = y.coeff n := Subtype.ext hc
  rw [hsub, show (ϖ A y).coeff n = IsLocalRing.residue A (y.coeff n) from coeffMap_coeff _ _ _, hred]

theorem modularLocalized_le_laurentBaseChange' {f : LaurentSeries L}
    (hf : f ∈ modularLocalized N A.toSubring red) : f ∈ FF := by
  have hR : ∀ g : LaurentSeries L, g ∈ modularRing N A.toSubring → g ∈ FF := by
    intro g hg
    refine Subring.closure_induction (fun x hx => ?_) (zero_mem _) (one_mem _)
      (fun _ _ _ _ hx hy => add_mem hx hy) (fun _ _ hx => neg_mem hx)
      (fun _ _ _ _ hx hy => mul_mem hx hy) hg
    rcases hx with ⟨a, rfl⟩ | rfl | rfl
    · exact (laurentBaseChange L (modularFunctionFieldFull N)).algebraMap_mem (a : L)
    · rw [← coe_jF (L := L) N]; exact (jF N).2
    · rw [show jqNModC L N = ((jNF A N : FF) : LaurentSeries L) from (coe_jNF A N).symm]
      exact (jNF A N).2
  obtain ⟨r, s, hs, hfs⟩ := (mem_localizedAtKer _ _ _ _).mp hf
  have hs0 : (s : LaurentSeries L) ≠ 0 := by
    intro h0
    apply (notMem_redKer_iff _ _ _ _).mp hs
    rw [redRes_apply]
    have : (⟨(s : LaurentSeries L), modularRing_le_integralCoeffs N A.toSubring s.2⟩ :
        integralCoeffs A.toSubring) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hf' : f = (r : LaurentSeries L) * (s : LaurentSeries L)⁻¹ := by
    rw [← hfs, mul_inv_cancel_right₀ hs0]
  rw [hf']
  exact mul_mem (hR _ r.2) (inv_mem (hR _ s.2))

include hred in

theorem isInt_of_mem_modularLocalized' {f : LaurentSeries L}
    (hf : f ∈ modularLocalized N A.toSubring red) : IsInt A f := by
  obtain ⟨r, s, hs, hfs⟩ := (mem_localizedAtKer _ _ _ _).mp hf
  obtain ⟨r₀, hr₀⟩ := exists_coeffMap_subtype_eq A (r : LaurentSeries L)
    (fun n => modularRing_le_integralCoeffs N A.toSubring r.2 n)
  obtain ⟨s₀, hs₀⟩ := exists_coeffMap_subtype_eq A (s : LaurentSeries L)
    (fun n => modularRing_le_integralCoeffs N A.toSubring s.2 n)
  refine ⟨r₀, s₀, fun h0 => (notMem_redKer_iff _ _ _ _).mp hs ?_, ?_⟩
  · rw [redRes_apply, coeffRed_eq_coeffMap_ϖ A red redBar hred _ s₀ hs₀.symm, h0, map_zero]
  · show f * ι A s₀ = ι A r₀
    rw [show ι A s₀ = s from hs₀, show ι A r₀ = r from hr₀]
    exact hfs

include hred in

theorem mem_gaussRing_of_mem_modularLocalized' {f : LaurentSeries L}
    (hf : f ∈ modularLocalized N A.toSubring red) (hF : f ∈ FF) :
    (⟨f, hF⟩ : FF) ∈ gaussRing A N :=
  isInt_of_mem_modularLocalized' A N red redBar hred hf

include hred in

theorem coeffMap_resHom_eq_modularRedLocHom {f : LaurentSeries L}
    (hO : f ∈ modularLocalized N A.toSubring red) (hF : f ∈ FF)
    (hG : (⟨f, hF⟩ : FF) ∈ gaussRing A N) :
    coeffMap redBar (resHom A N ⟨⟨f, hF⟩, hG⟩)
      = modularRedLocHom N A.toSubring red ⟨f, hO⟩ := by
  obtain ⟨r, s, hs, hfs⟩ := (mem_localizedAtKer _ _ _ _).mp hO
  obtain ⟨r₀, hr₀⟩ := exists_coeffMap_subtype_eq A (r : LaurentSeries L)
    (fun n => modularRing_le_integralCoeffs N A.toSubring r.2 n)
  obtain ⟨s₀, hs₀⟩ := exists_coeffMap_subtype_eq A (s : LaurentSeries L)
    (fun n => modularRing_le_integralCoeffs N A.toSubring s.2 n)
  have hreds : redRes A.toSubring red (modularRing N A.toSubring)
      (modularRing_le_integralCoeffs N A.toSubring) s = coeffMap redBar (ϖ A s₀) := by
    rw [redRes_apply, coeffRed_eq_coeffMap_ϖ A red redBar hred _ s₀ hs₀.symm]
  have hredr : redRes A.toSubring red (modularRing N A.toSubring)
      (modularRing_le_integralCoeffs N A.toSubring) r = coeffMap redBar (ϖ A r₀) := by
    rw [redRes_apply, coeffRed_eq_coeffMap_ϖ A red redBar hred _ r₀ hr₀.symm]
  have hbs : coeffMap redBar (ϖ A s₀) ≠ 0 := by
    rw [← hreds]; exact (notMem_redKer_iff _ _ _ _).mp hs
  have hϖs : ϖ A s₀ ≠ 0 := fun h0 => hbs (by rw [h0, map_zero])
  have hwit : (((⟨⟨f, hF⟩, hG⟩ : gaussRing A N) : FF) : LaurentSeries L) * ι A s₀ = ι A r₀ := by
    show f * ι A s₀ = ι A r₀
    rw [show ι A s₀ = s from hs₀, show ι A r₀ = r from hr₀]
    exact hfs
  rw [resHom_eq A N hϖs hwit, map_div₀]
  have hspec := redLoc_spec (A := A.toSubring) (red := red)
    (R := modularRing N A.toSubring) (hR := modularRing_le_integralCoeffs N A.toSubring)
    ⟨f, hO⟩ (r := r) (s := s) hfs
  rw [hreds, hredr] at hspec
  rw [show modularRedLocHom N A.toSubring red ⟨f, hO⟩ = redLoc ⟨f, hO⟩ from rfl, div_eq_iff hbs]
  exact hspec.symm

end DictGeneric
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Key

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] [Fact N.Prime] [CharP K N]

theorem jqModC_pow_sq_ne : jqModC K ^ (N * N) ≠ jqModC K := by
  intro h
  have ho := congrArg HahnSeries.order h
  have h1 : (jqModC K).order = -1 := by
    have := order_jqModC_pow K 1
    rwa [pow_one, Nat.cast_one] at this
  rw [h1, order_jqModC_pow] at ho
  have h2 : (2 : ℤ) ≤ N := by exact_mod_cast (Fact.out : N.Prime).two_le
  push_cast at ho
  nlinarith

theorem eq_zero_of_sum_pow_and_sum_qExpand (ρ : ℕ → LaurentSeries K)
    (h1 : ∑ i ∈ Finset.range (N + 1), ρ i * (jqModC K ^ N) ^ i = 0)
    (h2 : ∑ i ∈ Finset.range (N + 1), qExpand K N (ρ i) * jqModC K ^ i = 0) :
    ∀ i ≤ N, ρ i = 0 := by
  have hfrob : qExpand K N (jqModC K) = jqModC K ^ N :=
    ModularCurve.frobenius_identity_geom_unconditional K
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)

  set S := ∑ i ∈ Finset.Ico 1 N, qExpand K N (ρ i) * jqModC K ^ i with hS
  have h2a : qExpand K N (ρ 0) + S + qExpand K N (ρ N) * jqModC K ^ N = 0 := by
    rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN0, pow_zero,
      mul_one, ← hS] at h2
    exact h2

  let c' : ℕ → LaurentSeries K := fun i =>
    if i = 0 then qExpand K N (ρ 0 + ρ N * jqModC K) else qExpand K N (ρ i)
  have h2' : ∑ i ∈ Finset.range N, c' i * jqModC K ^ i = 0 := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN0, pow_zero, mul_one]
    have hS' : ∑ i ∈ Finset.Ico 1 N, c' i * jqModC K ^ i = S := by
      rw [hS]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [c', if_neg (Nat.one_le_iff_ne_zero.mp (Finset.mem_Ico.mp hi).1)]
    rw [hS', show c' 0 = qExpand K N (ρ 0 + ρ N * jqModC K) from rfl, map_add, map_mul, hfrob,
      ← h2a]
    ring

  have hc := eq_zero_of_sum_mul_pow_jqModC_eq_zero K N (fun i : Fin N => c' i)
    (fun i => by
      show c' i ∈ Set.range (qExpand K N)
      simp only [c']
      split_ifs
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩)
    (by rw [Fin.sum_univ_eq_sum_range (fun i => c' i * jqModC K ^ i) N]; exact h2')
  have hmid : ∀ i, 0 < i → i < N → ρ i = 0 := by
    intro i hi0 hiN
    have h := hc ⟨i, hiN⟩
    simp only [c', if_neg (Nat.pos_iff_ne_zero.mp hi0)] at h
    exact qExpand_injective (R := K) (N := N) (by rw [h, map_zero])
  have h0 : ρ 0 + ρ N * jqModC K = 0 := by
    have h : qExpand K N (ρ 0 + ρ N * jqModC K) = 0 := by simpa [c'] using hc ⟨0, hN0⟩
    exact qExpand_injective (R := K) (N := N) (by rw [h, map_zero])

  have h1' : ρ 0 + ρ N * jqModC K ^ (N * N) = 0 := by
    rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN0, pow_zero,
      mul_one, ← pow_mul, Finset.sum_eq_zero (fun i hi => ?_), add_zero] at h1
    · exact h1
    · rw [hmid i (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp (Finset.mem_Ico.mp hi).1))
        (Finset.mem_Ico.mp hi).2, zero_mul]
  have hρN : ρ N = 0 := by
    have hsub : ρ N * (jqModC K ^ (N * N) - jqModC K) = 0 := by linear_combination h1' - h0
    rcases mul_eq_zero.mp hsub with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) (jqModC_pow_sq_ne K N)
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [hρN, zero_mul, add_zero] at h0; exact h0
  · rcases Nat.lt_or_ge i N with hiN | hiN
    · exact hmid i hi0 hiN
    · rw [le_antisymm hi hiN]; exact hρN

end Key
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section RegTwo

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]
  [Fact N.Prime]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem mem_nonunits_gaussRing_iff {x : FF} (hx : x ∈ gaussRing A N) :
    x ∈ (gaussRing A N).nonunits ↔ resHom A N ⟨x, hx⟩ = 0 := by
  rw [resHom_eq_zero_iff, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩

theorem forall_mem_nonunits_of_sum_mem_nonunits [CharP kk N]
    (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N) (hσjN : σ (jNF A N) = jF N) (κ : ℕ → FF)
    (hκK : ∀ i, κ i ∈ IntermediateField.adjoin L ({(jF N : FF)} : Set FF))
    (hκO : ∀ i, κ i ∈ gaussRing A N)
    (h1 : (∑ i ∈ Finset.range (N + 1), κ i * jNF A N ^ i) ∈ (gaussRing A N).nonunits)
    (h2 : σ (∑ i ∈ Finset.range (N + 1), κ i * jNF A N ^ i) ∈ (gaussRing A N).nonunits) :
    ∀ i ≤ N, κ i ∈ (gaussRing A N).nonunits := by
  have hfrob : qExpand kk N (jqModC kk) = jqModC kk ^ N :=
    ModularCurve.frobenius_identity_geom_unconditional kk

  have hσκ : ∀ i, κ i ∈ gaussComap A N σ := fun i =>
    mem_gaussComap_of_mem_adjoin A N σ hσj (hκK i) (hκO i)
  set ρ : ℕ → LaurentSeries kk := fun i => resHom A N ⟨κ i, hκO i⟩ with hρ

  set X : gaussRing A N := ∑ i ∈ Finset.range (N + 1),
    (⟨κ i, hκO i⟩ : gaussRing A N) * ⟨jNF A N, jNF_mem_gaussRing A N⟩ ^ i with hX
  set Y : gaussRing A N := ∑ i ∈ Finset.range (N + 1),
    sigmaRes A N σ ⟨κ i, hσκ i⟩ * ⟨jF N, jF_mem_gaussRing A N⟩ ^ i with hY
  have hXc : (X : FF) = ∑ i ∈ Finset.range (N + 1), κ i * jNF A N ^ i := by
    rw [hX]; push_cast; rfl
  have hYc : (Y : FF) = σ (∑ i ∈ Finset.range (N + 1), κ i * jNF A N ^ i) := by
    rw [hY, map_sum]; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hσjN, coe_sigmaRes]

  have hrX : resHom A N X = 0 := by
    have h := (mem_nonunits_gaussRing_iff A N X.2).mp (by rw [hXc]; exact h1)
    simpa using h
  have hrY : resHom A N Y = 0 := by
    have h := (mem_nonunits_gaussRing_iff A N Y.2).mp (by rw [hYc]; exact h2)
    simpa using h
  have hK1 : ∑ i ∈ Finset.range (N + 1), ρ i * (jqModC kk ^ N) ^ i = 0 := by
    rw [← hfrob, ← resHom_jNF A N, ← hrX, hX, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow]
  have hK2 : ∑ i ∈ Finset.range (N + 1), qExpand kk N (ρ i) * jqModC kk ^ i = 0 := by
    rw [← resHom_jF A N, ← hrY, hY, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, resHom_sigmaRes_of_mem_adjoin A N σ hσj (hκK i) (hκO i)]
  have hkey := eq_zero_of_sum_pow_and_sum_qExpand kk N ρ hK1 hK2
  intro i hi
  exact (mem_nonunits_gaussRing_iff A N (hκO i)).mpr (hkey i hi)

theorem exists_div_mem_gaussRing (g : ℕ → FF) (hne : ∃ i ≤ N, g i ≠ 0) :
    ∃ i₀ ≤ N, g i₀ ≠ 0 ∧ ∀ i ≤ N, g i / g i₀ ∈ gaussRing A N := by
  classical
  have hne' : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (Finset.range (N + 1))
    (fun i => (gaussRing A N).valuation (g i)) hne'
  obtain ⟨j, hj, hj0⟩ := hne
  have hvj : 0 < (gaussRing A N).valuation (g j) := by
    rw [zero_lt_iff, ne_eq, Valuation.zero_iff]; exact hj0
  have hv0 : (gaussRing A N).valuation (g i₀) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hvj (hmax j (Finset.mem_range_succ_iff.mpr hj)))
  refine ⟨i₀, Finset.mem_range_succ_iff.mp hi₀, (Valuation.ne_zero_iff _).mp hv0, fun i hi => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀, div_le_one₀ (zero_lt_iff.mpr hv0)]
  exact hmax i (Finset.mem_range_succ_iff.mpr hi)

theorem linearIndependent_pow_jNF [CharP kk N]
    (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N) (hσjN : σ (jNF A N) = jF N) :
    LinearIndependent (IntermediateField.adjoin L ({(jF N : FF)} : Set FF))
      (fun i : Fin (N + 1) => jNF A N ^ (i : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨i₁, hi₁⟩ := hne

  set G : ℕ → FF := fun n => if h : n < N + 1 then ((g ⟨n, h⟩ :
    IntermediateField.adjoin L ({(jF N : FF)} : Set FF)) : FF) else 0 with hG
  have hGi : ∀ i : Fin (N + 1), G i = (g i : FF) := fun i => by
    simp only [hG, dif_pos i.2]
  have hGK : ∀ n, G n ∈ IntermediateField.adjoin L ({(jF N : FF)} : Set FF) := fun n => by
    simp only [hG]; split_ifs with h
    · exact (g ⟨n, h⟩).2
    · exact zero_mem _
  have hsum : ∑ n ∈ Finset.range (N + 1), G n * jNF A N ^ n = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => G n * jNF A N ^ n) (N + 1), ← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGi, IntermediateField.smul_def, smul_eq_mul]
  have hne' : ∃ i ≤ N, G i ≠ 0 := ⟨i₁, Nat.lt_succ_iff.mp i₁.2, by
    rw [hGi]; exact_mod_cast hi₁⟩
  obtain ⟨i₀, hi₀, hG0, hdiv⟩ := exists_div_mem_gaussRing A N G hne'

  have hκK : ∀ n, G n / G i₀ ∈ IntermediateField.adjoin L ({(jF N : FF)} : Set FF) := fun n =>
    div_mem (hGK n) (hGK i₀)
  have hκO : ∀ n, G n / G i₀ ∈ gaussRing A N := fun n => by
    by_cases hn : n ≤ N
    · exact hdiv n hn
    · have : G n = 0 := by simp only [hG, dif_neg (by omega : ¬ n < N + 1)]
      rw [this, zero_div]; exact zero_mem _
  have hsum' : ∑ n ∈ Finset.range (N + 1), G n / G i₀ * jNF A N ^ n = 0 := by
    have : (∑ n ∈ Finset.range (N + 1), G n / G i₀ * jNF A N ^ n)
        = (G i₀)⁻¹ * ∑ n ∈ Finset.range (N + 1), G n * jNF A N ^ n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [this, hsum, mul_zero]
  have h0non : (0 : FF) ∈ (gaussRing A N).nonunits :=
    (ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inl rfl)
  have hall := forall_mem_nonunits_of_sum_mem_nonunits A N σ hσj hσjN (fun n => G n / G i₀)
    hκK hκO (by rw [hsum']; exact h0non) (by rw [hsum', map_zero]; exact h0non) i₀ hi₀
  replace hall : (1 : FF) ∈ (gaussRing A N).nonunits := by simpa [div_self hG0] using hall
  rw [ValuationSubring.mem_nonunits_iff, map_one] at hall
  exact lt_irrefl _ hall

theorem exists_sum_eq [CharP kk N]
    (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N) (hσjN : σ (jNF A N) = jF N)
    (hN : (N : L) ≠ 0) (hp : N.Prime) (x : FF) :
    ∃ κ : ℕ → FF, (∀ i, κ i ∈ IntermediateField.adjoin L ({(jF N : FF)} : Set FF)) ∧
      x = ∑ i ∈ Finset.range (N + 1), κ i * jNF A N ^ i := by
  classical
  have hli := linearIndependent_pow_jNF A N σ hσj hσjN
  have hcard : Fintype.card (Fin (N + 1))
      = Module.finrank (IntermediateField.adjoin L ({(jF N : FF)} : Set FF)) FF := by
    rw [Fintype.card_fin, finrank_adjoin_jF N hN, dedekindPsi_prime hp]
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(jF N : FF)} : Set FF)) FF :=
    Module.finite_of_finrank_pos (by rw [← hcard, Fintype.card_fin]; exact Nat.succ_pos N)
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hx : x ∈ Submodule.span (IntermediateField.adjoin L ({(jF N : FF)} : Set FF))
      (Set.range fun i : Fin (N + 1) => jNF A N ^ (i : ℕ)) := by rw [hspan]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  refine ⟨fun n => if h : n < N + 1 then ((c ⟨n, h⟩ :
    IntermediateField.adjoin L ({(jF N : FF)} : Set FF)) : FF) else 0, fun n => ?_, ?_⟩
  · dsimp only; split_ifs with h
    · exact (c ⟨n, h⟩).2
    · exact zero_mem _
  · rw [← hc, ← Fin.sum_univ_eq_sum_range (fun n => (if h : n < N + 1 then ((c ⟨n, h⟩ :
      IntermediateField.adjoin L ({(jF N : FF)} : Set FF)) : FF) else 0) * jNF A N ^ n) (N + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dif_pos i.2, IntermediateField.smul_def, smul_eq_mul]

end RegTwo
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section RegLevelOne

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]
variable {k : Type*} [Field k] (red : A →+* k)
  (redBar : IsLocalRing.ResidueField A →+* k)
  (hred : ∀ a : A, redBar (IsLocalRing.residue A a) = red a)

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

open ModularCurve.CharPReduction

omit [NeZero N] in
theorem coeffMap_ne_zero_of_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) {x : LaurentSeries R} (hx : x ≠ 0) : coeffMap f x ≠ 0 := by
  intro h
  apply hx
  ext n
  have hn := congrArg (fun s : LaurentSeries S => s.coeff n) h
  simp only [coeffMap_coeff, HahnSeries.coeff_zero] at hn
  rw [HahnSeries.coeff_zero]
  exact hf (by rw [hn, map_zero])

theorem aeval_map_mem_modularRing (p : A[X]) :
    aeval (jqModC L) (p.map A.subtype) ∈ modularRing N A.toSubring := by
  rw [aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [coeff_map, Algebra.smul_def]
  exact Subring.mul_mem _ (constSeries_mem_modularRing N A.toSubring ⟨_, (p.coeff i).2⟩)
    (Subring.pow_mem _ (jqModC_mem_modularRing N A.toSubring) i)

theorem coe_aeval_jF (p : L[X]) :
    ((aeval (jF N) p : FF) : LaurentSeries L) = aeval (jqModC L) p := by
  rw [← coe_jF (L := L) N]
  exact (aeval_algHom_apply (laurentBaseChange L (modularFunctionFieldFull N)).val (jF N) p).symm

include hred in

theorem coe_mem_modularLocalized_of_mem_adjoin {κ : FF}
    (hK : κ ∈ IntermediateField.adjoin L ({(jF N : FF)} : Set FF)) (hO : κ ∈ gaussRing A N) :
    (κ : LaurentSeries L) ∈ modularLocalized N A.toSubring red := by
  classical
  by_cases hκ0 : κ = 0
  · rw [hκ0]; exact Subring.zero_mem _
  obtain ⟨r, hr, s, hs, hrs⟩ := (IntermediateField.mem_adjoin_iff_div (F := L)).mp hK
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hr hs
  obtain ⟨P, rfl⟩ := hr
  obtain ⟨Q, rfl⟩ := hs
  change κ = aeval (jF N) P / aeval (jF N) Q at hrs
  have hQ0 : Q ≠ 0 := by rintro rfl; apply hκ0; rw [hrs, map_zero, div_zero]
  have hP0 : P ≠ 0 := by rintro rfl; apply hκ0; rw [hrs, map_zero, zero_div]
  obtain ⟨c, hc0, P₀, hP, hP₀⟩ := exists_primitive_poly A hP0
  obtain ⟨c', hc'0, Q₀, hQ, hQ₀⟩ := exists_primitive_poly A hQ0

  set uP : FF := aeval (jF N) (P₀.map A.subtype) with huP
  set uQ : FF := aeval (jF N) (Q₀.map A.subtype) with huQ
  have hcoeP : (uP : LaurentSeries L) = ι A (aeval (jqModC A) P₀) := by
    rw [huP, coe_aeval_jF, ι_aeval]
  have hcoeQ : (uQ : LaurentSeries L) = ι A (aeval (jqModC A) Q₀) := by
    rw [huQ, coe_aeval_jF, ι_aeval]
  have huPm : uP ∈ gaussRing A N := by
    have h := ι_mem_gaussRing A N (y := aeval (jqModC A) P₀) (hcoeP ▸ uP.2)
    convert h using 1; exact Subtype.ext hcoeP
  have huQm : uQ ∈ gaussRing A N := by
    have h := ι_mem_gaussRing A N (y := aeval (jqModC A) Q₀) (hcoeQ ▸ uQ.2)
    convert h using 1; exact Subtype.ext hcoeQ
  have hruP : resHom A N ⟨uP, huPm⟩ = aeval (jqModC kk) (P₀.map (IsLocalRing.residue A)) := by
    rw [← ϖ_aeval]
    have : (⟨uP, huPm⟩ : gaussRing A N) = ⟨⟨ι A (aeval (jqModC A) P₀), hcoeP ▸ uP.2⟩,
        ι_mem_gaussRing A N _⟩ := Subtype.ext (Subtype.ext hcoeP)
    rw [this, resHom_ι]
  have hruQ : resHom A N ⟨uQ, huQm⟩ = aeval (jqModC kk) (Q₀.map (IsLocalRing.residue A)) := by
    rw [← ϖ_aeval]
    have : (⟨uQ, huQm⟩ : gaussRing A N) = ⟨⟨ι A (aeval (jqModC A) Q₀), hcoeQ ▸ uQ.2⟩,
        ι_mem_gaussRing A N _⟩ := Subtype.ext (Subtype.ext hcoeQ)
    rw [this, resHom_ι]
  have huPu : IsUnit (⟨uP, huPm⟩ : gaussRing A N) :=
    isUnit_of_resHom_ne_zero A N (by rw [hruP]; exact aeval_jqModC_ne_zero hP₀)
  have huQu : IsUnit (⟨uQ, huQm⟩ : gaussRing A N) :=
    isUnit_of_resHom_ne_zero A N (by rw [hruQ]; exact aeval_jqModC_ne_zero hQ₀)
  have huP0 : uP ≠ 0 := fun h => huPu.ne_zero (Subtype.ext h)
  have huQ0 : uQ ≠ 0 := fun h => huQu.ne_zero (Subtype.ext h)

  have hκ : κ = algebraMap L FF (c / c') * (uP / uQ) := by
    rw [hrs, hP, hQ, map_mul, map_mul, aeval_C, aeval_C, ← huP, ← huQ, map_div₀, div_mul_div_comm]
  have hunit : uP / uQ ∈ gaussRing A N ∧ (uP / uQ)⁻¹ ∈ gaussRing A N := by
    obtain ⟨vQ, hvQ⟩ := huQu.exists_left_inv
    obtain ⟨vP, hvP⟩ := huPu.exists_left_inv
    have hvQc : ((vQ : gaussRing A N) : FF) = uQ⁻¹ := by
      have := congrArg (fun w : gaussRing A N => (w : FF)) hvQ
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
      exact eq_inv_of_mul_eq_one_left this
    have hvPc : ((vP : gaussRing A N) : FF) = uP⁻¹ := by
      have := congrArg (fun w : gaussRing A N => (w : FF)) hvP
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
      exact eq_inv_of_mul_eq_one_left this
    refine ⟨?_, ?_⟩
    · rw [div_eq_mul_inv, ← hvQc]; exact mul_mem huPm vQ.2
    · rw [inv_div, div_eq_mul_inv, ← hvPc]; exact mul_mem huQm vP.2
  have hcc : c / c' ∈ A := by
    rw [← algebraMap_mem_gaussRing_iff A N]
    have : algebraMap L FF (c / c') = κ * (uP / uQ)⁻¹ := by
      rw [hκ, mul_assoc, mul_inv_cancel₀ (div_ne_zero huP0 huQ0), mul_one]
    rw [this]; exact mul_mem hO hunit.2

  refine (mem_localizedAtKer _ _ _ _).mpr
    ⟨⟨constSeries A.toSubring ⟨c / c', hcc⟩ * aeval (jqModC L) (P₀.map A.subtype),
        Subring.mul_mem _ (constSeries_mem_modularRing N A.toSubring _)
          (aeval_map_mem_modularRing A N P₀)⟩,
      ⟨aeval (jqModC L) (Q₀.map A.subtype), aeval_map_mem_modularRing A N Q₀⟩, ?_, ?_⟩
  · rw [notMem_redKer_iff, redRes_apply]
    have hxy : ((⟨aeval (jqModC L) (Q₀.map A.subtype), modularRing_le_integralCoeffs N A.toSubring
        (aeval_map_mem_modularRing A N Q₀)⟩ : integralCoeffs A.toSubring) : LaurentSeries L)
        = ι A (aeval (jqModC A) Q₀) := ι_aeval A Q₀ |>.symm
    rw [coeffRed_eq_coeffMap_ϖ A red redBar hred _ _ hxy, ϖ_aeval]
    exact coeffMap_ne_zero_of_injective redBar redBar.injective (aeval_jqModC_ne_zero hQ₀)
  · show (κ : LaurentSeries L) * aeval (jqModC L) (Q₀.map A.subtype)
      = constSeries A.toSubring ⟨c / c', hcc⟩ * aeval (jqModC L) (P₀.map A.subtype)
    have hFF : κ * uQ = algebraMap L FF (c / c') * uP := by
      rw [hκ, mul_assoc, div_mul_cancel₀ uP huQ0]
    have h := congrArg (fun w : FF => (w : LaurentSeries L)) hFF
    simp only [MulMemClass.coe_mul] at h
    rw [huQ, huP, coe_aeval_jF, coe_aeval_jF] at h
    exact h

end RegLevelOne
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section RegAssembly

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] [Fact N.Prime]

local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

open ModularCurve.CharPReduction

set_option maxHeartbeats 3200000 in

theorem coe_mem_modularLocalized_of_mem_gaussRing (hA : A.LiesOverPrime N)
    {k : Type*} [Field k] [CharP k N] (red : A →+* k) (x : FF) (hx : x ∈ gaussRing A N) :
    (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized N A.toSubring red := by
  classical
  have hp : N.Prime := Fact.out
  haveI : CharP kk N := charP_residueField_of_liesOverPrime A hp hA

  have hred0 : ∀ a ∈ IsLocalRing.maximalIdeal A, red a = 0 := fun a ha =>
    map_eq_zero_of_mem_maximalIdeal_algebraicClosure A hA red a ha
  let redBar : kk →+* k := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) red hred0
  have hred : ∀ a : A, redBar (IsLocalRing.residue A a) = red a := fun a =>
    Ideal.Quotient.lift_mk _ _ _

  by_cases hx0 : x = 0
  · rw [hx0]; exact Subring.zero_mem _

  set σ := frickeInvolutionBar N with hσdef
  have hσj : σ (jF N) = jNF A N := frickeInvolutionBar_jF A N
  have hσjN : σ (jNF A N) = jF N := by
    rw [← hσj]; exact frickeInvolutionBar_frickeInvolutionBar N _
  set τ : FF := ((τG A N : gaussRing A N) : FF) with hτdef
  have hτO : τ ∈ gaussRing A N := (τG A N).2
  have hτu : τ ∉ (gaussRing A N).nonunits := coe_τG_not_mem_nonunits A N hp
  have hτ0 : τ ≠ 0 := fun h => hτu ((ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inl h))
  have hστ : σ τ ∈ (gaussRing A N).nonunits := by
    have h := coe_τG_mem_nonunits_gaussComap A N
    rwa [show gaussComap A N (frickeInvolutionBar N) = (gaussRing A N).comap
      ((frickeInvolutionBar N : FF ≃ₐ[AlgebraicClosure ℚ] FF) : FF →+* FF) from rfl,
      mem_nonunits_comap_iff'] at h

  have hM : ∃ M : ℕ, σ (τ ^ M * x) ∈ gaussRing A N := by
    obtain ⟨c, hc, hcne⟩ := exists_smul_mem_gaussRing A N (σ x) ((_root_.map_ne_zero σ).mpr hx0)
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hcne
      have h0 : (⟨(0 : AlgebraicClosure ℚ) • σ x, hc⟩ : gaussRing A N) = 0 :=
        Subtype.ext (zero_smul _ _)
      rw [h0, map_zero]
    by_cases hci : c⁻¹ ∈ A
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      have : σ x = algebraMap (AlgebraicClosure ℚ) FF c⁻¹ * (c • σ x) := by
        rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [this]
      exact mul_mem ((algebraMap_mem_gaussRing_iff A N _).mpr hci) hc
    ·
      have hcA : c ∈ A := (A.mem_or_inv_mem c).resolve_right hci
      have hcmax : (⟨c, hcA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨b, hb⟩ := hu.exists_left_inv
        apply hci
        have hbc : ((b : A) : AlgebraicClosure ℚ) * c = 1 := by
          have := congrArg (fun w : A => (w : AlgebraicClosure ℚ)) hb
          simpa using this
        rw [show c⁻¹ = (b : AlgebraicClosure ℚ) from (eq_inv_of_mul_eq_one_left hbc).symm]
        exact b.2

      obtain ⟨e, he, hene⟩ := exists_smul_mem_gaussRing A N (σ τ) ((_root_.map_ne_zero σ).mpr hτ0)
      have he0 : e ≠ 0 := by
        rintro rfl
        apply hene
        have h0 : (⟨(0 : AlgebraicClosure ℚ) • σ τ, he⟩ : gaussRing A N) = 0 :=
          Subtype.ext (zero_smul _ _)
        rw [h0, map_zero]
      have heA : e ∉ A := by
        intro heA
        apply hene
        rw [← mem_nonunits_gaussRing_iff]
        rw [Algebra.smul_def, ValuationSubring.mem_nonunits_iff, map_mul]
        calc (gaussRing A N).valuation (algebraMap _ FF e) * (gaussRing A N).valuation (σ τ)
            ≤ 1 * (gaussRing A N).valuation (σ τ) := by
              gcongr
              exact (ValuationSubring.valuation_le_one_iff _ _).mpr
                ((algebraMap_mem_gaussRing_iff A N e).mpr heA)
          _ < 1 := by rw [one_mul]; exact (ValuationSubring.mem_nonunits_iff _).mp hστ
      have heiA : e⁻¹ ∈ A := (A.mem_or_inv_mem e).resolve_left heA
      have heimax : (⟨e⁻¹, heiA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨b, hb⟩ := hu.exists_left_inv
        apply heA
        have hbc : ((b : A) : AlgebraicClosure ℚ) * e⁻¹ = 1 := by
          have := congrArg (fun w : A => (w : AlgebraicClosure ℚ)) hb
          simpa using this
        rw [show e = (b : AlgebraicClosure ℚ) from by
          have := eq_inv_of_mul_eq_one_left hbc; rw [inv_inv] at this; exact this.symm]
        exact b.2
      obtain ⟨M, a, hMa⟩ := exists_pow_eq_mul_of_mem_maximalIdeal_algebraicClosure A hA
        ⟨c, hcA⟩ (fun h => hc0 (congrArg Subtype.val h)) ⟨e⁻¹, heiA⟩ heimax
        (fun h => inv_ne_zero he0 (congrArg Subtype.val h))
      refine ⟨M, ?_⟩

      have key : σ (τ ^ M * x) = algebraMap _ FF (a : AlgebraicClosure ℚ)
          * (e • σ τ) ^ M * (c • σ x) := by
        rw [map_mul, map_pow, Algebra.smul_def, Algebra.smul_def, mul_pow]
        have hτe : σ τ = algebraMap _ FF e⁻¹ * (algebraMap _ FF e * σ τ) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ he0, map_one, one_mul]
        have hMa' : (e⁻¹) ^ M = c * (a : AlgebraicClosure ℚ) := by simpa using hMa
        conv_lhs => rw [hτe, mul_pow, ← map_pow, hMa']
        rw [map_mul]; ring
      rw [key]
      exact mul_mem (mul_mem ((algebraMap_mem_gaussRing_iff A N _).mpr a.2) (pow_mem he M)) hc
  obtain ⟨M, hM⟩ := hM

  set y : FF := τ ^ M * x with hydef
  have hyO : y ∈ gaussRing A N := mul_mem (pow_mem hτO M) hx
  obtain ⟨κ, hκK, hy⟩ := exists_sum_eq A N σ hσj hσjN
    (by exact_mod_cast hp.ne_zero) hp y

  have hκO : ∀ i ≤ N, κ i ∈ gaussRing A N := by
    by_contra hnot
    push_neg at hnot
    obtain ⟨i₁, hi₁, hκi₁⟩ := hnot
    have hne : ∃ i ≤ N, κ i ≠ 0 := ⟨i₁, hi₁, fun h => hκi₁ (h ▸ zero_mem _)⟩
    obtain ⟨i₀, hi₀, hκ0, hdiv⟩ := exists_div_mem_gaussRing A N κ hne

    have hbig : 1 < (gaussRing A N).valuation (κ i₀) := by
      have h1 : 1 < (gaussRing A N).valuation (κ i₁) := by
        rw [← not_le, ValuationSubring.valuation_le_one_iff]; exact hκi₁
      have h2 : (gaussRing A N).valuation (κ i₁) ≤ (gaussRing A N).valuation (κ i₀) := by
        have := (ValuationSubring.valuation_le_one_iff _ _).mpr (hdiv i₁ hi₁)
        rwa [map_div₀, div_le_one₀ ((Valuation.pos_iff _).mpr hκ0)] at this
      exact lt_of_lt_of_le h1 h2
    have hinvO : (κ i₀)⁻¹ ∈ gaussRing A N := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀]; exact inv_le_one_of_one_le₀ hbig.le
    have hinvnon : (κ i₀)⁻¹ ∈ (gaussRing A N).nonunits := by
      rw [ValuationSubring.mem_nonunits_iff, map_inv₀]; exact inv_lt_one_of_one_lt₀ hbig
    have hinvK : (κ i₀)⁻¹ ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({(jF N : FF)} : Set FF) :=
      inv_mem (hκK i₀)

    set κ' : ℕ → FF := fun n => if n ≤ N then κ n / κ i₀ else 0 with hκ'
    have hκ'K : ∀ n, κ' n ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({(jF N : FF)} : Set FF) :=
      fun n => by simp only [hκ']; split_ifs; exacts [div_mem (hκK n) (hκK i₀), zero_mem _]
    have hκ'O : ∀ n, κ' n ∈ gaussRing A N :=
      fun n => by simp only [hκ']; split_ifs with h; exacts [hdiv n h, zero_mem _]
    have hsum : ∑ n ∈ Finset.range (N + 1), κ' n * jNF A N ^ n = (κ i₀)⁻¹ * y := by
      rw [hy, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      simp only [hκ', if_pos (Finset.mem_range_succ_iff.mp hn)]; ring
    have h1 : (κ i₀)⁻¹ * y ∈ (gaussRing A N).nonunits := by
      rw [ValuationSubring.mem_nonunits_iff, map_mul]
      calc (gaussRing A N).valuation (κ i₀)⁻¹ * (gaussRing A N).valuation y
          ≤ (gaussRing A N).valuation (κ i₀)⁻¹ * 1 := by
            gcongr; exact (ValuationSubring.valuation_le_one_iff _ _).mpr hyO
        _ < 1 := by rw [mul_one]; exact (ValuationSubring.mem_nonunits_iff _).mp hinvnon
    have h2 : σ ((κ i₀)⁻¹ * y) ∈ (gaussRing A N).nonunits := by
      have hσinvO : σ (κ i₀)⁻¹ ∈ gaussRing A N := mem_gaussComap_of_mem_adjoin A N σ hσj hinvK hinvO
      have hσinvnon : σ (κ i₀)⁻¹ ∈ (gaussRing A N).nonunits := by
        rw [mem_nonunits_gaussRing_iff A N hσinvO,
          show (⟨σ (κ i₀)⁻¹, hσinvO⟩ : gaussRing A N) = sigmaRes A N σ ⟨(κ i₀)⁻¹,
            mem_gaussComap_of_mem_adjoin A N σ hσj hinvK hinvO⟩ from Subtype.ext rfl,
          resHom_sigmaRes_of_mem_adjoin A N σ hσj hinvK hinvO,
          (mem_nonunits_gaussRing_iff A N hinvO).mp hinvnon, map_zero]
      rw [map_mul, ValuationSubring.mem_nonunits_iff, map_mul]
      calc (gaussRing A N).valuation (σ (κ i₀)⁻¹) * (gaussRing A N).valuation (σ y)
          ≤ (gaussRing A N).valuation (σ (κ i₀)⁻¹) * 1 := by
            gcongr; exact (ValuationSubring.valuation_le_one_iff _ _).mpr hM
        _ < 1 := by rw [mul_one]; exact (ValuationSubring.mem_nonunits_iff _).mp hσinvnon
    have hall := forall_mem_nonunits_of_sum_mem_nonunits A N σ hσj hσjN κ' hκ'K hκ'O
      (by rw [hsum]; exact h1) (by rw [hsum]; exact h2) i₀ hi₀
    simp only [hκ', if_pos hi₀, div_self hκ0] at hall
    rw [ValuationSubring.mem_nonunits_iff, map_one] at hall
    exact lt_irrefl _ hall

  have hyL : (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized N A.toSubring red := by
    rw [hy]; push_cast
    refine Subring.sum_mem _ fun i hi => Subring.mul_mem _
      (coe_mem_modularLocalized_of_mem_adjoin A N red redBar hred (hκK i)
        (hκO i (Finset.mem_range_succ_iff.mp hi))) (Subring.pow_mem _ ?_ i)
    rw [coe_jNF]
    exact subring_le_localizedAtKer _ _ _ _ (jqNModC_mem_modularRing N A.toSubring)

  have hτL : (τ : LaurentSeries (AlgebraicClosure ℚ))⁻¹ ∈ modularLocalized N A.toSubring red := by
    have hτcoe : (τ : LaurentSeries (AlgebraicClosure ℚ))
        = ι A (jqModC A - (qExpand A N (jqModC A)) ^ N) := by
      rw [hτdef, coe_τG]; push_cast; rw [map_sub, map_pow, ← coe_jF' A N, coe_jNF, ι_qExpand_jqModC]
    have hτR : (τ : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularRing N A.toSubring := by
      rw [hτdef, coe_τG]; push_cast; rw [coe_jF, coe_jNF]
      exact Subring.sub_mem _ (jqModC_mem_modularRing N A.toSubring)
        (Subring.pow_mem _ (jqNModC_mem_modularRing N A.toSubring) N)
    have hτK : (⟨_, hτR⟩ : modularRing N A.toSubring) ∉ redKer A.toSubring red (modularRing N A.toSubring)
        (modularRing_le_integralCoeffs N A.toSubring) := by
      rw [notMem_redKer_iff, redRes_apply, coeffRed_eq_coeffMap_ϖ A red redBar hred _ _ hτcoe]
      refine coeffMap_ne_zero_of_injective redBar redBar.injective ?_
      rw [← resHom_ι A N (hτcoe ▸ (τG A N).1.2)]
      have : (⟨⟨ι A (jqModC A - qExpand A N (jqModC A) ^ N), hτcoe ▸ (τG A N).1.2⟩,
          ι_mem_gaussRing A N _⟩ : gaussRing A N) = τG A N := Subtype.ext (Subtype.ext hτcoe.symm)
      rw [this]; exact resHom_τG_ne_zero A N hp
    exact (mem_localizedAtKer _ _ _ _).mpr ⟨1, ⟨_, hτR⟩, hτK, by
      rw [OneMemClass.coe_one]; exact inv_mul_cancel₀ (by exact_mod_cast hτ0)⟩
  have hxy : (x : LaurentSeries (AlgebraicClosure ℚ))
      = (y : LaurentSeries (AlgebraicClosure ℚ)) * ((τ : LaurentSeries (AlgebraicClosure ℚ))⁻¹) ^ M := by
    rw [hydef]; push_cast
    rw [inv_pow, mul_comm ((τ : LaurentSeries (AlgebraicClosure ℚ)) ^ M), mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hτ0)), mul_one]
  rw [hxy]
  exact Subring.mul_mem _ hyL (Subring.pow_mem _ hτL M)

theorem coe_mem_modularLocalized_or_inv (hA : A.LiesOverPrime N)
    {k : Type*} [Field k] [CharP k N] (red : A →+* k) (g : FF) (hg : g ≠ 0) :
    (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized N A.toSubring red ∨
      ((g⁻¹ : FF) : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized N A.toSubring red := by
  rcases (gaussRing A N).mem_or_inv_mem g with h | h
  · exact Or.inl (coe_mem_modularLocalized_of_mem_gaussRing A N hA red g h)
  · exact Or.inr (coe_mem_modularLocalized_of_mem_gaussRing A N hA red g⁻¹ h)

end RegAssembly
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

end Ws25.GaussE
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25 P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE"
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25"

end
p2m_reactivate "P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE.AlgebraicCurve.RegularProlongation P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25 P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized.Ws25.GaussE"

p2m_open "ModularCurve~dedekindPsi_prime"

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (g : ↥(modularFunctionFieldBar (1 * q))) :
    (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red ∨
      ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  have hq0 : (q : k) = 0 := CharP.cast_eq_zero k q
  haveI hfact : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩
  haveI : CharP k (1 * q) := by rw [one_mul]; infer_instance
  have hA : A.LiesOverPrime (1 * q) := by
    show (((1 * q : ℕ)) : AlgebraicClosure ℚ) ∈ A.nonunits
    rw [one_mul]
    have hq : red (q : A) = 0 := by rw [map_natCast]; exact hq0
    have hmax : (q : A) ∈ IsLocalRing.maximalIdeal A :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) ((RingHom.mem_ker).mpr hq)
    refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨(q : A).2, ?_⟩
    first | exact hmax | simpa using hmax | (simp at hmax ⊢; exact hmax)
  by_cases hg : g = 0
  · left; rw [hg]; exact Subring.zero_mem _
  exact Ws25.GaussE.coe_mem_modularLocalized_or_inv A (1 * q) hA red g hg

end S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized
end P2MW
export P2MW.S_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized (solution)
