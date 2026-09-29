-- Prove2me | solution 1 for ModularCurve.exists_mul_eq_of_height_one_of_natCast_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/bb29856b-9b21-5054-8502-ff3de74ec3ec

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_kroneckerCongruence
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open scoped Classical
p2m_open "IntermediateField AlgebraicCurve ModularCurve~dedekindPsi_prime~nonempty_modularPolynomialData Polynomial"

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

p2m_alias "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.AlgebraicCurve.RegularProlongation.mapResidue" "AlgebraicCurve.RegularProlongation.mapResidue"
@[scoped simp] private theorem _root_.AlgebraicCurve.RegularProlongation.mapResidue_integers (R : RegularProlongation A F Fbar)
    (e : Fbar ≃ₐ[IsLocalRing.ResidueField A] Fbar') : (R.mapResidue A e).integers = R.integers := rfl

p2m_alias "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.AlgebraicCurve.RegularProlongation.mapResidue_integers" "AlgebraicCurve.RegularProlongation.mapResidue_integers"
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"
private theorem _root_.AlgebraicCurve.RegularProlongation.mapResidue_residue (R : RegularProlongation A F Fbar)
    (e : Fbar ≃ₐ[IsLocalRing.ResidueField A] Fbar') (x : R.integers) :
    (R.mapResidue A e).residue x = e (R.residue x) := rfl

p2m_alias "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.AlgebraicCurve.RegularProlongation.mapResidue_residue" "AlgebraicCurve.RegularProlongation.mapResidue_residue"
end MapResidue
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

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

p2m_alias "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.AlgebraicCurve.RegularProlongation.transport" "AlgebraicCurve.RegularProlongation.transport"
private theorem _root_.AlgebraicCurve.RegularProlongation.mem_transport_integers_iff (R : RegularProlongation A F Fbar)
    (σ : F ≃ₐ[L] F) (f : F) : f ∈ (R.transport A σ).integers ↔ σ f ∈ R.integers := Iff.rfl

p2m_alias "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.AlgebraicCurve.RegularProlongation.mem_transport_integers_iff" "AlgebraicCurve.RegularProlongation.mem_transport_integers_iff"
private theorem _root_.AlgebraicCurve.RegularProlongation.transport_residue (R : RegularProlongation A F Fbar)
    (σ : F ≃ₐ[L] F) (f : F) (h : f ∈ (R.transport A σ).integers) :
    (R.transport A σ).residue ⟨f, h⟩ = R.residue ⟨σ f, h⟩ := rfl

p2m_alias "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.AlgebraicCurve.RegularProlongation.transport_residue" "AlgebraicCurve.RegularProlongation.transport_residue"
end Transport
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

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
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

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
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

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
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

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
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Bivariate

open Polynomial

def bev {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x y : S)
    (P : Polynomial (Polynomial R)) : S :=
  P.eval₂ (eval₂RingHom f x) y

theorem map_bev {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (f : R →+* S) (g : S →+* T) (x y : S) (P : Polynomial (Polynomial R)) :
    g (bev f x y P) = bev (g.comp f) (g x) (g y) P := by
  unfold bev
  rw [hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp
  · simp

theorem bev_map {R R' S : Type*} [CommSemiring R] [CommSemiring R'] [CommSemiring S]
    (h : R →+* R') (f : R' →+* S) (x y : S) (P : Polynomial (Polynomial R)) :
    bev f x y (P.map (mapRingHom h)) = bev (f.comp h) x y P := by
  unfold bev
  rw [eval₂_map]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp
  · simp

theorem bev_mul {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x y : S)
    (P Q : Polynomial (Polynomial R)) : bev f x y (P * Q) = bev f x y P * bev f x y Q := by
  simp [bev]

theorem bev_add {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x y : S)
    (P Q : Polynomial (Polynomial R)) : bev f x y (P + Q) = bev f x y P + bev f x y Q := by
  simp [bev]

theorem bev_sub {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x y : S)
    (P Q : Polynomial (Polynomial R)) : bev f x y (P - Q) = bev f x y P - bev f x y Q := by
  simp [bev]

theorem bev_C {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x y : S)
    (p : Polynomial R) : bev f x y (C p) = p.eval₂ f x := by
  simp [bev]

theorem bev_X {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x y : S) :
    bev f x y X = y := by
  simp [bev]

theorem bev_pow {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x y : S)
    (P : Polynomial (Polynomial R)) (n : ℕ) : bev f x y (P ^ n) = bev f x y P ^ n := by
  unfold bev; rw [eval₂_pow]

theorem jqModC_pow_sq_ne_biv (K : Type*) [Field K] {N : ℕ} (hN : 2 ≤ N) :
    jqModC K ^ (N * N) ≠ jqModC K := by
  intro h
  have ho := congrArg HahnSeries.order h
  have h1 : (jqModC K).order = -1 := by
    have := order_jqModC_pow K 1
    rwa [pow_one, Nat.cast_one] at this
  rw [h1, order_jqModC_pow] at ho
  have h2 : (2 : ℤ) ≤ N := by exact_mod_cast hN
  push_cast at ho
  nlinarith

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

def cA : A →+* FF := (algebraMap L FF : L →+* FF).comp A.subtype

theorem cA_apply (a : A) : cA A N a = algebraMap L FF (a : L) := rfl

def bF (P : Polynomial (Polynomial A)) : FF := bev (cA A N) (jF N) (jNF A N) P

def bF' (P : Polynomial (Polynomial A)) : FF := bev (cA A N) (jNF A N) (jF N) P

def bA (P : Polynomial (Polynomial A)) : LaurentSeries A :=
  bev (algebraMap A (LaurentSeries A)) (jqModC A) (qExpand A N (jqModC A)) P

def bA' (P : Polynomial (Polynomial A)) : LaurentSeries A :=
  bev (algebraMap A (LaurentSeries A)) (qExpand A N (jqModC A)) (jqModC A) P

theorem ι_comp_algebraMap_A :
    (ι A).comp (algebraMap A (LaurentSeries A)) = (algebraMap L (LaurentSeries L)).comp A.subtype := by
  refine RingHom.ext fun a => ?_
  show ι A (algebraMap A (LaurentSeries A) a) = algebraMap L (LaurentSeries L) (a : L)
  rw [algebraMap_laurentSeries_A, ι_C]

theorem ϖ_comp_algebraMap_A :
    (ϖ A).comp (algebraMap A (LaurentSeries A))
      = (algebraMap kk (LaurentSeries kk)).comp (IsLocalRing.residue A) := by
  refine RingHom.ext fun a => ?_
  show ϖ A (algebraMap A (LaurentSeries A) a) = algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A a)
  rw [algebraMap_laurentSeries_A, ϖ_C]

theorem subtype_comp_cA :
    ((laurentBaseChange L (modularFunctionFieldFull N)).val : FF →+* LaurentSeries L).comp (cA A N)
      = (algebraMap L (LaurentSeries L)).comp A.subtype :=
  RingHom.ext fun _ => rfl

theorem coe_bF (P : Polynomial (Polynomial A)) :
    ((bF A N P : FF) : LaurentSeries L) = ι A (bA A N P) := by
  have h1 := map_bev (cA A N)
    ((laurentBaseChange L (modularFunctionFieldFull N)).val : FF →+* LaurentSeries L) (jF N) (jNF A N) P
  have h2 := map_bev (algebraMap A (LaurentSeries A)) (ι A) (jqModC A) (qExpand A N (jqModC A)) P
  rw [ι_comp_algebraMap_A, ι_qExpand_jqModC, coeffMap_jqModC] at h2
  rw [subtype_comp_cA] at h1
  rw [bA, h2]
  refine h1.trans ?_
  show bev _ ((jF N : FF) : LaurentSeries L) ((jNF A N : FF) : LaurentSeries L) P = _
  rw [coe_jF, coe_jNF]

theorem coe_bF' (P : Polynomial (Polynomial A)) :
    ((bF' A N P : FF) : LaurentSeries L) = ι A (bA' A N P) := by
  have h1 := map_bev (cA A N)
    ((laurentBaseChange L (modularFunctionFieldFull N)).val : FF →+* LaurentSeries L) (jNF A N) (jF N) P
  have h2 := map_bev (algebraMap A (LaurentSeries A)) (ι A) (qExpand A N (jqModC A)) (jqModC A) P
  rw [ι_comp_algebraMap_A, ι_qExpand_jqModC, coeffMap_jqModC] at h2
  rw [subtype_comp_cA] at h1
  rw [bA', h2]
  refine h1.trans ?_
  show bev _ ((jNF A N : FF) : LaurentSeries L) ((jF N : FF) : LaurentSeries L) P = _
  rw [coe_jF, coe_jNF]

theorem bF_mem_gaussRing (P : Polynomial (Polynomial A)) : bF A N P ∈ gaussRing A N := by
  have h := ι_mem_gaussRing A N (y := bA A N P) ((coe_bF A N P) ▸ (bF A N P).2)
  convert h using 1; exact Subtype.ext (coe_bF A N P)

theorem bF'_mem_gaussRing (P : Polynomial (Polynomial A)) : bF' A N P ∈ gaussRing A N := by
  have h := ι_mem_gaussRing A N (y := bA' A N P) ((coe_bF' A N P) ▸ (bF' A N P).2)
  convert h using 1; exact Subtype.ext (coe_bF' A N P)

theorem resHom_bF (P : Polynomial (Polynomial A)) :
    resHom A N ⟨bF A N P, bF_mem_gaussRing A N P⟩
      = bev (algebraMap kk (LaurentSeries kk)) (jqModC kk) (qExpand kk N (jqModC kk))
          (P.map (mapRingHom (IsLocalRing.residue A))) := by
  have : (⟨bF A N P, bF_mem_gaussRing A N P⟩ : gaussRing A N)
      = ⟨⟨ι A (bA A N P), (coe_bF A N P) ▸ (bF A N P).2⟩, ι_mem_gaussRing A N _⟩ :=
    Subtype.ext (Subtype.ext (coe_bF A N P))
  rw [this, resHom_ι, bA, map_bev, ϖ_comp_algebraMap_A, coeffMap_jqModC, ϖ_qExpand_jqModC, bev_map]

theorem resHom_bF' (P : Polynomial (Polynomial A)) :
    resHom A N ⟨bF' A N P, bF'_mem_gaussRing A N P⟩
      = bev (algebraMap kk (LaurentSeries kk)) (qExpand kk N (jqModC kk)) (jqModC kk)
          (P.map (mapRingHom (IsLocalRing.residue A))) := by
  have : (⟨bF' A N P, bF'_mem_gaussRing A N P⟩ : gaussRing A N)
      = ⟨⟨ι A (bA' A N P), (coe_bF' A N P) ▸ (bF' A N P).2⟩, ι_mem_gaussRing A N _⟩ :=
    Subtype.ext (Subtype.ext (coe_bF' A N P))
  rw [this, resHom_ι, bA', map_bev, ϖ_comp_algebraMap_A, coeffMap_jqModC, ϖ_qExpand_jqModC, bev_map]

theorem sigma_bF (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N) (hσjN : σ (jNF A N) = jF N)
    (P : Polynomial (Polynomial A)) : σ (bF A N P) = bF' A N P := by
  have h := map_bev (cA A N) (σ : FF →+* FF) (jF N) (jNF A N) P
  rw [RingHom.coe_coe, hσj, hσjN] at h
  have hc : (σ : FF →+* FF).comp (cA A N) = cA A N := RingHom.ext fun a => by
    simp only [RingHom.comp_apply, RingHom.coe_coe, cA_apply]
    exact σ.commutes _
  rw [hc] at h
  exact h

variable (K : Type*) [Field K]

theorem X_sub_C_dvd_of_bev_eq_zero (x : LaurentSeries K) (hx : Transcendental K x) (s : Polynomial K)
    (Q : Polynomial (Polynomial K))
    (hQ : bev (algebraMap K (LaurentSeries K)) x (s.eval₂ (algebraMap K (LaurentSeries K)) x) Q = 0) :
    (X - C s) ∣ Q := by
  have hmonic : (X - C s : Polynomial (Polynomial K)).Monic := monic_X_sub_C s
  rw [← modByMonic_eq_zero_iff_dvd hmonic]
  have hdeg : (Q %ₘ (X - C s)).degree ≤ 0 := by
    have h := degree_modByMonic_lt Q hmonic
    rw [degree_X_sub_C] at h
    exact Nat.WithBot.lt_one_iff_le_zero.mp h
  have hr := eq_C_of_degree_le_zero hdeg
  set r := (Q %ₘ (X - C s)).coeff 0 with hrdef
  have hdiv := modByMonic_add_div Q (X - C s)

  have hev : r.eval₂ (algebraMap K (LaurentSeries K)) x = 0 := by
    have h := congrArg (bev (algebraMap K (LaurentSeries K)) x (s.eval₂ (algebraMap K (LaurentSeries K)) x)) hdiv
    rw [hQ, bev_add, bev_mul, bev_sub, bev_X, bev_C, sub_self, zero_mul, add_zero, hr, bev_C] at h
    exact h
  have hr0 : r = 0 := by
    have := (transcendental_iff.mp hx) r
    apply this
    rwa [aeval_def]
  rw [hr, hr0, C_0]

theorem X_pow_sub_C_X_dvd_of_bev_eq_zero [Fact N.Prime] [CharP K N] (Q : Polynomial (Polynomial K))
    (hQ : bev (algebraMap K (LaurentSeries K)) (qExpand K N (jqModC K)) (jqModC K) Q = 0) :
    (X ^ N - C X : Polynomial (Polynomial K)) ∣ Q := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hmonic : (X ^ N - C X : Polynomial (Polynomial K)).Monic := monic_X_pow_sub_C _ hN0.ne'
  rw [← modByMonic_eq_zero_iff_dvd hmonic]
  set Rm := Q %ₘ (X ^ N - C X) with hRm
  have hdeg : Rm.natDegree < N := by
    have h := degree_modByMonic_lt Q hmonic
    rw [degree_X_pow_sub_C hN0] at h
    by_cases h0 : Rm = 0
    · rw [h0, natDegree_zero]; exact hN0
    · rwa [← hRm, degree_eq_natDegree h0, Nat.cast_lt] at h
  have hdiv := modByMonic_add_div Q (X ^ N - C X)
  have hfrob : qExpand K N (jqModC K) = jqModC K ^ N := ModularCurve.frobenius_identity_geom_unconditional K

  have hev : bev (algebraMap K (LaurentSeries K)) (qExpand K N (jqModC K)) (jqModC K) Rm = 0 := by
    have h := congrArg (bev (algebraMap K (LaurentSeries K)) (qExpand K N (jqModC K)) (jqModC K)) hdiv
    rw [hQ, bev_add, bev_mul, bev_sub, bev_pow, bev_X, bev_C, eval₂_X, ← hfrob, sub_self, zero_mul,
      add_zero] at h
    exact h

  have hsum : ∑ i : Fin N, (Rm.coeff i).eval₂ (algebraMap K (LaurentSeries K)) (qExpand K N (jqModC K))
      * jqModC K ^ (i : ℕ) = 0 := by
    rw [← hev, bev, eval₂_eq_sum_range' (eval₂RingHom _ _) hdeg, Fin.sum_univ_eq_sum_range
      (fun i => (Rm.coeff i).eval₂ (algebraMap K (LaurentSeries K)) (qExpand K N (jqModC K))
        * jqModC K ^ i) N]
    rfl
  have hc := eq_zero_of_sum_mul_pow_jqModC_eq_zero K N
    (fun i : Fin N => (Rm.coeff i).eval₂ (algebraMap K (LaurentSeries K)) (qExpand K N (jqModC K)))
    (fun i => ⟨(Rm.coeff i).eval₂ (algebraMap K (LaurentSeries K)) (jqModC K), by
      rw [hom_eval₂]
      congr 1
      refine RingHom.ext fun a => ?_
      simp [qExpand_C, algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]⟩)
    hsum

  have hcoef : ∀ i < N, Rm.coeff i = 0 := by
    intro i hi
    have h := hc ⟨i, hi⟩
    dsimp only at h
    have h' : (Rm.coeff i).eval₂ (algebraMap K (LaurentSeries K)) (jqModC K) = 0 := by
      apply qExpand_injective (R := K) (N := N)
      rw [map_zero, hom_eval₂]
      convert h using 2
      refine RingHom.ext fun a => ?_
      simp [qExpand_C, algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
    exact (transcendental_iff.mp (ModularCurve.transcendental_jqModC K)) _ (by rwa [aeval_def])
  ext n : 1
  rw [coeff_zero]
  by_cases hn : n < N
  · exact hcoef n hn
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (not_lt.mp hn))

theorem prod_dvd_of_bev_eq_zero [Fact N.Prime] [CharP K N] (Q : Polynomial (Polynomial K))
    (h1 : bev (algebraMap K (LaurentSeries K)) (jqModC K) (qExpand K N (jqModC K)) Q = 0)
    (h2 : bev (algebraMap K (LaurentSeries K)) (qExpand K N (jqModC K)) (jqModC K) Q = 0) :
    ((X - C (X ^ N)) * (X ^ N - C X) : Polynomial (Polynomial K)) ∣ Q := by
  have hfrob : qExpand K N (jqModC K) = jqModC K ^ N := ModularCurve.frobenius_identity_geom_unconditional K
  have hs : (X ^ N : Polynomial K).eval₂ (algebraMap K (LaurentSeries K)) (jqModC K)
      = qExpand K N (jqModC K) := by
    rw [eval₂_pow, eval₂_X, hfrob]
  obtain ⟨G, hG⟩ := X_sub_C_dvd_of_bev_eq_zero K (jqModC K) (ModularCurve.transcendental_jqModC K)
    (X ^ N) Q (by rw [hs]; exact h1)
  have hG0 : bev (algebraMap K (LaurentSeries K)) (qExpand K N (jqModC K)) (jqModC K) G = 0 := by
    have h := h2
    rw [hG, bev_mul, bev_sub, bev_X, bev_C, eval₂_pow, eval₂_X,
      show qExpand K N (jqModC K) ^ N = jqModC K ^ (N * N) from by rw [hfrob, ← pow_mul]] at h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h).symm (jqModC_pow_sq_ne_biv K (Fact.out : N.Prime).two_le)
    · exact h
  obtain ⟨H, hH⟩ := X_pow_sub_C_X_dvd_of_bev_eq_zero N K G hG0
  exact ⟨H, by rw [hG, hH, mul_assoc]⟩

theorem map_Φ_eq [Fact N.Prime] [CharP K N] (data : ModularPolynomialData N)
    (hKr : KroneckerCongruence N data) :
    data.Φ.map (mapRingHom (Int.castRingHom K))
      = ((X - C (X ^ N)) * (X ^ N - C X) : Polynomial (Polynomial K)) := by
  have hc : (ZMod.castHom (dvd_refl N) K).comp (Int.castRingHom (ZMod N)) = Int.castRingHom K :=
    RingHom.ext_int _ _
  have hcomp : (mapRingHom (ZMod.castHom (dvd_refl N) K)).comp (mapRingHom (Int.castRingHom (ZMod N)))
      = mapRingHom (Int.castRingHom K) := RingHom.ext fun p => by
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_map, hc]
  have h := congrArg (Polynomial.map (mapRingHom (ZMod.castHom (dvd_refl N) K))) hKr
  simp only [reduceModBivar, coe_mapRingHom, Polynomial.map_map, hcomp, Polynomial.map_mul,
    Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] at h
  rw [h, C_pow]
  ring

variable {K}

theorem bA_map_Φ_eq_zero (data : ModularPolynomialData N) :
    bA A N (data.Φ.map (mapRingHom (Int.castRingHom A))) = 0 := by
  rw [bA, bev_map]
  have h0 := data.eval_jqNModC_mul_eq_zero A 1
  unfold bev
  convert h0 using 2 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  · symm
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [jqNModC_one, eq_intCast, map_intCast]
    · simp [jqNModC_one]
  · show qExpand A N (jqModC A) = qExpand A (1 * N) (jqModC A)
    exact (qExpand_congr (one_mul N) _).symm

theorem sat_one [Fact N.Prime] [CharP kk N] (data : ModularPolynomialData N) (hKr : KroneckerCongruence N data)
    (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N) (hσjN : σ (jNF A N) = jF N)
    (A₀ : Subring L) (hle : A₀ ≤ A.toSubring) {ϖ₀ : A₀}
    (hϖm : IsLocalRing.residue A (Subring.inclusion hle ϖ₀) = 0)
    (hgen : ∀ a : A₀, IsLocalRing.residue A (Subring.inclusion hle a) = 0 → ∃ c : A₀, a = ϖ₀ * c)
    (P : Polynomial (Polynomial A₀)) (x : FF) (hx : x ∈ gaussRing A N) (hσx : σ x ∈ gaussRing A N)
    (hb : bF A N (P.map (mapRingHom (Subring.inclusion hle))) = algebraMap L FF ((ϖ₀ : L)) * x) :
    ∃ Q : Polynomial (Polynomial A₀),
      bF A N (P.map (mapRingHom (Subring.inclusion hle)))
        = algebraMap L FF ((ϖ₀ : L)) * bF A N (Q.map (mapRingHom (Subring.inclusion hle))) := by
  set incl : A₀ →+* A := Subring.inclusion hle with hincl

  have hϖO : algebraMap L FF ((ϖ₀ : L)) ∈ gaussRing A N :=
    (algebraMap_mem_gaussRing_iff A N _).mpr (incl ϖ₀).2
  have hresϖ : resHom A N ⟨algebraMap L FF ((ϖ₀ : L)), hϖO⟩ = 0 := by
    have h := resHom_algebraMap A N (incl ϖ₀) hϖO
    rw [hϖm, map_zero] at h
    exact h

  have hres1 : resHom A N ⟨bF A N (P.map (mapRingHom incl)), bF_mem_gaussRing A N _⟩ = 0 := by
    have : (⟨bF A N (P.map (mapRingHom incl)), bF_mem_gaussRing A N _⟩ : gaussRing A N)
        = ⟨algebraMap L FF ((ϖ₀ : L)), hϖO⟩ * ⟨x, hx⟩ := Subtype.ext hb
    rw [this, map_mul, hresϖ, zero_mul]
  have hres2 : resHom A N ⟨bF' A N (P.map (mapRingHom incl)), bF'_mem_gaussRing A N _⟩ = 0 := by
    have hb' : bF' A N (P.map (mapRingHom incl)) = algebraMap L FF ((ϖ₀ : L)) * σ x := by
      rw [← sigma_bF A N σ hσj hσjN, hb, map_mul, AlgEquiv.commutes]
    have : (⟨bF' A N (P.map (mapRingHom incl)), bF'_mem_gaussRing A N _⟩ : gaussRing A N)
        = ⟨algebraMap L FF ((ϖ₀ : L)), hϖO⟩ * ⟨σ x, hσx⟩ := Subtype.ext hb'
    rw [this, map_mul, hresϖ, zero_mul]

  set r₀ : A₀ →+* kk := (IsLocalRing.residue A).comp incl with hr₀
  have hPbar : (P.map (mapRingHom incl)).map (mapRingHom (IsLocalRing.residue A)) = P.map (mapRingHom r₀) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun p => by simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_map, hr₀]
  have h1 : bev (algebraMap kk (LaurentSeries kk)) (jqModC kk) (qExpand kk N (jqModC kk))
      (P.map (mapRingHom r₀)) = 0 := by rw [← hPbar, ← resHom_bF, hres1]
  have h2 : bev (algebraMap kk (LaurentSeries kk)) (qExpand kk N (jqModC kk)) (jqModC kk)
      (P.map (mapRingHom r₀)) = 0 := by rw [← hPbar, ← resHom_bF', hres2]
  have hdvd : data.Φ.map (mapRingHom (Int.castRingHom kk)) ∣ P.map (mapRingHom r₀) := by
    rw [map_Φ_eq N kk data hKr]; exact prod_dvd_of_bev_eq_zero N kk _ h1 h2

  set Φ₀ : Polynomial (Polynomial A₀) := data.Φ.map (mapRingHom (Int.castRingHom A₀)) with hΦ₀
  have hΦ₀m : Φ₀.Monic := data.monic.map _
  have hΦ₀bar : Φ₀.map (mapRingHom r₀) = data.Φ.map (mapRingHom (Int.castRingHom kk)) := by
    rw [hΦ₀, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun p => by
      simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_map,
        RingHom.ext_int (r₀.comp (Int.castRingHom A₀)) (Int.castRingHom kk)]
  have hΦ₀incl : Φ₀.map (mapRingHom incl) = data.Φ.map (mapRingHom (Int.castRingHom A)) := by
    rw [hΦ₀, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun p => by
      simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_map,
        RingHom.ext_int (incl.comp (Int.castRingHom A₀)) (Int.castRingHom A)]
  have hdiv := modByMonic_add_div P Φ₀
  set Rm := P %ₘ Φ₀ with hRm
  set E := P /ₘ Φ₀ with hE
  have hdegΦ : Φ₀.natDegree = N + 1 := by
    rw [hΦ₀, (data.monic).natDegree_map, data.natDegree_eq, dedekindPsi_prime (Fact.out : N.Prime)]
  have hRm0 : Rm.map (mapRingHom r₀) = 0 := by
    by_contra hne
    have hdvdR : Φ₀.map (mapRingHom r₀) ∣ Rm.map (mapRingHom r₀) := by
      have : Rm = P - Φ₀ * E := by rw [← hdiv]; ring
      rw [this, Polynomial.map_sub, Polynomial.map_mul, hΦ₀bar]
      exact dvd_sub hdvd (dvd_mul_right _ _)
    have hlt : (Rm.map (mapRingHom r₀)).natDegree < (Φ₀.map (mapRingHom r₀)).natDegree := by
      rw [hΦ₀m.natDegree_map, hdegΦ]
      refine lt_of_le_of_lt natDegree_map_le ?_
      by_cases h0 : Rm = 0
      · rw [h0, natDegree_zero]; exact Nat.succ_pos N
      · have := degree_modByMonic_lt P hΦ₀m
        rw [← hRm, degree_eq_natDegree h0, degree_eq_natDegree hΦ₀m.ne_zero, Nat.cast_lt, hdegΦ] at this
        exact this
    exact (hΦ₀m.map (mapRingHom r₀)).not_dvd_of_natDegree_lt hne hlt hdvdR

  have hcoef : ∀ i j, r₀ ((Rm.coeff i).coeff j) = 0 := by
    intro i j
    have := congrArg (fun T : Polynomial (Polynomial kk) => (T.coeff i).coeff j) hRm0
    simpa only [Polynomial.coeff_map, coe_mapRingHom, Polynomial.coeff_zero] using this
  have hC : C (C ϖ₀) ∣ Rm := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [C_dvd_iff_dvd_coeff]
    intro j
    obtain ⟨c, hc⟩ := hgen _ (hcoef i j)
    exact ⟨c, hc⟩
  obtain ⟨Qm, hQm⟩ := hC
  refine ⟨Qm, ?_⟩

  have hΦ0 : bF A N (Φ₀.map (mapRingHom incl)) = 0 := by
    apply Subtype.ext
    rw [coe_bF, hΦ₀incl, bA_map_Φ_eq_zero, map_zero]
    rfl
  let ψ : Polynomial (Polynomial A₀) →+* FF :=
    (eval₂RingHom (eval₂RingHom (cA A N) (jF N)) (jNF A N)).comp (mapRingHom (mapRingHom incl))
  have hψ : ∀ T : Polynomial (Polynomial A₀), bF A N (T.map (mapRingHom incl)) = ψ T := fun T => rfl
  have hψC : ψ (C (C ϖ₀)) = algebraMap L FF ((ϖ₀ : L)) := by
    rw [← hψ, Polynomial.map_C, coe_mapRingHom, Polynomial.map_C, bF, bev_C, eval₂_C]
    rfl
  rw [hψ, hψ, ← hdiv, hQm, map_add, map_mul, map_mul, hψC, ← hψ Φ₀, hΦ0, zero_mul, add_zero]

theorem sat_pow [Fact N.Prime] [CharP kk N] (data : ModularPolynomialData N) (hKr : KroneckerCongruence N data)
    (σ : FF ≃ₐ[L] FF) (hσj : σ (jF N) = jNF A N) (hσjN : σ (jNF A N) = jF N)
    (A₀ : Subring L) (hle : A₀ ≤ A.toSubring) {ϖ₀ : A₀} (hϖ0 : (ϖ₀ : L) ≠ 0)
    (hϖm : IsLocalRing.residue A (Subring.inclusion hle ϖ₀) = 0)
    (hgen : ∀ a : A₀, IsLocalRing.residue A (Subring.inclusion hle a) = 0 → ∃ c : A₀, a = ϖ₀ * c)
    (m : ℕ) : ∀ (P : Polynomial (Polynomial A₀)) (x : FF), x ∈ gaussRing A N → σ x ∈ gaussRing A N →
      bF A N (P.map (mapRingHom (Subring.inclusion hle))) = algebraMap L FF ((ϖ₀ : L) ^ m) * x →
      ∃ Q : Polynomial (Polynomial A₀), x = bF A N (Q.map (mapRingHom (Subring.inclusion hle))) := by
  induction m with
  | zero =>
    intro P x _ _ hb
    exact ⟨P, by rw [pow_zero, map_one, one_mul] at hb; exact hb.symm⟩
  | succ m ih =>
    intro P x hx hσx hb
    have hϖO : algebraMap L FF ((ϖ₀ : L)) ∈ gaussRing A N :=
      (algebraMap_mem_gaussRing_iff A N _).mpr (Subring.inclusion hle ϖ₀).2
    have hϖmO : algebraMap L FF ((ϖ₀ : L) ^ m) ∈ gaussRing A N := by
      rw [map_pow]; exact pow_mem hϖO m
    have hx' : algebraMap L FF ((ϖ₀ : L) ^ m) * x ∈ gaussRing A N := mul_mem hϖmO hx
    have hσx' : σ (algebraMap L FF ((ϖ₀ : L) ^ m) * x) ∈ gaussRing A N := by
      rw [map_mul, AlgEquiv.commutes]; exact mul_mem hϖmO hσx
    obtain ⟨Q₁, hQ₁⟩ := sat_one A N data hKr σ hσj hσjN A₀ hle hϖm hgen P _ hx' hσx'
      (by rw [hb, pow_succ', map_mul, mul_assoc])
    have hb₁ : bF A N (Q₁.map (mapRingHom (Subring.inclusion hle))) = algebraMap L FF ((ϖ₀ : L) ^ m) * x := by
      have h := hQ₁.symm.trans hb
      rw [pow_succ', map_mul, mul_assoc] at h
      exact mul_left_cancel₀ ((_root_.map_ne_zero (algebraMap L FF)).mpr hϖ0) h
    exact ih Q₁ x hx hσx hb₁

def θ (A₀ : Subring L) : Polynomial (Polynomial A₀) →+* LaurentSeries L :=
  eval₂RingHom (eval₂RingHom (ModularCurve.CharPReduction.constSeries A₀) (jqModC L)) (jqNModC L N)

theorem coe_bF_map (A₀ : Subring L) (hle : A₀ ≤ A.toSubring) (P : Polynomial (Polynomial A₀)) :
    ((bF A N (P.map (mapRingHom (Subring.inclusion hle))) : FF) : LaurentSeries L) = θ N A₀ P := by
  rw [coe_bF, bA, bev_map, map_bev, ι_qExpand_jqModC, coeffMap_jqModC]
  have hc : (ι A).comp ((algebraMap A (LaurentSeries A)).comp (Subring.inclusion hle))
      = ModularCurve.CharPReduction.constSeries A₀ := RingHom.ext fun a => by
    show ι A (algebraMap A (LaurentSeries A) (Subring.inclusion hle a)) = algebraMap L (LaurentSeries L) (a : L)
    rw [algebraMap_laurentSeries_A, ι_C]
    rfl
  rw [hc]
  rfl

theorem θ_mem_modularRing (A₀ : Subring L) (P : Polynomial (Polynomial A₀)) :
    θ N A₀ P ∈ ModularCurve.CharPReduction.modularRing N A₀ := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
  | monomial n p =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ ?_ n)
    · rw [θ, coe_eval₂RingHom, eval₂_C, coe_eval₂RingHom]
      induction p using Polynomial.induction_on' with
      | add p q hp hq => rw [eval₂_add]; exact Subring.add_mem _ hp hq
      | monomial k a =>
        rw [← C_mul_X_pow_eq_monomial, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
        exact Subring.mul_mem _ (ModularCurve.CharPReduction.constSeries_mem_modularRing N A₀ a)
          (Subring.pow_mem _ (ModularCurve.CharPReduction.jqModC_mem_modularRing N A₀) k)
    · show θ N A₀ X ∈ ModularCurve.CharPReduction.modularRing N A₀
      rw [θ, coe_eval₂RingHom, eval₂_X]
      exact ModularCurve.CharPReduction.jqNModC_mem_modularRing N A₀

theorem mem_modularRing_iff_exists (A₀ : Subring L) (b : LaurentSeries L) :
    b ∈ ModularCurve.CharPReduction.modularRing N A₀ ↔ ∃ P : Polynomial (Polynomial A₀), b = θ N A₀ P := by
  constructor
  · intro hb
    refine Subring.closure_induction (p := fun b _ => ∃ P : Polynomial (Polynomial A₀), b = θ N A₀ P)
      ?_ ⟨0, by rw [map_zero]⟩ ⟨1, by rw [map_one]⟩ ?_ ?_ ?_ hb
    · rintro y (⟨a, rfl⟩ | rfl | rfl)
      · exact ⟨C (C a), by rw [θ, coe_eval₂RingHom, eval₂_C, coe_eval₂RingHom, eval₂_C]⟩
      · exact ⟨C X, by rw [θ, coe_eval₂RingHom, eval₂_C, coe_eval₂RingHom, eval₂_X]⟩
      · exact ⟨X, by rw [θ, coe_eval₂RingHom, eval₂_X]⟩
    · rintro y z _ _ ⟨P, rfl⟩ ⟨Q, rfl⟩; exact ⟨P + Q, by rw [map_add]⟩
    · rintro y _ ⟨P, rfl⟩; exact ⟨-P, (map_neg (θ N A₀) P).symm⟩
    · rintro y z _ _ ⟨P, rfl⟩ ⟨Q, rfl⟩; exact ⟨P * Q, by rw [map_mul]⟩
  · rintro ⟨P, rfl⟩; exact θ_mem_modularRing N A₀ P

theorem mem_modularRing_iff_exists_bF (A₀ : Subring L) (hle : A₀ ≤ A.toSubring) (b : LaurentSeries L) :
    b ∈ ModularCurve.CharPReduction.modularRing N A₀ ↔
      ∃ P : Polynomial (Polynomial A₀),
        b = ((bF A N (P.map (mapRingHom (Subring.inclusion hle))) : FF) : LaurentSeries L) := by
  rw [mem_modularRing_iff_exists]
  simp only [coe_bF_map]

end Bivariate
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section RedBar

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]

theorem liesOverPrime_of_red (red : A →+* k) : A.LiesOverPrime q := by
  have h0 : red (q : A) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k q
  have hq : ((q : A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by simp
  show (q : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [← hq, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h1 := congrArg red u.inv_mul
  rw [map_mul, hu, h0, mul_zero, map_one] at h1
  exact zero_ne_one h1

def redBarOf (red : A →+* k) : IsLocalRing.ResidueField A →+* k :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) red fun a ha =>
    ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q (liesOverPrime_of_red red) red a
      ((ValuationSubring.valuation_lt_one_iff A a).mp ha)

theorem redBarOf_residue (red : A →+* k) (a : A) :
    redBarOf (q := q) red (IsLocalRing.residue A a) = red a :=
  Ideal.Quotient.lift_mk _ _ _

end RedBar
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Presentation

open ModularCurve.NodeLocalized ModularCurve.CharPReduction Polynomial

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "LS" => LaurentSeries (AlgebraicClosure ℚ)
local notation "A₀" => coeffSubring A K

theorem algebraMap_K_apply (x : K) : algebraMap K LS x = algebraMap ℚ̄ LS (x : ℚ̄) := rfl

theorem fieldOver_eq_adjoin :
    fieldOver N K = (IntermediateField.adjoin K ({jqModC ℚ̄, jqNModC ℚ̄ N} : Set LS)).toSubfield := by
  have hr : Set.range (constSeries K.toSubalgebra.toSubring) = Set.range (algebraMap K LS) := by
    ext x; constructor
    · rintro ⟨a, rfl⟩; exact ⟨⟨a, a.2⟩, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨⟨a, a.2⟩, rfl⟩
  rw [fieldOver, hr]
  rfl

theorem exists_div_eq (x : K) : ∃ a b : A₀, (b : ℚ̄) ≠ 0 ∧ (x : ℚ̄) * b = a := by
  rcases A.mem_or_inv_mem (x : ℚ̄) with h | h
  · exact ⟨⟨x, h, x.2⟩, ⟨1, A.one_mem, K.one_mem⟩, one_ne_zero, by simp⟩
  · by_cases hx : (x : ℚ̄) = 0
    · exact ⟨⟨0, A.zero_mem, K.zero_mem⟩, ⟨1, A.one_mem, K.one_mem⟩, one_ne_zero, by simp [hx]⟩
    · refine ⟨⟨1, A.one_mem, K.one_mem⟩, ⟨(x : ℚ̄)⁻¹, h, ?_⟩, inv_ne_zero hx, ?_⟩
      · exact K.inv_mem x.2
      · simp [mul_inv_cancel₀ hx]

theorem exists_mul_mem_coeffSubring (s : Finset K) :
    ∃ d : A₀, (d : ℚ̄) ≠ 0 ∧ ∀ x ∈ s, (d : ℚ̄) * x ∈ A₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⟨1, A.one_mem, K.one_mem⟩, one_ne_zero, fun x hx => absurd hx (Finset.notMem_empty _)⟩
  | insert x s hxs ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, b, hb, hab⟩ := exists_div_eq A K x
    refine ⟨d * b, mul_ne_zero hd hb, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · have : ((d * b : coeffSubring A K) : ℚ̄) * (y : ℚ̄) = (d : ℚ̄) * ((y : ℚ̄) * b) := by
        push_cast; ring
      rw [this, hab]; exact mul_mem d.2 a.2
    · have : ((d * b : coeffSubring A K) : ℚ̄) * (y : ℚ̄) = (b : ℚ̄) * ((d : ℚ̄) * y) := by
        push_cast; ring
      rw [this]; exact mul_mem b.2 (h y hy)

end Presentation
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Presentation2

open ModularCurve.NodeLocalized ModularCurve.CharPReduction Polynomial IntermediateField

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "LS" => LaurentSeries (AlgebraicClosure ℚ)
local notation "A₀" => coeffSubring A K
local notation "jj" => jqModC (AlgebraicClosure ℚ)
local notation "jjN" => jqNModC (AlgebraicClosure ℚ) N

def evalAtJBar : ℤ[X] →+* LS := eval₂RingHom (Int.castRingHom LS) jj

theorem evalAtJBar_eq : (evalAtJBar : ℤ[X] →+* LS) = (coeffMap (algebraMap ℚ ℚ̄)).comp evalAtJ := by
  refine Polynomial.ringHom_ext (fun n => by simp [evalAtJBar]) ?_
  simp only [evalAtJBar, coe_eval₂RingHom, eval₂_X, RingHom.comp_apply, evalAtJ_X]
  exact (coeffMap_jqModC _).symm

theorem modularPolynomial_eval₂_bar (data : ModularPolynomialData N) :
    data.Φ.eval₂ evalAtJBar jjN = 0 := by
  have h := congrArg (coeffMap (algebraMap ℚ ℚ̄)) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂, ← evalAtJBar_eq] at h
  rwa [← jqNModC_rat, coeffMap_jqNModC] at h

theorem isIntegral_jN (data : ModularPolynomialData N) :
    IsIntegral (K⟮(jj : LS)⟯) (jjN : LS) := by
  let φ : ℤ[X] →+* K⟮(jj : LS)⟯ :=
    eval₂RingHom (Int.castRingHom _) ⟨jj, mem_adjoin_simple_self K (jj : LS)⟩
  refine ⟨data.Φ.map φ, data.monic.map φ, ?_⟩
  rw [eval₂_map]
  have hcomp : (algebraMap (K⟮(jj : LS)⟯) LS).comp φ = evalAtJBar := by
    refine Polynomial.ringHom_ext (fun n => by simp [φ, evalAtJBar]) ?_
    simp only [RingHom.comp_apply, φ, coe_eval₂RingHom, eval₂_X, evalAtJBar]
    rfl
  rw [hcomp]
  exact modularPolynomial_eval₂_bar N data

theorem exists_presentation_K (data : ModularPolynomialData N) {g : LS} (hg : g ∈ fieldOver N K) :
    ∃ D : K[X], aeval (jj : LS) D ≠ 0 ∧
      g * aeval (jj : LS) D ∈ Algebra.adjoin K ({(jj : LS), jjN} : Set LS) := by
  classical
  rw [fieldOver_eq_adjoin] at hg
  change g ∈ IntermediateField.adjoin K ({(jj : LS), jjN} : Set LS) at hg

  have hg' : g ∈ (K⟮(jj : LS)⟯)⟮(jjN : LS)⟯ := by
    have h2 := IntermediateField.adjoin_adjoin_left K ({(jj : LS)} : Set LS) ({(jjN : LS)} : Set LS)
    have hset : ({(jj : LS)} : Set LS) ∪ {(jjN : LS)} = {(jj : LS), jjN} := by
      ext x; simp [or_comm]
    rw [hset] at h2
    rw [← h2] at hg
    exact hg

  have hint := isIntegral_jN N K data
  have hg'' : g ∈ Algebra.adjoin (K⟮(jj : LS)⟯) ({(jjN : LS)} : Set LS) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]; exact hg'
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hg''
  obtain ⟨p, rfl⟩ := hg''

  have hcoef : ∀ i, ∃ r s : K[X], aeval (jj : LS) s ≠ 0 ∧
      ((p.coeff i : K⟮(jj : LS)⟯) : LS) * aeval (jj : LS) s = aeval (jj : LS) r := by
    intro i
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K _).mp (p.coeff i).2
    by_cases hs : aeval (jj : LS) s = 0
    · refine ⟨0, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
      rw [map_one, mul_one, map_zero, hrs, hs, div_zero]
    · exact ⟨r, s, hs, by rw [hrs, div_mul_cancel₀ _ hs]⟩
  choose r s hs hrs using hcoef

  set S : Subalgebra K LS := Algebra.adjoin K ({(jj : LS), jjN} : Set LS) with hS
  have hjS : (jj : LS) ∈ S := Algebra.subset_adjoin (by simp)
  have hjNS : (jjN : LS) ∈ S := Algebra.subset_adjoin (by simp)
  have haevS : ∀ t : K[X], aeval (jj : LS) t ∈ S := fun t => by
    rw [Polynomial.aeval_eq_sum_range]
    exact S.sum_mem fun n _ => S.smul_mem (S.pow_mem hjS n) _

  refine ⟨∏ k ∈ p.support, s k, ?_, ?_⟩
  · rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun k _ => hs k
  ·
    show aeval (jjN : LS) p * aeval (jj : LS) (∏ k ∈ p.support, s k) ∈ S
    have hp : aeval (jjN : LS) p = ∑ i ∈ p.support, algebraMap _ LS (p.coeff i) * (jjN : LS) ^ i := by
      conv_lhs => rw [p.as_sum_support]
      rw [map_sum]
      simp only [aeval_monomial]
    rw [hp, Finset.sum_mul]
    refine S.sum_mem fun i hi => ?_
    have hD : aeval (jj : LS) (∏ k ∈ p.support, s k)
        = aeval (jj : LS) (s i) * aeval (jj : LS) (∏ k ∈ p.support.erase i, s k) := by
      rw [← map_mul, Finset.mul_prod_erase _ _ hi]

    have : (algebraMap (K⟮(jj : LS)⟯) LS (p.coeff i)) * (jjN : LS) ^ i * aeval (jj : LS) (∏ k ∈ p.support, s k)
        = aeval (jj : LS) (r i) * aeval (jj : LS) (∏ k ∈ p.support.erase i, s k) * (jjN : LS) ^ i := by
      rw [hD, ← hrs i]
      show ((p.coeff i : K⟮(jj : LS)⟯) : LS) * (jjN : LS) ^ i * _ = _
      ring
    rw [this]
    exact S.mul_mem (S.mul_mem (haevS _) (haevS _)) (S.pow_mem hjNS i)

theorem exists_mul_mem_modularRing_of_mem_adjoin {h : LS}
    (hh : h ∈ Algebra.adjoin K ({(jj : LS), jjN} : Set LS)) :
    ∃ d : A₀, (d : ℚ̄) ≠ 0 ∧ algebraMap ℚ̄ LS (d : ℚ̄) * h ∈ modularRing N A₀ := by
  classical
  have hrange : Algebra.adjoin K ({(jj : LS), jjN} : Set LS)
      = (MvPolynomial.aeval (R := K) ![(jj : LS), jjN]).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    congr 1
    ext x; simp [or_comm]
  rw [hrange] at hh
  obtain ⟨Q, rfl⟩ := hh
  obtain ⟨d, hd, hdQ⟩ := exists_mul_mem_coeffSubring A K (Q.support.image Q.coeff)
  refine ⟨d, hd, ?_⟩

  have hcoeffs : ∀ m, (d : ℚ̄) * ((MvPolynomial.coeff m Q : K) : ℚ̄) ∈ A₀ := by
    intro m
    by_cases hm : m ∈ Q.support
    · exact hdQ _ (Finset.mem_image_of_mem _ hm)
    · rw [MvPolynomial.notMem_support_iff.mp hm]; simp [zero_mem]
  let Q₀ : MvPolynomial (Fin 2) A₀ := ∑ m ∈ Q.support, MvPolynomial.monomial m ⟨_, hcoeffs m⟩
  have hQ : algebraMap ℚ̄ LS (d : ℚ̄) * MvPolynomial.aeval ![(jj : LS), jjN] Q
      = MvPolynomial.eval₂Hom (constSeries A₀) ![(jj : LS), jjN] Q₀ := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    rw [map_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.aeval_monomial, MvPolynomial.eval₂Hom_monomial, ← mul_assoc]
    congr 1
    show algebraMap ℚ̄ LS (d : ℚ̄) * algebraMap ℚ̄ LS ((MvPolynomial.coeff m Q : K) : ℚ̄)
      = algebraMap ℚ̄ LS ((d : ℚ̄) * ((MvPolynomial.coeff m Q : K) : ℚ̄))
    rw [map_mul]
  show algebraMap ℚ̄ LS (d : ℚ̄) * MvPolynomial.aeval ![(jj : LS), jjN] Q ∈ modularRing N A₀
  rw [hQ]

  induction Q₀ using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  | add p' q' hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p' i hp =>
    rw [map_mul, MvPolynomial.eval₂Hom_X']
    refine mul_mem hp (Subring.subset_closure (Or.inr ?_))
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

end Presentation2
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section GoingDown

open Ideal

theorem eq_of_le_of_height_eq_one {R : Type*} [CommRing R] [IsDomain R]
    (p : Ideal R) [hp : p.IsPrime] (hh : p.height = 1)
    (q : Ideal R) (hq : q.IsPrime) (hq0 : q ≠ ⊥) (hqp : q ≤ p) : q = p := by
  set S := Localization.AtPrime p
  have hdim : ringKrullDim S = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S, hh]
    norm_cast
  have hKDL : Ring.KrullDimLE 1 S :=
    Ring.krullDimLE_iff.mpr (le_of_eq (by rw [hdim, Nat.cast_one]))
  have hmax : ∀ P : Ideal S, P ≠ ⊥ → P.IsPrime → P.IsMaximal :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hKDL
  have hdisj : Disjoint (p.primeCompl : Set R) q :=
    Set.disjoint_left.mpr fun x hx hxq => hx (hqp hxq)
  have hqS : (Ideal.map (algebraMap R S) q).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q hq hdisj
  have hqS0 : Ideal.map (algebraMap R S) q ≠ ⊥ := by
    obtain ⟨b, hbq, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
    intro hbot
    have hbS : algebraMap R S b ∈ Ideal.map (algebraMap R S) q := Ideal.mem_map_of_mem _ hbq
    rw [hbot, Ideal.mem_bot] at hbS
    exact hb ((IsLocalization.injective S p.primeCompl_le_nonZeroDivisors) (by rw [hbS, map_zero]))
  have hqmax : Ideal.map (algebraMap R S) q = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (hmax _ hqS0 hqS)
  rw [← IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl S hq hdisj, hqmax,
    Localization.AtPrime.comap_maximalIdeal]

theorem under_eq_of_height_eq_one {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [FaithfulSMul R S] [Algebra.HasGoingDown R S]
    (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (P₀ : Ideal R) [P₀.IsPrime] (hP₀ : P₀ ≠ ⊥) (hle : P₀ ≤ 𝔭.under R) :
    𝔭.under R = P₀ := by
  by_contra hne
  have hlt : P₀ < 𝔭.under R := lt_of_le_of_ne hle (Ne.symm hne)

  obtain ⟨𝔮, h𝔮𝔭, h𝔮prime, h𝔮over⟩ := Ideal.exists_ideal_lt_liesOver_of_lt 𝔭 hlt
  have h𝔮ne : 𝔮 ≠ ⊥ := by
    rintro rfl
    apply hP₀
    rw [h𝔮over.over, Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R S)]
  exact h𝔮𝔭.ne (eq_of_le_of_height_eq_one 𝔭 h𝔭 𝔮 h𝔮prime h𝔮ne h𝔮𝔭.le)

end GoingDown
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Assembly

open ModularCurve.NodeLocalized ModularCurve.CharPReduction Polynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q]
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "LS" => LaurentSeries (AlgebraicClosure ℚ)
local notation "jj" => jqModC (AlgebraicClosure ℚ)

theorem nonempty_modularPolynomialData : Nonempty (ModularPolynomialData (1 * q)) := by
  haveI : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩
  obtain ⟨data, -⟩ := ModularCurve.exists_kroneckerCongruence_of_prime (1 * q)
  exact ⟨data⟩

variable (A) in

def inclA : coeffSubring A K →+* A where
  toFun a := ⟨a, a.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_inclA (a : coeffSubring A K) : ((inclA A K a : A) : ℚ̄) = a := rfl

theorem isDiscreteValuationRing_coeffSubring (hq : A.LiesOverPrime q) :
    IsDiscreteValuationRing (coeffSubring A K) := by
  rcases coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso

    have hinvK : ((q : ℚ̄))⁻¹ ∈ K := inv_mem (_root_.natCast_mem K q)
    have hinvA0 : ((q : ℚ̄))⁻¹ ∈ coeffSubring A K := by rw [h]; exact hinvK
    have hinvA : ((q : ℚ̄))⁻¹ ∈ A := hinvA0.1
    have hq0 : (q : ℚ̄) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

    rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff] at hq
    have h1 := (A.valuation_le_one_iff _).mpr hinvA
    rw [map_inv₀, inv_le_one₀ (by rw [Valuation.pos_iff]; exact hq0)] at h1
    exact absurd hq (not_lt.mpr h1)
  · exact h

variable (A) in

def e₀ : (coeffSubring A K)[X] →+* LS := eval₂RingHom (constSeries (coeffSubring A K)) jj

theorem e₀_eq_aeval (t : (coeffSubring A K)[X]) :
    e₀ A K t = aeval (jj : LS) (t.map (coeffSubring A K).subtype) := by
  rw [aeval_def, eval₂_map]; rfl

theorem e₀_C (a : coeffSubring A K) : e₀ A K (C a) = algebraMap ℚ̄ LS (a : ℚ̄) := by
  rw [e₀, coe_eval₂RingHom, eval₂_C]; rfl

theorem e₀_X : e₀ A K X = jj := by rw [e₀, coe_eval₂RingHom, eval₂_X]

theorem e₀_mem_jRing (t : (coeffSubring A K)[X]) : e₀ A K t ∈ jRing A K := by
  rw [e₀, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum_def]
  refine Subring.sum_mem _ fun n _ => Subring.mul_mem _ ?_ (Subring.pow_mem _ ?_ _)
  · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  · exact Subring.subset_closure (Or.inr (Set.mem_singleton _))

theorem jRing_le_fieldOver : jRing A K ≤ (fieldOver (1 * q) K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨⟨a, a.2.2⟩, rfl⟩)
  · rw [Set.mem_singleton_iff.mp hx]
    exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem exists_e₀_eq {z : LS} (hz : z ∈ jRing A K) : ∃ t : (coeffSubring A K)[X], e₀ A K t = z := by
  refine Subring.closure_induction (fun x hx => ?_) ⟨0, map_zero _⟩ ⟨1, map_one _⟩
    (fun _ _ _ _ ⟨t, ht⟩ ⟨u, hu⟩ => ⟨t + u, by rw [map_add, ht, hu]⟩)
    (fun _ _ ⟨t, ht⟩ => ⟨-t, by rw [map_neg, ht]⟩)
    (fun _ _ _ _ ⟨t, ht⟩ ⟨u, hu⟩ => ⟨t * u, by rw [map_mul, ht, hu]⟩) hz
  rcases hx with ⟨a, rfl⟩ | hx
  · exact ⟨C a, e₀_C K a⟩
  · exact ⟨X, by rw [e₀_X, Set.mem_singleton_iff.mp hx]⟩

theorem e₀_mem_C (t : (coeffSubring A K)[X]) : e₀ A K t ∈ jIntegralClosure (1 * q) A K := by
  refine ⟨jRing_le_fieldOver K (e₀_mem_jRing K t), ?_⟩
  have : e₀ A K t = algebraMap (jRing A K) LS ⟨e₀ A K t, e₀_mem_jRing K t⟩ := rfl
  rw [this]; exact isIntegral_algebraMap

variable (A) in

def toC : (coeffSubring A K)[X] →+* jIntegralClosure (1 * q) A K :=
  (e₀ A K).codRestrict _ (e₀_mem_C K)

@[scoped simp] theorem coe_toC (t : (coeffSubring A K)[X]) :
    ((toC (q := q) A K t : jIntegralClosure (1 * q) A K) : LS) = e₀ A K t := rfl

theorem e₀_injective : Function.Injective (e₀ A K) := by
  intro t u h
  rw [e₀_eq_aeval, e₀_eq_aeval] at h
  have h0 : aeval (jj : LS) ((t - u).map (coeffSubring A K).subtype) = 0 := by
    rw [Polynomial.map_sub, map_sub, h, sub_self]
  have := (transcendental_iff.mp (ModularCurve.transcendental_jqModC ℚ̄)) _ h0
  rw [Polynomial.map_eq_zero_iff Subtype.val_injective] at this
  exact sub_eq_zero.mp this

theorem toC_injective : Function.Injective (toC (q := q) A K) := fun t u h =>
  e₀_injective K (congrArg (fun x : jIntegralClosure (1 * q) A K => (x : LS)) h)

theorem jqN_mem_C : (jqNModC ℚ̄ (1 * q) : LS) ∈ jIntegralClosure (1 * q) A K := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData (q := q)
  refine ⟨Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_⟩
  let φ : ℤ[X] →+* jRing A K :=
    eval₂RingHom (Int.castRingHom _) ⟨jj, e₀_X (A := A) K ▸ e₀_mem_jRing K X⟩
  refine ⟨data.Φ.map φ, data.monic.map φ, ?_⟩
  rw [eval₂_map]
  have hcomp : (algebraMap (jRing A K) LS).comp φ = evalAtJBar := by
    refine Polynomial.ringHom_ext (fun n => by simp [φ, evalAtJBar]) ?_
    simp only [RingHom.comp_apply, φ, coe_eval₂RingHom, eval₂_X, evalAtJBar]
    rfl
  rw [hcomp]
  exact modularPolynomial_eval₂_bar (1 * q) data

theorem modularRing_le_C : modularRing (1 * q) (coeffSubring A K) ≤ jIntegralClosure (1 * q) A K := by
  rw [modularRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · have h := e₀_mem_C (q := q) K (C a)
    rwa [e₀_C] at h
  · rcases hx with rfl | hx
    · have h := e₀_mem_C (q := q) K (X : (coeffSubring A K)[X])
      rwa [e₀_X] at h
    · rw [Set.mem_singleton_iff.mp hx]; exact jqN_mem_C K

theorem exists_e₀_eq_smul_aeval (D : K[X]) :
    ∃ (d : coeffSubring A K) (D₀ : (coeffSubring A K)[X]), (d : ℚ̄) ≠ 0 ∧
      e₀ A K D₀ = algebraMap ℚ̄ LS (d : ℚ̄) * aeval (jj : LS) D := by
  obtain ⟨d, hd, hdD⟩ := exists_mul_mem_coeffSubring A K (D.support.image D.coeff)
  have hcoeffs : ∀ n, (d : ℚ̄) * (D.coeff n : ℚ̄) ∈ coeffSubring A K := by
    intro n
    by_cases hn : n ∈ D.support
    · exact hdD _ (Finset.mem_image_of_mem _ hn)
    · rw [Polynomial.notMem_support_iff.mp hn]; simp [zero_mem]
  refine ⟨d, ∑ n ∈ D.support, monomial n ⟨_, hcoeffs n⟩, hd, ?_⟩
  rw [map_sum, aeval_def, eval₂_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [e₀, coe_eval₂RingHom, eval₂_monomial, ← mul_assoc]
  congr 1
  show algebraMap ℚ̄ LS ((d : ℚ̄) * ((D.coeff n : K) : ℚ̄)) = algebraMap ℚ̄ LS (d : ℚ̄) * algebraMap ℚ̄ LS ((D.coeff n : K) : ℚ̄)
  rw [map_mul]

theorem ι_aeval_gen (x : LaurentSeries A) (P : A[X]) :
    ι A (aeval x P) = aeval (ι A x) (P.map A.subtype) := by
  rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
  congr 1
  refine RingHom.ext fun a => ?_
  change ι A (algebraMap A (LaurentSeries A) a) = algebraMap ℚ̄ LS (a : ℚ̄)
  rw [algebraMap_laurentSeries_A]
  exact ι_C A a

theorem isInt_aeval (x : LaurentSeries A) (t : (coeffSubring A K)[X]) :
    IsInt A (aeval (ι A x) (t.map (coeffSubring A K).subtype)) := by
  refine ⟨aeval x (t.map (inclA A K)), 1, by rw [map_one]; exact one_ne_zero, ?_⟩
  rw [map_one, mul_one, ι_aeval_gen, Polynomial.map_map]
  rfl

def jBar : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

def jqBar : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb ℚ̄ (qExpand ℚ (1 * q) jq), coeffEmb_mem_laurentBaseChange ℚ̄ (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

theorem coe_jBar : ((jBar (q := q) : modularFunctionFieldBar (1 * q)) : LS) = jj := coeffMap_jqModC _

theorem coe_jqBar : ((jqBar (q := q) : modularFunctionFieldBar (1 * q)) : LS) = jqNModC ℚ̄ (1 * q) := by
  show coeffEmb ℚ̄ (qExpand ℚ (1 * q) jq) = qExpand ℚ̄ (1 * q) (jqModC ℚ̄)
  rw [coeffEmb_qExpand_jq]

theorem frickeInvolutionBar_jBar : frickeInvolutionBar (1 * q) (jBar (q := q)) = jqBar := by
  have hFr : IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
    isFrickeAutFull_frickeInvolutionFull (1 * q) (ModularCurve.exists_isFrickeAutFull_of_neZero (1 * q))
  have h := ModularCurve.frickeInvolutionBar_coeffEmb_qExpand (1 * q) hFr 1 (1 * q) (one_mul _)
  have h1 : (jBar (q := q) : modularFunctionFieldBar (1 * q)) = ⟨coeffEmb ℚ̄ (qExpand ℚ 1 jq),
      coeffEmb_mem_laurentBaseChange ℚ̄ (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩ :=
    Subtype.ext (by show coeffEmb ℚ̄ jq = coeffEmb ℚ̄ (qExpand ℚ 1 jq); rw [qExpand_one_apply])
  rw [h1, h]
  rfl

theorem coe_aeval_jBar (P : ℚ̄[X]) :
    ((aeval (jBar (q := q)) P : modularFunctionFieldBar (1 * q)) : LS) = aeval (jj : LS) P := by
  rw [← coe_jBar (q := q)]
  exact (aeval_algHom_apply (modularFunctionFieldBar (1 * q)).val _ P).symm

theorem coe_frickeInvolutionBar_aeval_jBar (P : ℚ̄[X]) :
    ((frickeInvolutionBar (1 * q) (aeval (jBar (q := q)) P) : modularFunctionFieldBar (1 * q)) : LS)
      = aeval (jqNModC ℚ̄ (1 * q) : LS) P := by
  have hw : frickeInvolutionBar (1 * q) (aeval (jBar (q := q)) P)
      = aeval (frickeInvolutionBar (1 * q) (jBar (q := q))) P := by
    rw [Polynomial.aeval_algEquiv]; rfl
  rw [hw, frickeInvolutionBar_jBar, ← coe_jqBar (q := q)]
  exact (aeval_algHom_apply (modularFunctionFieldBar (1 * q)).val _ P).symm

theorem isIntegral_toC (y : jIntegralClosure (1 * q) A K) :
    letI := (toC (q := q) A K).toAlgebra
    IsIntegral (coeffSubring A K)[X] y := by
  letI := (toC (q := q) A K).toAlgebra
  obtain ⟨p, hpm, hp0⟩ := y.2.2

  let ψ : (coeffSubring A K)[X] →+* jRing A K := (e₀ A K).codRestrict _ (e₀_mem_jRing K)
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨t, ht⟩ := exists_e₀_eq K hz
    exact ⟨t, Subtype.ext ht⟩
  obtain ⟨P, hP, -, hPm⟩ := lifts_and_natDegree_eq_and_monic (map_surjective ψ hψ p) hpm
  refine ⟨P, hPm, Subtype.ext ?_⟩

  show (jIntegralClosure (1 * q) A K).subtype (eval₂ (algebraMap _ _) y P)
    = ((0 : jIntegralClosure (1 * q) A K) : LS)
  rw [hom_eval₂, ZeroMemClass.coe_zero, ← hp0, ← hP, eval₂_map]
  congr 1

theorem main (red : A →+* k)
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∈ 𝔭)
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg : (g : LS) ∈ fieldOver (1 * q) K)
    (h₁ : (g : LS) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂ : ((frickeInvolutionBar (1 * q) g : modularFunctionFieldBar (1 * q)) : LS)
            ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    ∃ r s : ↥(jIntegralClosure (1 * q) A K), s ∉ 𝔭 ∧ (g : LS) * (s : LS) = r := by
  classical
  have hA : A.LiesOverPrime q := liesOverPrime_of_red red
  haveI hdvr : IsDiscreteValuationRing (coeffSubring A K) := isDiscreteValuationRing_coeffSubring K hA
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (coeffSubring A K)

  letI alg : Algebra (coeffSubring A K)[X] (jIntegralClosure (1 * q) A K) := (toC (q := q) A K).toAlgebra
  haveI : FaithfulSMul (coeffSubring A K)[X] (jIntegralClosure (1 * q) A K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (toC_injective K)
  haveI : Algebra.IsIntegral (coeffSubring A K)[X] (jIntegralClosure (1 * q) A K) :=
    ⟨isIntegral_toC K⟩
  have hϖC : Prime (C ϖ : (coeffSubring A K)[X]) := Polynomial.prime_C_iff.mpr hϖ.prime
  haveI : (Ideal.span {(C ϖ : (coeffSubring A K)[X])}).IsPrime :=
    (Ideal.span_singleton_prime hϖC.ne_zero).mpr hϖC

  have hϖA : IsLocalRing.residue A (inclA A K ϖ) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hϖ.not_isUnit
    have hϖ0 : (ϖ : ℚ̄) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
    have hv : ((↑u⁻¹ : A) : ℚ̄) = ((ϖ : ℚ̄))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have := congrArg (fun z : A => (z : ℚ̄)) u.inv_mul
      simpa [hu] using this
    have hvK : ((↑u⁻¹ : A) : ℚ̄) ∈ coeffSubring A K :=
      ⟨(↑u⁻¹ : A).2, by rw [hv]; exact K.inv_mem ϖ.2.2⟩
    refine IsUnit.of_mul_eq_one (M := coeffSubring A K) (a := ϖ) (b := ⟨_, hvK⟩) (Subtype.ext ?_)
    show (ϖ : ℚ̄) * ((↑u⁻¹ : A) : ℚ̄) = 1
    rw [hv, mul_inv_cancel₀ hϖ0]
  have hgen : ∀ a : coeffSubring A K, IsLocalRing.residue A (inclA A K a) = 0 → ϖ ∣ a := by
    intro a ha
    rw [IsLocalRing.residue_eq_zero_iff] at ha
    have hna : a ∈ IsLocalRing.maximalIdeal (coeffSubring A K) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).mp ha (hu.map (inclA A K))
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hna
    exact hna
  have hqϖ : (toC (q := q) A K) (C ϖ) ∈ 𝔭 := by

    have hq0 : ((q : ℕ) : coeffSubring A K) ≠ 0 := by
      intro h; apply (Fact.out : q.Prime).ne_zero
      have := congrArg (fun z : coeffSubring A K => (z : ℚ̄)) h
      simpa using this
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hq0 hϖ

    have hmem : (toC (q := q) A K) (C (ϖ ^ n)) ∈ 𝔭 := by
      have hq' : (toC (q := q) A K) (C ((q : ℕ) : coeffSubring A K)) = (q : jIntegralClosure (1 * q) A K) :=
        Subtype.ext (by rw [coe_toC, e₀_C]; simp)
      rw [← hu, C_mul, map_mul, hq']
      exact 𝔭.mul_mem_right _ hq
    rw [C_pow, map_pow] at hmem
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n hmem

  have hunder : 𝔭.under (coeffSubring A K)[X] = Ideal.span {C ϖ} := by
    refine under_eq_of_height_eq_one 𝔭 h𝔭 (Ideal.span {C ϖ}) ?_ ?_
    · rw [Ne, Ideal.span_singleton_eq_bot]; exact hϖC.ne_zero
    · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hqϖ

  haveI : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩
  obtain ⟨data, hKr⟩ := ModularCurve.exists_kroneckerCongruence_of_prime (1 * q)
  obtain ⟨D, hD0, hmem⟩ := exists_presentation_K (1 * q) K data hg
  obtain ⟨d, hd, hb⟩ := exists_mul_mem_modularRing_of_mem_adjoin (1 * q) A K hmem
  obtain ⟨d', D₀, hd', hD₀⟩ := exists_e₀_eq_smul_aeval (A := A) K D
  set t : (coeffSubring A K)[X] := C d * D₀ with ht_def
  have het : e₀ A K t = algebraMap ℚ̄ LS (d : ℚ̄) * (algebraMap ℚ̄ LS (d' : ℚ̄) * aeval (jj : LS) D) := by
    rw [ht_def, map_mul, e₀_C, hD₀]
  have hbt : (g : LS) * e₀ A K t ∈ CharPReduction.modularRing (1 * q) (coeffSubring A K) := by
    have : (g : LS) * e₀ A K t
        = algebraMap ℚ̄ LS (d' : ℚ̄) * (algebraMap ℚ̄ LS (d : ℚ̄) * ((g : LS) * aeval (jj : LS) D)) := by
      rw [het]; ring
    rw [this]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨d', rfl⟩)) hb
  have ht0 : t ≠ 0 := by
    intro h0
    have : e₀ A K t = 0 := by rw [h0, map_zero]
    rw [het] at this
    exact (mul_ne_zero ((_root_.map_ne_zero _).mpr hd) (mul_ne_zero ((_root_.map_ne_zero _).mpr hd') hD0)) this

  obtain ⟨m, t₀, hndvd, htt⟩ := WfDvdMonoid.max_power_factor ht0 hϖC.irreducible

  have hsplit : (g : LS) * e₀ A K t = ((g : LS) * e₀ A K t₀) * algebraMap ℚ̄ LS ((ϖ : ℚ̄) ^ m) := by
    rw [htt, map_mul, map_pow, e₀_C, map_pow]; ring

  have hIg : IsInt A (g : LS) :=
    isInt_of_mem_modularLocalized' A (1 * q) red (redBarOf (q := q) red) (redBarOf_residue red) h₁
  have hIwg : IsInt A ((frickeInvolutionBar (1 * q) g : modularFunctionFieldBar (1 * q)) : LS) :=
    isInt_of_mem_modularLocalized' A (1 * q) red (redBarOf (q := q) red) (redBarOf_residue red) h₂
  let P₀ : ℚ̄[X] := t₀.map (coeffSubring A K).subtype
  let hB : modularFunctionFieldBar (1 * q) := g * aeval (jBar (q := q)) P₀
  have hcoe : (hB : LS) = (g : LS) * e₀ A K t₀ := by
    show (g : LS) * ((aeval (jBar (q := q)) P₀ : modularFunctionFieldBar (1 * q)) : LS) = _
    rw [coe_aeval_jBar, e₀_eq_aeval]
  have hI1 : IsInt A (hB : LS) := by
    rw [hcoe, e₀_eq_aeval, ← coeffMap_jqModC A.subtype]
    exact hIg.mul (isInt_aeval K (jqModC A) t₀)
  have hI2 : IsInt A ((frickeInvolutionBar (1 * q) hB : modularFunctionFieldBar (1 * q)) : LS) := by
    show IsInt A ((frickeInvolutionBar (1 * q) (g * aeval (jBar (q := q)) P₀) : modularFunctionFieldBar (1 * q)) : LS)
    rw [map_mul, IntermediateField.coe_mul, coe_frickeInvolutionBar_aeval_jBar, ← coeffMap_jqNModC A.subtype]
    exact hIwg.mul (isInt_aeval K (jqNModC A (1 * q)) t₀)

  have hle : coeffSubring A K ≤ A.toSubring := inf_le_left
  haveI : CharP (IsLocalRing.ResidueField A) (1 * q) :=
    charP_residueField_of_liesOverPrime A (Fact.out : (1 * q).Prime) (by rw [one_mul]; exact hA)
  have hσj : frickeInvolutionBar (1 * q) (jF (1 * q)) = jNF A (1 * q) := frickeInvolutionBar_jF A (1 * q)
  have hσjN : frickeInvolutionBar (1 * q) (jNF A (1 * q)) = jF (1 * q) := by
    rw [← hσj]; exact ModularCurve.frickeInvolutionBar_frickeInvolutionBar _ _
  obtain ⟨P, hP⟩ := (mem_modularRing_iff_exists_bF A (1 * q) (coeffSubring A K) hle _).mp hbt
  have hPx : bF A (1 * q) (P.map (mapRingHom (Subring.inclusion hle)))
      = algebraMap ℚ̄ (modularFunctionFieldBar (1 * q)) ((ϖ : ℚ̄) ^ m) * hB := by
    apply Subtype.ext
    rw [← hP, hsplit, IntermediateField.coe_mul, coe_algebraMap, hcoe, mul_comm]
  obtain ⟨Q, hQ⟩ := sat_pow A (1 * q) data hKr (frickeInvolutionBar (1 * q)) hσj hσjN
    (coeffSubring A K) hle (ϖ₀ := ϖ) (fun h0 => hϖ.ne_zero (Subtype.ext h0)) hϖA
    (fun a ha => hgen a ha) m P hB ((mem_gaussRing_iff A (1 * q) _).mpr hI1)
    ((mem_gaussRing_iff A (1 * q) _).mpr hI2) hPx
  have hsat : (hB : LS) ∈ CharPReduction.modularRing (1 * q) (coeffSubring A K) :=
    (mem_modularRing_iff_exists (1 * q) (coeffSubring A K) _).mpr ⟨Q, by rw [hQ, coe_bF_map]⟩

  refine ⟨⟨(hB : LS), modularRing_le_C K hsat⟩, toC (q := q) A K t₀, ?_, ?_⟩
  · intro hs
    have : t₀ ∈ 𝔭.under (coeffSubring A K)[X] := hs
    rw [hunder, Ideal.mem_span_singleton] at this
    exact hndvd this
  · rw [coe_toC, ← hcoe]

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

end Ws25.GaussE
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25 P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE"
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25"

p2m_open "ModularCurve~dedekindPsi_prime~nonempty_modularPolynomialData" in open AlgebraicCurve IsLocalRing ModularCurve.NodeLocalized in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∈ 𝔭)
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K)
    (h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂ : ((frickeInvolutionBar (1 * q) g : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    ∃ r s : ↥(jIntegralClosure (1 * q) A K), s ∉ 𝔭 ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) = r :=
  Ws25.GaussE.main K red 𝔭 h𝔭 hq g hg h₁ h₂

end
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE.AlgebraicCurve.RegularProlongation P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25 P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem.Ws25.GaussE"

end S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem
end P2MW
export P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem (solution)
