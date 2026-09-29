-- Prove2me | solution 1 for ModularCurve.exists_regularProlongation_modularFunctionFieldBar_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6601a9b2-594d-5949-897d-d85f07f9f42d

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self
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

p2m_alias "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.AlgebraicCurve.RegularProlongation.mapResidue" "AlgebraicCurve.RegularProlongation.mapResidue"
@[scoped simp] private theorem _root_.AlgebraicCurve.RegularProlongation.mapResidue_integers (R : RegularProlongation A F Fbar)
    (e : Fbar ≃ₐ[IsLocalRing.ResidueField A] Fbar') : (R.mapResidue A e).integers = R.integers := rfl

p2m_alias "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.AlgebraicCurve.RegularProlongation.mapResidue_integers" "AlgebraicCurve.RegularProlongation.mapResidue_integers"
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25.GaussE.AlgebraicCurve.RegularProlongation"
private theorem _root_.AlgebraicCurve.RegularProlongation.mapResidue_residue (R : RegularProlongation A F Fbar)
    (e : Fbar ≃ₐ[IsLocalRing.ResidueField A] Fbar') (x : R.integers) :
    (R.mapResidue A e).residue x = e (R.residue x) := rfl

p2m_alias "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.AlgebraicCurve.RegularProlongation.mapResidue_residue" "AlgebraicCurve.RegularProlongation.mapResidue_residue"
end MapResidue
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

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

theorem gaussComap_frickeInvolutionBar_ne (hp : N.Prime) (hA : A.LiesOverPrime N) :
    gaussComap A N (frickeInvolutionBar N) ≠ gaussRing A N := by
  haveI : Fact N.Prime := ⟨hp⟩
  haveI : CharP kk N := charP_residueField_of_liesOverPrime A hp hA
  have hσj : frickeInvolutionBar N (jF N) = jNF A N := frickeInvolutionBar_jF A N
  have hσjN : frickeInvolutionBar N (jNF A N) = jF N := by
    rw [← hσj]; exact frickeInvolutionBar_frickeInvolutionBar N _

  set g : gaussRing A N :=
    (⟨jNF A N, jNF_mem_gaussRing A N⟩ : gaussRing A N) - ⟨jF N, jF_mem_gaussRing A N⟩ ^ N with hg
  set g' : gaussRing A N :=
    (⟨jF N, jF_mem_gaussRing A N⟩ : gaussRing A N) - ⟨jNF A N, jNF_mem_gaussRing A N⟩ ^ N with hg'
  have hcoe : (g : FF) = jNF A N - jF N ^ N := by simp [hg]
  have hcoe' : (g' : FF) = jF N - jNF A N ^ N := by simp [hg']

  have hres : resHom A N g = 0 := by
    rw [hg, map_sub, map_pow, resHom_jNF, resHom_jF,
      show qExpand kk N (jqModC kk) = jqNModC kk N from rfl,
      frobenius_identity_geom_unconditional kk, sub_self]
  have hres' : resHom A N g' ≠ 0 := by
    rw [hg', map_sub, map_pow, resHom_jNF, resHom_jF,
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

  have hg_non : (g : FF) ∈ (gaussRing A N).nonunits :=
    ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
      ⟨g.2, by simpa using (resHom_eq_zero_iff A N g).mp hres⟩
  have hg'_non : (g' : FF) ∉ (gaussRing A N).nonunits := fun h => by
    obtain ⟨hm, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
    have hmax' : g' ∈ IsLocalRing.maximalIdeal (gaussRing A N) := by simpa using hmax
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax' (isUnit_of_resHom_ne_zero A N hres')

  have hσg : frickeInvolutionBar N (g : FF) = (g' : FF) := by
    rw [hcoe, hcoe', map_sub, map_pow, hσj, hσjN]

  intro heq
  have hmem : (g : FF) ∈ (gaussComap A N (frickeInvolutionBar N)).nonunits := by
    rw [heq]; exact hg_non
  rw [show gaussComap A N (frickeInvolutionBar N)
      = (gaussRing A N).comap ((frickeInvolutionBar N : FF ≃ₐ[AlgebraicClosure ℚ] FF) : FF →+* FF)
      from rfl, mem_nonunits_comap_iff'] at hmem
  exact hg'_non (by rw [← hσg]; exact hmem)

end Fricke
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

section Modular

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))

theorem exists_regularProlongation_self (hp : N.Prime) (hA : A.LiesOverPrime N) :
    ∃ R : AlgebraicCurve.RegularProlongation A (modularFunctionFieldBar N)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      (∀ f : modularFunctionFieldBar N, f ∈ R.integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y := by
  obtain ⟨R, hR, h⟩ := exists_regularProlongation_of_sigma A N (frickeInvolutionBar N)
    (gaussComap_frickeInvolutionBar_ne A N hp hA) (Nat.cast_ne_zero.mpr hp.ne_zero) hp
    (frickeInvolutionBar_jF A N)
  refine ⟨R, fun f => ?_, h⟩
  rw [hR]
  exact mem_gaussRing_iff A N f

end Modular
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25.GaussE.AlgebraicCurve.RegularProlongation"

end Ws25.GaussE
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25.GaussE.AlgebraicCurve.RegularProlongation P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25 P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25.GaussE"
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25.GaussE.AlgebraicCurve.RegularProlongation P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25"

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    (hN : N.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime N) :
    ∃ R : AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar N)
        (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      (∀ f : ModularCurve.modularFunctionFieldBar N, f ∈ R.integers ↔
        ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A.subtype y
            = ModularCurve.coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar N),
        ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ : ModularCurve.modularFunctionFieldBar N) ∈
            R.integers,
          ((R.residue ⟨_, hint⟩ :
              ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y :=
  Ws25.GaussE.exists_regularProlongation_self N A hN hA

end
p2m_reactivate "P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25.GaussE.AlgebraicCurve.RegularProlongation P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25 P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self.Ws25.GaussE"

end S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self
end P2MW
export P2MW.S_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self (solution)
