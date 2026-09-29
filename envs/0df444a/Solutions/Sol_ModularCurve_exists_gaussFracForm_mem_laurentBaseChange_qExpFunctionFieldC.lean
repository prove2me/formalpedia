-- Prove2me | solution 1 for ModularCurve.exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/49846d29-278b-5967-9459-7ad6beb83ccc

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC.ModularCurve IntermediateField"
open scoped MatrixGroups Classical

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC algebraMap_apply_eq_single coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC"
namespace GaussFracForm
p2m_open "ModularCurve"

section Coeff

variable {L : Type*} [Field L] (A : ValuationSubring L)

private abbrev ι : LaurentSeries A →+* LaurentSeries L := coeffMap A.subtype

private abbrev ϖ : LaurentSeries A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
  coeffMap (IsLocalRing.residue A)

end Coeff

section Scaling

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem exists_coeffMap_subtype_eq (x : LaurentSeries L) (hx : ∀ n, x.coeff n ∈ A) :
    ∃ y : LaurentSeries A, ι A y = x := by
  refine ⟨⟨fun n => ⟨x.coeff n, hx n⟩, ?_⟩, ?_⟩
  · convert x.isPWO_support' using 1
    ext n
    simp only [Function.mem_support, ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero]
  · ext n
    rfl

private theorem valuation_le_of_mem_span (T : Finset L) (c : L) (hc : ∀ t ∈ T, A.valuation t ≤ A.valuation c)
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

private theorem exists_primitive_scaling {x : LaurentSeries L} (hx : x ≠ 0) (M : Submodule ℤ L) (hM : M.FG)
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

private theorem exists_primitive_form {x : LaurentSeries L} (hx : x ≠ 0) (M : Submodule ℤ L) (hM : M.FG)
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

variable (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ))

private def G : Set (LaurentSeries L) :=
  {g | ∃ (z : LaurentSeries ℚ) (m : ℤ) (P : PowerSeries ℤ), z ∈ qExpFunctionFieldC ℚ Γ ∧
    z = HahnSeries.single m 1 * intSeriesC ℚ P ∧ g = coeffEmb L z}

private theorem G_subset : G L Γ ⊆ (laurentBaseChange L (qExpFunctionFieldC ℚ Γ) : Set (LaurentSeries L)) := by
  rintro _ ⟨z, m, P, hz, -, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L hz

private theorem exists_int_coeff_of_mem_G {g : LaurentSeries L} (hg : g ∈ G L Γ) (n : ℤ) :
    ∃ k : ℤ, g.coeff n = (k : L) := by
  obtain ⟨z, m, P, -, rfl, rfl⟩ := hg
  rw [coeffEmb_coeff]
  have : n = (n - m) + m := by ring
  rw [this, HahnSeries.coeff_single_mul_add, one_mul]
  rcases le_or_gt 0 (n - m) with h | h
  · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le h
    rw [hd, intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
    exact ⟨PowerSeries.coeff d P, by simp⟩
  · refine ⟨0, ?_⟩
    rw [intSeriesC, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
    · simp
    · simp only [Set.mem_range, not_exists]
      intro d hd
      have : (0 : ℤ) ≤ n - m := by rw [← hd]; exact Int.natCast_nonneg _
      omega

include Γ in
private theorem laurentBaseChange_le_adjoin_G (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods) :
    laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ≤ adjoin L (G L Γ) := by
  change adjoin L _ ≤ adjoin L (G L Γ)
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ) := hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ)).map (coeffEmb L) := ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨r, hr | hr, rfl⟩
  · obtain ⟨c, rfl⟩ := hr
    rw [algebraMap_apply_eq_single]
    change coeffMap (algebraMap ℚ L) (HahnSeries.single 0 c) ∈ adjoin L (G L Γ)
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (adjoin L (G L Γ)).algebraMap_mem _
  ·
    obtain ⟨a, b, m, n, P, Q, ha, hb, haP, hbQ, hb0, hrab⟩ :=
      ModularCurve.exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC ℚ Γ hΓ r hr
    have haG : coeffEmb L a ∈ G L Γ := ⟨a, m, P, ha, haP, rfl⟩
    have hbG : coeffEmb L b ∈ G L Γ := ⟨b, n, Q, hb, hbQ, rfl⟩
    have hb0' : coeffEmb L b ≠ 0 := by
      intro h; apply hb0
      have hinj : Function.Injective (coeffEmb L) := (coeffEmb L).injective
      exact hinj (by rw [h, map_zero])
    have : coeffEmb L r = coeffEmb L a / coeffEmb L b := by
      rw [eq_div_iff hb0', ← map_mul, hrab]
    rw [this]
    exact div_mem (subset_adjoin L _ haG) (subset_adjoin L _ hbG)

private theorem exists_fg_coeff_mem {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (G L Γ)) :
    ∃ M : Submodule ℤ L, M.FG ∧ ∀ n, x.coeff n ∈ M := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      refine ⟨Submodule.span ℤ {(1 : L)}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      obtain ⟨k, hk⟩ := exists_int_coeff_of_mem_G L Γ hx n
      rw [hk, ← zsmul_one]
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

end Generators

end ModularCurve.GaussFracForm

open ModularCurve.GaussFracForm in

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ Γ))) (hf : f ≠ 0) :
    ∃ (c : L) (x y : LaurentSeries ↥A), c ≠ 0 ∧
      coeffMap (IsLocalRing.residue ↥A) x ≠ 0 ∧ coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      coeffMap A.subtype x ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ∧
      coeffMap A.subtype y ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ∧
      (f : LaurentSeries L) * coeffMap A.subtype y = algebraMap L (LaurentSeries L) c * coeffMap A.subtype x := by
  have hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    refine ⟨ModularGroup.T, hT, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]
  have hFG : laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ≤ adjoin L (G L Γ) := laurentBaseChange_le_adjoin_G L Γ hΓ
  have hGF : Algebra.adjoin L (G L Γ) ≤ (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)).toSubalgebra := by
    rw [Algebra.adjoin_le_iff]; exact G_subset L Γ

  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_adjoin_iff_div (F := L)).mp (hFG f.2)
  have hf0 : (f : LaurentSeries L) ≠ 0 := fun h => hf (Subtype.ext h)
  have hr0 : r ≠ 0 := by rintro rfl; exact hf0 (by rw [hrs, zero_div])
  have hs0 : s ≠ 0 := by rintro rfl; exact hf0 (by rw [hrs, div_zero])
  obtain ⟨Mr, hMr, hrM⟩ := exists_fg_coeff_mem L Γ hr
  obtain ⟨Ms, hMs, hsM⟩ := exists_fg_coeff_mem L Γ hs
  obtain ⟨cr, hcr0, r₀, hr₀, hrr₀⟩ := exists_primitive_form A hr0 Mr hMr hrM
  obtain ⟨cs, hcs0, s₀, hs₀, hss₀⟩ := exists_primitive_form A hs0 Ms hMs hsM

  have hιr₀ : ι A r₀ = algebraMap L (LaurentSeries L) cr⁻¹ * r := by
    rw [hrr₀, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcr0, map_one, one_mul]
  have hιs₀ : ι A s₀ = algebraMap L (LaurentSeries L) cs⁻¹ * s := by
    rw [hss₀, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcs0, map_one, one_mul]
  refine ⟨cr / cs, r₀, s₀, div_ne_zero hcr0 hcs0, hr₀, hs₀, ?_, ?_, ?_⟩
  · rw [show coeffMap A.subtype r₀ = ι A r₀ from rfl, hιr₀]
    exact (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)).mul_mem ((laurentBaseChange L (qExpFunctionFieldC ℚ Γ)).algebraMap_mem _) (hGF hr)
  · rw [show coeffMap A.subtype s₀ = ι A s₀ from rfl, hιs₀]
    exact (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)).mul_mem ((laurentBaseChange L (qExpFunctionFieldC ℚ Γ)).algebraMap_mem _) (hGF hs)
  · show (f : LaurentSeries L) * ι A s₀ = algebraMap L (LaurentSeries L) (cr / cs) * ι A r₀
    rw [hrs, hιr₀, hιs₀, mul_comm (algebraMap L (LaurentSeries L) cs⁻¹) s, ← mul_assoc, div_mul_cancel₀ _ hs0,
      ← mul_assoc, ← map_mul, show cr / cs * cr⁻¹ = cs⁻¹ by field_simp, mul_comm]

end

end S_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC (solution)
