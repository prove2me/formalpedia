-- Prove2me | solution 1 for ModularCurve.mem_intFormRatiosC_of_coe_eq_intSeriesC_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/96b4b310-7131-5033-93e1-9b404b4409d7

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_intFormRatiosC_of_coe_eq_intSeriesC_div

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_mem_intFormRatiosC_of_coe_eq_intSeriesC_div.ModularCurve UpperHalfPlane HahnSeries"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "IsIntegralQExp isIntegralQExp_one isIntegralQExp_zero intSeriesC intSeriesC_mul intFormRatiosC one_mem_intFormRatiosC qExpFunctionFieldC coeffMap coeffMap_single coeffMap_intSeriesC"
p2m_open "ModularCurve"

namespace LDRatio

variable (K : Type*) [Field K] {Γ : Subgroup SL(2, ℤ)}
variable (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)

local notation "Γ'" => ((Γ : Subgroup (GL (Fin 2) ℝ)))

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) : (1 : ℝ) ∈ (Γ').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

include hΓ in
theorem analytic {k : ℤ} (f : ModularForm Γ' k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ

include hΓ in
theorem isIntegralQExp_mul {k₁ k₂ : ℤ} (f : ModularForm Γ' k₁) (g : ModularForm Γ' k₂)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (⇑(f.mul g)) (pf * pg) := by
  unfold IsIntegralQExp at *
  rw [map_mul, hf, hg, ModularForm.qExpansion_mul one_pos hΓ f g]

include hΓ in
theorem isIntegralQExp_add {k : ℤ} (f g : ModularForm Γ' k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (⇑(f + g)) (pf + pg) := by
  unfold IsIntegralQExp at *
  rw [map_add, hf, hg, ModularForm.coe_add, ModularForm.qExpansion_add one_pos hΓ f g]

include hΓ in
theorem isIntegralQExp_intCast_smul {k : ℤ} (a : ℤ) (f : ModularForm Γ' k) {pf : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) : IsIntegralQExp (⇑(((a : ℂ)) • f)) (PowerSeries.C a * pf) := by
  unfold IsIntegralQExp at *
  rw [map_mul, hf, PowerSeries.map_C, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos hΓ (a : ℂ) f, eq_intCast, ← PowerSeries.smul_eq_C_mul]

theorem intSeriesC_add (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

theorem intSeriesC_C (a : ℤ) : intSeriesC K (PowerSeries.C a) = HahnSeries.C (a : K) := by
  simp [intSeriesC]

include hΓ in

def ratios : Subfield (LaurentSeries K) where
  carrier := intFormRatiosC K Γ
  mul_mem' := by
    rintro _ _ ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, h₁, rfl⟩ ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, h₂, rfl⟩
    refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, isIntegralQExp_mul hΓ f₁ f₂ hf₁ hf₂,
      isIntegralQExp_mul hΓ g₁ g₂ hg₁ hg₂, ?_, ?_⟩
    · rw [intSeriesC_mul]; exact mul_ne_zero h₁ h₂
    · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]
  one_mem' := one_mem_intFormRatiosC K Γ
  add_mem' := by
    rintro _ _ ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, h₁, rfl⟩ ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, h₂, rfl⟩
    refine ⟨k₁ + k₂, f₁.mul g₂ + g₁.mul f₂, g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂,
      isIntegralQExp_add hΓ _ _ (isIntegralQExp_mul hΓ f₁ g₂ hf₁ hg₂)
        (isIntegralQExp_mul hΓ g₁ f₂ hg₁ hf₂),
      isIntegralQExp_mul hΓ g₁ g₂ hg₁ hg₂, ?_, ?_⟩
    · rw [intSeriesC_mul]; exact mul_ne_zero h₁ h₂
    · rw [intSeriesC_add, intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ h₁ h₂]
  zero_mem' := by
    refine ⟨0, 0, 1, 0, 1, ?_, ?_, by simp, by simp⟩
    · show IsIntegralQExp (⇑(0 : ModularForm Γ' 0)) 0
      rw [ModularForm.coe_zero]; exact isIntegralQExp_zero
    · show IsIntegralQExp (⇑(1 : ModularForm Γ' 0)) 1
      rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one
  neg_mem' := by
    rintro _ ⟨k, f, g, pf, pg, hf, hg, h, rfl⟩
    refine ⟨k, (((-1 : ℤ) : ℂ)) • f, g, PowerSeries.C (-1 : ℤ) * pf, pg,
      isIntegralQExp_intCast_smul hΓ (-1) f hf, hg, h, ?_⟩
    rw [intSeriesC_mul, intSeriesC_C]
    push_cast
    simp [neg_div]
  inv_mem' := by
    rintro _ ⟨k, f, g, pf, pg, hf, hg, h, rfl⟩
    by_cases hpf : intSeriesC K pf = 0
    · rw [hpf, zero_div, inv_zero]
      refine ⟨0, 0, 1, 0, 1, ?_, ?_, by simp, by simp⟩
      · show IsIntegralQExp (⇑(0 : ModularForm Γ' 0)) 0
        rw [ModularForm.coe_zero]; exact isIntegralQExp_zero
      · show IsIntegralQExp (⇑(1 : ModularForm Γ' 0)) 1
        rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one
    · exact ⟨k, g, f, pg, pf, hg, hf, hpf, (inv_div _ _)⟩

theorem mem_ratios_iff {x : LaurentSeries K} : x ∈ ratios K hΓ ↔ x ∈ intFormRatiosC K Γ := Iff.rfl

theorem coe_ratios : (ratios K hΓ : Set (LaurentSeries K)) = intFormRatiosC K Γ := rfl

theorem intCast_div_intCast_smul_mem (m n : ℤ) {x : LaurentSeries K} (hx : x ∈ ratios K hΓ) :
    ((m : K) / (n : K)) • x ∈ ratios K hΓ := by
  by_cases hn : (n : K) = 0
  · rw [hn, div_zero, zero_smul]; exact zero_mem _
  obtain ⟨k, f, g, pf, pg, hf, hg, h, rfl⟩ := hx
  refine ⟨k, ((m : ℂ)) • f, ((n : ℂ)) • g, PowerSeries.C m * pf, PowerSeries.C n * pg,
    isIntegralQExp_intCast_smul hΓ m f hf, isIntegralQExp_intCast_smul hΓ n g hg, ?_, ?_⟩
  · rw [intSeriesC_mul, intSeriesC_C]
    exact mul_ne_zero (HahnSeries.C_ne_zero hn) h
  · rw [intSeriesC_mul, intSeriesC_C, intSeriesC_mul, intSeriesC_C, ← HahnSeries.C_mul_eq_smul,
      map_div₀, div_mul_div_comm]

def primeField : Subfield K := Subfield.closure (Set.range ((↑) : ℤ → K))

theorem closure_range_intCast_eq : Subring.closure (Set.range ((↑) : ℤ → K)) = (Int.castRingHom K).range := by
  apply le_antisymm
  · exact Subring.closure_le.mpr (by rintro _ ⟨m, rfl⟩; exact ⟨m, rfl⟩)
  · rintro _ ⟨m, rfl⟩; exact Subring.subset_closure ⟨m, rfl⟩

theorem exists_eq_intCast_div_intCast {c : K} (hc : c ∈ primeField K) :
    ∃ m n : ℤ, c = (m : K) / (n : K) := by
  rw [primeField, Subfield.mem_closure_iff] at hc
  obtain ⟨y, hy, z, hz, rfl⟩ := hc
  rw [closure_range_intCast_eq] at hy hz
  obtain ⟨m, rfl⟩ := hy
  obtain ⟨n, rfl⟩ := hz
  exact ⟨m, n, rfl⟩

theorem coe_smul_mem_ratios (c : primeField K) {x : LaurentSeries K} (hx : x ∈ ratios K hΓ) :
    (c : K) • x ∈ ratios K hΓ := by
  obtain ⟨m, n, hmn⟩ := exists_eq_intCast_div_intCast K c.2
  rw [hmn]
  exact intCast_div_intCast_smul_mem K hΓ m n hx

def embQ : LaurentSeries (primeField K) →+* LaurentSeries K := coeffMap (primeField K).subtype

theorem intSeriesC_mem_fieldRange (p : PowerSeries ℤ) : intSeriesC K p ∈ (embQ K).fieldRange :=
  ⟨intSeriesC (primeField K) p, coeffMap_intSeriesC _ p⟩

theorem ratios_le_fieldRange : ratios K hΓ ≤ (embQ K).fieldRange := by
  rintro _ ⟨k, f, g, pf, pg, -, -, -, rfl⟩
  exact div_mem (intSeriesC_mem_fieldRange K pf) (intSeriesC_mem_fieldRange K pg)

theorem coe_smul_mem_fieldRange (c : primeField K) {x : LaurentSeries K} (hx : x ∈ (embQ K).fieldRange) :
    (c : K) • x ∈ (embQ K).fieldRange := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨HahnSeries.C c * y, ?_⟩
  rw [map_mul, ← HahnSeries.C_mul_eq_smul]
  congr 1
  show coeffMap _ (HahnSeries.single 0 c) = HahnSeries.single 0 (c : K)
  rw [coeffMap_single]
  rfl

theorem eq_zero_of_sum_smul_eq_zero {ι : Type*} (s : Finset ι) (e : ι → K)
    (he : LinearIndependent (primeField K) e) (g : ι → LaurentSeries (primeField K))
    (h : ∑ i ∈ s, e i • embQ K (g i) = 0) : ∀ i ∈ s, g i = 0 := by
  intro i hi
  ext n
  have hn := congrArg (fun f : LaurentSeries K => f.coeff n) h
  simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, HahnSeries.coeff_zero, smul_eq_mul] at hn
  have hn' : ∑ j ∈ s, ((g j).coeff n) • e j = 0 := by
    rw [← hn]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, mul_comm]
    rfl
  have := linearIndependent_iff'.mp he s (fun j => (g j).coeff n) hn' i hi
  simpa using this

theorem mul_mem_span {y z : LaurentSeries K}
    (hy : y ∈ Submodule.span K (ratios K hΓ : Set (LaurentSeries K)))
    (hz : z ∈ Submodule.span K (ratios K hΓ : Set (LaurentSeries K))) :
    y * z ∈ Submodule.span K (ratios K hΓ : Set (LaurentSeries K)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    induction hz using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span (mul_mem hy hz)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add z₁ z₂ _ _ h₁ h₂ => rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
    | smul a z _ h =>
      rw [← HahnSeries.C_mul_eq_smul, mul_left_comm, HahnSeries.C_mul_eq_smul]
      exact Submodule.smul_mem _ a h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  | smul a y _ h =>
    rw [← HahnSeries.C_mul_eq_smul, mul_assoc, HahnSeries.C_mul_eq_smul]
    exact Submodule.smul_mem _ a h

theorem mem_span_of_mem_closure {y : LaurentSeries K}
    (hy : y ∈ Subring.closure
      (Set.range (algebraMap K (LaurentSeries K)) ∪ (ratios K hΓ : Set (LaurentSeries K)))) :
    y ∈ Submodule.span K (ratios K hΓ : Set (LaurentSeries K)) := by
  induction hy using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨c, rfl⟩ | hy
    · have e : algebraMap K (LaurentSeries K) c = c • (1 : LaurentSeries K) := by
        rw [show algebraMap K (LaurentSeries K) c = HahnSeries.C c from by
              show HahnSeries.ofPowerSeries ℤ K (algebraMap K (PowerSeries K) c) = _; simp,
          ← mul_one (HahnSeries.C c), HahnSeries.C_mul_eq_smul]
      rw [e]
      exact Submodule.smul_mem _ c (Submodule.subset_span (ratios K hΓ).one_mem)
    · exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | one => exact Submodule.subset_span (ratios K hΓ).one_mem
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | neg y _ hy => exact Submodule.neg_mem _ hy
  | mul y z _ _ hy hz => exact mul_mem_span K hΓ hy hz

theorem exists_common_expansion {y z : LaurentSeries K}
    (hy : y ∈ Submodule.span K (ratios K hΓ : Set (LaurentSeries K)))
    (hz : z ∈ Submodule.span K (ratios K hΓ : Set (LaurentSeries K))) :
    ∃ (B : Finset (Module.Basis.ofVectorSpaceIndex (primeField K) K))
      (Y Z : Module.Basis.ofVectorSpaceIndex (primeField K) K → LaurentSeries K),
      (∀ b, Y b ∈ ratios K hΓ) ∧ (∀ b, Z b ∈ ratios K hΓ) ∧
      y = ∑ b ∈ B, (Module.Basis.ofVectorSpace (primeField K) K b) • Y b ∧
      z = ∑ b ∈ B, (Module.Basis.ofVectorSpace (primeField K) K b) • Z b := by
  classical
  set E := Module.Basis.ofVectorSpace (primeField K) K with hE
  obtain ⟨cy, ty, hty, hsy, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hy
  obtain ⟨cz, tz, htz, hsz, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hz

  set u : Finset (LaurentSeries K) := ty ∪ tz with hu
  set B : Finset (Module.Basis.ofVectorSpaceIndex (primeField K) K) :=
    u.biUnion (fun v => (E.repr (cy v)).support ∪ (E.repr (cz v)).support) with hB
  have hsum : ∀ (c : LaurentSeries K → K) (t : Finset (LaurentSeries K)), Function.support c ⊆ t → t ⊆ u →
      (∀ v ∈ u, (E.repr (c v)).support ⊆ B) →
      ∑ v ∈ t, c v • v = ∑ b ∈ B, E b • ∑ v ∈ u, ((E.repr (c v) b : primeField K) : K) • v := by
    intro c t hct htu hsupp
    have h1 : ∑ v ∈ t, c v • v = ∑ v ∈ u, c v • v := by
      refine Finset.sum_subset htu fun v _ hvt => ?_
      rw [Function.notMem_support.mp (fun h => hvt (hct h)), zero_smul]
    rw [h1]
    have h2 : ∀ v ∈ u, c v = ∑ b ∈ B, ((E.repr (c v) b : primeField K) : K) * E b := by
      intro v hv
      conv_lhs => rw [← E.linearCombination_repr (c v), Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset (E.repr (c v)) (hsupp v hv) (fun i a => a • E i)
          (fun b _ => zero_smul _ _)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subfield.smul_def, smul_eq_mul]
    calc ∑ v ∈ u, c v • v = ∑ v ∈ u, ∑ b ∈ B, (((E.repr (c v) b : primeField K) : K) * E b) • v := by
          refine Finset.sum_congr rfl fun v hv => ?_
          conv_lhs => rw [h2 v hv]
          rw [Finset.sum_smul]
      _ = ∑ b ∈ B, ∑ v ∈ u, (((E.repr (c v) b : primeField K) : K) * E b) • v := Finset.sum_comm
      _ = ∑ b ∈ B, E b • ∑ v ∈ u, ((E.repr (c v) b : primeField K) : K) • v := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [mul_comm, mul_smul]
  refine ⟨B, fun b => ∑ v ∈ u, ((E.repr (cy v) b : primeField K) : K) • v,
    fun b => ∑ v ∈ u, ((E.repr (cz v) b : primeField K) : K) • v, ?_, ?_, ?_, ?_⟩
  · intro b
    refine Subfield.sum_mem _ fun v hv => coe_smul_mem_ratios K hΓ _ ?_
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hty hv
    · exact htz hv
  · intro b
    refine Subfield.sum_mem _ fun v hv => coe_smul_mem_ratios K hΓ _ ?_
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hty hv
    · exact htz hv
  · refine hsum cy ty hsy Finset.subset_union_left fun v hv => ?_
    exact (Finset.subset_union_left).trans
      (Finset.subset_biUnion_of_mem (fun v => (E.repr (cy v)).support ∪ (E.repr (cz v)).support) hv)
  · refine hsum cz tz hsz Finset.subset_union_right fun v hv => ?_
    exact (Finset.subset_union_right).trans
      (Finset.subset_biUnion_of_mem (fun v => (E.repr (cy v)).support ∪ (E.repr (cz v)).support) hv)

theorem main (hT : ModularGroup.T ∈ Γ) (x : qExpFunctionFieldC K Γ) (P Q : PowerSeries ℤ)
    (hQ : intSeriesC K Q ≠ 0) (hx : (x : LaurentSeries K) = intSeriesC K P / intSeriesC K Q) :
    (x : LaurentSeries K) ∈ intFormRatiosC K Γ := by
  classical
  have hΓ := one_mem_strictPeriods hT
  set T := ratios K hΓ with hTdef
  set E := Module.Basis.ofVectorSpace (primeField K) K with hE
  rw [← mem_ratios_iff K hΓ]

  have hxcl : (x : LaurentSeries K) ∈ Subfield.closure
      (Set.range (algebraMap K (LaurentSeries K)) ∪ (T : Set (LaurentSeries K))) := by
    rw [← IntermediateField.adjoin_toSubfield]
    show (x : LaurentSeries K) ∈ (IntermediateField.adjoin K (intFormRatiosC K Γ)).toSubfield
    exact x.2
  rw [Subfield.mem_closure_iff] at hxcl
  obtain ⟨y, hy, z, hz, hyz⟩ := hxcl
  have hy' := mem_span_of_mem_closure K hΓ hy
  have hz' := mem_span_of_mem_closure K hΓ hz

  rcases eq_or_ne z 0 with rfl | hz0
  · rw [div_zero] at hyz
    rw [← hyz]
    exact zero_mem _

  obtain ⟨B, Y, Z, hY, hZ, rfl, rfl⟩ := exists_common_expansion K hΓ hy' hz'

  have hrel : ∑ b ∈ B, E b • ((x : LaurentSeries K) * Z b - Y b) = 0 := by
    have h1 : ∀ b, E b • ((x : LaurentSeries K) * Z b - Y b) =
        (x : LaurentSeries K) * (E b • Z b) - E b • Y b := by
      intro b
      rw [smul_sub, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul,
        mul_left_comm]
    simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [sub_eq_zero, ← hyz, div_mul_cancel₀ _ hz0]

  have hmem : ∀ b, (x : LaurentSeries K) * Z b - Y b ∈ (embQ K).fieldRange := by
    intro b
    refine sub_mem (mul_mem ?_ (ratios_le_fieldRange K hΓ (hZ b))) (ratios_le_fieldRange K hΓ (hY b))
    rw [hx]
    exact div_mem (intSeriesC_mem_fieldRange K P) (intSeriesC_mem_fieldRange K Q)
  choose g hg using fun b => RingHom.mem_fieldRange.mp (hmem b)
  have hrel' : ∑ b ∈ B, E b • embQ K (g b) = 0 := by
    rw [← hrel]
    exact Finset.sum_congr rfl fun b _ => by rw [hg b]
  have hzero := eq_zero_of_sum_smul_eq_zero K B E E.linearIndependent g hrel'

  have hZne : ∃ b ∈ B, Z b ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hz0
    exact Finset.sum_eq_zero fun b hb => by rw [hall b hb, smul_zero]
  obtain ⟨b, hb, hZb⟩ := hZne
  have hxb : (x : LaurentSeries K) * Z b = Y b := by
    have h := hg b
    rw [hzero b hb, map_zero] at h
    exact (sub_eq_zero.mp h.symm)
  have : (x : LaurentSeries K) = Y b / Z b := by
    rw [eq_div_iff hZb, hxb]
  rw [this]
  exact div_mem (hY b) (hZ b)

end LDRatio

end ModularCurve

end

theorem solution
    (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hT : ModularGroup.T ∈ Γ)
    (x : ModularCurve.qExpFunctionFieldC K Γ) (P Q : PowerSeries ℤ)
    (hQ : ModularCurve.intSeriesC K Q ≠ 0)
    (hx : (x : LaurentSeries K) = ModularCurve.intSeriesC K P / ModularCurve.intSeriesC K Q) :
    (x : LaurentSeries K) ∈ ModularCurve.intFormRatiosC K Γ :=
  ModularCurve.LDRatio.main K hT x P Q hQ hx

end S_ModularCurve_mem_intFormRatiosC_of_coe_eq_intSeriesC_div
end P2MW
export P2MW.S_ModularCurve_mem_intFormRatiosC_of_coe_eq_intSeriesC_div (solution)
