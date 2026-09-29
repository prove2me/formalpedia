-- Prove2me | solution 1 for ModularCurve.mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f5196e59-e339-5b1f-9d54-f27d37eadd86

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularForm_exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic
import Theorems.Thm_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne
import Theorems.Thm_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open UpperHalfPlane Polynomial
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "qExpand_one_apply jq coeff_jq_neg_one dedekindPsi modularFunctionFieldFull jqd_mem_full coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast exists_gamma0_qExpansion_div_eq_jqNModC jqModC_eq_qExpansion_E4_cube_div_discriminant Gamma0_index finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero coeffMap_qExpand"
namespace QExpPrinciple
p2m_open "ModularCurve~transcendental_jqModC~coeffEmb_jq~coeff_jqModC_neg_one"

section Level

variable {N : ℕ}

abbrev qL (F : ℍ → ℂ) : LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qL_mul {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) :
    qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N), PowerSeries.coe_mul]

theorem qL_add {a : ℤ} (f g : ModularForm (CongruenceSubgroup.Gamma0 N) a) :
    qL (⇑(f + g)) = qL f + qL g := by
  simp only [qL, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N), PowerSeries.coe_add]

theorem qL_mcast {a b : ℤ} (h : a = b) (f : ModularForm (CongruenceSubgroup.Gamma0 N) a) :
    qL (ModularForm.mcast h f) = qL f := by
  simp only [qL, ModularForm.coe_mcast]

theorem qL_zero' {a : ℤ} : qL (⇑(0 : ModularForm (CongruenceSubgroup.Gamma0 N) a)) = 0 := by
  simp only [qL, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ), PowerSeries.coe_zero]

theorem qL_one' : qL (⇑(1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0)) = 1 := by
  simp only [qL, ModularForm.qExpansion_one, PowerSeries.coe_one]

theorem qL_const (c : ℂ) :
    qL (⇑(c • (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0))) =
      algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [qL, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N), ModularForm.qExpansion_one,
    Algebra.smul_def, mul_one, HahnSeries.algebraMap_apply']

theorem qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  simpa [qL] using h

theorem one_ne_zero' : (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) ≠ 0 := by
  intro h
  have := congrArg
    (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) 0 => (F : ℍ → ℂ) UpperHalfPlane.I) h
  simp [ModularForm.one_coe_eq_one] at this

theorem mul_ne_zero' {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mul g ≠ 0 := by
  intro hfg
  have h := congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) (a + b) => qL F) hfg
  beta_reduce at h
  rw [qL_mul, qL_zero'] at h
  exact (mul_ne_zero (qL_ne_zero f hf) (qL_ne_zero g hg)) h

variable (N) in

def IsRatio (x : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧ x * qL h = qL g

theorem isRatio_algebraMap (c : ℂ) : IsRatio N (algebraMap ℂ (LaurentSeries ℂ) c) :=
  ⟨0, c • 1, 1, one_ne_zero', by rw [qL_one', mul_one, qL_const]⟩

theorem isRatio_one : IsRatio N 1 := by
  simpa using isRatio_algebraMap (N := N) 1

theorem IsRatio.mul {x y : LaurentSeries ℂ} (hx : IsRatio N x) (hy : IsRatio N y) :
    IsRatio N (x * y) := by
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  obtain ⟨b, g', h', hh', hye⟩ := hy
  refine ⟨a + b, g.mul g', h.mul h', mul_ne_zero' h h' hh hh', ?_⟩
  rw [qL_mul, qL_mul, ← hxe, ← hye]; ring

theorem IsRatio.add {x y : LaurentSeries ℂ} (hx : IsRatio N x) (hy : IsRatio N y) :
    IsRatio N (x + y) := by
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  obtain ⟨b, g', h', hh', hye⟩ := hy
  refine ⟨a + b, g.mul h' + ModularForm.mcast (add_comm b a) (g'.mul h), h.mul h',
    mul_ne_zero' h h' hh hh', ?_⟩
  rw [qL_add, qL_mul, qL_mul, qL_mcast, qL_mul, ← hxe, ← hye]; ring

theorem IsRatio.neg {x : LaurentSeries ℂ} (hx : IsRatio N x) : IsRatio N (-x) := by
  have : -x = algebraMap ℂ (LaurentSeries ℂ) (-1) * x := by rw [map_neg, map_one]; ring
  rw [this]
  exact (isRatio_algebraMap (-1)).mul hx

theorem IsRatio.inv {x : LaurentSeries ℂ} (hx : IsRatio N x) : IsRatio N x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using isRatio_algebraMap (N := N) 0
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  have hg : g ≠ 0 := by
    intro hg0
    rw [hg0, qL_zero'] at hxe
    exact (mul_ne_zero hx0 (qL_ne_zero h hh)) hxe
  refine ⟨a, h, g, hg, ?_⟩
  rw [← hxe, mul_comm x, mul_comm x⁻¹, mul_assoc, mul_inv_cancel₀ hx0, mul_one]

theorem IsRatio.of_eq_div {x : LaurentSeries ℂ} {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0) (hx : x = qL g / qL h) :
    IsRatio N x :=
  ⟨k, g, h, hh, by rw [hx, div_mul_cancel₀ _ (qL_ne_zero h hh)]⟩

theorem IsRatio.eq_div {x : LaurentSeries ℂ} {k : ℤ}
    {g h : ModularForm (CongruenceSubgroup.Gamma0 N) k} (hh : h ≠ 0) (hx : x * qL h = qL g) :
    x = qL g / qL h := by
  rw [← hx, mul_div_cancel_right₀ _ (qL_ne_zero h hh)]

end Level

section Generators

def E4cube : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num) ((ModularForm.E₄.mul ModularForm.E₄).mul ModularForm.E₄)

theorem coe_E4cube :
    (E4cube : ℍ → ℂ) = (ModularForm.E₄ : ℍ → ℂ) * ModularForm.E₄ * ModularForm.E₄ := by
  simp only [E4cube, ModularForm.coe_mcast, ModularForm.coe_mul]

theorem qL_E4cube : qL E4cube = qL ModularForm.E₄ ^ 3 := by
  rw [coe_E4cube, qL, ← ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos
    one_mem_strictPeriods_SL, ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos
    one_mem_strictPeriods_SL, PowerSeries.coe_mul, PowerSeries.coe_mul]
  ring

def DeltaMF : ModularForm 𝒮ℒ 12 := ModularFormClass.modularForm CuspForm.discriminant

theorem coe_DeltaMF : (DeltaMF : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem DeltaMF_apply_ne_zero (z : ℍ) : DeltaMF z ≠ 0 := by
  rw [coe_DeltaMF]
  exact ModularForm.discriminant_ne_zero z

variable (N : ℕ) [NeZero N]

theorem isRatio_jqModC : IsRatio N (jqModC ℂ) := by
  obtain ⟨G, hG⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne N E4cube
  obtain ⟨Dl, hDl⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne N DeltaMF
  have hDl0 : Dl ≠ 0 := by
    intro h0
    have := congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) 12 => (F : ℍ → ℂ) I) h0
    simp only [hDl, ModularForm.coe_zero, Pi.zero_apply] at this
    exact DeltaMF_apply_ne_zero I this
  refine IsRatio.of_eq_div G Dl hDl0 ?_
  rw [ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, hG, hDl, qL_E4cube, coe_DeltaMF]

theorem isRatio_jqNModC : IsRatio N (jqNModC ℂ N) := by
  obtain ⟨G, H, hH, hGH⟩ := ModularCurve.exists_gamma0_qExpansion_div_eq_jqNModC N
  exact IsRatio.of_eq_div G H hH hGH.symm

theorem card_quotient_Gamma0 :
    Nat.card (𝒮ℒ ⧸ ((CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))).subgroupOf 𝒮ℒ) =
      dedekindPsi N := by
  rw [← ModularCurve.Gamma0_index N]
  change ((CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ).index = _
  rw [← Subgroup.relIndex, MonoidHom.range_eq_map, ← Subgroup.relIndex_comap,
    Subgroup.comap_map_eq_self_of_injective Matrix.SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]

end Generators

section ClearDenominators

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem exists_dependence_of_aeval_eq_zero {t z : E} {D : ℕ}
    (B : Polynomial (IntermediateField.adjoin F ({t} : Set E))) (hB0 : B ≠ 0)
    (hBdeg : B.natDegree ≤ D) (hBz : aeval z B = 0) :
    ∃ (M : ℕ) (c : Fin (D + 1) × Fin (M + 1) → F), (∃ im, c im ≠ 0) ∧
      ∑ im, c im • (t ^ (im.2 : ℕ) * z ^ (im.1 : ℕ)) = 0 := by
  classical

  have hrep : ∀ b : IntermediateField.adjoin F ({t} : Set E),
      ∃ rs : F[X] × F[X], aeval t rs.2 ≠ 0 ∧ (b : E) * aeval t rs.2 = aeval t rs.1 := by
    intro b
    obtain ⟨r, s, hb⟩ := (IntermediateField.mem_adjoin_simple_iff F (b : E)).mp b.2
    by_cases hs : aeval t s = 0
    · refine ⟨(0, 1), by simp, ?_⟩
      simp [hb, hs]
    · exact ⟨(r, s), hs, by rw [hb, div_mul_cancel₀ _ hs]⟩
  choose rs hrs0 hrs using hrep
  set S : F[X] := ∏ i ∈ Finset.range (D + 1), (rs (B.coeff i)).2 with hS
  have hS0 : aeval t S ≠ 0 := by
    rw [hS, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hrs0 _
  set p : ℕ → F[X] := fun i =>
    (rs (B.coeff i)).1 * ∏ i' ∈ (Finset.range (D + 1)).erase i, (rs (B.coeff i')).2 with hp
  have hpi : ∀ i ∈ Finset.range (D + 1), aeval t (p i) = (B.coeff i : E) * aeval t S := by
    intro i hi
    simp only [hp, map_mul, ← hrs, hS]
    rw [mul_assoc, ← map_mul, map_prod, ← Finset.mul_prod_erase _ _ hi, map_mul, map_prod]
  set M : ℕ := (Finset.range (D + 1)).sup fun i => (p i).natDegree with hM
  have hpdeg : ∀ i ∈ Finset.range (D + 1), (p i).natDegree < M + 1 := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (p i).natDegree) hi)
  refine ⟨M, fun im => (p im.1).coeff im.2, ?_, ?_⟩
  ·
    have hlead : (B.coeff B.natDegree : E) ≠ 0 := by
      have h := leadingCoeff_ne_zero.mpr hB0
      rwa [Ne, ← ZeroMemClass.coe_eq_zero] at h
    have hiD : B.natDegree ∈ Finset.range (D + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hBdeg)
    have hp0 : p B.natDegree ≠ 0 := by
      intro h0
      have h := hpi _ hiD
      rw [h0, map_zero] at h
      exact mul_ne_zero hlead hS0 h.symm
    refine ⟨(⟨B.natDegree, Nat.lt_succ_of_le hBdeg⟩,
      ⟨(p B.natDegree).natDegree, hpdeg _ hiD⟩), ?_⟩
    change (p B.natDegree).coeff (p B.natDegree).natDegree ≠ 0
    exact leadingCoeff_ne_zero.mpr hp0
  ·
    have hBz' : ∑ i ∈ Finset.range (D + 1), (B.coeff i : E) * z ^ i = 0 := by
      have h := hBz
      rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hBdeg)] at h
      simpa only [Algebra.smul_def, IntermediateField.algebraMap_apply] using h
    calc ∑ im : Fin (D + 1) × Fin (M + 1), (p im.1).coeff im.2 • (t ^ (im.2 : ℕ) * z ^ (im.1 : ℕ))
        = ∑ i : Fin (D + 1), (∑ m : Fin (M + 1), (p i).coeff m • t ^ (m : ℕ)) * z ^ (i : ℕ) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [smul_mul_assoc]
      _ = ∑ i ∈ Finset.range (D + 1), aeval t (p i) * z ^ i := by
          rw [Fin.sum_univ_eq_sum_range
            (fun i => (∑ m : Fin (M + 1), (p i).coeff m • t ^ (m : ℕ)) * z ^ i) (D + 1)]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [aeval_eq_sum_range' (hpdeg i hi),
            Fin.sum_univ_eq_sum_range (fun m => (p i).coeff m • t ^ m) (M + 1)]
      _ = (∑ i ∈ Finset.range (D + 1), (B.coeff i : E) * z ^ i) * aeval t S := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hpi i hi]; ring
      _ = 0 := by rw [hBz', zero_mul]

end ClearDenominators

section Sigma

variable {K : Type*} [Field K] (σ : K →+* ℂ)

theorem exists_retraction :
    ∃ l : ℂ →+ K, (∀ a c, l (σ a * c) = a * l c) ∧ l 1 = 1 := by
  letI : Algebra K ℂ := σ.toAlgebra
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)
  refine ⟨g.toAddMonoidHom, fun a c => ?_, ?_⟩
  · have := g.map_smul a c
    rw [Algebra.smul_def] at this
    first | exact this | simpa using this
  · have := LinearMap.congr_fun hg 1
    simpa using this

theorem linearIndependent_coeffMap {ι : Type*} [Fintype ι] {u : ι → LaurentSeries K}
    (hu : LinearIndependent K u) : LinearIndependent ℂ (fun i => coeffMap σ (u i)) := by
  classical
  obtain ⟨l, hl, hl1⟩ := exists_retraction σ
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨i₀, hi₀⟩ := hne
  set g' : ι → ℂ := fun i => (g i₀)⁻¹ * g i with hg'def
  have hg'₀ : g' i₀ = 1 := by simp [hg'def, hi₀]
  have hg' : ∑ i, g' i • coeffMap σ (u i) = 0 := by
    have : ∑ i, g' i • coeffMap σ (u i) = (g i₀)⁻¹ • ∑ i, g i • coeffMap σ (u i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
    rw [this, hg, smul_zero]
  have key : ∑ i, l (g' i) • u i = 0 := by
    ext n
    have hn := congrArg (fun z : LaurentSeries ℂ => l (z.coeff n)) hg'
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul,
      HahnSeries.coeff_zero, map_zero, map_sum] at hn ⊢
    rw [← hn]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (g' i), hl, mul_comm]
  have := hu (fun i => l (g' i)) key i₀
  rw [hg'₀, hl1] at this
  exact one_ne_zero this

theorem coeffMap_algebraMap (c : K) :
    coeffMap σ (algebraMap K (LaurentSeries K) c) = algebraMap ℂ (LaurentSeries ℂ) (σ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_jqModC : coeffMap σ (jqModC K) = jqModC ℂ := map_jqModC σ

theorem coeffMap_jqNModC (N : ℕ) [NeZero N] : coeffMap σ (jqNModC K N) = jqNModC ℂ N := by
  rw [jqNModC, ModularCurve.coeffMap_qExpand, coeffMap_jqModC]; rfl

theorem coeff_jqModC_neg_one_int : (jqModC ℤ).coeff (-1) = 1 := by
  have h : (((jqModC ℤ).coeff (-1) : ℤ) : ℚ) = 1 := by
    rw [← coeff_jq_neg_one, ← jqModC_rat, jqModC_eq_map_intCast ℚ, HahnSeries.map_coeff]; rfl
  exact_mod_cast h

theorem coeff_jqModC_neg_one : (jqModC K).coeff (-1) = 1 := by
  rw [jqModC_eq_map_intCast K, HahnSeries.map_coeff, coeff_jqModC_neg_one_int, map_one]

theorem transcendental_jqModC : Transcendental K (jqModC K) := by
  intro halg
  have h := LaurentSeries.eq_C_coeff_zero_of_isAlgebraic halg
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff (-1)) h
  simp only [coeff_jqModC_neg_one, HahnSeries.C_apply,
    HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by norm_num)] at h1
  exact one_ne_zero h1

variable (N : ℕ) [NeZero N]

theorem isRatio_coeffMap_of_mem {x y : LaurentSeries K} (hx : IsRatio N (coeffMap σ x))
    (hy : y ∈ IntermediateField.adjoin K
      (({jqModC K} : Set (LaurentSeries K)) ∪ {jqNModC K N, x})) :
    IsRatio N (coeffMap σ y) := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hy
  induction hy using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | hz
      · rw [coeffMap_algebraMap]; exact isRatio_algebraMap _
      · simp only [Set.singleton_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · rw [coeffMap_jqModC]; exact isRatio_jqModC N
        · rw [coeffMap_jqNModC]; exact isRatio_jqNModC N
        · exact hx
  | one => simpa using isRatio_one (N := N)
  | add x y _ _ hx hy => simpa using hx.add hy
  | neg x _ hx => simpa using hx.neg
  | inv x _ hx => simpa using hx.inv
  | mul x y _ _ hx hy => simpa using hx.mul hy

theorem exists_polynomial_of_isRatio {y : LaurentSeries K} (hy : IsRatio N (coeffMap σ y)) :
    ∃ P : Polynomial (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))),
      P ≠ 0 ∧ P.natDegree ≤ dedekindPsi N ∧ aeval y P = 0 := by
  classical
  obtain ⟨k, g, h, hh, hyq⟩ := hy
  obtain ⟨B, hB0, hBdeg, hBy⟩ :=
    ModularForm.exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic
      (𝒢 := (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (one_mem_strictPeriods N)
      g h hh
  rw [card_quotient_Gamma0] at hBdeg
  rw [← IsRatio.eq_div hh hyq] at hBy
  obtain ⟨M, c, ⟨im₀, hc0⟩, hsum⟩ := exists_dependence_of_aeval_eq_zero B hB0 hBdeg hBy
  rw [← ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, ← coeffMap_jqModC σ] at hsum

  set u : Fin (dedekindPsi N + 1) × Fin (M + 1) → LaurentSeries K :=
    fun im => jqModC K ^ (im.2 : ℕ) * y ^ (im.1 : ℕ) with hu
  have hsum' : ∑ im, c im • coeffMap σ (u im) = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun im _ => ?_
    rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul,
      hu]
    simp only [map_mul, map_pow]
  have hdep : ¬ LinearIndependent ℂ (fun im => coeffMap σ (u im)) :=
    Fintype.not_linearIndependent_iff.mpr ⟨c, hsum', im₀, hc0⟩
  have hdepK : ¬ LinearIndependent K u := fun hli => hdep (linearIndependent_coeffMap σ hli)
  obtain ⟨d, hdsum, im₁, hd0⟩ := Fintype.not_linearIndependent_iff.mp hdepK

  set L := IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) with hL
  let jL : L := ⟨jqModC K, IntermediateField.mem_adjoin_simple_self K _⟩
  let Dp : Fin (dedekindPsi N + 1) → K[X] := fun i => ∑ m : Fin (M + 1), C (d (i, m)) * X ^ (m : ℕ)
  have hDp_coeff : ∀ i (m : Fin (M + 1)), (Dp i).coeff (m : ℕ) = d (i, m) := by
    intro i m
    simp only [Dp, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single m]
    · simp
    · intro m' _ hm'
      rw [if_neg]
      exact fun h => hm' (Fin.ext h.symm)
    · simp
  have hDp_aeval : ∀ i,
      aeval (jqModC K) (Dp i) = ∑ m : Fin (M + 1), d (i, m) • jqModC K ^ (m : ℕ) := by
    intro i
    simp only [Dp, map_sum, map_mul, aeval_C, map_pow, aeval_X, algebraMap_laurentSeries_eq_single,
      HahnSeries.single_zero_mul_eq_smul]
  have hjL_aeval : ∀ i, aeval (jqModC K) (Dp i) = ((aeval jL (Dp i) : L) : LaurentSeries K) := by
    intro i
    have h := Polynomial.aeval_algHom_apply L.val jL (Dp i)
    exact h
  let P : L[X] := ∑ i : Fin (dedekindPsi N + 1), C (aeval jL (Dp i)) * X ^ (i : ℕ)
  have hP_coeff : ∀ i : Fin (dedekindPsi N + 1), P.coeff (i : ℕ) = aeval jL (Dp i) := by
    intro i
    simp only [P, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hi'
      rw [if_neg]
      exact fun h => hi' (Fin.ext h.symm)
    · simp
  refine ⟨P, ?_, ?_, ?_⟩
  ·
    intro hP
    have hcoef : ∀ i : Fin (dedekindPsi N + 1), aeval (jqModC K) (Dp i) = 0 := by
      intro i
      have h1 : aeval jL (Dp i) = 0 := by rw [← hP_coeff i, hP, Polynomial.coeff_zero]
      rw [hjL_aeval i, h1]; rfl
    have hDp0 : ∀ i, Dp i = 0 := by
      intro i
      by_contra hne
      exact transcendental_jqModC (K := K) ⟨Dp i, hne, hcoef i⟩
    apply hd0
    rw [show im₁ = (im₁.1, im₁.2) from rfl, ← hDp_coeff, hDp0, Polynomial.coeff_zero]
  ·
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.2)
  ·
    calc aeval y P
        = ∑ i : Fin (dedekindPsi N + 1), aeval (jqModC K) (Dp i) * y ^ (i : ℕ) := by
          simp only [P, map_sum, map_mul, aeval_C, map_pow, aeval_X,
            IntermediateField.algebraMap_apply, ← hjL_aeval]
      _ = ∑ im, d im • u im := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hDp_aeval, Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hu, ← HahnSeries.single_zero_mul_eq_smul, ← HahnSeries.single_zero_mul_eq_smul,
            mul_assoc]
      _ = 0 := hdsum

set_option hygiene false in

local notation "LK" => IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

theorem mem_adjoin_of_isRatio [CharZero K] {x : LaurentSeries K} (hx : IsRatio N (coeffMap σ x)) :
    x ∈ IntermediateField.adjoin K ({jqModC K, jqNModC K N} : Set (LaurentSeries K)) := by
  classical

  have hrat : ∀ y : LaurentSeries K,
      y ∈ IntermediateField.adjoin LK ({jqNModC K N, x} : Set (LaurentSeries K)) →
        IsRatio N (coeffMap σ y) := by
    intro y hy
    have hy' : y ∈ IntermediateField.adjoin K
        (({jqModC K} : Set (LaurentSeries K)) ∪ {jqNModC K N, x}) := by
      rw [← IntermediateField.adjoin_adjoin_left]
      exact hy
    exact isRatio_coeffMap_of_mem σ N hx hy'

  have halg : ∀ y : LaurentSeries K,
      y ∈ IntermediateField.adjoin LK ({jqNModC K N, x} : Set (LaurentSeries K)) →
        ∃ P : Polynomial LK, P ≠ 0 ∧ P.natDegree ≤ dedekindPsi N ∧ aeval y P = 0 :=
    fun y hy => exists_polynomial_of_isRatio σ N (hrat y hy)
  haveI hfd : FiniteDimensional LK
      (IntermediateField.adjoin LK ({jqNModC K N, x} : Set (LaurentSeries K))) := by
    refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
    obtain ⟨P, hP0, -, hPz⟩ := halg z (IntermediateField.subset_adjoin _ _ hz)
    exact (show IsAlgebraic LK z from ⟨P, hP0, hPz⟩).isIntegral
  set M' : IntermediateField LK (LaurentSeries K) :=
    IntermediateField.adjoin LK ({jqNModC K N, x} : Set (LaurentSeries K)) with hM'
  have hdeg : ∀ y : M', ∃ P : Polynomial LK, P ≠ 0 ∧ P.natDegree ≤ dedekindPsi N ∧
      aeval y P = 0 := by
    intro y
    obtain ⟨P, hP0, hPd, hPy⟩ := halg y y.2
    refine ⟨P, hP0, hPd, ?_⟩
    apply M'.val.toRingHom.injective
    rw [map_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ← Polynomial.aeval_algHom_apply]
    exact hPy
  have hint : ∀ y : M', IsIntegral LK y := fun y => by
    obtain ⟨P, hP0, -, hPy⟩ := hdeg y
    exact (show IsAlgebraic LK y from ⟨P, hP0, hPy⟩).isIntegral

  haveI : CharZero LK := charZero_of_injective_algebraMap (algebraMap K LK).injective
  haveI : PerfectField LK := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic LK M' := Algebra.IsAlgebraic.of_finite LK M'
  haveI : Algebra.IsSeparable LK M' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hfin : Module.finrank LK M' ≤ dedekindPsi N := by
    obtain ⟨α, hα⟩ := Field.exists_primitive_element LK M'
    rw [← IntermediateField.finrank_top', ← hα, IntermediateField.adjoin.finrank (hint α)]
    obtain ⟨P, hP0, hPd, hPα⟩ := hdeg α
    exact (natDegree_le_natDegree (minpoly.degree_le_of_ne_zero LK α hP0 hPα)).trans hPd

  have hMM' : IntermediateField.adjoin LK ({jqNModC K N} : Set (LaurentSeries K)) ≤ M' :=
    IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hMeq : IntermediateField.adjoin LK ({jqNModC K N} : Set (LaurentSeries K)) = M' := by
    refine IntermediateField.eq_of_le_of_finrank_le hMM' ?_
    rw [ModularCurve.finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero (K := K) N]
    exact hfin
  have hxM' : x ∈ M' :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_singleton x))
  rw [← hMeq] at hxM'
  have hxK : x ∈ IntermediateField.adjoin K
      (({jqModC K} : Set (LaurentSeries K)) ∪ {jqNModC K N}) := by
    rw [← IntermediateField.adjoin_adjoin_left]
    exact hxM'
  simpa only [Set.singleton_union] using hxK

end Sigma

section Bar

variable (N : ℕ) [NeZero N]

local notation "ℚb" => AlgebraicClosure ℚ

theorem coeffEmb_jq : coeffEmb ℚb jq = jqModC ℚb := by
  rw [coeffEmb, ← jqModC_rat]
  exact map_jqModC _

theorem adjoin_le_laurentBaseChange :
    IntermediateField.adjoin ℚb ({jqModC ℚb, jqNModC ℚb N} : Set (LaurentSeries ℚb)) ≤
      laurentBaseChange ℚb (modularFunctionFieldFull N) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro z (rfl | rfl)
  · haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
    rw [← coeffEmb_jq]
    simpa [qExpand_one_apply] using
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N := N) (d := 1) (one_dvd N))
  · rw [SetLike.mem_coe, jqNModC, ← coeffEmb_jq, coeffEmb, ← ModularCurve.coeffMap_qExpand]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (N := N) (d := N) dvd_rfl)

end Bar

end ModularCurve.QExpPrinciple

end

open UpperHalfPlane in
theorem solution (N : ℕ) [NeZero N]
    {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (σ : AlgebraicClosure ℚ →+* ℂ) (x : LaurentSeries (AlgebraicClosure ℚ))
    (hx : ModularCurve.coeffMap σ x =
      ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    x ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldFull N) :=
  ModularCurve.QExpPrinciple.adjoin_le_laurentBaseChange N
    (ModularCurve.QExpPrinciple.mem_adjoin_of_isRatio σ N
      (ModularCurve.QExpPrinciple.IsRatio.of_eq_div g h hh hx))

end S_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div
end P2MW
export P2MW.S_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div (solution)
