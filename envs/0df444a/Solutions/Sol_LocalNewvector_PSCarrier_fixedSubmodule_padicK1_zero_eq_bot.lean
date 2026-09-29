-- Prove2me | solution 1 for LocalNewvector.PSCarrier.fixedSubmodule_padicK1_zero_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c851ef68-ad10-540b-bc24-56a1353bd429

import Definitions.Def_RepTheory_SmoothVectors
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_IntegralSubgroupCompact
import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot

set_option autoImplicit false

open Matrix

namespace LocalGL2
p2m_export "LocalGL2" "unipotentR unipotentInt weylInt weylInt_mem coe_weylInt integralSubgroup exists_entry_eq_of_mem_integralSubgroup"
p2m_open "LocalGL2"

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [Algebra R K]

def lowerUnipotentR (r : R) : GL (Fin 2) R :=
  ⟨!![1, 0; r, 1], !![1, 0; -r, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def lowerUnipotentInt (K : Type*) [Field K] [Algebra R K] (r : R) : GL (Fin 2) K :=
  ⟨!![1, 0; algebraMap R K r, 1], !![1, 0; -(algebraMap R K r), 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[scoped simp] lemma coe_lowerUnipotentInt (r : R) :
    (lowerUnipotentInt K r : Matrix (Fin 2) (Fin 2) K) = !![1, 0; algebraMap R K r, 1] :=
  rfl

@[scoped simp] lemma coe_lowerUnipotentInt_inv (r : R) :
    ((lowerUnipotentInt K r)⁻¹ : GL (Fin 2) K).val = !![1, 0; -(algebraMap R K r), 1] :=
  rfl

lemma lowerUnipotentInt_mem (r : R) : lowerUnipotentInt K r ∈ integralSubgroup R K := by
  refine ⟨lowerUnipotentR r, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotentR, lowerUnipotentInt, Matrix.GeneralLinearGroup.map]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

private theorem dvd_total_dvr (x y : R) : x ∣ y ∨ y ∣ x := by
  rcases le_total (IsDiscreteValuationRing.addVal R x) (IsDiscreteValuationRing.addVal R y)
    with h | h
  · exact Or.inl (IsDiscreteValuationRing.addVal_le_iff_dvd.mp h)
  · exact Or.inr (IsDiscreteValuationRing.addVal_le_iff_dvd.mp h)

theorem exists_ratio_or_ratio (x y : K) :
    (∃ r : R, x = algebraMap R K r * y) ∨ (∃ r : R, y = algebraMap R K r * x) := by
  obtain ⟨p, s, hs, hx⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨q, t, ht, hy⟩ := IsFractionRing.div_surjective (A := R) y
  have hs0 : algebraMap R K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have ht0 : algebraMap R K t ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht

  rcases dvd_total_dvr (p * t) (q * s) with ⟨c, hc⟩ | ⟨c, hc⟩
  ·
    refine Or.inr ⟨c, ?_⟩
    rw [← hx, ← hy, ← mul_div_assoc, div_eq_div_iff ht0 hs0, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg (algebraMap R K) (by linear_combination hc)
  ·
    refine Or.inl ⟨c, ?_⟩
    rw [← hx, ← hy, ← mul_div_assoc, div_eq_div_iff hs0 ht0, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg (algebraMap R K) (by linear_combination hc)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem exists_iwasawa_of_ratio (g : GL (Fin 2) K) (r : R)
    (h : (g : Matrix (Fin 2) (Fin 2) K) 1 0
        = algebraMap R K r * (g : Matrix (Fin 2) (Fin 2) K) 1 1) :
    ∃ b k : GL (Fin 2) K, k ∈ integralSubgroup R K ∧
      (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ g = b * k := by
  refine ⟨g * (lowerUnipotentInt K r)⁻¹, lowerUnipotentInt K r, lowerUnipotentInt_mem r,
    ?_, (inv_mul_cancel_right _ _).symm⟩
  show (g.val * ((lowerUnipotentInt K r)⁻¹ : GL (Fin 2) K).val) 1 0 = 0
  rw [coe_lowerUnipotentInt_inv, Matrix.mul_apply, Fin.sum_univ_two]
  show g.val 1 0 * 1 + g.val 1 1 * -(algebraMap R K r) = 0
  rw [h]
  ring

theorem exists_iwasawa (g : GL (Fin 2) K) :
    ∃ b k : GL (Fin 2) K, k ∈ integralSubgroup R K ∧
      (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ g = b * k := by
  rcases exists_ratio_or_ratio (R := R) ((g : Matrix (Fin 2) (Fin 2) K) 1 0)
      ((g : Matrix (Fin 2) (Fin 2) K) 1 1) with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact exists_iwasawa_of_ratio g r hr
  ·

    have hswap : ((g * weylInt R K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0
        = algebraMap R K r
          * ((g * weylInt R K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      have hcoe : ((g * weylInt R K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          = g.val * !![0, 1; 1, 0] := by
        rw [Units.val_mul, coe_weylInt]
      rw [hcoe]
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using hr
    obtain ⟨b, k, hk, hb, hbk⟩ := exists_iwasawa_of_ratio (g * weylInt R K) r hswap
    refine ⟨b, k * (weylInt R K)⁻¹, mul_mem hk (inv_mem (weylInt_mem)), hb, ?_⟩
    rw [← mul_assoc, ← hbk, mul_inv_cancel_right]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem exists_iwasawa_of_upper_triangular (g : GL (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ∃ b k : GL (Fin 2) K, k ∈ integralSubgroup R K ∧
      (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ g = b * k :=
  ⟨g, 1, one_mem _, hg, (mul_one g).symm⟩

theorem diag_ne_zero_of_isUnit_of_upper_triangular {b : Matrix (Fin 2) (Fin 2) K}
    (hb : IsUnit b) (h10 : b 1 0 = 0) : b 0 0 ≠ 0 ∧ b 1 1 ≠ 0 := by
  have hdet : b.det ≠ 0 := by
    intro h0
    simpa [h0] using (Matrix.isUnit_iff_isUnit_det b).mp hb
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem exists_iwasawa_diag (g : GL (Fin 2) K) :
    ∃ (z : K) (a₁ a₂ : Kˣ) (k : GL (Fin 2) K), k ∈ integralSubgroup R K ∧
      (g : Matrix (Fin 2) (Fin 2) K) = !![1, z; 0, 1] * !![(a₁ : K), 0; 0, (a₂ : K)] * k := by
  obtain ⟨b, k, hk, hb, rfl⟩ := exists_iwasawa (R := R) g
  obtain ⟨h00, h11⟩ := diag_ne_zero_of_isUnit_of_upper_triangular b.isUnit hb
  have hsplit : (b : Matrix (Fin 2) (Fin 2) K)
      = !![1, (b : Matrix (Fin 2) (Fin 2) K) 0 1 / (b : Matrix (Fin 2) (Fin 2) K) 1 1; 0, 1]
        * !![(b : Matrix (Fin 2) (Fin 2) K) 0 0, 0; 0, (b : Matrix (Fin 2) (Fin 2) K) 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hb, div_mul_cancel₀ _ h11]
  refine ⟨(b : Matrix (Fin 2) (Fin 2) K) 0 1 / (b : Matrix (Fin 2) (Fin 2) K) 1 1,
    Units.mk0 _ h00, Units.mk0 _ h11, k, hk, ?_⟩
  rw [Units.val_mul]
  simp only [Units.val_mk0]
  rw [← hsplit]

section Gates

variable (ϖ : R)

def bigCellWitness : GL (Fin 2) K :=
  ⟨!![1, 0; (algebraMap R K ϖ)⁻¹, 1], !![1, 0; -(algebraMap R K ϖ)⁻¹, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[scoped simp] lemma coe_bigCellWitness :
    (bigCellWitness (K := K) ϖ : Matrix (Fin 2) (Fin 2) K)
      = !![1, 0; (algebraMap R K ϖ)⁻¹, 1] :=
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

lemma bigCellWitness_apply_one_zero :
    (bigCellWitness (K := K) ϖ : Matrix (Fin 2) (Fin 2) K) 1 0 = (algebraMap R K ϖ)⁻¹ := by
  rw [coe_bigCellWitness]
  simp

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem bigCellWitness_eq_mul (hϖ0 : algebraMap R K ϖ ≠ 0) :
    (bigCellWitness (K := K) ϖ : Matrix (Fin 2) (Fin 2) K)
      = !![-(algebraMap R K ϖ), 1; 0, (algebraMap R K ϖ)⁻¹]
        * !![0, 1; 1, algebraMap R K ϖ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hϖ0]

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem bigCellWitness_notMem_integralSubgroup (hϖ : Irreducible ϖ) :
    bigCellWitness (K := K) ϖ ∉ integralSubgroup R K := by
  intro hmem
  obtain ⟨r, hr⟩ := exists_entry_eq_of_mem_integralSubgroup hmem 1 0

  have hϖ0 : algebraMap R K ϖ ≠ 0 := fun h0 =>
    hϖ.ne_zero (IsFractionRing.injective R K (by rw [h0, map_zero]))
  have hr' : algebraMap R K r = (algebraMap R K ϖ)⁻¹ :=
    hr.trans (bigCellWitness_apply_one_zero ϖ)

  have h1 : ϖ * r = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_one, hr', mul_inv_cancel₀ hϖ0]
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one r h1)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem bigCellWitness_apply_one_zero_ne_zero (hϖ0 : algebraMap R K ϖ ≠ 0) :
    (bigCellWitness (K := K) ϖ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
  rw [bigCellWitness_apply_one_zero]
  exact inv_ne_zero hϖ0

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem not_exists_iwasawa_integral (hϖ : Irreducible ϖ) :
    ¬ ∃ b k : GL (Fin 2) K, b ∈ integralSubgroup R K ∧ k ∈ integralSubgroup R K ∧
      bigCellWitness (K := K) ϖ = b * k := by
  rintro ⟨b, k, hb, hk, hbk⟩
  exact bigCellWitness_notMem_integralSubgroup ϖ hϖ (hbk ▸ mul_mem hb hk)

end Gates

end LocalGL2
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

set_option autoImplicit false

open Matrix
open scoped Topology

noncomputable section

namespace FLT
p2m_export "FLT" "SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"

open LocalNewvector

open FLT.SmoothVectors

variable (p : ℕ) [Fact p.Prime]

section BorelElements

theorem exists_borelElem_eq_of_lower_left_zero (b : GL (Fin 2) ℚ_[p])
    (hb : (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0) :
    ∃ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]), b = borelElem p a₁ a₂ x := by
  obtain ⟨h00, h11⟩ := LocalGL2.diag_ne_zero_of_isUnit_of_upper_triangular b.isUnit hb
  refine ⟨Units.mk0 _ h00, Units.mk0 _ h11, (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1, ?_⟩
  apply Units.ext
  show (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb]

theorem exists_iwasawa_borelElem (g : GL (Fin 2) ℚ_[p]) :
    ∃ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (k : GL (Fin 2) ℚ_[p]),
      k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] ∧ g = borelElem p a₁ a₂ x * k := by
  obtain ⟨b, k, hk, hb, hbk⟩ := LocalGL2.exists_iwasawa (R := ℤ_[p]) g
  obtain ⟨a₁, a₂, x, rfl⟩ := exists_borelElem_eq_of_lower_left_zero p b hb
  exact ⟨a₁, a₂, x, k, hk, hbk⟩

private theorem norm_eq_one_of_integral_of_inv_integral {y : ℚ_[p]ˣ}
    (h : ∃ r : ℤ_[p], (y : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] r)
    (h' : ∃ r : ℤ_[p], ((y⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] r) :
    ‖(y : ℚ_[p])‖ = 1 := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨s, hs⟩ := h'
  have hle : ‖(y : ℚ_[p])‖ ≤ 1 := by
    rw [hr, PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one r
  have hle' : ‖((y⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := by
    rw [hs, PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one s
  have hmul : ‖(y : ℚ_[p])‖ * ‖((y⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
    rw [← norm_mul, Units.mul_inv, norm_one]
  have hge : (1 : ℝ) ≤ ‖(y : ℚ_[p])‖ := by
    calc (1 : ℝ) = ‖(y : ℚ_[p])‖ * ‖((y⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ := hmul.symm
    _ ≤ ‖(y : ℚ_[p])‖ * 1 := mul_le_mul_of_nonneg_left hle' (norm_nonneg _)
    _ = ‖(y : ℚ_[p])‖ := mul_one _
  exact le_antisymm hle hge

theorem norm_eq_one_of_borelElem_mem_integral {a₁ a₂ : ℚ_[p]ˣ} {x : ℚ_[p]}
    (h : borelElem p a₁ a₂ x ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) :
    ‖(a₁ : ℚ_[p])‖ = 1 ∧ ‖(a₂ : ℚ_[p])‖ = 1 := by
  have hinv : (borelElem p a₁ a₂ x)⁻¹ ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := inv_mem h
  constructor
  · refine norm_eq_one_of_integral_of_inv_integral p ?_ ?_
    · obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup h 0 0
      exact ⟨r, hr.symm⟩
    · obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup hinv 0 0
      exact ⟨r, hr.symm⟩
  · refine norm_eq_one_of_integral_of_inv_integral p ?_ ?_
    · obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup h 1 1
      exact ⟨r, hr.symm⟩
    · obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup hinv 1 1
      exact ⟨r, hr.symm⟩

private theorem mem_range_algebraMap_of_norm_le_one {y : ℚ_[p]} (h : ‖y‖ ≤ 1) :
    y ∈ Set.range (algebraMap ℤ_[p] ℚ_[p]) :=
  ⟨⟨y, h⟩, by rw [PadicInt.algebraMap_apply]⟩

theorem borelElem_mem_integralSubgroup_iff (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    borelElem p a₁ a₂ x ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]
      ↔ ‖(a₁ : ℚ_[p])‖ = 1 ∧ ‖(a₂ : ℚ_[p])‖ = 1 ∧ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := norm_eq_one_of_borelElem_mem_integral p h
    refine ⟨h1, h2, ?_⟩
    obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup h 0 1
    have hx : x = algebraMap ℤ_[p] ℚ_[p] r := hr.symm
    rw [hx, PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one r
  · rintro ⟨h1, h2, hx⟩
    have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := fun a b hab => by
      have ha := PadicInt.algebraMap_apply (p := p) a
      have hb := PadicInt.algebraMap_apply (p := p) b
      rw [ha, hb] at hab
      exact Subtype.coe_injective hab
    have h1' : ‖((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, h1, inv_one]
    have h2' : ‖((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, h2, inv_one]
    have hzero : ‖(0 : ℚ_[p])‖ ≤ 1 := by rw [norm_zero]; exact zero_le_one
    have hoffdiag : ‖-(((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p]))‖ ≤ 1 := by
      rw [norm_neg, norm_mul, norm_mul, h1', h2', one_mul, mul_one]
      exact hx
    rw [FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem hinj]
    constructor
    · intro i j
      fin_cases i <;> fin_cases j
      · exact mem_range_algebraMap_of_norm_le_one p h1.le
      · exact mem_range_algebraMap_of_norm_le_one p hx
      · exact mem_range_algebraMap_of_norm_le_one p hzero
      · exact mem_range_algebraMap_of_norm_le_one p h2.le
    · intro i j
      fin_cases i <;> fin_cases j
      · exact mem_range_algebraMap_of_norm_le_one p h1'.le
      · exact mem_range_algebraMap_of_norm_le_one p hoffdiag
      · exact mem_range_algebraMap_of_norm_le_one p hzero
      · exact mem_range_algebraMap_of_norm_le_one p h2'.le

end BorelElements
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

section HalfModulus

end HalfModulus
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

section PrincipalSeries

theorem smul_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} (g : GL (Fin 2) ℚ_[p])
    (f : RightTranslationFn (GL (Fin 2) ℚ_[p]) ℂ)
    (hf : RightTranslationFn.toFun f ∈ principalSeries p μ₁ μ₂) :
    RightTranslationFn.toFun (g • f) ∈ principalSeries p μ₁ μ₂ :=
  rightTranslate_mem_principalSeries p hf g

end PrincipalSeries
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

section RightInvariant

theorem isLocallyConstant_of_mem_rightInvariantFunctions {U : Subgroup (GL (Fin 2) ℚ_[p])}
    (hU : IsOpen (U : Set (GL (Fin 2) ℚ_[p]))) {f : GL (Fin 2) ℚ_[p] → ℂ}
    (hf : f ∈ rightInvariantFunctions p U) : IsLocallyConstant f := by
  have hf' := (mem_rightInvariantFunctions_iff p).mp hf
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (U : Set (GL (Fin 2) ℚ_[p])),
    hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · show x⁻¹ * x ∈ (U : Set (GL (Fin 2) ℚ_[p]))
    rw [inv_mul_cancel]
    exact U.one_mem
  · intro y hy
    have hy' : x⁻¹ * y ∈ U := hy
    have := hf' _ hy' x
    rwa [mul_inv_cancel_left] at this

theorem isSmoothVector_of_mem_rightInvariantFunctions {U : Subgroup (GL (Fin 2) ℚ_[p])}
    (hU : IsOpen (U : Set (GL (Fin 2) ℚ_[p]))) {f : GL (Fin 2) ℚ_[p] → ℂ}
    (hf : f ∈ rightInvariantFunctions p U) :
    IsSmoothVector (GL (Fin 2) ℚ_[p]) (RightTranslationFn.mk f) := by
  have hf' := (mem_rightInvariantFunctions_iff p).mp hf
  refine Subgroup.isOpen_mono (H₁ := U) (fun u hu => ?_) hU
  rw [MulAction.mem_stabilizer_iff]
  exact RightTranslationFn.ext fun y => hf' u hu y

end RightInvariant
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

section Restriction

theorem apply_borelElem_mul_of_mem_integral {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂)
    {a₁ a₂ : ℚ_[p]ˣ} {x : ℚ_[p]}
    (hmem : borelElem p a₁ a₂ x ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])
    (g : GL (Fin 2) ℚ_[p]) :
    f (borelElem p a₁ a₂ x * g) = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * f g := by
  obtain ⟨h1, h2⟩ := norm_eq_one_of_borelElem_mem_integral p hmem
  rw [apply_borelElem_mul_of_mem_principalSeries p hf,
    halfModulus_eq_one_of_norm_eq_one p h1 h2, mul_one]

theorem eq_zero_of_forall_integral_eq_zero {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂)
    (h : ∀ k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p], f k = 0) : f = 0 := by
  funext g
  show f g = 0
  obtain ⟨a₁, a₂, x, k, hk, rfl⟩ := exists_iwasawa_borelElem p g
  rw [apply_borelElem_mul_of_mem_principalSeries p hf, h k hk, mul_zero]

theorem eq_of_forall_integral_eq {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f₁ f₂ : GL (Fin 2) ℚ_[p] → ℂ} (hf₁ : f₁ ∈ principalSeries p μ₁ μ₂)
    (hf₂ : f₂ ∈ principalSeries p μ₁ μ₂)
    (h : ∀ k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p], f₁ k = f₂ k) : f₁ = f₂ := by
  have hsub : f₁ - f₂ = 0 := by
    refine eq_zero_of_forall_integral_eq_zero p (sub_mem hf₁ hf₂) fun k hk => ?_
    show f₁ k - f₂ k = 0
    rw [h k hk, sub_self]
  funext g
  have h2 : f₁ g - f₂ g = 0 := congrFun hsub g
  exact sub_eq_zero.mp h2

end Restriction
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

section Admissibility

theorem finiteDimensional_principalSeries_inf_rightInvariant (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)
    (U : Subgroup (GL (Fin 2) ℚ_[p])) (hU : IsOpen (U : Set (GL (Fin 2) ℚ_[p]))) :
    FiniteDimensional ℂ
      ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p U) := by
  classical

  have hK₀c : IsCompact ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :
      Subgroup (GL (Fin 2) ℚ_[p])) : Set (GL (Fin 2) ℚ_[p])) :=
    FLT.SpectralSide.isCompact_coe_integralSubgroup_padic p

  have hcover : ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :
      Subgroup (GL (Fin 2) ℚ_[p])) : Set (GL (Fin 2) ℚ_[p]))
      ⊆ ⋃ k ∈ ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :
          Subgroup (GL (Fin 2) ℚ_[p])) : Set (GL (Fin 2) ℚ_[p])),
        (fun y : GL (Fin 2) ℚ_[p] => k⁻¹ * y) ⁻¹' (U : Set (GL (Fin 2) ℚ_[p])) := by
    intro k hk
    refine Set.mem_iUnion₂.mpr ⟨k, hk, ?_⟩
    show k⁻¹ * k ∈ (U : Set (GL (Fin 2) ℚ_[p]))
    rw [inv_mul_cancel]
    exact U.one_mem
  obtain ⟨s, hssub, hsfin, hscover⟩ := hK₀c.elim_finite_subcover_image
    (fun k _ => hU.preimage (continuous_const.mul continuous_id)) hcover
  haveI : Finite ↥s := hsfin.to_subtype

  have hinj : Function.Injective
      (LinearMap.pi (R := ℂ) fun j : s =>
        (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin 2) ℚ_[p] => ℂ)
            ((j : GL (Fin 2) ℚ_[p]))).comp
          (principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p U).subtype) := by
    intro f g hfg

    have hzero : ∀ j : s, ((f : GL (Fin 2) ℚ_[p] → ℂ) - (g : GL (Fin 2) ℚ_[p] → ℂ))
        ((j : GL (Fin 2) ℚ_[p])) = 0 := by
      intro j
      have h1 := congrFun hfg j
      simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.proj_apply, Submodule.coe_subtype] at h1
      show (f : GL (Fin 2) ℚ_[p] → ℂ) (j : GL (Fin 2) ℚ_[p])
          - (g : GL (Fin 2) ℚ_[p] → ℂ) (j : GL (Fin 2) ℚ_[p]) = 0
      rw [h1, sub_self]

    have hmem := sub_mem f.2 g.2
    obtain ⟨hB, hU'⟩ := Submodule.mem_inf.mp hmem
    have hUinv := (mem_rightInvariantFunctions_iff p).mp hU'
    have hK₀ : ∀ k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p],
        ((f : GL (Fin 2) ℚ_[p] → ℂ) - (g : GL (Fin 2) ℚ_[p] → ℂ)) k = 0 := by
      intro k hk
      obtain ⟨i, his, hki⟩ := Set.mem_iUnion₂.mp (hscover hk)
      have hki' : i⁻¹ * k ∈ U := hki
      have hrw : ((f : GL (Fin 2) ℚ_[p] → ℂ) - (g : GL (Fin 2) ℚ_[p] → ℂ)) k
          = ((f : GL (Fin 2) ℚ_[p] → ℂ) - (g : GL (Fin 2) ℚ_[p] → ℂ)) i := by
        have := hUinv _ hki' i
        rwa [mul_inv_cancel_left] at this
      rw [hrw]
      exact hzero ⟨i, his⟩
    have hsub : (f : GL (Fin 2) ℚ_[p] → ℂ) - (g : GL (Fin 2) ℚ_[p] → ℂ) = 0 :=
      eq_zero_of_forall_integral_eq_zero p hB hK₀
    exact Subtype.ext (sub_eq_zero.mp hsub)
  exact FiniteDimensional.of_injective _ hinj

theorem finiteDimensional_principalSeries_inf_rightInvariant_integral
    (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) :
    FiniteDimensional ℂ
      ↥(principalSeries p μ₁ μ₂
          ⊓ rightInvariantFunctions p (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) :=
  finiteDimensional_principalSeries_inf_rightInvariant p μ₁ μ₂ _
    (FLT.SpectralSide.isOpen_coe_integralSubgroup_padic p)

end Admissibility
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

section Smoothness

theorem isSmoothVector_of_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂) :
    IsSmoothVector (GL (Fin 2) ℚ_[p]) (RightTranslationFn.mk f) := by
  classical
  obtain ⟨hlc, htrans⟩ := (mem_principalSeries_iff p).mp hf

  have key : ∀ k : GL (Fin 2) ℚ_[p], ∃ V : Subgroup (GL (Fin 2) ℚ_[p]),
      IsOpen (V : Set (GL (Fin 2) ℚ_[p])) ∧ ∀ v ∈ V, f (k * v) = f k := by
    intro k
    obtain ⟨W, hWopen, hkW, hWconst⟩ := hlc.exists_open k
    have h1 : (fun v : GL (Fin 2) ℚ_[p] => k * v) ⁻¹' W ∈ 𝓝 (1 : GL (Fin 2) ℚ_[p]) :=
      (hWopen.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using hkW)
    obtain ⟨n, hn⟩ := exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one p h1
    exact ⟨gl2CongruenceSubgroup p n, isOpen_coe_gl2CongruenceSubgroup p n,
      fun v hv => hWconst _ (hn hv)⟩
  choose V hVopen hVconst using key

  have hK₀c : IsCompact ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :
      Subgroup (GL (Fin 2) ℚ_[p])) : Set (GL (Fin 2) ℚ_[p])) :=
    FLT.SpectralSide.isCompact_coe_integralSubgroup_padic p
  have hcover : ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :
      Subgroup (GL (Fin 2) ℚ_[p])) : Set (GL (Fin 2) ℚ_[p]))
      ⊆ ⋃ k ∈ ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :
          Subgroup (GL (Fin 2) ℚ_[p])) : Set (GL (Fin 2) ℚ_[p])),
        (fun y : GL (Fin 2) ℚ_[p] => k⁻¹ * y) ⁻¹' (V k : Set (GL (Fin 2) ℚ_[p])) := by
    intro k hk
    refine Set.mem_iUnion₂.mpr ⟨k, hk, ?_⟩
    show k⁻¹ * k ∈ (V k : Set (GL (Fin 2) ℚ_[p]))
    rw [inv_mul_cancel]
    exact (V k).one_mem
  obtain ⟨s, hssub, hsfin, hscover⟩ := hK₀c.elim_finite_subcover_image
    (fun k _ => (hVopen k).preimage (continuous_const.mul continuous_id)) hcover
  haveI : Finite ↥s := hsfin.to_subtype

  set Wgrp : Subgroup (GL (Fin 2) ℚ_[p]) := ⨅ k : s, V (k : GL (Fin 2) ℚ_[p]) with hWgrp
  have hWopen : IsOpen (Wgrp : Set (GL (Fin 2) ℚ_[p])) := by
    rw [hWgrp, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun k => hVopen _
  have hWle : ∀ k : GL (Fin 2) ℚ_[p], k ∈ s → Wgrp ≤ V k := by
    intro k hk
    rw [hWgrp]
    exact iInf_le _ (⟨k, hk⟩ : s)

  have hK0inv : ∀ k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p], ∀ w ∈ Wgrp,
      f (k * w) = f k := by
    intro k hk w hw
    obtain ⟨i, his, hki⟩ := Set.mem_iUnion₂.mp (hscover hk)
    have hv : i⁻¹ * k ∈ V i := hki
    have hvw : i⁻¹ * (k * w) ∈ V i := by
      rw [← mul_assoc]
      exact (V i).mul_mem hv (hWle i his hw)
    have e1 : f (k * w) = f i := by
      have := hVconst i _ hvw
      rwa [mul_inv_cancel_left] at this
    have e2 : f k = f i := by
      have := hVconst i _ hv
      rwa [mul_inv_cancel_left] at this
    rw [e1, e2]

  have hGinv : ∀ w ∈ Wgrp, ∀ y : GL (Fin 2) ℚ_[p], f (y * w) = f y := by
    intro w hw y
    obtain ⟨a₁, a₂, x, k, hk, rfl⟩ := exists_iwasawa_borelElem p y
    rw [mul_assoc, htrans, htrans, hK0inv k hk w hw]

  refine Subgroup.isOpen_mono (H₁ := Wgrp) (fun w hw => ?_) hWopen
  rw [MulAction.mem_stabilizer_iff]
  exact RightTranslationFn.ext fun y => hGinv w hw y

end Smoothness
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

section Spherical

def sphericalVector (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) (g : GL (Fin 2) ℚ_[p]) : ℂ :=
  (μ₁ (exists_iwasawa_borelElem p g).choose : ℂ)
    * (μ₂ (exists_iwasawa_borelElem p g).choose_spec.choose : ℂ)
    * halfModulus p (exists_iwasawa_borelElem p g).choose
        (exists_iwasawa_borelElem p g).choose_spec.choose

theorem sphericalVector_spec (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) (g : GL (Fin 2) ℚ_[p]) :
    ∃ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (k : GL (Fin 2) ℚ_[p]),
      k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] ∧ g = borelElem p a₁ a₂ x * k ∧
        sphericalVector p μ₁ μ₂ g
          = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ :=
  ⟨(exists_iwasawa_borelElem p g).choose,
    (exists_iwasawa_borelElem p g).choose_spec.choose,
    (exists_iwasawa_borelElem p g).choose_spec.choose_spec.choose,
    (exists_iwasawa_borelElem p g).choose_spec.choose_spec.choose_spec.choose,
    (exists_iwasawa_borelElem p g).choose_spec.choose_spec.choose_spec.choose_spec.1,
    (exists_iwasawa_borelElem p g).choose_spec.choose_spec.choose_spec.choose_spec.2,
    rfl⟩

variable {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}

theorem sphericalVector_eq_of_decomp (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    {g : GL (Fin 2) ℚ_[p]} {a₁ a₂ : ℚ_[p]ˣ} {x : ℚ_[p]} {k : GL (Fin 2) ℚ_[p]}
    (hk : k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) (hg : g = borelElem p a₁ a₂ x * k) :
    sphericalVector p μ₁ μ₂ g = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ := by
  obtain ⟨A₁, A₂, X, Kk, hKkmem, hgA, hval⟩ := sphericalVector_spec p μ₁ μ₂ g
  rw [hval]

  have hcomp : borelElem p A₁ A₂ X * Kk = borelElem p a₁ a₂ x * k := hgA.symm.trans hg
  have hquot : (borelElem p a₁ a₂ x)⁻¹ * borelElem p A₁ A₂ X = k * Kk⁻¹ := by
    calc (borelElem p a₁ a₂ x)⁻¹ * borelElem p A₁ A₂ X
        = (borelElem p a₁ a₂ x)⁻¹ * (borelElem p A₁ A₂ X * Kk * Kk⁻¹) := by
          rw [mul_inv_cancel_right]
      _ = (borelElem p a₁ a₂ x)⁻¹ * (borelElem p a₁ a₂ x * k * Kk⁻¹) := by rw [hcomp]
      _ = k * Kk⁻¹ := by rw [mul_assoc, inv_mul_cancel_left]
  have hquotmem : (borelElem p a₁ a₂ x)⁻¹ * borelElem p A₁ A₂ X
      ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by
    rw [hquot]
    exact mul_mem hk (inv_mem hKkmem)
  rw [borelElem_inv, borelElem_mul] at hquotmem
  obtain ⟨hn1, hn2⟩ := norm_eq_one_of_borelElem_mem_integral p hquotmem

  have hμ1 : μ₁ A₁ = μ₁ a₁ := by
    have h := h₁ _ hn1
    calc μ₁ A₁ = μ₁ (a₁ * (a₁⁻¹ * A₁)) := by rw [mul_inv_cancel_left]
      _ = μ₁ a₁ * μ₁ (a₁⁻¹ * A₁) := by rw [map_mul]
      _ = μ₁ a₁ := by rw [h, mul_one]
  have hμ2 : μ₂ A₂ = μ₂ a₂ := by
    have h := h₂ _ hn2
    calc μ₂ A₂ = μ₂ (a₂ * (a₂⁻¹ * A₂)) := by rw [mul_inv_cancel_left]
      _ = μ₂ a₂ * μ₂ (a₂⁻¹ * A₂) := by rw [map_mul]
      _ = μ₂ a₂ := by rw [h, mul_one]
  have hnormA₁ : ‖(A₁ : ℚ_[p])‖ = ‖(a₁ : ℚ_[p])‖ := by
    have hone : ‖((a₁⁻¹ * A₁ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := hn1
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv] at hone
    have ha : ‖(a₁ : ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr a₁.ne_zero
    field_simp at hone
    linarith
  have hnormA₂ : ‖(A₂ : ℚ_[p])‖ = ‖(a₂ : ℚ_[p])‖ := by
    have hone : ‖((a₂⁻¹ * A₂ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := hn2
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv] at hone
    have ha : ‖(a₂ : ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr a₂.ne_zero
    field_simp at hone
    linarith
  rw [hμ1, hμ2, halfModulus_congr p hnormA₁ hnormA₂]

theorem sphericalVector_one (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    sphericalVector p μ₁ μ₂ 1 = 1 := by
  have h : (1 : GL (Fin 2) ℚ_[p]) = borelElem p 1 1 0 * 1 := by
    rw [borelElem_one, one_mul]
  rw [sphericalVector_eq_of_decomp p h₁ h₂ (one_mem _) h, map_one, map_one, halfModulus_one]
  simp

theorem sphericalVector_ne_zero (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    sphericalVector p μ₁ μ₂ ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  rw [sphericalVector_one p h₁ h₂] at h1
  exact one_ne_zero h1

theorem sphericalVector_mem (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    sphericalVector p μ₁ μ₂
      ∈ principalSeries p μ₁ μ₂
          ⊓ rightInvariantFunctions p (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) := by

  have hinv : sphericalVector p μ₁ μ₂
      ∈ rightInvariantFunctions p (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) := by
    rw [mem_rightInvariantFunctions_iff]
    intro u hu g
    obtain ⟨a₁, a₂, x, k, hk, hg⟩ := exists_iwasawa_borelElem p g
    have hg' : g * u = borelElem p a₁ a₂ x * (k * u) := by rw [hg, mul_assoc]
    rw [sphericalVector_eq_of_decomp p h₁ h₂ (mul_mem hk hu) hg',
      sphericalVector_eq_of_decomp p h₁ h₂ hk hg]
  refine Submodule.mem_inf.mpr ⟨(mem_principalSeries_iff p).mpr ⟨?_, ?_⟩, hinv⟩

  · exact isLocallyConstant_of_mem_rightInvariantFunctions p
      (FLT.SpectralSide.isOpen_coe_integralSubgroup_padic p) hinv

  · intro a₁ a₂ x g
    obtain ⟨b₁, b₂, y, k, hk, hg⟩ := exists_iwasawa_borelElem p g
    have hg' : borelElem p a₁ a₂ x * g
        = borelElem p (a₁ * b₁) (a₂ * b₂) ((a₁ : ℚ_[p]) * y + x * (b₂ : ℚ_[p])) * k := by
      rw [hg, ← mul_assoc, borelElem_mul]
    rw [sphericalVector_eq_of_decomp p h₁ h₂ hk hg',
      sphericalVector_eq_of_decomp p h₁ h₂ hk hg, map_mul, map_mul, halfModulus_mul,
      Units.val_mul, Units.val_mul]
    ring

theorem principalSeries_inf_rightInvariant_integral_eq_span
    (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    principalSeries p μ₁ μ₂
        ⊓ rightInvariantFunctions p (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])
      = Submodule.span ℂ {sphericalVector p μ₁ μ₂} := by
  apply le_antisymm
  ·
    intro f hf
    obtain ⟨hfB, hfK⟩ := Submodule.mem_inf.mp hf
    have hfK' := (mem_rightInvariantFunctions_iff p).mp hfK
    have hkey : f = f 1 • sphericalVector p μ₁ μ₂ := by
      funext g
      obtain ⟨a₁, a₂, x, k, hk, hg⟩ := exists_iwasawa_borelElem p g
      have h1 : f g = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * f 1 := by
        have hfk : f k = f 1 := by
          have := hfK' k hk 1
          rwa [one_mul] at this
        rw [hg, apply_borelElem_mul_of_mem_principalSeries p hfB, hfk]
      have h2 : sphericalVector p μ₁ μ₂ g
          = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ :=
        sphericalVector_eq_of_decomp p h₁ h₂ hk hg
      show f g = f 1 * sphericalVector p μ₁ μ₂ g
      rw [h1, h2]
      ring
    rw [hkey]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  ·
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact sphericalVector_mem p h₁ h₂

theorem finrank_principalSeries_inf_rightInvariant_integral_eq_one
    (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    Module.finrank ℂ
      ↥(principalSeries p μ₁ μ₂
          ⊓ rightInvariantFunctions p (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) = 1 := by
  rw [principalSeries_inf_rightInvariant_integral_eq_span p h₁ h₂]
  exact finrank_span_singleton (sphericalVector_ne_zero p h₁ h₂)

theorem principalSeries_inf_rightInvariant_integral_eq_bot
    (hram : ¬ IsUnramified p μ₁ ∨ ¬ IsUnramified p μ₂) :
    principalSeries p μ₁ μ₂
        ⊓ rightInvariantFunctions p (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  obtain ⟨hfB, hfK⟩ := Submodule.mem_inf.mp hf
  have hfK' := (mem_rightInvariantFunctions_iff p).mp hfK

  have hf1 : f 1 = 0 := by
    rcases hram with h₁ | h₂
    ·
      have h₁' : ∃ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 ∧ μ₁ u ≠ 1 := by
        by_contra hcon
        apply h₁
        intro u hu
        by_contra hne
        exact hcon ⟨u, hu, hne⟩
      obtain ⟨u, hu_norm, hu_ne⟩ := h₁'
      have hmem : borelElem p u 1 0 ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by
        rw [borelElem_mem_integralSubgroup_iff]
        exact ⟨hu_norm, by simp, by simp⟩
      have hK : f (borelElem p u 1 0) = f 1 := by
        have := hfK' _ hmem 1
        rwa [one_mul] at this
      have hB : f (borelElem p u 1 0) = (μ₁ u : ℂ) * f 1 := by
        have h := apply_borelElem_mul_of_mem_principalSeries p hfB u 1 0 1
        rw [mul_one, map_one, halfModulus_eq_one_of_norm_eq_one p hu_norm (by simp)] at h
        rw [h, Units.val_one, mul_one, mul_one]
      have hfactor : ((μ₁ u : ℂ) - 1) * f 1 = 0 := by
        rw [sub_mul, one_mul, ← hB, hK, sub_self]
      rcases mul_eq_zero.mp hfactor with h | h
      · exact absurd (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h)) hu_ne
      · exact h
    ·
      have h₂' : ∃ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 ∧ μ₂ u ≠ 1 := by
        by_contra hcon
        apply h₂
        intro u hu
        by_contra hne
        exact hcon ⟨u, hu, hne⟩
      obtain ⟨u, hu_norm, hu_ne⟩ := h₂'
      have hmem : borelElem p 1 u 0 ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by
        rw [borelElem_mem_integralSubgroup_iff]
        exact ⟨by simp, hu_norm, by simp⟩
      have hK : f (borelElem p 1 u 0) = f 1 := by
        have := hfK' _ hmem 1
        rwa [one_mul] at this
      have hB : f (borelElem p 1 u 0) = (μ₂ u : ℂ) * f 1 := by
        have h := apply_borelElem_mul_of_mem_principalSeries p hfB 1 u 0 1
        rw [mul_one, map_one, halfModulus_eq_one_of_norm_eq_one p (by simp) hu_norm] at h
        rw [h, Units.val_one, one_mul, mul_one]
      have hfactor : ((μ₂ u : ℂ) - 1) * f 1 = 0 := by
        rw [sub_mul, one_mul, ← hB, hK, sub_self]
      rcases mul_eq_zero.mp hfactor with h | h
      · exact absurd (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h)) hu_ne
      · exact h

  refine eq_zero_of_forall_integral_eq_zero p hfB fun k hk => ?_
  have := hfK' k hk 1
  rw [one_mul] at this
  rw [this, hf1]

theorem finrank_principalSeries_inf_rightInvariant_integral_eq_zero
    (hram : ¬ IsUnramified p μ₁ ∨ ¬ IsUnramified p μ₂) :
    Module.finrank ℂ
      ↥(principalSeries p μ₁ μ₂
          ⊓ rightInvariantFunctions p (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) = 0 := by
  rw [principalSeries_inf_rightInvariant_integral_eq_bot p hram]
  exact finrank_bot ℂ _

end Spherical
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

section Gates

theorem principalSeries_one_one_ne_bot :
    principalSeries p (1 : ℚ_[p]ˣ →* ℂˣ) (1 : ℚ_[p]ˣ →* ℂˣ) ≠ ⊥ := by
  intro h
  have hmem := sphericalVector_mem p (isUnramified_one p) (isUnramified_one p)
  have hB : sphericalVector p 1 1 ∈ principalSeries p 1 1 := (Submodule.mem_inf.mp hmem).1
  rw [h, Submodule.mem_bot] at hB
  exact sphericalVector_ne_zero p (isUnramified_one p) (isUnramified_one p) hB

theorem const_one_notMem_principalSeries_one_one :
    (fun _ : GL (Fin 2) ℚ_[p] => (1 : ℂ))
      ∉ principalSeries p (1 : ℚ_[p]ˣ →* ℂˣ) (1 : ℚ_[p]ˣ →* ℂˣ) := by
  intro h
  obtain ⟨-, htr⟩ := (mem_principalSeries_iff p).mp h
  have hp0 : (p : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out (p := p.Prime)))
  have h1 := htr (Units.mk0 (p : ℚ_[p]) hp0) 1 0 1
  simp only [MonoidHom.one_apply, Units.val_one, one_mul, mul_one] at h1

  have h2 : ((Real.sqrt (‖(p : ℚ_[p])‖ / ‖((1 : ℚ_[p]ˣ) : ℚ_[p])‖) : ℝ) : ℂ) = 1 := h1.symm
  rw [Complex.ofReal_eq_one] at h2
  rw [Units.val_one, norm_one, div_one, Real.sqrt_eq_one] at h2
  exact absurd h2 (ne_of_lt Padic.norm_p_lt_one)

end Gates
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

namespace FLT
p2m_export "FLT" "SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"

theorem PSCarrier.fixedSubmodule_padicK1_zero_eq_bot_impl (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (hram : ¬ LocalNewvector.IsUnramified p μ₁ ∨ ¬ LocalNewvector.IsUnramified p μ₂) :
    LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p 0) (LocalNewvector.PSCarrier p μ₁ μ₂) = ⊥ :=
  by
  rw [LocalNewvector.padicK1_zero_eq_integralSubgroup]
  haveI := FLT.PrincipalSeriesGL2Padic.finiteDimensional_principalSeries_inf_rightInvariant_integral p μ₁ μ₂
  haveI : FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])
      (LocalNewvector.PSCarrier p μ₁ μ₂)) :=
    LinearEquiv.finiteDimensional
      (LocalNewvector.PSCarrier.fixedEquiv p μ₁ μ₂ (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])).symm
  rw [← Submodule.finrank_eq_zero, LocalNewvector.PSCarrier.finrank_fixed_eq]
  exact FLT.PrincipalSeriesGL2Padic.finrank_principalSeries_inf_rightInvariant_integral_eq_zero p hram

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot.LocalGL2"

#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.fixedSubmodule_padicK1_zero_eq_bot_impl

theorem solution (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (hram : ¬ LocalNewvector.IsUnramified p μ₁ ∨ ¬ LocalNewvector.IsUnramified p μ₂) :
    LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p 0) (LocalNewvector.PSCarrier p μ₁ μ₂) = ⊥ := by
  apply FLT.PrincipalSeriesGL2Padic.PSCarrier.fixedSubmodule_padicK1_zero_eq_bot_impl <;> assumption

end S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot
end P2MW
export P2MW.S_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_eq_bot (solution)
