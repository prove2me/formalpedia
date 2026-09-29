-- Prove2me | solution 1 for LocalNewvector.PSCarrier.hasNewvectorConductor_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3769ff68-7ff3-5882-be75-1607a050180a

import Definitions.Def_RepTheory_SmoothVectors
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_IntegralSubgroupCompact
import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Theorems.Thm_LocalNewvector_gl2CongruenceSubgroup_le_padicK1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add

set_option autoImplicit false

open Matrix

namespace LocalGL2
p2m_export "LocalGL2" "unipotentR unipotentInt weylInt weylInt_mem coe_weylInt integralSubgroup mem_integralSubgroup_iff exists_entry_eq_of_mem_integralSubgroup"
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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

set_option autoImplicit false

open Matrix
open scoped Topology

noncomputable section

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.isOpen_coe_gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

section HalfModulus

end HalfModulus
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

section PrincipalSeries

theorem smul_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} (g : GL (Fin 2) ℚ_[p])
    (f : RightTranslationFn (GL (Fin 2) ℚ_[p]) ℂ)
    (hf : RightTranslationFn.toFun f ∈ principalSeries p μ₁ μ₂) :
    RightTranslationFn.toFun (g • f) ∈ principalSeries p μ₁ μ₂ :=
  rightTranslate_mem_principalSeries p hf g

end PrincipalSeries
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2"

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.isOpen_coe_gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"

open LocalNewvector

variable (p : ℕ) [Fact p.Prime]

def IntegralBorelLaw (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)
    (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ) : Prop :=
  ∀ (u₁ u₂ : ℚ_[p]ˣ) (x : ℚ_[p])
    (hu : borelElem p u₁ u₂ x ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])
    (k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])),
    ψ (⟨borelElem p u₁ u₂ x, hu⟩ * k) = (μ₁ u₁ : ℂ) * (μ₂ u₂ : ℂ) * ψ k

theorem isLocallyConstant_restrict_of_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂) :
    IsLocallyConstant fun k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) =>
      f (k : GL (Fin 2) ℚ_[p]) :=
  (isLocallyConstant_of_mem_principalSeries p hf).comp_continuous continuous_subtype_val

theorem integralBorelLaw_restrict_of_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂) :
    IntegralBorelLaw p μ₁ μ₂
      fun k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) => f (k : GL (Fin 2) ℚ_[p]) := by
  intro u₁ u₂ x hu k
  have h := apply_borelElem_mul_of_mem_integral p hf hu (k : GL (Fin 2) ℚ_[p])
  simpa using h

def extendIntegral (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)
    (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ) (g : GL (Fin 2) ℚ_[p]) : ℂ :=
  (μ₁ (exists_iwasawa_borelElem p g).choose : ℂ)
    * (μ₂ (exists_iwasawa_borelElem p g).choose_spec.choose : ℂ)
    * halfModulus p (exists_iwasawa_borelElem p g).choose
        (exists_iwasawa_borelElem p g).choose_spec.choose
    * ψ ⟨(exists_iwasawa_borelElem p g).choose_spec.choose_spec.choose_spec.choose,
        (exists_iwasawa_borelElem p g).choose_spec.choose_spec.choose_spec.choose_spec.1⟩

theorem extendIntegral_spec (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)
    (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ) (g : GL (Fin 2) ℚ_[p]) :
    ∃ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (k : GL (Fin 2) ℚ_[p])
      (hk : k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]),
      g = borelElem p a₁ a₂ x * k ∧
        extendIntegral p μ₁ μ₂ ψ g
          = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * ψ ⟨k, hk⟩ :=
  ⟨(exists_iwasawa_borelElem p g).choose,
    (exists_iwasawa_borelElem p g).choose_spec.choose,
    (exists_iwasawa_borelElem p g).choose_spec.choose_spec.choose,
    (exists_iwasawa_borelElem p g).choose_spec.choose_spec.choose_spec.choose,
    (exists_iwasawa_borelElem p g).choose_spec.choose_spec.choose_spec.choose_spec.1,
    (exists_iwasawa_borelElem p g).choose_spec.choose_spec.choose_spec.choose_spec.2,
    rfl⟩

theorem extendIntegral_eq_of_decomp {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ} (hlaw : IntegralBorelLaw p μ₁ μ₂ ψ)
    {g : GL (Fin 2) ℚ_[p]} {a₁ a₂ : ℚ_[p]ˣ} {x : ℚ_[p]} {k : GL (Fin 2) ℚ_[p]}
    (hk : k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) (hg : g = borelElem p a₁ a₂ x * k) :
    extendIntegral p μ₁ μ₂ ψ g
      = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * ψ ⟨k, hk⟩ := by
  obtain ⟨A₁, A₂, X, K, hK, hgA, hval⟩ := extendIntegral_spec p μ₁ μ₂ ψ g
  rw [hval]

  have hcomp : borelElem p A₁ A₂ X * K = borelElem p a₁ a₂ x * k := hgA.symm.trans hg
  have hquot : (borelElem p A₁ A₂ X)⁻¹ * borelElem p a₁ a₂ x = K * k⁻¹ := by
    calc (borelElem p A₁ A₂ X)⁻¹ * borelElem p a₁ a₂ x
        = (borelElem p A₁ A₂ X)⁻¹ * (borelElem p a₁ a₂ x * k * k⁻¹) := by
          rw [mul_inv_cancel_right]
      _ = (borelElem p A₁ A₂ X)⁻¹ * (borelElem p A₁ A₂ X * K * k⁻¹) := by rw [hcomp]
      _ = K * k⁻¹ := by rw [mul_assoc, inv_mul_cancel_left]
  have hquotmem : (borelElem p A₁ A₂ X)⁻¹ * borelElem p a₁ a₂ x
      ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by
    rw [hquot]
    exact mul_mem hK (inv_mem hk)

  obtain ⟨z, hz⟩ : ∃ z : ℚ_[p], (borelElem p A₁ A₂ X)⁻¹ * borelElem p a₁ a₂ x
      = borelElem p (A₁⁻¹ * a₁) (A₂⁻¹ * a₂) z := by
    rw [borelElem_inv, borelElem_mul]
    exact ⟨_, rfl⟩
  rw [hz] at hquot hquotmem
  obtain ⟨hn₁, hn₂⟩ := norm_eq_one_of_borelElem_mem_integral p hquotmem

  have hlawK : ψ ⟨K, hK⟩ = (μ₁ (A₁⁻¹ * a₁) : ℂ) * (μ₂ (A₂⁻¹ * a₂) : ℂ) * ψ ⟨k, hk⟩ := by
    have h := hlaw (A₁⁻¹ * a₁) (A₂⁻¹ * a₂) z hquotmem ⟨k, hk⟩
    have hsub : (⟨borelElem p (A₁⁻¹ * a₁) (A₂⁻¹ * a₂) z, hquotmem⟩ :
          ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) * ⟨k, hk⟩ = ⟨K, hK⟩ := by
      apply Subtype.ext
      show borelElem p (A₁⁻¹ * a₁) (A₂⁻¹ * a₂) z * k = K
      rw [hquot, inv_mul_cancel_right]
    rw [hsub] at h
    exact h

  have hμ₁ : (μ₁ A₁ : ℂ) * (μ₁ (A₁⁻¹ * a₁) : ℂ) = (μ₁ a₁ : ℂ) := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have hμ₂ : (μ₂ A₂ : ℂ) * (μ₂ (A₂⁻¹ * a₂) : ℂ) = (μ₂ a₂ : ℂ) := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have hnormA₁ : ‖(A₁ : ℚ_[p])‖ = ‖(a₁ : ℚ_[p])‖ := by
    have hone : ‖((A₁⁻¹ * a₁ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := hn₁
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv] at hone
    have hA : ‖(A₁ : ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr A₁.ne_zero
    field_simp at hone
    linarith
  have hnormA₂ : ‖(A₂ : ℚ_[p])‖ = ‖(a₂ : ℚ_[p])‖ := by
    have hone : ‖((A₂⁻¹ * a₂ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := hn₂
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv] at hone
    have hA : ‖(A₂ : ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr A₂.ne_zero
    field_simp at hone
    linarith
  rw [hlawK, halfModulus_congr p hnormA₁ hnormA₂, ← hμ₁, ← hμ₂]
  ring

theorem extendIntegral_apply_of_mem_integral {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ} (hlaw : IntegralBorelLaw p μ₁ μ₂ ψ)
    {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) :
    extendIntegral p μ₁ μ₂ ψ k = ψ ⟨k, hk⟩ := by
  have hg : k = borelElem p 1 1 0 * k := by rw [borelElem_one, one_mul]
  rw [extendIntegral_eq_of_decomp p hlaw hk hg]
  simp

private theorem exists_ambient_open_const_of_isLocallyConstant
    {ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ} (hlc : IsLocallyConstant ψ)
    {k₀ : GL (Fin 2) ℚ_[p]} (hk₀ : k₀ ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) :
    ∃ W : Set (GL (Fin 2) ℚ_[p]), IsOpen W ∧ k₀ ∈ W ∧
      (∀ y ∈ W, y ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) ∧
      ∀ (y : GL (Fin 2) ℚ_[p]) (hy : y ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]),
        y ∈ W → ψ ⟨y, hy⟩ = ψ ⟨k₀, hk₀⟩ := by
  obtain ⟨U, hUopen, hkU, hUconst⟩ := hlc.exists_open ⟨k₀, hk₀⟩
  refine ⟨Subtype.val '' U,
    (FLT.SpectralSide.isOpen_coe_integralSubgroup_padic p).isOpenMap_subtype_val U hUopen,
    ⟨⟨k₀, hk₀⟩, hkU, rfl⟩, ?_, ?_⟩
  · rintro y ⟨y', _, rfl⟩
    exact y'.2
  · rintro y hy ⟨y', hy'U, hy'eq⟩
    have hsub : (⟨y, hy⟩ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) = y' :=
      Subtype.ext hy'eq.symm
    rw [hsub]
    exact hUconst y' hy'U

theorem isLocallyConstant_extendIntegral {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ} (hlaw : IntegralBorelLaw p μ₁ μ₂ ψ)
    (hlc : IsLocallyConstant ψ) :
    IsLocallyConstant (extendIntegral p μ₁ μ₂ ψ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  obtain ⟨a₁, a₂, x, k₀, hk₀, hg₀⟩ := exists_iwasawa_borelElem p g₀
  obtain ⟨W, hWopen, hk₀W, hWsub, hWconst⟩ :=
    exists_ambient_open_const_of_isLocallyConstant p hlc hk₀
  refine ⟨(fun y => (borelElem p a₁ a₂ x)⁻¹ * y) ⁻¹' W,
    hWopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · show (borelElem p a₁ a₂ x)⁻¹ * g₀ ∈ W
    rw [hg₀, inv_mul_cancel_left]
    exact hk₀W
  · intro y hy
    have hyW : (borelElem p a₁ a₂ x)⁻¹ * y ∈ W := hy
    have hymem : (borelElem p a₁ a₂ x)⁻¹ * y ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
      hWsub _ hyW
    have hydecomp : y = borelElem p a₁ a₂ x * ((borelElem p a₁ a₂ x)⁻¹ * y) := by
      rw [mul_inv_cancel_left]
    rw [extendIntegral_eq_of_decomp p hlaw hymem hydecomp,
      extendIntegral_eq_of_decomp p hlaw hk₀ hg₀, hWconst _ hymem hyW]

theorem extendIntegral_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ} (hlaw : IntegralBorelLaw p μ₁ μ₂ ψ)
    (hlc : IsLocallyConstant ψ) :
    extendIntegral p μ₁ μ₂ ψ ∈ principalSeries p μ₁ μ₂ := by
  refine (mem_principalSeries_iff p).mpr
    ⟨isLocallyConstant_extendIntegral p hlaw hlc, fun a₁ a₂ x g => ?_⟩
  obtain ⟨b₁, b₂, y, k, hk, hg⟩ := exists_iwasawa_borelElem p g
  have hg' : borelElem p a₁ a₂ x * g
      = borelElem p (a₁ * b₁) (a₂ * b₂) ((a₁ : ℚ_[p]) * y + x * (b₂ : ℚ_[p])) * k := by
    rw [hg, ← mul_assoc, borelElem_mul]
  rw [extendIntegral_eq_of_decomp p hlaw hk hg', extendIntegral_eq_of_decomp p hlaw hk hg,
    map_mul, map_mul, halfModulus_mul, Units.val_mul, Units.val_mul]
  ring

theorem existsUnique_mem_principalSeries_of_restriction {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ}
    (hlc : IsLocallyConstant ψ) (hlaw : IntegralBorelLaw p μ₁ μ₂ ψ) :
    ∃! F : GL (Fin 2) ℚ_[p] → ℂ, F ∈ principalSeries p μ₁ μ₂ ∧
      ∀ (k : GL (Fin 2) ℚ_[p]) (hk : k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]),
        F k = ψ ⟨k, hk⟩ := by
  refine ⟨extendIntegral p μ₁ μ₂ ψ,
    ⟨extendIntegral_mem_principalSeries p hlaw hlc,
      fun k hk => extendIntegral_apply_of_mem_integral p hlaw hk⟩, ?_⟩
  rintro F ⟨hFmem, hFres⟩
  refine eq_of_forall_integral_eq p hFmem (extendIntegral_mem_principalSeries p hlaw hlc)
    fun k hk => ?_
  rw [hFres k hk, extendIntegral_apply_of_mem_integral p hlaw hk]

theorem existsUnique_mem_principalSeries_restrict_eq {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {φ : GL (Fin 2) ℚ_[p] → ℂ}
    (hlc : IsLocallyConstant fun k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) =>
      φ (k : GL (Fin 2) ℚ_[p]))
    (hlaw : ∀ (u₁ u₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (k : GL (Fin 2) ℚ_[p]),
      borelElem p u₁ u₂ x ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] →
      k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] →
      φ (borelElem p u₁ u₂ x * k) = (μ₁ u₁ : ℂ) * (μ₂ u₂ : ℂ) * φ k) :
    ∃! F : GL (Fin 2) ℚ_[p] → ℂ, F ∈ principalSeries p μ₁ μ₂ ∧
      ∀ k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p], F k = φ k := by
  have hlaw' : IntegralBorelLaw p μ₁ μ₂
      fun k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) => φ (k : GL (Fin 2) ℚ_[p]) := by
    intro u₁ u₂ x hu k
    have h := hlaw u₁ u₂ x (k : GL (Fin 2) ℚ_[p]) hu k.2
    simpa using h
  obtain ⟨F, ⟨hFmem, hFres⟩, hFuniq⟩ :=
    existsUnique_mem_principalSeries_of_restriction p hlc hlaw'
  exact ⟨F, ⟨hFmem, fun k hk => hFres k hk⟩,
    fun G hG => hFuniq G ⟨hG.1, fun k hk => hG.2 k hk⟩⟩

theorem exists_mem_principalSeries_restrict_eq_iff {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {φ : GL (Fin 2) ℚ_[p] → ℂ} :
    (∃ F ∈ principalSeries p μ₁ μ₂,
        ∀ k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p], F k = φ k)
      ↔ (IsLocallyConstant fun k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) =>
            φ (k : GL (Fin 2) ℚ_[p])) ∧
          ∀ (u₁ u₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (k : GL (Fin 2) ℚ_[p]),
            borelElem p u₁ u₂ x ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] →
            k ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] →
            φ (borelElem p u₁ u₂ x * k) = (μ₁ u₁ : ℂ) * (μ₂ u₂ : ℂ) * φ k := by
  constructor
  · rintro ⟨F, hFmem, hFres⟩
    constructor
    · have hres : (fun k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) =>
            φ (k : GL (Fin 2) ℚ_[p]))
          = fun k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) => F (k : GL (Fin 2) ℚ_[p]) :=
        funext fun k => (hFres (k : GL (Fin 2) ℚ_[p]) k.2).symm
      rw [hres]
      exact isLocallyConstant_restrict_of_mem_principalSeries p hFmem
    · intro u₁ u₂ x k hu hk
      rw [← hFres _ (mul_mem hu hk), ← hFres _ hk]
      exact apply_borelElem_mul_of_mem_integral p hFmem hu k
  · rintro ⟨hlc, hlaw⟩
    obtain ⟨F, hF, -⟩ := existsUnique_mem_principalSeries_restrict_eq p hlc hlaw
    exact ⟨F, hF.1, hF.2⟩

def restrictionSpace (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) :
    Submodule ℂ (↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ) where
  carrier := {ψ | IsLocallyConstant ψ ∧ IntegralBorelLaw p μ₁ μ₂ ψ}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ _ _ _ _ => by simp⟩
  add_mem' := by
    intro ψ₁ ψ₂ h₁ h₂
    obtain ⟨h₁lc, h₁law⟩ := h₁
    obtain ⟨h₂lc, h₂law⟩ := h₂
    refine ⟨h₁lc.comp₂ h₂lc (· + ·), fun u₁ u₂ x hu k => ?_⟩
    show ψ₁ _ + ψ₂ _ = _ * (ψ₁ k + ψ₂ k)
    rw [h₁law u₁ u₂ x hu k, h₂law u₁ u₂ x hu k]
    ring
  smul_mem' := by
    intro c ψ hψ
    obtain ⟨hlc, hlaw⟩ := hψ
    refine ⟨hlc.comp (c * ·), fun u₁ u₂ x hu k => ?_⟩
    show c * ψ _ = _ * (c * ψ k)
    rw [hlaw u₁ u₂ x hu k]
    ring

theorem mem_restrictionSpace_iff {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ} :
    ψ ∈ restrictionSpace p μ₁ μ₂ ↔ IsLocallyConstant ψ ∧ IntegralBorelLaw p μ₁ μ₂ ψ :=
  Iff.rfl

theorem restrict_mem_restrictionSpace {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂) :
    (fun k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) => f (k : GL (Fin 2) ℚ_[p]))
      ∈ restrictionSpace p μ₁ μ₂ :=
  (mem_restrictionSpace_iff p).mpr
    ⟨isLocallyConstant_restrict_of_mem_principalSeries p hf,
      integralBorelLaw_restrict_of_mem_principalSeries p hf⟩

def restrictIntegralLinear (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) :
    ↥(principalSeries p μ₁ μ₂) →ₗ[ℂ] ↥(restrictionSpace p μ₁ μ₂) where
  toFun f := ⟨fun k => (f : GL (Fin 2) ℚ_[p] → ℂ) (k : GL (Fin 2) ℚ_[p]),
    restrict_mem_restrictionSpace p f.2⟩
  map_add' f g := by
    apply Subtype.ext
    funext k
    simp
  map_smul' c f := by
    apply Subtype.ext
    funext k
    simp

@[scoped simp] theorem restrictIntegralLinear_apply {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (f : ↥(principalSeries p μ₁ μ₂)) (k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) :
    (restrictIntegralLinear p μ₁ μ₂ f : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ) k
      = (f : GL (Fin 2) ℚ_[p] → ℂ) (k : GL (Fin 2) ℚ_[p]) :=
  rfl

theorem restrictIntegralLinear_injective (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) :
    Function.Injective (restrictIntegralLinear p μ₁ μ₂) := by
  intro f₁ f₂ h
  apply Subtype.ext
  refine eq_of_forall_integral_eq p f₁.2 f₂.2 fun k hk => ?_
  have h' := congrFun (congrArg (Subtype.val) h) ⟨k, hk⟩
  simpa using h'

theorem restrictIntegralLinear_surjective (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) :
    Function.Surjective (restrictIntegralLinear p μ₁ μ₂) := by
  intro ψ
  obtain ⟨hlc, hlaw⟩ := (mem_restrictionSpace_iff p).mp ψ.2
  refine ⟨⟨extendIntegral p μ₁ μ₂ (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ),
    extendIntegral_mem_principalSeries p hlaw hlc⟩, ?_⟩
  apply Subtype.ext
  funext k
  show extendIntegral p μ₁ μ₂ (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ)
      (k : GL (Fin 2) ℚ_[p]) = (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ) k
  rw [extendIntegral_apply_of_mem_integral p hlaw k.2]

theorem restrictIntegralLinear_bijective (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) :
    Function.Bijective (restrictIntegralLinear p μ₁ μ₂) :=
  ⟨restrictIntegralLinear_injective p μ₁ μ₂, restrictIntegralLinear_surjective p μ₁ μ₂⟩

def restrictIntegralEquiv (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) :
    ↥(principalSeries p μ₁ μ₂) ≃ₗ[ℂ] ↥(restrictionSpace p μ₁ μ₂) :=
  LinearEquiv.ofBijective (restrictIntegralLinear p μ₁ μ₂)
    (restrictIntegralLinear_bijective p μ₁ μ₂)

@[scoped simp] theorem restrictIntegralEquiv_apply {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (f : ↥(principalSeries p μ₁ μ₂)) (k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) :
    (restrictIntegralEquiv p μ₁ μ₂ f : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ) k
      = (f : GL (Fin 2) ℚ_[p] → ℂ) (k : GL (Fin 2) ℚ_[p]) :=
  rfl

theorem restrictIntegralEquiv_symm_apply {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (ψ : ↥(restrictionSpace p μ₁ μ₂)) :
    ((restrictIntegralEquiv p μ₁ μ₂).symm ψ : GL (Fin 2) ℚ_[p] → ℂ)
      = extendIntegral p μ₁ μ₂ (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ) := by
  obtain ⟨hlc, hlaw⟩ := (mem_restrictionSpace_iff p).mp ψ.2
  have hmem : extendIntegral p μ₁ μ₂ (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ)
      ∈ principalSeries p μ₁ μ₂ := extendIntegral_mem_principalSeries p hlaw hlc
  have hkey : (restrictIntegralEquiv p μ₁ μ₂).symm ψ
      = ⟨extendIntegral p μ₁ μ₂ (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ), hmem⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    funext k
    show (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ) k
        = extendIntegral p μ₁ μ₂ (ψ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) → ℂ)
            (k : GL (Fin 2) ℚ_[p])
    rw [extendIntegral_apply_of_mem_integral p hlaw k.2]
  rw [hkey]

theorem integralBorelLaw_const_one {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    IntegralBorelLaw p μ₁ μ₂ fun _ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) => (1 : ℂ) := by
  intro u₁ u₂ x hu k
  obtain ⟨hn₁, hn₂⟩ := norm_eq_one_of_borelElem_mem_integral p hu
  rw [h₁ u₁ hn₁, h₂ u₂ hn₂]
  simp

theorem const_one_mem_restrictionSpace_one_one :
    (fun _ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) => (1 : ℂ))
      ∈ restrictionSpace p (1 : ℚ_[p]ˣ →* ℂˣ) (1 : ℚ_[p]ˣ →* ℂˣ) :=
  (mem_restrictionSpace_iff p).mpr
    ⟨IsLocallyConstant.const 1,
      integralBorelLaw_const_one p (isUnramified_one p) (isUnramified_one p)⟩

theorem extendIntegral_const_one_eq_sphericalVector {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    extendIntegral p μ₁ μ₂ (fun _ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) => (1 : ℂ))
      = sphericalVector p μ₁ μ₂ := by
  refine eq_of_forall_integral_eq p
    (extendIntegral_mem_principalSeries p (integralBorelLaw_const_one p h₁ h₂)
      (IsLocallyConstant.const 1))
    ((Submodule.mem_inf.mp (sphericalVector_mem p h₁ h₂)).1) fun k hk => ?_
  have hg : k = borelElem p 1 1 0 * k := by rw [borelElem_one, one_mul]
  rw [extendIntegral_apply_of_mem_integral p (integralBorelLaw_const_one p h₁ h₂) hk,
    sphericalVector_eq_of_decomp p h₁ h₂ hk hg]
  simp

theorem extendIntegral_one_one_const_one_ne_zero :
    extendIntegral p (1 : ℚ_[p]ˣ →* ℂˣ) (1 : ℚ_[p]ˣ →* ℂˣ)
      (fun _ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) => (1 : ℂ)) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  rw [extendIntegral_apply_of_mem_integral p
    (integralBorelLaw_const_one p (isUnramified_one p) (isUnramified_one p))
    (one_mem (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]))] at h1
  exact one_ne_zero h1

theorem extendIntegral_one_one_const_one_ne_const_one :
    extendIntegral p (1 : ℚ_[p]ˣ →* ℂˣ) (1 : ℚ_[p]ˣ →* ℂˣ)
      (fun _ : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) => (1 : ℂ))
      ≠ fun _ : GL (Fin 2) ℚ_[p] => (1 : ℂ) := by
  intro h
  apply const_one_notMem_principalSeries_one_one p
  rw [← h]
  exact extendIntegral_mem_principalSeries p
    (integralBorelLaw_const_one p (isUnramified_one p) (isUnramified_one p))
    (IsLocallyConstant.const 1)

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT"

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.isOpen_coe_gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"

open LocalNewvector

open FLT.SmoothVectors

section RepCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

namespace PSCarrier

open LocalNewvector.PSCarrier

theorem isSmoothVector_carrier (f : PSCarrier p μ₁ μ₂) :
    IsSmoothVector (GL (Fin 2) ℚ_[p]) f := by
  have hmk : IsSmoothVector (GL (Fin 2) ℚ_[p]) (RightTranslationFn.mk (toFn p μ₁ μ₂ f)) :=
    isSmoothVector_of_mem_principalSeries p (toFn_mem p μ₁ μ₂ f)
  rw [isSmoothVector_iff_isOpen_stabilizer] at hmk ⊢
  have hstab : MulAction.stabilizer (GL (Fin 2) ℚ_[p]) f
      = MulAction.stabilizer (GL (Fin 2) ℚ_[p]) (RightTranslationFn.mk (toFn p μ₁ μ₂ f)) := by
    ext g
    simp only [MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      refine RightTranslationFn.ext fun y => ?_
      exact congrArg (fun z => toFn p μ₁ μ₂ z y) h
    · intro h
      refine ext p μ₁ μ₂ fun y => ?_
      exact congrArg (fun z => RightTranslationFn.toFun z y) h
  rw [hstab]
  exact hmk

scoped instance : ContinuousSMulDiscrete (GL (Fin 2) ℚ_[p]) (PSCarrier p μ₁ μ₂) :=
  continuousSMulDiscrete_iff_forall_isSmoothVector.mpr
    (fun f => isSmoothVector_carrier p μ₁ μ₂ f)

theorem hasFiniteLevelFixed : LocalNewvector.HasFiniteLevelFixed p (PSCarrier p μ₁ μ₂) := by
  intro n
  haveI := finiteDimensional_principalSeries_inf_rightInvariant p μ₁ μ₂
    (gl2CongruenceSubgroup p n) (isOpen_coe_gl2CongruenceSubgroup p n)
  exact Module.Finite.equiv (fixedEquiv p μ₁ μ₂ (gl2CongruenceSubgroup p n)).symm

theorem halfModulus_same (u : ℚ_[p]ˣ) : halfModulus p u u = 1 := by
  have h : ‖(u : ℚ_[p])‖ / ‖(u : ℚ_[p])‖ = 1 :=
    div_self (norm_ne_zero_iff.mpr u.ne_zero)
  simp only [halfModulus, h, Real.sqrt_one, Complex.ofReal_one]

theorem centralGL_eq_borelElem (u : ℚ_[p]ˣ) :
    LocalNewvector.centralGL p u = borelElem p u u 0 := by
  refine Units.ext ?_
  have h1 : ((LocalNewvector.centralGL p u : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = algebraMap ℚ_[p] (Matrix (Fin 2) (Fin 2) ℚ_[p]) (u : ℚ_[p]) := rfl
  rw [h1, coe_borelElem, Matrix.algebraMap_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem isCentralCharacterRep :
    LocalNewvector.IsCentralCharacterRep p (PSCarrier p μ₁ μ₂) (μ₁ * μ₂) := by
  intro u f
  refine ext p μ₁ μ₂ fun y => ?_
  have hcomm : y * LocalNewvector.centralGL p u = LocalNewvector.centralGL p u * y := by
    refine Units.ext ?_
    simp only [Units.val_mul]
    exact (Algebra.commutes (u : ℚ_[p])
      ((y : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])).symm
  calc toFn p μ₁ μ₂ (LocalNewvector.centralGL p u • f) y
      = toFn p μ₁ μ₂ f (y * LocalNewvector.centralGL p u) := rfl
    _ = toFn p μ₁ μ₂ f (LocalNewvector.centralGL p u * y) := by rw [hcomm]
    _ = toFn p μ₁ μ₂ f (borelElem p u u 0 * y) := by rw [centralGL_eq_borelElem p u]
    _ = (μ₁ u : ℂ) * (μ₂ u : ℂ) * halfModulus p u u * toFn p μ₁ μ₂ f y :=
        apply_borelElem_mul_of_mem_principalSeries p (toFn_mem p μ₁ μ₂ f) u u 0 y
    _ = ((μ₁ * μ₂) u : ℂ) * toFn p μ₁ μ₂ f y := by
        rw [halfModulus_same p u, mul_one, MonoidHom.mul_apply, Units.val_mul]

def spherical (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) : PSCarrier p μ₁ μ₂ :=
  mk p μ₁ μ₂ ⟨sphericalVector p μ₁ μ₂,
    (Submodule.mem_inf.mp (sphericalVector_mem p h₁ h₂)).1⟩

theorem spherical_mem_fixed (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    spherical p μ₁ μ₂ h₁ h₂
      ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p 0) (PSCarrier p μ₁ μ₂) := by
  rw [LocalNewvector.mem_fixedSubmodule_iff]
  intro g hg
  rw [LocalNewvector.padicK1_zero_eq_integralSubgroup p] at hg
  refine ext p μ₁ μ₂ fun y => ?_
  exact (mem_rightInvariantFunctions_iff p).mp
    (Submodule.mem_inf.mp (sphericalVector_mem p h₁ h₂)).2 g hg y

theorem spherical_ne_zero (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    spherical p μ₁ μ₂ h₁ h₂ ≠ 0 := by
  intro h
  have h1 : toFn p μ₁ μ₂ (spherical p μ₁ μ₂ h₁ h₂) 1 = 0 := by rw [h]; rfl
  rw [show toFn p μ₁ μ₂ (spherical p μ₁ μ₂ h₁ h₂) 1 = sphericalVector p μ₁ μ₂ 1 from rfl,
    sphericalVector_one p h₁ h₂] at h1
  exact one_ne_zero h1

theorem hasNewvectorConductor_zero (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    LocalNewvector.HasNewvectorConductor p (PSCarrier p μ₁ μ₂) 0 := by
  constructor
  · rw [Submodule.ne_bot_iff]
    exact ⟨spherical p μ₁ μ₂ h₁ h₂, spherical_mem_fixed p μ₁ μ₂ h₁ h₂,
      spherical_ne_zero p μ₁ μ₂ h₁ h₂⟩
  · intro m hm
    exact absurd hm (Nat.not_lt_zero m)

theorem finrank_fixed_padicK1_zero_eq_one
    (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    Module.finrank ℂ
      ↥(LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p 0) (PSCarrier p μ₁ μ₂))
      = 1 := by
  rw [LocalNewvector.padicK1_zero_eq_integralSubgroup p]
  exact (finrank_fixed_eq p μ₁ μ₂ (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])).trans
    (finrank_principalSeries_inf_rightInvariant_integral_eq_one p h₁ h₂)

end PSCarrier
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end RepCarrier
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

section AuditE
variable (p : ℕ) [Fact p.Prime]
end AuditE
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.isOpen_coe_gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"

open LocalNewvector

variable (p : ℕ) [Fact p.Prime]

section CharConductor

end CharConductor
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.isOpen_coe_gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"

open LocalNewvector

section CasselmanStrata

variable (p : ℕ) [Fact p.Prime]

local notation:1024 "↑ₘ" A:1024 => ((A : GL (Fin 2) ℤ_[p]) : Matrix (Fin 2) (Fin 2) ℤ_[p])

def pIdeal (n : ℕ) : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p]) ^ n}

@[scoped simp] theorem pIdeal_zero : pIdeal p 0 = ⊤ := by
  rw [pIdeal, pow_zero, Ideal.span_singleton_one]

theorem pIdeal_antitone {m n : ℕ} (h : m ≤ n) : pIdeal p n ≤ pIdeal p m :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ h)

theorem mem_pIdeal_iff_norm_le {n : ℕ} {x : ℤ_[p]} :
    x ∈ pIdeal p n ↔ ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
  (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm

theorem mem_pIdeal_iff_le_valuation {n : ℕ} {x : ℤ_[p]} (hx : x ≠ 0) :
    x ∈ pIdeal p n ↔ n ≤ x.valuation :=
  PadicInt.mem_span_pow_iff_le_valuation x hx n

theorem ne_zero_of_not_mem_pIdeal {n : ℕ} {x : ℤ_[p]} (hx : x ∉ pIdeal p n) : x ≠ 0 :=
  fun h => hx (h ▸ Submodule.zero_mem _)

theorem pow_mul_mem_pIdeal_iff {i n : ℕ} {x : ℤ_[p]} :
    (p : ℤ_[p]) ^ i * x ∈ pIdeal p (i + n) ↔ x ∈ pIdeal p n := by
  by_cases hx : x = 0
  · subst hx; simp
  have hpi : (p : ℤ_[p]) ^ i ≠ 0 := pow_ne_zero _ (NeZero.ne _)
  rw [mem_pIdeal_iff_le_valuation p (mul_ne_zero hpi hx), mem_pIdeal_iff_le_valuation p hx,
    PadicInt.valuation_p_pow_mul _ _ hx]
  omega

theorem not_isUnit_of_mem_pIdeal_one {x : ℤ_[p]} (hx : x ∈ pIdeal p 1) : ¬ IsUnit x := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Nat.Prime.one_lt (Fact.out (p := p.Prime)))
  have hlt : ‖x‖ < 1 :=
    ((mem_pIdeal_iff_norm_le p).mp hx).trans_lt (zpow_lt_one_of_neg₀ hp1 (by norm_num))
  exact mem_nonunits_iff.mp (PadicInt.mem_nonunits.mpr hlt)

theorem isUnit_diag_of_mem_pIdeal_one (k : GL (Fin 2) ℤ_[p]) (hc : ↑ₘk 1 0 ∈ pIdeal p 1) :
    IsUnit (↑ₘk 0 0) ∧ IsUnit (↑ₘk 1 1) := by
  have hdet : IsUnit (↑ₘk 0 0 * ↑ₘk 1 1 - ↑ₘk 0 1 * ↑ₘk 1 0) := by
    rw [← Matrix.det_fin_two, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  have hmax : ↑ₘk 0 0 * ↑ₘk 1 1 ∉ IsLocalRing.maximalIdeal ℤ_[p] := by
    intro hmem
    have hc' : ↑ₘk 0 1 * ↑ₘk 1 0 ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      Ideal.mul_mem_left _ _
        ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (not_isUnit_of_mem_pIdeal_one p hc)))
    exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.sub_mem _ hmem hc') hdet
  have had : IsUnit (↑ₘk 0 0 * ↑ₘk 1 1) := by
    by_contra h
    exact hmax ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h))
  exact ⟨isUnit_of_mul_isUnit_left had, isUnit_of_mul_isUnit_right had⟩

theorem valuation_coe_unit (w : ℤ_[p]ˣ) : (w : ℤ_[p]).valuation = 0 := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Nat.Prime.one_lt (Fact.out (p := p.Prime)))
  have h := PadicInt.norm_eq_zpow_neg_valuation (Units.ne_zero w)
  rw [PadicInt.norm_units] at h
  have h' : (p : ℝ) ^ (0 : ℤ) = (p : ℝ) ^ (-((w : ℤ_[p]).valuation : ℤ)) := by rw [zpow_zero]; exact h
  have := (zpow_right_inj₀ (zero_lt_one.trans hp1) hp1.ne').mp h'
  omega

theorem unitCoeff_unit_mul (w : ℤ_[p]ˣ) {x : ℤ_[p]} (hx : x ≠ 0) (hwx : (w : ℤ_[p]) * x ≠ 0) :
    PadicInt.unitCoeff hwx = w * PadicInt.unitCoeff hx := by
  have hval : ((w : ℤ_[p]) * x).valuation = x.valuation := by
    rw [PadicInt.valuation_mul (Units.ne_zero w) hx, valuation_coe_unit, zero_add]
  have hpv : (p : ℤ_[p]) ^ x.valuation ≠ 0 := pow_ne_zero _ (NeZero.ne _)
  apply Units.ext
  apply mul_right_cancel₀ hpv
  have h1 := PadicInt.unitCoeff_spec hwx
  have h2 := PadicInt.unitCoeff_spec hx
  rw [hval] at h1
  rw [Units.val_mul, mul_assoc, ← h2, ← h1]

theorem unitCoeff_mul_pow_eq {c : ℤ_[p]} (hc : c ≠ 0) {i : ℕ} (hi : c.valuation = i) :
    (PadicInt.unitCoeff hc : ℤ_[p]) * (p : ℤ_[p]) ^ i = c := by
  rw [← hi]; exact (PadicInt.unitCoeff_spec hc).symm

def unitLift : ℤ_[p]ˣ →* ℚ_[p]ˣ :=
  Units.map (algebraMap ℤ_[p] ℚ_[p] : ℤ_[p] →+* ℚ_[p]).toMonoidHom

@[scoped simp] theorem coe_unitLift (w : ℤ_[p]ˣ) :
    ((unitLift p w : ℚ_[p]ˣ) : ℚ_[p]) = ((w : ℤ_[p]) : ℚ_[p]) := rfl

theorem unitLift_mem_higherUnits {n : ℕ} {w : ℤ_[p]ˣ} (hw : (w : ℤ_[p]) - 1 ∈ pIdeal p n) :
    unitLift p w ∈ higherUnits p n := by
  refine ⟨?_, ?_⟩
  · rw [coe_unitLift, ← PadicInt.norm_def]
    exact PadicInt.norm_units w
  · rcases Nat.eq_zero_or_pos n with rfl | _
    · exact Or.inl rfl
    · right
      rw [coe_unitLift, ← PadicInt.coe_one, ← PadicInt.coe_sub, ← PadicInt.norm_def]
      exact (mem_pIdeal_iff_norm_le p).mp hw

theorem exists_unitLift_eq_of_mem_higherUnits {n : ℕ} {u : ℚ_[p]ˣ} (hu : u ∈ higherUnits p n) :
    ∃ w : ℤ_[p]ˣ, unitLift p w = u ∧ (w : ℤ_[p]) - 1 ∈ pIdeal p n := by
  obtain ⟨hnorm, hball⟩ := hu
  refine ⟨PadicInt.mkUnits hnorm, Units.ext rfl, ?_⟩
  rcases hball with rfl | hball
  · simp
  · rw [mem_pIdeal_iff_norm_le, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
    exact hball

theorem apply_unitLift_eq_one {μ : ℚ_[p]ˣ →* ℂˣ} {c : ℕ} (h : HasCharConductor p μ c)
    {n : ℕ} (hcn : c ≤ n) {w : ℤ_[p]ˣ} (hw : (w : ℤ_[p]) - 1 ∈ pIdeal p n) :
    μ (unitLift p w) = 1 :=
  h.1 _ (higherUnits_antitone p hcn (unitLift_mem_higherUnits p hw))

theorem exists_unit_apply_ne_one {μ : ℚ_[p]ˣ →* ℂˣ} {c : ℕ} (h : HasCharConductor p μ c)
    {n : ℕ} (hn : n < c) :
    ∃ w : ℤ_[p]ˣ, (w : ℤ_[p]) - 1 ∈ pIdeal p n ∧ μ (unitLift p w) ≠ 1 := by
  obtain ⟨u, hu, hne⟩ := h.2 n hn
  obtain ⟨w, rfl, hw⟩ := exists_unitLift_eq_of_mem_higherUnits p hu
  exact ⟨w, hw, hne⟩

def borelInt (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) : GL (Fin 2) ℤ_[p] :=
  Matrix.GeneralLinearGroup.mk'' !![(u₁ : ℤ_[p]), x; 0, (u₂ : ℤ_[p])]
    (by rw [Matrix.det_fin_two_of, mul_zero, sub_zero]; exact u₁.isUnit.mul u₂.isUnit)

@[scoped simp] theorem coe_borelInt (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) :
    ↑ₘ(borelInt p u₁ u₂ x) = !![(u₁ : ℤ_[p]), x; 0, (u₂ : ℤ_[p])] := rfl

theorem det_borelInt (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) :
    Matrix.GeneralLinearGroup.det (borelInt p u₁ u₂ x) = u₁ * u₂ :=
  Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_borelInt, Matrix.det_fin_two_of, Units.val_mul]
    ring)

theorem map_borelInt (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) (borelInt p u₁ u₂ x)
      = borelElem p (unitLift p u₁) (unitLift p u₂) (x : ℚ_[p]) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply, coe_borelInt, coe_borelElem]
  fin_cases i <;> fin_cases j <;> simp

theorem borelElem_unitLift_mem_integralSubgroup (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) :
    borelElem p (unitLift p u₁) (unitLift p u₂) (x : ℚ_[p]) ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  ⟨borelInt p u₁ u₂ x, map_borelInt p u₁ u₂ x⟩

theorem coe_inv_eq (k : GL (Fin 2) ℤ_[p]) :
    ↑ₘ(k⁻¹) = (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) •
      !![↑ₘk 1 1, -(↑ₘk 0 1); -(↑ₘk 1 0), ↑ₘk 0 0] := by
  have hdet : (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
      * (↑ₘk 0 0 * ↑ₘk 1 1 - ↑ₘk 0 1 * ↑ₘk 1 0) = 1 := by
    rw [← Matrix.det_fin_two, ← Matrix.GeneralLinearGroup.val_det_apply, Units.inv_mul]
  rw [Matrix.GeneralLinearGroup.coe_inv]
  refine Matrix.inv_eq_left_inv ?_
  generalize (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = D at hdet ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hdet | ring

theorem conj_borelInt_apply_one_zero (k : GL (Fin 2) ℤ_[p]) (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) :
    ↑ₘ(k⁻¹ * borelInt p u₁ u₂ x * k) 1 0
      = (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
          * (↑ₘk 1 0 * (↑ₘk 0 0 * ((u₂ : ℤ_[p]) - u₁) - x * ↑ₘk 1 0)) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_inv_eq, coe_borelInt]
  generalize (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = D
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem conj_borelInt_apply_one_one (k : GL (Fin 2) ℤ_[p]) (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) :
    ↑ₘ(k⁻¹ * borelInt p u₁ u₂ x * k) 1 1
      = (u₂ : ℤ_[p]) + (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
          * (↑ₘk 1 0 * (↑ₘk 0 1 * ((u₂ : ℤ_[p]) - u₁) - x * ↑ₘk 1 1)) := by
  have hdet : (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
      * (↑ₘk 0 0 * ↑ₘk 1 1 - ↑ₘk 0 1 * ↑ₘk 1 0) = 1 := by
    rw [← Matrix.det_fin_two, ← Matrix.GeneralLinearGroup.val_det_apply, Units.inv_mul]
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_inv_eq, coe_borelInt]
  generalize (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = D at hdet ⊢
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (u₂ : ℤ_[p]) * hdet

theorem map_mem_padicK1 {m : ℕ} {y : GL (Fin 2) ℤ_[p]}
    (h10 : ↑ₘy 1 0 ∈ pIdeal p m) (h11 : ↑ₘy 1 1 - 1 ∈ pIdeal p m) :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) y ∈ LocalNewvector.padicK1 p m :=
  LocalNewvector.mem_congruenceK1_iff.mpr ⟨y, rfl, h10, h11⟩

theorem apply_map_eq_zero_of_conj {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {f : GL (Fin 2) ℚ_[p] → ℂ}
    (hf : f ∈ principalSeries p μ₁ μ₂) {m : ℕ}
    (hri : f ∈ rightInvariantFunctions p (LocalNewvector.padicK1 p m))
    (k : GL (Fin 2) ℤ_[p]) (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p])
    (h10 : ↑ₘ(k⁻¹ * borelInt p u₁ u₂ x * k) 1 0 ∈ pIdeal p m)
    (h11 : ↑ₘ(k⁻¹ * borelInt p u₁ u₂ x * k) 1 1 - 1 ∈ pIdeal p m)
    (hχ : (μ₁ (unitLift p u₁) : ℂ) * μ₂ (unitLift p u₂) ≠ 1) :
    f (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k) = 0 := by
  have h1 := apply_borelElem_mul_of_mem_integral p hf
    (borelElem_unitLift_mem_integralSubgroup p u₁ u₂ x)
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k)
  have hgrp : k * (k⁻¹ * borelInt p u₁ u₂ x * k) = borelInt p u₁ u₂ x * k := by
    rw [mul_assoc, mul_inv_cancel_left]
  have h2 : Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k
        * Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) (k⁻¹ * borelInt p u₁ u₂ x * k)
      = borelElem p (unitLift p u₁) (unitLift p u₂) (x : ℚ_[p])
          * Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k := by
    rw [← map_mul, hgrp, map_mul, map_borelInt]
  have h3 := (mem_rightInvariantFunctions_iff p).mp hri _ (map_mem_padicK1 p h10 h11)
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k)
  rw [h2, h1] at h3
  have h4 : ((μ₁ (unitLift p u₁) : ℂ) * μ₂ (unitLift p u₂) - 1)
      * f (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k) = 0 := by
    rw [sub_mul, one_mul, h3, sub_self]
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd (sub_eq_zero.mp h) hχ
  · exact h

theorem apply_map_eq_zero_of_cases {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {n₁ n₂ : ℕ}
    (h₁ : HasCharConductor p μ₁ n₁) (h₂ : HasCharConductor p μ₂ n₂) {m : ℕ} {f : GL (Fin 2) ℚ_[p] → ℂ}
    (hps : f ∈ principalSeries p μ₁ μ₂) (hri : f ∈ rightInvariantFunctions p (LocalNewvector.padicK1 p m))
    (k : GL (Fin 2) ℤ_[p])
    (hA : ↑ₘk 1 0 ∈ pIdeal p m → m < n₂ ∨ 0 < n₁)
    (hB : ↑ₘk 1 0 ∉ pIdeal p m → (↑ₘk 1 0).valuation < n₂ ∨ m - (↑ₘk 1 0).valuation < n₁) :
    f (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k) = 0 := by
  by_cases hc : ↑ₘk 1 0 ∈ pIdeal p m
  ·
    rcases hA hc with hn₂ | hn₁
    · obtain ⟨w, hw, hne⟩ := exists_unit_apply_ne_one p h₂ hn₂
      refine apply_map_eq_zero_of_conj p hps hri k 1 w 0 ?_ ?_ (by simpa using hne)
      · rw [conj_borelInt_apply_one_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hc)
      · rw [conj_borelInt_apply_one_one, Units.val_one, add_sub_right_comm]
        exact Ideal.add_mem _ hw (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hc))
    · obtain ⟨w, -, hne⟩ := exists_unit_apply_ne_one p h₁ hn₁
      refine apply_map_eq_zero_of_conj p hps hri k w 1 0 ?_ ?_ (by simpa using hne)
      · rw [conj_borelInt_apply_one_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hc)
      · rw [conj_borelInt_apply_one_one, Units.val_one, add_sub_cancel_left]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hc)
  ·
    have hc0 : ↑ₘk 1 0 ≠ 0 := ne_zero_of_not_mem_pIdeal p hc
    have hi : (↑ₘk 1 0).valuation < m := by
      rwa [mem_pIdeal_iff_le_valuation p hc0, not_le] at hc
    have hcu : (PadicInt.unitCoeff hc0 : ℤ_[p]) * (p : ℤ_[p]) ^ (↑ₘk 1 0).valuation = ↑ₘk 1 0 :=
      unitCoeff_mul_pow_eq p hc0 rfl
    rcases hB hc with hin₂ | hmi
    · obtain ⟨w, hw, hne⟩ := exists_unit_apply_ne_one p h₂ hin₂
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hw
      have huc : (((PadicInt.unitCoeff hc0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (PadicInt.unitCoeff hc0 : ℤ_[p]) = 1 :=
        Units.inv_mul _

      have ht : ↑ₘk 0 0 * ((w : ℤ_[p]) - 1)
          - ↑ₘk 0 0 * s * (((PadicInt.unitCoeff hc0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ↑ₘk 1 0 = 0 := by
        linear_combination (-(↑ₘk 0 0)) * hs
          + (-(↑ₘk 0 0 * s * (p : ℤ_[p]) ^ (↑ₘk 1 0).valuation)) * huc
          + (↑ₘk 0 0 * s * (((PadicInt.unitCoeff hc0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) * hcu
      refine apply_map_eq_zero_of_conj p hps hri k 1 w
        (↑ₘk 0 0 * s * (((PadicInt.unitCoeff hc0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) ?_ ?_ (by simpa using hne)
      · rw [conj_borelInt_apply_one_zero, Units.val_one, ht, mul_zero, mul_zero]
        exact Submodule.zero_mem _
      · rw [conj_borelInt_apply_one_one, Units.val_one]
        have hdet : (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
            * (↑ₘk 0 0 * ↑ₘk 1 1 - ↑ₘk 0 1 * ↑ₘk 1 0) = 1 := by
          rw [← Matrix.det_fin_two, ← Matrix.GeneralLinearGroup.val_det_apply, Units.inv_mul]
        have hzero : (w : ℤ_[p]) + (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
            * (↑ₘk 1 0 * (↑ₘk 0 1 * ((w : ℤ_[p]) - 1)
              - ↑ₘk 0 0 * s * (((PadicInt.unitCoeff hc0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ↑ₘk 1 1)) - 1 = 0 := by
          linear_combination ((((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ↑ₘk 1 1) * ht
            - ((w : ℤ_[p]) - 1) * hdet
        rw [hzero]
        exact Submodule.zero_mem _
    · obtain ⟨w, hw, hne⟩ := exists_unit_apply_ne_one p h₁ hmi

      have hcw : ↑ₘk 1 0 * (1 - (w : ℤ_[p])) ∈ pIdeal p m := by
        have h' : (p : ℤ_[p]) ^ (↑ₘk 1 0).valuation * ((w : ℤ_[p]) - 1) ∈ pIdeal p m := by
          have := (pow_mul_mem_pIdeal_iff p (i := (↑ₘk 1 0).valuation)
            (n := m - (↑ₘk 1 0).valuation)).mpr hw
          rwa [Nat.add_sub_cancel' hi.le] at this
        have h'' : ↑ₘk 1 0 * (1 - (w : ℤ_[p]))
            = -(PadicInt.unitCoeff hc0 : ℤ_[p]) * ((p : ℤ_[p]) ^ (↑ₘk 1 0).valuation * ((w : ℤ_[p]) - 1)) := by
          linear_combination (-(1 - (w : ℤ_[p]))) * hcu
        rw [h'']
        exact Ideal.mul_mem_left _ _ h'
      refine apply_map_eq_zero_of_conj p hps hri k w 1 0 ?_ ?_ (by simpa using hne)
      · rw [conj_borelInt_apply_one_zero, Units.val_one]
        have h' : ↑ₘk 1 0 * (↑ₘk 0 0 * (1 - (w : ℤ_[p])) - 0 * ↑ₘk 1 0)
            = ↑ₘk 0 0 * (↑ₘk 1 0 * (1 - (w : ℤ_[p]))) := by ring
        rw [h']
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hcw)
      · rw [conj_borelInt_apply_one_one, Units.val_one, add_sub_cancel_left]
        have h' : ↑ₘk 1 0 * (↑ₘk 0 1 * (1 - (w : ℤ_[p])) - 0 * ↑ₘk 1 1)
            = ↑ₘk 0 1 * (↑ₘk 1 0 * (1 - (w : ℤ_[p]))) := by ring
        rw [h']
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hcw)

theorem principalSeries_inf_rightInvariant_padicK1_eq_bot {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {n₁ n₂ : ℕ}
    (h₁ : HasCharConductor p μ₁ n₁) (h₂ : HasCharConductor p μ₂ n₂) {m : ℕ} (hm : m < n₁ + n₂) :
    principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p (LocalNewvector.padicK1 p m) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  obtain ⟨hps, hri⟩ := Submodule.mem_inf.mp hf
  rw [Submodule.mem_bot]
  refine eq_zero_of_forall_integral_eq_zero p hps fun g hg => ?_
  obtain ⟨k, rfl⟩ := hg
  refine apply_map_eq_zero_of_cases p h₁ h₂ hps hri k (fun _ => by omega) fun hc => ?_
  have hi : (↑ₘk 1 0).valuation < m := by
    rwa [mem_pIdeal_iff_le_valuation p (ne_zero_of_not_mem_pIdeal p hc), not_le] at hc
  omega

theorem PSCarrier.fixed_padicK1_eq_bot_of_lt {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {n₁ n₂ : ℕ}
    (h₁ : HasCharConductor p μ₁ n₁) (h₂ : HasCharConductor p μ₂ n₂) {m : ℕ} (hm : m < n₁ + n₂) :
    LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p m) (PSCarrier p μ₁ μ₂) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hw' := (PSCarrier.fixedEquiv p μ₁ μ₂ (LocalNewvector.padicK1 p m) ⟨v, hv⟩).property
  have hw : ((PSCarrier.fixedEquiv p μ₁ μ₂ (LocalNewvector.padicK1 p m) ⟨v, hv⟩ :
      ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p (LocalNewvector.padicK1 p m))) :
        GL (Fin 2) ℚ_[p] → ℂ) = 0 := by
    rw [← Submodule.mem_bot ℂ, ← principalSeries_inf_rightInvariant_padicK1_eq_bot p h₁ h₂ hm]
    exact hw'
  have hzero : PSCarrier.fixedEquiv p μ₁ μ₂ (LocalNewvector.padicK1 p m) ⟨v, hv⟩ = 0 := Subtype.ext hw
  rw [LinearEquiv.map_eq_zero_iff] at hzero
  rw [Submodule.mem_bot]
  exact congrArg Subtype.val hzero

theorem mul_apply_one_zero (k y : GL (Fin 2) ℤ_[p]) :
    ↑ₘ(k * y) 1 0 = ↑ₘk 1 0 * ↑ₘy 0 0 + ↑ₘk 1 1 * ↑ₘy 1 0 := by
  rw [Matrix.GeneralLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_apply_one_one (k y : GL (Fin 2) ℤ_[p]) :
    ↑ₘ(k * y) 1 1 = ↑ₘk 1 0 * ↑ₘy 0 1 + ↑ₘk 1 1 * ↑ₘy 1 1 := by
  rw [Matrix.GeneralLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_det_eq (k : GL (Fin 2) ℤ_[p]) :
    ((Matrix.GeneralLinearGroup.det k : ℤ_[p]ˣ) : ℤ_[p]) = ↑ₘk 0 0 * ↑ₘk 1 1 - ↑ₘk 0 1 * ↑ₘk 1 0 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem borelInt_mul_apply_one_zero (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) (k : GL (Fin 2) ℤ_[p]) :
    ↑ₘ(borelInt p u₁ u₂ x * k) 1 0 = (u₂ : ℤ_[p]) * ↑ₘk 1 0 := by
  rw [mul_apply_one_zero, coe_borelInt]; simp

theorem borelInt_mul_apply_one_one (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) (k : GL (Fin 2) ℤ_[p]) :
    ↑ₘ(borelInt p u₁ u₂ x * k) 1 1 = (u₂ : ℤ_[p]) * ↑ₘk 1 1 := by
  rw [mul_apply_one_one, coe_borelInt]; simp

theorem valuation_eq_of_cell {i : ℕ} {c : ℤ_[p]} (hc : c ∈ pIdeal p i ∧ c ∉ pIdeal p (i + 1)) :
    c.valuation = i := by
  have hc0 := ne_zero_of_not_mem_pIdeal p hc.2
  have h1 := (mem_pIdeal_iff_le_valuation p hc0).mp hc.1
  have h2 : ¬ i + 1 ≤ c.valuation := fun h => hc.2 ((mem_pIdeal_iff_le_valuation p hc0).mpr h)
  omega

theorem cell_unit_mul_iff (u : ℤ_[p]ˣ) {i : ℕ} {c : ℤ_[p]} :
    ((u : ℤ_[p]) * c ∈ pIdeal p i ∧ (u : ℤ_[p]) * c ∉ pIdeal p (i + 1))
      ↔ (c ∈ pIdeal p i ∧ c ∉ pIdeal p (i + 1)) := by
  rw [Ideal.unit_mul_mem_iff_mem _ u.isUnit, Ideal.unit_mul_mem_iff_mem _ u.isUnit]

theorem mul_apply_one_zero_mem_iff {j m : ℕ} (hjm : j ≤ m) (hm : 1 ≤ m) (k y : GL (Fin 2) ℤ_[p])
    (h10 : ↑ₘy 1 0 ∈ pIdeal p m) :
    ↑ₘ(k * y) 1 0 ∈ pIdeal p j ↔ ↑ₘk 1 0 ∈ pIdeal p j := by
  have hy00 : IsUnit (↑ₘy 0 0) := (isUnit_diag_of_mem_pIdeal_one p y (pIdeal_antitone p hm h10)).1
  have hdj : ↑ₘk 1 1 * ↑ₘy 1 0 ∈ pIdeal p j := Ideal.mul_mem_left _ _ (pIdeal_antitone p hjm h10)
  rw [mul_apply_one_zero]
  constructor
  · intro h
    have h' : ↑ₘy 0 0 * ↑ₘk 1 0 ∈ pIdeal p j := by
      rw [mul_comm]; simpa using Ideal.sub_mem _ h hdj
    exact (Ideal.unit_mul_mem_iff_mem _ hy00).mp h'
  · intro h
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h) hdj

theorem unitCoeff_congr {x y : ℤ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) (h : x = y) :
    PadicInt.unitCoeff hx = PadicInt.unitCoeff hy := by
  subst h; rfl

section CellWitness

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

open scoped Classical in

def mu2Factor (d : ℤ_[p]) : ℂ :=
  if hd : IsUnit d then (μ₂ (unitLift p hd.unit) : ℂ) else 1

theorem mu2Factor_of_isUnit {d : ℤ_[p]} (hd : IsUnit d) :
    mu2Factor p μ₂ d = (μ₂ (unitLift p hd.unit) : ℂ) := by
  rw [mu2Factor, dif_pos hd]

theorem mu2Factor_of_not_isUnit {d : ℤ_[p]} (hd : ¬ IsUnit d) : mu2Factor p μ₂ d = 1 := by
  rw [mu2Factor, dif_neg hd]

theorem mu2Factor_coe_unit (w : ℤ_[p]ˣ) : mu2Factor p μ₂ (w : ℤ_[p]) = (μ₂ (unitLift p w) : ℂ) := by
  rw [mu2Factor_of_isUnit p μ₂ w.isUnit]
  congr 3
  exact Units.ext (IsUnit.unit_spec _)

theorem mu2Factor_eq_one_of_forall (h : ∀ w : ℤ_[p]ˣ, μ₂ (unitLift p w) = 1) (d : ℤ_[p]) :
    mu2Factor p μ₂ d = 1 := by
  by_cases hd : IsUnit d
  · rw [mu2Factor_of_isUnit p μ₂ hd, h, Units.val_one]
  · exact mu2Factor_of_not_isUnit p μ₂ hd

theorem mu2Factor_unit_mul_of_isUnit (u : ℤ_[p]ˣ) {d : ℤ_[p]} (hd : IsUnit d) :
    mu2Factor p μ₂ ((u : ℤ_[p]) * d) = (μ₂ (unitLift p u) : ℂ) * mu2Factor p μ₂ d := by
  have hud : IsUnit ((u : ℤ_[p]) * d) := (Units.isUnit_units_mul u d).mpr hd
  have hunit : hud.unit = u * hd.unit := Units.ext (by simp [IsUnit.unit_spec])
  rw [mu2Factor_of_isUnit p μ₂ hud, mu2Factor_of_isUnit p μ₂ hd, hunit, map_mul, map_mul, Units.val_mul]

theorem mu2Factor_eq_of_sub_mem {i : ℕ} (hμ₂ : ∀ w : ℤ_[p]ˣ, (w : ℤ_[p]) - 1 ∈ pIdeal p i → μ₂ (unitLift p w) = 1)
    {d d' : ℤ_[p]} (hd : IsUnit d) (hd' : IsUnit d') (hdd : d' - d ∈ pIdeal p i) :
    mu2Factor p μ₂ d' = mu2Factor p μ₂ d := by
  have hw : ((hd'.unit * hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1 ∈ pIdeal p i := by
    have hinv : (hd.unit : ℤ_[p]) * ((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := Units.mul_inv _
    have heq : ((hd'.unit * hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1 = (d' - d) * ((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
      rw [Units.val_mul, IsUnit.unit_spec]
      linear_combination hinv - ((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * hd.unit_spec
    rw [heq]
    exact Ideal.mul_mem_right _ _ hdd
  have hprod : hd'.unit = (hd'.unit * hd.unit⁻¹) * hd.unit := by rw [inv_mul_cancel_right]
  rw [mu2Factor_of_isUnit p μ₂ hd', mu2Factor_of_isUnit p μ₂ hd, hprod, map_mul, map_mul, hμ₂ _ hw, one_mul]

open scoped Classical in

def cellFn (i : ℕ) (k : GL (Fin 2) ℤ_[p]) : ℂ :=
  if hc : ↑ₘk 1 0 ∈ pIdeal p i ∧ ↑ₘk 1 0 ∉ pIdeal p (i + 1) then
    (μ₁ (unitLift p (Matrix.GeneralLinearGroup.det k)) : ℂ)
      / μ₁ (unitLift p (PadicInt.unitCoeff (ne_zero_of_not_mem_pIdeal p hc.2)))
      * mu2Factor p μ₂ (↑ₘk 1 1)
  else 0

theorem cellFn_of_not {i : ℕ} {k : GL (Fin 2) ℤ_[p]}
    (hc : ¬ (↑ₘk 1 0 ∈ pIdeal p i ∧ ↑ₘk 1 0 ∉ pIdeal p (i + 1))) : cellFn p μ₁ μ₂ i k = 0 := by
  rw [cellFn, dif_neg hc]

theorem cellFn_of_cell {i : ℕ} {k : GL (Fin 2) ℤ_[p]}
    (hc : ↑ₘk 1 0 ∈ pIdeal p i ∧ ↑ₘk 1 0 ∉ pIdeal p (i + 1)) :
    cellFn p μ₁ μ₂ i k
      = (μ₁ (unitLift p (Matrix.GeneralLinearGroup.det k)) : ℂ)
          / μ₁ (unitLift p (PadicInt.unitCoeff (ne_zero_of_not_mem_pIdeal p hc.2)))
          * mu2Factor p μ₂ (↑ₘk 1 1) := by
  rw [cellFn, dif_pos hc]

theorem cellFn_borelInt_mul (i : ℕ) (hμ₂ : i = 0 → ∀ w : ℤ_[p]ˣ, μ₂ (unitLift p w) = 1)
    (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) (k : GL (Fin 2) ℤ_[p]) :
    cellFn p μ₁ μ₂ i (borelInt p u₁ u₂ x * k)
      = (μ₁ (unitLift p u₁) : ℂ) * μ₂ (unitLift p u₂) * cellFn p μ₁ μ₂ i k := by
  by_cases hc : ↑ₘk 1 0 ∈ pIdeal p i ∧ ↑ₘk 1 0 ∉ pIdeal p (i + 1)
  · have hc' : ↑ₘ(borelInt p u₁ u₂ x * k) 1 0 ∈ pIdeal p i
        ∧ ↑ₘ(borelInt p u₁ u₂ x * k) 1 0 ∉ pIdeal p (i + 1) := by
      rw [borelInt_mul_apply_one_zero]; exact (cell_unit_mul_iff p u₂).mpr hc
    have hc0 := ne_zero_of_not_mem_pIdeal p hc.2
    have hc0' := ne_zero_of_not_mem_pIdeal p hc'.2
    rw [cellFn_of_cell p μ₁ μ₂ hc', cellFn_of_cell p μ₁ μ₂ hc]

    have huc : PadicInt.unitCoeff hc0' = u₂ * PadicInt.unitCoeff hc0 := by
      have hne : (u₂ : ℤ_[p]) * ↑ₘk 1 0 ≠ 0 := mul_ne_zero (Units.ne_zero u₂) hc0
      rw [unitCoeff_congr p hc0' hne (borelInt_mul_apply_one_zero p u₁ u₂ x k)]
      exact unitCoeff_unit_mul p u₂ hc0 hne
    have hdet : Matrix.GeneralLinearGroup.det (borelInt p u₁ u₂ x * k)
        = u₁ * u₂ * Matrix.GeneralLinearGroup.det k := by
      rw [map_mul, det_borelInt]

    have hfac : mu2Factor p μ₂ (↑ₘ(borelInt p u₁ u₂ x * k) 1 1)
        = (μ₂ (unitLift p u₂) : ℂ) * mu2Factor p μ₂ (↑ₘk 1 1) := by
      rw [borelInt_mul_apply_one_one]
      by_cases hd : IsUnit (↑ₘk 1 1)
      · exact mu2Factor_unit_mul_of_isUnit p μ₂ u₂ hd
      ·
        have hi : i = 0 := by
          by_contra hi
          have h1 : ↑ₘk 1 0 ∈ pIdeal p 1 := pIdeal_antitone p (Nat.one_le_iff_ne_zero.mpr hi) hc.1
          exact hd (isUnit_diag_of_mem_pIdeal_one p k h1).2
        have hud : ¬ IsUnit ((u₂ : ℤ_[p]) * ↑ₘk 1 1) := fun h => hd ((Units.isUnit_units_mul u₂ _).mp h)
        rw [mu2Factor_of_not_isUnit p μ₂ hud, mu2Factor_of_not_isUnit p μ₂ hd, hμ₂ hi u₂, Units.val_one,
          one_mul]
    rw [hfac, hdet, huc]
    have hne : ∀ w : ℤ_[p]ˣ, (μ₁ (unitLift p w) : ℂ) ≠ 0 := fun w => Units.ne_zero _
    simp only [map_mul, Units.val_mul]
    field_simp
  · have hc' : ¬ (↑ₘ(borelInt p u₁ u₂ x * k) 1 0 ∈ pIdeal p i
        ∧ ↑ₘ(borelInt p u₁ u₂ x * k) 1 0 ∉ pIdeal p (i + 1)) := by
      rw [borelInt_mul_apply_one_zero, cell_unit_mul_iff]; exact hc
    rw [cellFn_of_not p μ₁ μ₂ hc', cellFn_of_not p μ₁ μ₂ hc, mul_zero]

theorem cellFn_mul_eq {i m : ℕ} (him : i < m)
    (hμ₁ : ∀ w : ℤ_[p]ˣ, (w : ℤ_[p]) - 1 ∈ pIdeal p (m - i) → μ₁ (unitLift p w) = 1)
    (hμ₂ : ∀ w : ℤ_[p]ˣ, (w : ℤ_[p]) - 1 ∈ pIdeal p i → μ₂ (unitLift p w) = 1)
    (k y : GL (Fin 2) ℤ_[p]) (h10 : ↑ₘy 1 0 ∈ pIdeal p m) (h11 : ↑ₘy 1 1 - 1 ∈ pIdeal p m) :
    cellFn p μ₁ μ₂ i (k * y) = cellFn p μ₁ μ₂ i k := by
  have hm : 1 ≤ m := by omega
  have hcell : (↑ₘ(k * y) 1 0 ∈ pIdeal p i ∧ ↑ₘ(k * y) 1 0 ∉ pIdeal p (i + 1))
      ↔ (↑ₘk 1 0 ∈ pIdeal p i ∧ ↑ₘk 1 0 ∉ pIdeal p (i + 1)) := by
    rw [mul_apply_one_zero_mem_iff p him.le hm k y h10, mul_apply_one_zero_mem_iff p him hm k y h10]
  by_cases hc : ↑ₘk 1 0 ∈ pIdeal p i ∧ ↑ₘk 1 0 ∉ pIdeal p (i + 1)
  · have hc' := hcell.mpr hc
    have hc0 := ne_zero_of_not_mem_pIdeal p hc.2
    have hc0' := ne_zero_of_not_mem_pIdeal p hc'.2
    rw [cellFn_of_cell p μ₁ μ₂ hc', cellFn_of_cell p μ₁ μ₂ hc]
    have hy00 : IsUnit (↑ₘy 0 0) := (isUnit_diag_of_mem_pIdeal_one p y (pIdeal_antitone p hm h10)).1

    have hfac : mu2Factor p μ₂ (↑ₘ(k * y) 1 1) = mu2Factor p μ₂ (↑ₘk 1 1) := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · have hall : ∀ w : ℤ_[p]ˣ, μ₂ (unitLift p w) = 1 := fun w => hμ₂ w (by simp)
        rw [mu2Factor_eq_one_of_forall p μ₂ hall, mu2Factor_eq_one_of_forall p μ₂ hall]
      · have hd : IsUnit (↑ₘk 1 1) :=
          (isUnit_diag_of_mem_pIdeal_one p k (pIdeal_antitone p hi hc.1)).2
        have hd' : IsUnit (↑ₘ(k * y) 1 1) :=
          (isUnit_diag_of_mem_pIdeal_one p (k * y) (pIdeal_antitone p hi hc'.1)).2
        refine mu2Factor_eq_of_sub_mem p μ₂ hμ₂ hd hd' ?_
        rw [mul_apply_one_one]
        have heq : ↑ₘk 1 0 * ↑ₘy 0 1 + ↑ₘk 1 1 * ↑ₘy 1 1 - ↑ₘk 1 1
            = ↑ₘk 1 0 * ↑ₘy 0 1 + ↑ₘk 1 1 * (↑ₘy 1 1 - 1) := by ring
        rw [heq]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc.1)
          (Ideal.mul_mem_left _ _ (pIdeal_antitone p him.le h11))

    set r : ℤ_[p]ˣ := Matrix.GeneralLinearGroup.det y * PadicInt.unitCoeff hc0 * (PadicInt.unitCoeff hc0')⁻¹
      with hr_def
    have hz : (Matrix.GeneralLinearGroup.det y : ℤ_[p]) * (PadicInt.unitCoeff hc0 : ℤ_[p])
        - (PadicInt.unitCoeff hc0' : ℤ_[p]) ∈ pIdeal p (m - i) := by
      rw [← pow_mul_mem_pIdeal_iff p (i := i), Nat.add_sub_cancel' him.le]
      have hcu := unitCoeff_mul_pow_eq p hc0 (valuation_eq_of_cell p hc)
      have hcu' := unitCoeff_mul_pow_eq p hc0' (valuation_eq_of_cell p hc')
      have heq : (p : ℤ_[p]) ^ i * ((Matrix.GeneralLinearGroup.det y : ℤ_[p]) * (PadicInt.unitCoeff hc0 : ℤ_[p])
            - (PadicInt.unitCoeff hc0' : ℤ_[p]))
          = ↑ₘk 1 0 * (↑ₘy 0 0 * (↑ₘy 1 1 - 1)) - ↑ₘk 1 0 * (↑ₘy 0 1 * ↑ₘy 1 0) - ↑ₘk 1 1 * ↑ₘy 1 0 := by
        rw [coe_det_eq]
        linear_combination ((↑ₘy 0 0 * ↑ₘy 1 1 - ↑ₘy 0 1 * ↑ₘy 1 0)) * hcu - hcu'
          - mul_apply_one_zero p k y
      rw [heq]
      exact Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ h11))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ h10))) (Ideal.mul_mem_left _ _ h10)
    have hr : (r : ℤ_[p]) - 1 ∈ pIdeal p (m - i) := by
      have hinv : (((PadicInt.unitCoeff hc0')⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (PadicInt.unitCoeff hc0' : ℤ_[p]) = 1 :=
        Units.inv_mul _
      have heq : (r : ℤ_[p]) - 1 = (((PadicInt.unitCoeff hc0')⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
          * ((Matrix.GeneralLinearGroup.det y : ℤ_[p]) * (PadicInt.unitCoeff hc0 : ℤ_[p])
              - (PadicInt.unitCoeff hc0' : ℤ_[p])) := by
        rw [hr_def, Units.val_mul, Units.val_mul]
        linear_combination hinv
      rw [heq]
      exact Ideal.mul_mem_left _ _ hz
    have hμr : μ₁ (unitLift p r) = 1 := hμ₁ r hr
    have hunits : Matrix.GeneralLinearGroup.det y * PadicInt.unitCoeff hc0 = r * PadicInt.unitCoeff hc0' := by
      rw [hr_def, inv_mul_cancel_right]
    have hdet : Matrix.GeneralLinearGroup.det (k * y)
        = Matrix.GeneralLinearGroup.det k * Matrix.GeneralLinearGroup.det y := map_mul _ _ _
    have hne : ∀ w : ℤ_[p]ˣ, (μ₁ (unitLift p w) : ℂ) ≠ 0 := fun w => Units.ne_zero _
    rw [hfac, hdet, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (hne _) (hne _)]
    have key : (μ₁ (unitLift p (Matrix.GeneralLinearGroup.det y)) : ℂ) * μ₁ (unitLift p (PadicInt.unitCoeff hc0))
        = μ₁ (unitLift p (PadicInt.unitCoeff hc0')) := by
      rw [← Units.val_mul, ← map_mul, ← map_mul, hunits, map_mul, map_mul, hμr, one_mul]
    simp only [map_mul, Units.val_mul]
    linear_combination (μ₁ (unitLift p (Matrix.GeneralLinearGroup.det k)) : ℂ) * mu2Factor p μ₂ (↑ₘk 1 1) * key
  · rw [cellFn_of_not p μ₁ μ₂ (fun h => hc (hcell.mp h)), cellFn_of_not p μ₁ μ₂ hc]

theorem coe_lowerUnipotentR (r : ℤ_[p]) :
    ↑ₘ(LocalGL2.lowerUnipotentR r) = !![1, 0; r, 1] := rfl

theorem cellFn_lowerUnipotentR (i : ℕ) :
    cellFn p μ₁ μ₂ i (LocalGL2.lowerUnipotentR ((p : ℤ_[p]) ^ i)) = 1 := by
  have hpi : (p : ℤ_[p]) ^ i ≠ 0 := pow_ne_zero _ (NeZero.ne _)
  have hval : ((p : ℤ_[p]) ^ i).valuation = i := by
    rw [PadicInt.valuation_pow, PadicInt.valuation_p, mul_one]
  have hc : ↑ₘ(LocalGL2.lowerUnipotentR ((p : ℤ_[p]) ^ i)) 1 0 ∈ pIdeal p i
      ∧ ↑ₘ(LocalGL2.lowerUnipotentR ((p : ℤ_[p]) ^ i)) 1 0 ∉ pIdeal p (i + 1) := by
    rw [coe_lowerUnipotentR]
    refine ⟨Ideal.mem_span_singleton_self _, fun h => ?_⟩
    have := (mem_pIdeal_iff_le_valuation p (x := (p : ℤ_[p]) ^ i) hpi).mp (by simpa using h)
    omega
  rw [cellFn_of_cell p μ₁ μ₂ hc]
  have hdet : Matrix.GeneralLinearGroup.det (LocalGL2.lowerUnipotentR ((p : ℤ_[p]) ^ i)) = 1 :=
    Units.ext (by rw [coe_det_eq, coe_lowerUnipotentR]; simp)
  have huc : ∀ (h : ((!![1, 0; (p : ℤ_[p]) ^ i, 1] : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0) ≠ 0),
      PadicInt.unitCoeff h = 1 := by
    intro h
    apply Units.ext
    apply mul_right_cancel₀ hpi
    have := unitCoeff_mul_pow_eq p h (by show ((p : ℤ_[p]) ^ i).valuation = i; exact hval)
    simpa using this
  have hd : mu2Factor p μ₂ (↑ₘ(LocalGL2.lowerUnipotentR ((p : ℤ_[p]) ^ i)) 1 1) = 1 := by
    rw [coe_lowerUnipotentR]
    have h1 : ((!![1, 0; (p : ℤ_[p]) ^ i, 1] : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 1) = ((1 : ℤ_[p]ˣ) : ℤ_[p]) := by
      simp
    rw [h1, mu2Factor_coe_unit, map_one, map_one, Units.val_one]
  rw [hdet, hd, mul_one]
  have : PadicInt.unitCoeff (ne_zero_of_not_mem_pIdeal p hc.2) = 1 := huc _
  rw [this]
  simp

open scoped Classical in

def cellFnTop (m : ℕ) (k : GL (Fin 2) ℤ_[p]) : ℂ :=
  if ↑ₘk 1 0 ∈ pIdeal p m then
    if hd : IsUnit (↑ₘk 1 1) then
      (μ₁ (unitLift p (Matrix.GeneralLinearGroup.det k)) : ℂ) / μ₁ (unitLift p hd.unit) * μ₂ (unitLift p hd.unit)
    else 0
  else 0

theorem cellFnTop_of_not_mem {m : ℕ} {k : GL (Fin 2) ℤ_[p]} (hc : ↑ₘk 1 0 ∉ pIdeal p m) :
    cellFnTop p μ₁ μ₂ m k = 0 := by
  rw [cellFnTop, if_neg hc]

theorem cellFnTop_of_not_isUnit {m : ℕ} {k : GL (Fin 2) ℤ_[p]} (hd : ¬ IsUnit (↑ₘk 1 1)) :
    cellFnTop p μ₁ μ₂ m k = 0 := by
  rw [cellFnTop]
  split_ifs <;> rfl

theorem cellFnTop_of_mem {m : ℕ} {k : GL (Fin 2) ℤ_[p]} (hc : ↑ₘk 1 0 ∈ pIdeal p m) (hd : IsUnit (↑ₘk 1 1)) :
    cellFnTop p μ₁ μ₂ m k
      = (μ₁ (unitLift p (Matrix.GeneralLinearGroup.det k)) : ℂ) / μ₁ (unitLift p hd.unit)
          * μ₂ (unitLift p hd.unit) := by
  rw [cellFnTop, if_pos hc, dif_pos hd]

theorem cellFnTop_borelInt_mul (m : ℕ) (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) (k : GL (Fin 2) ℤ_[p]) :
    cellFnTop p μ₁ μ₂ m (borelInt p u₁ u₂ x * k)
      = (μ₁ (unitLift p u₁) : ℂ) * μ₂ (unitLift p u₂) * cellFnTop p μ₁ μ₂ m k := by
  by_cases hc : ↑ₘk 1 0 ∈ pIdeal p m
  · have hc' : ↑ₘ(borelInt p u₁ u₂ x * k) 1 0 ∈ pIdeal p m := by
      rw [borelInt_mul_apply_one_zero]; exact Ideal.mul_mem_left _ _ hc
    by_cases hd : IsUnit (↑ₘk 1 1)
    · have hd' : IsUnit (↑ₘ(borelInt p u₁ u₂ x * k) 1 1) := by
        rw [borelInt_mul_apply_one_one]; exact (Units.isUnit_units_mul u₂ _).mpr hd
      have hunit : hd'.unit = u₂ * hd.unit :=
        Units.ext (by rw [IsUnit.unit_spec, borelInt_mul_apply_one_one, Units.val_mul, IsUnit.unit_spec])
      have hdet : Matrix.GeneralLinearGroup.det (borelInt p u₁ u₂ x * k)
          = u₁ * u₂ * Matrix.GeneralLinearGroup.det k := by
        rw [map_mul, det_borelInt]
      rw [cellFnTop_of_mem p μ₁ μ₂ hc' hd', cellFnTop_of_mem p μ₁ μ₂ hc hd, hunit, hdet]
      have hne : ∀ w : ℤ_[p]ˣ, (μ₁ (unitLift p w) : ℂ) ≠ 0 := fun w => Units.ne_zero _
      simp only [map_mul, Units.val_mul]
      field_simp
    · have hd' : ¬ IsUnit (↑ₘ(borelInt p u₁ u₂ x * k) 1 1) := by
        rw [borelInt_mul_apply_one_one]; exact fun h => hd ((Units.isUnit_units_mul u₂ _).mp h)
      rw [cellFnTop_of_not_isUnit p μ₁ μ₂ hd', cellFnTop_of_not_isUnit p μ₁ μ₂ hd, mul_zero]
  · have hc' : ↑ₘ(borelInt p u₁ u₂ x * k) 1 0 ∉ pIdeal p m := by
      rw [borelInt_mul_apply_one_zero, Ideal.unit_mul_mem_iff_mem _ u₂.isUnit]; exact hc
    rw [cellFnTop_of_not_mem p μ₁ μ₂ hc', cellFnTop_of_not_mem p μ₁ μ₂ hc, mul_zero]

theorem cellFnTop_mul_eq {m : ℕ} (hm : 1 ≤ m)
    (hμ₁ : ∀ w : ℤ_[p]ˣ, μ₁ (unitLift p w) = 1)
    (hμ₂ : ∀ w : ℤ_[p]ˣ, (w : ℤ_[p]) - 1 ∈ pIdeal p m → μ₂ (unitLift p w) = 1)
    (k y : GL (Fin 2) ℤ_[p]) (h10 : ↑ₘy 1 0 ∈ pIdeal p m) (h11 : ↑ₘy 1 1 - 1 ∈ pIdeal p m) :
    cellFnTop p μ₁ μ₂ m (k * y) = cellFnTop p μ₁ μ₂ m k := by
  have hcell := mul_apply_one_zero_mem_iff p le_rfl hm k y h10
  by_cases hc : ↑ₘk 1 0 ∈ pIdeal p m
  · have hc' := hcell.mpr hc
    have hd : IsUnit (↑ₘk 1 1) := (isUnit_diag_of_mem_pIdeal_one p k (pIdeal_antitone p hm hc)).2
    have hd' : IsUnit (↑ₘ(k * y) 1 1) := (isUnit_diag_of_mem_pIdeal_one p (k * y) (pIdeal_antitone p hm hc')).2
    rw [cellFnTop_of_mem p μ₁ μ₂ hc' hd', cellFnTop_of_mem p μ₁ μ₂ hc hd]
    simp only [hμ₁, Units.val_one, div_one, one_mul]

    have h := mu2Factor_eq_of_sub_mem p μ₂ hμ₂ hd hd' (by
      rw [mul_apply_one_one]
      have heq : ↑ₘk 1 0 * ↑ₘy 0 1 + ↑ₘk 1 1 * ↑ₘy 1 1 - ↑ₘk 1 1
          = ↑ₘk 1 0 * ↑ₘy 0 1 + ↑ₘk 1 1 * (↑ₘy 1 1 - 1) := by ring
      rw [heq]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc) (Ideal.mul_mem_left _ _ h11))
    rw [mu2Factor_of_isUnit p μ₂ hd', mu2Factor_of_isUnit p μ₂ hd] at h
    exact h
  · rw [cellFnTop_of_not_mem p μ₁ μ₂ (fun h => hc (hcell.mp h)), cellFnTop_of_not_mem p μ₁ μ₂ hc]

theorem cellFnTop_one (m : ℕ) : cellFnTop p μ₁ μ₂ m 1 = 1 := by
  have hc : ↑ₘ(1 : GL (Fin 2) ℤ_[p]) 1 0 ∈ pIdeal p m := by simp
  have h11 : ↑ₘ(1 : GL (Fin 2) ℤ_[p]) 1 1 = ((1 : ℤ_[p]ˣ) : ℤ_[p]) := by simp
  have hd : IsUnit (↑ₘ(1 : GL (Fin 2) ℤ_[p]) 1 1) := by rw [h11]; exact Units.isUnit _
  have hunit : hd.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, h11])
  rw [cellFnTop_of_mem p μ₁ μ₂ hc hd, hunit]
  simp

end CellWitness
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

theorem map_integral_injective :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p])) := by
  intro x y h
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hij := congrArg (fun g : GL (Fin 2) ℚ_[p] => (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j) h
  simp only [Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply] at hij
  exact Subtype.ext hij

def intPre (k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) : GL (Fin 2) ℤ_[p] :=
  (LocalGL2.mem_integralSubgroup_iff.mp k.2).choose

theorem map_intPre (k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) (intPre p k) = k :=
  (LocalGL2.mem_integralSubgroup_iff.mp k.2).choose_spec

theorem intPre_eq_of_map_eq {k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])} {y : GL (Fin 2) ℤ_[p]}
    (h : Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) y = k) : intPre p k = y :=
  map_integral_injective p ((map_intPre p k).trans h.symm)

theorem intPre_mul (k k' : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) :
    intPre p (k * k') = intPre p k * intPre p k' :=
  map_integral_injective p (by rw [map_mul, map_intPre, map_intPre, map_intPre]; rfl)

theorem exists_ne_zero_mem_inf_of_integral (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) (m : ℕ) (F : GL (Fin 2) ℤ_[p] → ℂ)
    (hlaw : ∀ (u₁ u₂ : ℤ_[p]ˣ) (x : ℤ_[p]) (k : GL (Fin 2) ℤ_[p]),
      F (borelInt p u₁ u₂ x * k) = (μ₁ (unitLift p u₁) : ℂ) * μ₂ (unitLift p u₂) * F k)
    (hinv : ∀ (k y : GL (Fin 2) ℤ_[p]), ↑ₘy 1 0 ∈ pIdeal p m → ↑ₘy 1 1 - 1 ∈ pIdeal p m → F (k * y) = F k)
    {γ : GL (Fin 2) ℤ_[p]} (hγ : F γ ≠ 0) :
    ∃ f ∈ principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p (LocalNewvector.padicK1 p m), f ≠ 0 := by

  have hψinv : ∀ (k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) (u : GL (Fin 2) ℚ_[p])
      (hu : u ∈ LocalNewvector.padicK1 p m) (hu0 : u ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]),
      F (intPre p (k * ⟨u, hu0⟩)) = F (intPre p k) := by
    intro k u hu hu0
    obtain ⟨y, hyu, h10, h11⟩ := LocalNewvector.mem_congruenceK1_iff.mp hu
    rw [intPre_mul, intPre_eq_of_map_eq p (k := ⟨u, hu0⟩) hyu]
    exact hinv _ _ h10 h11

  have hlawψ : IntegralBorelLaw p μ₁ μ₂ (fun k => F (intPre p k)) := by
    intro u₁ u₂ x hu k
    obtain ⟨h1, h2, hx⟩ := (borelElem_mem_integralSubgroup_iff p u₁ u₂ x).mp hu
    have e1 : unitLift p (PadicInt.mkUnits h1) = u₁ := Units.ext rfl
    have e2 : unitLift p (PadicInt.mkUnits h2) = u₂ := Units.ext rfl
    have hB : Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p])
        (borelInt p (PadicInt.mkUnits h1) (PadicInt.mkUnits h2) ⟨x, hx⟩) = borelElem p u₁ u₂ x := by
      rw [map_borelInt, e1, e2]
    show F (intPre p (⟨borelElem p u₁ u₂ x, hu⟩ * k)) = (μ₁ u₁ : ℂ) * μ₂ u₂ * F (intPre p k)
    rw [intPre_mul, intPre_eq_of_map_eq p (k := ⟨borelElem p u₁ u₂ x, hu⟩) hB, hlaw, e1, e2]

  have hlc : IsLocallyConstant (fun k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) => F (intPre p k)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k₀
    refine ⟨{k | ((k₀ : GL (Fin 2) ℚ_[p]))⁻¹ * (k : GL (Fin 2) ℚ_[p])
        ∈ FLT.SmoothVectors.gl2CongruenceSubgroup p m}, ?_, ?_, ?_⟩
    · exact (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup p m).preimage
        (continuous_const.mul continuous_subtype_val)
    · show ((k₀ : GL (Fin 2) ℚ_[p]))⁻¹ * (k₀ : GL (Fin 2) ℚ_[p]) ∈ FLT.SmoothVectors.gl2CongruenceSubgroup p m
      rw [inv_mul_cancel]; exact Subgroup.one_mem _
    · intro k hk
      have hu : (((k₀⁻¹ * k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) : GL (Fin 2) ℚ_[p]))
          ∈ LocalNewvector.padicK1 p m :=
        LocalNewvector.gl2CongruenceSubgroup_le_padicK1 p m hk
      have h := hψinv k₀ _ hu (k₀⁻¹ * k).2
      have hkk : k₀ * ⟨((k₀⁻¹ * k : ↥(LocalGL2.integralSubgroup ℤ_[p] ℚ_[p])) : GL (Fin 2) ℚ_[p]), (k₀⁻¹ * k).2⟩
          = k := mul_inv_cancel_left k₀ k
      rw [hkk] at h
      exact h

  have hfps : extendIntegral p μ₁ μ₂ (fun k => F (intPre p k)) ∈ principalSeries p μ₁ μ₂ :=
    extendIntegral_mem_principalSeries p hlawψ hlc
  have hfri : extendIntegral p μ₁ μ₂ (fun k => F (intPre p k))
      ∈ rightInvariantFunctions p (LocalNewvector.padicK1 p m) := by
    rw [mem_rightInvariantFunctions_iff]
    intro u hu g
    have hu0 : u ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := LocalNewvector.congruenceK1_le_integralSubgroup _ _ hu
    obtain ⟨a₁, a₂, x, k, hk, rfl⟩ := exists_iwasawa_borelElem p g
    rw [extendIntegral_eq_of_decomp p hlawψ (Subgroup.mul_mem _ hk hu0) (mul_assoc _ _ _),
      extendIntegral_eq_of_decomp p hlawψ hk rfl]
    congr 1
    exact hψinv ⟨k, hk⟩ u hu hu0
  have hγ0 : Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) γ ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
    ⟨γ, rfl⟩
  have hfγ : extendIntegral p μ₁ μ₂ (fun k => F (intPre p k))
      (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) γ) ≠ 0 := by
    rw [extendIntegral_eq_of_decomp p hlawψ hγ0 (by rw [borelElem_one, one_mul]), map_one, map_one,
      Units.val_one, one_mul, one_mul, PSCarrier.halfModulus_same, one_mul]
    show F (intPre p ⟨_, hγ0⟩) ≠ 0
    rwa [intPre_eq_of_map_eq p (k := ⟨_, hγ0⟩) rfl]
  exact ⟨_, Submodule.mem_inf.mpr ⟨hfps, hfri⟩, fun h0 => hfγ (by rw [h0]; rfl)⟩

theorem PSCarrier.fixed_ne_bot_of_exists {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {U : Subgroup (GL (Fin 2) ℚ_[p])}
    (h : ∃ f ∈ principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p U, f ≠ 0) :
    LocalNewvector.fixedSubmodule U (PSCarrier p μ₁ μ₂) ≠ ⊥ := by
  obtain ⟨f, hf, hne⟩ := h
  rw [Submodule.ne_bot_iff]
  refine ⟨((PSCarrier.fixedEquiv p μ₁ μ₂ U).symm ⟨f, hf⟩ : _),
    ((PSCarrier.fixedEquiv p μ₁ μ₂ U).symm ⟨f, hf⟩).2, fun h0 => ?_⟩
  have hzero : (PSCarrier.fixedEquiv p μ₁ μ₂ U).symm ⟨f, hf⟩ = 0 := Subtype.ext h0
  rw [LinearEquiv.map_eq_zero_iff] at hzero
  exact hne (congrArg Subtype.val hzero)

theorem exists_ne_zero_mem_inf_padicK1 {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {n₁ n₂ : ℕ}
    (h₁ : HasCharConductor p μ₁ n₁) (h₂ : HasCharConductor p μ₂ n₂) (hm : 1 ≤ n₁ + n₂) :
    ∃ f ∈ principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p (LocalNewvector.padicK1 p (n₁ + n₂)), f ≠ 0 := by
  rcases Nat.eq_zero_or_pos n₁ with rfl | hn₁
  ·
    have hn₂ : 1 ≤ n₂ := by omega
    rw [zero_add]
    refine exists_ne_zero_mem_inf_of_integral p μ₁ μ₂ n₂ (cellFnTop p μ₁ μ₂ n₂)
      (cellFnTop_borelInt_mul p μ₁ μ₂ n₂)
      (fun k y h10 h11 => cellFnTop_mul_eq p μ₁ μ₂ hn₂
        (fun w => apply_unitLift_eq_one p h₁ (Nat.zero_le 0) (by simp))
        (fun w hw => apply_unitLift_eq_one p h₂ le_rfl hw) k y h10 h11)
      (γ := 1) ?_
    rw [cellFnTop_one]; exact one_ne_zero
  ·
    refine exists_ne_zero_mem_inf_of_integral p μ₁ μ₂ (n₁ + n₂) (cellFn p μ₁ μ₂ n₂)
      (cellFn_borelInt_mul p μ₁ μ₂ n₂ (fun h0 w => apply_unitLift_eq_one p h₂ (le_of_eq h0) (by simp)))
      (fun k y h10 h11 => cellFn_mul_eq p μ₁ μ₂ (by omega)
        (fun w hw => apply_unitLift_eq_one p h₁ (by omega) hw)
        (fun w hw => apply_unitLift_eq_one p h₂ le_rfl hw) k y h10 h11)
      (γ := LocalGL2.lowerUnipotentR ((p : ℤ_[p]) ^ n₂)) ?_
    rw [cellFn_lowerUnipotentR]; exact one_ne_zero

theorem PSCarrier.fixed_padicK1_ne_bot {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {n₁ n₂ : ℕ}
    (h₁ : HasCharConductor p μ₁ n₁) (h₂ : HasCharConductor p μ₂ n₂) :
    LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p (n₁ + n₂)) (PSCarrier p μ₁ μ₂) ≠ ⊥ := by
  rcases Nat.eq_zero_or_pos (n₁ + n₂) with h0 | hm
  · obtain ⟨rfl, rfl⟩ : n₁ = 0 ∧ n₂ = 0 := by omega
    exact (PSCarrier.hasNewvectorConductor_zero p μ₁ μ₂
      ((hasCharConductor_zero_iff_isUnramified p).mp h₁)
      ((hasCharConductor_zero_iff_isUnramified p).mp h₂)).1
  · exact PSCarrier.fixed_ne_bot_of_exists p (exists_ne_zero_mem_inf_padicK1 p h₁ h₂ hm)

theorem PSCarrier.hasNewvectorConductor_add {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {n₁ n₂ : ℕ}
    (h₁ : HasCharConductor p μ₁ n₁) (h₂ : HasCharConductor p μ₂ n₂) :
    LocalNewvector.HasNewvectorConductor p (PSCarrier p μ₁ μ₂) (n₁ + n₂) :=
  ⟨PSCarrier.fixed_padicK1_ne_bot p h₁ h₂, fun _ hm => PSCarrier.fixed_padicK1_eq_bot_of_lt p h₁ h₂ hm⟩

theorem apply_map_eq_mul_of_decomp {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {f : GL (Fin 2) ℚ_[p] → ℂ}
    (hps : f ∈ principalSeries p μ₁ μ₂) {m : ℕ}
    (hri : f ∈ rightInvariantFunctions p (LocalNewvector.padicK1 p m))
    {k γ h : GL (Fin 2) ℤ_[p]} {u₁ u₂ : ℤ_[p]ˣ} {x : ℤ_[p]} (hk : k = borelInt p u₁ u₂ x * γ * h)
    (h10 : ↑ₘh 1 0 ∈ pIdeal p m) (h11 : ↑ₘh 1 1 - 1 ∈ pIdeal p m) :
    f (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k)
      = (μ₁ (unitLift p u₁) : ℂ) * μ₂ (unitLift p u₂)
          * f (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) γ) := by
  rw [hk, map_mul, map_mul, map_borelInt, mul_assoc,
    apply_borelElem_mul_of_mem_integral p hps (borelElem_unitLift_mem_integralSubgroup p u₁ u₂ x),
    (mem_rightInvariantFunctions_iff p).mp hri _ (map_mem_padicK1 p h10 h11)]

theorem eq_decomp_mid {i : ℕ} (k : GL (Fin 2) ℤ_[p]) (hc0 : ↑ₘk 1 0 ≠ 0)
    (hval : (↑ₘk 1 0).valuation = i) (hd : IsUnit (↑ₘk 1 1)) :
    k = borelInt p (Matrix.GeneralLinearGroup.det k * (PadicInt.unitCoeff hc0)⁻¹) hd.unit (↑ₘk 0 1)
        * LocalGL2.lowerUnipotentR ((p : ℤ_[p]) ^ i)
        * borelInt p (PadicInt.unitCoeff hc0 * hd.unit⁻¹) 1 0 := by
  have hcu := unitCoeff_mul_pow_eq p hc0 hval
  have huc : (((PadicInt.unitCoeff hc0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (PadicInt.unitCoeff hc0 : ℤ_[p]) = 1 :=
    Units.inv_mul _
  have hdinv : ↑ₘk 1 1 * ((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := hd.mul_val_inv
  have hdet := coe_det_eq p k
  refine Matrix.GeneralLinearGroup.ext fun i' j' => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_borelInt, coe_borelInt,
    coe_lowerUnipotentR]
  generalize hD : ((Matrix.GeneralLinearGroup.det k : ℤ_[p]ˣ) : ℤ_[p]) = D at hdet
  have hD' : (((Matrix.GeneralLinearGroup.det k * (PadicInt.unitCoeff hc0)⁻¹ : ℤ_[p]ˣ)) : ℤ_[p])
      = D * (((PadicInt.unitCoeff hc0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by rw [Units.val_mul, hD]
  rw [hD']
  fin_cases i' <;> fin_cases j' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, -Matrix.GeneralLinearGroup.val_det_apply]
  · linear_combination (-(D * ((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))) * huc
      + (-(↑ₘk 0 1 * ((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))) * hcu
      + (-((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) * hdet + (-(↑ₘk 0 0)) * hdinv
  · linear_combination (-((p : ℤ_[p]) ^ i * (PadicInt.unitCoeff hc0 : ℤ_[p]))) * hdinv - hcu

theorem eq_decomp_bot (k : GL (Fin 2) ℤ_[p]) (hc : IsUnit (↑ₘk 1 0)) :
    k = borelInt p (Matrix.GeneralLinearGroup.det k * hc.unit⁻¹) 1
          ((↑ₘk 0 0 - (Matrix.GeneralLinearGroup.det k : ℤ_[p]ˣ)) * ((hc.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))
        * LocalGL2.lowerUnipotentR 1
        * borelInt p hc.unit 1 (↑ₘk 1 1 - 1) := by
  have hcinv : ↑ₘk 1 0 * ((hc.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := hc.mul_val_inv
  have hdet := coe_det_eq p k
  refine Matrix.GeneralLinearGroup.ext fun i' j' => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_borelInt, coe_borelInt,
    coe_lowerUnipotentR]
  generalize hD : ((Matrix.GeneralLinearGroup.det k : ℤ_[p]ˣ) : ℤ_[p]) = D at hdet
  have hD' : (((Matrix.GeneralLinearGroup.det k * hc.unit⁻¹ : ℤ_[p]ˣ)) : ℤ_[p])
      = D * ((hc.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by rw [Units.val_mul, hD]
  rw [hD']
  fin_cases i' <;> fin_cases j' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, -Matrix.GeneralLinearGroup.val_det_apply]
  · linear_combination (-(↑ₘk 0 0)) * hcinv
  · linear_combination (-(↑ₘk 0 1)) * hcinv + ((hc.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * hdet

theorem decomp_top {m : ℕ} (k : GL (Fin 2) ℤ_[p]) (hc : ↑ₘk 1 0 ∈ pIdeal p m) (hd : IsUnit (↑ₘk 1 1)) :
    ↑ₘ((borelInt p (Matrix.GeneralLinearGroup.det k * hd.unit⁻¹) hd.unit 0)⁻¹ * k) 1 0 ∈ pIdeal p m
    ∧ ↑ₘ((borelInt p (Matrix.GeneralLinearGroup.det k * hd.unit⁻¹) hd.unit 0)⁻¹ * k) 1 1 - 1 ∈ pIdeal p m := by
  have hdetB : Matrix.GeneralLinearGroup.det (borelInt p (Matrix.GeneralLinearGroup.det k * hd.unit⁻¹) hd.unit 0)
      = Matrix.GeneralLinearGroup.det k := by
    rw [det_borelInt, inv_mul_cancel_right]
  have hdinv : ↑ₘk 1 1 * ((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := hd.mul_val_inv
  have hDinv : (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
      * ((Matrix.GeneralLinearGroup.det k : ℤ_[p]ˣ) : ℤ_[p]) = 1 := Units.inv_mul _
  have h10 : ↑ₘ((borelInt p (Matrix.GeneralLinearGroup.det k * hd.unit⁻¹) hd.unit 0)⁻¹ * k) 1 0
      = (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
          * (((Matrix.GeneralLinearGroup.det k : ℤ_[p]ˣ) : ℤ_[p]) * ((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))
          * ↑ₘk 1 0 := by
    rw [Matrix.GeneralLinearGroup.coe_mul, coe_inv_eq, hdetB, coe_borelInt]
    generalize (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = E
    simp [Matrix.mul_apply, Fin.sum_univ_two, -Matrix.GeneralLinearGroup.val_det_apply]
  have h11 : ↑ₘ((borelInt p (Matrix.GeneralLinearGroup.det k * hd.unit⁻¹) hd.unit 0)⁻¹ * k) 1 1
      = (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
          * (((Matrix.GeneralLinearGroup.det k : ℤ_[p]ˣ) : ℤ_[p]) * ((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))
          * ↑ₘk 1 1 := by
    rw [Matrix.GeneralLinearGroup.coe_mul, coe_inv_eq, hdetB, coe_borelInt]
    generalize (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = E
    simp [Matrix.mul_apply, Fin.sum_univ_two, -Matrix.GeneralLinearGroup.val_det_apply]
  refine ⟨?_, ?_⟩
  · rw [h10]
    exact Ideal.mul_mem_left _ _ hc
  · rw [h11]
    generalize hD : ((Matrix.GeneralLinearGroup.det k : ℤ_[p]ˣ) : ℤ_[p]) = D at hDinv
    generalize hE : (((Matrix.GeneralLinearGroup.det k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = E at hDinv
    have hzero : E * (D * ((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) * ↑ₘk 1 1 - 1 = 0 := by
      linear_combination (((hd.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ↑ₘk 1 1) * hDinv + hdinv
    rw [hzero]
    exact Submodule.zero_mem _

def evalPoint (n₁ n₂ : ℕ) : GL (Fin 2) ℤ_[p] :=
  if n₁ = 0 then 1 else LocalGL2.lowerUnipotentR ((p : ℤ_[p]) ^ n₂)

theorem eq_zero_of_apply_evalPoint_eq_zero {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {n₁ n₂ : ℕ}
    (h₁ : HasCharConductor p μ₁ n₁) (h₂ : HasCharConductor p μ₂ n₂) (hm : 1 ≤ n₁ + n₂)
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hps : f ∈ principalSeries p μ₁ μ₂)
    (hri : f ∈ rightInvariantFunctions p (LocalNewvector.padicK1 p (n₁ + n₂)))
    (h0 : f (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) (evalPoint p n₁ n₂)) = 0) : f = 0 := by
  refine eq_zero_of_forall_integral_eq_zero p hps fun g hg => ?_
  obtain ⟨k, rfl⟩ := hg
  rcases Nat.eq_zero_or_pos n₁ with hn₁ | hn₁
  ·
    subst hn₁
    rw [evalPoint, if_pos rfl] at h0
    by_cases hc : ↑ₘk 1 0 ∈ pIdeal p (0 + n₂)
    · have hd : IsUnit (↑ₘk 1 1) := (isUnit_diag_of_mem_pIdeal_one p k (pIdeal_antitone p hm hc)).2
      obtain ⟨h10, h11⟩ := decomp_top p k hc hd
      rw [apply_map_eq_mul_of_decomp p hps hri (γ := 1)
        (by rw [mul_one, mul_inv_cancel_left]) h10 h11, h0, mul_zero]
    · have hc0 := ne_zero_of_not_mem_pIdeal p hc
      refine apply_map_eq_zero_of_cases p h₁ h₂ hps hri k (fun h => absurd h hc) fun _ => Or.inl ?_
      have := (mem_pIdeal_iff_le_valuation p hc0).not.mp hc
      omega
  · rw [evalPoint, if_neg (by omega)] at h0
    by_cases hcell : ↑ₘk 1 0 ∈ pIdeal p n₂ ∧ ↑ₘk 1 0 ∉ pIdeal p (n₂ + 1)
    ·
      have hc0 := ne_zero_of_not_mem_pIdeal p hcell.2
      have hval := valuation_eq_of_cell p hcell
      rcases Nat.eq_zero_or_pos n₂ with hn₂ | hn₂
      ·
        subst hn₂
        have hcu := unitCoeff_mul_pow_eq p hc0 hval
        rw [pow_zero, mul_one] at hcu
        have hc : IsUnit (↑ₘk 1 0) := hcu ▸ Units.isUnit _
        rw [pow_zero] at h0
        rw [apply_map_eq_mul_of_decomp p hps hri (eq_decomp_bot p k hc) (by simp) (by simp), h0, mul_zero]
      ·
        have hd : IsUnit (↑ₘk 1 1) := (isUnit_diag_of_mem_pIdeal_one p k (pIdeal_antitone p hn₂ hcell.1)).2
        rw [apply_map_eq_mul_of_decomp p hps hri (eq_decomp_mid p k hc0 hval hd) (by simp) (by simp), h0,
          mul_zero]
    ·
      refine apply_map_eq_zero_of_cases p h₁ h₂ hps hri k (fun _ => Or.inr hn₁) fun hc => ?_
      have hc0 := ne_zero_of_not_mem_pIdeal p hc
      have h1 := (mem_pIdeal_iff_le_valuation p (n := n₂) hc0)
      have h2 := (mem_pIdeal_iff_le_valuation p (n := n₂ + 1) hc0)
      have hne : (↑ₘk 1 0).valuation ≠ n₂ := by
        intro heq
        exact hcell ⟨h1.mpr heq.ge, fun h => by have := h2.mp h; omega⟩
      omega

theorem rightInvariantFunctions_le_of_le {U U' : Subgroup (GL (Fin 2) ℚ_[p])} (h : U ≤ U') :
    rightInvariantFunctions p U' ≤ rightInvariantFunctions p U := by
  intro f hf
  rw [mem_rightInvariantFunctions_iff] at hf ⊢
  exact fun u hu x => hf u (h hu) x

theorem finiteDimensional_principalSeries_inf_rightInvariant_padicK1 (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) (m : ℕ) :
    FiniteDimensional ℂ ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p (LocalNewvector.padicK1 p m)) := by
  haveI := finiteDimensional_principalSeries_inf_rightInvariant p μ₁ μ₂
    (FLT.SmoothVectors.gl2CongruenceSubgroup p m) (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup p m)
  exact Submodule.finiteDimensional_of_le (inf_le_inf_left _
    (rightInvariantFunctions_le_of_le p (LocalNewvector.gl2CongruenceSubgroup_le_padicK1 p m)))

theorem finrank_principalSeries_inf_rightInvariant_padicK1_eq_one {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {n₁ n₂ : ℕ}
    (h₁ : HasCharConductor p μ₁ n₁) (h₂ : HasCharConductor p μ₂ n₂) (hm : 1 ≤ n₁ + n₂) :
    Module.finrank ℂ
      ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p (LocalNewvector.padicK1 p (n₁ + n₂))) = 1 := by
  haveI := finiteDimensional_principalSeries_inf_rightInvariant_padicK1 p μ₁ μ₂ (n₁ + n₂)

  let ev : ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p (LocalNewvector.padicK1 p (n₁ + n₂))) →ₗ[ℂ] ℂ :=
    { toFun := fun f => (f : GL (Fin 2) ℚ_[p] → ℂ)
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) (evalPoint p n₁ n₂))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    obtain ⟨hps, hri⟩ := Submodule.mem_inf.mp f.2
    exact Subtype.ext (eq_zero_of_apply_evalPoint_eq_zero p h₁ h₂ hm hps hri hf)
  have hle : Module.finrank ℂ
      ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p (LocalNewvector.padicK1 p (n₁ + n₂))) ≤ 1 :=
    (LinearMap.finrank_le_finrank_of_injective hinj).trans_eq (Module.finrank_self ℂ)
  have hne : Module.finrank ℂ
      ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p (LocalNewvector.padicK1 p (n₁ + n₂))) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero, ← Ne, Submodule.ne_bot_iff]
    obtain ⟨f, hf, hf0⟩ := exists_ne_zero_mem_inf_padicK1 p h₁ h₂ hm
    exact ⟨f, hf, hf0⟩
  omega

theorem PSCarrier.finrank_fixed_padicK1_eq_one {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {n₁ n₂ : ℕ}
    (h₁ : HasCharConductor p μ₁ n₁) (h₂ : HasCharConductor p μ₂ n₂) :
    Module.finrank ℂ
      ↥(LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p (n₁ + n₂)) (PSCarrier p μ₁ μ₂)) = 1 := by
  rcases Nat.eq_zero_or_pos (n₁ + n₂) with h0 | hm
  · obtain ⟨rfl, rfl⟩ : n₁ = 0 ∧ n₂ = 0 := by omega
    exact PSCarrier.finrank_fixed_padicK1_zero_eq_one p μ₁ μ₂
      ((hasCharConductor_zero_iff_isUnramified p).mp h₁) ((hasCharConductor_zero_iff_isUnramified p).mp h₂)
  · rw [PSCarrier.finrank_fixed_eq]
    exact finrank_principalSeries_inf_rightInvariant_padicK1_eq_one p h₁ h₂ hm

end CasselmanStrata
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.isOpen_coe_gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"

theorem PSCarrier.hasNewvectorConductor_add_impl (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {n₁ n₂ : ℕ} (h₁ : LocalNewvector.HasCharConductor p μ₁ n₁) (h₂ : LocalNewvector.HasCharConductor p μ₂ n₂) :
    LocalNewvector.HasNewvectorConductor p (LocalNewvector.PSCarrier p μ₁ μ₂) (n₁ + n₂) :=
  FLT.PrincipalSeriesGL2Padic.PSCarrier.hasNewvectorConductor_add p h₁ h₂

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.FLT.PrincipalSeriesGL2Padic.PSCarrier"

#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.hasNewvectorConductor_add_impl

theorem solution (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {n₁ n₂ : ℕ} (h₁ : LocalNewvector.HasCharConductor p μ₁ n₁) (h₂ : LocalNewvector.HasCharConductor p μ₂ n₂) :
    LocalNewvector.HasNewvectorConductor p (LocalNewvector.PSCarrier p μ₁ μ₂) (n₁ + n₂) := by
  apply FLT.PrincipalSeriesGL2Padic.PSCarrier.hasNewvectorConductor_add_impl <;> assumption

end S_LocalNewvector_PSCarrier_hasNewvectorConductor_add
end P2MW
export P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add (solution)
