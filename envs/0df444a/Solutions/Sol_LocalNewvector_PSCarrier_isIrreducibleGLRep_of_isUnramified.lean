-- Prove2me | solution 1 for LocalNewvector.PSCarrier.isIrreducibleGLRep_of_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/30cfbab3-1557-5518-87a8-87cf6d2141af

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

namespace P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified

section P62Prefix

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

set_option autoImplicit false

open Matrix
open scoped Topology

noncomputable section

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

section HalfModulus

end HalfModulus
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

section PrincipalSeries

theorem smul_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} (g : GL (Fin 2) ℚ_[p])
    (f : RightTranslationFn (GL (Fin 2) ℚ_[p]) ℂ)
    (hf : RightTranslationFn.toFun f ∈ principalSeries p μ₁ μ₂) :
    RightTranslationFn.toFun (g • f) ∈ principalSeries p μ₁ μ₂ :=
  rightTranslate_mem_principalSeries p hf g

end PrincipalSeries
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2"

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT"

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
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
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end RepCarrier
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

section AuditE
variable (p : ℕ) [Fact p.Prime]
end AuditE
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end P62Prefix
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

section DeskModule00

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace AdmissibleRep
p2m_open "FLT"

section FixedVectors

variable {G : Type*} [Group G]

def fixedVectors (K : Subgroup G) (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] [DistribMulAction G M] [SMulCommClass G R M] : Submodule R M where
  carrier := {v | ∀ k ∈ K, k • v = v}
  zero_mem' := fun k _ => smul_zero k
  add_mem' := by
    intro a b ha hb k hk
    rw [smul_add, ha k hk, hb k hk]
  smul_mem' := by
    intro r v hv k hk
    rw [smul_comm, hv k hk]

variable {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  [DistribMulAction G M] [SMulCommClass G R M]

theorem mem_fixedVectors_iff {K : Subgroup G} {v : M} :
    v ∈ fixedVectors K R M ↔ ∀ k ∈ K, k • v = v :=
  Iff.rfl

theorem fixedVectors_antitone {K K' : Subgroup G} (h : K ≤ K') :
    fixedVectors K' R M ≤ fixedVectors K R M := by
  intro v hv k hk
  exact hv k (h hk)

theorem map_fixedVectors_le {N : Type*} [AddCommMonoid N] [Module R N] [DistribMulAction G N]
    [SMulCommClass G R N] (f : M →ₗ[R] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (K : Subgroup G) :
    (fixedVectors K R M).map f ≤ fixedVectors K R N := by
  rintro - ⟨v, hv, rfl⟩ k hk
  rw [← hf, hv k hk]

theorem fixedVectors_le_comap {N : Type*} [AddCommMonoid N] [Module R N] [DistribMulAction G N]
    [SMulCommClass G R N] (f : M →ₗ[R] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (K : Subgroup G) :
    fixedVectors K R M ≤ (fixedVectors K R N).comap f := by
  intro v hv k hk
  rw [← hf, hv k hk]

end FixedVectors
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end FLT.AdmissibleRep
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

open FLT.SmoothVectors FLT.AdmissibleRep

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace EKAverage
p2m_open "FLT"

section QuotientFiniteness

variable {Γ : Type*} [Group Γ]

theorem finite_quotient_of_le {A B : Subgroup Γ} (hAB : A ≤ B) [Finite (Γ ⧸ A)] :
    Finite (Γ ⧸ B) := by
  refine Finite.of_surjective (Subgroup.quotientMapOfLE hAB) ?_
  intro y
  refine Quotient.inductionOn' y (fun g => ?_)
  exact ⟨QuotientGroup.mk g, Subgroup.quotientMapOfLE_apply_mk hAB g⟩

theorem finite_quotient_inf {A B : Subgroup Γ} [Finite (Γ ⧸ A)] [Finite (Γ ⧸ B)] :
    Finite (Γ ⧸ (A ⊓ B)) := by
  haveI : A.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : B.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finite_quotient_of_finiteIndex

end QuotientFiniteness
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

section StabilizerBridge

variable {G : Type*} [Group G] {M : Type*} [MulAction G M]

theorem coe_mem_stabilizer_iff {K : Subgroup G} {k : ↥K} {v : M} :
    k ∈ MulAction.stabilizer K v ↔ (k : G) • v = v := by
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]

theorem stabilizer_eq_subgroupOf (K : Subgroup G) (v : M) :
    MulAction.stabilizer K v = (MulAction.stabilizer G v).subgroupOf K := by
  ext k
  rw [coe_mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]

theorem le_stabilizer_of_forall {K : Subgroup G} {H : Subgroup ↥K} {v : M}
    (h : ∀ k : ↥K, k ∈ H → (k : G) • v = v) : H ≤ MulAction.stabilizer K v := by
  intro k hk
  rw [coe_mem_stabilizer_iff]
  exact h k hk

end StabilizerBridge
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

section Average

variable (F : Type*) [Field F] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module F M]
  [MulAction G M]

noncomputable def ekAverage (K : Subgroup G) (v : M) : M :=
  (Nat.card (↥K ⧸ MulAction.stabilizer K v) : F)⁻¹ •
    ∑ᶠ x : ↥K ⧸ MulAction.stabilizer K v, MulAction.ofQuotientStabilizer K v x

theorem ekAverage_def (K : Subgroup G) (v : M) :
    ekAverage F K v = (Nat.card (↥K ⧸ MulAction.stabilizer K v) : F)⁻¹ •
      ∑ᶠ x : ↥K ⧸ MulAction.stabilizer K v, MulAction.ofQuotientStabilizer K v x :=
  rfl

theorem ekAverage_eq_finsetSum (K : Subgroup G) (v : M)
    [Fintype (↥K ⧸ MulAction.stabilizer K v)] :
    ekAverage F K v = (Nat.card (↥K ⧸ MulAction.stabilizer K v) : F)⁻¹ •
      ∑ x : ↥K ⧸ MulAction.stabilizer K v, MulAction.ofQuotientStabilizer K v x := by
  rw [ekAverage_def, finsum_eq_sum_of_fintype]

end Average
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

section CastSmul

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]

private theorem cast_card_smul_cancel {a b : ℕ} (hb : (b : F) ≠ 0) (x : M) :
    ((a : F) * (b : F))⁻¹ • (b • x) = (a : F)⁻¹ • x := by
  rw [← Nat.cast_smul_eq_nsmul F b x, smul_smul, mul_inv, mul_assoc, inv_mul_cancel₀ hb,
    mul_one]

end CastSmul
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

section Engine

variable {F : Type*} [Field F] {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
  [Module F M] [MulAction G M]

theorem ekAverage_eq_average_of_le_stabilizer [CharZero F] {K : Subgroup G} {v : M}
    {H : Subgroup ↥K}
    (hH : H ≤ MulAction.stabilizer K v) [Finite (↥K ⧸ H)] {ψ : ↥K ⧸ H → M}
    (hψ : ∀ k : ↥K, ψ (QuotientGroup.mk k) = (k : G) • v) :
    ekAverage F K v = (Nat.card (↥K ⧸ H) : F)⁻¹ • ∑ᶠ x : ↥K ⧸ H, ψ x := by
  classical

  haveI hfinS : Finite (↥K ⧸ MulAction.stabilizer K v) := finite_quotient_of_le hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI hfinSH :
      Finite (↥(MulAction.stabilizer K v) ⧸ H.subgroupOf (MulAction.stabilizer K v)) :=
    Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (↥K ⧸ H)
  letI := Fintype.ofFinite (↥K ⧸ MulAction.stabilizer K v)
  letI := Fintype.ofFinite
    (↥(MulAction.stabilizer K v) ⧸ H.subgroupOf (MulAction.stabilizer K v))

  have key : ∀ x : ↥K ⧸ H,
      ψ x = MulAction.ofQuotientStabilizer K v ((Subgroup.quotientEquivProdOfLE hH) x).1 := by
    intro x
    refine Quotient.inductionOn' x (fun k => ?_)
    show ψ (QuotientGroup.mk k) =
      MulAction.ofQuotientStabilizer K v
        ((Subgroup.quotientEquivProdOfLE hH) (QuotientGroup.mk k)).1
    have h1 : ((Subgroup.quotientEquivProdOfLE hH) (QuotientGroup.mk k)).1 =
        (QuotientGroup.mk k : ↥K ⧸ MulAction.stabilizer K v) := rfl
    rw [hψ, h1, MulAction.ofQuotientStabilizer_mk, Subgroup.smul_def]

  have hcard : Nat.card (↥K ⧸ H) = Nat.card (↥K ⧸ MulAction.stabilizer K v) *
      Nat.card (↥(MulAction.stabilizer K v) ⧸ H.subgroupOf (MulAction.stabilizer K v)) := by
    rw [Nat.card_congr (Subgroup.quotientEquivProdOfLE hH), Nat.card_prod]

  have hb0 : ((Nat.card
      (↥(MulAction.stabilizer K v) ⧸ H.subgroupOf (MulAction.stabilizer K v))) : F) ≠ 0 := by
    have hpos : 0 < Nat.card
        (↥(MulAction.stabilizer K v) ⧸ H.subgroupOf (MulAction.stabilizer K v)) := by
      have : Nonempty
          (↥(MulAction.stabilizer K v) ⧸ H.subgroupOf (MulAction.stabilizer K v)) :=
        ⟨QuotientGroup.mk 1⟩
      exact Nat.card_pos
    exact_mod_cast hpos.ne'

  have hsum : ∑ x : ↥K ⧸ H, ψ x =
      Nat.card (↥(MulAction.stabilizer K v) ⧸ H.subgroupOf (MulAction.stabilizer K v)) •
        ∑ y : ↥K ⧸ MulAction.stabilizer K v, MulAction.ofQuotientStabilizer K v y := by
    have h1 : ∑ x : ↥K ⧸ H, ψ x = ∑ x : ↥K ⧸ H,
        MulAction.ofQuotientStabilizer K v ((Subgroup.quotientEquivProdOfLE hH) x).1 :=
      Finset.sum_congr rfl (fun x _ => key x)
    have h2 : ∑ x : ↥K ⧸ H,
        MulAction.ofQuotientStabilizer K v ((Subgroup.quotientEquivProdOfLE hH) x).1 =
        ∑ p : (↥K ⧸ MulAction.stabilizer K v) ×
          (↥(MulAction.stabilizer K v) ⧸ H.subgroupOf (MulAction.stabilizer K v)),
          MulAction.ofQuotientStabilizer K v p.1 :=
      Fintype.sum_equiv (Subgroup.quotientEquivProdOfLE hH) _ _ (fun x => rfl)
    have h3 : ∑ p : (↥K ⧸ MulAction.stabilizer K v) ×
        (↥(MulAction.stabilizer K v) ⧸ H.subgroupOf (MulAction.stabilizer K v)),
        MulAction.ofQuotientStabilizer K v p.1 =
        ∑ y : ↥K ⧸ MulAction.stabilizer K v,
          (Fintype.card
            (↥(MulAction.stabilizer K v) ⧸ H.subgroupOf (MulAction.stabilizer K v))) •
            MulAction.ofQuotientStabilizer K v y := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl (fun y _ => by simp)
    rw [h1, h2, h3, ← Finset.smul_sum, Nat.card_eq_fintype_card]

  rw [ekAverage_def]
  simp only [finsum_eq_sum_of_fintype]
  rw [hsum, hcard, Nat.cast_mul]
  exact (cast_card_smul_cancel hb0 _).symm

theorem ekAverage_eq_average_of_subgroupOf_le_stabilizer [CharZero F] {K L : Subgroup G} {v : M}
    (hLs : L ≤ MulAction.stabilizer G v) [Finite (↥K ⧸ L.subgroupOf K)]
    {ψ : ↥K ⧸ L.subgroupOf K → M} (hψ : ∀ k : ↥K, ψ (QuotientGroup.mk k) = (k : G) • v) :
    ekAverage F K v = (Nat.card (↥K ⧸ L.subgroupOf K) : F)⁻¹ • ∑ᶠ x : ↥K ⧸ L.subgroupOf K, ψ x := by
  refine ekAverage_eq_average_of_le_stabilizer ?_ hψ
  intro k hk
  rw [coe_mem_stabilizer_iff]
  exact hLs (Subgroup.mem_subgroupOf.mp hk)

end Engine
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

section Properties

variable {F : Type*} [Field F] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module F M]
  [DistribMulAction G M]

theorem smul_ekAverage [SMulCommClass G F M] {K : Subgroup G} {k : G} (hk : k ∈ K) (v : M)
    [Finite (↥K ⧸ MulAction.stabilizer K v)] :
    k • ekAverage F K v = ekAverage F K v := by
  classical
  letI := Fintype.ofFinite (↥K ⧸ MulAction.stabilizer K v)
  rw [ekAverage_eq_finsetSum, smul_comm, Finset.smul_sum]
  congr 1
  have hterm : ∀ x : ↥K ⧸ MulAction.stabilizer K v,
      k • MulAction.ofQuotientStabilizer K v x =
        MulAction.ofQuotientStabilizer K v ((⟨k, hk⟩ : ↥K) • x) := by
    intro x
    simp [MulAction.ofQuotientStabilizer_smul, Subgroup.smul_def]
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : ↥K))
    (fun x => MulAction.ofQuotientStabilizer K v ((⟨k, hk⟩ : ↥K) • x))
    (MulAction.ofQuotientStabilizer K v) (fun x => rfl)

theorem ekAverage_mem_fixedVectors [SMulCommClass G F M] (K : Subgroup G) (v : M)
    [Finite (↥K ⧸ MulAction.stabilizer K v)] :
    ekAverage F K v ∈ fixedVectors K F M :=
  fun _k hk => smul_ekAverage hk v

theorem ekAverage_of_mem_fixedVectors [CharZero F] [SMulCommClass G F M] {K : Subgroup G}
    {v : M} (hv : v ∈ fixedVectors K F M) : ekAverage F K v = v := by
  classical
  have hall : ∀ k : ↥K, k ∈ MulAction.stabilizer K v := by
    intro k
    rw [coe_mem_stabilizer_iff]
    exact hv (k : G) k.2
  haveI hsub : Subsingleton (↥K ⧸ MulAction.stabilizer K v) := by
    constructor
    intro a b
    refine Quotient.inductionOn₂' a b (fun x y => ?_)
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    exact hall _
  haveI : Finite (↥K ⧸ MulAction.stabilizer K v) := Finite.of_subsingleton
  letI := Fintype.ofFinite (↥K ⧸ MulAction.stabilizer K v)
  have hQ : ((Nat.card (↥K ⧸ MulAction.stabilizer K v)) : F) ≠ 0 := by
    have hpos : 0 < Nat.card (↥K ⧸ MulAction.stabilizer K v) := by
      have : Nonempty (↥K ⧸ MulAction.stabilizer K v) := ⟨QuotientGroup.mk 1⟩
      exact Nat.card_pos
    exact_mod_cast hpos.ne'
  have hterm : ∀ x : ↥K ⧸ MulAction.stabilizer K v,
      MulAction.ofQuotientStabilizer K v x = v := by
    intro x
    refine Quotient.inductionOn' x (fun k => ?_)
    show MulAction.ofQuotientStabilizer K v (QuotientGroup.mk k) = v
    rw [MulAction.ofQuotientStabilizer_mk, Subgroup.smul_def]
    exact hv (k : G) k.2
  rw [ekAverage_eq_finsetSum, Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul (R := F), smul_smul,
    inv_mul_cancel₀ hQ, one_smul]

theorem ekAverage_zero [CharZero F] [SMulCommClass G F M] (K : Subgroup G) :
    ekAverage F K (0 : M) = 0 :=
  ekAverage_of_mem_fixedVectors (Submodule.zero_mem _)

theorem ekAverage_add [CharZero F] {K : Subgroup G} {v w : M}
    [Finite (↥K ⧸ MulAction.stabilizer K v)] [Finite (↥K ⧸ MulAction.stabilizer K w)] :
    ekAverage F K (v + w) = ekAverage F K v + ekAverage F K w := by
  classical
  set H : Subgroup ↥K := MulAction.stabilizer K v ⊓ MulAction.stabilizer K w with hHdef
  haveI : Finite (↥K ⧸ H) := finite_quotient_inf
  letI := Fintype.ofFinite (↥K ⧸ H)
  have hHv : H ≤ MulAction.stabilizer K v := inf_le_left
  have hHw : H ≤ MulAction.stabilizer K w := inf_le_right
  have hHvw : H ≤ MulAction.stabilizer K (v + w) := by
    intro k hk
    rw [coe_mem_stabilizer_iff, smul_add]
    rw [coe_mem_stabilizer_iff.mp (hHv hk), coe_mem_stabilizer_iff.mp (hHw hk)]

  have hψv : ∀ k : ↥K,
      (MulAction.ofQuotientStabilizer K v ∘ Subgroup.quotientMapOfLE hHv)
        (QuotientGroup.mk k) = (k : G) • v := by
    intro k
    simp only [Function.comp_apply, Subgroup.quotientMapOfLE_apply_mk,
      MulAction.ofQuotientStabilizer_mk, Subgroup.smul_def]
  have hψw : ∀ k : ↥K,
      (MulAction.ofQuotientStabilizer K w ∘ Subgroup.quotientMapOfLE hHw)
        (QuotientGroup.mk k) = (k : G) • w := by
    intro k
    simp only [Function.comp_apply, Subgroup.quotientMapOfLE_apply_mk,
      MulAction.ofQuotientStabilizer_mk, Subgroup.smul_def]
  have hψvw : ∀ k : ↥K,
      (MulAction.ofQuotientStabilizer K (v + w) ∘ Subgroup.quotientMapOfLE hHvw)
        (QuotientGroup.mk k) = (k : G) • (v + w) := by
    intro k
    simp only [Function.comp_apply, Subgroup.quotientMapOfLE_apply_mk,
      MulAction.ofQuotientStabilizer_mk, Subgroup.smul_def]
  rw [ekAverage_eq_average_of_le_stabilizer (F := F) hHv hψv,
    ekAverage_eq_average_of_le_stabilizer (F := F) hHw hψw,
    ekAverage_eq_average_of_le_stabilizer (F := F) hHvw hψvw]
  simp only [finsum_eq_sum_of_fintype]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Quotient.inductionOn' x (fun k => ?_)
  show (MulAction.ofQuotientStabilizer K (v + w) ∘ Subgroup.quotientMapOfLE hHvw)
      (QuotientGroup.mk k) =
    (MulAction.ofQuotientStabilizer K v ∘ Subgroup.quotientMapOfLE hHv)
      (QuotientGroup.mk k) +
    (MulAction.ofQuotientStabilizer K w ∘ Subgroup.quotientMapOfLE hHw)
      (QuotientGroup.mk k)
  rw [hψv, hψw, hψvw, smul_add]

theorem ekAverage_const_smul [CharZero F] [SMulCommClass G F M] {K : Subgroup G} (c : F) (v : M)
    [Finite (↥K ⧸ MulAction.stabilizer K v)] :
    ekAverage F K (c • v) = c • ekAverage F K v := by
  classical
  letI := Fintype.ofFinite (↥K ⧸ MulAction.stabilizer K v)
  have hle : MulAction.stabilizer K v ≤ MulAction.stabilizer K (c • v) := by
    intro k hk
    rw [coe_mem_stabilizer_iff, smul_comm (k : G) c v, coe_mem_stabilizer_iff.mp hk]
  have hψ : ∀ k : ↥K,
      (fun x => c • MulAction.ofQuotientStabilizer K v x) (QuotientGroup.mk k) =
        (k : G) • (c • v) := by
    intro k
    simp only [MulAction.ofQuotientStabilizer_mk, Subgroup.smul_def]
    exact (smul_comm (k : G) c v).symm
  rw [ekAverage_eq_average_of_le_stabilizer (F := F)
      (ψ := fun x => c • MulAction.ofQuotientStabilizer K v x) hle hψ,
    ekAverage_eq_finsetSum]
  simp only [finsum_eq_sum_of_fintype]
  rw [← Finset.smul_sum, smul_smul, smul_smul, mul_comm]

theorem ekAverage_idem [CharZero F] [SMulCommClass G F M] (K : Subgroup G) (v : M)
    [Finite (↥K ⧸ MulAction.stabilizer K v)] :
    ekAverage F K (ekAverage F K v) = ekAverage F K v :=
  ekAverage_of_mem_fixedVectors (ekAverage_mem_fixedVectors K v)

theorem map_ekAverage [CharZero F] {K : Subgroup G} {N : Type*} [AddCommGroup N] [Module F N]
    [DistribMulAction G N] (f : M →ₗ[F] N) (hf : ∀ k ∈ K, ∀ m : M, f (k • m) = k • f m)
    (v : M) [Finite (↥K ⧸ MulAction.stabilizer K v)] :
    f (ekAverage F K v) = ekAverage F K (f v) := by
  classical
  letI := Fintype.ofFinite (↥K ⧸ MulAction.stabilizer K v)
  have hle : MulAction.stabilizer K v ≤ MulAction.stabilizer K (f v) := by
    intro k hk
    rw [coe_mem_stabilizer_iff, ← hf (k : G) k.2 v, coe_mem_stabilizer_iff.mp hk]
  have hψ : ∀ k : ↥K,
      (fun x => f (MulAction.ofQuotientStabilizer K v x)) (QuotientGroup.mk k) =
        (k : G) • f v := by
    intro k
    simp only [MulAction.ofQuotientStabilizer_mk, Subgroup.smul_def]
    exact hf (k : G) k.2 v
  rw [ekAverage_eq_average_of_le_stabilizer (F := F)
      (ψ := fun x => f (MulAction.ofQuotientStabilizer K v x)) hle hψ,
    ekAverage_eq_finsetSum]
  simp only [finsum_eq_sum_of_fintype]
  rw [map_smul, map_sum]

end Properties
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

section Bundled

variable (F : Type*) [Field F] [CharZero F] {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
  [Module F M] [DistribMulAction G M] [SMulCommClass G F M]

variable (K : Subgroup G)

noncomputable def ekAverageHom (hfin : ∀ v : M, Finite (↥K ⧸ MulAction.stabilizer K v)) :
    M →ₗ[F] M where
  toFun v := ekAverage F K v
  map_add' v w := by
    haveI := hfin v
    haveI := hfin w
    exact ekAverage_add
  map_smul' c v := by
    haveI := hfin v
    simpa using ekAverage_const_smul (F := F) c v

@[scoped simp] theorem ekAverageHom_apply (hfin : ∀ v : M, Finite (↥K ⧸ MulAction.stabilizer K v))
    (v : M) : ekAverageHom F K hfin v = ekAverage F K v :=
  rfl

theorem isProj_ekAverageHom (hfin : ∀ v : M, Finite (↥K ⧸ MulAction.stabilizer K v)) :
    LinearMap.IsProj (fixedVectors K F M) (ekAverageHom F K hfin) := by
  constructor
  · intro v
    haveI := hfin v
    exact ekAverage_mem_fixedVectors K v
  · intro v hv
    exact ekAverage_of_mem_fixedVectors hv

theorem range_ekAverageHom (hfin : ∀ v : M, Finite (↥K ⧸ MulAction.stabilizer K v)) :
    LinearMap.range (ekAverageHom F K hfin) = fixedVectors K F M :=
  (isProj_ekAverageHom F K hfin).range

theorem ekAverageHom_comp_ekAverageHom
    (hfin : ∀ v : M, Finite (↥K ⧸ MulAction.stabilizer K v)) :
    (ekAverageHom F K hfin).comp (ekAverageHom F K hfin) = ekAverageHom F K hfin := by
  apply LinearMap.ext
  intro v
  haveI := hfin v
  simp only [LinearMap.comp_apply, ekAverageHom_apply]
  exact ekAverage_idem K v

theorem ekAverageHom_comm {N : Type*} [AddCommGroup N] [Module F N] [DistribMulAction G N]
    [SMulCommClass G F N] (hfinM : ∀ v : M, Finite (↥K ⧸ MulAction.stabilizer K v))
    (hfinN : ∀ w : N, Finite (↥K ⧸ MulAction.stabilizer K w)) (f : M →ₗ[F] N)
    (hf : ∀ k ∈ K, ∀ m : M, f (k • m) = k • f m) :
    f.comp (ekAverageHom F K hfinM) = (ekAverageHom F K hfinN).comp f := by
  apply LinearMap.ext
  intro v
  haveI := hfinM v
  simp only [LinearMap.comp_apply, ekAverageHom_apply]
  exact map_ekAverage f hf v

end Bundled
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

section Topological

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [MulAction G M]

theorem finite_quotient_stabilizer_of_isCompact_of_isSmoothVector {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) {v : M} (hv : IsSmoothVector G v) :
    Finite (↥K ⧸ MulAction.stabilizer K v) := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKc
  have hopen : IsOpen ((MulAction.stabilizer K v : Subgroup ↥K) : Set ↥K) :=
    hv.restrict_subgroup K
  exact Subgroup.quotient_finite_of_isOpen (MulAction.stabilizer K v) hopen

theorem forall_finite_quotient_stabilizer_of_isCompact [ContinuousSMulDiscrete G M]
    {K : Subgroup G} (hKc : IsCompact (K : Set G)) (v : M) :
    Finite (↥K ⧸ MulAction.stabilizer K v) :=
  finite_quotient_stabilizer_of_isCompact_of_isSmoothVector hKc
    (isSmoothVector_of_continuousSMulDiscrete v)

end Topological
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

end FLT.EKAverage
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier"

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace EKAverage
p2m_open "FLT"

open FLT.AdmissibleRep

theorem fixedVectors_eq_fixedSubmodule {G : Type*} [Group G] (K : Subgroup G) (V : Type*)
    [AddCommGroup V] [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] :
    fixedVectors K ℂ V = LocalNewvector.fixedSubmodule K V := by
  ext v
  exact Iff.rfl

#print axioms FLT.EKAverage.ekAverage
#print axioms FLT.EKAverage.ekAverage_eq_average_of_le_stabilizer
#print axioms FLT.EKAverage.ekAverage_eq_average_of_subgroupOf_le_stabilizer
#print axioms FLT.EKAverage.smul_ekAverage
#print axioms FLT.EKAverage.ekAverage_mem_fixedVectors
#print axioms FLT.EKAverage.ekAverage_of_mem_fixedVectors
#print axioms FLT.EKAverage.ekAverage_add
#print axioms FLT.EKAverage.ekAverage_const_smul
#print axioms FLT.EKAverage.ekAverage_idem
#print axioms FLT.EKAverage.map_ekAverage
#print axioms FLT.EKAverage.isProj_ekAverageHom
#print axioms FLT.EKAverage.range_ekAverageHom
#print axioms FLT.EKAverage.ekAverageHom_comp_ekAverageHom
#print axioms FLT.EKAverage.ekAverageHom_comm
#print axioms FLT.EKAverage.finite_quotient_stabilizer_of_isCompact_of_isSmoothVector
#print axioms FLT.EKAverage.forall_finite_quotient_stabilizer_of_isCompact
#print axioms FLT.EKAverage.fixedVectors_eq_fixedSubmodule

end FLT.EKAverage
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end DeskModule00
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section DeskModule01

set_option autoImplicit false

noncomputable section

open Matrix

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"
open LocalNewvector

variable (p : ℕ) [Fact p.Prime]

section Cells

def lowerUnip (y : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  ⟨!![1, 0; y, 1], !![1, 0; -y, 1],
   by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
   by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[scoped simp] theorem coe_lowerUnip (y : ℚ_[p]) :
    (lowerUnip p y : Matrix (Fin 2) (Fin 2) ℚ_[p]) = !![1, 0; y, 1] := rfl

theorem lowerUnip_zero : lowerUnip p 0 = 1 := by
  apply Units.ext
  show (lowerUnip p 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem lowerUnip_add (y z : ℚ_[p]) : lowerUnip p (y + z) = lowerUnip p y * lowerUnip p z := by
  apply Units.ext
  show (lowerUnip p (y + z) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = (lowerUnip p y : Matrix (Fin 2) (Fin 2) ℚ_[p]) * (lowerUnip p z : Matrix (Fin 2) (Fin 2) ℚ_[p])
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lowerUnip_inv (y : ℚ_[p]) : (lowerUnip p y)⁻¹ = lowerUnip p (-y) :=
  Units.ext rfl

def weyl : GL (Fin 2) ℚ_[p] := LocalGL2.weylInt ℤ_[p] ℚ_[p]

@[scoped simp] theorem coe_weyl : (weyl p : Matrix (Fin 2) (Fin 2) ℚ_[p]) = !![0, 1; 1, 0] :=
  LocalGL2.coe_weylInt

theorem weyl_mul_weyl : weyl p * weyl p = 1 := by
  apply Units.ext
  show (weyl p : Matrix (Fin 2) (Fin 2) ℚ_[p]) * (weyl p : Matrix (Fin 2) (Fin 2) ℚ_[p]) = 1
  rw [coe_weyl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_inv : (weyl p)⁻¹ = weyl p :=
  inv_eq_of_mul_eq_one_right (weyl_mul_weyl p)

theorem weyl_mem_integralSubgroup : weyl p ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  LocalGL2.weylInt_mem

theorem weyl_mul_borelElem_one_one_mul_weyl (x : ℚ_[p]) :
    weyl p * borelElem p 1 1 x * weyl p = lowerUnip p x := by
  apply Units.ext
  show (weyl p : Matrix (Fin 2) (Fin 2) ℚ_[p]) * (borelElem p 1 1 x : Matrix (Fin 2) (Fin 2) ℚ_[p])
      * (weyl p : Matrix (Fin 2) (Fin 2) ℚ_[p]) = (lowerUnip p x : Matrix (Fin 2) (Fin 2) ℚ_[p])
  rw [coe_weyl, coe_borelElem, coe_lowerUnip]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_mul_borelElem_zero_mul_weyl (a₁ a₂ : ℚ_[p]ˣ) :
    weyl p * borelElem p a₁ a₂ 0 * weyl p = borelElem p a₂ a₁ 0 := by
  apply Units.ext
  show (weyl p : Matrix (Fin 2) (Fin 2) ℚ_[p]) * (borelElem p a₁ a₂ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p])
      * (weyl p : Matrix (Fin 2) (Fin 2) ℚ_[p]) = (borelElem p a₂ a₁ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p])
  rw [coe_weyl, coe_borelElem, coe_borelElem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerUnip_mul_borelElem_zero (y : ℚ_[p]) (a₁ a₂ : ℚ_[p]ˣ) :
    lowerUnip p y * borelElem p a₁ a₂ 0
      = borelElem p a₁ a₂ 0 * lowerUnip p ((a₁ : ℚ_[p]) * y * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p])) := by
  apply Units.ext
  show (lowerUnip p y : Matrix (Fin 2) (Fin 2) ℚ_[p]) * (borelElem p a₁ a₂ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = (borelElem p a₁ a₂ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) * (lowerUnip p _ : Matrix (Fin 2) (Fin 2) ℚ_[p])
  rw [coe_lowerUnip, coe_borelElem, coe_lowerUnip]
  have h2 : (a₂ : ℚ_[p]) ≠ 0 := a₂.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
  all_goals (try field_simp)

theorem borelElem_one_one_mul_borelElem_zero (x : ℚ_[p]) (a₁ a₂ : ℚ_[p]ˣ) :
    borelElem p 1 1 x * borelElem p a₁ a₂ 0
      = borelElem p a₁ a₂ 0 * borelElem p 1 1 (((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * (a₂ : ℚ_[p])) := by
  rw [borelElem_mul, borelElem_mul, one_mul, one_mul, mul_one, mul_one]
  congr 1
  have h1 : (a₁ : ℚ_[p]) ≠ 0 := a₁.ne_zero
  rw [Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem entry_det_ne_zero (g : GL (Fin 2) ℚ_[p]) :
    (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1
      - (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 ≠ 0 := by
  have h := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  rwa [Matrix.det_fin_two] at h

theorem eq_borelElem_mul_lowerUnip (g : GL (Fin 2) ℚ_[p])
    (h : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 ≠ 0) :
    g = borelElem p
          (Units.mk0 (((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1
              - (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0)
              / (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)
            (div_ne_zero (entry_det_ne_zero p g) h))
          (Units.mk0 ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1) h)
          ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1)
        * lowerUnip p ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 / (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1) := by
  apply Units.ext
  rw [Units.val_mul, coe_borelElem, coe_lowerUnip]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_bigCell (g : GL (Fin 2) ℚ_[p]) (h : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 ≠ 0) :
    ∃ (a₁ a₂ : ℚ_[p]ˣ),
      (a₁ : ℚ_[p]) * (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1
          = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1
            - (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 ∧
      (a₂ : ℚ_[p]) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 ∧
      g = borelElem p a₁ a₂ ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1)
            * lowerUnip p ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 / (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1) := by
  refine ⟨_, _, ?_, rfl, eq_borelElem_mul_lowerUnip p g h⟩
  rw [Units.val_mk0, div_mul_cancel₀ _ h]

theorem eq_borelElem_mul_weyl (g : GL (Fin 2) ℚ_[p])
    (h : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 0) :
    ∃ (h01 : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 ≠ 0) (h10 : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 ≠ 0),
      g = borelElem p (Units.mk0 _ h01) (Units.mk0 _ h10) ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0)
            * weyl p := by
  have hdet := entry_det_ne_zero p g
  rw [h, mul_zero, zero_sub, neg_ne_zero, mul_ne_zero_iff] at hdet
  refine ⟨hdet.1, hdet.2, ?_⟩
  apply Units.ext
  rw [Units.val_mul, coe_borelElem, coe_weyl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h]

theorem lowerUnip_eq_borelElem_mul_weyl_mul (y : ℚ_[p]) (hy : y ≠ 0) :
    lowerUnip p y
      = borelElem p (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy))) (Units.mk0 y hy) 1
          * weyl p * borelElem p 1 1 y⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_borelElem, coe_weyl, coe_borelElem, coe_lowerUnip]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy]

theorem weyl_mul_borelElem_one_one_mem_integralSubgroup {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    weyl p * borelElem p 1 1 x ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  mul_mem (weyl_mem_integralSubgroup p)
    ((borelElem_mem_integralSubgroup_iff p 1 1 x).mpr ⟨by simp, by simp, hx⟩)

theorem lowerUnip_mem_integralSubgroup {y : ℚ_[p]} (hy : ‖y‖ ≤ 1) :
    lowerUnip p y ∈ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by
  rw [← weyl_mul_borelElem_one_one_mul_weyl]
  exact mul_mem (weyl_mul_borelElem_one_one_mem_integralSubgroup p hy) (weyl_mem_integralSubgroup p)

end Cells
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section LawFactor

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

def lawFactor (a₁ a₂ : ℚ_[p]ˣ) : ℂ :=
  (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂

theorem lawFactor_mul (a₁ a₂ b₁ b₂ : ℚ_[p]ˣ) :
    lawFactor p μ₁ μ₂ (a₁ * b₁) (a₂ * b₂) = lawFactor p μ₁ μ₂ a₁ a₂ * lawFactor p μ₁ μ₂ b₁ b₂ := by
  simp only [lawFactor, map_mul, Units.val_mul, halfModulus_mul]
  ring

@[scoped simp] theorem lawFactor_one : lawFactor p μ₁ μ₂ 1 1 = 1 := by
  simp [lawFactor]

theorem halfModulus_ne_zero (a₁ a₂ : ℚ_[p]ˣ) : halfModulus p a₁ a₂ ≠ 0 := by
  simp only [halfModulus, ne_eq, Complex.ofReal_eq_zero]
  have h1 : 0 < ‖(a₁ : ℚ_[p])‖ := norm_pos_iff.mpr a₁.ne_zero
  have h2 : 0 < ‖(a₂ : ℚ_[p])‖ := norm_pos_iff.mpr a₂.ne_zero
  exact (Real.sqrt_pos.mpr (div_pos h1 h2)).ne'

theorem lawFactor_ne_zero (a₁ a₂ : ℚ_[p]ˣ) : lawFactor p μ₁ μ₂ a₁ a₂ ≠ 0 :=
  mul_ne_zero (mul_ne_zero (μ₁ a₁).ne_zero (μ₂ a₂).ne_zero) (halfModulus_ne_zero p a₁ a₂)

theorem lawFactor_eq_one_of_norm_eq_one (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    {a₁ a₂ : ℚ_[p]ˣ} (ha₁ : ‖(a₁ : ℚ_[p])‖ = 1) (ha₂ : ‖(a₂ : ℚ_[p])‖ = 1) :
    lawFactor p μ₁ μ₂ a₁ a₂ = 1 := by
  rw [lawFactor, h₁ a₁ ha₁, h₂ a₂ ha₂, halfModulus_eq_one_of_norm_eq_one p ha₁ ha₂]
  simp

theorem apply_borelElem_mul {f : GL (Fin 2) ℚ_[p] → ℂ}
    (hf : f ∈ principalSeries p μ₁ μ₂) (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]) :
    f (borelElem p a₁ a₂ x * g) = lawFactor p μ₁ μ₂ a₁ a₂ * f g :=
  apply_borelElem_mul_of_mem_principalSeries p hf a₁ a₂ x g

theorem apply_borelElem {f : GL (Fin 2) ℚ_[p] → ℂ}
    (hf : f ∈ principalSeries p μ₁ μ₂) (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    f (borelElem p a₁ a₂ x) = lawFactor p μ₁ μ₂ a₁ a₂ * f 1 := by
  rw [← apply_borelElem_mul p μ₁ μ₂ hf a₁ a₂ x 1, mul_one]

end LawFactor
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section Bumps

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

def InBall (k : ℤ) (g : GL (Fin 2) ℚ_[p]) : Prop :=
  (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 ≠ 0 ∧
    ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 / (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1‖ ≤ (p : ℝ) ^ (-k)

open Classical in

def bumpFn (k : ℤ) (g : GL (Fin 2) ℚ_[p]) : ℂ :=
  if h : InBall p k g then
    lawFactor p μ₁ μ₂
      (Units.mk0 (((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1
          - (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0)
          / (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1) (div_ne_zero (entry_det_ne_zero p g) h.1))
      (Units.mk0 ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1) h.1)
  else 0

theorem bumpFn_of_not_inBall {k : ℤ} {g : GL (Fin 2) ℚ_[p]} (h : ¬ InBall p k g) :
    bumpFn p μ₁ μ₂ k g = 0 := by
  unfold bumpFn
  rw [dif_neg h]

theorem coe_borelElem_mul_lowerUnip (a₁ a₂ : ℚ_[p]ˣ) (x y : ℚ_[p]) :
    ((borelElem p a₁ a₂ x * lowerUnip p y : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![(a₁ : ℚ_[p]) + x * y, x; (a₂ : ℚ_[p]) * y, (a₂ : ℚ_[p])] := by
  rw [Units.val_mul, coe_borelElem, coe_lowerUnip]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem inBall_borelElem_mul_lowerUnip_iff (k : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x y : ℚ_[p]) :
    InBall p k (borelElem p a₁ a₂ x * lowerUnip p y) ↔ ‖y‖ ≤ (p : ℝ) ^ (-k) := by
  have h2 : (a₂ : ℚ_[p]) ≠ 0 := a₂.ne_zero
  simp only [InBall, coe_borelElem_mul_lowerUnip, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  rw [mul_div_cancel_left₀ y h2]
  exact ⟨fun h => h.2, fun h => ⟨h2, h⟩⟩

theorem bumpFn_borelElem_mul_lowerUnip (k : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x y : ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (borelElem p a₁ a₂ x * lowerUnip p y)
      = if ‖y‖ ≤ (p : ℝ) ^ (-k) then lawFactor p μ₁ μ₂ a₁ a₂ else 0 := by
  by_cases hy : ‖y‖ ≤ (p : ℝ) ^ (-k)
  · have hin : InBall p k (borelElem p a₁ a₂ x * lowerUnip p y) :=
      (inBall_borelElem_mul_lowerUnip_iff p k a₁ a₂ x y).mpr hy
    rw [if_pos hy]
    unfold bumpFn
    rw [dif_pos hin]
    have h2 : (a₂ : ℚ_[p]) ≠ 0 := a₂.ne_zero
    congr 1
    · apply Units.ext
      simp only [Units.val_mk0, coe_borelElem_mul_lowerUnip, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
      field_simp
      ring
    · apply Units.ext
      simp
  · rw [if_neg hy, bumpFn_of_not_inBall]
    exact fun h => hy ((inBall_borelElem_mul_lowerUnip_iff p k a₁ a₂ x y).mp h)

theorem bumpFn_borelElem_mul_weyl (k : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (borelElem p a₁ a₂ x * weyl p) = 0 := by
  apply bumpFn_of_not_inBall
  intro h
  apply h.1
  rw [Units.val_mul, coe_borelElem, coe_weyl]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem bumpFn_lowerUnip (k : ℤ) (y : ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (lowerUnip p y) = if ‖y‖ ≤ (p : ℝ) ^ (-k) then 1 else 0 := by
  have h := bumpFn_borelElem_mul_lowerUnip p μ₁ μ₂ k 1 1 0 y
  rwa [borelElem_one, one_mul, lawFactor_one] at h

@[scoped simp] theorem bumpFn_one (k : ℤ) : bumpFn p μ₁ μ₂ k 1 = 1 := by
  rw [← lowerUnip_zero, bumpFn_lowerUnip, if_pos]
  rw [norm_zero]
  exact zpow_nonneg (Nat.cast_nonneg p) _

@[scoped simp] theorem bumpFn_weyl (k : ℤ) : bumpFn p μ₁ μ₂ k (weyl p) = 0 := by
  have h := bumpFn_borelElem_mul_weyl p μ₁ μ₂ k 1 1 0
  rwa [borelElem_one, one_mul] at h

theorem cell_cases (g : GL (Fin 2) ℚ_[p]) :
    (∃ (a₁ a₂ : ℚ_[p]ˣ) (x y : ℚ_[p]), g = borelElem p a₁ a₂ x * lowerUnip p y) ∨
    (∃ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]), g = borelElem p a₁ a₂ x * weyl p) := by
  by_cases h : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 0
  · obtain ⟨h01, h10, hg⟩ := eq_borelElem_mul_weyl p g h
    exact Or.inr ⟨_, _, _, hg⟩
  · exact Or.inl ⟨_, _, _, _, eq_borelElem_mul_lowerUnip p g h⟩

theorem bumpFn_borelElem_mul (k : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (borelElem p a₁ a₂ x * g) = lawFactor p μ₁ μ₂ a₁ a₂ * bumpFn p μ₁ μ₂ k g := by
  rcases cell_cases p g with ⟨b₁, b₂, x', y, rfl⟩ | ⟨b₁, b₂, x', rfl⟩
  · rw [← mul_assoc, borelElem_mul, bumpFn_borelElem_mul_lowerUnip, bumpFn_borelElem_mul_lowerUnip]
    split_ifs
    · rw [lawFactor_mul]
    · rw [mul_zero]
  · rw [← mul_assoc, borelElem_mul, bumpFn_borelElem_mul_weyl, bumpFn_borelElem_mul_weyl, mul_zero]

open FLT.SmoothVectors in

theorem coe_lowerUnip_mul (r : ℚ_[p]) (κ : GL (Fin 2) ℚ_[p]) :
    ((lowerUnip p r * κ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![(κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0, (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1;
           r * (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 + (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0,
           r * (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 + (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1] := by
  rw [Units.val_mul, coe_lowerUnip]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem one_lt_p_real : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Nat.Prime.one_lt (Fact.out (p := p.Prime)))

open FLT.SmoothVectors in

theorem inBall_mul_and_bumpFn_mul_eq (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    {k : ℤ} {m : ℕ} (hm1 : 1 ≤ m) (hmk : k ≤ (m : ℤ)) (hmk' : 1 - k ≤ (m : ℤ))
    {g κ : GL (Fin 2) ℚ_[p]} (hg : InBall p k g) (hκ : κ ∈ gl2CongruenceSubgroup p m) :
    InBall p k (g * κ) ∧ bumpFn p μ₁ μ₂ k (g * κ) = bumpFn p μ₁ μ₂ k g := by

  have hp1 := one_lt_p_real p
  set ε : ℝ := (p : ℝ) ^ (-(m : ℤ)) with hε
  have hE : ∀ i j, ‖((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ ε :=
    ((mem_gl2CongruenceSubgroup_iff p).mp hκ).1
  have hε1 : ε < 1 := zpow_lt_one_of_neg₀ hp1 (by omega)
  have hεle1 : ε ≤ 1 := hε1.le
  have hεk : ε ≤ (p : ℝ) ^ (-k) := zpow_le_zpow_right₀ hp1.le (by omega)
  have hrk : (p : ℝ) ^ (-k) * ε < 1 := by
    rw [hε, ← zpow_add₀ (ne_of_gt (lt_trans zero_lt_one hp1))]
    exact zpow_lt_one_of_neg₀ hp1 (by omega)
  obtain ⟨hg11, hr⟩ := hg
  set r : ℚ_[p] := (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 / (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 with hr_def

  have e00 : (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 = ((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 0 0 + 1 := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq]; ring
  have e11 : (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = ((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 1 + 1 := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq]; ring
  have e01 : (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 = ((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 0 1 := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide)]; ring
  have e10 : (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = ((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 0 := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide)]; ring

  set u : ℚ_[p] := r * (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 + (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 with hu_def
  set v : ℚ_[p] := r * (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 + (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 with hv_def
  have hu1 : ‖u - 1‖ < 1 := by
    have hsplit : u - 1 = r * ((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 0 1
        + ((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 1 := by
      rw [hu_def, e01, e11]; ring
    rw [hsplit]
    refine lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt ?_ (lt_of_le_of_lt (hE 1 1) hε1))
    rw [norm_mul]
    calc ‖r‖ * ‖((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 0 1‖ ≤ (p : ℝ) ^ (-k) * ε :=
          mul_le_mul hr (hE 0 1) (norm_nonneg _) (zpow_nonneg (Nat.cast_nonneg p) _)
      _ < 1 := hrk
  have hun : ‖u‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one p hu1
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hun]; exact one_ne_zero)
  have hvk : ‖v‖ ≤ (p : ℝ) ^ (-k) := by
    have hsplit : v = r + (r * ((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 0 0
        + ((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 0) := by
      rw [hv_def, e00, e10]; ring
    rw [hsplit]
    refine le_trans (Padic.nonarchimedean _ _) (max_le hr ?_)
    refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ (le_trans (hE 1 0) hεk))
    rw [norm_mul]
    calc ‖r‖ * ‖((κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 0 0‖ ≤ (p : ℝ) ^ (-k) * 1 :=
          mul_le_mul hr (le_trans (hE 0 0) hεle1) (norm_nonneg _) (zpow_nonneg (Nat.cast_nonneg p) _)
      _ = (p : ℝ) ^ (-k) := mul_one _
  have hvu : ‖v / u‖ ≤ (p : ℝ) ^ (-k) := by rw [norm_div, hun, div_one]; exact hvk

  obtain ⟨A₁, A₂, _, hA₂, hdec⟩ := exists_bigCell p g hg11
  set g' : GL (Fin 2) ℚ_[p] := lowerUnip p r * κ with hg'_def
  have hg'11 : (g' : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = u := by
    rw [hg'_def, coe_lowerUnip_mul]; simp [hu_def]
  have hg'10 : (g' : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = v := by
    rw [hg'_def, coe_lowerUnip_mul]; simp [hv_def]
  have hg'00 : (g' : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 = (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 := by
    rw [hg'_def, coe_lowerUnip_mul]; simp
  have hg'01 : (g' : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 = (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 := by
    rw [hg'_def, coe_lowerUnip_mul]; simp
  have hg'11ne : (g' : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 ≠ 0 := by rw [hg'11]; exact hu0
  obtain ⟨a₁, a₂, ha₁, ha₂, hdec'⟩ := exists_bigCell p g' hg'11ne
  rw [hg'11, hg'10] at hdec'
  rw [hg'11] at ha₂
  rw [hg'11, hg'00, hg'01, hg'10] at ha₁

  have hdetκ : ‖(κ : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ = 1 := norm_det_eq_one_of_sub_entry_le p hε1 κ hE
  have ha₁u : (a₁ : ℚ_[p]) * u = (κ : Matrix (Fin 2) (Fin 2) ℚ_[p]).det := by
    rw [ha₁, Matrix.det_fin_two, hu_def, hv_def]; ring
  have hna₂ : ‖(a₂ : ℚ_[p])‖ = 1 := by rw [ha₂]; exact hun
  have hna₁ : ‖(a₁ : ℚ_[p])‖ = 1 := by
    have h := congrArg (fun z : ℚ_[p] => ‖z‖) ha₁u
    simp only [norm_mul, hun, mul_one, hdetκ] at h
    exact h

  obtain ⟨X, hprod⟩ : ∃ X : ℚ_[p], g * κ = borelElem p (A₁ * a₁) (A₂ * a₂) X * lowerUnip p (v / u) :=
    ⟨_, by rw [hdec, mul_assoc, ← hg'_def, hdec', ← mul_assoc, borelElem_mul]⟩
  constructor
  · rw [hprod]
    exact (inBall_borelElem_mul_lowerUnip_iff p k _ _ _ _).mpr hvu
  · rw [hprod, bumpFn_borelElem_mul_lowerUnip, if_pos hvu, lawFactor_mul,
      lawFactor_eq_one_of_norm_eq_one p μ₁ μ₂ h₁ h₂ hna₁ hna₂, mul_one,
      hdec, bumpFn_borelElem_mul_lowerUnip, if_pos hr]

open FLT.SmoothVectors in

theorem bumpFn_mul_of_mem_gl2CongruenceSubgroup (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    {k : ℤ} {m : ℕ} (hm1 : 1 ≤ m) (hmk : k ≤ (m : ℤ)) (hmk' : 1 - k ≤ (m : ℤ))
    (g : GL (Fin 2) ℚ_[p]) {κ : GL (Fin 2) ℚ_[p]} (hκ : κ ∈ gl2CongruenceSubgroup p m) :
    bumpFn p μ₁ μ₂ k (g * κ) = bumpFn p μ₁ μ₂ k g := by
  by_cases hg : InBall p k g
  · exact (inBall_mul_and_bumpFn_mul_eq p μ₁ μ₂ h₁ h₂ hm1 hmk hmk' hg hκ).2
  · have hgκ : ¬ InBall p k (g * κ) := by
      intro h
      have h' := (inBall_mul_and_bumpFn_mul_eq p μ₁ μ₂ h₁ h₂ hm1 hmk hmk' h (inv_mem hκ)).1
      rw [mul_inv_cancel_right] at h'
      exact hg h'
    rw [bumpFn_of_not_inBall p μ₁ μ₂ hg, bumpFn_of_not_inBall p μ₁ μ₂ hgκ]

open FLT.SmoothVectors in

theorem bumpFn_mem_rightInvariantFunctions (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    {k : ℤ} {m : ℕ} (hm1 : 1 ≤ m) (hmk : k ≤ (m : ℤ)) (hmk' : 1 - k ≤ (m : ℤ)) :
    bumpFn p μ₁ μ₂ k ∈ rightInvariantFunctions p (gl2CongruenceSubgroup p m) :=
  (mem_rightInvariantFunctions_iff p).mpr fun _ hκ g =>
    bumpFn_mul_of_mem_gl2CongruenceSubgroup p μ₁ μ₂ h₁ h₂ hm1 hmk hmk' g hκ

def levelOf (k : ℤ) : ℕ := Int.toNat (max 1 (max k (1 - k)))

theorem one_le_levelOf (k : ℤ) : 1 ≤ levelOf k := by
  unfold levelOf; omega

theorem le_levelOf (k : ℤ) : k ≤ (levelOf k : ℤ) := by
  unfold levelOf; omega

theorem one_sub_le_levelOf (k : ℤ) : 1 - k ≤ (levelOf k : ℤ) := by
  unfold levelOf; omega

open FLT.SmoothVectors in

theorem bumpFn_mem_principalSeries (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) (k : ℤ) :
    bumpFn p μ₁ μ₂ k ∈ principalSeries p μ₁ μ₂ :=
  (mem_principalSeries_iff p).mpr
    ⟨isLocallyConstant_of_mem_rightInvariantFunctions p (isOpen_coe_gl2CongruenceSubgroup p (levelOf k))
        (bumpFn_mem_rightInvariantFunctions p μ₁ μ₂ h₁ h₂ (one_le_levelOf k) (le_levelOf k)
          (one_sub_le_levelOf k)),
      fun a₁ a₂ x g => bumpFn_borelElem_mul p μ₁ μ₂ k a₁ a₂ x g⟩

theorem bumpFn_ne_zero (k : ℤ) : bumpFn p μ₁ μ₂ k ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  rw [bumpFn_one, Pi.zero_apply] at h1
  exact one_ne_zero h1

end Bumps
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section Audit
#print axioms FLT.PrincipalSeriesGL2Padic.lowerUnip
#print axioms FLT.PrincipalSeriesGL2Padic.weyl_mul_weyl
#print axioms FLT.PrincipalSeriesGL2Padic.weyl_mul_borelElem_one_one_mul_weyl
#print axioms FLT.PrincipalSeriesGL2Padic.weyl_mul_borelElem_zero_mul_weyl
#print axioms FLT.PrincipalSeriesGL2Padic.lowerUnip_mul_borelElem_zero
#print axioms FLT.PrincipalSeriesGL2Padic.borelElem_one_one_mul_borelElem_zero
#print axioms FLT.PrincipalSeriesGL2Padic.eq_borelElem_mul_lowerUnip
#print axioms FLT.PrincipalSeriesGL2Padic.exists_bigCell
#print axioms FLT.PrincipalSeriesGL2Padic.eq_borelElem_mul_weyl
#print axioms FLT.PrincipalSeriesGL2Padic.lowerUnip_eq_borelElem_mul_weyl_mul
#print axioms FLT.PrincipalSeriesGL2Padic.lowerUnip_mem_integralSubgroup
#print axioms FLT.PrincipalSeriesGL2Padic.cell_cases
#print axioms FLT.PrincipalSeriesGL2Padic.lawFactor_mul
#print axioms FLT.PrincipalSeriesGL2Padic.lawFactor_ne_zero
#print axioms FLT.PrincipalSeriesGL2Padic.lawFactor_eq_one_of_norm_eq_one
#print axioms FLT.PrincipalSeriesGL2Padic.apply_borelElem
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_borelElem_mul_lowerUnip
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_borelElem_mul_weyl
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_lowerUnip
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_one
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_weyl
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_borelElem_mul
#print axioms FLT.PrincipalSeriesGL2Padic.inBall_mul_and_bumpFn_mul_eq
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_mul_of_mem_gl2CongruenceSubgroup
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_mem_rightInvariantFunctions
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_mem_principalSeries
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_ne_zero
end Audit
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end DeskModule01
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section DeskModule02

set_option autoImplicit false

noncomputable section

open FLT.PrincipalSeriesGL2Padic FLT.SmoothVectors LocalNewvector

namespace P6B
open LocalNewvector

variable (p : ℕ) [Fact p.Prime]

theorem norm_one_add_eq_one {t : ℚ_[p]} (ht : ‖t‖ < 1) : ‖(1 : ℚ_[p]) + t‖ = 1 := by
  have hne : ‖(1 : ℚ_[p])‖ ≠ ‖t‖ := by rw [norm_one]; exact (ne_of_lt ht).symm
  rw [Padic.add_eq_max_of_ne hne, norm_one]
  exact max_eq_left ht.le

theorem isUnramified_apply_eq_of_norm_lt {μ : ℚ_[p]ˣ →* ℂˣ} (hμ : IsUnramified p μ)
    (y v : ℚ_[p]ˣ) {w : ℚ_[p]} (hw : ‖w‖ < ‖(y : ℚ_[p])‖)
    (hv : (v : ℚ_[p]) = (y : ℚ_[p]) + w) : μ v = μ y := by
  have hpos : (0 : ℝ) < ‖(y : ℚ_[p])‖ := norm_pos_iff.mpr y.ne_zero
  have hcoe : ((y⁻¹ * v : ℚ_[p]ˣ) : ℚ_[p]) = 1 + ((y : ℚ_[p]))⁻¹ * w := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hv, mul_add,
      inv_mul_cancel₀ y.ne_zero]
  have hsmall : ‖((y : ℚ_[p]))⁻¹ * w‖ < 1 := by
    rw [norm_mul, norm_inv]
    calc ‖(y : ℚ_[p])‖⁻¹ * ‖w‖
        < ‖(y : ℚ_[p])‖⁻¹ * ‖(y : ℚ_[p])‖ :=
          mul_lt_mul_of_pos_left hw (inv_pos.mpr hpos)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have hnorm : ‖((y⁻¹ * v : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
    rw [hcoe]
    exact norm_one_add_eq_one p hsmall
  have hu : μ (y⁻¹ * v) = 1 := hμ _ hnorm
  calc μ v = μ (y * (y⁻¹ * v)) := by rw [mul_inv_cancel_left]
    _ = μ y * μ (y⁻¹ * v) := map_mul μ _ _
    _ = μ y := by rw [hu, mul_one]

theorem add_ne_zero_of_norm_lt {y z : ℚ_[p]} (hz : ‖z‖ < ‖y‖) :
    y + z ≠ 0 := by
  intro h0
  have hzy : z = -y := by linear_combination h0
  rw [hzy, norm_neg] at hz
  exact lt_irrefl _ hz

theorem isUnramified_apply_mk0_add {μ : ℚ_[p]ˣ →* ℂˣ} (hμ : IsUnramified p μ)
    {y z : ℚ_[p]} (hy : y ≠ 0) (hz : ‖z‖ < ‖y‖) :
    μ (Units.mk0 (y + z) (add_ne_zero_of_norm_lt p hz)) = μ (Units.mk0 y hy) :=
  isUnramified_apply_eq_of_norm_lt p hμ (Units.mk0 y hy)
    (Units.mk0 (y + z) (add_ne_zero_of_norm_lt p hz)) hz rfl

theorem exists_right_unipotent_level (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) (f : PSCarrier p μ₁ μ₂) :
    ∃ m : ℕ, ∀ (x : GL (Fin 2) ℚ_[p]) (z : ℚ_[p]), ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ)) →
      PSCarrier.toFn p μ₁ μ₂ f (x * borelElem p 1 1 z) = PSCarrier.toFn p μ₁ μ₂ f x := by
  have hsm : IsSmoothVector (GL (Fin 2) ℚ_[p]) f := PSCarrier.isSmoothVector_carrier p μ₁ μ₂ f
  rw [isSmoothVector_iff_isOpen_stabilizer] at hsm
  obtain ⟨m, hm⟩ := FLT.SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one p
    (hsm.mem_nhds (MulAction.stabilizer (GL (Fin 2) ℚ_[p]) f).one_mem)
  refine ⟨m, fun x z hz => ?_⟩
  have hz' : ‖z‖ ≤ ((p : ℝ) ^ m)⁻¹ := by rwa [zpow_neg, zpow_natCast] at hz
  have hval : (borelElem p 1 1 z : Matrix (Fin 2) (Fin 2) ℚ_[p]) = !![1, z; 0, 1] := by
    show !![((1 : ℚ_[p]ˣ) : ℚ_[p]), z; 0, ((1 : ℚ_[p]ˣ) : ℚ_[p])] = !![1, z; 0, 1]
    simp
  have hinv : (((borelElem p 1 1 z)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![1, -z; 0, 1] := by
    show !![((1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), -(((1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * z * ((1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]));
        0, ((1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])] = !![1, -z; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hmem : borelElem p 1 1 z ∈ FLT.SmoothVectors.gl2CongruenceSubgroup p m := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [hval]
      (fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply]); exact hz'
    · rw [hinv]
      (fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply, norm_neg]); exact hz'
  have hstab' := hm hmem
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hstab'
  calc PSCarrier.toFn p μ₁ μ₂ f (x * borelElem p 1 1 z)
      = PSCarrier.toFn p μ₁ μ₂ (borelElem p 1 1 z • f) x := rfl
    _ = PSCarrier.toFn p μ₁ μ₂ f x := by rw [hstab']

end P6B
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

#print axioms P6B.norm_one_add_eq_one
#print axioms P6B.isUnramified_apply_eq_of_norm_lt
#print axioms P6B.add_ne_zero_of_norm_lt
#print axioms P6B.isUnramified_apply_mk0_add
#print axioms P6B.exists_right_unipotent_level

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end DeskModule02
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section DeskModule03

set_option autoImplicit false

noncomputable section

open Matrix

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"
open LocalNewvector

variable (p : ℕ) [Fact p.Prime]

section Tail

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

def tailChar (y : ℚ_[p]ˣ) : ℂ :=
  (μ₂ y : ℂ) * ((μ₁ y : ℂ))⁻¹ * ((‖(y : ℚ_[p])‖ : ℂ))⁻¹

theorem tailChar_ne_zero (y : ℚ_[p]ˣ) : tailChar p μ₁ μ₂ y ≠ 0 := by
  have hy : (‖(y : ℚ_[p])‖ : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]
    exact y.ne_zero
  exact mul_ne_zero (mul_ne_zero (μ₂ y).ne_zero (inv_ne_zero (μ₁ y).ne_zero)) (inv_ne_zero hy)

theorem mk0_neg_inv (y : ℚ_[p]) (hy : y ≠ 0) :
    Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy)) = -(Units.mk0 y hy)⁻¹ := by
  apply Units.ext
  simp [Units.val_inv_eq_inv_val]

theorem halfModulus_neg_inv_self (y : ℚ_[p]) (hy : y ≠ 0) :
    halfModulus p (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy))) (Units.mk0 y hy)
      = ((‖y‖ : ℂ))⁻¹ := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  simp only [halfModulus, Units.val_mk0, norm_neg, norm_inv]
  rw [show ‖y‖⁻¹ / ‖y‖ = (‖y‖⁻¹) ^ 2 by rw [pow_two, div_eq_mul_inv],
    Real.sqrt_sq (inv_nonneg.mpr hn.le), Complex.ofReal_inv]

theorem lawFactor_neg_inv_self (y : ℚ_[p]) (hy : y ≠ 0) :
    lawFactor p μ₁ μ₂ (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy))) (Units.mk0 y hy)
      = (μ₁ (-1) : ℂ) * tailChar p μ₁ μ₂ (Units.mk0 y hy) := by
  rw [lawFactor, halfModulus_neg_inv_self p y hy, mk0_neg_inv p y hy,
    ← neg_one_mul ((Units.mk0 y hy)⁻¹), map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    tailChar, Units.val_mk0]
  ring

theorem apply_lowerUnip_eq_tail {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂)
    (y : ℚ_[p]) (hy : y ≠ 0) :
    f (lowerUnip p y)
      = (μ₁ (-1) : ℂ) * tailChar p μ₁ μ₂ (Units.mk0 y hy) * f (weyl p * borelElem p 1 1 y⁻¹) := by
  rw [lowerUnip_eq_borelElem_mul_weyl_mul p y hy, mul_assoc,
    apply_borelElem_mul p μ₁ μ₂ hf, lawFactor_neg_inv_self]

theorem apply_borelElem_mul_lowerUnip_eq_tail {f : GL (Fin 2) ℚ_[p] → ℂ}
    (hf : f ∈ principalSeries p μ₁ μ₂) (a₁ a₂ : ℚ_[p]ˣ) (x y : ℚ_[p]) (hy : y ≠ 0) :
    f (borelElem p a₁ a₂ x * lowerUnip p y)
      = lawFactor p μ₁ μ₂ a₁ a₂ * ((μ₁ (-1) : ℂ) * tailChar p μ₁ μ₂ (Units.mk0 y hy))
          * f (weyl p * borelElem p 1 1 y⁻¹) := by
  rw [apply_borelElem_mul p μ₁ μ₂ hf, apply_lowerUnip_eq_tail p μ₁ μ₂ hf y hy]
  ring

theorem tailChar_eq_of_norm_eq (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    {y y' : ℚ_[p]ˣ} (h : ‖(y : ℚ_[p])‖ = ‖(y' : ℚ_[p])‖) :
    tailChar p μ₁ μ₂ y = tailChar p μ₁ μ₂ y' := by
  have hq : ‖((y * y'⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, h,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr y'.ne_zero)]
  have e₁ : μ₁ y = μ₁ y' := by
    have := h₁ _ hq
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have e₂ : μ₂ y = μ₂ y' := by
    have := h₂ _ hq
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  rw [tailChar, tailChar, e₁, e₂, h]

end Tail
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section OtherChart

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

theorem weyl_mul_borelElem_one_one_eq (y : ℚ_[p]) (hy : y ≠ 0) :
    weyl p * borelElem p 1 1 y
      = borelElem p (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy))) (Units.mk0 y hy) 1
          * lowerUnip p y⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_weyl, coe_borelElem, coe_borelElem, coe_lowerUnip]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy]

theorem lowerUnip_mul_weyl (y : ℚ_[p]) : lowerUnip p y * weyl p = weyl p * borelElem p 1 1 y := by
  rw [← weyl_mul_borelElem_one_one_mul_weyl, mul_assoc, weyl_mul_weyl, mul_one]

theorem bumpFn_borelElem_mul_weyl_mul_borelElem_one_one (k : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x y : ℚ_[p])
    (hy : y ≠ 0) :
    bumpFn p μ₁ μ₂ k (borelElem p a₁ a₂ x * weyl p * borelElem p 1 1 y)
      = if ‖y⁻¹‖ ≤ (p : ℝ) ^ (-k)
        then lawFactor p μ₁ μ₂ a₁ a₂ * ((μ₁ (-1) : ℂ) * tailChar p μ₁ μ₂ (Units.mk0 y hy)) else 0 := by
  rw [mul_assoc, weyl_mul_borelElem_one_one_eq p y hy, ← mul_assoc, borelElem_mul,
    bumpFn_borelElem_mul_lowerUnip]
  split_ifs
  · rw [lawFactor_mul, lawFactor_neg_inv_self]
  · rfl

theorem bumpFn_borelElem_mul_weyl_mul_borelElem_one_one_zero (k : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (borelElem p a₁ a₂ x * weyl p * borelElem p 1 1 0) = 0 := by
  rw [borelElem_one, mul_one, bumpFn_borelElem_mul_weyl]

end OtherChart
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section Phi

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

def phiFn (s : ℤ) (g : GL (Fin 2) ℚ_[p]) : ℂ :=
  bumpFn p μ₁ μ₂ (-s) (g * weyl p)

theorem phiFn_apply (s : ℤ) (g : GL (Fin 2) ℚ_[p]) :
    phiFn p μ₁ μ₂ s g = bumpFn p μ₁ μ₂ (-s) (g * weyl p) := rfl

theorem bumpFn_eq_phiFn_mul_weyl (k : ℤ) (g : GL (Fin 2) ℚ_[p]) :
    bumpFn p μ₁ μ₂ k g = phiFn p μ₁ μ₂ (-k) (g * weyl p) := by
  rw [phiFn_apply, neg_neg, mul_assoc, weyl_mul_weyl, mul_one]

theorem phiFn_borelElem_mul_weyl_mul_borelElem_one_one (s : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x' x : ℚ_[p]) :
    phiFn p μ₁ μ₂ s (borelElem p a₁ a₂ x' * weyl p * borelElem p 1 1 x)
      = if ‖x‖ ≤ (p : ℝ) ^ s then lawFactor p μ₁ μ₂ a₁ a₂ else 0 := by
  rw [phiFn_apply, mul_assoc (borelElem p a₁ a₂ x'), mul_assoc (borelElem p a₁ a₂ x'),
    weyl_mul_borelElem_one_one_mul_weyl, bumpFn_borelElem_mul_lowerUnip, neg_neg]

theorem phiFn_borelElem_mul_lowerUnip (s : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x y : ℚ_[p]) (hy : y ≠ 0) :
    phiFn p μ₁ μ₂ s (borelElem p a₁ a₂ x * lowerUnip p y)
      = if (p : ℝ) ^ (-s) ≤ ‖y‖
        then lawFactor p μ₁ μ₂ a₁ a₂ * ((μ₁ (-1) : ℂ) * tailChar p μ₁ μ₂ (Units.mk0 y hy)) else 0 := by
  rw [phiFn_apply, mul_assoc, lowerUnip_mul_weyl, ← mul_assoc,
    bumpFn_borelElem_mul_weyl_mul_borelElem_one_one p μ₁ μ₂ (-s) a₁ a₂ x y hy, neg_neg]
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hps : 0 < (p : ℝ) ^ s := zpow_pos (lt_trans zero_lt_one (one_lt_p_real p)) s
  have hiff : ‖y⁻¹‖ ≤ (p : ℝ) ^ s ↔ (p : ℝ) ^ (-s) ≤ ‖y‖ := by
    rw [norm_inv, _root_.zpow_neg, inv_le_comm₀ hn hps]
  by_cases h : (p : ℝ) ^ (-s) ≤ ‖y‖
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

theorem phiFn_borelElem (s : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    phiFn p μ₁ μ₂ s (borelElem p a₁ a₂ x) = 0 := by
  rw [phiFn_apply, bumpFn_borelElem_mul_weyl]

@[scoped simp] theorem phiFn_one (s : ℤ) : phiFn p μ₁ μ₂ s 1 = 0 := by
  rw [← borelElem_one, phiFn_borelElem]

@[scoped simp] theorem phiFn_weyl (s : ℤ) : phiFn p μ₁ μ₂ s (weyl p) = 1 := by
  rw [phiFn_apply, weyl_mul_weyl, bumpFn_one]

theorem phiFn_borelElem_mul (s : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]) :
    phiFn p μ₁ μ₂ s (borelElem p a₁ a₂ x * g) = lawFactor p μ₁ μ₂ a₁ a₂ * phiFn p μ₁ μ₂ s g := by
  rw [phiFn_apply, phiFn_apply, mul_assoc, bumpFn_borelElem_mul]

theorem phiFn_mem_principalSeries (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) (s : ℤ) :
    phiFn p μ₁ μ₂ s ∈ principalSeries p μ₁ μ₂ :=
  rightTranslate_mem_principalSeries p (bumpFn_mem_principalSeries p μ₁ μ₂ h₁ h₂ (-s)) (weyl p)

theorem phiFn_ne_zero (s : ℤ) : phiFn p μ₁ μ₂ s ≠ 0 := by
  intro h
  have h1 := congrFun h (weyl p)
  rw [phiFn_weyl, Pi.zero_apply] at h1
  exact one_ne_zero h1

theorem phiFn_ne_bumpFn (s k : ℤ) : phiFn p μ₁ μ₂ s ≠ bumpFn p μ₁ μ₂ k := by
  intro h
  have h1 := congrFun h 1
  rw [phiFn_one, bumpFn_one] at h1
  exact zero_ne_one h1

end Phi
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section Dilation

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

theorem bumpFn_mul_borelElem_zero (k k' : ℤ) (a₁ a₂ : ℚ_[p]ˣ)
    (hkk' : ‖(a₁ : ℚ_[p])‖ * (p : ℝ) ^ (-k') = ‖(a₂ : ℚ_[p])‖ * (p : ℝ) ^ (-k))
    (g : GL (Fin 2) ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (g * borelElem p a₁ a₂ 0) = lawFactor p μ₁ μ₂ a₁ a₂ * bumpFn p μ₁ μ₂ k' g := by
  have ha₁ : 0 < ‖(a₁ : ℚ_[p])‖ := norm_pos_iff.mpr a₁.ne_zero
  have ha₂ : 0 < ‖(a₂ : ℚ_[p])‖ := norm_pos_iff.mpr a₂.ne_zero
  rcases cell_cases p g with ⟨b₁, b₂, x, y, rfl⟩ | ⟨b₁, b₂, x, rfl⟩
  · rw [mul_assoc, lowerUnip_mul_borelElem_zero, ← mul_assoc, borelElem_mul,
      bumpFn_borelElem_mul_lowerUnip, bumpFn_borelElem_mul_lowerUnip]
    have hiff : ‖(a₁ : ℚ_[p]) * y * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-k)
        ↔ ‖y‖ ≤ (p : ℝ) ^ (-k') := by
      rw [norm_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, ← div_eq_mul_inv, div_le_iff₀ ha₂,
        mul_comm ((p : ℝ) ^ (-k)), ← hkk', mul_le_mul_iff_right₀ ha₁]
    by_cases hy : ‖y‖ ≤ (p : ℝ) ^ (-k')
    · rw [if_pos (hiff.mpr hy), if_pos hy, lawFactor_mul, mul_comm]
    · rw [if_neg (fun h => hy (hiff.mp h)), if_neg hy, mul_zero]
  · rw [mul_assoc, show weyl p * borelElem p a₁ a₂ 0 = borelElem p a₂ a₁ 0 * weyl p by
        rw [← weyl_mul_borelElem_zero_mul_weyl p a₁ a₂, mul_assoc, weyl_mul_weyl, mul_one],
      ← mul_assoc, borelElem_mul, bumpFn_borelElem_mul_weyl, bumpFn_borelElem_mul_weyl, mul_zero]

def pUnit : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))

@[scoped simp] theorem val_pUnit : (pUnit p : ℚ_[p]) = p := rfl

theorem norm_pUnit : ‖(pUnit p : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [val_pUnit, Padic.norm_p]

def diagP : GL (Fin 2) ℚ_[p] := borelElem p (pUnit p) 1 0

def diagPw : GL (Fin 2) ℚ_[p] := borelElem p 1 (pUnit p) 0

theorem weyl_mul_diagP_mul_weyl : weyl p * diagP p * weyl p = diagPw p :=
  weyl_mul_borelElem_zero_mul_weyl p _ _

theorem weyl_mul_diagPw_mul_weyl : weyl p * diagPw p * weyl p = diagP p :=
  weyl_mul_borelElem_zero_mul_weyl p _ _

theorem bumpFn_mul_diagP (k : ℤ) (g : GL (Fin 2) ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (g * diagP p) = lawFactor p μ₁ μ₂ (pUnit p) 1 * bumpFn p μ₁ μ₂ (k - 1) g := by
  refine bumpFn_mul_borelElem_zero p μ₁ μ₂ k (k - 1) (pUnit p) 1 ?_ g
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one (one_lt_p_real p))
  rw [norm_pUnit, Units.val_one, norm_one, one_mul, neg_sub, ← _root_.zpow_neg_one, ← zpow_add₀ hp0]
  congr 1
  ring

theorem bumpFn_mul_diagPw (k : ℤ) (g : GL (Fin 2) ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (g * diagPw p) = lawFactor p μ₁ μ₂ 1 (pUnit p) * bumpFn p μ₁ μ₂ (k + 1) g := by
  refine bumpFn_mul_borelElem_zero p μ₁ μ₂ k (k + 1) 1 (pUnit p) ?_ g
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one (one_lt_p_real p))
  rw [norm_pUnit, Units.val_one, norm_one, one_mul, ← _root_.zpow_neg_one, ← zpow_add₀ hp0]
  congr 1
  ring

theorem bumpFn_mul_borelElem_zero_of_norm_eq_one (k : ℤ) {u₁ u₂ : ℚ_[p]ˣ}
    (hu₁ : ‖(u₁ : ℚ_[p])‖ = 1) (hu₂ : ‖(u₂ : ℚ_[p])‖ = 1) (g : GL (Fin 2) ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (g * borelElem p u₁ u₂ 0) = lawFactor p μ₁ μ₂ u₁ u₂ * bumpFn p μ₁ μ₂ k g :=
  bumpFn_mul_borelElem_zero p μ₁ μ₂ k k u₁ u₂ (by rw [hu₁, hu₂]) g

theorem phiFn_mul_borelElem_zero (s s' : ℤ) (a₁ a₂ : ℚ_[p]ˣ)
    (hss' : ‖(a₂ : ℚ_[p])‖ * (p : ℝ) ^ s' = ‖(a₁ : ℚ_[p])‖ * (p : ℝ) ^ s)
    (g : GL (Fin 2) ℚ_[p]) :
    phiFn p μ₁ μ₂ s (g * borelElem p a₁ a₂ 0) = lawFactor p μ₁ μ₂ a₂ a₁ * phiFn p μ₁ μ₂ s' g := by
  rw [phiFn_apply, phiFn_apply, mul_assoc,
    show borelElem p a₁ a₂ 0 * weyl p = weyl p * borelElem p a₂ a₁ 0 by
      rw [← weyl_mul_borelElem_zero_mul_weyl p a₁ a₂, ← mul_assoc, ← mul_assoc, weyl_mul_weyl, one_mul],
    ← mul_assoc]
  refine bumpFn_mul_borelElem_zero p μ₁ μ₂ (-s) (-s') a₂ a₁ ?_ (g * weyl p)
  rw [neg_neg, neg_neg, hss']

theorem phiFn_mul_diagP (s : ℤ) (g : GL (Fin 2) ℚ_[p]) :
    phiFn p μ₁ μ₂ s (g * diagP p) = lawFactor p μ₁ μ₂ 1 (pUnit p) * phiFn p μ₁ μ₂ (s - 1) g := by
  refine phiFn_mul_borelElem_zero p μ₁ μ₂ s (s - 1) (pUnit p) 1 ?_ g
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one (one_lt_p_real p))
  rw [norm_pUnit, Units.val_one, norm_one, one_mul, ← _root_.zpow_neg_one, ← zpow_add₀ hp0]
  congr 1
  ring

theorem phiFn_mul_diagPw (s : ℤ) (g : GL (Fin 2) ℚ_[p]) :
    phiFn p μ₁ μ₂ s (g * diagPw p) = lawFactor p μ₁ μ₂ (pUnit p) 1 * phiFn p μ₁ μ₂ (s + 1) g := by
  refine phiFn_mul_borelElem_zero p μ₁ μ₂ s (s + 1) 1 (pUnit p) ?_ g
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one (one_lt_p_real p))
  rw [norm_pUnit, Units.val_one, norm_one, one_mul, ← _root_.zpow_neg_one, ← zpow_add₀ hp0]
  congr 1
  ring

end Dilation
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section Translation

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

theorem bumpFn_borelElem_mul_lowerUnip_mul_lowerUnip (k : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x y z : ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (borelElem p a₁ a₂ x * lowerUnip p y * lowerUnip p z)
      = if ‖y + z‖ ≤ (p : ℝ) ^ (-k) then lawFactor p μ₁ μ₂ a₁ a₂ else 0 := by
  rw [mul_assoc, ← lowerUnip_add, bumpFn_borelElem_mul_lowerUnip]

theorem bumpFn_borelElem_mul_weyl_mul_lowerUnip (k : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x z : ℚ_[p]) :
    bumpFn p μ₁ μ₂ k (borelElem p a₁ a₂ x * weyl p * lowerUnip p z) = 0 := by
  rw [mul_assoc, show weyl p * lowerUnip p z = borelElem p 1 1 z * weyl p by
      rw [← weyl_mul_borelElem_one_one_mul_weyl, ← mul_assoc, ← mul_assoc, weyl_mul_weyl, one_mul],
    ← mul_assoc, borelElem_mul, bumpFn_borelElem_mul_weyl]

theorem phiFn_borelElem_mul_weyl_mul_borelElem_one_one_mul (s : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x₀ x' x : ℚ_[p]) :
    phiFn p μ₁ μ₂ s (borelElem p a₁ a₂ x₀ * weyl p * borelElem p 1 1 x' * borelElem p 1 1 x)
      = if ‖x' + x‖ ≤ (p : ℝ) ^ s then lawFactor p μ₁ μ₂ a₁ a₂ else 0 := by
  rw [mul_assoc, borelElem_mul, one_mul, Units.val_one, one_mul, mul_one,
    phiFn_borelElem_mul_weyl_mul_borelElem_one_one, add_comm]

theorem bumpFn_translate_disjoint (k : ℤ) {z : ℚ_[p]} (hz : (p : ℝ) ^ (-k) < ‖z‖) :
    bumpFn p μ₁ μ₂ k (1 * lowerUnip p (-z)) = 0 ∧ bumpFn p μ₁ μ₂ k 1 = 1 ∧
    bumpFn p μ₁ μ₂ k (lowerUnip p z * lowerUnip p (-z)) = 1 ∧ bumpFn p μ₁ μ₂ k (lowerUnip p z) = 0 := by
  refine ⟨?_, bumpFn_one p μ₁ μ₂ k, ?_, ?_⟩
  · rw [one_mul, bumpFn_lowerUnip, if_neg]
    rw [norm_neg]
    exact not_le.mpr hz
  · rw [← lowerUnip_add, add_neg_cancel, lowerUnip_zero, bumpFn_one]
  · rw [bumpFn_lowerUnip, if_neg (not_le.mpr hz)]

end Translation
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section Levels

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

open FLT.SmoothVectors in

theorem weyl_mem_gl2CongruenceSubgroup_zero : weyl p ∈ gl2CongruenceSubgroup p 0 := by
  rw [mem_gl2CongruenceSubgroup_iff, weyl_inv]
  have h : ∀ i j, ‖((weyl p : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ (p : ℝ) ^ (-((0 : ℕ) : ℤ)) := by
    intro i j
    rw [show ((0 : ℕ) : ℤ) = 0 from rfl, neg_zero, zpow_zero, norm_sub_one_entry_le_one_iff, coe_weyl]
    fin_cases i <;> fin_cases j <;> simp
  exact ⟨h, h⟩

open FLT.SmoothVectors in

theorem phiFn_mul_of_mem_gl2CongruenceSubgroup (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    {s : ℤ} {m : ℕ} (hm1 : 1 ≤ m) (hms : -s ≤ (m : ℤ)) (hms' : 1 + s ≤ (m : ℤ))
    (g : GL (Fin 2) ℚ_[p]) {κ : GL (Fin 2) ℚ_[p]} (hκ : κ ∈ gl2CongruenceSubgroup p m) :
    phiFn p μ₁ μ₂ s (g * κ) = phiFn p μ₁ μ₂ s g := by
  have hconj : weyl p * κ * (weyl p)⁻¹ ∈ gl2CongruenceSubgroup p m :=
    conj_mem_gl2CongruenceSubgroup p (weyl_mem_gl2CongruenceSubgroup_zero p) hκ
  rw [weyl_inv] at hconj
  rw [phiFn_apply, phiFn_apply,
    show g * κ * weyl p = g * weyl p * (weyl p * κ * weyl p) by
      simp only [← mul_assoc]
      rw [mul_assoc g (weyl p) (weyl p), weyl_mul_weyl, mul_one]]
  exact bumpFn_mul_of_mem_gl2CongruenceSubgroup p μ₁ μ₂ h₁ h₂ hm1 (by omega) (by omega) _ hconj

open FLT.SmoothVectors in
theorem phiFn_mem_rightInvariantFunctions (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    {s : ℤ} {m : ℕ} (hm1 : 1 ≤ m) (hms : -s ≤ (m : ℤ)) (hms' : 1 + s ≤ (m : ℤ)) :
    phiFn p μ₁ μ₂ s ∈ rightInvariantFunctions p (gl2CongruenceSubgroup p m) :=
  (mem_rightInvariantFunctions_iff p).mpr fun _ hκ g =>
    phiFn_mul_of_mem_gl2CongruenceSubgroup p μ₁ μ₂ h₁ h₂ hm1 hms hms' g hκ

end Levels
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section Audit
#print axioms FLT.PrincipalSeriesGL2Padic.lawFactor_neg_inv_self
#print axioms FLT.PrincipalSeriesGL2Padic.apply_lowerUnip_eq_tail
#print axioms FLT.PrincipalSeriesGL2Padic.apply_borelElem_mul_lowerUnip_eq_tail
#print axioms FLT.PrincipalSeriesGL2Padic.tailChar_eq_of_norm_eq
#print axioms FLT.PrincipalSeriesGL2Padic.weyl_mul_borelElem_one_one_eq
#print axioms FLT.PrincipalSeriesGL2Padic.lowerUnip_mul_weyl
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_borelElem_mul_weyl_mul_borelElem_one_one
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_borelElem_mul_weyl_mul_borelElem_one_one
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_borelElem_mul_lowerUnip
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_borelElem
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_weyl
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_borelElem_mul
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_mem_principalSeries
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_ne_bumpFn
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_mul_borelElem_zero
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_mul_diagP
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_mul_diagPw
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_mul_borelElem_zero_of_norm_eq_one
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_mul_borelElem_zero
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_mul_diagP
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_mul_diagPw
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_borelElem_mul_lowerUnip_mul_lowerUnip
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_borelElem_mul_weyl_mul_lowerUnip
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_borelElem_mul_weyl_mul_borelElem_one_one_mul
#print axioms FLT.PrincipalSeriesGL2Padic.bumpFn_translate_disjoint
#print axioms FLT.PrincipalSeriesGL2Padic.weyl_mem_gl2CongruenceSubgroup_zero
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_mul_of_mem_gl2CongruenceSubgroup
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_mem_rightInvariantFunctions
end Audit
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end DeskModule03
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section DeskModule04

set_option autoImplicit false

noncomputable section

open FLT.PrincipalSeriesGL2Padic LocalNewvector

namespace P6B
open LocalNewvector

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

theorem norm_add_eq_of_norm_lt {y z : ℚ_[p]} (hz : ‖z‖ < ‖y‖) : ‖y + z‖ = ‖y‖ := by
  rw [Padic.add_eq_max_of_ne (ne_of_lt hz).symm]
  exact max_eq_left hz.le

theorem tail_summand {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂)
    (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) {m : ℕ}
    (hm : ∀ (x : GL (Fin 2) ℚ_[p]) (z : ℚ_[p]), ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ)) →
      f (x * borelElem p 1 1 z) = f x)
    {y₀ z : ℚ_[p]} (hy₀ : y₀ ≠ 0) (hy₀m : (p : ℝ) ^ (m : ℤ) ≤ ‖y₀‖) (hz : ‖z‖ < ‖y₀‖) :
    f (lowerUnip p (y₀ + z))
      = (μ₁ (-1) : ℂ) * tailChar p μ₁ μ₂ (Units.mk0 y₀ hy₀) * f (weyl p) := by
  have h0 : y₀ + z ≠ 0 := add_ne_zero_of_norm_lt p hz
  have hnorm : ‖y₀ + z‖ = ‖y₀‖ := norm_add_eq_of_norm_lt p hz
  rw [apply_lowerUnip_eq_tail p μ₁ μ₂ hf (y₀ + z) h0]
  have htail : tailChar p μ₁ μ₂ (Units.mk0 (y₀ + z) h0)
      = tailChar p μ₁ μ₂ (Units.mk0 y₀ hy₀) :=
    tailChar_eq_of_norm_eq p μ₁ μ₂ h₁ h₂ (by simpa using hnorm)
  have hcollapse : f (weyl p * borelElem p 1 1 (y₀ + z)⁻¹) = f (weyl p) := by
    refine hm (weyl p) _ ?_
    rw [norm_inv, hnorm, zpow_neg, ← one_div, ← one_div]
    exact one_div_le_one_div_of_le
      (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _) hy₀m
  rw [htail, hcollapse]

theorem weyl_summand {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂)
    (z : ℚ_[p]) : f (weyl p * lowerUnip p z) = f (weyl p) := by
  have hkey : weyl p * lowerUnip p z = borelElem p 1 1 z * weyl p := by
    have h1 : weyl p * borelElem p 1 1 z * weyl p = lowerUnip p z :=
      weyl_mul_borelElem_one_one_mul_weyl p z
    calc weyl p * lowerUnip p z
        = weyl p * (weyl p * borelElem p 1 1 z * weyl p) := by rw [h1]
      _ = (weyl p * weyl p) * borelElem p 1 1 z * weyl p := by group
      _ = borelElem p 1 1 z * weyl p := by rw [weyl_mul_weyl, one_mul]
  rw [hkey, apply_borelElem_mul p μ₁ μ₂ hf 1 1 z (weyl p), lawFactor_one, one_mul]

end P6B
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

#print axioms P6B.norm_add_eq_of_norm_lt
#print axioms P6B.tail_summand
#print axioms P6B.weyl_summand

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end DeskModule04
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section DeskModule05

set_option autoImplicit false

noncomputable section

open Matrix

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"
open LocalNewvector

open FLT.EKAverage FLT.SmoothVectors FLT.AdmissibleRep

variable (p : ℕ) [Fact p.Prime]

section LowerUnipSubgroup

def lowerUnipSubgroup (j : ℤ) : Subgroup (GL (Fin 2) ℚ_[p]) where
  carrier := {g | ∃ y : ℚ_[p], ‖y‖ ≤ (p : ℝ)^(-j) ∧ lowerUnip p y = g}
  one_mem' := ⟨0, by simp only [norm_zero]; positivity, lowerUnip_zero p⟩
  mul_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    exact ⟨y + z, (IsUltrametricDist.norm_add_le_max y z).trans (max_le hy hz),
      lowerUnip_add p y z⟩
  inv_mem' := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨-y, by rwa [norm_neg], (lowerUnip_inv p y).symm⟩

theorem mem_lowerUnipSubgroup_iff {j : ℤ} {g : GL (Fin 2) ℚ_[p]} :
    g ∈ lowerUnipSubgroup p j ↔ ∃ y : ℚ_[p], ‖y‖ ≤ (p : ℝ)^(-j) ∧ lowerUnip p y = g :=
  Iff.rfl

theorem lowerUnip_mem_lowerUnipSubgroup {j : ℤ} {y : ℚ_[p]} (hy : ‖y‖ ≤ (p : ℝ)^(-j)) :
    lowerUnip p y ∈ lowerUnipSubgroup p j :=
  ⟨y, hy, rfl⟩

theorem continuous_lowerUnip : Continuous (lowerUnip p) := by
  have hval : Continuous fun y : ℚ_[p] => (!![1, 0; y, 1] : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply] <;>
      first | exact continuous_const | exact continuous_id
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact hval
  · simp only [lowerUnip_inv, coe_lowerUnip]
    exact hval.comp continuous_neg

theorem isCompact_lowerUnipSubgroup (j : ℤ) :
    IsCompact (lowerUnipSubgroup p j : Set (GL (Fin 2) ℚ_[p])) := by
  have hball : IsCompact (Metric.closedBall (0 : ℚ_[p]) ((p : ℝ)^(-j))) :=
    isCompact_closedBall 0 _
  have himg : (lowerUnipSubgroup p j : Set (GL (Fin 2) ℚ_[p]))
      = lowerUnip p '' Metric.closedBall (0 : ℚ_[p]) ((p : ℝ)^(-j)) := by
    ext g
    simp only [Set.mem_image, Metric.mem_closedBall, dist_zero_right, SetLike.mem_coe,
      mem_lowerUnipSubgroup_iff]
  rw [himg]
  exact hball.image (continuous_lowerUnip p)

theorem lowerUnipSubgroup_antitone {j j' : ℤ} (hjj' : j ≤ j') :
    lowerUnipSubgroup p j' ≤ lowerUnipSubgroup p j := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, hy.trans ?_, rfl⟩
  have hp : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Fact.out (p := p.Prime)).one_le
  exact zpow_le_zpow_right₀ hp (neg_le_neg hjj')

theorem finite_quotient_stabilizer_lowerUnipSubgroup {M : Type*} [AddCommGroup M] [Module ℂ M]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) M] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ M]
    (j : ℤ) {f : M} (hf : IsSmoothVector (GL (Fin 2) ℚ_[p]) f) :
    Finite (↥(lowerUnipSubgroup p j) ⧸ MulAction.stabilizer (lowerUnipSubgroup p j) f) :=
  finite_quotient_stabilizer_of_isCompact_of_isSmoothVector (isCompact_lowerUnipSubgroup p j) hf

theorem forall_finite_quotient_stabilizer_lowerUnipSubgroup {M : Type*} [AddCommGroup M]
    [Module ℂ M] [DistribMulAction (GL (Fin 2) ℚ_[p]) M] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ M]
    [ContinuousSMulDiscrete (GL (Fin 2) ℚ_[p]) M] (j : ℤ) (f : M) :
    Finite (↥(lowerUnipSubgroup p j) ⧸ MulAction.stabilizer (lowerUnipSubgroup p j) f) :=
  forall_finite_quotient_stabilizer_of_isCompact (isCompact_lowerUnipSubgroup p j) f

theorem ekAverage_mem_of_invariant {M : Type*} [AddCommGroup M] [Module ℂ M]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) M] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ M]
    (K : Subgroup (GL (Fin 2) ℚ_[p])) (W : Submodule ℂ M)
    (hW : ∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W)
    {f : M} (hf : f ∈ W) (hfin : Finite (↥K ⧸ MulAction.stabilizer K f)) :
    ekAverage ℂ K f ∈ W := by
  haveI := hfin
  haveI := Fintype.ofFinite (↥K ⧸ MulAction.stabilizer K f)
  rw [ekAverage_eq_finsetSum]
  refine W.smul_mem _ (Submodule.sum_mem W fun x _ => ?_)
  obtain ⟨k, rfl⟩ := Quotient.exists_rep x
  exact hW k.val f hf

end LowerUnipSubgroup
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section AuditN0
#print axioms FLT.PrincipalSeriesGL2Padic.lowerUnipSubgroup
#print axioms FLT.PrincipalSeriesGL2Padic.continuous_lowerUnip
#print axioms FLT.PrincipalSeriesGL2Padic.isCompact_lowerUnipSubgroup
#print axioms FLT.PrincipalSeriesGL2Padic.lowerUnipSubgroup_antitone
#print axioms FLT.PrincipalSeriesGL2Padic.finite_quotient_stabilizer_lowerUnipSubgroup
#print axioms FLT.PrincipalSeriesGL2Padic.forall_finite_quotient_stabilizer_lowerUnipSubgroup
#print axioms FLT.PrincipalSeriesGL2Padic.ekAverage_mem_of_invariant
end AuditN0
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end DeskModule05
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section DeskModule06

set_option autoImplicit false

noncomputable section

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"
open LocalNewvector

section Bridge

variable (p : ℕ) [Fact p.Prime]

theorem lowerUnip_eq_lowerUnipotentR (y : ℚ_[p]) :
    lowerUnip p y = LocalGL2.lowerUnipotentR (R := ℚ_[p]) y := rfl

theorem lowerUnipotentInt_eq_lowerUnip (r : ℤ_[p]) :
    LocalGL2.lowerUnipotentInt ℚ_[p] r = lowerUnip p (r : ℚ_[p]) := by
  apply Units.ext
  rw [LocalGL2.coe_lowerUnipotentInt, coe_lowerUnip, PadicInt.algebraMap_apply]

end Bridge
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

namespace PSCarrier
open LocalNewvector.PSCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

section Vectors

variable (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)

def bumpV (k : ℤ) : PSCarrier p μ₁ μ₂ :=
  mk p μ₁ μ₂ ⟨bumpFn p μ₁ μ₂ k, bumpFn_mem_principalSeries p μ₁ μ₂ h₁ h₂ k⟩

def phiV (s : ℤ) : PSCarrier p μ₁ μ₂ :=
  mk p μ₁ μ₂ ⟨phiFn p μ₁ μ₂ s, phiFn_mem_principalSeries p μ₁ μ₂ h₁ h₂ s⟩

@[scoped simp] theorem toFn_bumpV (k : ℤ) : toFn p μ₁ μ₂ (bumpV p μ₁ μ₂ h₁ h₂ k) = bumpFn p μ₁ μ₂ k := rfl

@[scoped simp] theorem toFn_phiV (s : ℤ) : toFn p μ₁ μ₂ (phiV p μ₁ μ₂ h₁ h₂ s) = phiFn p μ₁ μ₂ s := rfl

theorem toFn_bumpV_one (k : ℤ) : toFn p μ₁ μ₂ (bumpV p μ₁ μ₂ h₁ h₂ k) 1 = 1 := by
  rw [toFn_bumpV, bumpFn_one]

theorem toFn_bumpV_weyl (k : ℤ) : toFn p μ₁ μ₂ (bumpV p μ₁ μ₂ h₁ h₂ k) (weyl p) = 0 := by
  rw [toFn_bumpV, bumpFn_weyl]

theorem toFn_phiV_one (s : ℤ) : toFn p μ₁ μ₂ (phiV p μ₁ μ₂ h₁ h₂ s) 1 = 0 := by
  rw [toFn_phiV, phiFn_one]

theorem toFn_phiV_weyl (s : ℤ) : toFn p μ₁ μ₂ (phiV p μ₁ μ₂ h₁ h₂ s) (weyl p) = 1 := by
  rw [toFn_phiV, phiFn_weyl]

theorem bumpV_ne_zero (k : ℤ) : bumpV p μ₁ μ₂ h₁ h₂ k ≠ 0 := by
  intro h
  have h1 := congrArg (fun v => toFn p μ₁ μ₂ v 1) h
  simp only [toFn_bumpV_one] at h1
  exact one_ne_zero h1

theorem phiV_ne_zero (s : ℤ) : phiV p μ₁ μ₂ h₁ h₂ s ≠ 0 := by
  intro h
  have h1 := congrArg (fun v => toFn p μ₁ μ₂ v (weyl p)) h
  simp only [toFn_phiV_weyl] at h1
  exact one_ne_zero h1

include h₁ h₂ in

theorem exists_ne_zero : ∃ v : PSCarrier p μ₁ μ₂, v ≠ 0 :=
  ⟨bumpV p μ₁ μ₂ h₁ h₂ 0, bumpV_ne_zero p μ₁ μ₂ h₁ h₂ 0⟩

theorem weyl_smul_bumpV (k : ℤ) : weyl p • bumpV p μ₁ μ₂ h₁ h₂ k = phiV p μ₁ μ₂ h₁ h₂ (-k) :=
  ext p μ₁ μ₂ fun y => by rw [toFn_smul, toFn_bumpV, toFn_phiV, phiFn_apply, neg_neg]

theorem weyl_smul_phiV (s : ℤ) : weyl p • phiV p μ₁ μ₂ h₁ h₂ s = bumpV p μ₁ μ₂ h₁ h₂ (-s) :=
  ext p μ₁ μ₂ fun y => by
    rw [toFn_smul, toFn_bumpV, toFn_phiV, phiFn_apply, mul_assoc, weyl_mul_weyl, mul_one]

theorem diagP_smul_bumpV (k : ℤ) :
    diagP p • bumpV p μ₁ μ₂ h₁ h₂ k = lawFactor p μ₁ μ₂ (pUnit p) 1 • bumpV p μ₁ μ₂ h₁ h₂ (k - 1) :=
  ext p μ₁ μ₂ fun y => by rw [toFn_smul, toFn_csmul, toFn_bumpV, toFn_bumpV, bumpFn_mul_diagP]

theorem diagP_smul_phiV (s : ℤ) :
    diagP p • phiV p μ₁ μ₂ h₁ h₂ s = lawFactor p μ₁ μ₂ 1 (pUnit p) • phiV p μ₁ μ₂ h₁ h₂ (s - 1) :=
  ext p μ₁ μ₂ fun y => by rw [toFn_smul, toFn_csmul, toFn_phiV, toFn_phiV, phiFn_mul_diagP]

theorem diagPw_smul_bumpV (k : ℤ) :
    diagPw p • bumpV p μ₁ μ₂ h₁ h₂ k = lawFactor p μ₁ μ₂ 1 (pUnit p) • bumpV p μ₁ μ₂ h₁ h₂ (k + 1) :=
  ext p μ₁ μ₂ fun y => by rw [toFn_smul, toFn_csmul, toFn_bumpV, toFn_bumpV, bumpFn_mul_diagPw]

theorem diagPw_smul_phiV (s : ℤ) :
    diagPw p • phiV p μ₁ μ₂ h₁ h₂ s = lawFactor p μ₁ μ₂ (pUnit p) 1 • phiV p μ₁ μ₂ h₁ h₂ (s + 1) :=
  ext p μ₁ μ₂ fun y => by rw [toFn_smul, toFn_csmul, toFn_phiV, toFn_phiV, phiFn_mul_diagPw]

theorem toFn_combo_one (a b : ℂ) (k s : ℤ) :
    toFn p μ₁ μ₂ (a • bumpV p μ₁ μ₂ h₁ h₂ k + b • phiV p μ₁ μ₂ h₁ h₂ s) 1 = a := by
  rw [show toFn p μ₁ μ₂ (a • bumpV p μ₁ μ₂ h₁ h₂ k + b • phiV p μ₁ μ₂ h₁ h₂ s) 1
      = toFn p μ₁ μ₂ (a • bumpV p μ₁ μ₂ h₁ h₂ k) 1 + toFn p μ₁ μ₂ (b • phiV p μ₁ μ₂ h₁ h₂ s) 1 from rfl,
    toFn_csmul, toFn_csmul, toFn_bumpV_one, toFn_phiV_one, mul_one, mul_zero, add_zero]

theorem toFn_combo_weyl (a b : ℂ) (k s : ℤ) :
    toFn p μ₁ μ₂ (a • bumpV p μ₁ μ₂ h₁ h₂ k + b • phiV p μ₁ μ₂ h₁ h₂ s) (weyl p) = b := by
  rw [show toFn p μ₁ μ₂ (a • bumpV p μ₁ μ₂ h₁ h₂ k + b • phiV p μ₁ μ₂ h₁ h₂ s) (weyl p)
      = toFn p μ₁ μ₂ (a • bumpV p μ₁ μ₂ h₁ h₂ k) (weyl p)
        + toFn p μ₁ μ₂ (b • phiV p μ₁ μ₂ h₁ h₂ s) (weyl p) from rfl,
    toFn_csmul, toFn_csmul, toFn_bumpV_weyl, toFn_phiV_weyl, mul_one, mul_zero, zero_add]

theorem bumpV_mem_of_smul_mem {W : Submodule ℂ (PSCarrier p μ₁ μ₂)} {c : ℂ} (hc : c ≠ 0) {k : ℤ}
    (h : c • bumpV p μ₁ μ₂ h₁ h₂ k ∈ W) : bumpV p μ₁ μ₂ h₁ h₂ k ∈ W := by
  have := W.smul_mem c⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end Vectors
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section Wlog

theorem exists_toFn_ne_zero {f : PSCarrier p μ₁ μ₂} (hf : f ≠ 0) : ∃ g : GL (Fin 2) ℚ_[p], toFn p μ₁ μ₂ f g ≠ 0 := by
  by_contra h
  exact hf (ext p μ₁ μ₂ fun y => by rw [not_exists.mp h y |> not_not.mp]; rfl)

theorem exists_mem_toFn_weyl_ne_zero {W : Submodule ℂ (PSCarrier p μ₁ μ₂)}
    (hW : ∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W) (hbot : W ≠ ⊥) :
    ∃ f ∈ W, toFn p μ₁ μ₂ f (weyl p) ≠ 0 := by
  obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff W).mp hbot
  obtain ⟨g₀, hg₀⟩ := exists_toFn_ne_zero p μ₁ μ₂ hf0
  refine ⟨(weyl p * g₀) • f, hW _ f hfW, ?_⟩
  rwa [toFn_smul, ← mul_assoc, weyl_mul_weyl, one_mul]

theorem sub_smul_mem {W : Submodule ℂ (PSCarrier p μ₁ μ₂)}
    (hW : ∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W) {u v : PSCarrier p μ₁ μ₂}
    (hu : u ∈ W) (hv : v ∈ W) (c : ℂ) (g : GL (Fin 2) ℚ_[p]) : c • u - g • v ∈ W :=
  W.sub_mem (W.smul_mem c hu) (hW g v hv)

end Wlog
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end PSCarrier
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section Audit
#print axioms FLT.PrincipalSeriesGL2Padic.lowerUnip_eq_lowerUnipotentR
#print axioms FLT.PrincipalSeriesGL2Padic.lowerUnipotentInt_eq_lowerUnip
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.bumpV
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.phiV
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.exists_ne_zero
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.weyl_smul_bumpV
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.weyl_smul_phiV
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.diagP_smul_bumpV
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.diagP_smul_phiV
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.diagPw_smul_bumpV
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.diagPw_smul_phiV
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.toFn_combo_one
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.toFn_combo_weyl
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.bumpV_mem_of_smul_mem
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.exists_mem_toFn_weyl_ne_zero
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.sub_smul_mem
end Audit
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

end DeskModule06
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage"

section DeskModule07

set_option autoImplicit false

noncomputable section

open FLT.PrincipalSeriesGL2Padic FLT.AdmissibleRep FLT.EKAverage LocalNewvector

namespace P6B
open LocalNewvector

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

def avgOp (j : ℤ) (f : PSCarrier p μ₁ μ₂) : PSCarrier p μ₁ μ₂ :=
  ekAverage ℂ (lowerUnipSubgroup p j) f

def evalLin (x : GL (Fin 2) ℚ_[p]) : PSCarrier p μ₁ μ₂ →ₗ[ℂ] ℂ where
  toFun v := PSCarrier.toFn p μ₁ μ₂ v x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem evalLin_apply (x : GL (Fin 2) ℚ_[p]) (v : PSCarrier p μ₁ μ₂) :
    evalLin p μ₁ μ₂ x v = PSCarrier.toFn p μ₁ μ₂ v x := rfl

theorem toFn_avgOp_eq_of_const (j : ℤ) (f : PSCarrier p μ₁ μ₂)
    (hfin : Finite
      (↥(lowerUnipSubgroup p j) ⧸ MulAction.stabilizer (lowerUnipSubgroup p j) f))
    {x : GL (Fin 2) ℚ_[p]} {c : ℂ}
    (hc : ∀ k : ↥(lowerUnipSubgroup p j),
      PSCarrier.toFn p μ₁ μ₂ f (x * (k : GL (Fin 2) ℚ_[p])) = c) :
    PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) x = c := by
  classical
  show PSCarrier.toFn p μ₁ μ₂ (ekAverage ℂ (lowerUnipSubgroup p j) f) x = c
  haveI := hfin
  haveI := Fintype.ofFinite
    (↥(lowerUnipSubgroup p j) ⧸ MulAction.stabilizer (lowerUnipSubgroup p j) f)
  have hN : (Nat.card
      (↥(lowerUnipSubgroup p j) ⧸ MulAction.stabilizer (lowerUnipSubgroup p j) f) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hunfold := ekAverage_eq_finsetSum ℂ (lowerUnipSubgroup p j) f
  have heval := congrArg (evalLin p μ₁ μ₂ x) hunfold
  rw [map_smul, map_sum] at heval
  have hterm : ∀ q : ↥(lowerUnipSubgroup p j) ⧸
      MulAction.stabilizer (lowerUnipSubgroup p j) f,
      evalLin p μ₁ μ₂ x (MulAction.ofQuotientStabilizer (lowerUnipSubgroup p j) f q) = c := by
    intro q
    refine Quotient.inductionOn q (fun k => ?_)
    have hmk : MulAction.ofQuotientStabilizer (lowerUnipSubgroup p j) f
        (QuotientGroup.mk k) = k • f :=
      MulAction.ofQuotientStabilizer_mk (lowerUnipSubgroup p j) f k
    rw [hmk]
    have hsm : (k • f : PSCarrier p μ₁ μ₂) = (k : GL (Fin 2) ℚ_[p]) • f := rfl
    rw [evalLin_apply, hsm]
    exact hc k
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_const, Finset.card_univ] at heval
  rw [evalLin_apply] at heval
  rw [heval, nsmul_eq_mul, smul_eq_mul, ← Nat.card_eq_fintype_card, ← mul_assoc,
    inv_mul_cancel₀ hN, one_mul]

theorem toFn_avgOp_lowerUnip (j : ℤ) (f : PSCarrier p μ₁ μ₂)
    (hfin : Finite
      (↥(lowerUnipSubgroup p j) ⧸ MulAction.stabilizer (lowerUnipSubgroup p j) f))
    {y : ℚ_[p]} (hy : ‖y‖ ≤ (p : ℝ) ^ (-j)) :
    PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) (lowerUnip p y)
      = PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) 1 := by
  haveI := hfin
  have hmem := ekAverage_mem_fixedVectors (F := ℂ) (lowerUnipSubgroup p j) f
  have hfix : lowerUnip p y • avgOp p μ₁ μ₂ j f = avgOp p μ₁ μ₂ j f :=
    hmem (lowerUnip p y) (lowerUnip_mem_lowerUnipSubgroup p hy)
  calc PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) (lowerUnip p y)
      = PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) (1 * lowerUnip p y) := by rw [one_mul]
    _ = PSCarrier.toFn p μ₁ μ₂ (lowerUnip p y • avgOp p μ₁ μ₂ j f) 1 := rfl
    _ = PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) 1 := by rw [hfix]

theorem zpow_succ_le_norm_of_lt {y : ℚ_[p]} (hy : y ≠ 0) {k : ℤ}
    (h : (p : ℝ) ^ k < ‖y‖) : (p : ℝ) ^ (k + 1) ≤ ‖y‖ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [Padic.norm_eq_zpow_neg_valuation hy] at h ⊢
  have hklt : k < -y.valuation := (zpow_lt_zpow_iff_right₀ hp1).mp h
  exact zpow_le_zpow_right₀ hp1.le (by omega)

theorem phiFn_lowerUnip (s : ℤ) {y : ℚ_[p]} (hy : y ≠ 0) :
    phiFn p μ₁ μ₂ s (lowerUnip p y)
      = if (p : ℝ) ^ (-s) ≤ ‖y‖
        then (μ₁ (-1) : ℂ) * tailChar p μ₁ μ₂ (Units.mk0 y hy) else 0 := by
  have h := phiFn_borelElem_mul_lowerUnip p μ₁ μ₂ s 1 1 0 y hy
  rwa [borelElem_one, one_mul, lawFactor_one, one_mul] at h

theorem avgOp_eq_smul_psiM_add_smul_phiM (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    (f : PSCarrier p μ₁ μ₂) {m : ℕ}
    (hm : ∀ (x : GL (Fin 2) ℚ_[p]) (z : ℚ_[p]), ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ)) →
      PSCarrier.toFn p μ₁ μ₂ f (x * borelElem p 1 1 z) = PSCarrier.toFn p μ₁ μ₂ f x)
    {j : ℤ} (hj : j ≤ -(m : ℤ)) :
    avgOp p μ₁ μ₂ j f
      = PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) 1 • PSCarrier.bumpV p μ₁ μ₂ h₁ h₂ j
        + PSCarrier.toFn p μ₁ μ₂ f (weyl p) • PSCarrier.phiV p μ₁ μ₂ h₁ h₂ (j - 1) := by
  have hfin : Finite
      (↥(lowerUnipSubgroup p j) ⧸ MulAction.stabilizer (lowerUnipSubgroup p j) f) :=
    forall_finite_quotient_stabilizer_lowerUnipSubgroup p j f
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  set I : ℂ := PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) 1 with hI
  set fW : ℂ := PSCarrier.toFn p μ₁ μ₂ f (weyl p) with hfW

  refine PSCarrier.ext p μ₁ μ₂ fun g => ?_

  have hRHS : ∀ x : GL (Fin 2) ℚ_[p],
      PSCarrier.toFn p μ₁ μ₂
        (I • PSCarrier.bumpV p μ₁ μ₂ h₁ h₂ j + fW • PSCarrier.phiV p μ₁ μ₂ h₁ h₂ (j - 1)) x
      = I * bumpFn p μ₁ μ₂ j x + fW * phiFn p μ₁ μ₂ (j - 1) x := fun x => rfl
  rw [hRHS]

  have hcoreLower : ∀ y₀ : ℚ_[p],
      PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) (lowerUnip p y₀)
        = I * bumpFn p μ₁ μ₂ j (lowerUnip p y₀) + fW * phiFn p μ₁ μ₂ (j - 1) (lowerUnip p y₀) := by
    intro y₀
    by_cases hball : ‖y₀‖ ≤ (p : ℝ) ^ (-j)
    ·
      rw [toFn_avgOp_lowerUnip p μ₁ μ₂ j f hfin hball, ← hI,
        bumpFn_lowerUnip p μ₁ μ₂ j y₀, if_pos hball]
      by_cases hy0 : y₀ = 0
      · subst hy0
        rw [lowerUnip_zero, phiFn_one, mul_zero, add_zero, mul_one]
      · rw [phiFn_lowerUnip p μ₁ μ₂ (j - 1) hy0, if_neg, mul_zero, add_zero, mul_one]
        exact not_le.mpr (lt_of_le_of_lt hball (zpow_lt_zpow_right₀ hp1 (by omega)))
    ·
      rw [not_le] at hball
      have hy0 : y₀ ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hball
        exact absurd hball (not_lt.mpr (le_of_lt (zpow_pos (by positivity) _)))
      have hy₀m : (p : ℝ) ^ (m : ℤ) ≤ ‖y₀‖ := by
        refine le_trans (zpow_le_zpow_right₀ hp1.le ?_) hball.le
        omega
      have hconst : PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) (lowerUnip p y₀)
          = (μ₁ (-1) : ℂ) * tailChar p μ₁ μ₂ (Units.mk0 y₀ hy0) * fW := by
        refine toFn_avgOp_eq_of_const p μ₁ μ₂ j f hfin (fun k => ?_)
        obtain ⟨yk, hyk, hgk⟩ := k.property
        have hx : lowerUnip p y₀ * (k : GL (Fin 2) ℚ_[p]) = lowerUnip p (y₀ + yk) := by
          rw [← hgk, ← lowerUnip_add]
        rw [hx]
        exact tail_summand p μ₁ μ₂ (PSCarrier.toFn_mem p μ₁ μ₂ f) h₁ h₂ hm hy0 hy₀m
          (lt_of_le_of_lt hyk hball)
      rw [hconst, bumpFn_lowerUnip p μ₁ μ₂ j y₀, if_neg (not_le.mpr hball), mul_zero,
        zero_add, phiFn_lowerUnip p μ₁ μ₂ (j - 1) hy0, if_pos]
      · ring
      · have := zpow_succ_le_norm_of_lt p hy0 hball
        calc (p : ℝ) ^ (-(j - 1)) = (p : ℝ) ^ (-j + 1) := by ring_nf
          _ ≤ ‖y₀‖ := by simpa using this
  have hcoreWeyl :
      PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) (weyl p)
        = I * bumpFn p μ₁ μ₂ j (weyl p) + fW * phiFn p μ₁ μ₂ (j - 1) (weyl p) := by
    have hconst : PSCarrier.toFn p μ₁ μ₂ (avgOp p μ₁ μ₂ j f) (weyl p) = fW := by
      refine toFn_avgOp_eq_of_const p μ₁ μ₂ j f hfin (fun k => ?_)
      obtain ⟨yk, hyk, hgk⟩ := k.property
      rw [← hgk]
      exact weyl_summand p μ₁ μ₂ (PSCarrier.toFn_mem p μ₁ μ₂ f) yk
    rw [hconst, bumpFn_weyl, phiFn_weyl, mul_zero, zero_add, mul_one]

  have hAmem := PSCarrier.toFn_mem p μ₁ μ₂ (avgOp p μ₁ μ₂ j f)
  rcases cell_cases p g with ⟨a₁, a₂, x, y₀, rfl⟩ | ⟨a₁, a₂, x, rfl⟩
  · rw [apply_borelElem_mul p μ₁ μ₂ hAmem a₁ a₂ x (lowerUnip p y₀),
      bumpFn_borelElem_mul p μ₁ μ₂ j a₁ a₂ x (lowerUnip p y₀),
      phiFn_borelElem_mul p μ₁ μ₂ (j - 1) a₁ a₂ x (lowerUnip p y₀),
      hcoreLower y₀]
    ring
  · rw [apply_borelElem_mul p μ₁ μ₂ hAmem a₁ a₂ x (weyl p),
      bumpFn_borelElem_mul p μ₁ μ₂ j a₁ a₂ x (weyl p),
      phiFn_borelElem_mul p μ₁ μ₂ (j - 1) a₁ a₂ x (weyl p),
      hcoreWeyl]
    ring

end P6B
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

#print axioms P6B.avgOp
#print axioms P6B.toFn_avgOp_eq_of_const
#print axioms P6B.toFn_avgOp_lowerUnip
#print axioms P6B.zpow_succ_le_norm_of_lt
#print axioms P6B.phiFn_lowerUnip
#print axioms P6B.avgOp_eq_smul_psiM_add_smul_phiM

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end DeskModule07
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section DeskModule08

set_option autoImplicit false

noncomputable section

open FLT.PrincipalSeriesGL2Padic FLT.SmoothVectors LocalNewvector

namespace P6B
open LocalNewvector

variable (p : ℕ) [Fact p.Prime]

theorem exists_right_lower_unipotent_level (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) (f : PSCarrier p μ₁ μ₂) :
    ∃ m : ℕ, ∀ (x : GL (Fin 2) ℚ_[p]) (z : ℚ_[p]), ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ)) →
      PSCarrier.toFn p μ₁ μ₂ f (x * lowerUnip p z) = PSCarrier.toFn p μ₁ μ₂ f x := by
  have hsm : IsSmoothVector (GL (Fin 2) ℚ_[p]) f := PSCarrier.isSmoothVector_carrier p μ₁ μ₂ f
  rw [isSmoothVector_iff_isOpen_stabilizer] at hsm
  obtain ⟨m, hm⟩ := FLT.SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one p
    (hsm.mem_nhds (MulAction.stabilizer (GL (Fin 2) ℚ_[p]) f).one_mem)
  refine ⟨m, fun x z hz => ?_⟩
  have hz' : ‖z‖ ≤ ((p : ℝ) ^ m)⁻¹ := by rwa [zpow_neg, zpow_natCast] at hz
  have hval : (lowerUnip p z : Matrix (Fin 2) (Fin 2) ℚ_[p]) = !![1, 0; z, 1] :=
    coe_lowerUnip p z
  have hinv : (((lowerUnip p z)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![1, 0; -z, 1] := by
    rw [lowerUnip_inv]
    exact coe_lowerUnip p (-z)
  have hmem : lowerUnip p z ∈ FLT.SmoothVectors.gl2CongruenceSubgroup p m := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [hval]
      (fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply]); exact hz'
    · rw [hinv]
      (fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply, norm_neg]); exact hz'
  have hstab' := hm hmem
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hstab'
  calc PSCarrier.toFn p μ₁ μ₂ f (x * lowerUnip p z)
      = PSCarrier.toFn p μ₁ μ₂ (lowerUnip p z • f) x := rfl
    _ = PSCarrier.toFn p μ₁ μ₂ f x := by rw [hstab']

end P6B
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

#print axioms P6B.exists_right_lower_unipotent_level

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end DeskModule08
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section DeskModule09

set_option autoImplicit false

noncomputable section

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"
open LocalNewvector

namespace PSCarrier
open LocalNewvector.PSCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

def IsStable (W : Submodule ℂ (PSCarrier p μ₁ μ₂)) : Prop :=
  ∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W

def gammaRatio : ℂ := (μ₁ (pUnit p) : ℂ) * ((μ₂ (pUnit p) : ℂ))⁻¹

theorem gammaRatio_ne_zero : gammaRatio p μ₁ μ₂ ≠ 0 :=
  mul_ne_zero (μ₁ (pUnit p)).ne_zero (inv_ne_zero (μ₂ (pUnit p)).ne_zero)

section Driver

variable (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)

theorem isIrreducibleGLRep_of_generation_of_extraction
    (hgen : ∀ W : Submodule ℂ (PSCarrier p μ₁ μ₂), IsStable p μ₁ μ₂ W →
      ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∈ W → W = ⊤)
    (hext : ∀ W : Submodule ℂ (PSCarrier p μ₁ μ₂), IsStable p μ₁ μ₂ W →
      (∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∉ W) →
      ∀ f ∈ W, toFn p μ₁ μ₂ f (weyl p) ≠ 0 → False) :
    LocalNewvector.IsIrreducibleGLRep p (PSCarrier p μ₁ μ₂) := by
  refine ⟨exists_ne_zero p μ₁ μ₂ h₁ h₂, fun W hW => ?_⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    by_cases hex : ∃ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∈ W
    · obtain ⟨k, hk⟩ := hex
      exact hgen W hW k hk
    · obtain ⟨f, hfW, hfw⟩ := exists_mem_toFn_weyl_ne_zero p μ₁ μ₂ hW hbot
      exact (hext W hW (fun k hk => hex ⟨k, hk⟩) f hfW hfw).elim

theorem bumpV_mem_of_phiV_mem {W : Submodule ℂ (PSCarrier p μ₁ μ₂)} (hW : IsStable p μ₁ μ₂ W)
    {s : ℤ} (hs : phiV p μ₁ μ₂ h₁ h₂ s ∈ W) : bumpV p μ₁ μ₂ h₁ h₂ (-s) ∈ W := by
  rw [← weyl_smul_phiV]
  exact hW _ _ hs

theorem phiV_mem_of_bumpV_mem {W : Submodule ℂ (PSCarrier p μ₁ μ₂)} (hW : IsStable p μ₁ μ₂ W)
    {k : ℤ} (hk : bumpV p μ₁ μ₂ h₁ h₂ k ∈ W) : phiV p μ₁ μ₂ h₁ h₂ (-k) ∈ W := by
  rw [← weyl_smul_bumpV]
  exact hW _ _ hk

theorem extraction_step {W : Submodule ℂ (PSCarrier p μ₁ μ₂)} (hW : IsStable p μ₁ μ₂ W)
    {j : ℤ} {a b c : ℂ} {u v : PSCarrier p μ₁ μ₂} (hu : u ∈ W) (hv : v ∈ W)
    (hu_eq : u = a • bumpV p μ₁ μ₂ h₁ h₂ (j - 1) + c • phiV p μ₁ μ₂ h₁ h₂ (j - 1 - 1))
    (hv_eq : v = b • bumpV p μ₁ μ₂ h₁ h₂ j + c • phiV p μ₁ μ₂ h₁ h₂ (j - 1)) :
    (lawFactor p μ₁ μ₂ 1 (pUnit p) * a - lawFactor p μ₁ μ₂ (pUnit p) 1 * b)
        • bumpV p μ₁ μ₂ h₁ h₂ (j - 1) ∈ W := by
  have hmem : lawFactor p μ₁ μ₂ 1 (pUnit p) • u - diagP p • v ∈ W := sub_smul_mem p μ₁ μ₂ hW hu hv _ _
  have hcalc : lawFactor p μ₁ μ₂ 1 (pUnit p) • u - diagP p • v
      = (lawFactor p μ₁ μ₂ 1 (pUnit p) * a - lawFactor p μ₁ μ₂ (pUnit p) 1 * b)
          • bumpV p μ₁ μ₂ h₁ h₂ (j - 1) := by
    rw [hu_eq, hv_eq, smul_add, smul_add, smul_comm (diagP p) b, smul_comm (diagP p) c,
      diagP_smul_bumpV, diagP_smul_phiV]
    module
  rwa [hcalc] at hmem

theorem extraction_coeff_eq_zero {W : Submodule ℂ (PSCarrier p μ₁ μ₂)} (hW : IsStable p μ₁ μ₂ W)
    (hno : ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∉ W)
    {j : ℤ} {a b c : ℂ} {u v : PSCarrier p μ₁ μ₂} (hu : u ∈ W) (hv : v ∈ W)
    (hu_eq : u = a • bumpV p μ₁ μ₂ h₁ h₂ (j - 1) + c • phiV p μ₁ μ₂ h₁ h₂ (j - 1 - 1))
    (hv_eq : v = b • bumpV p μ₁ μ₂ h₁ h₂ j + c • phiV p μ₁ μ₂ h₁ h₂ (j - 1)) :
    lawFactor p μ₁ μ₂ 1 (pUnit p) * a = lawFactor p μ₁ μ₂ (pUnit p) 1 * b := by
  by_contra hne
  exact hno (j - 1) (bumpV_mem_of_smul_mem p μ₁ μ₂ h₁ h₂ (sub_ne_zero.mpr hne)
    (extraction_step p μ₁ μ₂ h₁ h₂ hW hu hv hu_eq hv_eq))

theorem weyl_testVector_mem {W : Submodule ℂ (PSCarrier p μ₁ μ₂)} (hW : IsStable p μ₁ μ₂ W)
    {j : ℤ} {b c : ℂ} (hc : c ≠ 0) {v : PSCarrier p μ₁ μ₂} (hv : v ∈ W)
    (hv_eq : v = b • bumpV p μ₁ μ₂ h₁ h₂ j + c • phiV p μ₁ μ₂ h₁ h₂ (j - 1)) :
    (b * c⁻¹) • phiV p μ₁ μ₂ h₁ h₂ (-j) + bumpV p μ₁ μ₂ h₁ h₂ (1 - j) ∈ W := by
  have hΞ : (b * c⁻¹) • bumpV p μ₁ μ₂ h₁ h₂ j + phiV p μ₁ μ₂ h₁ h₂ (j - 1) ∈ W := by
    have := W.smul_mem c⁻¹ hv
    rw [hv_eq, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, mul_comm] at this
    exact this
  have hw := hW (weyl p) _ hΞ
  rw [smul_add, smul_comm, weyl_smul_bumpV, weyl_smul_phiV, show -(j - 1) = 1 - j by ring] at hw
  exact hw

end Driver
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section Locus

theorem locus_factorization (γ q : ℂ) : q * (γ - 1) ^ 2 - γ * (q - 1) ^ 2 = (q * γ - 1) * (γ - q) := by
  ring

theorem locus_ne_zero {γ : ℂ} (hγp : γ ≠ (p : ℂ)) (hγp' : γ ≠ ((p : ℂ))⁻¹) :
    ((p : ℂ) * γ - 1) * (γ - p) ≠ 0 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  refine mul_ne_zero ?_ (sub_ne_zero.mpr hγp)
  intro h
  apply hγp'
  rw [sub_eq_zero] at h
  exact eq_inv_of_mul_eq_one_right h

end Locus
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end PSCarrier
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section Audit
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.isIrreducibleGLRep_of_generation_of_extraction
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.extraction_step
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.extraction_coeff_eq_zero
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.weyl_testVector_mem
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.locus_factorization
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.locus_ne_zero
end Audit
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end DeskModule09
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section DeskModule10

set_option autoImplicit false

noncomputable section

open Matrix FLT.EKAverage FLT.SmoothVectors

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"
open LocalNewvector

namespace PSCarrier
open LocalNewvector.PSCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

section EvalWeyl

def evalWeyl : PSCarrier p μ₁ μ₂ →ₗ[ℂ] ℂ where
  toFun f := toFn p μ₁ μ₂ f (weyl p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem evalWeyl_apply (f : PSCarrier p μ₁ μ₂) :
    evalWeyl p μ₁ μ₂ f = toFn p μ₁ μ₂ f (weyl p) := rfl

theorem evalWeyl_surjective (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    Function.Surjective (evalWeyl p μ₁ μ₂) := fun c =>
  ⟨c • phiV p μ₁ μ₂ h₁ h₂ 0, by
    rw [map_smul, evalWeyl_apply, toFn_phiV_weyl, smul_eq_mul, mul_one]⟩

end EvalWeyl
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section ExtCells

theorem ext_cells {f g : PSCarrier p μ₁ μ₂}
    (hN : ∀ y : ℚ_[p], toFn p μ₁ μ₂ f (lowerUnip p y) = toFn p μ₁ μ₂ g (lowerUnip p y))
    (hw : toFn p μ₁ μ₂ f (weyl p) = toFn p μ₁ μ₂ g (weyl p)) :
    f = g := by
  refine ext p μ₁ μ₂ fun z => ?_
  rcases cell_cases p z with ⟨a₁, a₂, x, y, hz⟩ | ⟨a₁, a₂, x, hz⟩
  · rw [hz, apply_borelElem_mul p μ₁ μ₂ (toFn_mem p μ₁ μ₂ f),
      apply_borelElem_mul p μ₁ μ₂ (toFn_mem p μ₁ μ₂ g), hN]
  · rw [hz, apply_borelElem_mul p μ₁ μ₂ (toFn_mem p μ₁ μ₂ f),
      apply_borelElem_mul p μ₁ μ₂ (toFn_mem p μ₁ μ₂ g), hw]

theorem eq_zero_of_cells {f : PSCarrier p μ₁ μ₂}
    (hN : ∀ y : ℚ_[p], toFn p μ₁ μ₂ f (lowerUnip p y) = 0)
    (hw : toFn p μ₁ μ₂ f (weyl p) = 0) :
    f = 0 :=
  ext_cells p μ₁ μ₂ (fun y => (hN y).trans rfl) (hw.trans rfl)

end ExtCells
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section TailVanishing

theorem apply_lowerUnip_eq_zero_of_weyl_eq_zero
    (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂)
    {m : ℕ} (hm : ∀ (x : GL (Fin 2) ℚ_[p]) (z : ℚ_[p]), ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ)) →
      f (x * borelElem p 1 1 z) = f x)
    (hw : f (weyl p) = 0) {y : ℚ_[p]} (hy : (p : ℝ) ^ (m : ℤ) ≤ ‖y‖) :
    f (lowerUnip p y) = 0 := by
  have hy0 : y ≠ 0 := by
    rintro rfl; simp only [norm_zero] at hy
    have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out (p := p.Prime)).pos
    exact absurd hy (not_le.mpr (zpow_pos hp _))
  have hz0 : ‖(0 : ℚ_[p])‖ < ‖y‖ := by
    simp only [norm_zero]; exact norm_pos_iff.mpr hy0
  have := P6B.tail_summand p μ₁ μ₂ hf h₁ h₂ hm hy0 hy hz0
  rw [add_zero] at this
  rw [this, hw, mul_zero]

end TailVanishing
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section WInclusions

variable (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)

theorem bumpV_pred_mem {W : Submodule ℂ (PSCarrier p μ₁ μ₂)} (hW : IsStable p μ₁ μ₂ W)
    {k : ℤ} (hk : bumpV p μ₁ μ₂ h₁ h₂ k ∈ W) :
    bumpV p μ₁ μ₂ h₁ h₂ (k - 1) ∈ W :=
  bumpV_mem_of_smul_mem p μ₁ μ₂ h₁ h₂ (lawFactor_ne_zero p μ₁ μ₂ _ _)
    (diagP_smul_bumpV p μ₁ μ₂ h₁ h₂ k ▸ hW _ _ hk)

theorem bumpV_succ_mem {W : Submodule ℂ (PSCarrier p μ₁ μ₂)} (hW : IsStable p μ₁ μ₂ W)
    {k : ℤ} (hk : bumpV p μ₁ μ₂ h₁ h₂ k ∈ W) :
    bumpV p μ₁ μ₂ h₁ h₂ (k + 1) ∈ W :=
  bumpV_mem_of_smul_mem p μ₁ μ₂ h₁ h₂ (lawFactor_ne_zero p μ₁ μ₂ _ _)
    (diagPw_smul_bumpV p μ₁ μ₂ h₁ h₂ k ▸ hW _ _ hk)

theorem bumpV_mem_of_bumpV_mem {W : Submodule ℂ (PSCarrier p μ₁ μ₂)} (hW : IsStable p μ₁ μ₂ W)
    {k₀ : ℤ} (hk₀ : bumpV p μ₁ μ₂ h₁ h₂ k₀ ∈ W) (k : ℤ) :
    bumpV p μ₁ μ₂ h₁ h₂ k ∈ W := by
  obtain ⟨n, rfl | rfl⟩ : ∃ n : ℕ, k = k₀ + n ∨ k = k₀ - n := by
    rcases le_or_gt k₀ k with h | h
    · exact ⟨(k - k₀).toNat, Or.inl (by omega)⟩
    · exact ⟨(k₀ - k).toNat, Or.inr (by omega)⟩
  · induction n with
    | zero => simpa using hk₀
    | succ n ih =>
        have : k₀ + ↑(n + 1) = (k₀ + ↑n) + 1 := by push_cast; ring
        exact this ▸ bumpV_succ_mem p μ₁ μ₂ h₁ h₂ hW ih
  · induction n with
    | zero => simpa using hk₀
    | succ n ih =>
        have : k₀ - ↑(n + 1) = (k₀ - ↑n) - 1 := by push_cast; ring
        exact this ▸ bumpV_pred_mem p μ₁ μ₂ h₁ h₂ hW ih

theorem lowerUnip_smul_bumpV_mem {W : Submodule ℂ (PSCarrier p μ₁ μ₂)} (hW : IsStable p μ₁ μ₂ W)
    {k₀ : ℤ} (hk₀ : bumpV p μ₁ μ₂ h₁ h₂ k₀ ∈ W) (z : ℚ_[p]) (k : ℤ) :
    lowerUnip p z • bumpV p μ₁ μ₂ h₁ h₂ k ∈ W :=
  hW _ _ (bumpV_mem_of_bumpV_mem p μ₁ μ₂ h₁ h₂ hW hk₀ k)

end WInclusions
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section PartitionEngine

variable (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)

theorem lowerUnip_smul_bumpV_eq_self_iff (M : ℤ) (z : ℚ_[p]) :
    lowerUnip p z • bumpV p μ₁ μ₂ h₁ h₂ M = bumpV p μ₁ μ₂ h₁ h₂ M
      ↔ ‖z‖ ≤ (p : ℝ)^(-M) := by
  constructor
  · intro heq
    have h1 := congrArg (fun v => toFn p μ₁ μ₂ v (lowerUnip p (-z))) heq
    simp only [toFn_smul, toFn_bumpV, ← lowerUnip_add, neg_add_cancel, lowerUnip_zero,
      bumpFn_one, bumpFn_lowerUnip] at h1
    by_contra hz
    rw [if_neg (by rwa [norm_neg])] at h1
    exact one_ne_zero h1
  · intro hz
    refine ext_cells p μ₁ μ₂ (fun y => ?_) ?_
    · simp only [toFn_smul, toFn_bumpV, ← lowerUnip_add, bumpFn_lowerUnip]
      congr 1
      refine propext ⟨fun h => ?_, fun h => ?_⟩
      · calc ‖y‖ = ‖(y + z) + (-z)‖ := by ring_nf
          _ ≤ max ‖y + z‖ ‖-z‖ := IsUltrametricDist.norm_add_le_max _ _
          _ ≤ (p : ℝ)^(-M) := max_le h (by rwa [norm_neg])
      · exact (IsUltrametricDist.norm_add_le_max y z).trans (max_le h hz)
    · simp only [toFn_smul, toFn_bumpV]
      have hwnz : weyl p * lowerUnip p z = borelElem p 1 1 z * weyl p := by
        have h := lowerUnip_mul_weyl p z
        calc weyl p * lowerUnip p z
            = weyl p * (lowerUnip p z * weyl p * weyl p) := by
              rw [mul_assoc _ (weyl p) (weyl p), weyl_mul_weyl, mul_one]
          _ = weyl p * (weyl p * borelElem p 1 1 z * weyl p) := by rw [h]
          _ = weyl p * weyl p * borelElem p 1 1 z * weyl p := by
              rw [← mul_assoc, ← mul_assoc]
          _ = borelElem p 1 1 z * weyl p := by rw [weyl_mul_weyl, one_mul]
      rw [hwnz, bumpFn_borelElem_mul, bumpFn_weyl, mul_zero]

theorem stabilizer_bumpV_eq_subgroupOf (j M : ℤ) :
    MulAction.stabilizer (lowerUnipSubgroup p j) (bumpV p μ₁ μ₂ h₁ h₂ M)
      = (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p j) := by
  ext ⟨g, hg⟩
  obtain ⟨z, hz, rfl⟩ := hg
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
    mem_lowerUnipSubgroup_iff]
  constructor
  · intro heq
    refine ⟨z, ?_, rfl⟩
    have heq' : lowerUnip p z • bumpV p μ₁ μ₂ h₁ h₂ M = bumpV p μ₁ μ₂ h₁ h₂ M := heq
    exact (lowerUnip_smul_bumpV_eq_self_iff p μ₁ μ₂ h₁ h₂ M z).mp heq'
  · rintro ⟨z', hz', heq⟩
    have hzz' : z' = z := by
      have hc := congrArg (fun g => ((g : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0)
        heq
      simpa using hc
    show lowerUnip p z • bumpV p μ₁ μ₂ h₁ h₂ M = bumpV p μ₁ μ₂ h₁ h₂ M
    exact (lowerUnip_smul_bumpV_eq_self_iff p μ₁ μ₂ h₁ h₂ M z).mpr (hzz' ▸ hz')

include h₁ h₂ in

theorem finite_lowerUnipSubgroup_quotient (j M : ℤ) :
    Finite (↥(lowerUnipSubgroup p j)
      ⧸ (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p j)) := by
  rw [← stabilizer_bumpV_eq_subgroupOf p μ₁ μ₂ h₁ h₂ j M]
  exact finite_quotient_stabilizer_lowerUnipSubgroup p j
    (isSmoothVector_carrier p μ₁ μ₂ (bumpV p μ₁ μ₂ h₁ h₂ M))

end PartitionEngine
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section AuditN3a
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.evalWeyl
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.evalWeyl_surjective
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.ext_cells
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.eq_zero_of_cells
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.apply_lowerUnip_eq_zero_of_weyl_eq_zero
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.bumpV_mem_of_bumpV_mem
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.lowerUnip_smul_bumpV_eq_self_iff
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.stabilizer_bumpV_eq_subgroupOf
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.finite_lowerUnipSubgroup_quotient
end AuditN3a
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end PSCarrier
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end DeskModule10
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section DeskModule11

set_option autoImplicit false

noncomputable section

open Matrix

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"
open LocalNewvector

variable (p : ℕ) [Fact p.Prime]

def entry10 (g : GL (Fin 2) ℚ_[p]) : ℚ_[p] := (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0

@[scoped simp] theorem entry10_lowerUnip (y : ℚ_[p]) : entry10 p (lowerUnip p y) = y := by
  simp [entry10, coe_lowerUnip]

theorem lowerUnip_injective : Function.Injective (lowerUnip p) := by
  intro y y' h
  have := congrArg (entry10 p) h
  rwa [entry10_lowerUnip, entry10_lowerUnip] at this

theorem lowerUnip_mem_lowerUnipSubgroup_iff {j : ℤ} {y : ℚ_[p]} :
    lowerUnip p y ∈ lowerUnipSubgroup p j ↔ ‖y‖ ≤ (p : ℝ) ^ (-j) := by
  constructor
  · rintro ⟨y', hy', h⟩
    rwa [lowerUnip_injective p h] at hy'
  · exact fun h => lowerUnip_mem_lowerUnipSubgroup p h

theorem exists_eq_lowerUnip_of_mem_of_notMem {a : ℤ} {k : GL (Fin 2) ℚ_[p]}
    (hk : k ∈ lowerUnipSubgroup p (a - 1)) (hk' : k ∉ lowerUnipSubgroup p a) :
    ∃ y : ℚ_[p], ‖y‖ = (p : ℝ) ^ (1 - a) ∧ lowerUnip p y = k := by
  obtain ⟨y, hy, rfl⟩ := hk
  refine ⟨y, le_antisymm (by rwa [neg_sub] at hy) ?_, rfl⟩
  rw [lowerUnip_mem_lowerUnipSubgroup_iff, not_le] at hk'
  have h := (Padic.norm_le_pow_iff_norm_lt_pow_add_one y (-a)).not
  rw [not_le, not_lt, show -a + 1 = 1 - a by ring] at h
  exact h.mp hk'

section Digit

variable (a : ℤ)

theorem norm_entry10_le (k : ↥(lowerUnipSubgroup p (a - 1))) :
    ‖entry10 p (k : GL (Fin 2) ℚ_[p])‖ ≤ (p : ℝ) ^ (1 - a) := by
  obtain ⟨y, hy, hk⟩ := k.property
  rw [← hk, entry10_lowerUnip, ← neg_sub]
  exact hy

def scaledEntry (k : ↥(lowerUnipSubgroup p (a - 1))) : ℤ_[p] :=
  ⟨(p : ℚ_[p]) ^ (1 - a) * entry10 p (k : GL (Fin 2) ℚ_[p]), by
    have hp1 := one_lt_p_real p
    have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
    rw [norm_mul, norm_zpow, Padic.norm_p, _root_.inv_zpow', neg_sub]
    calc (p : ℝ) ^ (a - 1) * ‖entry10 p (k : GL (Fin 2) ℚ_[p])‖
        ≤ (p : ℝ) ^ (a - 1) * (p : ℝ) ^ (1 - a) :=
          mul_le_mul_of_nonneg_left (norm_entry10_le p a k) (zpow_nonneg hp0.le _)
      _ = 1 := by rw [← zpow_add₀ (ne_of_gt hp0), show a - 1 + (1 - a) = 0 by ring, zpow_zero]⟩

@[scoped simp] theorem coe_scaledEntry (k : ↥(lowerUnipSubgroup p (a - 1))) :
    (scaledEntry p a k : ℚ_[p]) = (p : ℚ_[p]) ^ (1 - a) * entry10 p (k : GL (Fin 2) ℚ_[p]) := rfl

theorem scaledEntry_one : scaledEntry p a 1 = 0 := by
  apply Subtype.ext
  rw [coe_scaledEntry, PadicInt.coe_zero]
  simp [entry10]

theorem scaledEntry_mul (k k' : ↥(lowerUnipSubgroup p (a - 1))) :
    scaledEntry p a (k * k') = scaledEntry p a k + scaledEntry p a k' := by
  apply Subtype.ext
  rw [PadicInt.coe_add, coe_scaledEntry, coe_scaledEntry, coe_scaledEntry, ← mul_add]
  congr 1
  obtain ⟨y, -, hk⟩ := k.property
  obtain ⟨y', -, hk'⟩ := k'.property
  rw [Subgroup.coe_mul, ← hk, ← hk', ← lowerUnip_add, entry10_lowerUnip, entry10_lowerUnip,
    entry10_lowerUnip]

def digit : ↥(lowerUnipSubgroup p (a - 1)) →* Multiplicative (ZMod p) where
  toFun k := Multiplicative.ofAdd (PadicInt.toZMod (scaledEntry p a k))
  map_one' := by rw [scaledEntry_one, map_zero, ofAdd_zero]
  map_mul' k k' := by rw [scaledEntry_mul, map_add, ofAdd_add]

theorem digit_apply (k : ↥(lowerUnipSubgroup p (a - 1))) :
    digit p a k = Multiplicative.ofAdd (PadicInt.toZMod (scaledEntry p a k)) := rfl

theorem digit_eq_one_iff (k : ↥(lowerUnipSubgroup p (a - 1))) :
    digit p a k = 1 ↔ (k : GL (Fin 2) ℚ_[p]) ∈ lowerUnipSubgroup p a := by
  have hp1 := one_lt_p_real p
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  obtain ⟨y, hy, hk⟩ := k.property
  rw [digit_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ← RingHom.mem_ker,
    PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def,
    coe_scaledEntry, ← hk, entry10_lowerUnip, lowerUnip_mem_lowerUnipSubgroup_iff, norm_mul,
    norm_zpow, Padic.norm_p, _root_.inv_zpow', neg_sub,
    Padic.norm_le_pow_iff_norm_lt_pow_add_one y (-a)]
  rw [← zpow_neg_mul_zpow_self (1 - a) (ne_of_gt hp0), neg_sub, show -a + 1 = 1 - a by ring]
  exact mul_lt_mul_iff_right₀ (zpow_pos hp0 _)

theorem ker_digit :
    (digit p a).ker = (lowerUnipSubgroup p a).subgroupOf (lowerUnipSubgroup p (a - 1)) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, digit_eq_one_iff]

theorem digit_surjective : Function.Surjective (digit p a) := by
  have hp1 := one_lt_p_real p
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  have hp0' : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  intro t
  set n : ℕ := (Multiplicative.toAdd t).val with hn
  have hy : ‖(p : ℚ_[p]) ^ (a - 1) * (n : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(a - 1)) := by
    rw [norm_mul, norm_zpow, Padic.norm_p, _root_.inv_zpow']
    calc (p : ℝ) ^ (-(a - 1)) * ‖(n : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(a - 1)) * 1 :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast Padic.norm_int_le_one (n : ℤ))
            (zpow_nonneg hp0.le _)
      _ = (p : ℝ) ^ (-(a - 1)) := mul_one _
  refine ⟨⟨lowerUnip p ((p : ℚ_[p]) ^ (a - 1) * (n : ℚ_[p])), lowerUnip_mem_lowerUnipSubgroup p hy⟩, ?_⟩
  rw [digit_apply]
  have hz : scaledEntry p a ⟨lowerUnip p ((p : ℚ_[p]) ^ (a - 1) * (n : ℚ_[p])),
      lowerUnip_mem_lowerUnipSubgroup p hy⟩ = (n : ℤ_[p]) := by
    apply Subtype.ext
    rw [coe_scaledEntry, PadicInt.coe_natCast, Subgroup.coe_mk, entry10_lowerUnip, ← mul_assoc,
      ← zpow_add₀ hp0', show 1 - a + (a - 1) = 0 by ring, zpow_zero, one_mul]
  rw [hz, map_natCast, hn, ZMod.natCast_zmod_val]
  rfl

end Digit
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

theorem card_quotient_lowerUnipSubgroup (a : ℤ) :
    Nat.card (↥(lowerUnipSubgroup p (a - 1)) ⧸
      (lowerUnipSubgroup p a).subgroupOf (lowerUnipSubgroup p (a - 1))) = p := by
  rw [Nat.card_congr (Subgroup.quotientEquivOfEq (ker_digit p a).symm),
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (digit p a)
      (digit_surjective p a)).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

scoped instance finite_quotient_lowerUnipSubgroup (a : ℤ) :
    Finite (↥(lowerUnipSubgroup p (a - 1)) ⧸
      (lowerUnipSubgroup p a).subgroupOf (lowerUnipSubgroup p (a - 1))) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_quotient_lowerUnipSubgroup]
  exact Nat.Prime.ne_zero Fact.out

theorem index_lowerUnipSubgroup (a : ℤ) :
    ((lowerUnipSubgroup p a).subgroupOf (lowerUnipSubgroup p (a - 1))).index = p := by
  rw [Subgroup.index_eq_card, card_quotient_lowerUnipSubgroup]

theorem mk_eq_one_iff {a : ℤ} (k : ↥(lowerUnipSubgroup p (a - 1))) :
    (QuotientGroup.mk k : ↥(lowerUnipSubgroup p (a - 1)) ⧸
        (lowerUnipSubgroup p a).subgroupOf (lowerUnipSubgroup p (a - 1)))
      = QuotientGroup.mk 1 ↔ (k : GL (Fin 2) ℚ_[p]) ∈ lowerUnipSubgroup p a := by
  rw [QuotientGroup.eq, mul_one, inv_mem_iff, Subgroup.mem_subgroupOf]

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section Audit
#print axioms FLT.PrincipalSeriesGL2Padic.lowerUnip_injective
#print axioms FLT.PrincipalSeriesGL2Padic.exists_eq_lowerUnip_of_mem_of_notMem
#print axioms FLT.PrincipalSeriesGL2Padic.digit
#print axioms FLT.PrincipalSeriesGL2Padic.digit_eq_one_iff
#print axioms FLT.PrincipalSeriesGL2Padic.ker_digit
#print axioms FLT.PrincipalSeriesGL2Padic.digit_surjective
#print axioms FLT.PrincipalSeriesGL2Padic.card_quotient_lowerUnipSubgroup
#print axioms FLT.PrincipalSeriesGL2Padic.index_lowerUnipSubgroup
#print axioms FLT.PrincipalSeriesGL2Padic.mk_eq_one_iff
end Audit
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end DeskModule11
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section DeskModule12

set_option autoImplicit false

noncomputable section

open FLT.PrincipalSeriesGL2Padic FLT.PrincipalSeriesGL2Padic.PSCarrier LocalNewvector LocalNewvector.PSCarrier

namespace P6B
open LocalNewvector

variable (p : ℕ) [Fact p.Prime]

theorem weyl_mul_lowerUnip (z : ℚ_[p]) :
    weyl p * lowerUnip p z = borelElem p 1 1 z * weyl p := by
  have h1 := weyl_mul_borelElem_one_one_mul_weyl p z
  calc weyl p * lowerUnip p z
      = weyl p * (weyl p * borelElem p 1 1 z * weyl p) := by rw [h1]
    _ = borelElem p 1 1 z * weyl p := by
        rw [← mul_assoc, ← mul_assoc, weyl_mul_weyl, one_mul]

def repCoord {j M : ℤ}
    (q : ↥(lowerUnipSubgroup p j) ⧸
      (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p j)) : ℚ_[p] :=
  Classical.choose ((mem_lowerUnipSubgroup_iff p).mp (Quotient.out q).2)

theorem norm_repCoord_le {j M : ℤ}
    (q : ↥(lowerUnipSubgroup p j) ⧸
      (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p j)) :
    ‖repCoord p q‖ ≤ (p : ℝ) ^ (-j) :=
  (Classical.choose_spec ((mem_lowerUnipSubgroup_iff p).mp (Quotient.out q).2)).1

theorem lowerUnip_repCoord {j M : ℤ}
    (q : ↥(lowerUnipSubgroup p j) ⧸
      (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p j)) :
    lowerUnip p (repCoord p q)
      = ((Quotient.out q : ↥(lowerUnipSubgroup p j)) : GL (Fin 2) ℚ_[p]) :=
  (Classical.choose_spec ((mem_lowerUnipSubgroup_iff p).mp (Quotient.out q).2)).2

theorem mk_eq_mk_iff_norm_sub {j M : ℤ} {y y' : ℚ_[p]}
    (hy : ‖y‖ ≤ (p : ℝ) ^ (-j)) (hy' : ‖y'‖ ≤ (p : ℝ) ^ (-j)) :
    (QuotientGroup.mk (⟨lowerUnip p y, lowerUnip_mem_lowerUnipSubgroup p hy⟩ :
        ↥(lowerUnipSubgroup p j)) :
      ↥(lowerUnipSubgroup p j) ⧸
        (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p j))
      = QuotientGroup.mk ⟨lowerUnip p y', lowerUnip_mem_lowerUnipSubgroup p hy'⟩
    ↔ ‖y' - y‖ ≤ (p : ℝ) ^ (-M) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hcoe : (((⟨lowerUnip p y, lowerUnip_mem_lowerUnipSubgroup p hy⟩ :
        ↥(lowerUnipSubgroup p j))⁻¹
      * ⟨lowerUnip p y', lowerUnip_mem_lowerUnipSubgroup p hy'⟩ :
        ↥(lowerUnipSubgroup p j)) : GL (Fin 2) ℚ_[p])
      = lowerUnip p (y' - y) := by
    show (lowerUnip p y)⁻¹ * lowerUnip p y' = lowerUnip p (y' - y)
    rw [lowerUnip_inv, ← lowerUnip_add, neg_add_eq_sub]
  rw [hcoe]
  constructor
  · rintro ⟨y'', hy'', heq⟩
    rwa [← lowerUnip_injective p heq]
  · intro h
    exact lowerUnip_mem_lowerUnipSubgroup p h

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

theorem partition_of_toFn_weyl_eq_zero (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    (f : PSCarrier p μ₁ μ₂) (hfw : toFn p μ₁ μ₂ f (weyl p) = 0)
    {mp mm : ℕ}
    (hmp : ∀ (x : GL (Fin 2) ℚ_[p]) (z : ℚ_[p]), ‖z‖ ≤ (p : ℝ) ^ (-(mp : ℤ)) →
      toFn p μ₁ μ₂ f (x * borelElem p 1 1 z) = toFn p μ₁ μ₂ f x)
    (hmm : ∀ (x : GL (Fin 2) ℚ_[p]) (z : ℚ_[p]), ‖z‖ ≤ (p : ℝ) ^ (-(mm : ℤ)) →
      toFn p μ₁ μ₂ f (x * lowerUnip p z) = toFn p μ₁ μ₂ f x)
    {M : ℤ} (hMp : (mp : ℤ) ≤ M) (hMm : (mm : ℤ) ≤ M) (hM0 : 0 ≤ M)
    [Fintype (↥(lowerUnipSubgroup p (-M)) ⧸
      (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)))] :
    f = ∑ q : ↥(lowerUnipSubgroup p (-M)) ⧸
          (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)),
        toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q)) •
          (lowerUnip p (-(repCoord p q)) • bumpV p μ₁ μ₂ h₁ h₂ M) := by
  classical
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt

  have hval : ∀ (q : ↥(lowerUnipSubgroup p (-M)) ⧸
      (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)))
      (x : GL (Fin 2) ℚ_[p]), toFn p μ₁ μ₂
      (toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q)) •
        (lowerUnip p (-(repCoord p q)) • bumpV p μ₁ μ₂ h₁ h₂ M)) x
      = toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q))
          * bumpFn p μ₁ μ₂ M (x * lowerUnip p (-(repCoord p q))) := by
    intro q x
    rw [toFn_csmul, toFn_smul, toFn_bumpV]

  have hterm : ∀ (y : ℚ_[p]) (q : ↥(lowerUnipSubgroup p (-M)) ⧸
      (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M))), toFn p μ₁ μ₂
      (toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q)) •
        (lowerUnip p (-(repCoord p q)) • bumpV p μ₁ μ₂ h₁ h₂ M)) (lowerUnip p y)
      = toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q))
          * (if ‖y - repCoord p q‖ ≤ (p : ℝ) ^ (-M) then 1 else 0) := by
    intro y q
    rw [hval q (lowerUnip p y), ← lowerUnip_add,
      show y + -(repCoord p q) = y - repCoord p q from (sub_eq_add_neg _ _).symm,
      bumpFn_lowerUnip]
  refine ext_cells p μ₁ μ₂ (fun y => ?_) ?_
  ·
    have hsum : toFn p μ₁ μ₂ (∑ q : ↥(lowerUnipSubgroup p (-M)) ⧸
        (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)),
        toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q)) •
        (lowerUnip p (-(repCoord p q)) • bumpV p μ₁ μ₂ h₁ h₂ M)) (lowerUnip p y)
        = ∑ q : ↥(lowerUnipSubgroup p (-M)) ⧸
            (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)),
            toFn p μ₁ μ₂ (toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q)) •
            (lowerUnip p (-(repCoord p q)) • bumpV p μ₁ μ₂ h₁ h₂ M)) (lowerUnip p y) := by
      exact map_sum (evalLin p μ₁ μ₂ (lowerUnip p y)) _ Finset.univ
    rw [hsum]
    by_cases hy : ‖y‖ ≤ (p : ℝ) ^ M
    ·
      have hymem : ‖y‖ ≤ (p : ℝ) ^ (-(-M) : ℤ) := by rwa [neg_neg]
      set qy := (QuotientGroup.mk
        (⟨lowerUnip p y, lowerUnip_mem_lowerUnipSubgroup p hymem⟩ :
          ↥(lowerUnipSubgroup p (-M))) :
        ↥(lowerUnipSubgroup p (-M)) ⧸
          (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M))) with hqy
      have hchar : ∀ q, (‖y - repCoord p q‖ ≤ (p : ℝ) ^ (-M)) ↔ q = qy := by
        intro q
        have hznorm : ‖repCoord p q‖ ≤ (p : ℝ) ^ (-(-M) : ℤ) := norm_repCoord_le p q
        have hq : (QuotientGroup.mk
            (⟨lowerUnip p (repCoord p q), lowerUnip_mem_lowerUnipSubgroup p hznorm⟩ :
              ↥(lowerUnipSubgroup p (-M))) :
            ↥(lowerUnipSubgroup p (-M)) ⧸
              (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M))) = q := by
          have hout : (⟨lowerUnip p (repCoord p q),
              lowerUnip_mem_lowerUnipSubgroup p hznorm⟩ :
              ↥(lowerUnipSubgroup p (-M))) = Quotient.out q :=
            Subtype.ext (lowerUnip_repCoord p q)
          rw [hout]
          exact Quotient.out_eq q
        constructor
        · intro hcond
          rw [← hq, hqy]
          exact (mk_eq_mk_iff_norm_sub p hznorm hymem).mpr hcond
        · intro heq
          have hmk : (QuotientGroup.mk
              (⟨lowerUnip p (repCoord p q), lowerUnip_mem_lowerUnipSubgroup p hznorm⟩ :
                ↥(lowerUnipSubgroup p (-M))) :
              ↥(lowerUnipSubgroup p (-M)) ⧸
                (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)))
              = QuotientGroup.mk ⟨lowerUnip p y, lowerUnip_mem_lowerUnipSubgroup p hymem⟩ := by
            rw [hq, heq, hqy]
          exact (mk_eq_mk_iff_norm_sub p hznorm hymem).mp hmk
      have hLHS : toFn p μ₁ μ₂ f (lowerUnip p y)
          = toFn p μ₁ μ₂ f (lowerUnip p (repCoord p qy)) := by
        have hclose : ‖y - repCoord p qy‖ ≤ (p : ℝ) ^ (-M) := (hchar qy).mpr rfl
        have hc' : ‖repCoord p qy - y‖ ≤ (p : ℝ) ^ (-(mm : ℤ)) := by
          rw [norm_sub_rev]
          exact le_trans hclose (zpow_le_zpow_right₀ hp1.le (by omega))
        have h := hmm (lowerUnip p y) (repCoord p qy - y) hc'
        rw [← lowerUnip_add,
          show y + (repCoord p qy - y) = repCoord p qy from by ring] at h
        exact h.symm
      calc toFn p μ₁ μ₂ f (lowerUnip p y)
            = toFn p μ₁ μ₂ f (lowerUnip p (repCoord p qy)) := hLHS
        _ = ∑ q : ↥(lowerUnipSubgroup p (-M)) ⧸
              (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)),
              toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q))
              * (if q = qy then 1 else 0) := by
            rw [Finset.sum_congr rfl
              (fun q _ => by rw [mul_ite, mul_one, mul_zero]),
              Finset.sum_ite_eq' Finset.univ qy
                (fun q => toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q))),
              if_pos (Finset.mem_univ _)]
        _ = ∑ q : ↥(lowerUnipSubgroup p (-M)) ⧸
              (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)),
              toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q))
              * (if ‖y - repCoord p q‖ ≤ (p : ℝ) ^ (-M) then 1 else 0) := by
            refine Finset.sum_congr rfl fun q _ => ?_
            exact congrArg (toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q)) * ·)
              (if_congr (hchar q).symm rfl rfl)
        _ = _ := Finset.sum_congr rfl fun q _ => (hterm y q).symm
    ·
      rw [not_le] at hy
      have hy0 : y ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hy
        exact absurd hy (not_lt.mpr (le_of_lt (zpow_pos (by positivity) _)))
      have hLHS : toFn p μ₁ μ₂ f (lowerUnip p y) = 0 := by
        have htail := apply_lowerUnip_eq_tail p μ₁ μ₂ (toFn_mem p μ₁ μ₂ f) y hy0
        have hbound : ‖(y⁻¹ : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(mp : ℤ)) := by
          rw [norm_inv]
          have h1 : (p : ℝ) ^ (mp : ℤ) ≤ ‖y‖ :=
            le_of_lt (lt_of_le_of_lt (zpow_le_zpow_right₀ hp1.le hMp) hy)
          rw [zpow_neg, ← one_div, ← one_div]
          exact one_div_le_one_div_of_le (zpow_pos (by positivity) _) h1
        have hcol := hmp (weyl p) y⁻¹ hbound
        rw [htail, hcol, hfw, mul_zero]
      rw [hLHS]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [hterm y q, if_neg, mul_zero]
      rw [not_le, sub_eq_add_neg,
        norm_add_eq_of_norm_lt p (by
          rw [norm_neg]
          exact lt_of_le_of_lt (by simpa [neg_neg] using norm_repCoord_le p q) hy)]
      exact lt_of_le_of_lt (zpow_le_zpow_right₀ hp1.le (by omega)) hy
  ·
    have hsum : toFn p μ₁ μ₂ (∑ q : ↥(lowerUnipSubgroup p (-M)) ⧸
        (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)),
        toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q)) •
        (lowerUnip p (-(repCoord p q)) • bumpV p μ₁ μ₂ h₁ h₂ M)) (weyl p)
        = ∑ q : ↥(lowerUnipSubgroup p (-M)) ⧸
            (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)),
            toFn p μ₁ μ₂ (toFn p μ₁ μ₂ f (lowerUnip p (repCoord p q)) •
            (lowerUnip p (-(repCoord p q)) • bumpV p μ₁ μ₂ h₁ h₂ M)) (weyl p) := by
      exact map_sum (evalLin p μ₁ μ₂ (weyl p)) _ Finset.univ
    rw [hsum, hfw]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [hval, weyl_mul_lowerUnip, bumpFn_borelElem_mul, bumpFn_weyl, mul_zero, mul_zero]

theorem generation (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) :
    ∀ W : Submodule ℂ (PSCarrier p μ₁ μ₂), IsStable p μ₁ μ₂ W →
      ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∈ W → W = ⊤ := by
  intro W hW k hk
  have hall : ∀ k', bumpV p μ₁ μ₂ h₁ h₂ k' ∈ W :=
    bumpV_mem_of_bumpV_mem p μ₁ μ₂ h₁ h₂ hW hk
  have hphi : ∀ s, phiV p μ₁ μ₂ h₁ h₂ s ∈ W := by
    intro s
    have h := phiV_mem_of_bumpV_mem p μ₁ μ₂ h₁ h₂ hW (hall (-s))
    rwa [neg_neg] at h
  rw [eq_top_iff]
  rintro f -
  set c := toFn p μ₁ μ₂ f (weyl p) with hc
  set g := f - c • phiV p μ₁ μ₂ h₁ h₂ 0 with hg
  have hgw : toFn p μ₁ μ₂ g (weyl p) = 0 := by
    rw [hg]
    show toFn p μ₁ μ₂ f (weyl p)
        - c * toFn p μ₁ μ₂ (phiV p μ₁ μ₂ h₁ h₂ 0) (weyl p) = 0
    rw [toFn_phiV_weyl, mul_one, hc, sub_self]
  obtain ⟨mp, hmp⟩ := exists_right_unipotent_level p μ₁ μ₂ g
  obtain ⟨mm, hmm⟩ := exists_right_lower_unipotent_level p μ₁ μ₂ g
  set M : ℤ := max (max (mp : ℤ) (mm : ℤ)) 0 with hM
  haveI : Finite (↥(lowerUnipSubgroup p (-M)) ⧸
      (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M))) :=
    finite_lowerUnipSubgroup_quotient p μ₁ μ₂ h₁ h₂ (-M) M
  haveI := Fintype.ofFinite (↥(lowerUnipSubgroup p (-M)) ⧸
      (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M)))
  have hpart := partition_of_toFn_weyl_eq_zero p μ₁ μ₂ h₁ h₂ g hgw hmp hmm
    (M := M) (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hgW : g ∈ W := by
    rw [hpart]
    exact Submodule.sum_mem W fun q _ =>
      Submodule.smul_mem W _ (hW _ _ (hall M))
  have hf : f = g + c • phiV p μ₁ μ₂ h₁ h₂ 0 := by
    rw [hg]
    abel
  rw [hf]
  exact Submodule.add_mem W hgW (Submodule.smul_mem W c (hphi 0))

end P6B
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

#print axioms P6B.weyl_mul_lowerUnip
#print axioms P6B.repCoord
#print axioms P6B.mk_eq_mk_iff_norm_sub
#print axioms P6B.partition_of_toFn_weyl_eq_zero
#print axioms P6B.generation

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end DeskModule12
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section DeskModule13

set_option autoImplicit false

noncomputable section

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"
open LocalNewvector

namespace PSCarrier
open LocalNewvector.PSCarrier

open FLT.PrincipalSeriesGL2Padic LocalNewvector

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

section Constants

def sqrtC : ℂ := ((Real.sqrt (p : ℝ) : ℝ) : ℂ)

omit [Fact p.Prime] in
theorem sqrtC_mul_self : sqrtC p * sqrtC p = (p : ℂ) := by
  rw [sqrtC, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p), Complex.ofReal_natCast]

theorem natCast_p_ne_zero : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)

theorem lawFactor_one_pUnit : lawFactor p μ₁ μ₂ 1 (pUnit p) = (μ₂ (pUnit p) : ℂ) * sqrtC p := by
  rw [lawFactor, map_one, Units.val_one, one_mul, halfModulus, Units.val_one, norm_one, norm_pUnit,
    one_div, inv_inv, sqrtC]

theorem lawFactor_pUnit_one_mul_sqrtC :
    lawFactor p μ₁ μ₂ (pUnit p) 1 * sqrtC p = (μ₁ (pUnit p) : ℂ) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [lawFactor, map_one, Units.val_one, mul_one, halfModulus, Units.val_one, norm_one, norm_pUnit,
    div_one, sqrtC, mul_assoc, ← Complex.ofReal_mul, ← Real.sqrt_mul (inv_nonneg.mpr hp0),
    inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one (one_lt_p_real p))), Real.sqrt_one,
    Complex.ofReal_one, mul_one]

theorem gammaRatio_mul : gammaRatio p μ₁ μ₂ * (μ₂ (pUnit p) : ℂ) = (μ₁ (pUnit p) : ℂ) := by
  rw [gammaRatio, mul_assoc, inv_mul_cancel₀ (μ₂ (pUnit p)).ne_zero, mul_one]

theorem p_mul_eq_gamma_mul_of_extraction {A B : ℂ}
    (hD : lawFactor p μ₁ μ₂ 1 (pUnit p) * A = lawFactor p μ₁ μ₂ (pUnit p) 1 * B) :
    (p : ℂ) * A = gammaRatio p μ₁ μ₂ * B := by
  rw [lawFactor_one_pUnit] at hD
  have hs := sqrtC_mul_self p
  have hL := lawFactor_pUnit_one_mul_sqrtC p μ₁ μ₂
  have hγ := gammaRatio_mul p μ₁ μ₂
  have h1 : (μ₂ (pUnit p) : ℂ) * ((p : ℂ) * A) = (μ₂ (pUnit p) : ℂ) * (gammaRatio p μ₁ μ₂ * B) := by
    linear_combination (sqrtC p) * hD - ((μ₂ (pUnit p) : ℂ) * A) * hs + B * hL - B * hγ
  exact mul_left_cancel₀ (μ₂ (pUnit p)).ne_zero h1

theorem tailChar_mul (y y' : ℚ_[p]ˣ) :
    tailChar p μ₁ μ₂ (y * y') = tailChar p μ₁ μ₂ y * tailChar p μ₁ μ₂ y' := by
  simp only [tailChar, map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_inv]
  ring

def tailAt (n : ℤ) : ℂ := tailChar p μ₁ μ₂ (pUnit p ^ n)

theorem tailAt_add (m n : ℤ) : tailAt p μ₁ μ₂ (m + n) = tailAt p μ₁ μ₂ m * tailAt p μ₁ μ₂ n := by
  rw [tailAt, tailAt, tailAt, zpow_add, tailChar_mul]

theorem p_mul_tailAt_neg_one : (p : ℂ) * tailAt p μ₁ μ₂ (-1) = gammaRatio p μ₁ μ₂ := by
  have hp0 := natCast_p_ne_zero p
  rw [tailAt, zpow_neg_one, tailChar, map_inv, map_inv, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, inv_inv, Units.val_inv_eq_inv_val, val_pUnit, norm_inv, Padic.norm_p,
    inv_inv, Complex.ofReal_natCast, gammaRatio]
  field_simp

theorem p_mul_tailAt_sub_one (n : ℤ) :
    (p : ℂ) * tailAt p μ₁ μ₂ (n - 1) = gammaRatio p μ₁ μ₂ * tailAt p μ₁ μ₂ n := by
  rw [sub_eq_add_neg, tailAt_add, mul_left_comm, p_mul_tailAt_neg_one, mul_comm]

theorem p_mul_tailAt_mul_tailAt (j : ℤ) :
    (p : ℂ) * (tailAt p μ₁ μ₂ (j - 1) * tailAt p μ₁ μ₂ (-j)) = gammaRatio p μ₁ μ₂ := by
  rw [← tailAt_add, show j - 1 + -j = -1 by ring, p_mul_tailAt_neg_one]

theorem norm_pUnit_zpow (n : ℤ) : ‖((pUnit p ^ n : ℚ_[p]ˣ) : ℚ_[p])‖ = (p : ℝ) ^ (-n) := by
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, norm_pUnit, inv_zpow', ]

theorem tailChar_eq_tailAt (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) {a : ℤ} {y : ℚ_[p]}
    (hy0 : y ≠ 0) (hy : ‖y‖ = (p : ℝ) ^ (1 - a)) :
    tailChar p μ₁ μ₂ (Units.mk0 y hy0) = tailAt p μ₁ μ₂ (a - 1) := by
  refine tailChar_eq_of_norm_eq p μ₁ μ₂ h₁ h₂ ?_
  rw [Units.val_mk0, hy, norm_pUnit_zpow, neg_sub]

theorem mu_neg_one_mul_self : (μ₁ (-1) : ℂ) * (μ₁ (-1) : ℂ) = 1 := by
  rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]

end Constants
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

def ShellRec : Prop :=
  ∀ (f : PSCarrier p μ₁ μ₂) (a : ℤ) (c : ℂ),
    (∀ y : ℚ_[p], ‖y‖ = (p : ℝ) ^ (1 - a) → toFn p μ₁ μ₂ f (lowerUnip p y) = c) →
    toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (a - 1) f) 1
      = (p : ℂ)⁻¹ * toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ a f) 1 + (1 - (p : ℂ)⁻¹) * c

section Hext

variable (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)

theorem shellRec_mul (hrec : ShellRec p μ₁ μ₂) (f : PSCarrier p μ₁ μ₂) (a : ℤ) (c : ℂ)
    (hc : ∀ y : ℚ_[p], ‖y‖ = (p : ℝ) ^ (1 - a) → toFn p μ₁ μ₂ f (lowerUnip p y) = c) :
    (p : ℂ) * toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (a - 1) f) 1
      = toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ a f) 1 + ((p : ℂ) - 1) * c := by
  have h := hrec f a c hc
  have hp0 := natCast_p_ne_zero p
  rw [h, mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul, mul_sub, mul_one,
    mul_inv_cancel₀ hp0]

theorem shell_equation (hrec : ShellRec p μ₁ μ₂) {W : Submodule ℂ (PSCarrier p μ₁ μ₂)}
    (hW : IsStable p μ₁ μ₂ W) (hno : ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∉ W)
    {f : PSCarrier p μ₁ μ₂} (hf : f ∈ W) {m : ℕ}
    (hm : ∀ (x : GL (Fin 2) ℚ_[p]) (z : ℚ_[p]), ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ)) →
      toFn p μ₁ μ₂ f (x * borelElem p 1 1 z) = toFn p μ₁ μ₂ f x)
    {a : ℤ} (ha : a ≤ -(m : ℤ)) {c : ℂ}
    (hc : ∀ y : ℚ_[p], ‖y‖ = (p : ℝ) ^ (1 - a) → toFn p μ₁ μ₂ f (lowerUnip p y) = c) :
    (gammaRatio p μ₁ μ₂ - 1) * toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ a f) 1 = ((p : ℂ) - 1) * c := by
  have hu : P6B.avgOp p μ₁ μ₂ (a - 1) f ∈ W :=
    ekAverage_mem_of_invariant p (lowerUnipSubgroup p (a - 1)) W hW hf
      (forall_finite_quotient_stabilizer_lowerUnipSubgroup p (a - 1) f)
  have hv : P6B.avgOp p μ₁ μ₂ a f ∈ W :=
    ekAverage_mem_of_invariant p (lowerUnipSubgroup p a) W hW hf
      (forall_finite_quotient_stabilizer_lowerUnipSubgroup p a f)
  have hu_eq := P6B.avgOp_eq_smul_psiM_add_smul_phiM p μ₁ μ₂ h₁ h₂ f hm (j := a - 1) (by omega)
  have hv_eq := P6B.avgOp_eq_smul_psiM_add_smul_phiM p μ₁ μ₂ h₁ h₂ f hm (j := a) ha
  have hD := extraction_coeff_eq_zero p μ₁ μ₂ h₁ h₂ hW hno hu hv hu_eq hv_eq
  have hE := p_mul_eq_gamma_mul_of_extraction p μ₁ μ₂ hD
  have hR := shellRec_mul p μ₁ μ₂ hrec f a c hc
  linear_combination hR - hE

theorem shell_equation_tail (hrec : ShellRec p μ₁ μ₂) {W : Submodule ℂ (PSCarrier p μ₁ μ₂)}
    (hW : IsStable p μ₁ μ₂ W) (hno : ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∉ W)
    {f : PSCarrier p μ₁ μ₂} (hf : f ∈ W) {m : ℕ}
    (hm : ∀ (x : GL (Fin 2) ℚ_[p]) (z : ℚ_[p]), ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ)) →
      toFn p μ₁ μ₂ f (x * borelElem p 1 1 z) = toFn p μ₁ μ₂ f x)
    {j : ℤ} (hj : j ≤ -(m : ℤ)) :
    (gammaRatio p μ₁ μ₂ - 1) * toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ j f) 1
      = ((p : ℂ) - 1) * ((μ₁ (-1) : ℂ) * tailAt p μ₁ μ₂ (j - 1) * toFn p μ₁ μ₂ f (weyl p)) := by
  refine shell_equation p μ₁ μ₂ h₁ h₂ hrec hW hno hf hm hj (fun y hy => ?_)
  have hp1 := one_lt_p_real p
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy
    exact (ne_of_gt (zpow_pos (lt_trans zero_lt_one hp1) _)) hy.symm
  rw [apply_lowerUnip_eq_tail p μ₁ μ₂ (toFn_mem p μ₁ μ₂ f) y hy0,
    tailChar_eq_tailAt p μ₁ μ₂ h₁ h₂ hy0 hy]
  have hcollapse : toFn p μ₁ μ₂ f (weyl p * borelElem p 1 1 y⁻¹) = toFn p μ₁ μ₂ f (weyl p) := by
    refine hm (weyl p) y⁻¹ ?_
    rw [norm_inv, hy, ← zpow_neg]
    exact zpow_le_zpow_right₀ hp1.le (by omega)
  rw [hcollapse]

theorem locus_of_shell_equations {γ P u fw If β Tf Tj : ℂ} (hfw : fw ≠ 0)
    (hu : u * u = 1) (hβ : β * fw = If) (hTT : P * (Tf * Tj) = γ)
    (E1 : (γ - 1) * If = (P - 1) * (u * Tf * fw))
    (E4 : γ - 1 = β * (P - 1) * u * Tj) :
    P * (γ - 1) ^ 2 - γ * (P - 1) ^ 2 = 0 := by
  have key : (P * (γ - 1) ^ 2 - γ * (P - 1) ^ 2) * fw = 0 := by
    linear_combination (P * (γ - 1) * fw) * E4 + (P * (γ - 1) * (P - 1) * u * Tj) * hβ
      + (P * (P - 1) * u * Tj) * E1 + ((P - 1) ^ 2 * u ^ 2 * fw) * hTT + ((P - 1) ^ 2 * γ * fw) * hu
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact (hfw h).elim

theorem E4_of_E2_T4 {γ P u β Ta Tj Ra Iag : ℂ} (hRa : Ra ≠ 0)
    (E2 : (γ - 1) * Iag = (P - 1) * (β * (u * Ta)))
    (T4 : (γ - 1) * Iag = (γ - 1) * Ra + β * (P - 1) * u * (Ta - Tj * Ra)) :
    γ - 1 = β * (P - 1) * u * Tj := by
  have h : Ra * (γ - 1) = Ra * (β * (P - 1) * u * Tj) := by linear_combination E2 - T4
  exact mul_left_cancel₀ hRa h

def testV (β : ℂ) (j : ℤ) : PSCarrier p μ₁ μ₂ :=
  β • phiV p μ₁ μ₂ h₁ h₂ (-j) + bumpV p μ₁ μ₂ h₁ h₂ (1 - j)

theorem toFn_testV (β : ℂ) (j : ℤ) (x : GL (Fin 2) ℚ_[p]) :
    toFn p μ₁ μ₂ (testV p μ₁ μ₂ h₁ h₂ β j) x = β * phiFn p μ₁ μ₂ (-j) x + bumpFn p μ₁ μ₂ (1 - j) x := rfl

theorem testV_shell {β : ℂ} {j a : ℤ} (ha : a ≤ 1 - j) (y : ℚ_[p]) (hy : ‖y‖ = (p : ℝ) ^ (1 - a)) :
    toFn p μ₁ μ₂ (testV p μ₁ μ₂ h₁ h₂ β j) (lowerUnip p y) = β * ((μ₁ (-1) : ℂ) * tailAt p μ₁ μ₂ (a - 1)) := by
  have hp1 := one_lt_p_real p
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy
    exact (ne_of_gt (zpow_pos (lt_trans zero_lt_one hp1) _)) hy.symm
  have hcond1 : (p : ℝ) ^ (-(-j)) ≤ ‖y‖ := by
    rw [hy, neg_neg]; exact zpow_le_zpow_right₀ hp1.le (by omega)
  have hcond2 : ¬ ‖y‖ ≤ (p : ℝ) ^ (-(1 - j)) := by
    rw [hy, not_le]; exact zpow_lt_zpow_right₀ hp1 (by omega)
  rw [toFn_testV, P6B.phiFn_lowerUnip p μ₁ μ₂ (-j) hy0, if_pos hcond1, bumpFn_lowerUnip, if_neg hcond2,
    add_zero, tailChar_eq_tailAt p μ₁ μ₂ h₁ h₂ hy0 hy]

theorem toFn_avgOp_testV_start (β : ℂ) (j : ℤ) :
    toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (1 - j) (testV p μ₁ μ₂ h₁ h₂ β j)) 1 = 1 := by
  have hp1 := one_lt_p_real p
  refine P6B.toFn_avgOp_eq_of_const p μ₁ μ₂ (1 - j) (testV p μ₁ μ₂ h₁ h₂ β j)
    (forall_finite_quotient_stabilizer_lowerUnipSubgroup p (1 - j) _) (fun k => ?_)
  obtain ⟨y, hy, hk⟩ := k.property
  rw [← hk, one_mul, toFn_testV, bumpFn_lowerUnip, if_pos hy]
  by_cases hy0 : y = 0
  · rw [hy0, lowerUnip_zero, phiFn_one, mul_zero, zero_add]
  · rw [P6B.phiFn_lowerUnip p μ₁ μ₂ (-j) hy0, if_neg, mul_zero, zero_add]
    rw [neg_neg, not_le]
    exact lt_of_le_of_lt hy (zpow_lt_zpow_right₀ hp1 (by omega))

theorem unrolled (hrec : ShellRec p μ₁ μ₂) (β : ℂ) (j : ℤ) (n : ℕ) :
    (gammaRatio p μ₁ μ₂ - 1) * toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (1 - j - (n : ℤ)) (testV p μ₁ μ₂ h₁ h₂ β j)) 1
      = (gammaRatio p μ₁ μ₂ - 1) * (p : ℂ) ^ (-(n : ℤ))
        + β * ((p : ℂ) - 1) * (μ₁ (-1) : ℂ)
          * (tailAt p μ₁ μ₂ (-j - (n : ℤ)) - tailAt p μ₁ μ₂ (-j) * (p : ℂ) ^ (-(n : ℤ))) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, sub_zero, neg_zero, zpow_zero]
    rw [toFn_avgOp_testV_start]
    ring
  | succ n ih =>
    have hp0 := natCast_p_ne_zero p
    have hidx : (1 - j - ((n + 1 : ℕ) : ℤ)) = (1 - j - (n : ℤ)) - 1 := by push_cast; ring
    have hidx2 : (-j - ((n + 1 : ℕ) : ℤ)) = (-j - (n : ℤ)) - 1 := by push_cast; ring
    have hz : (p : ℂ) ^ (-((n + 1 : ℕ) : ℤ)) = (p : ℂ) ^ (-(n : ℤ) - 1) := by
      congr 1; push_cast; ring
    rw [hidx, hidx2, hz]
    have hR := shellRec_mul p μ₁ μ₂ hrec (testV p μ₁ μ₂ h₁ h₂ β j) (1 - j - (n : ℤ)) _
      (fun y hy => testV_shell p μ₁ μ₂ h₁ h₂ (β := β) (j := j) (a := 1 - j - (n : ℤ)) (by omega) y hy)
    have hT' : tailAt p μ₁ μ₂ (1 - j - (n : ℤ) - 1) = tailAt p μ₁ μ₂ (-j - (n : ℤ)) := by
      congr 1; ring
    rw [hT'] at hR
    have hT := p_mul_tailAt_sub_one p μ₁ μ₂ (-j - (n : ℤ))
    have hpz : (p : ℂ) * (p : ℂ) ^ (-(n : ℤ) - 1) = (p : ℂ) ^ (-(n : ℤ)) := by
      rw [zpow_sub_one₀ hp0, mul_left_comm, mul_inv_cancel₀ hp0, mul_one]
    refine mul_left_cancel₀ hp0 ?_
    linear_combination (gammaRatio p μ₁ μ₂ - 1) * hR + ih
      + (β * ((p : ℂ) - 1) * (μ₁ (-1) : ℂ) * tailAt p μ₁ μ₂ (-j) - (gammaRatio p μ₁ μ₂ - 1)) * hpz
      - (β * ((p : ℂ) - 1) * (μ₁ (-1) : ℂ)) * hT

theorem hext_of_rec (hrec : ShellRec p μ₁ μ₂)
    (hγp : gammaRatio p μ₁ μ₂ ≠ (p : ℂ)) (hγp' : gammaRatio p μ₁ μ₂ ≠ ((p : ℂ))⁻¹)
    (W : Submodule ℂ (PSCarrier p μ₁ μ₂)) (hW : IsStable p μ₁ μ₂ W)
    (hno : ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∉ W)
    (f : PSCarrier p μ₁ μ₂) (hf : f ∈ W) (hfw : toFn p μ₁ μ₂ f (weyl p) ≠ 0) : False := by
  obtain ⟨m, hm⟩ := P6B.exists_right_unipotent_level p μ₁ μ₂ f
  have hjm : -(m : ℤ) - 1 ≤ -(m : ℤ) := by omega

  have E1 := shell_equation_tail p μ₁ μ₂ h₁ h₂ hrec hW hno hf hm hjm

  have hv : P6B.avgOp p μ₁ μ₂ (-(m : ℤ) - 1) f ∈ W :=
    ekAverage_mem_of_invariant p (lowerUnipSubgroup p (-(m : ℤ) - 1)) W hW hf
      (forall_finite_quotient_stabilizer_lowerUnipSubgroup p (-(m : ℤ) - 1) f)
  have hv_eq := P6B.avgOp_eq_smul_psiM_add_smul_phiM p μ₁ μ₂ h₁ h₂ f hm hjm
  have hg : testV p μ₁ μ₂ h₁ h₂
      (toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (-(m : ℤ) - 1) f) 1 * (toFn p μ₁ μ₂ f (weyl p))⁻¹)
      (-(m : ℤ) - 1) ∈ W :=
    weyl_testVector_mem p μ₁ μ₂ h₁ h₂ hW hfw hv hv_eq

  obtain ⟨m', hm'⟩ := P6B.exists_right_unipotent_level p μ₁ μ₂ (testV p μ₁ μ₂ h₁ h₂
      (toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (-(m : ℤ) - 1) f) 1 * (toFn p μ₁ μ₂ f (weyl p))⁻¹)
      (-(m : ℤ) - 1))
  have ha1 : 1 - (-(m : ℤ) - 1) - ((Int.toNat (1 - (-(m : ℤ) - 1) + m') : ℕ) : ℤ) ≤ -(m' : ℤ) := by
    have := Int.self_le_toNat (1 - (-(m : ℤ) - 1) + m')
    omega

  have E2 := shell_equation p μ₁ μ₂ h₁ h₂ hrec hW hno hg hm' ha1
    (fun y hy => testV_shell p μ₁ μ₂ h₁ h₂ (by omega) y hy)
  have hT' : tailAt p μ₁ μ₂ (1 - (-(m : ℤ) - 1) - ((Int.toNat (1 - (-(m : ℤ) - 1) + m') : ℕ) : ℤ) - 1)
      = tailAt p μ₁ μ₂ (-(-(m : ℤ) - 1) - ((Int.toNat (1 - (-(m : ℤ) - 1) + m') : ℕ) : ℤ)) := by
    congr 1; ring
  rw [hT'] at E2

  have T4 := unrolled p μ₁ μ₂ h₁ h₂ hrec
    (toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (-(m : ℤ) - 1) f) 1 * (toFn p μ₁ μ₂ f (weyl p))⁻¹)
    (-(m : ℤ) - 1) (Int.toNat (1 - (-(m : ℤ) - 1) + m'))

  have hRa : (p : ℂ) ^ (-((Int.toNat (1 - (-(m : ℤ) - 1) + m') : ℕ) : ℤ)) ≠ 0 :=
    zpow_ne_zero _ (natCast_p_ne_zero p)
  have E4 := E4_of_E2_T4 hRa E2 T4
  have hβ : toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (-(m : ℤ) - 1) f) 1 * (toFn p μ₁ μ₂ f (weyl p))⁻¹
      * toFn p μ₁ μ₂ f (weyl p) = toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (-(m : ℤ) - 1) f) 1 :=
    inv_mul_cancel_right₀ hfw _
  have hloc := locus_of_shell_equations hfw (mu_neg_one_mul_self p μ₁) hβ
    (p_mul_tailAt_mul_tailAt p μ₁ μ₂ (-(m : ℤ) - 1)) E1 E4
  rw [locus_factorization] at hloc
  exact locus_ne_zero p hγp hγp' hloc

end Hext
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section Assembly

variable (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)

theorem isIrreducibleGLRep_of_isUnramified_of
    (hgen : ∀ W : Submodule ℂ (PSCarrier p μ₁ μ₂), IsStable p μ₁ μ₂ W →
      ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∈ W → W = ⊤)
    (hrec : ShellRec p μ₁ μ₂)
    (hγp : gammaRatio p μ₁ μ₂ ≠ (p : ℂ)) (hγp' : gammaRatio p μ₁ μ₂ ≠ ((p : ℂ))⁻¹) :
    LocalNewvector.IsIrreducibleGLRep p (PSCarrier p μ₁ μ₂) :=
  isIrreducibleGLRep_of_generation_of_extraction p μ₁ μ₂ h₁ h₂ hgen
    (fun W hW hno f hf hfw => hext_of_rec p μ₁ μ₂ h₁ h₂ hrec hγp hγp' W hW hno f hf hfw)

end Assembly
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end PSCarrier
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section Audit
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.p_mul_eq_gamma_mul_of_extraction
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.p_mul_tailAt_mul_tailAt
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.shell_equation
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.shell_equation_tail
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.locus_of_shell_equations
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.testV_shell
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.toFn_avgOp_testV_start
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.unrolled
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.hext_of_rec
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.isIrreducibleGLRep_of_isUnramified_of
end Audit
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end DeskModule13
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section DeskModule14

set_option autoImplicit false

noncomputable section

open Matrix FLT.EKAverage

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"
open LocalNewvector

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

section PhiInvariance

theorem weyl_mul_lowerUnip_mul_weyl (z : ℚ_[p]) :
    weyl p * lowerUnip p z * weyl p = borelElem p 1 1 z := by
  rw [← weyl_mul_borelElem_one_one_mul_weyl, ← mul_assoc, ← mul_assoc, weyl_mul_weyl, one_mul,
    mul_assoc, weyl_mul_weyl, mul_one]

theorem weyl_mul_lowerUnip' (z : ℚ_[p]) : weyl p * lowerUnip p z = borelElem p 1 1 z * weyl p := by
  rw [← weyl_mul_lowerUnip_mul_weyl p z, mul_assoc (weyl p * lowerUnip p z), weyl_mul_weyl, mul_one]

theorem phiFn_borelElem_mul_weyl (s : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    phiFn p μ₁ μ₂ s (borelElem p a₁ a₂ x * weyl p) = lawFactor p μ₁ μ₂ a₁ a₂ := by
  rw [phiFn_apply, mul_assoc, weyl_mul_weyl, bumpFn_borelElem_mul, bumpFn_one, mul_one]

theorem phiFn_borelElem_mul_lowerUnip_of_norm_lt (s : ℤ) (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) {y : ℚ_[p]}
    (hy : ‖y‖ < (p : ℝ) ^ (-s)) : phiFn p μ₁ μ₂ s (borelElem p a₁ a₂ x * lowerUnip p y) = 0 := by
  by_cases hy0 : y = 0
  · rw [hy0, lowerUnip_zero, mul_one, phiFn_borelElem]
  · rw [phiFn_borelElem_mul_lowerUnip p μ₁ μ₂ s a₁ a₂ x y hy0, if_neg (not_le.mpr hy)]

theorem phiFn_lowerUnip_of_norm_lt (s : ℤ) {y : ℚ_[p]} (hy : ‖y‖ < (p : ℝ) ^ (-s)) :
    phiFn p μ₁ μ₂ s (lowerUnip p y) = 0 := by
  have h := phiFn_borelElem_mul_lowerUnip_of_norm_lt p μ₁ μ₂ s 1 1 0 hy
  rwa [borelElem_one, one_mul] at h

theorem phiFn_mul_lowerUnip (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂) (s : ℤ) {z : ℚ_[p]}
    (hz : ‖z‖ ≤ (p : ℝ) ^ (-(s + 1))) (g : GL (Fin 2) ℚ_[p]) :
    phiFn p μ₁ μ₂ s (g * lowerUnip p z) = phiFn p μ₁ μ₂ s g := by
  have hp1 := one_lt_p_real p
  have hzlt : ‖z‖ < (p : ℝ) ^ (-s) := lt_of_le_of_lt hz (zpow_lt_zpow_right₀ hp1 (by omega))
  rcases cell_cases p g with ⟨a₁, a₂, x, y, rfl⟩ | ⟨a₁, a₂, x, rfl⟩
  · rw [mul_assoc, ← lowerUnip_add]
    by_cases hy : (p : ℝ) ^ (-s) ≤ ‖y‖
    · have hzy : ‖z‖ < ‖y‖ := lt_of_lt_of_le hzlt hy
      have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) hzy)
      have hsum : ‖y + z‖ = ‖y‖ := P6B.norm_add_eq_of_norm_lt p hzy
      have hyz0 : y + z ≠ 0 := norm_pos_iff.mp (by rw [hsum]; exact norm_pos_iff.mpr hy0)
      have hn : ‖((Units.mk0 (y + z) hyz0 : ℚ_[p]ˣ) : ℚ_[p])‖ = ‖((Units.mk0 y hy0 : ℚ_[p]ˣ) : ℚ_[p])‖ := by
        rw [Units.val_mk0, Units.val_mk0, hsum]
      rw [phiFn_borelElem_mul_lowerUnip p μ₁ μ₂ s a₁ a₂ x (y + z) hyz0,
        if_pos (by rw [hsum]; exact hy), phiFn_borelElem_mul_lowerUnip p μ₁ μ₂ s a₁ a₂ x y hy0,
        if_pos hy, tailChar_eq_of_norm_eq p μ₁ μ₂ h₁ h₂ hn]
    · rw [not_le] at hy
      have hyz : ‖y + z‖ < (p : ℝ) ^ (-s) :=
        lt_of_le_of_lt (Padic.nonarchimedean y z) (max_lt hy hzlt)
      rw [phiFn_borelElem_mul_lowerUnip_of_norm_lt p μ₁ μ₂ s a₁ a₂ x hyz,
        phiFn_borelElem_mul_lowerUnip_of_norm_lt p μ₁ μ₂ s a₁ a₂ x hy]
  · rw [mul_assoc, weyl_mul_lowerUnip', ← mul_assoc, borelElem_mul, phiFn_borelElem_mul_weyl,
      phiFn_borelElem_mul_weyl, mul_one, mul_one]

end PhiInvariance
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

namespace PSCarrier
open LocalNewvector.PSCarrier

variable (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)

theorem lowerUnip_smul_phiV (s : ℤ) {z : ℚ_[p]} (hz : ‖z‖ ≤ (p : ℝ) ^ (-(s + 1))) :
    lowerUnip p z • phiV p μ₁ μ₂ h₁ h₂ s = phiV p μ₁ μ₂ h₁ h₂ s :=
  ext p μ₁ μ₂ fun x => by rw [toFn_smul, toFn_phiV, phiFn_mul_lowerUnip p μ₁ μ₂ h₁ h₂ s hz]

def combo (a : ℤ) (X Y : ℂ) : PSCarrier p μ₁ μ₂ :=
  X • bumpV p μ₁ μ₂ h₁ h₂ a + Y • phiV p μ₁ μ₂ h₁ h₂ (a - 1)

theorem combo_def (a : ℤ) (X Y : ℂ) :
    combo p μ₁ μ₂ h₁ h₂ a X Y = X • bumpV p μ₁ μ₂ h₁ h₂ a + Y • phiV p μ₁ μ₂ h₁ h₂ (a - 1) := rfl

theorem toFn_combo (a : ℤ) (X Y : ℂ) (x : GL (Fin 2) ℚ_[p]) :
    toFn p μ₁ μ₂ (combo p μ₁ μ₂ h₁ h₂ a X Y) x = X * bumpFn p μ₁ μ₂ a x + Y * phiFn p μ₁ μ₂ (a - 1) x :=
  rfl

theorem toFn_combo_one' (a : ℤ) (X Y : ℂ) : toFn p μ₁ μ₂ (combo p μ₁ μ₂ h₁ h₂ a X Y) 1 = X :=
  toFn_combo_one p μ₁ μ₂ h₁ h₂ X Y a (a - 1)

theorem toFn_combo_weyl' (a : ℤ) (X Y : ℂ) : toFn p μ₁ μ₂ (combo p μ₁ μ₂ h₁ h₂ a X Y) (weyl p) = Y :=
  toFn_combo_weyl p μ₁ μ₂ h₁ h₂ X Y a (a - 1)

theorem toFn_combo_lowerUnip_shell (a : ℤ) (X Y : ℂ) {y : ℚ_[p]} (hy0 : y ≠ 0)
    (hy : ‖y‖ = (p : ℝ) ^ (1 - a)) :
    toFn p μ₁ μ₂ (combo p μ₁ μ₂ h₁ h₂ a X Y) (lowerUnip p y)
      = Y * ((μ₁ (-1) : ℂ) * tailAt p μ₁ μ₂ (a - 1)) := by
  have hp1 := one_lt_p_real p
  have hnot : ¬ ‖y‖ ≤ (p : ℝ) ^ (-a) := by
    rw [hy, not_le]; exact zpow_lt_zpow_right₀ hp1 (by omega)
  have hle : (p : ℝ) ^ (-(a - 1)) ≤ ‖y‖ := by rw [hy, neg_sub]
  rw [toFn_combo, bumpFn_lowerUnip, if_neg hnot, mul_zero, zero_add,
    P6B.phiFn_lowerUnip p μ₁ μ₂ (a - 1) hy0, if_pos hle, tailChar_eq_tailAt p μ₁ μ₂ h₁ h₂ hy0 hy]

theorem lowerUnip_smul_combo (a : ℤ) (X Y : ℂ) {z : ℚ_[p]} (hz : ‖z‖ ≤ (p : ℝ) ^ (-a)) :
    lowerUnip p z • combo p μ₁ μ₂ h₁ h₂ a X Y = combo p μ₁ μ₂ h₁ h₂ a X Y := by
  rw [combo_def, smul_add, smul_comm (lowerUnip p z) X (bumpV p μ₁ μ₂ h₁ h₂ a),
    smul_comm (lowerUnip p z) Y (phiV p μ₁ μ₂ h₁ h₂ (a - 1)),
    (lowerUnip_smul_bumpV_eq_self_iff p μ₁ μ₂ h₁ h₂ a z).mpr hz,
    lowerUnip_smul_phiV p μ₁ μ₂ h₁ h₂ (a - 1) (by rwa [sub_add_cancel])]

theorem lowerUnipSubgroup_le_stabilizer_combo (a : ℤ) (X Y : ℂ) :
    lowerUnipSubgroup p a ≤ MulAction.stabilizer (GL (Fin 2) ℚ_[p]) (combo p μ₁ μ₂ h₁ h₂ a X Y) := by
  rintro _ ⟨z, hz, rfl⟩
  exact lowerUnip_smul_combo p μ₁ μ₂ h₁ h₂ a X Y hz

def transQ (a : ℤ) (X Y : ℂ) :
    ↥(lowerUnipSubgroup p (a - 1)) ⧸ (lowerUnipSubgroup p a).subgroupOf (lowerUnipSubgroup p (a - 1))
      → PSCarrier p μ₁ μ₂ :=
  Quotient.lift
    (fun k : ↥(lowerUnipSubgroup p (a - 1)) => (k : GL (Fin 2) ℚ_[p]) • combo p μ₁ μ₂ h₁ h₂ a X Y)
    (by
      intro k k' hkk'
      have hmem : ((k : GL (Fin 2) ℚ_[p])⁻¹ * (k' : GL (Fin 2) ℚ_[p])) ∈ lowerUnipSubgroup p a := by
        have h := QuotientGroup.leftRel_apply.mp hkk'
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h
        exact h
      have hfix := lowerUnipSubgroup_le_stabilizer_combo p μ₁ μ₂ h₁ h₂ a X Y hmem
      rw [MulAction.mem_stabilizer_iff, mul_smul] at hfix
      have h2 := congrArg (fun v => (k : GL (Fin 2) ℚ_[p]) • v) hfix
      simp only [smul_inv_smul] at h2
      exact h2.symm)

theorem transQ_mk (a : ℤ) (X Y : ℂ) (k : ↥(lowerUnipSubgroup p (a - 1))) :
    transQ p μ₁ μ₂ h₁ h₂ a X Y (QuotientGroup.mk k)
      = (k : GL (Fin 2) ℚ_[p]) • combo p μ₁ μ₂ h₁ h₂ a X Y := rfl

theorem avgOp_combo_eq_sum (a : ℤ) (X Y : ℂ) :
    P6B.avgOp p μ₁ μ₂ (a - 1) (combo p μ₁ μ₂ h₁ h₂ a X Y)
      = (p : ℂ)⁻¹ • ∑ᶠ x, transQ p μ₁ μ₂ h₁ h₂ a X Y x := by
  have h := ekAverage_eq_average_of_subgroupOf_le_stabilizer (F := ℂ)
    (K := lowerUnipSubgroup p (a - 1))
    (lowerUnipSubgroup_le_stabilizer_combo p μ₁ μ₂ h₁ h₂ a X Y)
    (ψ := transQ p μ₁ μ₂ h₁ h₂ a X Y) (fun k => rfl)
  rw [P6B.avgOp, h, card_quotient_lowerUnipSubgroup]

theorem p_mul_toFn_avgOp_combo_one (a : ℤ) (X Y : ℂ) :
    (p : ℂ) * toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (a - 1) (combo p μ₁ μ₂ h₁ h₂ a X Y)) 1
      = X + ((p : ℂ) - 1) * (Y * ((μ₁ (-1) : ℂ) * tailAt p μ₁ μ₂ (a - 1))) := by
  classical
  set Q := ↥(lowerUnipSubgroup p (a - 1)) ⧸
    (lowerUnipSubgroup p a).subgroupOf (lowerUnipSubgroup p (a - 1)) with hQ
  haveI : Fintype Q := Fintype.ofFinite Q
  have hp0 := natCast_p_ne_zero p
  have hpr : p.Prime := Fact.out
  rw [avgOp_combo_eq_sum, finsum_eq_sum_of_fintype, toFn_csmul, ← mul_assoc, mul_inv_cancel₀ hp0,
    one_mul]
  have hsum := map_sum (P6B.evalLin p μ₁ μ₂ (1 : GL (Fin 2) ℚ_[p])) (transQ p μ₁ μ₂ h₁ h₂ a X Y)
    Finset.univ
  simp only [P6B.evalLin_apply] at hsum
  rw [hsum]
  set x₀ : Q := QuotientGroup.mk 1 with hx₀
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ x₀)]
  have h0 : toFn p μ₁ μ₂ (transQ p μ₁ μ₂ h₁ h₂ a X Y x₀) 1 = X := by
    rw [hx₀, transQ_mk, Subgroup.coe_one, one_smul, toFn_combo_one']
  have hrest : ∀ x ∈ Finset.univ.erase x₀,
      toFn p μ₁ μ₂ (transQ p μ₁ μ₂ h₁ h₂ a X Y x) 1 = Y * ((μ₁ (-1) : ℂ) * tailAt p μ₁ μ₂ (a - 1)) := by
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have hne : (QuotientGroup.mk k : Q) ≠ x₀ := Finset.ne_of_mem_erase hx
    have hk' : (k : GL (Fin 2) ℚ_[p]) ∉ lowerUnipSubgroup p a :=
      fun h => hne ((mk_eq_one_iff p k).mpr h)
    obtain ⟨y, hy, hky⟩ := exists_eq_lowerUnip_of_mem_of_notMem p k.property hk'
    have hy0 : y ≠ 0 := by
      intro h; rw [h, norm_zero] at hy
      exact (ne_of_gt (zpow_pos (lt_trans zero_lt_one (one_lt_p_real p)) _)) hy.symm
    rw [transQ_mk, toFn_smul, one_mul, ← hky, toFn_combo_lowerUnip_shell p μ₁ μ₂ h₁ h₂ a X Y hy0 hy]
  rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ← Nat.card_eq_fintype_card, card_quotient_lowerUnipSubgroup, h0, nsmul_eq_mul,
    Nat.cast_sub hpr.one_lt.le, Nat.cast_one]

theorem avgOp_combo_eq (a : ℤ) (X Y : ℂ) :
    P6B.avgOp p μ₁ μ₂ (a - 1) (combo p μ₁ μ₂ h₁ h₂ a X Y)
      = combo p μ₁ μ₂ h₁ h₂ (a - 1)
          (toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (a - 1) (combo p μ₁ μ₂ h₁ h₂ a X Y)) 1) Y := by
  have hp1 := one_lt_p_real p
  have hfin := forall_finite_quotient_stabilizer_lowerUnipSubgroup p (a - 1) (combo p μ₁ μ₂ h₁ h₂ a X Y)
  refine ext_cells p μ₁ μ₂ (fun y => ?_) ?_
  · by_cases hy : ‖y‖ ≤ (p : ℝ) ^ (-(a - 1))
    ·
      have hlt : ‖y‖ < (p : ℝ) ^ (-(a - 1 - 1)) :=
        lt_of_le_of_lt hy (zpow_lt_zpow_right₀ hp1 (by omega))
      rw [P6B.toFn_avgOp_lowerUnip p μ₁ μ₂ (a - 1) _ hfin hy, toFn_combo, bumpFn_lowerUnip, if_pos hy,
        mul_one, phiFn_lowerUnip_of_norm_lt p μ₁ μ₂ (a - 1 - 1) hlt, mul_zero, add_zero]
    ·
      rw [not_le] at hy
      have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_trans (zpow_pos (lt_trans zero_lt_one hp1) _) hy)
      have hc : ∀ k : ↥(lowerUnipSubgroup p (a - 1)),
          toFn p μ₁ μ₂ (combo p μ₁ μ₂ h₁ h₂ a X Y) (lowerUnip p y * (k : GL (Fin 2) ℚ_[p]))
            = Y * ((μ₁ (-1) : ℂ) * tailChar p μ₁ μ₂ (Units.mk0 y hy0)) := by
        intro k
        obtain ⟨y', hy', hk⟩ := k.property
        have hlt' : ‖y'‖ < ‖y‖ := lt_of_le_of_lt hy' hy
        have hsum : ‖y + y'‖ = ‖y‖ := P6B.norm_add_eq_of_norm_lt p hlt'
        have hyy0 : y + y' ≠ 0 := norm_pos_iff.mp (by rw [hsum]; exact norm_pos_iff.mpr hy0)
        have hnot : ¬ ‖y + y'‖ ≤ (p : ℝ) ^ (-a) := by
          rw [hsum, not_le]; exact lt_trans (zpow_lt_zpow_right₀ hp1 (by omega)) hy
        have hle : (p : ℝ) ^ (-(a - 1)) ≤ ‖y + y'‖ := by rw [hsum]; exact hy.le
        have hn : ‖((Units.mk0 (y + y') hyy0 : ℚ_[p]ˣ) : ℚ_[p])‖ = ‖((Units.mk0 y hy0 : ℚ_[p]ˣ) : ℚ_[p])‖ := by
          rw [Units.val_mk0, Units.val_mk0, hsum]
        rw [← hk, ← lowerUnip_add, toFn_combo, bumpFn_lowerUnip, if_neg hnot, mul_zero, zero_add,
          P6B.phiFn_lowerUnip p μ₁ μ₂ (a - 1) hyy0, if_pos hle, tailChar_eq_of_norm_eq p μ₁ μ₂ h₁ h₂ hn]
      have hnot1 : ¬ ‖y‖ ≤ (p : ℝ) ^ (-(a - 1)) := not_le.mpr hy
      have hle2 : (p : ℝ) ^ (-(a - 1 - 1)) ≤ ‖y‖ := by
        have h := P6B.zpow_succ_le_norm_of_lt p hy0 hy
        rwa [show -(a - 1) + 1 = -(a - 1 - 1) by ring] at h
      rw [P6B.toFn_avgOp_eq_of_const p μ₁ μ₂ (a - 1) _ hfin hc, toFn_combo, bumpFn_lowerUnip,
        if_neg hnot1, mul_zero, zero_add, P6B.phiFn_lowerUnip p μ₁ μ₂ (a - 1 - 1) hy0, if_pos hle2]
  ·
    have hc : ∀ k : ↥(lowerUnipSubgroup p (a - 1)),
        toFn p μ₁ μ₂ (combo p μ₁ μ₂ h₁ h₂ a X Y) (weyl p * (k : GL (Fin 2) ℚ_[p])) = Y := by
      intro k
      obtain ⟨y', -, hk⟩ := k.property
      rw [← hk, P6B.weyl_summand p μ₁ μ₂ (toFn_mem p μ₁ μ₂ _) y', toFn_combo_weyl']
    rw [P6B.toFn_avgOp_eq_of_const p μ₁ μ₂ (a - 1) _ hfin hc, toFn_combo_weyl']

section Master

variable {W : Submodule ℂ (PSCarrier p μ₁ μ₂)}

theorem combo_relation (hW : IsStable p μ₁ μ₂ W) (hno : ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∉ W)
    {a : ℤ} {X Y : ℂ} (hv : combo p μ₁ μ₂ h₁ h₂ a X Y ∈ W) :
    (gammaRatio p μ₁ μ₂ - 1) * X = ((p : ℂ) - 1) * (Y * ((μ₁ (-1) : ℂ) * tailAt p μ₁ μ₂ (a - 1))) := by
  have hu : P6B.avgOp p μ₁ μ₂ (a - 1) (combo p μ₁ μ₂ h₁ h₂ a X Y) ∈ W :=
    ekAverage_mem_of_invariant p (lowerUnipSubgroup p (a - 1)) W hW hv
      (forall_finite_quotient_stabilizer_lowerUnipSubgroup p (a - 1) _)
  have hu_eq := avgOp_combo_eq p μ₁ μ₂ h₁ h₂ a X Y
  rw [combo_def p μ₁ μ₂ h₁ h₂ (a - 1)] at hu_eq
  have hD := extraction_coeff_eq_zero p μ₁ μ₂ h₁ h₂ hW hno hu hv (j := a) (b := X) (c := Y)
    hu_eq (combo_def p μ₁ μ₂ h₁ h₂ a X Y)
  have hE := p_mul_eq_gamma_mul_of_extraction p μ₁ μ₂ hD
  have hS := p_mul_toFn_avgOp_combo_one p μ₁ μ₂ h₁ h₂ a X Y
  linear_combination hS - hE

theorem E1 (hW : IsStable p μ₁ μ₂ W) (hno : ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∉ W)
    {f : PSCarrier p μ₁ μ₂} (hf : f ∈ W) {m : ℕ}
    (hm : ∀ (x : GL (Fin 2) ℚ_[p]) (z : ℚ_[p]), ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ)) →
      toFn p μ₁ μ₂ f (x * borelElem p 1 1 z) = toFn p μ₁ μ₂ f x)
    {j : ℤ} (hj : j ≤ -(m : ℤ)) :
    (gammaRatio p μ₁ μ₂ - 1) * toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ j f) 1
      = ((p : ℂ) - 1) * (toFn p μ₁ μ₂ f (weyl p) * ((μ₁ (-1) : ℂ) * tailAt p μ₁ μ₂ (j - 1))) := by
  have hv : P6B.avgOp p μ₁ μ₂ j f ∈ W :=
    ekAverage_mem_of_invariant p (lowerUnipSubgroup p j) W hW hf
      (forall_finite_quotient_stabilizer_lowerUnipSubgroup p j f)
  have hv_eq := P6B.avgOp_eq_smul_psiM_add_smul_phiM p μ₁ μ₂ h₁ h₂ f hm hj
  have hv' : combo p μ₁ μ₂ h₁ h₂ j (toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ j f) 1)
      (toFn p μ₁ μ₂ f (weyl p)) ∈ W := by
    rw [combo_def, ← hv_eq]; exact hv
  exact combo_relation p μ₁ μ₂ h₁ h₂ hW hno hv'

theorem hext (hγp : gammaRatio p μ₁ μ₂ ≠ (p : ℂ)) (hγp' : gammaRatio p μ₁ μ₂ ≠ ((p : ℂ))⁻¹)
    (W : Submodule ℂ (PSCarrier p μ₁ μ₂)) (hW : IsStable p μ₁ μ₂ W)
    (hno : ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∉ W)
    (f : PSCarrier p μ₁ μ₂) (hf : f ∈ W) (hfw : toFn p μ₁ μ₂ f (weyl p) ≠ 0) : False := by
  obtain ⟨m, hm⟩ := P6B.exists_right_unipotent_level p μ₁ μ₂ f
  have hjm : -(m : ℤ) ≤ -(m : ℤ) := le_rfl

  have hE1 := E1 p μ₁ μ₂ h₁ h₂ hW hno hf hm hjm

  have hv : P6B.avgOp p μ₁ μ₂ (-(m : ℤ)) f ∈ W :=
    ekAverage_mem_of_invariant p (lowerUnipSubgroup p (-(m : ℤ))) W hW hf
      (forall_finite_quotient_stabilizer_lowerUnipSubgroup p (-(m : ℤ)) f)
  have hv_eq := P6B.avgOp_eq_smul_psiM_add_smul_phiM p μ₁ μ₂ h₁ h₂ f hm hjm
  have hg := weyl_testVector_mem p μ₁ μ₂ h₁ h₂ hW hfw hv hv_eq

  have hg' : combo p μ₁ μ₂ h₁ h₂ (1 - -(m : ℤ)) 1
      (toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (-(m : ℤ)) f) 1 * (toFn p μ₁ μ₂ f (weyl p))⁻¹) ∈ W := by
    rw [combo_def, one_smul, add_comm, show (1 : ℤ) - -(m : ℤ) - 1 = -(-(m : ℤ)) by ring]
    exact hg
  have hE4 := combo_relation p μ₁ μ₂ h₁ h₂ hW hno hg'
  rw [show (1 : ℤ) - -(m : ℤ) - 1 = -(-(m : ℤ)) by ring] at hE4

  have hβ : toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (-(m : ℤ)) f) 1 * (toFn p μ₁ μ₂ f (weyl p))⁻¹
      * toFn p μ₁ μ₂ f (weyl p) = toFn p μ₁ μ₂ (P6B.avgOp p μ₁ μ₂ (-(m : ℤ)) f) 1 :=
    inv_mul_cancel_right₀ hfw _
  have hloc := locus_of_shell_equations hfw (mu_neg_one_mul_self p μ₁) hβ
    (p_mul_tailAt_mul_tailAt p μ₁ μ₂ (-(m : ℤ))) (by linear_combination hE1)
    (by linear_combination hE4)
  rw [locus_factorization] at hloc
  exact locus_ne_zero p hγp hγp' hloc

end Master
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

theorem isIrreducibleGLRep_of_isUnramified_of_generation
    (hgen : ∀ W : Submodule ℂ (PSCarrier p μ₁ μ₂), IsStable p μ₁ μ₂ W →
      ∀ k : ℤ, bumpV p μ₁ μ₂ h₁ h₂ k ∈ W → W = ⊤)
    (hγp : gammaRatio p μ₁ μ₂ ≠ (p : ℂ)) (hγp' : gammaRatio p μ₁ μ₂ ≠ ((p : ℂ))⁻¹) :
    LocalNewvector.IsIrreducibleGLRep p (PSCarrier p μ₁ μ₂) :=
  isIrreducibleGLRep_of_generation_of_extraction p μ₁ μ₂ h₁ h₂ hgen
    (fun W hW hno f hf hfw => hext p μ₁ μ₂ h₁ h₂ hγp hγp' W hW hno f hf hfw)

end PSCarrier
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section Audit
#print axioms FLT.PrincipalSeriesGL2Padic.phiFn_mul_lowerUnip
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.lowerUnip_smul_combo
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.avgOp_combo_eq_sum
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.p_mul_toFn_avgOp_combo_one
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.avgOp_combo_eq
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.combo_relation
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.E1
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.hext
#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.isIrreducibleGLRep_of_isUnramified_of_generation
end Audit
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end DeskModule14
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

section DeskModule15

set_option autoImplicit false

noncomputable section

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"
open LocalNewvector

namespace PSCarrier
open LocalNewvector.PSCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

theorem isIrreducibleGLRep_of_isUnramified (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)
    (hγp : gammaRatio p μ₁ μ₂ ≠ (p : ℂ)) (hγp' : gammaRatio p μ₁ μ₂ ≠ ((p : ℂ))⁻¹) :
    LocalNewvector.IsIrreducibleGLRep p (PSCarrier p μ₁ μ₂) :=
  isIrreducibleGLRep_of_isUnramified_of_generation p μ₁ μ₂ h₁ h₂ (P6B.generation p μ₁ μ₂ h₁ h₂)
    hγp hγp'

end PSCarrier
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.isIrreducibleGLRep_of_isUnramified

end
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

end DeskModule15
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

namespace FLT
p2m_export "FLT" "SmoothVectors.gl2CongruenceSubgroup SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one SpectralSide.mem_integralSubgroup_iff_entries_mem SpectralSide.isOpen_coe_integralSubgroup_padic SpectralSide.isCompact_coe_integralSubgroup_padic"
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"

theorem PSCarrier.isIrreducibleGLRep_of_isUnramified_impl (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)
    (h₁ : LocalNewvector.IsUnramified p μ₁) (h₂ : LocalNewvector.IsUnramified p μ₂)
    (hγp : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ ≠ (p : ℂ))
    (hγp' : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ ≠ ((p : ℂ))⁻¹) :
    LocalNewvector.IsIrreducibleGLRep p (LocalNewvector.PSCarrier p μ₁ μ₂) :=
  FLT.PrincipalSeriesGL2Padic.PSCarrier.isIrreducibleGLRep_of_isUnramified p μ₁ μ₂ h₁ h₂ hγp hγp'

end FLT.PrincipalSeriesGL2Padic
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"
p2m_reactivate "P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.LocalGL2 P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.PrincipalSeriesGL2Padic.PSCarrier P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.FLT.EKAverage P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.P6B"

#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.isIrreducibleGLRep_of_isUnramified_impl

theorem solution (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)
    (h₁ : LocalNewvector.IsUnramified p μ₁) (h₂ : LocalNewvector.IsUnramified p μ₂)
    (hγp : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ ≠ (p : ℂ))
    (hγp' : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ ≠ ((p : ℂ))⁻¹) :
    LocalNewvector.IsIrreducibleGLRep p (LocalNewvector.PSCarrier p μ₁ μ₂) := by
  apply FLT.PrincipalSeriesGL2Padic.PSCarrier.isIrreducibleGLRep_of_isUnramified_impl <;> assumption

end S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified
end P2MW
export P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified (solution)
