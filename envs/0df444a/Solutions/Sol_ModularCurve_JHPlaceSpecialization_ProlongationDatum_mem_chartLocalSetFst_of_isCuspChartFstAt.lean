-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_chartLocalSetFst_of_isCuspChartFstAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ab20a2cd-1651-56aa-8acf-2339b72dd4ad

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHChartSemicontinuity
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_finrankAlong_id
import Theorems.Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
import Theorems.Thm_ModularCurve_finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

section
open AlgebraicCurve Polynomial

namespace Ws49
namespace SplitEngine

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
  [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
variable (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)

section Coordinates

variable {E : IntermediateField L F} (hE₂ : ∀ e ∈ E, e ∈ R₁.integers → e ∈ R₂.integers)
  (σ : Fb₁ →+* Fb₂)
  (hσ : ∀ e (he : e ∈ E) (h₁ : e ∈ R₁.integers), R₂.residue ⟨e, hE₂ e he h₁⟩ = σ (R₁.residue ⟨e, h₁⟩))
  {q : ℕ} (hq : q.Prime) [CharP Fb₂ q] (hpi : ∀ y : Fb₂, y ^ q ∈ σ.range)
  {z : F} (hz₁ : z ∈ R₁.integers) (hz₂ : z ∈ R₂.integers)
  (hzr₂ : R₂.residue ⟨z, hz₂⟩ ∉ σ.range)

include hσ hq hpi hz₁ hzr₂ in

private theorem residue_coeff_eq_zero_of_residues_eq_zero (γ : Fin (q + 1) → F) (hγE : ∀ i, γ i ∈ E)
    (hγ₁ : ∀ i, γ i ∈ R₁.integers) {θ : F} (hθ : θ = ∑ i, γ i * z ^ (i : ℕ))
    (hθ₁ : θ ∈ R₁.integers) (hθ₂ : θ ∈ R₂.integers)
    (h₁ : R₁.residue ⟨θ, hθ₁⟩ = 0) (h₂ : R₂.residue ⟨θ, hθ₂⟩ = 0) :
    ∀ i, R₁.residue ⟨γ i, hγ₁ i⟩ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq.pos).symm⟩

  obtain ⟨η, hη⟩ := RingHom.mem_range.mp (hpi (R₂.residue ⟨z, hz₂⟩))
  haveI : Fact (m + 1).Prime := ⟨hq⟩
  have hfrob : ∀ a b : Fb₂, a ^ (m + 1) = b ^ (m + 1) → a = b := by
    intro a b hab
    have h : (a - b) ^ (m + 1) = a ^ (m + 1) - b ^ (m + 1) := by rw [sub_pow_char]
    rw [hab, sub_self] at h
    exact sub_eq_zero.mp (pow_eq_zero_iff (Nat.succ_ne_zero m) |>.mp h)
  have hηq : ∀ b : Fb₁, b ^ (m + 1) ≠ η := by
    intro b hb
    apply hzr₂
    refine RingHom.mem_range.mpr ⟨b, hfrob _ _ ?_⟩
    rw [← map_pow, hb, hη]
  have hζ : R₁.residue ⟨z, hz₁⟩ ^ (m + 1) ≠ η := by
    intro hc
    apply hzr₂
    refine RingHom.mem_range.mpr ⟨R₁.residue ⟨z, hz₁⟩, hfrob _ _ ?_⟩
    rw [← map_pow, hc, hη]
  set xb := η with hxb
  set ζ := R₁.residue ⟨z, hz₁⟩ with hζdef
  set ξ := R₂.residue ⟨z, hz₂⟩ with hξ
  set δ : Fin (m + 1 + 1) → Fb₁ := fun i => R₁.residue ⟨γ i, hγ₁ i⟩ with hδ

  have hI : ∑ i, δ i * ζ ^ (i : ℕ) = 0 := by
    have hsub : (⟨θ, hθ₁⟩ : R₁.integers) = ∑ i : Fin (m + 1 + 1), ⟨γ i, hγ₁ i⟩ * ⟨z, hz₁⟩ ^ (i : ℕ) := by
      apply Subtype.ext
      push_cast
      exact hθ
    rw [hsub, map_sum] at h₁
    simpa only [map_mul, map_pow] using h₁
  have hII : ∑ i, σ (δ i) * ξ ^ (i : ℕ) = 0 := by
    have hsub : (⟨θ, hθ₂⟩ : R₂.integers)
        = ∑ i : Fin (m + 1 + 1), ⟨γ i, hE₂ (γ i) (hγE i) (hγ₁ i)⟩ * ⟨z, hz₂⟩ ^ (i : ℕ) := by
      apply Subtype.ext
      push_cast
      exact hθ
    rw [hsub, map_sum] at h₂
    simp only [map_mul, map_pow] at h₂
    rw [← h₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hσ (γ i) (hγE i) (hγ₁ i), hδ, hξ]

  letI : Algebra Fb₁ Fb₂ := σ.toAlgebra
  have hmin : minpoly Fb₁ ξ = X ^ (m + 1) - C xb := by
    refine (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hq hηq) ?_
      (monic_X_pow_sub_C xb (Nat.succ_ne_zero m))).symm
    simp [RingHom.algebraMap_toAlgebra, hη]
  have hli : LinearIndependent Fb₁ fun i : Fin (m + 1) => ξ ^ (i : ℕ) := by
    have h := linearIndependent_pow (K := Fb₁) ξ
    rwa [hmin, natDegree_X_pow_sub_C] at h

  set g : Fin (m + 1) → Fb₁ :=
    fun i => δ (Fin.castSucc i) + if i = 0 then δ (Fin.last _) * xb else 0 with hg
  have hg0 : ∀ i, g i = 0 := by
    refine Fintype.linearIndependent_iff.mp hli g ?_
    simp only [hg, Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_add, add_mul, Finset.sum_add_distrib]
    rw [Fin.sum_univ_castSucc] at hII
    have hlast : σ (δ (Fin.last (m + 1))) * ξ ^ ((Fin.last (m + 1) : ℕ)) = σ (δ (Fin.last _) * xb) := by
      rw [Fin.val_last, ← hη, map_mul]
    rw [hlast] at hII
    convert hII using 2
    all_goals first
      | rfl
      | (rw [Finset.sum_eq_single (0 : Fin (m + 1)) (fun b _ hb => by simp [hb])
          (fun h => absurd (Finset.mem_univ _) h)]; simp)
      | simp [Fin.coe_castSucc]
  have hmid : ∀ i : Fin (m + 1), i ≠ 0 → δ (Fin.castSucc i) = 0 := by
    intro i hi
    simpa [hg, hi] using hg0 i
  have h0 : δ 0 = -(δ (Fin.last _) * xb) := by
    have h := hg0 0
    simp only [hg, if_true, Fin.castSucc_zero] at h
    exact eq_neg_of_add_eq_zero_left h

  have hlastzero : δ (Fin.last _) = 0 := by
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_single (0 : Fin (m + 1))] at hI
    · simp only [Fin.castSucc_zero, Fin.val_zero, pow_zero, mul_one, Fin.val_last, h0] at hI
      have hI' : δ (Fin.last _) * (ζ ^ (m + 1) - xb) = 0 := by
        rw [mul_sub]
        linear_combination hI
      exact (mul_eq_zero.mp hI').resolve_right (sub_ne_zero.mpr hζ)
    · intro b _ hb
      rw [hmid b hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  intro i
  show δ i = 0
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · by_cases hj : j = 0
    · subst hj
      rw [Fin.castSucc_zero, h0, hlastzero, zero_mul, neg_zero]
    · exact hmid j hj
  · exact hlastzero

end Coordinates

section Gauss

variable {E : IntermediateField L F} (hE₂ : ∀ e ∈ E, e ∈ R₁.integers → e ∈ R₂.integers)
  (σ : Fb₁ →+* Fb₂)
  (hσ : ∀ e (he : e ∈ E) (h₁ : e ∈ R₁.integers), R₂.residue ⟨e, hE₂ e he h₁⟩ = σ (R₁.residue ⟨e, h₁⟩))
  {q : ℕ} (hq : q.Prime) [CharP Fb₂ q] (hpi : ∀ y : Fb₂, y ^ q ∈ σ.range)
  {z : F} (hz₁ : z ∈ R₁.integers) (hz₂ : z ∈ R₂.integers)
  (hzr₂ : R₂.residue ⟨z, hz₂⟩ ∉ σ.range)

private theorem const_smul_mem {c : L} (hc : c ∈ A) {f : F} (hf : f ∈ R₁.integers) :
    c • f ∈ R₁.integers := by
  rw [Algebra.smul_def]
  exact mul_mem ((R₁.algebraMap_mem_iff c).mpr hc) hf

include hσ hq hpi hz₁ hzr₂ in

private theorem coeff_mem_integers_of_mem_integers (γ : Fin (q + 1) → F) (hγE : ∀ i, γ i ∈ E) {h : F}
    (hh : h = ∑ i, γ i * z ^ (i : ℕ)) (hh₁ : h ∈ R₁.integers) (hh₂ : h ∈ R₂.integers) :
    ∀ i, γ i ∈ R₁.integers := by
  classical
  by_cases hzero : ∀ i, γ i = 0
  · intro i
    rw [hzero i]
    exact zero_mem _
  obtain ⟨i₁, hi₁⟩ := not_forall.mp hzero

  have hsc : ∀ i, ∃ c : L, ∃ hc : c • γ i ∈ R₁.integers, γ i ≠ 0 → R₁.residue ⟨c • γ i, hc⟩ ≠ 0 := by
    intro i
    by_cases hi : γ i = 0
    · exact ⟨1, by rw [hi, smul_zero]; exact zero_mem _, fun h => absurd hi h⟩
    · obtain ⟨c, hc, hres⟩ := R₁.exists_smul_mem (γ i) hi
      exact ⟨c, hc, fun _ => hres⟩
  choose cs hcs hcsres using hsc
  have hcs0 : ∀ i, γ i ≠ 0 → cs i ≠ 0 := fun i hi => R₁.smul_const_ne_zero (hcs i) (hcsres i hi)

  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i => γ i ≠ 0)
    (fun i => A.valuation (cs i)) ⟨i₁, by simpa using hi₁⟩
  have hγi₀ : γ i₀ ≠ 0 := by simpa using hi₀
  set c := cs i₀ with hc
  have hc0 : c ≠ 0 := hcs0 i₀ hγi₀

  have hcγ : ∀ i, c • γ i ∈ R₁.integers := by
    intro i
    by_cases hi : γ i = 0
    · rw [hi, smul_zero]; exact zero_mem _
    have hdiv : c / cs i ∈ A := by
      rw [← A.valuation_le_one_iff, map_div₀,
        div_le_one₀ (by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr (hcs0 i hi))]
      exact hmin i (by simpa using hi)
    have : c • γ i = (c / cs i) • (cs i • γ i) := by
      rw [smul_smul, div_mul_cancel₀ _ (hcs0 i hi)]
    rw [this]
    exact const_smul_mem R₁ hdiv (hcs i)
  rcases A.mem_or_inv_mem c with hcA | hcinv
  swap
  ·
    intro i
    have : γ i = c⁻¹ • (c • γ i) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact const_smul_mem R₁ hcinv (hcγ i)

  by_cases hunit : c⁻¹ ∈ A
  · intro i
    have : γ i = c⁻¹ • (c • γ i) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact const_smul_mem R₁ hunit (hcγ i)
  exfalso
  have hcmax : (⟨c, hcA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hunit
    have hmul : ((u⁻¹ : Aˣ) : A) * ⟨c, hcA⟩ = 1 := by rw [← hu, Units.inv_mul]
    have hmul' : ((u⁻¹ : Aˣ) : L) * c = 1 := by
      have h := congrArg (fun a : A => (a : L)) hmul
      simpa using h
    rw [← eq_inv_of_mul_eq_one_left hmul']
    exact ((u⁻¹ : Aˣ) : A).2
  have hcres : IsLocalRing.residue A ⟨c, hcA⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hcmax

  set θ := c • h with hθdef
  have hθ : θ = ∑ i, (c • γ i) * z ^ (i : ℕ) := by
    rw [hθdef, hh, Finset.smul_sum]
    simp only [smul_mul_assoc]
  have hθ₁ : θ ∈ R₁.integers := const_smul_mem R₁ hcA hh₁
  have hθ₂ : θ ∈ R₂.integers := by
    rw [hθdef, Algebra.smul_def]
    exact mul_mem ((R₂.algebraMap_mem_iff c).mpr hcA) hh₂
  have hres₁ : R₁.residue ⟨θ, hθ₁⟩ = 0 := by
    have hsub : (⟨θ, hθ₁⟩ : R₁.integers)
        = ⟨algebraMap L F c, (R₁.algebraMap_mem_iff c).mpr hcA⟩ * ⟨h, hh₁⟩ := by
      apply Subtype.ext
      simp [hθdef, Algebra.smul_def]
    rw [hsub, map_mul, R₁.residue_algebraMap ⟨c, hcA⟩, hcres, map_zero, zero_mul]
  have hres₂ : R₂.residue ⟨θ, hθ₂⟩ = 0 := by
    have hsub : (⟨θ, hθ₂⟩ : R₂.integers)
        = ⟨algebraMap L F c, (R₂.algebraMap_mem_iff c).mpr hcA⟩ * ⟨h, hh₂⟩ := by
      apply Subtype.ext
      simp [hθdef, Algebra.smul_def]
    rw [hsub, map_mul, R₂.residue_algebraMap ⟨c, hcA⟩, hcres, map_zero, zero_mul]
  have hall := residue_coeff_eq_zero_of_residues_eq_zero R₁ R₂ hE₂ σ hσ hq hpi hz₁ hz₂ hzr₂
    (fun i => c • γ i) (fun i => E.smul_mem (hγE i)) hcγ hθ hθ₁ hθ₂ hres₁ hres₂ i₀
  exact hcsres i₀ hγi₀ hall

include hσ hq hpi hz₁ hzr₂ in

private theorem eq_zero_of_sum_mul_pow_eq_zero (γ : Fin (q + 1) → F) (hγE : ∀ i, γ i ∈ E)
    (hsum : ∑ i, γ i * z ^ (i : ℕ) = 0) : ∀ i, γ i = 0 := by
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
  set γ' : Fin (q + 1) → F := fun i => (γ i₀)⁻¹ * γ i with hγ'
  have hγ'E : ∀ i, γ' i ∈ E := fun i => E.mul_mem (E.inv_mem (hγE i₀)) (hγE i)
  have hsum' : (0 : F) = ∑ i, γ' i * z ^ (i : ℕ) := by
    simp only [hγ', mul_assoc, ← Finset.mul_sum, hsum, mul_zero]
  have hγ'₁ := coeff_mem_integers_of_mem_integers R₁ R₂ hE₂ σ hσ hq hpi hz₁ hz₂ hzr₂ γ' hγ'E hsum'
    (zero_mem _) (zero_mem _)
  have hres := residue_coeff_eq_zero_of_residues_eq_zero R₁ R₂ hE₂ σ hσ hq hpi hz₁ hz₂ hzr₂ γ' hγ'E hγ'₁
    hsum' (zero_mem _) (zero_mem _) (map_zero _) (map_zero _) i₀
  have h1 : γ' i₀ = 1 := inv_mul_cancel₀ hi₀
  have hone : (⟨γ' i₀, hγ'₁ i₀⟩ : R₁.integers) = 1 := Subtype.ext h1
  rw [hone, map_one] at hres
  exact one_ne_zero hres

end Gauss

end Ws49.SplitEngine

end

section
open AlgebraicCurve Polynomial

namespace Ws49
namespace SplitEngine

private theorem map_derivative_eval {S T : Type*} [CommRing S] [CommRing T] (ρ : S →+* T) (p : Polynomial S)
    (a : S) : ρ ((derivative p).eval a) = (derivative (p.map ρ)).eval (ρ a) := by
  rw [derivative_map, eval_map, eval₂_at_apply]

private theorem map_eval' {S T : Type*} [CommRing S] [CommRing T] (ρ : S →+* T) (p : Polynomial S) (a : S) :
    ρ (p.eval a) = (p.map ρ).eval (ρ a) := by
  rw [eval_map, eval₂_at_apply]

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
  [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
variable (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
variable {E : IntermediateField L F} (hE₂ : ∀ e ∈ E, e ∈ R₁.integers → e ∈ R₂.integers)
  (σ : Fb₁ →+* Fb₂)
  (hσ : ∀ e (he : e ∈ E) (h₁ : e ∈ R₁.integers), R₂.residue ⟨e, hE₂ e he h₁⟩ = σ (R₁.residue ⟨e, h₁⟩))
  {q : ℕ} (hq : q.Prime) [CharP Fb₂ q] (hpi : ∀ y : Fb₂, y ^ q ∈ σ.range)
  {z : F} (hz₂ : z ∈ R₂.integers) (hzr₂ : R₂.residue ⟨z, hz₂⟩ ∉ σ.range)

include hσ hq hpi hzr₂ in

private theorem core (P₁ : Polynomial R₁.integers) (hPE : ∀ i, ((P₁.coeff i : R₁.integers) : F) ∈ E)
    (hroot : (P₁.map R₁.integers.subtype).eval z = 0) :
    ∃ (η : Fb₁) (Q : Polynomial Fb₁), σ η = R₂.residue ⟨z, hz₂⟩ ^ q ∧
      P₁.map R₁.residue = (X ^ q - C η) * Q ∧
      ∃ hD : (derivative (P₁.map R₁.integers.subtype)).eval z ∈ R₂.integers,
        R₂.residue ⟨_, hD⟩ = (derivative ((P₁.map R₁.residue).map σ)).eval (R₂.residue ⟨z, hz₂⟩) := by
  set P : Polynomial F := P₁.map R₁.integers.subtype with hPdef
  have hc₁ : ∀ i, ((P₁.coeff i : R₁.integers) : F) = P.coeff i := fun i => by
    rw [hPdef, coeff_map]
    rfl

  obtain ⟨P₂, hP₂map⟩ := (mem_lifts (f := R₂.integers.subtype) P).mp
    ((lifts_iff_coeff_lifts (f := R₂.integers.subtype) P).mpr
      fun i => ⟨⟨P.coeff i, hE₂ _ (hc₁ i ▸ hPE i) (hc₁ i ▸ (P₁.coeff i).2)⟩, rfl⟩)
  have hc₂ : ∀ i, ((P₂.coeff i : R₂.integers) : F) = P.coeff i := fun i => by
    rw [← hP₂map, coeff_map]
    rfl
  set zI : R₂.integers := ⟨z, hz₂⟩ with hzI

  have hbar : P₂.map R₂.residue = (P₁.map R₁.residue).map σ := by
    ext i
    rw [coeff_map, coeff_map, coeff_map]
    have h₂ : P₂.coeff i = ⟨P.coeff i, hE₂ _ (hc₁ i ▸ hPE i) (hc₁ i ▸ (P₁.coeff i).2)⟩ :=
      Subtype.ext (hc₂ i)
    have h₁ : P₁.coeff i = ⟨P.coeff i, hc₁ i ▸ (P₁.coeff i).2⟩ := Subtype.ext (hc₁ i)
    rw [h₁, h₂]
    exact hσ (P.coeff i) (hc₁ i ▸ hPE i) (hc₁ i ▸ (P₁.coeff i).2)

  have hroot₂ : (P₂.map R₂.residue).eval (R₂.residue zI) = 0 := by
    have h0 : P₂.eval zI = 0 := by
      apply Subtype.ext
      have h := map_eval' R₂.integers.subtype P₂ zI
      rw [hP₂map] at h
      exact h.trans hroot
    rw [← map_eval', h0, map_zero]

  letI : Algebra Fb₁ Fb₂ := σ.toAlgebra
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨η, hη⟩ := RingHom.mem_range.mp (hpi (R₂.residue zI))
  have hfrob : ∀ a b : Fb₂, a ^ q = b ^ q → a = b := by
    intro a b hab
    have h : (a - b) ^ q = a ^ q - b ^ q := by rw [sub_pow_char]
    rw [hab, sub_self] at h
    exact sub_eq_zero.mp ((pow_eq_zero_iff hq.ne_zero).mp h)
  have hηq : ∀ b : Fb₁, b ^ q ≠ η := by
    intro b hb
    apply hzr₂
    refine RingHom.mem_range.mpr ⟨b, hfrob _ _ ?_⟩
    rw [← map_pow, hb, hη]
  have hmin : minpoly Fb₁ (R₂.residue zI) = X ^ q - C η := by
    refine (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hq hηq) ?_
      (monic_X_pow_sub_C η hq.ne_zero)).symm
    simp [RingHom.algebraMap_toAlgebra, hη]
  have haeval : aeval (R₂.residue zI) (P₁.map R₁.residue) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, RingHom.algebraMap_toAlgebra, ← hbar]
    exact hroot₂
  have hdvd := minpoly.dvd Fb₁ (R₂.residue zI) haeval
  rw [hmin] at hdvd
  obtain ⟨Q, hQ⟩ := hdvd

  have hDeq : (derivative P).eval z = (((derivative P₂).eval zI : R₂.integers) : F) := by
    rw [← hP₂map]
    exact (map_derivative_eval R₂.integers.subtype P₂ zI).symm
  have hmem : (derivative P).eval z ∈ R₂.integers := hDeq ▸ ((derivative P₂).eval zI).2
  refine ⟨η, Q, hη, hQ, hmem, ?_⟩
  have hel : (⟨(derivative P).eval z, hmem⟩ : R₂.integers) = (derivative P₂).eval zI := Subtype.ext hDeq
  rw [hel, map_derivative_eval, hbar]

include hσ hq hpi hzr₂ in

private theorem exists_mem_and_residue_derivative_eval_eq_zero (P : Polynomial F) (hPE : ∀ i, P.coeff i ∈ E)
    (hP₁ : ∀ i, P.coeff i ∈ R₁.integers) (hroot : P.eval z = 0) :
    ∃ hD : (derivative P).eval z ∈ R₂.integers, R₂.residue ⟨_, hD⟩ = 0 := by
  obtain ⟨P₁, rfl⟩ := (mem_lifts (f := R₁.integers.subtype) P).mp
    ((lifts_iff_coeff_lifts (f := R₁.integers.subtype) P).mpr fun i => ⟨⟨P.coeff i, hP₁ i⟩, rfl⟩)
  have hPE' : ∀ i, ((P₁.coeff i : R₁.integers) : F) ∈ E := fun i => by
    have h := hPE i
    rw [coeff_map] at h
    exact h
  obtain ⟨η, Q, hη, hQ, hD, hres⟩ := core R₁ R₂ hE₂ σ hσ hq hpi hz₂ hzr₂ P₁ hPE' hroot
  refine ⟨hD, ?_⟩
  rw [hres, hQ, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    derivative_mul, eval_add, eval_mul, eval_mul, eval_sub, eval_pow, eval_X, eval_C, hη, sub_self, zero_mul,
    add_zero, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C,
    CharP.cast_eq_zero Fb₂ q, zero_mul, zero_mul]

include hσ hq hpi hzr₂ in

private theorem exists_residue_derivative_eval_eq_pow_sub (hz₁ : z ∈ R₁.integers) (P : Polynomial F)
    (hPE : ∀ i, P.coeff i ∈ E) (hP₁ : ∀ i, P.coeff i ∈ R₁.integers) (hmonic : P.Monic)
    (hdeg : P.natDegree = q + 1) (hroot : P.eval z = 0) :
    ∃ η : Fb₁, σ η = R₂.residue ⟨z, hz₂⟩ ^ q ∧
      ∀ hD : (derivative P).eval z ∈ R₁.integers, R₁.residue ⟨_, hD⟩ = R₁.residue ⟨z, hz₁⟩ ^ q - η := by
  obtain ⟨P₁, rfl, hP₁deg, hP₁monic⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts (f := R₁.integers.subtype) P).mpr fun i => ⟨⟨P.coeff i, hP₁ i⟩, rfl⟩) hmonic
  have hPE' : ∀ i, ((P₁.coeff i : R₁.integers) : F) ∈ E := fun i => by
    have h := hPE i
    rw [coeff_map] at h
    exact h
  obtain ⟨η, Q, hη, hQ, -, -⟩ := core R₁ R₂ hE₂ σ hσ hq hpi hz₂ hzr₂ P₁ hPE' hroot
  refine ⟨η, hη, fun hD => ?_⟩

  have hbar_monic : (P₁.map R₁.residue).Monic := hP₁monic.map _
  have hXq : (X ^ q - C η : Polynomial Fb₁).Monic := monic_X_pow_sub_C η hq.ne_zero
  have hQmonic : Q.Monic := hXq.of_mul_monic_left (hQ ▸ hbar_monic)
  have hQdeg : Q.natDegree = 1 := by
    have h := congrArg natDegree hQ
    rw [hP₁monic.natDegree_map, hP₁deg, hdeg, hXq.natDegree_mul hQmonic, natDegree_X_pow_sub_C] at h
    omega
  have hq1 : ((q : ℕ) : Fb₁) = 0 := by
    apply σ.injective
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero Fb₂ q

  set zI₁ : R₁.integers := ⟨z, hz₁⟩ with hzI₁
  have hDeq : (derivative (P₁.map R₁.integers.subtype)).eval z = (((derivative P₁).eval zI₁ : R₁.integers) : F) :=
    (map_derivative_eval R₁.integers.subtype P₁ zI₁).symm
  have hel : (⟨(derivative (P₁.map R₁.integers.subtype)).eval z, hD⟩ : R₁.integers) = (derivative P₁).eval zI₁ :=
    Subtype.ext hDeq
  rw [hel, map_derivative_eval, hQ, hQmonic.eq_X_add_C hQdeg, derivative_mul, derivative_X_add_C, eval_add,
    eval_mul, eval_mul, eval_one, mul_one, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul,
    eval_C, hq1, zero_mul, zero_mul, zero_add, eval_sub, eval_pow, eval_X, eval_C]

end Ws49.SplitEngine
end

section
open AlgebraicCurve

namespace Ws49
namespace SplitEngine

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

private theorem natCast_mem_nonunits_of_charP {k : Type*} [Field k] {q : ℕ} [CharP k q] (red : A →+* k) :
    ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
  have hqA : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    have h' := h.map red
    rw [map_natCast, CharP.cast_eq_zero k q] at h'
    exact not_isUnit_zero h'
  have h := (ValuationSubring.coe_mem_nonunits_iff (A := A) (a := ((q : ℕ) : A))).mpr hqA
  simpa using h

variable {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F]
  {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb] (R : RegularProlongation A F Fb)

private theorem const_smul_mem' {c : AlgebraicClosure ℚ} (hc : c ∈ A) {f : F} (hf : f ∈ R.integers) :
    c • f ∈ R.integers := by
  rw [Algebra.smul_def]
  exact mul_mem ((R.algebraMap_mem_iff c).mpr hc) hf

private theorem exists_const_smul_mem (f : F) : ∃ d : A, d ≠ 0 ∧ (d : AlgebraicClosure ℚ) • f ∈ R.integers := by
  by_cases hf : f = 0
  · exact ⟨1, one_ne_zero, by rw [hf, smul_zero]; exact zero_mem _⟩
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf
  have hc0 : c ≠ 0 := R.smul_const_ne_zero hc hres
  rcases A.mem_or_inv_mem c with hcA | hcinv
  · exact ⟨⟨c, hcA⟩, fun h => hc0 (congrArg Subtype.val h), hc⟩
  · refine ⟨1, one_ne_zero, ?_⟩
    have : f = c⁻¹ • (c • f) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [OneMemClass.coe_one, one_smul, this]
    exact const_smul_mem' R hcinv hc

private theorem exists_const_smul_eq_of_residue_eq_zero {g : F} (hg : g ∈ R.integers) (hg0 : R.residue ⟨g, hg⟩ = 0)
    (hgne : g ≠ 0) :
    ∃ (c : A) (u : F) (hu : u ∈ R.integers),
      c ∈ IsLocalRing.maximalIdeal A ∧ c ≠ 0 ∧ R.residue ⟨u, hu⟩ ≠ 0 ∧ g = (c : AlgebraicClosure ℚ) • u := by
  obtain ⟨c₁, hc₁, hres⟩ := R.exists_smul_mem g hgne
  have hc₁0 : c₁ ≠ 0 := R.smul_const_ne_zero hc₁ hres

  have hinv : c₁⁻¹ ∈ A := by
    by_contra hnot
    have hc₁A : c₁ ∈ A := (A.mem_or_inv_mem c₁).resolve_right hnot
    apply hres
    have hsub : (⟨c₁ • g, hc₁⟩ : R.integers)
        = ⟨algebraMap (AlgebraicClosure ℚ) F c₁, (R.algebraMap_mem_iff c₁).mpr hc₁A⟩ * ⟨g, hg⟩ := by
      apply Subtype.ext
      simp [Algebra.smul_def]
    rw [hsub, map_mul, hg0, mul_zero]
  have hgeq : g = c₁⁻¹ • (c₁ • g) := by rw [smul_smul, inv_mul_cancel₀ hc₁0, one_smul]
  refine ⟨⟨c₁⁻¹, hinv⟩, c₁ • g, hc₁, ?_, fun h => inv_ne_zero hc₁0 (congrArg Subtype.val h), hres, hgeq⟩

  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsub : (⟨g, hg⟩ : R.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) F c₁⁻¹, (R.algebraMap_mem_iff c₁⁻¹).mpr hinv⟩ * ⟨c₁ • g, hc₁⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    rw [← Algebra.smul_def]
    exact hgeq
  have h := hg0
  rw [hsub, map_mul, R.residue_algebraMap ⟨c₁⁻¹, hinv⟩] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact (algebraMap (IsLocalRing.ResidueField A) Fb).injective (by rw [h0, map_zero])
  · exact absurd h0 hres

private theorem exists_pow_mul_mem {q : ℕ} [Fact q.Prime] (hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) (f : F)
    {g : F} (hg : g ∈ R.integers) (hg0 : R.residue ⟨g, hg⟩ = 0) (hgne : g ≠ 0) :
    ∃ M : ℕ, g ^ M * f ∈ R.integers := by
  obtain ⟨d, hd0, hdf⟩ := exists_const_smul_mem R f
  obtain ⟨c, u, hu, hcm, hc0, -, rfl⟩ := exists_const_smul_eq_of_residue_eq_zero R hg hg0 hgne
  obtain ⟨M, a, ha⟩ := ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal A hq d hd0 c hcm hc0
  refine ⟨M, ?_⟩
  have hcM : (c : AlgebraicClosure ℚ) ^ M = (d : AlgebraicClosure ℚ) * (a : AlgebraicClosure ℚ) := by
    have h := congrArg (fun x : A => (x : AlgebraicClosure ℚ)) ha
    simpa using h
  have hrepr : ((c : AlgebraicClosure ℚ) • u) ^ M * f
      = (a : AlgebraicClosure ℚ) • (u ^ M * ((d : AlgebraicClosure ℚ) • f)) := by
    rw [smul_pow, hcM, mul_comm (d : AlgebraicClosure ℚ), mul_smul, smul_mul_assoc, smul_mul_assoc]
    congr 1
    rw [mul_smul_comm]
  rw [hrepr]
  exact const_smul_mem' R a.2 (mul_mem (pow_mem hu M) hdf)

end Ws49.SplitEngine
end

section
open AlgebraicCurve

namespace Ws49
namespace SplitEngine

private theorem finrankAlong_algEquiv_toAlgHom {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F ≃ₐ[K] F') : finrankAlong K e.toAlgHom = 1 := by
  have h := finrankAlong_comp e.toAlgHom e.symm.toAlgHom
  have hid : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K F := by
    ext x
    simp
  rw [hid, finrankAlong_id] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

end Ws49.SplitEngine
end

section
open Polynomial AlgebraicCurve

namespace Ws49
namespace SplitEngine

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem coeff_minpolyDiv_mem_subring (x : L) (B : Subring L) (hx : x ∈ B)
    (hf : ∀ n, algebraMap K L ((minpoly K x).coeff n) ∈ B) (i : ℕ) : (minpolyDiv K x).coeff i ∈ B := by
  suffices H : ∀ j i : ℕ, (minpolyDiv K x).natDegree < i + j → (minpolyDiv K x).coeff i ∈ B from
    H ((minpolyDiv K x).natDegree + 1) i (by omega)
  intro j
  induction j with
  | zero =>
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hi)]
    exact zero_mem _
  | succ j ih =>
    intro i hi
    rw [coeff_minpolyDiv]
    exact add_mem (hf (i + 1)) (mul_mem (ih (i + 1) (by omega)) hx)

variable [Algebra.IsSeparable K L]

private theorem repr_eq_trace_mul (pb : PowerBasis K L) (h : L) (i : Fin pb.dim) :
    pb.basis.repr h i = Algebra.trace K L
      (h * ((minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative (minpoly K pb.gen)))) := by
  haveI := pb.finite
  rw [← Module.Basis.traceDual_powerBasis_eq pb i, ← Algebra.traceForm_apply,
    ← Module.Basis.traceDual_repr_apply, Module.Basis.traceDual_traceDual]

variable {O : Type*} [CommRing O] [Algebra O K] [Algebra O L] [IsScalarTower O K L]
  [IsIntegrallyClosed O] [IsFractionRing O K]

private theorem exists_algebraMap_eq_repr_of_isIntegral (pb : PowerBasis K L) (h : L)
    (hint : ∀ i : Fin pb.dim,
      IsIntegral O (h * ((minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative (minpoly K pb.gen)))))
    (i : Fin pb.dim) : ∃ y : O, algebraMap O K y = pb.basis.repr h i := by
  haveI := pb.finite
  rw [repr_eq_trace_mul]
  exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (hint i))

section Generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem ord_nonneg_of_mem' (v : Place K L) {f : L} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : L) * ((π : L) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem mem_of_ord_nonneg' (v : Place K L) {f : L} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem minpoly_eq_of_monic_of_natDegree_eq {x : L} {m : Polynomial K} (hm : m.Monic) (hroot : aeval x m = 0)
    (hdeg : m.natDegree = Module.finrank K L)
    (hgen : IntermediateField.adjoin K ({x} : Set L) = ⊤) : minpoly K x = m := by
  have hint : IsIntegral K x := ⟨m, hm, by rwa [← aeval_def]⟩
  have hnat : (minpoly K x).natDegree = Module.finrank K L := by
    rw [← IntermediateField.adjoin.finrank hint, hgen, IntermediateField.finrank_top']
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hm (minpoly.dvd _ _ hroot) ?_).symm
  rw [hdeg, hnat]

private theorem exists_powerBasis_of_adjoin_eq_top {x : L} (hint : IsIntegral K x)
    (hgen : IntermediateField.adjoin K ({x} : Set L) = ⊤) :
    ∃ pb : PowerBasis K L, pb.gen = x ∧ pb.dim = (minpoly K x).natDegree :=
  ⟨(IntermediateField.adjoin.powerBasis hint).map
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv), rfl, rfl⟩

private theorem eq_sum_repr_mul_pow (pb : PowerBasis K L) {n : ℕ} (hdim : pb.dim = n) (h : L) :
    h = ∑ i : Fin n, algebraMap K L (pb.basis.repr h (Fin.cast hdim.symm i)) * pb.gen ^ (i : ℕ) := by
  conv_lhs => rw [← pb.basis.sum_repr h]
  subst hdim
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pb.basis_eq_pow, Algebra.smul_def]
  rfl

private theorem coeff_minpoly_mem_of_isIntegral {K₀ : Type*} [Field K₀] [Algebra K₀ K] (v : Place K₀ K) (x : L)
    (hx : IsIntegral v.toValuationSubring x) (i : ℕ) : (minpoly K x).coeff i ∈ v.toValuationSubring := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, coeff_map]
  exact ((minpoly v.toValuationSubring x).coeff i).2

private theorem natDegree_minpoly_of_adjoin_eq_top [FiniteDimensional K L] (x : L)
    (hx : IntermediateField.adjoin K ({x} : Set L) = ⊤) : (minpoly K x).natDegree = Module.finrank K L := by
  rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite K x), hx, IntermediateField.finrank_top']

private theorem pow_eq_sum_neg_coeff_minpoly (x : L) (hx : IsIntegral K x) {n : ℕ} (hn : (minpoly K x).natDegree = n) :
    x ^ n = ∑ i : Fin n, (-(algebraMap K L ((minpoly K x).coeff i))) * x ^ (i : ℕ) := by
  have h0 := minpoly.aeval K x
  rw [(minpoly.monic hx).as_sum, hn] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  rw [Finset.sum_range] at h0
  rw [eq_neg_of_add_eq_zero_left h0, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_mul]

end Generic

section AtPlace

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']

private theorem isIntegral_of_forall_ord_fiber_nonneg (v : Place K F) {y : F'} (hy : ∀ w ∈ v.fiber F', 0 ≤ w.ord y) :
    IsIntegral v.toValuationSubring y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · exact isIntegral_zero
  obtain ⟨c, hc⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg hy0 hy
  rw [← hc]
  exact c.2

private theorem repr_mem_of_forall_ord_fiber_nonneg (v : Place K F) (pb : PowerBasis F F') (h : F')
    (hint : ∀ j : Fin pb.dim, ∀ w ∈ v.fiber F',
      0 ≤ w.ord (h * ((minpolyDiv F pb.gen).coeff j / aeval pb.gen (derivative (minpoly F pb.gen)))))
    (i : Fin pb.dim) : pb.basis.repr h i ∈ v.toValuationSubring := by
  obtain ⟨y, hy⟩ := exists_algebraMap_eq_repr_of_isIntegral (O := v.toValuationSubring) pb h
    (fun j => isIntegral_of_forall_ord_fiber_nonneg v (hint j)) i
  rw [← hy]
  exact y.2

private theorem repr_mem_of_forall_mem_fiber (v : Place K F) (pb : PowerBasis F F') (h : F')
    (hint : ∀ j : Fin pb.dim, ∀ w ∈ v.fiber F',
      h * ((minpolyDiv F pb.gen).coeff j / aeval pb.gen (derivative (minpoly F pb.gen))) ∈ w.toValuationSubring)
    (i : Fin pb.dim) : pb.basis.repr h i ∈ v.toValuationSubring :=
  repr_mem_of_forall_ord_fiber_nonneg v pb h (fun j w hw => ord_nonneg_of_mem' w (hint j w hw)) i

end AtPlace

end Ws49.SplitEngine
end

section
open Polynomial AlgebraicCurve

namespace Ws49
namespace SplitEngine

section Along

variable {L : Type*} [Field L] [CharZero L] {K F : Type*} [Field K] [Field F] [Algebra L K] [Algebra L F]
  [Algebra K F] [IsScalarTower L K F] {q : ℕ}

private theorem finiteDimensional_along
    (hdeg : Module.finrank K F = q + 1) :
    FiniteDimensional (K) (F) := by
  have h := hdeg
  exact Module.finite_of_finrank_pos (by omega)

private theorem isSeparable_along [CharZero K]
    (hdeg : Module.finrank K F = q + 1) :
    Algebra.IsSeparable (K) (F) := by
  haveI := finiteDimensional_along hdeg
  haveI := Algebra.IsAlgebraic.of_finite (K) (F)
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

private theorem adjoin_along_eq_top (z : F)
    (hgen : IntermediateField.adjoin L
      (Set.range (algebraMap K F) ∪ {z}) = ⊤) :
    IntermediateField.adjoin (K) ({z} : Set (F)) = ⊤ := by
  have hle : IntermediateField.adjoin L
      (Set.range (algebraMap K F) ∪ {z}) ≤
        (IntermediateField.adjoin (K)
          ({z} : Set (F))).restrictScalars L := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (⟨a, rfl⟩ | rfl)
    · exact (IntermediateField.mem_restrictScalars _).mpr (IntermediateField.algebraMap_mem _ a)
    · exact (IntermediateField.mem_restrictScalars _).mpr
        (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))
  rw [hgen] at hle
  rw [eq_top_iff]
  intro f _
  exact (IntermediateField.mem_restrictScalars _).mp (hle IntermediateField.mem_top)

private theorem aeval_along_eq (m : Polynomial (K)) (z : F) :
    aeval z m = (m.map (algebraMap K F)).eval z := by
  rw [aeval_def, eval₂_eq_eval_map]

private theorem exists_powerBasis_along
    (hdeg : Module.finrank K F = q + 1)
    (z : F)
    (hgen : IntermediateField.adjoin L
      (Set.range (algebraMap K F) ∪ {z}) = ⊤)
    (m : Polynomial (K)) (hm : m.Monic) (hdegm : m.natDegree = q + 1)
    (hroot : (m.map (algebraMap K F)).eval z = 0) :
    ∃ pb : PowerBasis (K) (F),
      pb.gen = z ∧ pb.dim = q + 1 ∧ minpoly (K) z = m := by
  have hgen' := adjoin_along_eq_top z hgen
  have haeval : aeval z m = 0 := by rw [aeval_along_eq]; exact hroot
  have hmin : minpoly (K) z = m :=
    minpoly_eq_of_monic_of_natDegree_eq hm haeval (by rw [hdegm, hdeg]) hgen'
  have hint : IsIntegral (K) z := ⟨m, hm, by rwa [← aeval_def]⟩
  obtain ⟨pb, hpb, hdim⟩ := exists_powerBasis_of_adjoin_eq_top hint hgen'
  exact ⟨pb, hpb, by rw [hdim, hmin, hdegm], hmin⟩

private theorem adjoin_union_eq_top_of_linearIndependent
    (hdeg : Module.finrank K F = q + 1)
    (z : F)
    (hli : LinearIndependent (K) fun i : Fin (q + 1) => z ^ (i : ℕ)) :
    IntermediateField.adjoin L
      (Set.range (algebraMap K F) ∪ {z}) = ⊤ := by
  haveI := finiteDimensional_along hdeg
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hdeg])
  rw [eq_top_iff]
  intro f _
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (K)).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span (K)
      (Set.range fun i : Fin (q + 1) => z ^ (i : ℕ)))
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  have hz : z ∈ IntermediateField.adjoin L
      (Set.range (algebraMap K F) ∪ {z}) :=
    IntermediateField.subset_adjoin _ _ (Or.inr rfl)
  have hc : algebraMap K F (c i) ∈ IntermediateField.adjoin L
      (Set.range (algebraMap K F) ∪ {z}) :=
    IntermediateField.subset_adjoin _ _ (Or.inl ⟨c i, rfl⟩)
  exact mul_mem hc (pow_mem hz _)

private theorem exists_monic_data_of_linearIndependent
    (hdeg : Module.finrank K F = q + 1)
    (z : F)
    (hli : LinearIndependent (K) fun i : Fin (q + 1) => z ^ (i : ℕ)) :
    IntermediateField.adjoin L
        (Set.range (algebraMap K F) ∪ {z}) = ⊤ ∧
      ∃ m : Polynomial (K), m.Monic ∧ m.natDegree = q + 1 ∧
        (m.map (algebraMap K F)).eval z = 0 ∧
        z ^ (q + 1) =
          ∑ i : Fin (q + 1), (-(algebraMap K F (m.coeff i))) * z ^ (i : ℕ) := by
  haveI := finiteDimensional_along hdeg
  have hgen := adjoin_union_eq_top_of_linearIndependent (L := L) hdeg z hli
  have hint : IsIntegral (K) z := IsIntegral.of_finite (K) z
  have hnat : (minpoly (K) z).natDegree = q + 1 := by
    rw [natDegree_minpoly_of_adjoin_eq_top z (adjoin_along_eq_top z hgen), hdeg]
  refine ⟨hgen, minpoly (K) z, minpoly.monic hint, hnat, ?_, ?_⟩
  · rw [← aeval_along_eq]
    exact minpoly.aeval _ _
  · exact pow_eq_sum_neg_coeff_minpoly z hint hnat

private theorem coeff_mem_of_forall_mem [HasPrincipalDivisors L F] [CharZero K] [Algebra.IsIntegral K F]
    (hdeg : Module.finrank K F = q + 1)
    (z : F)
    (hgen : IntermediateField.adjoin L
      (Set.range (algebraMap K F) ∪ {z}) = ⊤)
    (m : Polynomial (K)) (hm : m.Monic) (hdegm : m.natDegree = q + 1)
    (hroot : (m.map (algebraMap K F)).eval z = 0)
    (u₀ : Place L (K))
    (hz : ∀ W ∈ u₀.fiber F, z ∈ W.toValuationSubring)
    (i : ℕ) : m.coeff i ∈ u₀.toValuationSubring := by
  haveI := finiteDimensional_along hdeg
  haveI := isSeparable_along hdeg
  obtain ⟨-, -, -, hmin⟩ := exists_powerBasis_along hdeg z hgen m hm hdegm hroot
  rw [← hmin]
  refine coeff_minpoly_mem_of_isIntegral u₀ z (isIntegral_of_forall_ord_fiber_nonneg u₀ fun W hW => ?_) i
  exact ord_nonneg_of_mem' W (hz W hW)

end Along

end Ws49.SplitEngine
end

section
open Polynomial AlgebraicCurve

namespace Ws49
namespace SplitEngine

section GenericValues

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

private theorem val_not_hasValue_zero_mul (w : Place k E) {x y : E}
    (hx : x ∈ w.toValuationSubring) (hy : y ∈ w.toValuationSubring)
    (hx0 : ¬ w.HasValue x 0) (hy0 : ¬ w.HasValue y 0) : ¬ w.HasValue (x * y) 0 := by
  rintro ⟨_, hxy⟩
  rw [map_zero] at hxy
  have hmul : IsLocalRing.residue w.toValuationSubring ⟨x * y, mul_mem hx hy⟩ =
      IsLocalRing.residue w.toValuationSubring ⟨x, hx⟩ *
        IsLocalRing.residue w.toValuationSubring ⟨y, hy⟩ := by
    rw [← map_mul]; rfl
  rw [hmul] at hxy
  rcases mul_eq_zero.mp hxy with h | h
  · exact hx0 ⟨hx, by rw [h, map_zero]⟩
  · exact hy0 ⟨hy, by rw [h, map_zero]⟩

private theorem val_not_hasValue_zero_mul' (w : Place k E) {x y : E}
    (hx0 : ¬ w.HasValue x 0) (hy0 : ¬ w.HasValue y 0) : ¬ w.HasValue (x * y) 0 := by
  rintro ⟨hxy, hres⟩
  rw [map_zero, IsLocalRing.residue_eq_zero_iff] at hres
  by_cases hx : x ∈ w.toValuationSubring
  · by_cases hy : y ∈ w.toValuationSubring
    · exact val_not_hasValue_zero_mul w hx hy hx0 hy0
        ⟨hxy, by rw [map_zero, IsLocalRing.residue_eq_zero_iff]; exact hres⟩
    · have hyinv : y⁻¹ ∈ w.toValuationSubring := (w.toValuationSubring.mem_or_inv_mem y).resolve_left hy
      have hy0' : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
      have hxeq : x = x * y * y⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hy0', mul_one]
      have hxm : (⟨x, hx⟩ : w.toValuationSubring) = ⟨x * y, hxy⟩ * ⟨y⁻¹, hyinv⟩ := Subtype.ext hxeq
      exact hx0 ⟨hx, by rw [map_zero, IsLocalRing.residue_eq_zero_iff, hxm]; exact Ideal.mul_mem_right _ _ hres⟩
  · have hxinv : x⁻¹ ∈ w.toValuationSubring := (w.toValuationSubring.mem_or_inv_mem x).resolve_left hx
    have hx0' : x ≠ 0 := fun h => hx (h ▸ zero_mem _)
    have hyeq : y = x * y * x⁻¹ := by rw [mul_comm x y, mul_assoc, mul_inv_cancel₀ hx0', mul_one]
    have hy : y ∈ w.toValuationSubring := by rw [hyeq]; exact mul_mem hxy hxinv
    have hym : (⟨y, hy⟩ : w.toValuationSubring) = ⟨x * y, hxy⟩ * ⟨x⁻¹, hxinv⟩ := Subtype.ext hyeq
    exact hy0 ⟨hy, by rw [map_zero, IsLocalRing.residue_eq_zero_iff, hym]; exact Ideal.mul_mem_right _ _ hres⟩

private theorem val_not_hasValue_one_zero (w : Place k E) : ¬ w.HasValue (1 : E) 0 :=
  fun h => zero_ne_one (h.unique w.hasValue_one)

private theorem val_hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {x y : F} {a b : K} (hx : w.HasValue x a) (hy : w.HasValue y b) : w.HasValue (x + y) (a + b) := by
  obtain ⟨hxm, hxr⟩ := hx
  obtain ⟨hym, hyr⟩ := hy
  refine ⟨add_mem hxm hym, ?_⟩
  have e : (⟨x + y, add_mem hxm hym⟩ : w.toValuationSubring) = ⟨x, hxm⟩ + ⟨y, hym⟩ := rfl
  rw [e, map_add, hxr, hyr, map_add]

private theorem val_hasValue_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {x : F} {a : K} (hx : w.HasValue x a) : w.HasValue (-x) (-a) := by
  obtain ⟨hxm, hxr⟩ := hx
  refine ⟨neg_mem hxm, ?_⟩
  have e : (⟨-x, neg_mem hxm⟩ : w.toValuationSubring) = -⟨x, hxm⟩ := rfl
  rw [e, map_neg, hxr, map_neg]

end GenericValues

section ChartRing

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb₁ : Type*} [Field Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₁] {k : Type*} [Field k] [Algebra k Fb₁]
  (R₁ : RegularProlongation A F Fb₁) {v : Place k Fb₁} {r : Place L F → Place k Fb₁} {S : Set F}

private theorem aux_mem_integers_of_mem_chartRing (hint : ∀ s ∈ S, s ∈ R₁.integers)
    {g : F} (hg : g ∈ Subring.closure S) : g ∈ R₁.integers :=
  (Subring.closure_le.mpr (fun s hs => hint s hs) : Subring.closure S ≤ R₁.integers.toSubring) hg

private theorem aux_mem_of_mem_chartRing
    (hregOver : ∀ s ∈ S, ∀ W : Place L F,
      r W = v → s ∈ W.toValuationSubring)
    {g : F} (hg : g ∈ Subring.closure S)
    (W : Place L F) (hW : r W = v) :
    g ∈ W.toValuationSubring :=
  (Subring.closure_le.mpr (fun s hs => hregOver s hs W hW) :
    Subring.closure S ≤ W.toValuationSubring.toSubring) hg

private theorem aux_residue₁_mem_of_mem_chartRing (hint : ∀ s ∈ S, s ∈ R₁.integers)
    (hregv : ∀ (s : F) (hs : s ∈ S),
      R₁.residue ⟨s, hint s hs⟩ ∈ v.toValuationSubring)
    {g : F} (hg : g ∈ Subring.closure S) (hgI : g ∈ R₁.integers) :
    R₁.residue ⟨g, hgI⟩ ∈ v.toValuationSubring := by
  have hST : S ⊆ ((v.toValuationSubring.toSubring.comap R₁.residue).map R₁.integers.subtype :
      Set (F)) := by
    intro s hs
    rw [SetLike.mem_coe, Subring.mem_map]
    exact ⟨⟨s, hint s hs⟩, (Subring.mem_comap).mpr (hregv s hs), rfl⟩
  have hgT := (Subring.closure_le.mpr hST) hg
  rw [Subring.mem_map] at hgT
  obtain ⟨y, hy, hyg⟩ := hgT
  rw [Subring.mem_comap] at hy
  have hyg' : (⟨g, hgI⟩ : R₁.integers) = y := Subtype.ext hyg.symm
  rw [hyg']
  exact hy

private theorem aux_nv_mul (hint : ∀ s ∈ S, s ∈ R₁.integers)
    (hregv : ∀ (s : F) (hs : s ∈ S),
      R₁.residue ⟨s, hint s hs⟩ ∈ v.toValuationSubring)
    {x y : F} (hx : x ∈ Subring.closure S) (hy : y ∈ Subring.closure S)
    (hx₀ : ∀ h : x ∈ R₁.integers, ¬ v.HasValue (R₁.residue ⟨x, h⟩) (0 : k))
    (hy₀ : ∀ h : y ∈ R₁.integers, ¬ v.HasValue (R₁.residue ⟨y, h⟩) (0 : k)) :
    ∀ h : x * y ∈ R₁.integers, ¬ v.HasValue (R₁.residue ⟨x * y, h⟩) (0 : k) := by
  intro h
  have hxI := aux_mem_integers_of_mem_chartRing R₁ hint hx
  have hyI := aux_mem_integers_of_mem_chartRing R₁ hint hy
  have hsplit : (⟨x * y, h⟩ : R₁.integers) = ⟨x, hxI⟩ * ⟨y, hyI⟩ := rfl
  rw [hsplit, map_mul]
  exact val_not_hasValue_zero_mul v (aux_residue₁_mem_of_mem_chartRing R₁ hint hregv hx hxI)
    (aux_residue₁_mem_of_mem_chartRing R₁ hint hregv hy hyI) (hx₀ hxI) (hy₀ hyI)

private theorem aux_nv_one :
    ∀ h : (1 : F) ∈ R₁.integers, ¬ v.HasValue (R₁.residue ⟨1, h⟩) (0 : k) := by
  intro h
  have hone : (⟨1, h⟩ : R₁.integers) = 1 := rfl
  rw [hone, map_one]
  exact val_not_hasValue_one_zero v

private theorem aux_nv_pow (hint : ∀ s ∈ S, s ∈ R₁.integers)
    (hregv : ∀ (s : F) (hs : s ∈ S),
      R₁.residue ⟨s, hint s hs⟩ ∈ v.toValuationSubring)
    {x : F} (hx : x ∈ Subring.closure S)
    (hx₀ : ∀ h : x ∈ R₁.integers, ¬ v.HasValue (R₁.residue ⟨x, h⟩) (0 : k)) (n : ℕ) :
    ∀ h : x ^ n ∈ R₁.integers, ¬ v.HasValue (R₁.residue ⟨x ^ n, h⟩) (0 : k) := by
  induction n with
  | zero =>
    intro h
    have h0 : (⟨x ^ 0, h⟩ : R₁.integers) = ⟨1, one_mem _⟩ := Subtype.ext (pow_zero x)
    rw [h0]
    exact aux_nv_one R₁ (one_mem _)
  | succ n ih =>
    intro h
    have hs : (⟨x ^ (n + 1), h⟩ : R₁.integers) =
        ⟨x ^ n * x, aux_mem_integers_of_mem_chartRing R₁ hint (mul_mem (pow_mem hx n) hx)⟩ :=
      Subtype.ext (pow_succ x n)
    rw [hs]
    exact aux_nv_mul R₁ hint hregv (pow_mem hx n) hx ih hx₀ _

private theorem aux_eval_mem {p : Polynomial (F)}
    (hp : ∀ i, p.coeff i ∈ Subring.closure S) {x : F} (hx : x ∈ Subring.closure S) :
    p.eval x ∈ Subring.closure S := by
  rw [Polynomial.eval_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hp i) (pow_mem hx i)

private theorem aux_identity_pow_succ {G : Type*} [CommRing G] (x D : G) (M : ℕ) :
    x * D ^ (M + 1) = D * (D ^ M * x) := by
  ring

private theorem aux_identity_clear {G : Type*} [Field G] (x D a : G) (hD : D ≠ 0) (M : ℕ) :
    x * D ^ (M + 1) * (a / D) = x * (D ^ M * a) := by
  field_simp
  ring

private theorem aux_sum_mul_mem {G : Type*} [CommRing G] {T : Subring G} {n : ℕ} (a : Fin n → G) {z e : G} (hz : z ∈ T)
    (hae : ∀ i, a i * e ∈ T) : (∑ i : Fin n, a i * z ^ (i : ℕ)) * e ∈ T := by
  rw [Finset.sum_mul]
  refine sum_mem fun i _ => ?_
  rw [mul_assoc, mul_comm (z ^ (i : ℕ)) e, ← mul_assoc]
  exact mul_mem (hae i) (pow_mem hz _)

private theorem aux_ne_zero_of_nv {x : F} (hxI : x ∈ R₁.integers)
    (hx : ∀ h : x ∈ R₁.integers, ¬ v.HasValue (R₁.residue ⟨x, h⟩) (0 : k)) : x ≠ 0 := by
  intro h0
  apply hx hxI
  have hz : (⟨x, hxI⟩ : R₁.integers) = 0 := Subtype.ext h0
  rw [hz, map_zero]
  simpa using v.hasValue_algebraMap (0 : k)

private theorem aux_exists_separator_product_of_sep (hint : ∀ s ∈ S, s ∈ R₁.integers)
    (hregv : ∀ (s : F) (hs : s ∈ S),
      R₁.residue ⟨s, hint s hs⟩ ∈ v.toValuationSubring)
    (hregOver : ∀ s ∈ S, ∀ W : Place L F,
      r W = v → s ∈ W.toValuationSubring)
    {bad : Place L F → Prop}
    (hsep : ∀ W : Place L F,
      bad W → r W = v →
        ∃ (u : F) (hu : u ∈ S),
          ¬ v.HasValue (R₁.residue ⟨u, hint u hu⟩) (0 : k) ∧ 0 < W.ord u)
    (B : Finset (Place L F))
    (hB : ∀ W ∈ B, bad W ∧ r W = v)
    (n : Place L F → ℕ) :
    ∃ Z : F, Z ∈ Subring.closure S ∧ Z ≠ 0 ∧
      (∀ h : Z ∈ R₁.integers, ¬ v.HasValue (R₁.residue ⟨Z, h⟩) (0 : k)) ∧ ∀ W ∈ B, (n W : ℤ) ≤ W.ord Z := by
  classical
  induction B using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, one_ne_zero, aux_nv_one R₁, by simp⟩
  | insert W₀ B' hW₀ ih =>
    obtain ⟨Z', hZ'c, hZ'0, hZ'v, hZ'ord⟩ := ih fun W hW => hB W (Finset.mem_insert_of_mem hW)
    obtain ⟨hb₀, hr₀⟩ := hB W₀ (Finset.mem_insert_self _ _)
    obtain ⟨u, hu, hu₀, hord⟩ := hsep W₀ hb₀ hr₀
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [W₀.ord_zero] at hord
      exact lt_irrefl _ hord
    have huc : u ∈ Subring.closure S := Subring.subset_closure hu
    refine ⟨u ^ n W₀ * Z', mul_mem (pow_mem huc _) hZ'c, mul_ne_zero (pow_ne_zero _ hu0) hZ'0,
      aux_nv_mul R₁ hint hregv (pow_mem huc _) hZ'c (aux_nv_pow R₁ hint hregv huc (fun _ => hu₀) _) hZ'v, ?_⟩
    intro W hW
    have hn0 : (0 : ℤ) ≤ n W₀ := Int.natCast_nonneg _
    rcases Finset.mem_insert.mp hW with hWW | hW'
    · rw [hWW, W₀.ord_mul (pow_ne_zero _ hu0) hZ'0, ← zpow_natCast, W₀.ord_zpow]
      have hZ'nn : 0 ≤ W₀.ord Z' := ord_nonneg_of_mem' W₀ (aux_mem_of_mem_chartRing hregOver hZ'c W₀ hr₀)
      have h1le : (1 : ℤ) ≤ W₀.ord u := hord
      have hprod : (n W₀ : ℤ) ≤ n W₀ * W₀.ord u := le_mul_of_one_le_right hn0 h1le
      linarith
    · rw [W.ord_mul (pow_ne_zero _ hu0) hZ'0, ← zpow_natCast, W.ord_zpow]
      have hWv := (hB W (Finset.mem_insert_of_mem hW')).2
      have hunn : 0 ≤ W.ord u := ord_nonneg_of_mem' W (hregOver u hu W hWv)
      have hprod : (0 : ℤ) ≤ n W₀ * W.ord u := mul_nonneg hn0 hunn
      have := hZ'ord W hW'
      linarith

end ChartRing

end Ws49.SplitEngine
end

section JH
open Polynomial AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHPlaceSpecialization
open scoped MatrixGroups

namespace Ws49
namespace SplitEngine
namespace JH

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
  (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
  (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
    Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

scoped instance charP_fbar : CharP (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) p :=
  charP_of_injective_algebraMap (algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).injective p

section TwoSided
variable {L K F Fb : Type*} [Field L] [Field K] [Field F] [Field Fb] [Algebra L K] [Algebra L F]
  {A : ValuationSubring L} [Algebra (ResidueField ↥A) Fb]

theorem mem₂_of_unit (R₁ R₂ : RegularProlongation A F Fb) (α : K →ₐ[L] F) (φ : Fb → Fb) (hφ0 : ∀ y, φ y = 0 → y = 0)
    (hres : ∀ (v : K) (h₁ : α v ∈ R₁.integers) (h₂ : α v ∈ R₂.integers), R₂.residue ⟨α v, h₂⟩ = φ (R₁.residue ⟨α v, h₁⟩))
    (v : K) (h₁ : α v ∈ R₁.integers) (hr₁ : R₁.residue ⟨α v, h₁⟩ ≠ 0) : ∃ h₂ : α v ∈ R₂.integers, R₂.residue ⟨α v, h₂⟩ ≠ 0 := by
  by_cases h₂ : α v ∈ R₂.integers
  · exact ⟨h₂, by rw [hres v h₁ h₂]; exact fun h => hr₁ (hφ0 _ h)⟩
  · exfalso
    have hv0 : α v ≠ 0 := by
      intro h
      apply hr₁
      have : (⟨α v, h₁⟩ : ↥R₁.integers) = 0 := Subtype.ext h
      rw [this, map_zero]
    have hinv₂ : (α v)⁻¹ ∈ R₂.integers := (R₂.integers.mem_or_inv_mem (α v)).resolve_left h₂
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (R₁.isUnit_of_residue_ne_zero hr₁)
    have hb' : (b : F) = (α v)⁻¹ := eq_inv_of_mul_eq_one_right (by simpa using congrArg Subtype.val hb)
    have hinv₁ : (α v)⁻¹ ∈ R₁.integers := hb' ▸ b.2
    have k₁ : α v⁻¹ ∈ R₁.integers := by rw [map_inv₀]; exact hinv₁
    have k₂ : α v⁻¹ ∈ R₂.integers := by rw [map_inv₀]; exact hinv₂
    have hr₁' : R₁.residue ⟨α v⁻¹, k₁⟩ ≠ 0 := by
      apply R₁.residue_ne_zero_of_isUnit
      refine IsUnit.of_mul_eq_one ⟨α v, h₁⟩ (Subtype.ext ?_)
      simp [map_inv₀, inv_mul_cancel₀ hv0]
    have hr₂' : R₂.residue ⟨α v⁻¹, k₂⟩ ≠ 0 := by rw [hres v⁻¹ k₁ k₂]; exact fun h => hr₁' (hφ0 _ h)
    obtain ⟨b₂, hb₂⟩ := isUnit_iff_exists_inv.mp (R₂.isUnit_of_residue_ne_zero hr₂')
    have hb₂' : (b₂ : F) = (α v⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right (by simpa using congrArg Subtype.val hb₂)
    apply h₂
    have : (α v⁻¹)⁻¹ = α v := by rw [map_inv₀, inv_inv]
    rw [← this, ← hb₂']
    exact b₂.2

theorem mem₂_of_mem₁ (R₁ R₂ : RegularProlongation A F Fb) (α : K →ₐ[L] F) (φ : Fb → Fb) (hφ0 : ∀ y, φ y = 0 → y = 0)
    (hres : ∀ (v : K) (h₁ : α v ∈ R₁.integers) (h₂ : α v ∈ R₂.integers), R₂.residue ⟨α v, h₂⟩ = φ (R₁.residue ⟨α v, h₁⟩))
    (v : K) (h₁ : α v ∈ R₁.integers) : α v ∈ R₂.integers := by
  by_cases hr₁ : R₁.residue ⟨α v, h₁⟩ ≠ 0
  · exact (mem₂_of_unit R₁ R₂ α φ hφ0 hres v h₁ hr₁).1
  · push Not at hr₁
    have h₁' : α (1 + v) ∈ R₁.integers := by rw [map_add, map_one]; exact add_mem (one_mem _) h₁
    have hr : R₁.residue ⟨α (1 + v), h₁'⟩ ≠ 0 := by
      have : (⟨α (1 + v), h₁'⟩ : ↥R₁.integers) = 1 + ⟨α v, h₁⟩ := Subtype.ext (by simp)
      rw [this, map_add, map_one, hr₁, add_zero]
      exact one_ne_zero
    obtain ⟨h₂', -⟩ := mem₂_of_unit R₁ R₂ α φ hφ0 hres (1 + v) h₁' hr
    have : α v = α (1 + v) - 1 := by rw [map_add, map_one]; ring
    rw [this]
    exact sub_mem h₂' (one_mem _)

end TwoSided

include hres₂α in

theorem hE₂ : ∀ e ∈ α.fieldRange, e ∈ Rpd.R₁.integers → e ∈ Rpd.R₂.integers := by
  intro e he h₁
  obtain ⟨t, rfl⟩ := AlgHom.mem_fieldRange.mp he
  exact mem₂_of_mem₁ Rpd.R₁ Rpd.R₂ α _ (fun y hy => (map_eq_zero_iff _ (qExpFrobeniusModL_injective (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)).mp hy) hres₂α t h₁

theorem hσ : ∀ e (he : e ∈ α.fieldRange) (h₁ : e ∈ Rpd.R₁.integers),
    Rpd.R₂.residue ⟨e, hE₂ p M H hpM A θ α Psp Rpd hres₂α e he h₁⟩ = (qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p).toRingHom (Rpd.R₁.residue ⟨e, h₁⟩) := by
  intro e he h₁
  obtain ⟨t, rfl⟩ := AlgHom.mem_fieldRange.mp he
  exact hres₂α t h₁ _

omit [IsAlgClosed (ResidueField ↥A)] in

theorem hpi : ∀ y : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), y ^ p ∈ (qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p).toRingHom.range := by
  intro y
  obtain ⟨c, hc⟩ := exists_qExpFrobeniusModL_eq_pow (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y
  exact ⟨c, hc⟩

omit [IsAlgClosed (ResidueField ↥A)] [NeZero M] [NeZero (M / p)] in

theorem hzr₂ {g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)} (hg : ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ ((g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)).coeff n ≠ 0) :
    g ∉ (qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p).toRingHom.range := by
  rintro ⟨y, rfl⟩
  obtain ⟨n, hn, hc⟩ := hg
  apply hc
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  change ((qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)).coeff n = 0
  rw [coe_qExpFrobeniusModL]
  exact qExpand_coeff_of_not_dvd p _ hn

end Ws49.SplitEngine.JH
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine.JH"
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine"
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49"
end JH
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine.JH"

section JHB
open Polynomial AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHPlaceSpecialization
open scoped MatrixGroups

namespace Ws49
namespace SplitEngine
namespace JH

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
  (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
  (hα : α.IsIntegral)
  (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
  (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
    Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))
  {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))} {S : Set ↥(xHFunctionFieldBar M H)}

omit [NeZero (M / p)] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in

theorem different_mem_chartRing {z : ↥(xHFunctionFieldBar M H)} (hzc : z ∈ Subring.closure S)
    {m : Polynomial ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))} (hcoef : ∀ i : ℕ, α (m.coeff i) ∈ Subring.closure S)
    {D : ↥(xHFunctionFieldBar M H)} (hD : D = (derivative (m.map α.toRingHom)).eval z) : D ∈ Subring.closure S := by
  subst hD
  refine aux_eval_mem (fun i => ?_) hzc
  rw [coeff_derivative, coeff_map]
  exact mul_mem (hcoef (i + 1)) (add_mem (natCast_mem _ i) (one_mem _))

include hres₂α in

theorem different_residue₂ (hint : ∀ s ∈ S, s ∈ Rpd.R₁.integers)
    {z : ↥(xHFunctionFieldBar M H)} (hz₂ : z ∈ Rpd.R₂.integers)
    (hz : ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ ((Rpd.R₂.residue ⟨z, hz₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)).coeff n ≠ 0)
    {m : Polynomial ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))} (hroot : (m.map α.toRingHom).eval z = 0)
    (hcoef : ∀ i : ℕ, α (m.coeff i) ∈ Subring.closure S)
    {D : ↥(xHFunctionFieldBar M H)} (hD : D = (derivative (m.map α.toRingHom)).eval z) :
    ∃ hD₂ : D ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨D, hD₂⟩ = 0 := by
  subst hD
  exact exists_mem_and_residue_derivative_eval_eq_zero Rpd.R₁ Rpd.R₂ (hE₂ p M H hpM A θ α Psp Rpd hres₂α) _ (hσ p M H hpM A θ α Psp Rpd hres₂α)
    Fact.out (hpi p M H hpM A) hz₂ (hzr₂ p M H hpM A hz) (m.map α.toRingHom)
    (fun i => by rw [coeff_map]; exact AlgHom.mem_fieldRange.mpr ⟨m.coeff i, rfl⟩)
    (fun i => by rw [coeff_map]; exact aux_mem_integers_of_mem_chartRing Rpd.R₁ hint (hcoef i)) hroot

include hres₂α hα_coe hpM2 hHp in

theorem exists_coords {z : ↥(xHFunctionFieldBar M H)} (hz₁ : z ∈ Rpd.R₁.integers) (hz₂ : z ∈ Rpd.R₂.integers)
    (hz : ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ ((Rpd.R₂.residue ⟨z, hz₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)).coeff n ≠ 0)
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ) (Set.range α ∪ {z}) = ⊤)
    {m : Polynomial ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))} (hm : m.Monic) (hdegm : m.natDegree = p + 1)
    (hroot : (m.map α.toRingHom).eval z = 0)
    (hzc : z ∈ Subring.closure S) (hcoef : ∀ i : ℕ, α (m.coeff i) ∈ Subring.closure S)
    {D : ↥(xHFunctionFieldBar M H)} (hD : D = (derivative (m.map α.toRingHom)).eval z)
    {h : ↥(xHFunctionFieldBar M H)} (hh₁ : h ∈ Rpd.R₁.integers) (hh₂ : h ∈ Rpd.R₂.integers)
    (hreg : ∀ a ∈ Subring.closure S, ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = v → h * (a / D) ∈ W.toValuationSubring) :
    ∃ φ : Fin (p + 1) → ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      h = ∑ i : Fin (p + 1), α (φ i) * z ^ (i : ℕ) ∧ (∀ i, α (φ i) ∈ Rpd.R₁.integers) ∧
      ∀ i, ∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), Psp.sp u₀ = v → φ i ∈ u₀.toValuationSubring := by
  letI instKF : Algebra ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := algebraAlong α
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := isScalarTower_along α
  have hdeg := finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar p M H hpM hpM2 hHp α hα_coe
  dsimp only [finrankAlong] at hdeg
  haveI := finiteDimensional_along hdeg
  haveI : CharZero ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))).injective
  haveI := isSeparable_along hdeg
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1.toHasPrincipalDivisors
  haveI : Algebra.IsIntegral ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := Algebra.IsIntegral.of_finite _ _
  have hrootK : (m.map (algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H))).eval z = 0 := hroot
  have hgenK : IntermediateField.adjoin (AlgebraicClosure ℚ) (Set.range (algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H)) ∪ {z}) = ⊤ := hgen
  obtain ⟨pb, hpbgen, hpbdim, hpbmin⟩ := exists_powerBasis_along hdeg z hgenK m hm hdegm hrootK
  have hsum := eq_sum_repr_mul_pow pb hpbdim h
  rw [hpbgen] at hsum
  refine ⟨fun i => pb.basis.repr h (Fin.cast hpbdim.symm i), hsum, ?_, ?_⟩
  · exact coeff_mem_integers_of_mem_integers Rpd.R₁ Rpd.R₂ (hE₂ p M H hpM A θ α Psp Rpd hres₂α) _ (hσ p M H hpM A θ α Psp Rpd hres₂α) Fact.out (hpi p M H hpM A)
      hz₁ hz₂ (hzr₂ p M H hpM A hz) (fun i => α (pb.basis.repr h (Fin.cast hpbdim.symm i)))
      (fun i => AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩) hsum hh₁ hh₂
  · intro i u₀ hu₀
    refine repr_mem_of_forall_mem_fiber u₀ pb h ?_ (Fin.cast hpbdim.symm i)
    intro j W hW
    have hWv : Psp.reduceFst α hα W = v := by
      have hres : W.restrictAlong α hα = u₀ := Place.mem_fiber.mp hW
      show Psp.sp (W.restrictAlong α hα) = v
      rw [hres, hu₀]
    have hD' : aeval pb.gen (derivative (minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) pb.gen)) = D := by
      rw [hpbgen, hpbmin, aeval_along_eq, hD, derivative_map]; rfl
    have haj : (minpolyDiv ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) pb.gen).coeff j ∈ Subring.closure S := by
      rw [hpbgen]
      refine coeff_minpolyDiv_mem_subring z (Subring.closure S) hzc (fun n => ?_) j
      rw [hpbmin]; exact hcoef n
    rw [hD']
    exact hreg _ haj W hWv

omit [IsAlgClosed (ResidueField ↥A)] in

theorem exists_common_denominator (hint : ∀ s ∈ S, s ∈ Rpd.R₁.integers)
    (hregv : ∀ (s : ↥(xHFunctionFieldBar M H)) (hs : s ∈ S), (Rpd.R₁.residue ⟨s, hint s hs⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ∈ v.toValuationSubring)
    (hnIncl : ∀ φ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), α φ ∈ Rpd.R₁.integers →
      (∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), Psp.sp u₀ = v → φ ∈ u₀.toValuationSubring) →
      ∃ (s : ↥(xHFunctionFieldBar M H)) (_ : s ∈ S) (e : ↥(xHFunctionFieldBar M H)) (he : e ∈ S),
        ¬ v.HasValue (Rpd.R₁.residue ⟨e, hint e he⟩) (0 : (ResidueField ↥A)) ∧ α φ * e = s)
    {d : ℕ} (φ : Fin d → ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hφ₁ : ∀ i, α (φ i) ∈ Rpd.R₁.integers)
    (hφreg : ∀ i, ∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), Psp.sp u₀ = v → φ i ∈ u₀.toValuationSubring) :
    ∃ e : ↥(xHFunctionFieldBar M H), e ∈ Subring.closure S ∧
      (∀ h : e ∈ Rpd.R₁.integers, ¬ v.HasValue (Rpd.R₁.residue ⟨e, h⟩) (0 : (ResidueField ↥A))) ∧
      ∀ i, α (φ i) * e ∈ Subring.closure S := by
  classical
  suffices H' : ∀ T : Finset (Fin d), ∃ e : ↥(xHFunctionFieldBar M H), e ∈ Subring.closure S ∧
      (∀ h : e ∈ Rpd.R₁.integers, ¬ v.HasValue (Rpd.R₁.residue ⟨e, h⟩) (0 : (ResidueField ↥A))) ∧
      ∀ i ∈ T, α (φ i) * e ∈ Subring.closure S by
    obtain ⟨e, h1, h2, h3⟩ := H' Finset.univ
    exact ⟨e, h1, h2, fun i => h3 i (Finset.mem_univ i)⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, aux_nv_one Rpd.R₁, by simp⟩
  | insert i₀ T' hi₀ ih =>
    obtain ⟨e', he'c, he'v, he'T⟩ := ih
    obtain ⟨s, hs, e₀, he₀, he₀v, hse⟩ := hnIncl (φ i₀) (hφ₁ i₀) (hφreg i₀)
    have he₀c : e₀ ∈ Subring.closure S := Subring.subset_closure he₀
    refine ⟨e₀ * e', mul_mem he₀c he'c, aux_nv_mul Rpd.R₁ hint hregv he₀c he'c (fun _ => he₀v) he'v, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [← mul_assoc, hse]
      exact mul_mem (Subring.subset_closure hs) he'c
    · rw [mul_left_comm]
      exact mul_mem he₀c (he'T i hi)

end Ws49.SplitEngine.JH
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine.JH"
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine.JH"
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine.JH"
end JHB
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine.JH"

section JHC
open Polynomial AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHPlaceSpecialization
open scoped MatrixGroups

namespace Ws49
namespace SplitEngine
namespace JH

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
  (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
  (hα : α.IsIntegral)
  (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
  (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
    Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))
  {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))} {S : Set ↥(xHFunctionFieldBar M H)}

include hres₂α hα_coe hpM2 hHp in
set_option maxHeartbeats 1600000 in
theorem inclusion_core (hint : ∀ s ∈ S, s ∈ Rpd.R₁.integers)
    (hregv : ∀ (s : ↥(xHFunctionFieldBar M H)) (hs : s ∈ S),
      (Rpd.R₁.residue ⟨s, hint s hs⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ∈ v.toValuationSubring)
    (hregOver : ∀ s ∈ S, ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα W = v → s ∈ W.toValuationSubring)
    (hnIncl : ∀ φ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      α φ ∈ Rpd.R₁.integers →
      (∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), Psp.sp u₀ = v → φ ∈ u₀.toValuationSubring) →
      ∃ (s : ↥(xHFunctionFieldBar M H)) (_ : s ∈ S) (e : ↥(xHFunctionFieldBar M H)) (he : e ∈ S),
        ¬ v.HasValue (Rpd.R₁.residue ⟨e, hint e he⟩) (0 : (ResidueField ↥A)) ∧ α φ * e = s)
    (hE : Rpd.ChartEtaleAt α v S)
    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers)
    (Z : ↥(xHFunctionFieldBar M H)) (hZc : Z ∈ Subring.closure S) (hZ0 : Z ≠ 0)
    (hZv : ∀ h : Z ∈ Rpd.R₁.integers, ¬ v.HasValue (Rpd.R₁.residue ⟨Z, h⟩) (0 : (ResidueField ↥A)))
    (hfZ : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα W = v → 0 ≤ W.ord (f * Z)) :
    f ∈ Rpd.chartLocalSetFst v S := by
  have _ := hZ0
  obtain ⟨z, m, hzS, ⟨hz₂, hz⟩, hgen, hm, hdegm, hroot, hcoef, hetale⟩ := hE
  have hz₁ : z ∈ Rpd.R₁.integers := hint z hzS
  have hzc : z ∈ Subring.closure S := Subring.subset_closure hzS

  have hfZ' : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα W = v → f * Z ∈ W.toValuationSubring := by
    intro W hW
    rcases eq_or_ne (f * Z) 0 with h0 | h0
    · rw [h0]
      exact zero_mem _
    · exact mem_of_ord_nonneg' W h0 (hfZ W hW)

  obtain ⟨D, hD⟩ : ∃ D : ↥(xHFunctionFieldBar M H),
      D = (Polynomial.derivative (m.map α.toRingHom)).eval z := ⟨_, rfl⟩
  have hDv : ∀ h : D ∈ Rpd.R₁.integers, ¬ v.HasValue (Rpd.R₁.residue ⟨D, h⟩) (0 : (ResidueField ↥A)) := by
    rw [hD]
    exact hetale
  have hDc : D ∈ Subring.closure S := different_mem_chartRing p M H hpM α hzc hcoef hD
  have hD₁ : D ∈ Rpd.R₁.integers := aux_mem_integers_of_mem_chartRing Rpd.R₁ hint hDc
  have hD0 : D ≠ 0 := aux_ne_zero_of_nv Rpd.R₁ hD₁ hDv
  obtain ⟨hD₂, hDres⟩ := different_residue₂ p M H hpM A θ α Psp Rpd hres₂α hint hz₂ hz hroot hcoef hD

  obtain ⟨n₁, hM⟩ := exists_pow_mul_mem Rpd.R₂ (natCast_mem_nonunits_of_charP (IsLocalRing.residue ↥A)) (f * Z) hD₂ hDres hD0
  have hZ₁ : Z ∈ Rpd.R₁.integers := aux_mem_integers_of_mem_chartRing Rpd.R₁ hint hZc
  have hh₁ : f * Z * D ^ (n₁ + 1) ∈ Rpd.R₁.integers := mul_mem (mul_mem h₁ hZ₁) (pow_mem hD₁ _)
  have hh₂ : f * Z * D ^ (n₁ + 1) ∈ Rpd.R₂.integers := by
    rw [aux_identity_pow_succ]
    exact mul_mem hD₂ hM

  obtain ⟨φ, hhsum, hφ₁, hφreg⟩ := exists_coords p M H hpM hpM2 hHp A θ α hα_coe hα Psp Rpd hres₂α hz₁ hz₂ hz hgen hm hdegm hroot hzc hcoef hD hh₁ hh₂ (by
    intro a ha W hW
    rw [aux_identity_clear _ _ _ hD0]
    exact mul_mem (hfZ' W hW) (mul_mem (pow_mem (aux_mem_of_mem_chartRing hregOver hDc W hW) _)
      (aux_mem_of_mem_chartRing hregOver ha W hW)))

  obtain ⟨e, hec, hev, hφe⟩ := exists_common_denominator p M H hpM A θ α Psp Rpd hint hregv hnIncl φ hφ₁ hφreg
  have huc : Z * D ^ (n₁ + 1) * e ∈ Subring.closure S := mul_mem (mul_mem hZc (pow_mem hDc _)) hec
  refine ⟨f * Z * D ^ (n₁ + 1) * e, Z * D ^ (n₁ + 1) * e, ?_, huc, aux_mem_integers_of_mem_chartRing Rpd.R₁ hint huc,
    aux_nv_mul Rpd.R₁ hint hregv (mul_mem hZc (pow_mem hDc _)) hec
      (aux_nv_mul Rpd.R₁ hint hregv hZc (pow_mem hDc _) hZv (aux_nv_pow Rpd.R₁ hint hregv hDc hDv _)) hev _, ?_⟩
  · rw [hhsum]
    exact aux_sum_mul_mem _ hzc hφe
  · rw [← mul_assoc, ← mul_assoc]

include hres₂α hα_coe hpM2 hHp in
theorem inclusion_of_split (hint : ∀ s ∈ S, s ∈ Rpd.R₁.integers)
    (hregv : ∀ (s : ↥(xHFunctionFieldBar M H)) (hs : s ∈ S),
      (Rpd.R₁.residue ⟨s, hint s hs⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ∈ v.toValuationSubring)
    (hregOver : ∀ s ∈ S, ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα W = v → s ∈ W.toValuationSubring)
    (hnIncl : ∀ φ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      α φ ∈ Rpd.R₁.integers →
      (∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), Psp.sp u₀ = v → φ ∈ u₀.toValuationSubring) →
      ∃ (s : ↥(xHFunctionFieldBar M H)) (_ : s ∈ S) (e : ↥(xHFunctionFieldBar M H)) (he : e ∈ S),
        ¬ v.HasValue (Rpd.R₁.residue ⟨e, hint e he⟩) (0 : (ResidueField ↥A)) ∧ α φ * e = s)
    (hE : Rpd.ChartEtaleAt α v S)
    {good bad : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → Prop}
    (hsplit : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα W = v → good W ∨ bad W)
    (hsep : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      bad W → Psp.reduceFst α hα W = v →
        ∃ (u : ↥(xHFunctionFieldBar M H)) (hu : u ∈ S),
          ¬ v.HasValue (Rpd.R₁.residue ⟨u, hint u hu⟩) (0 : (ResidueField ↥A)) ∧ 0 < W.ord u)
    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers)
    (hreg : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      good W → Psp.reduceFst α hα W = v → 0 ≤ W.ord f) :
    f ∈ Rpd.chartLocalSetFst v S := by
  classical
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, 1, zero_mem _, one_mem _, one_mem _, aux_nv_one Rpd.R₁ (one_mem _), zero_mul 1⟩
  obtain ⟨Df, hDf, -⟩ := ((ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1.toHasPrincipalDivisors).exists_divisor f hf0
  obtain ⟨Z, hZc, hZ0, hZv, hZord⟩ := aux_exists_separator_product_of_sep Rpd.R₁ hint hregv hregOver hsep
    (Df.support.filter (fun W => bad W ∧ Psp.reduceFst α hα W = v)) (fun W hW => (Finset.mem_filter.mp hW).2)
    (fun W => (-W.ord f).toNat)
  refine inclusion_core p M H hpM hpM2 hHp A θ α hα_coe hα Psp Rpd hres₂α hint hregv hregOver hnIncl hE f h₁ Z hZc hZ0 hZv ?_
  intro W hW
  rw [W.ord_mul hf0 hZ0]
  have hZnn : 0 ≤ W.ord Z := ord_nonneg_of_mem' W (aux_mem_of_mem_chartRing hregOver hZc W hW)
  rcases hsplit W hW with hgood | hbad
  · have := hreg W hgood hW
    omega
  · by_cases hneg : W.ord f < 0
    · have hWB : W ∈ Df.support.filter (fun W => bad W ∧ Psp.reduceFst α hα W = v) := by
        rw [Finset.mem_filter, Finsupp.mem_support_iff, hDf W]
        exact ⟨hneg.ne, hbad, hW⟩
      have h1' := hZord W hWB
      have h2' : -W.ord f ≤ ((-W.ord f).toNat : ℤ) := Int.self_le_toNat _
      omega
    · omega

end Ws49.SplitEngine.JH
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine.JH"
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine.JH"
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine.JH"
end JHC
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49 P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt.Ws49.SplitEngine.JH"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (S : Set ↥(xHFunctionFieldBar M H)) (hS : Rpd.IsCuspChartFstAt α hα v S)
    (hsplit : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = v → (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) W ∨ (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) W)
    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers)
    (hreg : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) W → Psp.reduceFst α hα W = v → 0 ≤ W.ord f) :
    f ∈ Rpd.chartLocalSetFst v S :=
  Ws49.SplitEngine.JH.inclusion_of_split p M H hpM hpM2 hHp A θ α hα_coe hα Psp Rpd hres₂α hS.integral hS.regular hS.regularOver
    hS.nIncl hS.etale hsplit hS.separates f h₁ hreg

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_chartLocalSetFst_of_isCuspChartFstAt (solution)
