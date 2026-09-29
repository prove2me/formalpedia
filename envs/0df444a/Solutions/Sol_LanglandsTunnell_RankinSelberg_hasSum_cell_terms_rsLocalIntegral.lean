-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.hasSum_cell_terms_rsLocalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9d0463de-89c7-5ccb-9eef-8c3cd780b07f

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_HaarQuotient
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain UnramifiedWhittaker

noncomputable section

namespace LanglandsTunnell
namespace RankinSelberg
namespace FinIwasawaProof
namespace ResidueIndex

open IsDedekindDomain NumberField
open scoped WithZero

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with h0 | h0
  · rw [h0]; exact zero_le'
  · apply WithZero.le_exp_of_log_le
    have h1 : WithZero.log x < (0 : ℤ) := by
      rw [WithZero.log_lt_iff_lt_exp h0, WithZero.exp_zero]
      exact hx
    omega

variable {v}

private theorem dvd_iff_valued_lt_one {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) =
      WithZero.exp (-1 : ℤ))
    (x : v.adicCompletionIntegers ℚ) :
    ϖ ∣ x ↔ Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) x) < 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_mul, hϖ]
    have hy : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) y) ≤ 1 := y.2
    calc WithZero.exp (-1 : ℤ) * Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) y)
        ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
      _ < 1 := by
        rw [mul_one, ← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by norm_num)
  · intro hx
    refine (HeightOneSpectrum.adicCompletionIntegers.integers (K := ℚ) (v := v)).dvd_of_le ?_
    rw [hϖ]
    exact le_exp_neg_one_of_lt_one hx

private theorem span_singleton_eq_maximalIdeal {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) =
      WithZero.exp (-1 : ℤ)) :
    Ideal.span {ϖ} = IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) := by
  ext x
  rw [Ideal.mem_span_singleton, dvd_iff_valued_lt_one hϖ,
    NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 ℚ) ℚ v x]
  exact Iff.rfl

variable (v)

private noncomputable def residueLift :
    (𝓞 ℚ) ⧸ v.asIdeal →+* IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) :=
  Ideal.Quotient.lift v.asIdeal
    ((IsLocalRing.residue (v.adicCompletionIntegers ℚ)).comp
      (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ)))
    (fun _ ha => NumberField.AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 ℚ) ℚ v ha)

private theorem mem_of_residue_algebraMap_eq_zero {a : 𝓞 ℚ}
    (h : IsLocalRing.residue (v.adicCompletionIntegers ℚ)
      (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) a) = 0) :
    a ∈ v.asIdeal := by
  rw [IsLocalRing.residue_eq_zero_iff,
    NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 ℚ) ℚ v] at h
  simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply] at h
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap] at h
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mp h

private theorem residueLift_bijective : Function.Bijective (residueLift v) := by
  refine ⟨?_, ?_⟩
  · refine RingHom.lift_injective_of_ker_le_ideal _ _ ?_
    intro a ha
    exact mem_of_residue_algebraMap_eq_zero v (RingHom.mem_ker.mp ha)
  · intro z
    obtain ⟨a, ha⟩ := NumberField.AdelicHaar.residue_algebraMap_surjective (𝓞 ℚ) ℚ v z
    exact ⟨Ideal.Quotient.mk _ a, ha⟩

private theorem natCard_residueField :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (residueLift_bijective v)), Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

variable {v}

private theorem natCard_quot_span_uniformizer {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) =
      WithZero.exp (-1 : ℤ)) :
    Nat.card (v.adicCompletionIntegers ℚ ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal := by
  rw [← natCard_residueField v]
  exact Nat.card_congr (Ideal.quotEquivOfEq (span_singleton_eq_maximalIdeal hϖ)).toEquiv

private theorem index_span_uniformizer {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) =
      WithZero.exp (-1 : ℤ)) :
    (Ideal.span {ϖ} : Ideal (v.adicCompletionIntegers ℚ)).toAddSubgroup.index =
      Ideal.absNorm v.asIdeal := by
  rw [AddSubgroup.index, ← natCard_quot_span_uniformizer hϖ]
  rfl

end LanglandsTunnell.RankinSelberg.FinIwasawaProof.ResidueIndex

namespace LanglandsTunnell
namespace RankinSelberg
namespace FinIwasawaProof
namespace ResidueIndexAmbient

open IsDedekindDomain NumberField
open scoped WithZero

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def integersAdd : AddSubgroup (v.adicCompletion ℚ) :=
  (v.adicCompletionIntegers ℚ).toSubring.toAddSubgroup

variable {v}

private def scaledIntegersAdd (ϖ : v.adicCompletion ℚ) : AddSubgroup (v.adicCompletion ℚ) :=
  (integersAdd v).map (AddMonoidHom.mulLeft ϖ)

private theorem mem_integersAdd (x : v.adicCompletion ℚ) : x ∈ integersAdd v ↔ x ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

private theorem mem_scaledIntegersAdd (ϖ x : v.adicCompletion ℚ) :
    x ∈ scaledIntegersAdd ϖ ↔ ∃ y ∈ v.adicCompletionIntegers ℚ, ϖ * y = x :=
  Iff.rfl

private theorem scaledIntegersAdd_le (ϖ : v.adicCompletionIntegers ℚ) :
    scaledIntegersAdd (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≤ integersAdd v := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_integersAdd]
  exact (v.adicCompletionIntegers ℚ).mul_mem _ _ ϖ.2 hy

private def integersAddEquiv : ↥(integersAdd v) ≃+ v.adicCompletionIntegers ℚ where
  toFun x := ⟨x.1, x.2⟩
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem map_scaled_eq_span (ϖ : v.adicCompletionIntegers ℚ) :
    ((scaledIntegersAdd (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)).addSubgroupOf
        (integersAdd v)).map (integersAddEquiv (v := v)).toAddMonoidHom =
      (Ideal.span {ϖ} : Ideal (v.adicCompletionIntegers ℚ)).toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := (mem_scaledIntegersAdd _ _).mp hx
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hzx.symm
  · rintro ⟨c, rfl⟩
    refine ⟨⟨(ϖ * c : v.adicCompletionIntegers ℚ), (ϖ * c).2⟩, ?_, rfl⟩
    exact (mem_scaledIntegersAdd _ _).mpr ⟨c, c.2, rfl⟩

private def quotEquiv (ϖ : v.adicCompletionIntegers ℚ) :
    (integersAdd v ⧸
        (scaledIntegersAdd (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)).addSubgroupOf
          (integersAdd v)) ≃+
      (v.adicCompletionIntegers ℚ ⧸ Ideal.span {ϖ}) :=
  QuotientAddGroup.congr _ _ (integersAddEquiv (v := v)) (map_scaled_eq_span ϖ)

private theorem natCard_integersAdd_quot_scaled {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    Nat.card (integersAdd v ⧸
        (scaledIntegersAdd (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)).addSubgroupOf
          (integersAdd v)) =
      Ideal.absNorm v.asIdeal := by
  rw [Nat.card_congr (quotEquiv ϖ).toEquiv]
  exact ResidueIndex.natCard_quot_span_uniformizer hϖ

private theorem finite_integersAdd_quot_scaled {ϖ : v.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    Finite (integersAdd v ⧸
      (scaledIntegersAdd (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ)).addSubgroupOf
        (integersAdd v)) := by
  haveI : Finite (v.adicCompletionIntegers ℚ ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)))
  haveI : Finite (v.adicCompletionIntegers ℚ ⧸ Ideal.span {ϖ}) :=
    Finite.of_equiv _ (Ideal.quotEquivOfEq (ResidueIndex.span_singleton_eq_maximalIdeal hϖ)).symm.toEquiv
  exact Finite.of_equiv _ (quotEquiv ϖ).symm.toEquiv

end LanglandsTunnell.RankinSelberg.FinIwasawaProof.ResidueIndexAmbient

namespace LanglandsTunnell
namespace RankinSelberg
namespace FinIwasawaProof
namespace TorusConj

variable {K : Type*} [Field K]

private theorem diagZ_coe (π : K) (hπ : π ≠ 0) (m : ℤ) :
    (UnramifiedWhittaker.diagZ π hπ m : Matrix (Fin 2) (Fin 2) K) = !![π ^ m, 0; 0, 1] := rfl

private theorem scalarPi_coe (π : K) (hπ : π ≠ 0) :
    (UnramifiedWhittaker.scalarPi π hπ : Matrix (Fin 2) (Fin 2) K) = !![π, 0; 0, π] := rfl

private theorem diagZ_mul_unipotentGL2 (π : K) (hπ : π ≠ 0) (m : ℤ) (x : K) :
    UnramifiedWhittaker.diagZ π hπ m * AutomorphicForm.unipotentGL2 x =
      AutomorphicForm.unipotentGL2 (π ^ m * x) * UnramifiedWhittaker.diagZ π hπ m := by
  apply Units.ext
  simp only [Units.val_mul, diagZ_coe, AutomorphicForm.unipotentGL2_coe]
  simp

private theorem scalarPi_commute_unipotentGL2 (π : K) (hπ : π ≠ 0) (x : K) :
    Commute (UnramifiedWhittaker.scalarPi π hπ) (AutomorphicForm.unipotentGL2 x) := by
  apply Units.ext
  simp only [Units.val_mul, scalarPi_coe, AutomorphicForm.unipotentGL2_coe]
  simp [mul_comm]

private theorem torus_mul_unipotentGL2 (π : K) (hπ : π ≠ 0) (p : ℤ × ℤ) (x : K) :
    UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2 *
        AutomorphicForm.unipotentGL2 x =
      AutomorphicForm.unipotentGL2 (π ^ (p.1 - p.2) * x) *
        (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) := by
  have hc : Commute (UnramifiedWhittaker.scalarPi π hπ ^ p.2) (AutomorphicForm.unipotentGL2 x) :=
    (scalarPi_commute_unipotentGL2 π hπ x).zpow_left p.2
  calc UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2 *
          AutomorphicForm.unipotentGL2 x
      = UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) *
          (AutomorphicForm.unipotentGL2 x * UnramifiedWhittaker.scalarPi π hπ ^ p.2) := by
        rw [mul_assoc, hc.eq]
    _ = (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * AutomorphicForm.unipotentGL2 x) *
          UnramifiedWhittaker.scalarPi π hπ ^ p.2 := by
        rw [mul_assoc]
    _ = AutomorphicForm.unipotentGL2 (π ^ (p.1 - p.2) * x) *
          (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) := by
        rw [diagZ_mul_unipotentGL2, mul_assoc]

private theorem scalarPi_pow_coe (π : K) (hπ : π ≠ 0) (n : ℕ) :
    ((UnramifiedWhittaker.scalarPi π hπ ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![π ^ n, 0; 0, π ^ n] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, scalarPi_coe]
    simp [pow_succ]

private theorem scalarPi_inv (π : K) (hπ : π ≠ 0) :
    (UnramifiedWhittaker.scalarPi π hπ)⁻¹ = UnramifiedWhittaker.scalarPi π⁻¹ (inv_ne_zero hπ) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, scalarPi_coe, scalarPi_coe, Units.val_one]
  simp [mul_inv_cancel₀ hπ, Matrix.one_fin_two]

private theorem scalarPi_zpow_coe (π : K) (hπ : π ≠ 0) (m : ℤ) :
    ((UnramifiedWhittaker.scalarPi π hπ ^ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![π ^ m, 0; 0, π ^ m] := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, scalarPi_pow_coe]; simp
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow, scalarPi_inv, scalarPi_pow_coe]
    simp [zpow_negSucc, inv_pow]

private theorem torus_coe (π : K) (hπ : π ≠ 0) (m₁ m₂ : ℤ) :
    ((UnramifiedWhittaker.diagZ π hπ (m₁ - m₂) * UnramifiedWhittaker.scalarPi π hπ ^ m₂ :
        GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![π ^ m₁, 0; 0, π ^ m₂] := by
  have h : π ^ (m₁ - m₂) * π ^ m₂ = π ^ m₁ := by rw [← zpow_add₀ hπ, sub_add_cancel]
  rw [Units.val_mul, diagZ_coe, scalarPi_zpow_coe]
  simp [h]

private theorem torus_coe_pair (π : K) (hπ : π ≠ 0) (p : ℤ × ℤ) :
    ((UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2 :
        GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![π ^ p.1, 0; 0, π ^ p.2] :=
  torus_coe π hπ p.1 p.2

section Disjoint

open scoped WithZero

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰]

private theorem valued_zpow_of_uniformizer {π : F} (hπ1 : Valued.v π = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    Valued.v (π ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hπ1, ← WithZero.exp_zsmul]
  simp

private theorem mul_max_eq (c a b : ℤᵐ⁰) : max (c * a) (c * b) = c * max a b := by
  have hm : Monotone (fun t : ℤᵐ⁰ => c * t) := fun _ _ h => mul_le_mul_right h c
  exact (Monotone.map_max hm).symm

private theorem max_bottom_row_eq_one (k : Matrix (Fin 2) (Fin 2) F)
    (hk : ∀ i j, Valued.v (k i j) ≤ 1) (hdet : Valued.v k.det = 1) :
    max (Valued.v (k 1 0)) (Valued.v (k 1 1)) = 1 := by
  refine le_antisymm (max_le (hk 1 0) (hk 1 1)) ?_
  by_contra hlt
  rw [not_le, max_lt_iff] at hlt
  obtain ⟨h10, h11⟩ := hlt
  have h00 := hk 0 0
  have h01 := hk 0 1
  have h1 : Valued.v (k 0 0 * k 1 1) < 1 := by
    rw [map_mul]
    calc Valued.v (k 0 0) * Valued.v (k 1 1) ≤ 1 * Valued.v (k 1 1) := by gcongr
      _ < 1 := by rw [one_mul]; exact h11
  have h2 : Valued.v (k 0 1 * k 1 0) < 1 := by
    rw [map_mul]
    calc Valued.v (k 0 1) * Valued.v (k 1 0) ≤ 1 * Valued.v (k 1 0) := by gcongr
      _ < 1 := by rw [one_mul]; exact h10
  have hd : Valued.v k.det < 1 := by
    rw [Matrix.det_fin_two]
    exact lt_of_le_of_lt (Valued.v.map_sub _ _) (max_lt h1 h2)
  rw [hdet] at hd
  exact lt_irrefl _ hd

variable (π : F) (hπ : π ≠ 0)

omit [Valued F ℤᵐ⁰] in

private theorem cell_bottom_row (p : ℤ × ℤ) (x : F) (k : GL (Fin 2) F) (j : Fin 2) :
    ((AutomorphicForm.unipotentGL2 x *
        (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) * k :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j =
      π ^ p.2 * (k : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Units.val_mul, Units.val_mul, AutomorphicForm.unipotentGL2_coe, torus_coe_pair]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem valued_det_cell (hπ1 : Valued.v π = WithZero.exp (-1 : ℤ)) (p : ℤ × ℤ) (x : F) (k : GL (Fin 2) F)
    (hdet : Valued.v (k : Matrix (Fin 2) (Fin 2) F).det = 1) :
    Valued.v ((AutomorphicForm.unipotentGL2 x *
        (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) * k :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = WithZero.exp (-(p.1 + p.2)) := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, AutomorphicForm.unipotentGL2_coe,
    torus_coe_pair, map_mul, map_mul, hdet]
  simp only [Matrix.det_fin_two_of, mul_zero, sub_zero, mul_one, one_mul, map_mul, map_one,
    valued_zpow_of_uniformizer hπ1, ← WithZero.exp_add, neg_add]

private theorem max_valued_bottom_row_cell (hπ1 : Valued.v π = WithZero.exp (-1 : ℤ)) (p : ℤ × ℤ) (x : F)
    (k : GL (Fin 2) F) (hk : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1)
    (hdet : Valued.v (k : Matrix (Fin 2) (Fin 2) F).det = 1) :
    max (Valued.v (((AutomorphicForm.unipotentGL2 x *
          (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) * k :
          GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0))
        (Valued.v (((AutomorphicForm.unipotentGL2 x *
          (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) * k :
          GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1)) =
      WithZero.exp (-p.2) := by
  rw [cell_bottom_row, cell_bottom_row, map_mul, map_mul, mul_max_eq, max_bottom_row_eq_one _ hk hdet,
    mul_one, valued_zpow_of_uniformizer hπ1]

private theorem cell_index_eq (hπ1 : Valued.v π = WithZero.exp (-1 : ℤ)) {p p' : ℤ × ℤ} {x x' : F}
    {k k' : GL (Fin 2) F} (hk : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1)
    (hdet : Valued.v (k : Matrix (Fin 2) (Fin 2) F).det = 1)
    (hk' : ∀ i j, Valued.v ((k' : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1)
    (hdet' : Valued.v (k' : Matrix (Fin 2) (Fin 2) F).det = 1)
    (h : AutomorphicForm.unipotentGL2 x *
          (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) * k =
        AutomorphicForm.unipotentGL2 x' *
          (UnramifiedWhittaker.diagZ π hπ (p'.1 - p'.2) * UnramifiedWhittaker.scalarPi π hπ ^ p'.2) * k') :
    p = p' := by
  have h1 := valued_det_cell π hπ hπ1 p x k hdet
  have h2 := max_valued_bottom_row_cell π hπ hπ1 p x k hk hdet
  rw [h] at h1 h2
  rw [valued_det_cell π hπ hπ1 p' x' k' hdet', WithZero.exp_inj] at h1
  rw [max_valued_bottom_row_cell π hπ hπ1 p' x' k' hk' hdet', WithZero.exp_inj] at h2
  exact Prod.ext (by omega) (by omega)

end Disjoint

section Factorisation

open scoped WithZero
open IsDedekindDomain NumberField

variable {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}

private theorem exists_zpow_mul_unit {ϖ : v.adicCompletion ℚ} (hϖ1 : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (x : v.adicCompletion ℚ) (hx : x ≠ 0) :
    ∃ (m : ℤ) (u : (v.adicCompletionIntegers ℚ)ˣ),
      x = ϖ ^ m * ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ1
    exact WithZero.exp_ne_zero hϖ1.symm
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  set m : ℤ := -WithZero.log (Valued.v x) with hm
  have hpow : Valued.v (ϖ ^ m) = Valued.v x := by
    rw [map_zpow₀, hϖ1, ← WithZero.exp_zsmul, ← WithZero.exp_log hvx]
    congr 1
    rw [hm]
    simp
  have hpow0 : ϖ ^ m ≠ 0 := zpow_ne_zero m hϖ0
  set w : v.adicCompletion ℚ := x / ϖ ^ m with hw
  have hvw : Valued.v w = 1 := by
    rw [hw, map_div₀, hpow, div_self hvx]
  have hwmem : w ∈ v.adicCompletionIntegers ℚ := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hvw]
  have hunit : IsUnit (⟨w, hwmem⟩ : v.adicCompletionIntegers ℚ) :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hvw
  obtain ⟨u, hu⟩ := hunit
  refine ⟨m, u, ?_⟩
  rw [hu]
  show x = ϖ ^ m * w
  rw [hw, mul_div_cancel₀ x hpow0]

end Factorisation

end LanglandsTunnell.RankinSelberg.FinIwasawaProof.TorusConj

namespace LanglandsTunnell
namespace RankinSelberg
namespace FinIwasawaProof
namespace UnipotentMass

open IsDedekindDomain NumberField
open scoped WithZero

open MeasureTheory Matrix AutomorphicForm
open scoped ENNReal Pointwise

section Entry

variable {F : Type*} [Field F]

set_option quotPrecheck false in
local notation "N" => (AutomorphicForm.unipotentGL2Hom (R := F)).range

private def entry (n : N) : F := ((n : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1

private theorem unipotentGL2_mem (x : F) : unipotentGL2 x ∈ N := ⟨Multiplicative.ofAdd x, rfl⟩

private def up (x : F) : N := ⟨unipotentGL2 x, unipotentGL2_mem x⟩

@[scoped simp] private theorem entry_up (x : F) : entry (up x) = x := by
  simp [entry, up]

private theorem up_entry (n : N) : up (entry n) = n := by
  obtain ⟨g, y, rfl⟩ := n
  apply Subtype.ext
  show unipotentGL2 _ = unipotentGL2Hom y
  simp only [entry]
  rfl

private theorem entry_injective : Function.Injective (entry (F := F)) := fun n m h => by
  rw [← up_entry n, ← up_entry m, h]

private theorem up_add (x y : F) : up (x + y) = up x * up y :=
  Subtype.ext (unipotentGL2_add x y)

private theorem entry_mul (n m : N) : entry (n * m) = entry n + entry m := by
  rw [← up_entry n, ← up_entry m, ← up_add, entry_up, entry_up, entry_up]

variable [TopologicalSpace F]

private theorem continuous_entry : Continuous (entry (F := F)) :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 1

variable [IsTopologicalRing F]

private theorem continuous_unipotentGL2 : Continuous (unipotentGL2 (R := F)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop

private theorem continuous_up : Continuous (up (F := F)) :=
  continuous_unipotentGL2.subtype_mk _

private def upHomeomorph : F ≃ₜ N where
  toFun := up
  invFun := entry
  left_inv := entry_up
  right_inv := up_entry
  continuous_toFun := continuous_up
  continuous_invFun := continuous_entry

private def scaleEntry (a : F) (ha : a ≠ 0) : N ≃ₜ* N where
  toFun n := up (a * entry n)
  invFun n := up (a⁻¹ * entry n)
  left_inv n := by simp [ha, up_entry]
  right_inv n := by simp [ha, up_entry]
  map_mul' n m := by
    rw [entry_mul, mul_add, up_add]
  continuous_toFun := continuous_up.comp (continuous_const.mul continuous_entry)
  continuous_invFun := continuous_up.comp (continuous_const.mul continuous_entry)

@[scoped simp] private theorem scaleEntry_apply (a : F) (ha : a ≠ 0) (n : N) : scaleEntry a ha n = up (a * entry n) := rfl

private theorem entry_scaleEntry (a : F) (ha : a ≠ 0) (n : N) : entry (scaleEntry a ha n) = a * entry n := by
  simp

end Entry

section Generic

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private theorem map_eq_smul_of_conj (μX : Measure X) (μY : Measure Y) {e : X → Y} (he : Measurable e)
    (hμY : μX.map e = μY)
    {ψ : X → X} (hψ : Measurable ψ) {φ : Y → Y} (hφ : Measurable φ) (hconj : φ ∘ e = e ∘ ψ) (c : ℝ≥0∞)
    (hscale : μX.map ψ = c • μX) : μY.map φ = c • μY := by
  rw [← hμY, Measure.map_map hφ he, hconj, ← Measure.map_map he hψ, hscale, Measure.map_smul]

end Generic

section GenericGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private theorem map_eq_smul_of_apply (μ : Measure G) [μ.IsHaarMeasure] (φ : G ≃ₜ* G) {U : Set G} (hU : MeasurableSet U)
    (hU0 : μ U ≠ 0) (hUtop : μ U ≠ ⊤) (c : ℝ≥0∞) (hc : μ ((φ : G → G) ⁻¹' U) = c * μ U) :
    μ.map (φ : G → G) = c • μ := by
  haveI : (μ.map (φ : G → G)).IsHaarMeasure := φ.isHaarMeasure_map μ
  have hφm : Measurable (φ : G → G) := φ.continuous.measurable
  have hd : μ.map (φ : G → G) = (((μ.map (φ : G → G)).haarScalarFactor μ : NNReal) : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have hmapU : (μ.map (φ : G → G)) U = c * μ U := by
    rw [Measure.map_apply hφm hU, hc]
  rw [hd, Measure.smul_apply, smul_eq_mul] at hmapU
  have hdc : ((((μ.map (φ : G → G)).haarScalarFactor μ : NNReal)) : ℝ≥0∞) = c :=
    (ENNReal.mul_left_inj hU0 hUtop).mp hmapU
  rw [hd, hdc]

end GenericGroup

section GenericIndex

variable {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]

private theorem measure_eq_card_quotient_mul (μ : Measure A) [μ.IsAddLeftInvariant] (B C : AddSubgroup A) (hCB : C ≤ B)
    (hC : MeasurableSet (C : Set A)) [Finite (B ⧸ C.addSubgroupOf B)] :
    μ (B : Set A) = Nat.card (B ⧸ C.addSubgroupOf B) * μ (C : Set A) := by
  classical
  haveI : Fintype (B ⧸ C.addSubgroupOf B) := Fintype.ofFinite _
  let r : B ⧸ C.addSubgroupOf B → A := fun q => ((Quotient.out q : B) : A)
  have hcover : (B : Set A) = ⋃ q : B ⧸ C.addSubgroupOf B, (r q +ᵥ (C : Set A)) := by
    ext a
    constructor
    · intro ha
      set q : B ⧸ C.addSubgroupOf B := QuotientAddGroup.mk (⟨a, ha⟩ : B) with hq
      refine Set.mem_iUnion.mpr ⟨q, ?_⟩
      have hmem : -(Quotient.out q : B) + ⟨a, ha⟩ ∈ C.addSubgroupOf B :=
        QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.mk, Quotient.out_eq'])
      rw [AddSubgroup.mem_addSubgroupOf] at hmem
      refine ⟨-(r q) + a, hmem, ?_⟩
      simp [r, vadd_eq_add]
    · intro ha
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp ha
      obtain ⟨c, hc, rfl⟩ := hq
      exact B.add_mem (Quotient.out q).2 (hCB hc)
  have hdisj : Pairwise (Function.onFun Disjoint fun q : B ⧸ C.addSubgroupOf B => r q +ᵥ (C : Set A)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro a ⟨c, hc, rfl⟩ ⟨c', hc', he⟩
    apply hqq'
    have hmem : -(Quotient.out q : B) + (Quotient.out q' : B) ∈ C.addSubgroupOf B := by
      rw [AddSubgroup.mem_addSubgroupOf]
      have : -(r q) + r q' = c + -c' := by
        simp only [vadd_eq_add] at he
        have h2 : r q' = r q + c - c' := by
          rw [eq_sub_iff_add_eq]
          exact he
        rw [h2]
        abel
      simpa [r] using this ▸ C.add_mem hc (C.neg_mem hc')
    have := QuotientAddGroup.eq.mpr hmem
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
  rw [hcover, measure_iUnion hdisj fun q => hC.const_vadd (r q)]
  simp only [measure_vadd, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

end GenericIndex

section GenericScaling

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F]

private theorem map_mul_zpow_eq_smul (μ : Measure F) {a : F} (ha : a ≠ 0) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤)
    (h : μ.map (fun x => a * x) = c • μ) (k : ℤ) : μ.map (fun x => a ^ k * x) = c ^ k • μ := by
  have hm : ∀ b : F, Measurable (fun x : F => b * x) := fun b => (continuous_const.mul continuous_id).measurable
  have hnat : ∀ n : ℕ, μ.map (fun x => a ^ n * x) = c ^ n • μ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcomp : (fun x : F => a ^ (n + 1) * x) = (fun x => a * x) ∘ fun x => a ^ n * x := by
        funext x
        simp [pow_succ, mul_assoc, mul_comm a]
      rw [hcomp, ← Measure.map_map (hm a) (hm (a ^ n)), ih, Measure.map_smul, h, smul_smul, pow_succ]
  have hinv : μ.map (fun x => a⁻¹ * x) = c⁻¹ • μ := by
    have h1 : (μ.map fun x => a * x).map (fun x => a⁻¹ * x) = μ := by
      rw [Measure.map_map (hm a⁻¹) (hm a)]
      have : ((fun x : F => a⁻¹ * x) ∘ fun x => a * x) = id := by
        funext x
        simp [ha]
      rw [this, Measure.map_id]
    rw [h, Measure.map_smul] at h1
    calc μ.map (fun x => a⁻¹ * x) = c⁻¹ • (c • μ.map fun x => a⁻¹ * x) := by
          rw [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul]
      _ = c⁻¹ • μ := by rw [h1]
  rcases k with n | n
  · simpa using hnat n
  · have hcomp : (fun x : F => a ^ (Int.negSucc n) * x) = (fun x => a⁻¹ * x)^[n + 1] := by
      funext x
      rw [zpow_negSucc, ← inv_pow]
      induction n generalizing x with
      | zero => simp
      | succ m ihm =>
        rw [Function.iterate_succ_apply, ← ihm, pow_succ]
        ring
    rw [hcomp, zpow_negSucc, ENNReal.inv_pow]
    have hit : ∀ m : ℕ, μ.map ((fun x : F => a⁻¹ * x)^[m]) = (c⁻¹) ^ m • μ := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        have hitm : Measurable ((fun x : F => a⁻¹ * x)^[m]) := (hm a⁻¹).iterate m
        rw [Function.iterate_succ', ← Measure.map_map (hm a⁻¹) hitm, ihm, Measure.map_smul, hinv, smul_smul,
          pow_succ]
    exact hit (n + 1)

end GenericScaling

section M2

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
  [SecondCountableTopology F] [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]

set_option quotPrecheck false in
local notation "N" => (AutomorphicForm.unipotentGL2Hom (R := F)).range

private scoped instance : LocallyCompactSpace N := (upHomeomorph (F := F)).locallyCompactSpace_iff.mp inferInstance

private scoped instance : SecondCountableTopology N := (upHomeomorph (F := F)).symm.isInducing.secondCountableTopology

private theorem map_scaleEntry_zpow (μN : Measure N) [μN.IsHaarMeasure] {a : F} (ha : a ≠ 0) (B C : AddSubgroup F)
    (hBopen : IsOpen (B : Set F)) (hBcompact : IsCompact (B : Set F)) (hCset : (C : Set F) = (fun x => a * x) '' B)
    (hCB : C ≤ B) [Finite (B ⧸ C.addSubgroupOf B)] {q : ℕ} (hq0 : q ≠ 0) (hq : Nat.card (B ⧸ C.addSubgroupOf B) = q)
    (k : ℤ) : μN.map (scaleEntry (a ^ k) (zpow_ne_zero k ha) : N → N) = (q : ℝ≥0∞) ^ k • μN := by

  borelize F
  have hCopen : IsOpen (C : Set F) := by
    rw [hCset]
    exact (Homeomorph.mulLeft₀ a ha).isOpenMap _ hBopen
  have hCcompact : IsCompact (C : Set F) := by
    rw [hCset]
    exact hBcompact.image (continuous_const.mul continuous_id)
  have hentry : Measurable (entry (F := F)) := continuous_entry.measurable
  have hup : Measurable (up (F := F)) := continuous_up.measurable

  set lam : Measure F := μN.map entry with hlam
  haveI : lam.IsAddLeftInvariant := by
    refine ⟨fun g => ?_⟩
    have hadd : Measurable (fun x : F => g + x) := (continuous_const.add continuous_id).measurable
    have hcomp : ((fun x : F => g + x) ∘ entry) = entry ∘ (fun n : N => up g * n) := by
      funext n
      simp [entry_mul]
    rw [hlam, Measure.map_map hadd hentry, hcomp, ← Measure.map_map hentry (measurable_const_mul (up g)),
      map_mul_left_eq_self]

  have hindex : lam (B : Set F) = q * lam (C : Set F) := by
    rw [measure_eq_card_quotient_mul lam B C hCB hCopen.measurableSet, hq]

  set U : Set N := entry ⁻¹' (C : Set F) with hU
  have hUmeas : MeasurableSet U := hentry hCopen.measurableSet
  have hU_eq : μN U = lam (C : Set F) := by
    rw [hlam, Measure.map_apply hentry hCopen.measurableSet]
  have hBpre : μN (entry ⁻¹' (B : Set F)) = lam (B : Set F) := by
    rw [hlam, Measure.map_apply hentry hBopen.measurableSet]
  have hU0 : μN U ≠ 0 := by
    refine (IsOpen.measure_pos μN (hCopen.preimage continuous_entry) ⟨up 0, ?_⟩).ne'
    show entry (up 0) ∈ (C : Set F)
    rw [entry_up]
    exact C.zero_mem
  have hUtop : μN U ≠ ⊤ := by
    have hUc : IsCompact U := (upHomeomorph (F := F)).symm.isCompact_preimage.mpr hCcompact
    exact hUc.measure_lt_top.ne

  have hpre : (scaleEntry a ha : N → N) ⁻¹' U = entry ⁻¹' (B : Set F) := by
    ext n
    simp only [Set.mem_preimage, hU]
    rw [show entry ((scaleEntry a ha : N → N) n) = a * entry n from entry_scaleEntry a ha n, hCset]
    constructor
    · rintro ⟨b, hb, hab⟩
      rwa [mul_left_cancel₀ ha hab] at hb
    · intro hn
      exact ⟨entry n, hn, rfl⟩

  have hbase : μN.map (scaleEntry a ha : N → N) = (q : ℝ≥0∞) • μN := by
    refine map_eq_smul_of_apply μN (scaleEntry a ha) hUmeas hU0 hUtop q ?_
    rw [hpre, hBpre, hindex, hU_eq]
  have hlam_scale : lam.map (fun x => a * x) = (q : ℝ≥0∞) • lam :=
    map_eq_smul_of_conj μN lam hentry rfl (scaleEntry a ha).continuous.measurable
      (continuous_const.mul continuous_id).measurable (by
        funext n
        show a * entry n = entry (up (a * entry n))
        rw [entry_up]) _ hbase
  have hlam_pow : lam.map (fun x => a ^ k * x) = (q : ℝ≥0∞) ^ k • lam :=
    map_mul_zpow_eq_smul lam ha (by exact_mod_cast hq0) (ENNReal.natCast_ne_top q) hlam_scale k
  have hup_lam : lam.map up = μN := by
    rw [hlam, Measure.map_map hup hentry]
    have : (up ∘ entry : N → N) = id := funext up_entry
    rw [this, Measure.map_id]
  exact map_eq_smul_of_conj lam μN hup hup_lam (continuous_const.mul continuous_id).measurable
    (scaleEntry (a ^ k) (zpow_ne_zero k ha)).continuous.measurable
    (by
      funext x
      show up (a ^ k * entry (up x)) = up (a ^ k * x)
      rw [entry_up]) _ hlam_pow

end M2

section Instance

open IsDedekindDomain NumberField ResidueIndexAmbient

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem coe_integersAdd : ((integersAdd v : AddSubgroup (v.adicCompletion ℚ)) : Set (v.adicCompletion ℚ)) =
    (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  rfl

private theorem coe_scaledIntegersAdd (ϖ : v.adicCompletion ℚ) :
    ((scaledIntegersAdd ϖ : AddSubgroup (v.adicCompletion ℚ)) : Set (v.adicCompletion ℚ)) =
      (fun x => ϖ * x) '' (integersAdd v : Set (v.adicCompletion ℚ)) := by
  rw [scaledIntegersAdd, AddSubgroup.coe_map, AddMonoidHom.coe_mulLeft]

private theorem isOpen_integersAdd :
    IsOpen ((integersAdd v : AddSubgroup (v.adicCompletion ℚ)) : Set (v.adicCompletion ℚ)) := by
  rw [coe_integersAdd]
  exact (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out v

private theorem isCompact_integersAdd :
    IsCompact ((integersAdd v : AddSubgroup (v.adicCompletion ℚ)) : Set (v.adicCompletion ℚ)) := by
  rw [coe_integersAdd]
  exact isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 ℚ) ℚ v)

private theorem absNorm_ne_zero : Ideal.absNorm v.asIdeal ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

set_option quotPrecheck false in
local notation "Nv" => (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range

private theorem map_scaleEntry_uniformizer [SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ))]
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
    ∀ (μN : Measure Nv) [μN.IsHaarMeasure] (p : ℤ × ℤ),
      μN.map (scaleEntry (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ (p.1 - p.2))
          (zpow_ne_zero _ hπ) : Nv → Nv) =
        (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (p.1 - p.2) • μN := by
  intro μN _ p
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := ⟨rfl⟩
  haveI : SecondCountableTopology (v.adicCompletion ℚ) :=
    (upHomeomorph (F := v.adicCompletion ℚ)).isInducing.secondCountableTopology
  haveI := finite_integersAdd_quot_scaled hϖ
  exact map_scaleEntry_zpow μN hπ (integersAdd v) (scaledIntegersAdd _) isOpen_integersAdd isCompact_integersAdd
    (coe_scaledIntegersAdd _) (scaledIntegersAdd_le ϖ) absNorm_ne_zero (natCard_integersAdd_quot_scaled hϖ) _

private theorem coe_eq_unipotentGL2_entry (x : Nv) :
    (x : GL (Fin 2) (v.adicCompletion ℚ)) = AutomorphicForm.unipotentGL2 (entry x) := by
  conv_lhs => rw [← up_entry x]
  rfl

private theorem torus_mul_coe {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (p : ℤ × ℤ) (x : Nv) :
    UnramifiedWhittaker.diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
          UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2 *
        (x : GL (Fin 2) (v.adicCompletion ℚ)) =
      ((scaleEntry (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ (p.1 - p.2))
            (zpow_ne_zero _ hπ) x : Nv) : GL (Fin 2) (v.adicCompletion ℚ)) *
        (UnramifiedWhittaker.diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
          UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) := by
  rw [coe_eq_unipotentGL2_entry x]
  exact TorusConj.torus_mul_unipotentGL2 _ hπ p (entry x)

end Instance

end LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell"

namespace LanglandsTunnell
namespace RankinSelberg
namespace FinIwasawaProof
namespace IwasawaCover

open Matrix NumberField

variable {F : Type*} [Field F] (O : ValuationSubring F)

private def IsIntegralUnit (k : GL (Fin 2) F) : Prop :=
  (∀ i j, (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O) ∧ ∀ i j, ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O

variable {O}

private def mkUnit (m n : Matrix (Fin 2) (Fin 2) F) (h₁ : m * n = 1) (h₂ : n * m = 1) : GL (Fin 2) F :=
  ⟨m, n, h₁, h₂⟩

private theorem mkUnit_coe (m n : Matrix (Fin 2) (Fin 2) F) (h₁ : m * n = 1) (h₂ : n * m = 1) :
    ((mkUnit m n h₁ h₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = m := rfl

private theorem mkUnit_inv_coe (m n : Matrix (Fin 2) (Fin 2) F) (h₁ : m * n = 1) (h₂ : n * m = 1) :
    (((mkUnit m n h₁ h₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = n := rfl

private def shear (y : F) : GL (Fin 2) F :=
  mkUnit !![1, 0; y, 1] !![1, 0; -y, 1]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

private theorem shear_isIntegralUnit {y : F} (hy : y ∈ O) : IsIntegralUnit O (shear y) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [shear, mkUnit_coe]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · simp only [shear, mkUnit_inv_coe]
    fin_cases i <;> fin_cases j <;> simp [neg_mem hy]

private def swap : GL (Fin 2) F :=
  mkUnit !![0, 1; 1, 0] !![0, 1; 1, 0]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

private theorem swap_isIntegralUnit : IsIntegralUnit O (swap (F := F)) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [swap, mkUnit_coe]
    fin_cases i <;> fin_cases j <;> simp
  · simp only [swap, mkUnit_inv_coe]
    fin_cases i <;> fin_cases j <;> simp

private def diagUnits (u₁ u₂ : Oˣ) : GL (Fin 2) F :=
  mkUnit !![((u₁ : O) : F), 0; 0, ((u₂ : O) : F)] !![((u₁⁻¹ : Oˣ) : O), 0; 0, ((u₂⁻¹ : Oˣ) : O)]
    (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first
        | exact_mod_cast (congrArg (fun x : O => (x : F)) (Units.mul_inv u₁))
        | exact_mod_cast (congrArg (fun x : O => (x : F)) (Units.mul_inv u₂)))
    (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first
        | exact_mod_cast (congrArg (fun x : O => (x : F)) (Units.inv_mul u₁))
        | exact_mod_cast (congrArg (fun x : O => (x : F)) (Units.inv_mul u₂)))

private theorem diagUnits_isIntegralUnit (u₁ u₂ : Oˣ) : IsIntegralUnit O (diagUnits u₁ u₂) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [diagUnits, mkUnit_coe]
    fin_cases i <;> fin_cases j <;> simp
  · simp only [diagUnits, mkUnit_inv_coe]
    fin_cases i <;> fin_cases j <;> simp

private theorem isOpen_setOf_isIntegralUnit [TopologicalSpace F] [IsTopologicalRing F] (hO : IsOpen (O : Set F)) :
    IsOpen {k : GL (Fin 2) F | IsIntegralUnit O k} := by
  have h1 : ∀ i j : Fin 2, IsOpen {k : GL (Fin 2) F | (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O} := fun i j =>
    hO.preimage (Units.continuous_val.matrix_elem i j)
  have h2 : ∀ i j : Fin 2, IsOpen {k : GL (Fin 2) F | ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O} :=
    fun i j => hO.preimage (Units.continuous_coe_inv.matrix_elem i j)
  have hset : {k : GL (Fin 2) F | IsIntegralUnit O k} =
      (⋂ i, ⋂ j, {k : GL (Fin 2) F | (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O}) ∩
        ⋂ i, ⋂ j, {k : GL (Fin 2) F | ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O} := by
    ext k
    simp only [IsIntegralUnit, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h1 i j).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h2 i j)

private theorem det_mem {m : Matrix (Fin 2) (Fin 2) F} (hm : ∀ i j, m i j ∈ O) : m.det ∈ O := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hm 0 0) (hm 1 1)) (mul_mem (hm 0 1) (hm 1 0))

private theorem det_mul_det_inv (k : GL (Fin 2) F) :
    (k : Matrix (Fin 2) (Fin 2) F).det * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

private theorem eq_one_of_mul_eq_one_of_le_one {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] {a b : Γ} (ha : a ≤ 1)
    (hb : b ≤ 1) (hab : a * b = 1) : a = 1 :=
  le_antisymm ha (by calc (1 : Γ) = a * b := hab.symm
    _ ≤ a * 1 := mul_le_mul_right hb a
    _ = a := mul_one a)

section Cover

variable (O)

private theorem exists_triangular (K : Subgroup (GL (Fin 2) F)) (hK : ∀ k, k ∈ K ↔ IsIntegralUnit O k)
    (g : GL (Fin 2) F) :
    ∃ k₁ ∈ K, ∃ α β δ : F, α ≠ 0 ∧ δ ≠ 0 ∧ ((g * k₁ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![α, β; 0, δ] := by
  set a : F := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b : F := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c : F := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d : F := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hg : (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := Matrix.eta_fin_two _
  have hdet : a * d - b * c ≠ 0 := by
    have h := (Matrix.isUnits_det_units g).ne_zero
    rwa [hg, Matrix.det_fin_two_of] at h
  by_cases hd0 : d = 0
  ·
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hdet
      rw [hd0, hc0]
      ring
    have hb0 : b ≠ 0 := by
      intro hb0
      apply hdet
      rw [hd0, hb0]
      ring
    refine ⟨swap, (hK _).mpr swap_isIntegralUnit, b, a, c, hb0, hc0, ?_⟩
    rw [Units.val_mul, hg, hd0]
    simp only [swap, mkUnit_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · by_cases hcd : c / d ∈ O
    ·
      refine ⟨shear (-(c / d)), (hK _).mpr (shear_isIntegralUnit (neg_mem hcd)), a - b * (c / d), b, d, ?_, hd0, ?_⟩
      · intro h0
        apply hdet
        have : a - b * (c / d) = (a * d - b * c) / d := by
          field_simp
        rw [this, div_eq_zero_iff] at h0
        exact h0.resolve_right hd0
      · rw [Units.val_mul, hg]
        simp only [shear, mkUnit_coe]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
    ·
      have hdc : (c / d)⁻¹ ∈ O := (O.mem_or_inv_mem (c / d)).resolve_left hcd
      have hc0 : c ≠ 0 := by
        intro hc0
        apply hcd
        rw [hc0, zero_div]
        exact zero_mem _
      rw [inv_div] at hdc
      refine ⟨swap * shear (-(d / c)), K.mul_mem ((hK _).mpr swap_isIntegralUnit)
        ((hK _).mpr (shear_isIntegralUnit (neg_mem hdc))), b - a * (d / c), a, c, ?_, hc0, ?_⟩
      · intro h0
        apply hdet
        have : b - a * (d / c) = -(a * d - b * c) / c := by
          field_simp
          ring
        rw [this, div_eq_zero_iff, neg_eq_zero] at h0
        exact h0.resolve_right hc0
      · rw [← mul_assoc, Units.val_mul, Units.val_mul, hg]
        simp only [swap, shear, mkUnit_coe]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

private theorem exists_cover (K : Subgroup (GL (Fin 2) F)) (hK : ∀ k, k ∈ K ↔ IsIntegralUnit O k) {ϖ : F}
    (hfac : ∀ x : F, x ≠ 0 → ∃ (m : ℤ) (u : Oˣ), x = ϖ ^ m * ((u : O) : F)) (g : GL (Fin 2) F) :
    ∃ (x : F) (m : ℤ × ℤ) (k : GL (Fin 2) F), k ∈ K ∧
      (g : Matrix (Fin 2) (Fin 2) F) =
        !![1, x; 0, 1] * !![ϖ ^ m.1, 0; 0, ϖ ^ m.2] * (k : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨k₁, hk₁, α, β, δ, hα, hδ, htri⟩ := exists_triangular O K hK g
  obtain ⟨m₁, u₁, hu₁⟩ := hfac α hα
  obtain ⟨m₂, u₂, hu₂⟩ := hfac δ hδ
  refine ⟨β / δ, (m₁, m₂), diagUnits u₁ u₂ * k₁⁻¹,
    K.mul_mem ((hK _).mpr (diagUnits_isIntegralUnit u₁ u₂)) (K.inv_mem hk₁), ?_⟩

  have hfactor : !![α, β; 0, δ] =
      !![1, β / δ; 0, 1] * !![ϖ ^ m₁, 0; 0, ϖ ^ m₂] *
        ((diagUnits u₁ u₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have hϖ₂ : ϖ ^ m₂ ≠ 0 := left_ne_zero_of_mul (hu₂ ▸ hδ)
    simp only [diagUnits, mkUnit_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu₁, hu₂]
    field_simp
  have hg : (g : Matrix (Fin 2) (Fin 2) F) =
      ((g * k₁ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((k₁⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, mul_inv_cancel_right]
  rw [hg, htri, hfactor, Units.val_mul, Matrix.mul_assoc]

end Cover
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

section Bench

open IsDedekindDomain AdelicDock

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isLocalLevelOne_top_iff (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ := by
  refine ⟨fun h => h.integral, fun h => ⟨h, ?_, ?_⟩⟩
  · rw [AdelicLevel.idealBound_top]
    have := h 1 0
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
  · rw [AdelicLevel.idealBound_top]
    have := sub_mem (h 1 1) (one_mem (v.adicCompletionIntegers ℚ))
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

private theorem mem_localLevelOne_top_iff (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ ↔ IsIntegralUnit (v.adicCompletionIntegers ℚ) k := by
  rw [mem_localLevelOne_iff, isLocalLevelOne_top_iff, isLocalLevelOne_top_iff]
  exact Iff.rfl

private theorem valued_apply_le_one_of_mem {k : GL (Fin 2) (v.adicCompletion ℚ)} (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (i j : Fin 2) : Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1 := by
  have := ((mem_localLevelOne_top_iff v k).mp hk).1 i j
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

private theorem valued_det_eq_one_of_mem {k : GL (Fin 2) (v.adicCompletion ℚ)} (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
  obtain ⟨h₁, h₂⟩ := (mem_localLevelOne_top_iff v k).mp hk
  have hd₁ := det_mem h₁
  have hd₂ := det_mem h₂
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd₁ hd₂
  exact eq_one_of_mul_eq_one_of_le_one hd₁ hd₂ (by rw [← map_mul, det_mul_det_inv, map_one])

private theorem exists_cover_localLevelOne {ϖ : v.adicCompletion ℚ}
    (hfac : ∀ x : v.adicCompletion ℚ, x ≠ 0 → ∃ (m : ℤ) (u : (v.adicCompletionIntegers ℚ)ˣ),
      x = ϖ ^ m * ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ))
    (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    ∃ (x : v.adicCompletion ℚ) (m : ℤ × ℤ) (k : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ ∧
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
        !![1, x; 0, 1] * !![ϖ ^ m.1, 0; 0, ϖ ^ m.2] * (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
  exists_cover (v.adicCompletionIntegers ℚ) _ (mem_localLevelOne_top_iff v) hfac g

end Bench
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

end LanglandsTunnell.RankinSelberg.FinIwasawaProof.IwasawaCover
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

namespace LanglandsTunnell
namespace RankinSelberg
namespace FinIwasawaProof
namespace DensNorm

open MeasureTheory HaarQuotient
open scoped ENNReal Pointwise

section Norm

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SigmaCompactSpace G] [WeaklyLocallyCompactSpace G]
  (H : Subgroup G) (μH : Measure H)

private def coeff (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ n *
    (1 + μH (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹

omit [IsTopologicalGroup G] [BorelSpace G] in
private theorem weight_eq (g : G) :
    weight H μH g = ∑' n : ℕ,
      coeff H μH n * (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g := by
  unfold HaarQuotient.weight
  rw [dif_pos ⟨inferInstance, inferInstance⟩]
  rfl

omit [IsTopologicalGroup G] [BorelSpace G] in
private theorem coeff_le (n : ℕ) : coeff H μH n ≤ (2⁻¹ : ℝ≥0∞) ^ n :=
  mul_le_of_le_one_right (by simp) (ENNReal.inv_le_one.mpr le_self_add)

private theorem lintegral_term_le [μH.IsMulRightInvariant] (n : ℕ) (g : G) :
    ∫⁻ x : H, coeff H μH n *
        (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) ∂μH ≤
      (2⁻¹ : ℝ≥0∞) ^ n := by
  set E : Set G := CompactExhaustion.choice G (n + 1) with hE
  set U : Set H := {x : H | (x : G) * g ∈ interior E} with hU
  have hUmeas : MeasurableSet U :=
    (isOpen_interior.preimage (continuous_subtype_val.mul continuous_const)).measurableSet
  have hfun : (fun x : H => coeff H μH n * (interior E).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g)) =
      fun x : H => U.indicator (fun _ => coeff H μH n) x := by
    funext x
    by_cases hx : x ∈ U
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (show (x : G) * g ∈ interior E from hx)]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (x : G) * g ∉ interior E from hx)]
  rw [hfun, lintegral_indicator_const hUmeas]

  by_cases hne : U = ∅
  · simp [hne]
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hsub : U ⊆ (fun x : H => x * x₀⁻¹) ⁻¹' (((↑) : H → G) ⁻¹' (E * E⁻¹)) := by
    intro x hx
    refine ⟨(x : G) * g, interior_subset hx, ((x₀ : G) * g)⁻¹, Set.inv_mem_inv.mpr (interior_subset hx₀), ?_⟩
    simp [mul_assoc]
  calc coeff H μH n * μH U ≤ coeff H μH n * μH ((fun x : H => x * x₀⁻¹) ⁻¹' (((↑) : H → G) ⁻¹' (E * E⁻¹))) :=
        mul_le_mul_right (measure_mono hsub) _
    _ = coeff H μH n * μH (((↑) : H → G) ⁻¹' (E * E⁻¹)) := by rw [measure_preimage_mul_right]
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
        unfold coeff
        rw [mul_assoc]
        refine mul_le_of_le_one_right (by simp) ?_
        rw [← hE, ← ENNReal.div_eq_inv_mul]
        exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)

private theorem measurable_term (n : ℕ) (g : G) :
    Measurable fun x : H => coeff H μH n *
      (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) :=
  measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet).comp
    (measurable_subtype_coe.mul_const g))

private theorem lintegral_weight_mul_ne_top [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH ≠ ⊤ := by
  simp_rw [weight_eq H μH]
  rw [lintegral_tsum fun n => (measurable_term H μH n g).aemeasurable]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => lintegral_term_le H μH n g)
  rw [ENNReal.tsum_geometric]
  simp

private theorem lintegral_weight_mul_ne_zero [μH.IsHaarMeasure] (hH : IsClosed (H : Set G)) (g : G) :
    ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH ≠ 0 := by
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem g
  have hg : g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) :=
    (CompactExhaustion.choice G).subset_interior_succ n hn
  set U : Set H := {x : H | (x : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G)} with hU
  have hUopen : IsOpen U := isOpen_interior.preimage (continuous_subtype_val.mul continuous_const)
  have hU1 : (1 : H) ∈ U := by
    show ((1 : H) : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G)
    simpa using hg

  have hcompact : IsCompact (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)) :=
    (hH.isClosedEmbedding_subtypeVal).isCompact_preimage
      (((CompactExhaustion.choice G).isCompact (n + 1)).mul ((CompactExhaustion.choice G).isCompact (n + 1)).inv)
  have hcoeff : coeff H μH n ≠ 0 := by
    unfold coeff
    refine mul_ne_zero (pow_ne_zero _ (by simp)) (ENNReal.inv_ne_zero.mpr ?_)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hcompact.measure_lt_top.ne⟩

  have hterm : coeff H μH n * μH U ≤ ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH := by
    rw [← lintegral_indicator_const hUopen.measurableSet]
    refine lintegral_mono fun x => ?_
    rw [weight_eq H μH]
    refine le_trans ?_ (ENNReal.le_tsum n)
    by_cases hx : x ∈ U
    · have hxg : (x : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) := hx
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hxg]
    · simp [Set.indicator_of_notMem hx]
  refine ne_of_gt (lt_of_lt_of_le ?_ hterm)
  exact ENNReal.mul_pos hcoeff (hUopen.measure_pos μH ⟨1, hU1⟩).ne'

private theorem lintegral_density_mul [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (hH : IsClosed (H : Set G)) (g : G) :
    ∫⁻ x : H, density H μH ((x : G) * g) ∂μH = 1 := by
  have hinv : ∀ x : H, ∫⁻ y : H, weight H μH ((y : G) * ((x : G) * g)) ∂μH =
      ∫⁻ y : H, weight H μH ((y : G) * g) ∂μH := by
    intro x
    have := lintegral_mul_right_eq_self (μ := μH) (fun y : H => weight H μH ((y : G) * g)) x
    simp only [Subgroup.coe_mul, mul_assoc] at this
    exact this
  simp_rw [HaarQuotient.density, hinv, div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (lintegral_weight_mul_ne_zero H μH hH g))]
  exact ENNReal.mul_inv_cancel (lintegral_weight_mul_ne_zero H μH hH g) (lintegral_weight_mul_ne_top H μH g)

end Norm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

end LanglandsTunnell.RankinSelberg.FinIwasawaProof.DensNorm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

namespace LanglandsTunnell
namespace RankinSelberg
namespace FinIwasawaProof
namespace MassCore

open MeasureTheory
open scoped ENNReal Pointwise

variable {G : Type*} [Group G]

section Quotient

variable (H : Subgroup G)

local notation "Q" => MulAction.orbitRel.Quotient H G

private theorem mk_mul_eq (x : H) (g : G) :
    (Quotient.mk'' ((x : G) * g) : Q) = Quotient.mk'' g :=
  Quotient.sound' (MulAction.mem_orbit g x)

private theorem mk_out (q : Q) : (Quotient.mk'' q.out : Q) = q := Quotient.out_eq' q

private theorem exists_mul_eq_of_mk_eq {g g' : G} (h : (Quotient.mk'' g : Q) = Quotient.mk'' g') :
    ∃ x : H, (x : G) * g' = g := by
  have h' : (MulAction.orbitRel H G) g g' := Quotient.exact' h
  obtain ⟨x, hx⟩ := (MulAction.orbitRel_apply).1 h'
  exact ⟨x, hx⟩

private theorem preimage_image_mk_of_invariant {S : Set G} (hinv : ∀ (x : H) (g : G), g ∈ S → (x : G) * g ∈ S) :
    (Quotient.mk'' : G → Q) ⁻¹' ((Quotient.mk'' : G → Q) '' S) = S := by
  ext g
  refine ⟨fun hg => ?_, fun hg => Set.mem_image_of_mem _ hg⟩
  obtain ⟨g', hg', he⟩ := hg
  obtain ⟨x, hx⟩ := exists_mul_eq_of_mk_eq H he.symm
  rw [← hx]
  exact hinv x g' hg'

variable [MeasurableSpace G]

private theorem withDensity_apply_eq_of_map_eq (μ : Measure G) (ρ ρ' : G → ℝ≥0∞)
    (hmap : (μ.withDensity ρ).map (Quotient.mk'' : G → Q) = (μ.withDensity ρ').map (Quotient.mk'' : G → Q))
    {S : Set G} (hS : MeasurableSet S) (hinv : ∀ (x : H) (g : G), g ∈ S → (x : G) * g ∈ S) :
    (μ.withDensity ρ) S = (μ.withDensity ρ') S := by
  have hpre := preimage_image_mk_of_invariant H hinv
  have hmeas : MeasurableSet ((Quotient.mk'' : G → Q) '' S) := by
    rw [measurableSet_quotient, hpre]
    exact hS
  have h1 := congrArg (fun ν : Measure Q => ν ((Quotient.mk'' : G → Q) '' S)) hmap
  rwa [Measure.map_apply measurable_quotient_mk'' hmeas, Measure.map_apply measurable_quotient_mk'' hmeas,
    hpre] at h1

section Unfolding

variable {H}

private theorem map_withDensity_eq_of_unfolding (μ : Measure G) (μH : Measure H) (ν : Measure Q)
    (hunf : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g, F g ∂μ = ∫⁻ q, (∫⁻ x : H, F ((x : G) * q.out) ∂μH) ∂ν)
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρ1 : ∀ g, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1) :
    (μ.withDensity ρ).map (Quotient.mk'' : G → Q) = ν := by
  ext S hS
  have hpre : MeasurableSet ((Quotient.mk'' : G → Q) ⁻¹' S) := measurable_quotient_mk'' hS
  rw [Measure.map_apply measurable_quotient_mk'' hS, withDensity_apply _ hpre,
    ← lintegral_indicator hpre]
  have hF : Measurable (((Quotient.mk'' : G → Q) ⁻¹' S).indicator ρ) := hρ.indicator hpre
  rw [hunf _ hF]
  have hinner : ∀ q : Q, (∫⁻ x : H, ((Quotient.mk'' : G → Q) ⁻¹' S).indicator ρ ((x : G) * q.out) ∂μH) =
      S.indicator (fun _ => (1 : ℝ≥0∞)) q := by
    intro q
    by_cases hq : q ∈ S
    · have hmem : ∀ x : H, (x : G) * q.out ∈ (Quotient.mk'' : G → Q) ⁻¹' S := by
        intro x
        show (Quotient.mk'' ((x : G) * q.out) : Q) ∈ S
        rw [mk_mul_eq H x q.out, mk_out H q]
        exact hq
      simp only [Set.indicator_of_mem (hmem _), Set.indicator_of_mem hq]
      exact hρ1 _
    · have hmem : ∀ x : H, (x : G) * q.out ∉ (Quotient.mk'' : G → Q) ⁻¹' S := by
        intro x hx
        apply hq
        have hx' : (Quotient.mk'' ((x : G) * q.out) : Q) ∈ S := hx
        rwa [mk_mul_eq H x q.out, mk_out H q] at hx'
      simp only [Set.indicator_of_notMem (hmem _), Set.indicator_of_notMem hq, lintegral_zero]
  simp only [hinner]
  rw [lintegral_indicator hS, setLIntegral_one]

end Unfolding
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

end Quotient
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

section Sets

variable {H K : Subgroup G}

private theorem setBuilder_eq_mul (H K : Subgroup G) :
    {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} = (H : Set G) * (K : Set G) := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨n, hn, k, hk, rfl⟩
    exact ⟨n, hn, k, hk, rfl⟩
  · rintro ⟨n, hn, k, hk, rfl⟩
    exact ⟨n, hn, k, hk, rfl⟩

private theorem mem_mul_singleton_mul {t g : G} :
    g ∈ ((H : Set G) * {t}) * (K : Set G) ↔ ∃ n ∈ H, ∃ k ∈ K, g = n * t * k := by
  simp only [Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨n, hn, _, rfl, rfl⟩, k, hk, rfl⟩
    exact ⟨n, hn, k, hk, rfl⟩
  · rintro ⟨n, hn, k, hk, rfl⟩
    exact ⟨n * t, ⟨n, hn, t, rfl, rfl⟩, k, hk, rfl⟩

private theorem mul_mem_mul_of_mem (x : H) {g : G} (hg : g ∈ (H : Set G) * (K : Set G)) :
    (x : G) * g ∈ (H : Set G) * (K : Set G) := by
  obtain ⟨n, hn, k, hk, rfl⟩ := Set.mem_mul.mp hg
  rw [← mul_assoc]
  exact Set.mul_mem_mul (H.mul_mem x.2 hn) hk

private theorem mul_singleton_mul_eq_smul (t : G) (φ : H → H) (hφt : ∀ x : H, t * (x : G) = (φ x : G) * t)
    (hφs : Function.Surjective φ) :
    ((H : Set G) * {t}) * (K : Set G) = t • ((H : Set G) * (K : Set G)) := by
  ext g
  rw [mem_mul_singleton_mul, Set.mem_smul_set]
  constructor
  · rintro ⟨n, hn, k, hk, rfl⟩
    obtain ⟨x, hx⟩ := hφs ⟨n, hn⟩
    have hnt : t * (x : G) = n * t := by rw [hφt x, hx]
    refine ⟨(x : G) * k, Set.mul_mem_mul x.2 hk, ?_⟩
    rw [smul_eq_mul, ← mul_assoc, hnt]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, hn, k, hk, rfl⟩ := Set.mem_mul.mp hy
    refine ⟨φ ⟨n, hn⟩, (φ ⟨n, hn⟩).2, k, hk, ?_⟩
    rw [smul_eq_mul, ← mul_assoc, hφt ⟨n, hn⟩]

end Sets
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

variable [MeasurableSpace G]

private theorem withDensity_apply_smul [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (ρ : G → ℝ≥0∞)
    (t : G) {S : Set G} (hS : MeasurableSet S) :
    (μ.withDensity ρ) (t • S) = ∫⁻ h in S, ρ (t * h) ∂μ := by
  rw [withDensity_apply _ (hS.const_smul t), ← lintegral_indicator (hS.const_smul t), ← lintegral_indicator hS,
    ← lintegral_mul_left_eq_self ((t • S).indicator ρ) t]
  congr 1
  funext h
  have hmem : t * h ∈ t • S ↔ h ∈ S := by
    rw [← smul_eq_mul]
    exact Set.smul_mem_smul_set_iff
  by_cases hh : h ∈ S
  · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (hmem.mpr hh)]
  · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (fun h' => hh (hmem.mp h'))]

private theorem withDensity_apply_smul_eq_mul [MeasurableMul G] (H : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant]
    (ρ ρ' : G → ℝ≥0∞) (t : G) (c : ℝ≥0∞) (hc : c ≠ ⊤) (hρ' : ∀ h, ρ (t * h) = c * ρ' h)
    (hmap : (μ.withDensity ρ).map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) =
      (μ.withDensity ρ').map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G))
    {S : Set G} (hS : MeasurableSet S) (hinv : ∀ (x : H) (g : G), g ∈ S → (x : G) * g ∈ S) :
    (μ.withDensity ρ) (t • S) = c * (μ.withDensity ρ) S := by
  rw [withDensity_apply_smul μ ρ t hS, withDensity_apply_eq_of_map_eq H μ ρ ρ' hmap hS hinv,
    withDensity_apply _ hS]
  simp_rw [hρ']
  exact lintegral_const_mul' c _ hc

private theorem normalized_conj (H : Subgroup G) [MeasurableSpace H] (μH : Measure H) (ρ : G → ℝ≥0∞)
    (hρ : Measurable ρ) (hρ1 : ∀ g, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1) (t : G) (φ : H → H) (hφ : Measurable φ)
    (hφt : ∀ x : H, t * (x : G) = (φ x : G) * t) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hφμ : μH.map φ = c • μH)
    [MeasurableMul G] (hcoe : Measurable ((↑) : H → G)) (g : G) :
    ∫⁻ x : H, c⁻¹ * ρ (t * ((x : G) * g)) ∂μH = 1 := by
  have h1 : ∀ x : H, ρ (t * ((x : G) * g)) = ρ ((φ x : G) * (t * g)) := by
    intro x
    rw [← mul_assoc, hφt x, mul_assoc]
  simp_rw [h1]
  have hmeas : Measurable fun y : H => ρ ((y : G) * (t * g)) := hρ.comp (hcoe.mul_const _)
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0), ← lintegral_map hmeas hφ, hφμ, lintegral_smul_measure,
    hρ1, smul_eq_mul, mul_one, ENNReal.inv_mul_cancel hc0 hc]

private theorem withDensity_apply_smul_of_unfolding [MeasurableMul G] (H : Subgroup G) (μ : Measure G)
    [μ.IsMulLeftInvariant]
    (μH : Measure H) (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρ1 : ∀ g, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1)
    (ν : Measure (MulAction.orbitRel.Quotient H G))
    (hunf : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g, F g ∂μ = ∫⁻ q, (∫⁻ x : H, F ((x : G) * q.out) ∂μH) ∂ν)
    (t : G) (φ : H → H) (hφ : Measurable φ) (hφt : ∀ x : H, t * (x : G) = (φ x : G) * t)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hφμ : μH.map φ = c • μH)
    {S : Set G} (hS : MeasurableSet S) (hinv : ∀ (x : H) (g : G), g ∈ S → (x : G) * g ∈ S) :
    (μ.withDensity ρ) (t • S) = c * (μ.withDensity ρ) S := by
  set ρ' : G → ℝ≥0∞ := fun h => c⁻¹ * ρ (t * h) with hρ'_def
  have hρ' : ∀ h, ρ (t * h) = c * ρ' h := by
    intro h
    simp only [hρ'_def, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hc, one_mul]
  have hρ'meas : Measurable ρ' := measurable_const.mul (hρ.comp (measurable_const_mul t))
  have hρ'1 : ∀ g, ∫⁻ x : H, ρ' ((x : G) * g) ∂μH = 1 := fun g =>
    normalized_conj H μH ρ hρ hρ1 t φ hφ hφt c hc0 hc hφμ measurable_subtype_coe g
  have hmap : (μ.withDensity ρ).map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) =
      (μ.withDensity ρ').map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) := by
    rw [map_withDensity_eq_of_unfolding μ μH ν hunf ρ hρ hρ1,
      map_withDensity_eq_of_unfolding μ μH ν hunf ρ' hρ'meas hρ'1]
  exact withDensity_apply_smul_eq_mul H μ ρ ρ' t c hc hρ' hmap hS hinv

end LanglandsTunnell.RankinSelberg.FinIwasawaProof.MassCore
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

namespace LanglandsTunnell
namespace RankinSelberg
namespace FinIwasawaProof
namespace CellGlue

open MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

private theorem hasSum_measure_mul_of_integrable {ι : Type*} [Countable ι] (C : ι → Set X)
    (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (Function.onFun Disjoint C)) (hcover : (⋃ i, C i) = Set.univ)
    (f : X → ℂ) (hf : Integrable f ν) (c : ι → ℂ)
    (hc : ∀ i, ∀ x ∈ C i, f x = c i) :
    HasSum (fun i => ((ν (C i)).toReal : ℂ) * c i) (∫ x, f x ∂ν) := by
  have h := hasSum_integral_iUnion hC hdisj (hf.integrableOn (s := ⋃ i, C i))
  rw [hcover, Measure.restrict_univ] at h
  convert h using 1
  all_goals try rfl
  funext i
  rw [setIntegral_congr_fun (hC i) (fun x hx => hc i x hx), setIntegral_const, measureReal_def]
  exact Complex.real_smul.symm

private theorem toReal_natCast_zpow {q : ℕ} (hq : q ≠ 0) (k : ℤ) : ((q : ℝ≥0∞) ^ k).toReal = (q : ℝ) ^ k := by
  rw [← ENNReal.coe_natCast, ← ENNReal.coe_zpow (by exact_mod_cast hq), ENNReal.coe_toReal, NNReal.coe_zpow,
    NNReal.coe_natCast]

private theorem hasSum_of_cells (C : ℤ × ℤ → Set X) (S₀ : Set X) (hC : ∀ p, MeasurableSet (C p))
    (hdisj : Pairwise (Function.onFun Disjoint C)) (hcover : (⋃ p, C p) = Set.univ) {q : ℕ} (hq : q ≠ 0)
    (hmass : ∀ p : ℤ × ℤ, ν (C p) = (q : ℝ≥0∞) ^ (p.1 - p.2) * ν S₀)
    (f : X → ℂ) (hf : Integrable f ν) (val : ℤ × ℤ → ℂ) (hval : ∀ p, ∀ x ∈ C p, f x = val p) :
    HasSum (fun p : ℤ × ℤ => ((ν S₀).toReal : ℂ) * ((q : ℂ) ^ (p.1 - p.2)) * val p) (∫ x, f x ∂ν) := by
  have h := hasSum_measure_mul_of_integrable ν C hC hdisj hcover f hf val hval
  convert h using 1
  funext p
  rw [hmass p, ENNReal.toReal_mul, toReal_natCast_zpow hq]
  push_cast
  ring

end LanglandsTunnell.RankinSelberg.FinIwasawaProof.CellGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

namespace LanglandsTunnell
namespace RankinSelberg
namespace FinIwasawaProof

open MeasureTheory NumberField IsDedekindDomain UnramifiedWhittaker AutomorphicForm
open scoped ENNReal Pointwise
open IwasawaCover TorusConj UnipotentMass MassCore CellGlue

section Assembly

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem sigmaCompactSpace_of_isClosed {G : Type*} [Group G] [TopologicalSpace G] [SigmaCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : SigmaCompactSpace H :=
  hH.sigmaCompactSpace

private theorem sfinite_of_isHaarMeasure {H : Type*} [Group H] [TopologicalSpace H] [SigmaCompactSpace H]
    [MeasurableSpace H] (ν : Measure H) [ν.IsHaarMeasure] : SFinite ν :=
  inferInstance

section Unipotent

variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]

omit [TopologicalSpace R] [T2Space R] in

private theorem coe_range_unipotentGL2Hom :
    ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) =
      {g : GL (Fin 2) R | Units.val g 0 0 = 1 ∧ Units.val g 1 0 = 0 ∧ Units.val g 1 1 = 1} := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    change Units.val (unipotentGL2 y.toAdd) 0 0 = 1 ∧ Units.val (unipotentGL2 y.toAdd) 1 0 = 0 ∧
      Units.val (unipotentGL2 y.toAdd) 1 1 = 1
    simp [unipotentGL2]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd (Units.val g 0 1), ?_⟩
    change unipotentGL2 (Units.val g 0 1) = g
    refine Units.ext ?_
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

private theorem isClosed_range_unipotentGL2Hom :
    IsClosed ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) := by
  rw [coe_range_unipotentGL2Hom]
  have hc : Continuous fun g : GL (Fin 2) R => Units.val g := Units.continuous_val
  exact (isClosed_eq (hc.matrix_elem 0 0) continuous_const).inter
    ((isClosed_eq (hc.matrix_elem 1 0) continuous_const).inter
      (isClosed_eq (hc.matrix_elem 1 1) continuous_const))

end Unipotent
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

section Density

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]

private theorem measurable_weight (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · refine Measurable.tsum fun n => ?_
    exact (measurable_const.indicator isOpen_interior.measurableSet).const_mul _
  · exact measurable_const

private theorem measurable_lintegral_weight_mul [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable fun g : G => ∫⁻ x : H, HaarQuotient.weight H μH ((x : G) * g) ∂μH := by
  have hm : Measurable fun p : H × G => HaarQuotient.weight H μH ((p.1 : G) * p.2) :=
    (measurable_weight H μH).comp ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
  exact hm.lintegral_prod_left

private theorem measurable_density [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] (H : Subgroup G)
    (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  unfold HaarQuotient.density
  exact (measurable_weight H μH).div (measurable_lintegral_weight_mul H μH)

end Density
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

private theorem isOpen_localLevelOne_top :
    IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  have hset : ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) =
        {k : GL (Fin 2) (v.adicCompletion ℚ) | IsIntegralUnit (v.adicCompletionIntegers ℚ) k} := by
    ext k
    exact mem_localLevelOne_top_iff v k
  rw [hset]
  exact isOpen_setOf_isIntegralUnit ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out v)

variable {v}

private def tor {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (p : ℤ × ℤ) :
    GL (Fin 2) (v.adicCompletion ℚ) :=
  diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
    scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2

private theorem tor_coe {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0) (p : ℤ × ℤ) :
    ((tor hπ p : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ p.1, 0;
        0, algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ p.2] :=
  torus_coe_pair _ hπ p

private theorem main
    (v : HeightOneSpectrum (𝓞 ℚ)) [SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ))]
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ.IsHaarMeasure]
      (μN : Measure (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure]
      [μN.IsMulRightInvariant]
      (δ : GL (Fin 2) (v.adicCompletion ℚ) → ℝ)
      (_hδN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (n * g) = δ g)
      (_hδK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (g * k) = δ g)
      (s : ℂ) (W F : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (_hN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (n * g) * F (n * g) = W g * F g)
      (_hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (g * k) * F (g * k) = W g * F g)
      (_hint : Integrable
        (fun g : GL (Fin 2) (v.adicCompletion ℚ) => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ.withDensity
          (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))),
      HasSum (fun p : ℤ × ℤ =>
          (((μ.withDensity
                (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
              {g : GL (Fin 2) (v.adicCompletion ℚ) |
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ) *
            ((Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2)) *
            ((W (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) *
                F (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2)) *
              ((δ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) :
                    ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.rsLocalIntegral μ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN δ s W
          F) := by
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := ⟨rfl⟩
  intro μ _ μN _ _ δ hδN hδK s W F hN hK hint

  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := inferInstance
  have hNclosed : IsClosed (((unipotentGL2Hom (R := v.adicCompletion ℚ)).range : Subgroup _) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) := isClosed_range_unipotentGL2Hom
  haveI := sigmaCompactSpace_of_isClosed _ hNclosed
  haveI := sfinite_of_isHaarMeasure μ
  haveI := sfinite_of_isHaarMeasure μN

  set ρ := HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN with hρ_def
  have hρ : Measurable ρ := measurable_density _ μN
  have hρ1 : ∀ g, ∫⁻ x : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
      ρ ((x : GL (Fin 2) (v.adicCompletion ℚ)) * g) ∂μN = 1 :=
    DensNorm.lintegral_density_mul _ μN hNclosed

  set K : Set (GL (Fin 2) (v.adicCompletion ℚ)) :=
    (↑(AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) : Set (GL (Fin 2) (v.adicCompletion ℚ))) with hK_def
  set NS : Set (GL (Fin 2) (v.adicCompletion ℚ)) :=
    (↑(unipotentGL2Hom (R := v.adicCompletion ℚ)).range : Set (GL (Fin 2) (v.adicCompletion ℚ))) with hNS_def
  have hKopen : IsOpen K := isOpen_localLevelOne_top v
  set C : ℤ × ℤ → Set (GL (Fin 2) (v.adicCompletion ℚ)) := fun p => (NS * {tor hπ p}) * K with hC_def
  have hC : ∀ p, MeasurableSet (C p) := fun p => hKopen.mul_left.measurableSet
  have hS₀ : MeasurableSet (NS * K) := hKopen.mul_left.measurableSet

  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro p p' hpp'
    rw [Function.onFun, Set.disjoint_left]
    intro g hg hg'
    obtain ⟨n, hn, k, hk, rfl⟩ := mem_mul_singleton_mul.mp hg
    obtain ⟨n', hn', k', hk', heq⟩ := mem_mul_singleton_mul.mp hg'
    apply hpp'
    have h1 := coe_eq_unipotentGL2_entry (⟨n, hn⟩ : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    have h1' := coe_eq_unipotentGL2_entry (⟨n', hn'⟩ : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    dsimp only at h1 h1'
    rw [h1, h1'] at heq
    exact cell_index_eq _ hπ hϖ (valued_apply_le_one_of_mem v hk) (valued_det_eq_one_of_mem v hk)
      (valued_apply_le_one_of_mem v hk') (valued_det_eq_one_of_mem v hk') heq

  have hcover : (⋃ p, C p) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => Set.mem_iUnion.mpr ?_
    obtain ⟨x, m, k, hk, hg⟩ :=
      exists_cover_localLevelOne v (fun y hy => exists_zpow_mul_unit hϖ y hy) g
    refine ⟨m, mem_mul_singleton_mul.mpr ⟨unipotentGL2 x, unipotentGL2_mem x, k, hk, ?_⟩⟩
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, unipotentGL2_coe, tor_coe]

  set f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ :=
    fun g => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2) with hf_def
  have hval : ∀ p, ∀ g ∈ C p,
      f g = (W (tor hπ p) * F (tor hπ p)) * ((δ (tor hπ p) : ℝ) : ℂ) ^ (s - 1 / 2) := by
    intro p g hg
    obtain ⟨n, hn, k, hk, rfl⟩ := mem_mul_singleton_mul.mp hg
    simp only [hf_def]
    rw [mul_assoc n, hN n hn, hK k hk, hδN n hn, hδK k hk]

  have hq : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by exact_mod_cast absNorm_ne_zero (v := v)
  have hmass : ∀ p : ℤ × ℤ, (μ.withDensity ρ) (C p) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (p.1 - p.2) * (μ.withDensity ρ) (NS * K) := by
    intro p
    have hφt : ∀ x : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        tor hπ p * (x : GL (Fin 2) (v.adicCompletion ℚ)) =
          ((scaleEntry (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ^ (p.1 - p.2))
              (zpow_ne_zero _ hπ) x : (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) :
            GL (Fin 2) (v.adicCompletion ℚ)) * tor hπ p :=
      fun x => torus_mul_coe hπ p x
    have hcell : C p = tor hπ p • (NS * K) :=
      mul_singleton_mul_eq_smul (tor hπ p) _ hφt (EquivLike.surjective _)
    rw [hcell]
    exact withDensity_apply_smul_of_unfolding _ μ μN ρ hρ hρ1
      (HaarQuotient.measure μ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)
      (fun G hG => HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ _ hNclosed μN G hG)
      (tor hπ p) _ (scaleEntry _ (zpow_ne_zero _ hπ)).toHomeomorph.continuous.measurable hφt _
      (ENNReal.zpow_pos hq (ENNReal.natCast_ne_top _) _).ne' (ENNReal.zpow_lt_top hq (ENNReal.natCast_ne_top _) _).ne
      (map_scaleEntry_uniformizer hπ hϖ μN p) hS₀ (fun x g hg => mul_mem_mul_of_mem x hg)

  have h := hasSum_of_cells (μ.withDensity ρ) C (NS * K) hC hdisj hcover (absNorm_ne_zero (v := v)) hmass f hint
    (fun p => (W (tor hπ p) * F (tor hπ p)) * ((δ (tor hπ p) : ℝ) : ℂ) ^ (s - 1 / 2)) hval
  rw [setBuilder_eq_mul]
  exact h

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

end LanglandsTunnell.RankinSelberg.FinIwasawaProof
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) [SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ))]
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ.IsHaarMeasure]
      (μN : Measure (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure]
      [μN.IsMulRightInvariant]
      (δ : GL (Fin 2) (v.adicCompletion ℚ) → ℝ)
      (_hδN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (n * g) = δ g)
      (_hδK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (g * k) = δ g)
      (s : ℂ) (W F : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (_hN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (n * g) * F (n * g) = W g * F g)
      (_hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (g * k) * F (g * k) = W g * F g)
      (_hint : Integrable
        (fun g : GL (Fin 2) (v.adicCompletion ℚ) => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ.withDensity
          (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))),
      HasSum (fun p : ℤ × ℤ =>
          (((μ.withDensity
                (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
              {g : GL (Fin 2) (v.adicCompletion ℚ) |
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ) *
            ((Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2)) *
            ((W (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) *
                F (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2)) *
              ((δ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) :
                    ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.rsLocalIntegral μ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN δ s W
          F) :=
  LanglandsTunnell.RankinSelberg.FinIwasawaProof.main v hπ hϖ

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.LanglandsTunnell.RankinSelberg.FinIwasawaProof.UnipotentMass"

end S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral (solution)
