-- Prove2me | solution 1 for NumberField.AdeleRing.pi_measure_setOf_not_exists_apply_col_eq_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/38facfbd-1ee0-5220-ac7a-b6a78e765a94

import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero.NumberField IsDedekindDomain Filter"
open scoped ENNReal NNReal RestrictedProduct Pointwise Topology WithZero

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing InfinitePlace.Completion.extensionEmbedding InfinitePlace.mult_pos place HeightOneSpectrum.one_lt_absNorm InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective dedekindZeta InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace HeightOneSpectrum.absNorm_ne_zero AdeleRing FinitePlace.norm_def AdelicLevel.finIncl AdelicLevel.localUnit AdeleRing.secondCountableTopology AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta"
namespace UnimodularColumn
p2m_open "NumberField"

section Pivot

variable {F : Type*} [NormedField F]

open Classical in

def piv (a b : F) : F × F := if ‖b‖ ≤ ‖a‖ then (a⁻¹, 0) else (0, b⁻¹)

theorem piv_dot {a b : F} (h : ¬ (a = 0 ∧ b = 0)) : (piv a b).1 * a + (piv a b).2 * b = 1 := by
  unfold piv
  split_ifs with hle
  · have ha : a ≠ 0 := by
      intro ha
      apply h
      refine ⟨ha, ?_⟩
      have : ‖b‖ ≤ 0 := by simpa [ha] using hle
      exact norm_le_zero_iff.mp this
    simp [ha]
  · have hb : b ≠ 0 := by
      intro hb; apply hle; simp [hb]
    simp [hb]

theorem norm_piv_fst_le (a b : F) : ‖(piv a b).1‖ ≤ ‖a‖⁻¹ := by
  unfold piv; split_ifs <;> simp

theorem norm_piv_snd_le (a b : F) : ‖(piv a b).2‖ ≤ ‖b‖⁻¹ := by
  unfold piv; split_ifs <;> simp

theorem norm_piv_le_one {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (h : ¬ (‖a‖ < 1 ∧ ‖b‖ < 1)) :
    ‖(piv a b).1‖ ≤ 1 ∧ ‖(piv a b).2‖ ≤ 1 := by
  unfold piv
  split_ifs with hle
  · have ha1 : ‖a‖ = 1 := by
      rcases eq_or_lt_of_le ha with h1 | h1
      · exact h1
      · exact absurd ⟨h1, lt_of_le_of_lt hle h1⟩ h
    refine ⟨?_, by simp⟩
    simp [ha1]
  · have hb1 : ‖b‖ = 1 := by
      rcases eq_or_lt_of_le hb with h1 | h1
      · exact h1
      · exact absurd ⟨(lt_of_not_ge hle).trans h1, h1⟩ h
    refine ⟨by simp, ?_⟩
    simp [hb1]

end Pivot

section Column

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "Gp" => Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 K) K)
local notation "Xp" => (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ

variable {K}

def IsUnimod (c : Fin 2 → AdeleRing (𝓞 K) K) : Prop :=
  (∀ w : InfinitePlace K, ¬ ((c 0).1 w = 0 ∧ (c 1).1 w = 0)) ∧
  (∀ v : HeightOneSpectrum (𝓞 K), ¬ ((c 0).2 v = 0 ∧ (c 1).2 v = 0)) ∧
  ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ¬ (‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1)

theorem mem_integers_iff (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem fst_apply_ne_zero_of_units (u : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) : (u : 𝔸).1 w ≠ 0 := by
  intro h
  have h1 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).1 w = 1 := by rw [Units.mul_inv]; rfl
  have h2 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).1 w = (u : 𝔸).1 w * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).1 w :=
    rfl
  rw [h2, h, zero_mul] at h1
  exact zero_ne_one h1

theorem snd_apply_ne_zero_of_units (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (u : 𝔸).2 v ≠ 0 := by
  intro h
  have h1 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).2 v = 1 := by rw [Units.mul_inv]; rfl
  have h2 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).2 v = (u : 𝔸).2 v * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v :=
    rfl
  rw [h2, h, zero_mul] at h1
  exact zero_ne_one h1

theorem norm_snd_units_mul_inv (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ‖(u : 𝔸).2 v‖ * ‖((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v‖ = 1 := by
  have h1 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).2 v = 1 := by rw [Units.mul_inv]; rfl
  have h2 : ((u : 𝔸) * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).2 v = (u : 𝔸).2 v * ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v :=
    rfl
  rw [← norm_mul, ← h2, h1, norm_one]

theorem isUnimod_col (g : Gp) : IsUnimod (fun i => (g : Matrix (Fin 2) (Fin 2) 𝔸) i 0) := by
  have hcol0 : (fun i => (g : Matrix (Fin 2) (Fin 2) 𝔸) i 0) 0 = (g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0 := rfl
  have hcol1 : (fun i => (g : Matrix (Fin 2) (Fin 2) 𝔸) i 0) 1 = (g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 := rfl
  set d : (AdeleRing (𝓞 K) K)ˣ := Matrix.GeneralLinearGroup.det g with hd
  have hdv : (d : 𝔸) = (g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0 * (g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 * (g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 := by
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  refine ⟨fun w h => ?_, fun v h => ?_, ?_⟩
  · apply fst_apply_ne_zero_of_units d w
    show (d : 𝔸).1 w = 0
    rw [hdv]
    show ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).1 w * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).1 w -
      ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1).1 w * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0).1 w = 0
    rw [h.1, h.2]; ring
  · apply snd_apply_ne_zero_of_units d v
    show (d : 𝔸).2 v = 0
    rw [hdv]
    show ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).2 v * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).2 v -
      ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1).2 v * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0).2 v = 0
    rw [h.1, h.2]; ring
  ·
    have h01 := ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1).2.2
    have h11 := ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).2.2
    have hdi := (((d⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸)).2.2
    filter_upwards [h01, h11, hdi] with v h01 h11 hdi
    rintro ⟨ha, hc⟩
    rw [SetLike.mem_coe, mem_integers_iff] at h01 h11 hdi
    have hnon := IsUltrametricDist.isNonarchimedean_norm (R := v.adicCompletion K)
    have hdet : ‖(d : 𝔸).2 v‖ < 1 := by
      have : (d : 𝔸).2 v = ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).2 v * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).2 v -
          ((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1).2 v * ((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0).2 v := by
        rw [hdv]; rfl
      rw [this, sub_eq_add_neg]
      refine lt_of_le_of_lt (hnon _ _) (max_lt ?_ ?_)
      · dsimp only
        rw [norm_mul]
        calc ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).2 v‖ * ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).2 v‖
            ≤ ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).2 v‖ * 1 :=
              mul_le_mul_of_nonneg_left h11 (norm_nonneg _)
          _ < 1 := by rw [mul_one]; exact ha
      · dsimp only
        rw [norm_neg, norm_mul]
        calc ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 0 1).2 v‖ * ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0).2 v‖
            ≤ 1 * ‖((g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0).2 v‖ :=
              mul_le_mul_of_nonneg_right h01 (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hc
    have h1 := norm_snd_units_mul_inv d v
    have : ‖(d : 𝔸).2 v‖ * ‖((d⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v‖ < 1 := by
      calc ‖(d : 𝔸).2 v‖ * ‖((d⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v‖ ≤ ‖(d : 𝔸).2 v‖ * 1 :=
            mul_le_mul_of_nonneg_left hdi (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hdet
    rw [h1] at this
    exact lt_irrefl _ this

def pv {F : Type*} [NormedField F] (i : Fin 2) (a b : F) : F := ![(piv a b).1, (piv a b).2] i

theorem pv_zero {F : Type*} [NormedField F] (a b : F) : pv 0 a b = (piv a b).1 := rfl
theorem pv_one {F : Type*} [NormedField F] (a b : F) : pv 1 a b = (piv a b).2 := rfl

def rArch (c : Fin 2 → AdeleRing (𝓞 K) K) (i : Fin 2) : InfiniteAdeleRing K :=
  fun w => pv i ((c 0).1 w) ((c 1).1 w)

open Classical in

def rFin (c : Fin 2 → AdeleRing (𝓞 K) K) (i : Fin 2) : FiniteAdeleRing (𝓞 K) K :=
  if h : IsUnimod c then
    ⟨fun v => pv i ((c 0).2 v) ((c 1).2 v), by
      have h0 := (c 0).2.2
      have h1 := (c 1).2.2
      filter_upwards [h0, h1, h.2.2] with v h0 h1 h2
      rw [SetLike.mem_coe, mem_integers_iff] at h0 h1 ⊢
      have := norm_piv_le_one h0 h1 h2
      fin_cases i
      · exact this.1
      · exact this.2⟩
  else 0

def rRow (c : Fin 2 → AdeleRing (𝓞 K) K) (i : Fin 2) : AdeleRing (𝓞 K) K := (rArch c i, rFin c i)

open Classical in
theorem rFin_apply (c : Fin 2 → AdeleRing (𝓞 K) K) (i : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    (rFin c i) v = if IsUnimod c then pv i ((c 0).2 v) ((c 1).2 v) else 0 := by
  unfold rFin
  split_ifs with h
  · rfl
  · rfl

open Classical in
theorem rRow_dot {c : Fin 2 → AdeleRing (𝓞 K) K} (hc : IsUnimod c) : rRow c 0 * c 0 + rRow c 1 * c 1 = 1 := by
  refine Prod.ext ?_ ?_
  · funext w
    show pv 0 ((c 0).1 w) ((c 1).1 w) * (c 0).1 w + pv 1 ((c 0).1 w) ((c 1).1 w) * (c 1).1 w = 1
    rw [pv_zero, pv_one]
    exact piv_dot (hc.1 w)
  · apply RestrictedProduct.ext
    intro v
    show (rFin c 0) v * (c 0).2 v + (rFin c 1) v * (c 1).2 v = 1
    rw [rFin_apply, rFin_apply, if_pos hc, if_pos hc, pv_zero, pv_one]
    exact piv_dot (hc.2.1 v)

def secMat (p : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  !![p.1 0, -((p.2 : 𝔸) * rRow p.1 1); p.1 1, (p.2 : 𝔸) * rRow p.1 0]

theorem det_secMat {p : Xp} (hp : IsUnimod p.1) : (secMat p).det = (p.2 : 𝔸) := by
  rw [secMat, Matrix.det_fin_two_of]
  have := rRow_dot hp
  linear_combination (p.2 : 𝔸) * this

theorem det_secMat_one {c : Fin 2 → 𝔸} (hc : IsUnimod c) :
    (secMat (c, (1 : (AdeleRing (𝓞 K) K)ˣ))).det = 1 := by
  rw [det_secMat (p := (c, (1 : (AdeleRing (𝓞 K) K)ˣ))) hc, Units.val_one]

theorem exists_col_eq_of_isUnimod {c : Fin 2 → 𝔸} (hc : IsUnimod c) :
    ∃ g : Gp, (fun i => (g : Matrix (Fin 2) (Fin 2) 𝔸) i 0) = c := by
  refine ⟨Matrix.nonsingInvUnit (secMat (c, (1 : (AdeleRing (𝓞 K) K)ˣ))) (by rw [det_secMat_one hc]; exact isUnit_one), ?_⟩
  funext i
  show secMat (c, (1 : (AdeleRing (𝓞 K) K)ˣ)) i 0 = c i
  fin_cases i <;> rfl

theorem setOf_not_exists_subset :
    {c : Fin 2 → 𝔸 | ¬ ∃ g : Gp, (fun i => (g : Matrix (Fin 2) (Fin 2) 𝔸) i 0) = c} ⊆ {c | ¬ IsUnimod c} :=
  fun c hc hu => hc (exists_col_eq_of_isUnimod hu)

end Column

section Null

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "Gp" => Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 K) K)

theorem secondCountable_A : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology K

theorem t1Space_A : T1Space (AdeleRing (𝓞 K) K) := T2Space.t1Space

attribute [local instance] secondCountable_A t1Space_A

theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 K)) := by
  classical
  haveI : Countable K := by
    let b := Module.finBasis ℚ K
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (𝓞 K) := (RingOfIntegers.coe_injective (K := K)).countable
  have hsurj : Function.Surjective (fun s : Finset (𝓞 K) => Ideal.span (s : Set (𝓞 K))) := by
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  haveI : Countable (Ideal (𝓞 K)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

variable {K}

theorem measure_eq_zero_of_forall_smul_eq (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
    (d : (AdeleRing (𝓞 K) K)ˣ) (hd : distribHaarChar (AdeleRing (𝓞 K) K) d ≠ 1)
    {s : Set 𝔸} (hs : ∀ x ∈ s, d • x = x) (hfin : μ s ≠ ⊤) : μ s = 0 := by
  have hset : d • s = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show d • y ∈ s
      rw [hs y hy]; exact hy
    · intro hx
      exact ⟨x, hx, hs x hx⟩
  have h := distribHaarChar_mul μ d s
  rw [hset] at h
  by_contra h0
  apply hd
  have h1 : ((distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ≥0) : ℝ≥0∞) * μ s = 1 * μ s := by
    rw [one_mul]; exact h
  have h2 := (ENNReal.mul_left_inj h0 hfin).mp h1
  exact_mod_cast h2

theorem measure_eq_zero_of_forall_smul_eq' (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
    (d : (AdeleRing (𝓞 K) K)ˣ) (hd : distribHaarChar (AdeleRing (𝓞 K) K) d ≠ 1)
    {s : Set 𝔸} (hs : ∀ x ∈ s, d • x = x) : μ s = 0 := by
  have : s = ⋃ n, s ∩ spanningSets μ n := by
    rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
  rw [this]
  refine measure_iUnion_null fun n => ?_
  refine measure_eq_zero_of_forall_smul_eq μ d hd (fun x hx => hs x hx.1) ?_
  exact (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (measure_spanningSets_lt_top μ n)).ne

open Classical in

def archUnit (w : InfinitePlace K) (t : (w.Completion)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((Function.update (1 : InfiniteAdeleRing K) w (t : w.Completion) : InfiniteAdeleRing K),
    (1 : FiniteAdeleRing (𝓞 K) K))
  inv := ((Function.update (1 : InfiniteAdeleRing K) w ((t⁻¹ : (w.Completion)ˣ) : w.Completion) : InfiniteAdeleRing K),
    (1 : FiniteAdeleRing (𝓞 K) K))
  val_inv := by
    refine Prod.ext (funext fun w' => ?_) (one_mul _)
    show Function.update (1 : InfiniteAdeleRing K) w (t : w.Completion) w' *
      Function.update (1 : InfiniteAdeleRing K) w ((t⁻¹ : (w.Completion)ˣ) : w.Completion) w' = 1
    by_cases hw : w' = w
    · subst hw; simp
    · simp [Function.update_of_ne hw]
      show (1 : w'.Completion) * 1 = 1
      exact mul_one 1
  inv_val := by
    refine Prod.ext (funext fun w' => ?_) (one_mul _)
    show Function.update (1 : InfiniteAdeleRing K) w ((t⁻¹ : (w.Completion)ˣ) : w.Completion) w' *
      Function.update (1 : InfiniteAdeleRing K) w (t : w.Completion) w' = 1
    by_cases hw : w' = w
    · subst hw; simp
    · simp [Function.update_of_ne hw]
      show (1 : w'.Completion) * 1 = 1
      exact mul_one 1

def finUnit (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (AdelicLevel.finIncl (𝓞 K) K) (AdelicLevel.localUnit (𝓞 K) K v t)

open Classical in
theorem archUnit_fst (w : InfinitePlace K) (t : (w.Completion)ˣ) (w' : InfinitePlace K) :
    ((archUnit w t : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).1 w' = Function.update (1 : InfiniteAdeleRing K) w (t : w.Completion) w' :=
  rfl

theorem archUnit_snd (w : InfinitePlace K) (t : (w.Completion)ˣ) :
    ((archUnit w t : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 = 1 := rfl

theorem finUnit_fst (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((finUnit v t : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).1 = 1 := rfl

open Classical in
theorem finUnit_snd_apply (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) (u : HeightOneSpectrum (𝓞 K)) :
    ((finUnit v t : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 u =
      Function.update (1 : ∀ u : HeightOneSpectrum (𝓞 K), u.adicCompletion K) v (t : v.adicCompletion K) u :=
  rfl

theorem finUnit_inv (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    (finUnit v t)⁻¹ = finUnit (K := K) v t⁻¹ := by
  simp [finUnit, map_inv]

open Classical in

theorem distribHaarChar_archUnit (w : InfinitePlace K) (t : (w.Completion)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 K) K) (archUnit w t) : ℝ) = ‖(t : w.Completion)‖ ^ w.mult := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((archUnit w t : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [archUnit_snd]
    show ‖((1 : FiniteAdeleRing (𝓞 K) K) : FiniteAdeleRing (𝓞 K) K) v‖ = 1
    exact norm_one
  rw [h2, mul_one]
  rw [Finset.prod_eq_single w]
  · rw [archUnit_fst, Function.update_self]
  · intro w' _ hw'
    rw [archUnit_fst, Function.update_of_ne hw']
    show ‖(1 : w'.Completion)‖ ^ w'.mult = 1
    rw [norm_one, one_pow]
  · intro h; exact absurd (Finset.mem_univ w) h

open Classical in

theorem distribHaarChar_finUnit (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 K) K) (finUnit v t) : ℝ) = ‖(t : v.adicCompletion K)‖ := by
  classical
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
  have h1 : ∏ w : InfinitePlace K, ‖((finUnit v t : (AdeleRing (𝓞 K) K)ˣ) : 𝔸).1 w‖ ^ w.mult = 1 := by
    refine Finset.prod_eq_one fun w _ => ?_
    rw [finUnit_fst]
    show ‖(1 : w.Completion)‖ ^ w.mult = 1
    rw [norm_one, one_pow]
  rw [h1, one_mul]
  rw [finprod_eq_single _ v]
  · rw [finUnit_snd_apply, Function.update_self]
  · intro u hu
    rw [finUnit_snd_apply, Function.update_of_ne hu]
    exact norm_one

open Classical in

theorem measure_setOf_fst_apply_eq_zero (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
    (w : InfinitePlace K) : μ {x : 𝔸 | x.1 w = 0} = 0 := by
  obtain ⟨t, ht⟩ : ∃ t : w.Completion, 1 < ‖t‖ := by
    refine ⟨2, ?_⟩
    have h := (AddMonoidHomClass.isometry_iff_norm
      (InfinitePlace.Completion.extensionEmbedding w)).mp
      (InfinitePlace.Completion.isometry_extensionEmbedding w) 2
    rw [map_ofNat] at h
    rw [← h]
    norm_num
  have ht0 : t ≠ 0 := by
    intro h; rw [h, norm_zero] at ht; exact absurd ht (by norm_num)
  set d : (AdeleRing (𝓞 K) K)ˣ := archUnit w (Units.mk0 t ht0) with hd
  refine measure_eq_zero_of_forall_smul_eq' μ d ?_ ?_
  · intro h1
    have h2 : (distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ) = 1 := by rw [h1]; rfl
    rw [hd, distribHaarChar_archUnit] at h2
    have : (1 : ℝ) < ‖((Units.mk0 t ht0 : (w.Completion)ˣ) : w.Completion)‖ ^ w.mult :=
      one_lt_pow₀ ht (InfinitePlace.mult_pos).ne'
    rw [h2] at this
    exact lt_irrefl _ this
  · intro x hx
    show (d : 𝔸) * x = x
    refine Prod.ext (funext fun w' => ?_) ?_
    · show ((d : 𝔸).1 w') * x.1 w' = x.1 w'
      rw [hd, archUnit_fst]
      by_cases hw : w' = w
      · subst hw
        rw [Set.mem_setOf_eq] at hx
        rw [hx, mul_zero]
      · rw [Function.update_of_ne hw]
        exact one_mul _
    · show (d : 𝔸).2 * x.2 = x.2
      rw [hd, archUnit_snd, one_mul]

theorem measure_setOf_snd_apply_eq_zero (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
    (v : HeightOneSpectrum (𝓞 K)) : μ {x : 𝔸 | x.2 v = 0} = 0 := by
  classical
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
  have hπv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hπv
    exact WithZero.zero_ne_coe hπv
  have hnorm : ‖(π : v.adicCompletion K)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  set d : (AdeleRing (𝓞 K) K)ˣ := finUnit v (Units.mk0 _ hπ0) with hd
  refine measure_eq_zero_of_forall_smul_eq' μ d ?_ ?_
  · intro h1
    have h2 : (distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ) = 1 := by rw [h1]; rfl
    rw [hd, distribHaarChar_finUnit] at h2
    have : ‖((Units.mk0 _ hπ0 : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ < 1 := hnorm
    rw [h2] at this
    exact lt_irrefl _ this
  · intro x hx
    show (d : 𝔸) * x = x
    refine Prod.ext ?_ ?_
    · show (d : 𝔸).1 * x.1 = x.1
      rw [hd, finUnit_fst, one_mul]
    · apply RestrictedProduct.ext
      intro u
      show ((d : 𝔸).2 u) * x.2 u = x.2 u
      rw [hd, finUnit_snd_apply]
      by_cases hu : u = v
      · subst hu
        rw [Set.mem_setOf_eq] at hx
        rw [hx, mul_zero]
      · rw [Function.update_of_ne hu]
        exact one_mul _

end Null

section Summable

variable (K : Type) [Field K] [NumberField K]

theorem sum_le_prod_one_add {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hP : 1 ≤ ∏ i ∈ s, (1 + f i) := by
      calc (1 : ℝ) = ∏ i ∈ s, (1 : ℝ) := by simp
        _ ≤ ∏ i ∈ s, (1 + f i) := Finset.prod_le_prod (fun _ _ => zero_le_one) fun i hi => by linarith [hs i hi]
    have ih' := ih hs
    nlinarith

theorem summable_absNorm_sq_inv :
    Summable (fun v : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹) := by
  classical
  set f : HeightOneSpectrum (𝓞 K) → ℝ := fun v => ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹ with hf
  have hN : ∀ v : HeightOneSpectrum (𝓞 K), (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast this
  have hf0 : ∀ v, 0 ≤ f v := fun v => by positivity
  have hf1 : ∀ v, f v < 1 := fun v => by
    have h4 : (4 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by nlinarith [hN v]
    rw [hf]
    exact inv_lt_one_of_one_lt₀ (by linarith)

  have hE := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K 2 (by norm_num)
  set g : HeightOneSpectrum (𝓞 K) → ℂ := fun v => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹ with hg
  have hgf : ∀ v, g v = (((1 - f v)⁻¹ : ℝ) : ℂ) := by
    intro v
    have hN0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      have := hN v
      exact_mod_cast (show (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 by exact_mod_cast (by linarith : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0))
    rw [hg, hf]
    simp only [Complex.cpow_neg]
    rw [show ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (2 : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (2 : ℕ) from
      Complex.cpow_ofNat _ 2]
    push_cast
    ring
  have hnorm : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), ‖∏ v ∈ T, g v‖ = ∏ v ∈ T, (1 - f v)⁻¹ := by
    intro T
    rw [norm_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hgf, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    exact inv_pos.mpr (by linarith [hf1 v])
  have htend : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) => ∏ v ∈ T, (1 - f v)⁻¹) atTop
      (𝓝 ‖NumberField.dedekindZeta K 2‖) := by
    have := (continuous_norm.tendsto _).comp hE
    refine this.congr fun T => ?_
    exact hnorm T
  set M : ℝ := ‖NumberField.dedekindZeta K 2‖ + 1 with hM
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ T ≥ T₀, ∏ v ∈ T, (1 - f v)⁻¹ < M :=
    Filter.eventually_atTop.mp ((tendsto_order.1 htend).2 M (lt_add_one _))
  have hone : ∀ v, 1 ≤ (1 - f v)⁻¹ := fun v => one_le_inv_iff₀.mpr ⟨by linarith [hf1 v], by linarith [hf0 v]⟩
  have hbound : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ T, f v ≤ M := by
    intro T
    calc ∑ v ∈ T, f v ≤ ∏ v ∈ T, (1 + f v) := sum_le_prod_one_add T f fun v _ => hf0 v
      _ ≤ ∏ v ∈ T, (1 - f v)⁻¹ := by
          refine Finset.prod_le_prod (fun v _ => by linarith [hf0 v]) fun v _ => ?_
          rw [le_inv_comm₀ (by linarith [hf0 v]) (by linarith [hf1 v])]
          rw [inv_eq_one_div, le_div_iff₀ (by linarith [hf0 v])]
          nlinarith [hf0 v, hf1 v]
      _ ≤ ∏ v ∈ T ∪ T₀, (1 - f v)⁻¹ := by
          rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
          refine le_mul_of_one_le_right (Finset.prod_nonneg fun v _ => (zero_le_one.trans (hone v))) ?_
          calc (1 : ℝ) = ∏ v ∈ T₀ \ T, (1 : ℝ) := by simp
            _ ≤ ∏ v ∈ T₀ \ T, (1 - f v)⁻¹ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun v _ => hone v
      _ ≤ M := (hT₀ _ Finset.subset_union_right).le
  exact summable_of_sum_le hf0 hbound

theorem tsum_absNorm_sq_inv_ne_top :
    (∑' v : HeightOneSpectrum (𝓞 K), (((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ≥0∞) ^ 2)⁻¹) ≠ ⊤ := by
  have h := summable_absNorm_sq_inv K
  have h' : Summable (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ≥0) ^ 2)⁻¹ : ℝ≥0)) := by
    rw [← NNReal.summable_coe]
    refine h.congr fun v => ?_
    push_cast
    ring
  rw [← ENNReal.tsum_coe_ne_top_iff_summable] at h'
  refine ne_of_eq_of_ne ?_ h'
  refine tsum_congr fun v => ?_
  rw [ENNReal.coe_inv (pow_ne_zero 2 (NumberField.HeightOneSpectrum.absNorm_ne_zero v)),
    ENNReal.coe_pow]

end Summable

section Boxes

open scoped Classical

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "Gp" => Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 K) K)

attribute [local instance] secondCountable_A t1Space_A

scoped instance secondCountableTopology_completion' (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance secondCountableTopology_infiniteAdeleRing' : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace K) → v.Completion))

scoped instance sigmaCompactSpace_infiniteAdeleRing : SigmaCompactSpace (InfiniteAdeleRing K) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

def bnd (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : ℝ :=
  if v ∈ S then (2 : ℝ) ^ n else 1

theorem one_le_bnd (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : 1 ≤ bnd K S n v := by
  unfold bnd; split_ifs
  · exact one_le_pow₀ (by norm_num)
  · exact le_rfl

theorem bnd_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 K))} {n : ℕ} {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    bnd K S n v = 1 := by
  unfold bnd; rw [if_neg hv]

theorem bnd_mono {S S' : Finset (HeightOneSpectrum (𝓞 K))} {n n' : ℕ} (hS : S ⊆ S') (hn : n ≤ n')
    (v : HeightOneSpectrum (𝓞 K)) : bnd K S n v ≤ bnd K S' n' v := by
  unfold bnd
  by_cases hv : v ∈ S
  · rw [if_pos hv, if_pos (hS hv)]
    exact pow_le_pow_right₀ (by norm_num) hn
  · rw [if_neg hv]
    split_ifs
    · exact one_le_pow₀ (by norm_num)
    · exact le_rfl

def box (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : Set (AdeleRing (𝓞 K) K) :=
  {x | x.1 ∈ compactCovering (InfiniteAdeleRing K) n ∧ ∀ v : HeightOneSpectrum (𝓞 K), ‖x.2 v‖ ≤ bnd K S n v}

theorem isClosed_box (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : IsClosed (box K S n) := by
  have h1 : IsClosed {x : 𝔸 | x.1 ∈ compactCovering (InfiniteAdeleRing K) n} :=
    (isCompact_compactCovering (InfiniteAdeleRing K) n).isClosed.preimage continuous_fst
  have h2 : ∀ v : HeightOneSpectrum (𝓞 K), IsClosed {x : 𝔸 | ‖x.2 v‖ ≤ bnd K S n v} := fun v => by
    have hc : Continuous fun x : 𝔸 => x.2 v := (RestrictedProduct.continuous_eval v).comp continuous_snd
    exact isClosed_le (continuous_norm.comp hc) continuous_const
  have : box K S n = {x : 𝔸 | x.1 ∈ compactCovering (InfiniteAdeleRing K) n} ∩ ⋂ v, {x : 𝔸 | ‖x.2 v‖ ≤ bnd K S n v} := by
    ext x; simp [box]
  rw [this]
  exact h1.inter (isClosed_iInter h2)

theorem measurableSet_box (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : MeasurableSet (box K S n) :=
  (isClosed_box K S n).measurableSet

theorem box_mono {S S' : Finset (HeightOneSpectrum (𝓞 K))} {n n' : ℕ} (hS : S ⊆ S') (hn : n ≤ n') :
    box K S n ⊆ box K S' n' := by
  rintro x ⟨h1, h2⟩
  exact ⟨compactCovering_subset _ hn h1, fun v => (h2 v).trans (bnd_mono K hS hn v)⟩

theorem exists_mem_box (x : 𝔸) : ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ), x ∈ box K S n := by

  have hx := x.2.2
  rw [Filter.eventually_cofinite] at hx
  set S : Finset (HeightOneSpectrum (𝓞 K)) := hx.toFinset with hS

  obtain ⟨n₁, hn₁⟩ : ∃ n₁, x.1 ∈ compactCovering (InfiniteAdeleRing K) n₁ := by
    have : x.1 ∈ ⋃ n, compactCovering (InfiniteAdeleRing K) n := by
      rw [iUnion_compactCovering]; exact Set.mem_univ _
    exact Set.mem_iUnion.mp this

  have hb : ∀ v : HeightOneSpectrum (𝓞 K), ∃ m : ℕ, ‖x.2 v‖ ≤ (2 : ℝ) ^ m := fun v => by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖x.2 v‖ (by norm_num : (1 : ℝ) < 2)
    exact ⟨m, hm.le⟩
  choose m hm using hb
  refine ⟨S, n₁ ⊔ S.sup m, ⟨compactCovering_subset _ le_sup_left hn₁, fun v => ?_⟩⟩
  unfold bnd
  split_ifs with hv
  · calc ‖x.2 v‖ ≤ (2 : ℝ) ^ m v := hm v
      _ ≤ 2 ^ (n₁ ⊔ S.sup m) := pow_le_pow_right₀ (by norm_num) ((Finset.le_sup hv).trans le_sup_right)
  · have : x.2 v ∈ v.adicCompletionIntegers K := by
      by_contra h
      exact hv (hx.mem_toFinset.mpr h)
    exact (mem_integers_iff v _).mp this

theorem exists_isCompact_snd_subset (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    ∃ F : Set (FiniteAdeleRing (𝓞 K) K), IsCompact F ∧
      {y : FiniteAdeleRing (𝓞 K) K | ∀ v, ‖y v‖ ≤ bnd K S n v} ⊆ F := by

  let D : ∀ v : HeightOneSpectrum (𝓞 K), Type := fun v => {t : v.adicCompletion K // ‖t‖ ≤ bnd K S n v}
  haveI : ∀ v, CompactSpace (D v) := fun v => by
    have hc : IsCompact {t : v.adicCompletion K | ‖t‖ ≤ bnd K S n v} := by
      have : {t : v.adicCompletion K | ‖t‖ ≤ bnd K S n v} = Metric.closedBall 0 (bnd K S n v) := by
        ext t; simp
      rw [this]
      exact isCompact_closedBall _ _
    exact isCompact_iff_compactSpace.mp hc
  have hSc : (cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 ((↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :=
    le_principal_iff.mpr S.finite_toSet.compl_mem_cofinite
  let φ₀ : (∀ v, D v) → Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K,
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))]_[𝓟 ((↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)] :=
    fun z => ⟨fun v => (z v).1, by
      rw [Filter.eventually_principal]
      intro v hv
      have hv' : v ∉ S := fun h => hv h
      show (z v).1 ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))
      rw [SetLike.mem_coe, mem_integers_iff]
      exact (z v).2.trans (bnd_of_not_mem K hv').le⟩
  have hφ₀ : Continuous φ₀ := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v)
  let φ : (∀ v, D v) → FiniteAdeleRing (𝓞 K) K := fun z =>
    RestrictedProduct.inclusion (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) hSc (φ₀ z)
  have hφ : Continuous φ := (RestrictedProduct.continuous_inclusion hSc).comp hφ₀
  refine ⟨Set.range φ, isCompact_range hφ, fun y hy => ?_⟩
  refine ⟨fun v => (⟨y v, hy v⟩ : D v), ?_⟩
  show φ (fun v => (⟨y v, hy v⟩ : D v)) = y
  apply RestrictedProduct.ext
  intro v
  rfl

theorem measure_box_lt_top (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) : μ (box K S n) < ⊤ := by
  obtain ⟨F, hF, hsub⟩ := exists_isCompact_snd_subset K S n
  have hC : IsCompact ((compactCovering (InfiniteAdeleRing K) n) ×ˢ F) :=
    (isCompact_compactCovering (InfiniteAdeleRing K) n).prod hF
  have hC' : IsCompact (show Set 𝔸 from (compactCovering (InfiniteAdeleRing K) n) ×ˢ F) := hC
  refine lt_of_le_of_lt (measure_mono ?_) hC'.measure_lt_top
  rintro x ⟨h1, h2⟩
  exact ⟨h1, hsub h2⟩

end Boxes

section Main

open scoped Classical

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "Gp" => Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 K) K)

attribute [local instance] secondCountable_A t1Space_A

theorem countable_v : Countable (HeightOneSpectrum (𝓞 K)) := countable_heightOneSpectrum K

attribute [local instance] countable_v

theorem exists_uniformizer (v : HeightOneSpectrum (𝓞 K)) :
    ∃ π : v.adicCompletion K, π ≠ 0 ∧ Valued.v π = WithZero.exp (-1 : ℤ) ∧
      ‖π‖ = (((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ))⁻¹ := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
  have hπv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hπv
    exact WithZero.zero_ne_coe hπv
  refine ⟨π, hπ0, hπv, ?_⟩
  rw [NumberField.FinitePlace.norm_def, hπv]
  have hne : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ≠ 0 := WithZero.coe_ne_zero
  rw [WithZeroMulInt.toNNReal_neg_apply _ hne]
  have : (WithZero.unzero hne).toAdd = -1 := by
    have h1 : WithZero.unzero hne = Multiplicative.ofAdd (-1 : ℤ) := by
      apply WithZero.coe_injective
      rw [WithZero.coe_unzero]
      rfl
    rw [h1]; rfl
  rw [this, zpow_neg_one, NNReal.coe_inv]

theorem valued_le_exp_neg_one_of_norm_lt_one {v : HeightOneSpectrum (𝓞 K)} {x : v.adicCompletion K}
    (hx : ‖x‖ < 1) : Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  have h1 : Valued.v x < 1 := Valued.toNormedField.norm_lt_one_iff.mp hx
  have h2 : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) * WithZero.exp 1 = 1 := by
    rw [← WithZero.exp_add]; norm_num
  have h3 : Valued.v x < WithZero.exp (-1 : ℤ) * WithZero.exp 1 := by rw [h2]; exact h1
  exact (WithZero.lt_mul_exp_iff_le WithZero.coe_ne_zero).mp h3

theorem measure_sep_norm_lt_one_le (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    μ {x ∈ box K S n | ‖x.2 v‖ < 1} ≤ (((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ≥0∞))⁻¹ * μ (box K S n) := by
  obtain ⟨π, hπ0, hπv, hπn⟩ := exists_uniformizer K v
  set t : (v.adicCompletion K)ˣ := Units.mk0 π hπ0 with ht
  set d : (AdeleRing (𝓞 K) K)ˣ := finUnit v t with hd
  have hsub : {x ∈ box K S n | ‖x.2 v‖ < 1} ⊆ d • box K S n := by
    rintro x ⟨hxE, hxv⟩
    refine ⟨d⁻¹ • x, ?_, smul_inv_smul d x⟩
    have hval : d⁻¹ • x = (((finUnit v t⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : 𝔸) * x := by
      rw [hd, ← finUnit_inv]; rfl
    rw [hval]
    refine ⟨?_, fun u => ?_⟩
    · show ((((finUnit v t⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : 𝔸) * x).1 ∈ _
      have : ((((finUnit v t⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : 𝔸) * x).1 = x.1 := by
        show (((finUnit v t⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : 𝔸).1 * x.1 = x.1
        rw [finUnit_fst, one_mul]
      rw [this]; exact hxE.1
    · show ‖((((finUnit v t⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : 𝔸) * x).2 u‖ ≤ bnd K S n u
      have : ((((finUnit v t⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : 𝔸) * x).2 u =
          Function.update (1 : ∀ u : HeightOneSpectrum (𝓞 K), u.adicCompletion K) v
            ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) u * x.2 u := by
        rw [← finUnit_snd_apply]; rfl
      rw [this]
      by_cases hu : u = v
      · subst hu
        rw [Function.update_self, bnd_of_not_mem K hv]
        have hxle : ‖x.2 u‖ ≤ ‖π‖ := by
          rw [Valued.toNormedField.norm_le_iff, hπv]
          exact valued_le_exp_neg_one_of_norm_lt_one K hxv
        have htinv : ((t⁻¹ : (u.adicCompletion K)ˣ) : u.adicCompletion K) = π⁻¹ := by
          rw [ht, Units.val_inv_eq_inv_val]; rfl
        rw [htinv, norm_mul, norm_inv]
        have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
        rw [inv_mul_le_iff₀ hπpos, mul_one]
        exact hxle
      · rw [Function.update_of_ne hu]
        show ‖(1 : u.adicCompletion K) * x.2 u‖ ≤ bnd K S n u
        rw [one_mul]; exact hxE.2 u
  have hchar : (distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ≥0) = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
    apply NNReal.coe_injective
    rw [hd, distribHaarChar_finUnit, NNReal.coe_inv]
    show ‖π‖ = _
    exact hπn
  calc μ {x ∈ box K S n | ‖x.2 v‖ < 1} ≤ μ (d • box K S n) := measure_mono hsub
    _ = (distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ≥0∞) * μ (box K S n) := (distribHaarChar_mul μ d _).symm
    _ = (((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ≥0∞))⁻¹ * μ (box K S n) := by
        rw [show ((distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ≥0∞)) =
          (((distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ≥0)) : ℝ≥0∞) from rfl, hchar,
          ENNReal.coe_inv (NumberField.HeightOneSpectrum.absNorm_ne_zero v)]

theorem pi_measure_frequently_inter_box_eq_zero (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (Measure.pi fun _ : Fin 2 => μ)
      {c : Fin 2 → 𝔸 | c 0 ∈ box K S n ∧ c 1 ∈ box K S n ∧
        ∃ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1} = 0 := by
  set E := box K S n with hE
  have hEfin : μ E ≠ ⊤ := (measure_box_lt_top K μ S n).ne
  set T : HeightOneSpectrum (𝓞 K) → Set 𝔸 := fun v => {x ∈ E | ‖x.2 v‖ < 1} with hT
  set s : HeightOneSpectrum (𝓞 K) → Set (Fin 2 → 𝔸) := fun v => {c | c 0 ∈ T v ∧ c 1 ∈ T v} with hs

  have hpi : ∀ v, (Measure.pi fun _ : Fin 2 => μ) (s v) = μ (T v) * μ (T v) := by
    intro v
    have : s v = Set.pi Set.univ (fun _ : Fin 2 => T v) := by
      ext c; simp [hs, Fin.forall_fin_two]
    rw [this, Measure.pi_pi]
    simp [pow_two]
  set b : HeightOneSpectrum (𝓞 K) → ℝ≥0∞ := fun v =>
    if v ∈ S then 1 else (((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ≥0∞))⁻¹ with hb
  have hTle : ∀ v, μ (T v) ≤ b v * μ E := by
    intro v
    by_cases hv : v ∈ S
    · rw [hb]; simp only [if_pos hv, one_mul]
      exact measure_mono fun x hx => hx.1
    · rw [hb]; simp only [if_neg hv]
      exact measure_sep_norm_lt_one_le K μ S n hv
  have hb2 : ∀ v, b v * b v ≤ (if v ∈ S then 1 else 0) + ((((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ≥0∞)) ^ 2)⁻¹ := by
    intro v
    by_cases hv : v ∈ S
    · rw [hb]; simp only [if_pos hv, mul_one]; exact le_self_add
    · rw [hb]; simp only [if_neg hv, zero_add]
      rw [pow_two, ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)]
  have hsum : (∑' v, (Measure.pi fun _ : Fin 2 => μ) (s v)) ≠ ⊤ := by
    have h1 : ∀ v, (Measure.pi fun _ : Fin 2 => μ) (s v) ≤
        (μ E * μ E) * ((if v ∈ S then 1 else 0) + ((((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ≥0∞)) ^ 2)⁻¹) := by
      intro v
      rw [hpi]
      calc μ (T v) * μ (T v) ≤ (b v * μ E) * (b v * μ E) := mul_le_mul' (hTle v) (hTle v)
        _ = (μ E * μ E) * (b v * b v) := by ring
        _ ≤ (μ E * μ E) * ((if v ∈ S then 1 else 0) + ((((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ≥0∞)) ^ 2)⁻¹) :=
            mul_le_mul' le_rfl (hb2 v)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h1)
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top hEfin hEfin) ?_
    rw [ENNReal.tsum_add]
    refine ENNReal.add_ne_top.mpr ⟨?_, tsum_absNorm_sq_inv_ne_top K⟩
    rw [tsum_eq_sum (s := S) (fun v hv => if_neg hv)]
    exact ENNReal.sum_ne_top.mpr fun v hv => by rw [if_pos hv]; simp
  have hBC := measure_limsup_cofinite_eq_zero hsum
  refine measure_mono_null ?_ hBC
  rintro c ⟨h0, h1, hfr⟩
  rw [Filter.cofinite.limsup_set_eq, Set.mem_setOf_eq]
  have hinf := Filter.frequently_cofinite_iff_infinite.mp hfr
  refine hinf.mono fun v hv => ?_
  exact ⟨⟨h0, hv.1⟩, ⟨h1, hv.2⟩⟩

theorem pi_measure_frequently_eq_zero (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure] :
    (Measure.pi fun _ : Fin 2 => μ)
      {c : Fin 2 → 𝔸 | ∃ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1} = 0 := by
  have hcov : {c : Fin 2 → 𝔸 | ∃ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1} ⊆
      ⋃ p : Finset (HeightOneSpectrum (𝓞 K)) × ℕ,
        {c : Fin 2 → 𝔸 | c 0 ∈ box K p.1 p.2 ∧ c 1 ∈ box K p.1 p.2 ∧
          ∃ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1} := by
    intro c hc
    obtain ⟨S₀, n₀, h₀⟩ := exists_mem_box K (c 0)
    obtain ⟨S₁, n₁, h₁⟩ := exists_mem_box K (c 1)
    refine Set.mem_iUnion.mpr ⟨(S₀ ∪ S₁, n₀ ⊔ n₁), ?_, ?_, hc⟩
    · exact box_mono K Finset.subset_union_left le_sup_left h₀
    · exact box_mono K Finset.subset_union_right le_sup_right h₁
  refine measure_mono_null hcov (measure_iUnion_null fun p => ?_)
  exact pi_measure_frequently_inter_box_eq_zero K μ p.1 p.2

theorem pi_measure_not_isUnimod_eq_zero (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure] :
    (Measure.pi fun _ : Fin 2 => μ) {c : Fin 2 → 𝔸 | ¬ IsUnimod c} = 0 := by
  have hA₁ : (Measure.pi fun _ : Fin 2 => μ) (⋃ w : InfinitePlace K, {c : Fin 2 → 𝔸 | (c 0).1 w = 0}) = 0 := by
    refine measure_iUnion_null fun w => ?_
    exact Measure.pi_eval_preimage_null (μ := fun _ : Fin 2 => μ) (i := 0)
      (measure_setOf_fst_apply_eq_zero μ w)
  have hA₂ : (Measure.pi fun _ : Fin 2 => μ)
      (⋃ v : HeightOneSpectrum (𝓞 K), {c : Fin 2 → 𝔸 | (c 0).2 v = 0}) = 0 := by
    refine measure_iUnion_null fun v => ?_
    exact Measure.pi_eval_preimage_null (μ := fun _ : Fin 2 => μ) (i := 0)
      (measure_setOf_snd_apply_eq_zero μ v)
  have hA₃ := pi_measure_frequently_eq_zero K μ
  have hsub : {c : Fin 2 → 𝔸 | ¬ IsUnimod c} ⊆
      ((⋃ w : InfinitePlace K, {c : Fin 2 → 𝔸 | (c 0).1 w = 0}) ∪
        (⋃ v : HeightOneSpectrum (𝓞 K), {c : Fin 2 → 𝔸 | (c 0).2 v = 0})) ∪
      {c : Fin 2 → 𝔸 | ∃ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1} := by
    intro c hc
    rw [Set.mem_setOf_eq, IsUnimod] at hc
    by_cases h1 : ∀ w : InfinitePlace K, ¬ ((c 0).1 w = 0 ∧ (c 1).1 w = 0)
    · by_cases h2 : ∀ v : HeightOneSpectrum (𝓞 K), ¬ ((c 0).2 v = 0 ∧ (c 1).2 v = 0)
      · have h3 : ¬ ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ¬ (‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1) :=
          fun h3 => hc ⟨h1, h2, h3⟩
        right
        rw [Set.mem_setOf_eq]
        exact (Filter.not_eventually.mp h3).mono fun v hv => not_not.mp hv
      · left; right
        push Not at h2
        obtain ⟨v, hv⟩ := h2
        exact Set.mem_iUnion.mpr ⟨v, hv.1⟩
    · left; left
      push Not at h1
      obtain ⟨w, hw⟩ := h1
      exact Set.mem_iUnion.mpr ⟨w, hw.1⟩
  refine measure_mono_null hsub ?_
  rw [measure_union_null_iff, measure_union_null_iff]
  exact ⟨⟨hA₁, hA₂⟩, hA₃⟩

theorem main (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure) :
    (Measure.pi fun _ : Fin 2 => μ)
      {c : Fin 2 → AdeleRing (𝓞 K) K | ¬ ∃ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0) = c} = 0 := by
  haveI := hμ
  exact measure_mono_null setOf_not_exists_subset (pi_measure_not_isUnimod_eq_zero K μ)

end Main

end NumberField.UnimodularColumn
p2m_reactivate "P2MW.S_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero.NumberField P2MW.S_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero.NumberField.UnimodularColumn"
p2m_reactivate "P2MW.S_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero.NumberField"

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure) :
    (Measure.pi fun _ : Fin 2 => μ)
      {c : Fin 2 → AdeleRing (𝓞 K) K | ¬ ∃ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0) = c} = 0 :=
  NumberField.UnimodularColumn.main K μ hμ

end
p2m_reactivate "P2MW.S_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero.NumberField P2MW.S_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero.NumberField.UnimodularColumn"

end S_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero
end P2MW
export P2MW.S_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero (solution)
