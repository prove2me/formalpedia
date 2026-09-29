-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/40dec9d1-6708-5ca1-9100-6e1de2ac4443

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicBox
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_NumberField_AdelicBox_inv_measure_adelicBox_mul_integral_pureTensor_eq
import Theorems.Thm_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod
import Theorems.Thm_EisensteinGeneral_Factorization_inv_measure_mul_setIntegral_integralOffSet_finprod_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal NumberField.InfinitePlace

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lowerUnipotent21 lowerUnipotent21_coe globalZeta31 AdelicGL embedMat2 iotaGL coe_iotaGL localMaximalCompact3 mem_localMaximalCompact3_iff archComponentN componentAt3 archComponent3 LocalGL3 diagUnitGL2 coe_diagUnitGL2 diagHom_apply localZeta31 natCard_quot_eq_absNorm ofReal_norm_eq_of_valued_eq"
namespace EulerProductUnipotent
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

noncomputable section

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] LanglandsTunnell.TateLocal.localBorel

open scoped Classical

section Products

open Filter Topology

variable {ι : Type*}

private theorem finite_setOf_le_of_summable_rpow_neg {N : ι → ℕ} (hN : ∀ i, 1 ≤ N i) {σ : ℝ}
    (hs : Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ)) (n : ℕ) : {i | N i ≤ n}.Finite := by
  rcases le_or_gt σ 0 with hσ | hσ
  ·
    have hev := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (zero_lt_one' ℝ))
    rw [Filter.eventually_cofinite] at hev
    refine hev.subset fun i _ => ?_
    simp only [Set.mem_setOf_eq, not_lt]
    have h1 : (1 : ℝ) ≤ N i := by exact_mod_cast hN i
    exact Real.one_le_rpow h1 (neg_nonneg.mpr hσ)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine Set.finite_empty.subset fun i hi => ?_
      have := hN i
      simp only [Set.mem_setOf_eq, nonpos_iff_eq_zero] at hi
      omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hε : (0 : ℝ) < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hnpos _
    have hev := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)
    rw [Filter.eventually_cofinite] at hev
    refine hev.subset fun i hi => ?_
    simp only [Set.mem_setOf_eq, not_lt]
    have hNi : (0 : ℝ) < N i := by exact_mod_cast (hN i)
    have hle : ((N i : ℕ) : ℝ) ≤ n := by exact_mod_cast hi
    exact Real.rpow_le_rpow_of_nonpos hNi hle (neg_nonpos.mpr hσ.le)

private theorem prod_one_add_le_exp_tsum {c : ι → ℝ} (hc0 : ∀ i, 0 ≤ c i) (hc : Summable c)
    (s : Finset ι) : ∏ i ∈ s, (1 + c i) ≤ Real.exp (∑' i, c i) := by
  calc ∏ i ∈ s, (1 + c i) ≤ ∏ i ∈ s, Real.exp (c i) :=
        Finset.prod_le_prod (fun i _ => by linarith [hc0 i]) fun i _ => by
          linarith [Real.add_one_le_exp (c i)]
    _ = Real.exp (∑ i ∈ s, c i) := (Real.exp_sum s c).symm
    _ ≤ Real.exp (∑' i, c i) := Real.exp_le_exp.mpr (hc.sum_le_tsum s fun i _ => hc0 i)

private theorem tendsto_prod_toList_filter_of_hasProd (p : ι → Prop) [DecidablePred p] (g : ι → ℂ) {L : ℂ}
    (hL : HasProd (fun i : {i // p i} => g i.1) L) (N : ι → ℕ) (hfin : ∀ n, {i | N i ≤ n}.Finite) :
    Tendsto (fun n => ((((hfin n).toFinset.filter p).toList.map g).prod)) atTop (𝓝 L) := by
  have hF : Tendsto (fun n => ((hfin n).toFinset.subtype p)) atTop (atTop : Filter (Finset {i // p i})) := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b.sup fun i => N i.1, fun n hn i hi => ?_⟩
    rw [Finset.mem_subtype, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact le_trans (Finset.le_sup (f := fun i : {i // p i} => N i.1) hi) hn
  have h := hL.comp hF
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [Finset.prod_subtype_eq_prod_filter, Finset.prod_map_toList]

end Products

section Remint

open NumberField.AdeleRing NumberField.TateGlobal

private theorem two_le_absNorm {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem ideleNorm_zpow {F : Type} [Field F] [NumberField F] (x : (AdeleRing (𝓞 F) F)ˣ) (m : ℤ) :
    ideleNorm F (x ^ m) = ideleNorm F x ^ m := by
  simp only [ideleNorm, map_zpow, NNReal.coe_zpow]

private theorem ideleNorm_map_prod {F : Type} [Field F] [NumberField F] {ι : Type*} (l : List ι)
    (g : ι → (AdeleRing (𝓞 F) F)ˣ) :
    ideleNorm F (l.map g).prod = (l.map fun i => ideleNorm F (g i)).prod := by
  induction l with
  | nil => simp [ideleNorm]
  | cons i l ih => simp [ideleNorm_mul, ih]

private theorem units_val_map_prod {ι : Type*} (l : List ι) (g : ι → ℂˣ) :
    (((l.map g).prod : ℂˣ) : ℂ) = (l.map fun i => ((g i : ℂˣ) : ℂ)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

private theorem ofReal_map_prod {ι : Type*} (l : List ι) (g : ι → ℝ) :
    (((l.map g).prod : ℝ) : ℂ) = (l.map fun i => ((g i : ℝ) : ℂ)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

private theorem ofReal_map_prod_cpow {ι : Type*} (l : List ι) (g : ι → ℝ) (hg : ∀ i ∈ l, 0 ≤ g i) (z : ℂ) :
    ((((l.map g).prod : ℝ) : ℂ)) ^ z = (l.map fun i => ((g i : ℝ) : ℂ) ^ z).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : 0 ≤ g i := hg i (by simp)
    have hl : 0 ≤ (l.map g).prod := List.prod_nonneg fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact hg j (by simp [hj])
    rw [List.map_cons, List.prod_cons, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hi hl,
      ih fun j hj => hg j (by simp [hj]), List.map_cons, List.prod_cons]

private theorem iUnion_coe_unitIdelesOutside_eq_univ (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Lf : ℕ → List (HeightOneSpectrum (𝓞 F)))
    (hcov : ∀ n : ℕ, ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → Ideal.absNorm v.asIdeal ≤ n → v ∈ Lf n) :
    ⋃ n : ℕ, (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ Lf n}) : Set (AdeleRing (𝓞 F) F)ˣ) =
      Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_

  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (finitePartUnits (𝓞 F) F x : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F ∧
        (((finitePartUnits (𝓞 F) F x)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈
          v.adicCompletionIntegers F := by
    filter_upwards [(finitePartUnits (𝓞 F) F x : FiniteAdeleRing (𝓞 F) F).2,
      (((finitePartUnits (𝓞 F) F x)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F).2] with v h1 h2
    exact ⟨h1, h2⟩
  rw [Filter.eventually_cofinite] at hev

  obtain ⟨n, hn⟩ := (hev.image fun v => Ideal.absNorm v.asIdeal).bddAbove
  refine Set.mem_iUnion.2 ⟨n, ?_⟩
  rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  intro v hv
  by_contra hbad
  have hle : Ideal.absNorm v.asIdeal ≤ n := hn ⟨v, hbad, rfl⟩
  exact hv (Set.mem_union_right _ (hcov n v (fun hvS => hv (Set.mem_union_left _ hvS)) hle))

private theorem monotone_coe_unitIdelesOutside (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Lf : ℕ → List (HeightOneSpectrum (𝓞 F)))
    (hmono : ∀ n : ℕ, Lf n ⊆ Lf (n + 1)) :
    Monotone fun n : ℕ =>
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ Lf n}) : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have hmon : Monotone fun k : ℕ => ({v | v ∈ Lf k} : Set (HeightOneSpectrum (𝓞 F))) :=
    monotone_nat_of_le_succ fun k v hv => hmono k hv
  intro m n hmn x hx
  rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff] at hx ⊢
  exact IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_mono (R := 𝓞 F) (K := F)
    (Set.union_subset_union_right _ (hmon hmn)) hx

end Remint

section Valuations

open IsDedekindDomain.HeightOneSpectrum

variable (v : HeightOneSpectrum (𝓞 ℚ))
private theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((AdelicLevel.uniformizerUnit ℚ v ^ m : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

end Valuations

section Matrices

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_iotaGL_diagUnitGL2 {A : Type*} [CommRing A] (u : Aˣ) :
    ((iotaGL (diagUnitGL2 u) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal ![(u : A), 1, 1] := by
  rw [coe_iotaGL, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal]

private theorem coe_iotaGL_diagUnitGL2_inv {A : Type*} [CommRing A] (u : Aˣ) :
    (((iotaGL (diagUnitGL2 u))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      Matrix.diagonal ![((u⁻¹ : Aˣ) : A), 1, 1] := by
  show embedMat2 !![((u⁻¹ : Aˣ) : A), 0; 0, 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal]

private theorem valued_diagonal_entry_le_one {a : v.adicCompletion ℚ} (ha : Valued.v a ≤ 1) (i j : Fin 3) :
    Valued.v (Matrix.diagonal ![a, 1, 1] i j) ≤ 1 := by
  rw [Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    fin_cases i
    · simpa using ha
    · simp
    · simp
  · simp

private theorem iotaGL_diagUnitGL2_mem {u : (v.adicCompletion ℚ)ˣ} (hu : Valued.v (u : v.adicCompletion ℚ) ≤ 1)
    (hu' : Valued.v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1) :
    iotaGL (diagUnitGL2 u) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff, coe_iotaGL_diagUnitGL2, coe_iotaGL_diagUnitGL2_inv]
  exact ⟨valued_diagonal_entry_le_one v hu, valued_diagonal_entry_le_one v hu'⟩

private theorem iotaGL_diagUnitGL2_mul {A : Type*} [CommRing A] (x y : Aˣ) :
    iotaGL (diagUnitGL2 (x * y)) = iotaGL (diagUnitGL2 x) * iotaGL (diagUnitGL2 y) := by
  rw [← diagHom_apply, ← diagHom_apply, ← diagHom_apply, map_mul, map_mul]

private theorem iotaGL_diagUnitGL2_one {A : Type*} [CommRing A] : iotaGL (diagUnitGL2 (1 : Aˣ)) = 1 := by
  rw [← diagHom_apply, map_one, map_one]

end Matrices

section Components

private abbrev evalAt (v : HeightOneSpectrum (𝓞 ℚ)) : AdeleRing (𝓞 ℚ) ℚ →+* v.adicCompletion ℚ :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private theorem evalAt_apply (v : HeightOneSpectrum (𝓞 ℚ)) (a : AdeleRing (𝓞 ℚ) ℚ) : evalAt v a = a.2 v := rfl

private theorem componentAt3_eq_map (v : HeightOneSpectrum (𝓞 ℚ)) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v x = Matrix.GeneralLinearGroup.map (evalAt v) x := rfl

private abbrev evalUnits (v : HeightOneSpectrum (𝓞 ℚ)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* (v.adicCompletion ℚ)ˣ :=
  Units.map (evalAt v : AdeleRing (𝓞 ℚ) ℚ →* v.adicCompletion ℚ)

private abbrev archUnits : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* (InfiniteAdeleRing ℚ)ˣ :=
  Units.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ : AdeleRing (𝓞 ℚ) ℚ →* InfiniteAdeleRing ℚ)

private theorem coe_evalUnits (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((evalUnits v a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = (a : AdeleRing (𝓞 ℚ) ℚ).2 v := rfl

private theorem coe_evalUnits_inv (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (((evalUnits v a)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v := by
  rw [← map_inv]; rfl

private theorem coe_archUnits (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((archUnits a : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = (a : AdeleRing (𝓞 ℚ) ℚ).1 := rfl

private theorem map_iotaGL_diagUnitGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 (Units.map (f : A →* B) a)) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, MonoidHom.coe_coe, coe_iotaGL_diagUnitGL2]
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  · simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hij]

private theorem componentAt3_iotaGL_diagUnitGL2_mul (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a) * g) =
      iotaGL (diagUnitGL2 (evalUnits v a)) * componentAt3 (𝓞 ℚ) ℚ v g := by
  rw [map_mul, componentAt3_eq_map, map_iotaGL_diagUnitGL2, componentAt3_eq_map]

private theorem archComponent3_iotaGL_diagUnitGL2_mul (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a) * g) =
      iotaGL (diagUnitGL2 (archUnits a)) * archComponent3 (𝓞 ℚ) ℚ g := by
  rw [map_mul]
  congr 1
  exact map_iotaGL_diagUnitGL2 _ a

private theorem iotaGL_diagUnitGL2_units_map_mem (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (h1 : (a : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ)
    (h2 : ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ) :
    iotaGL (diagUnitGL2 (evalUnits v a)) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine iotaGL_diagUnitGL2_mem v ?_ ?_
  · rw [coe_evalUnits]; exact h1
  · rw [coe_evalUnits_inv]; exact h2

end Components

section Unipotent

private theorem componentAt3_lowerUnipotent21 (v : HeightOneSpectrum (𝓞 ℚ)) (x : AdeleRing (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (lowerUnipotent21 x) = lowerUnipotent21 (x.2 v) := by
  rw [componentAt3_eq_map]
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent21, evalAt, AdelicLevel.finAdeleEval_apply, AdelicLevel.adeleFin_apply] <;> rfl

private theorem archComponent3_lowerUnipotent21 (x : AdeleRing (𝓞 ℚ) ℚ) :
    archComponent3 (𝓞 ℚ) ℚ (lowerUnipotent21 x) = lowerUnipotent21 x.1 := by
  apply Units.ext
  simp only [archComponent3, archComponentN, Matrix.GeneralLinearGroup.map, Units.coe_map]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent21, AdelicLevel.adeleArch_apply] <;> rfl

end Unipotent

section UniformizerComponents

private theorem coe_uniformizerIdele_snd (v w : HeightOneSpectrum (𝓞 ℚ)) :
    ((uniformizerIdele ℚ v : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w =
      ((AdelicLevel.localUnit (𝓞 ℚ) ℚ v (AdelicLevel.uniformizerUnit ℚ v) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) w := rfl

private theorem coe_uniformizerIdele_fst (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((uniformizerIdele ℚ v : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := rfl

private theorem evalUnits_uniformizerIdele_self (v : HeightOneSpectrum (𝓞 ℚ)) :
    evalUnits v (uniformizerIdele ℚ v) = AdelicLevel.uniformizerUnit ℚ v := by
  apply Units.ext
  rw [coe_evalUnits, coe_uniformizerIdele_snd, AdelicLevel.localUnit_apply_self]

private theorem evalUnits_uniformizerIdele_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    evalUnits w (uniformizerIdele ℚ v) = 1 := by
  apply Units.ext
  rw [coe_evalUnits, coe_uniformizerIdele_snd, AdelicLevel.localUnit_apply_of_ne _ _ _ _ hw, Units.val_one]

private theorem archUnits_uniformizerIdele (v : HeightOneSpectrum (𝓞 ℚ)) : archUnits (uniformizerIdele ℚ v) = 1 := by
  apply Units.ext
  rw [coe_archUnits, coe_uniformizerIdele_fst, Units.val_one]

private theorem list_prod_map_eq_of_nodup {M : Type*} [CommMonoid M] (L : List (HeightOneSpectrum (𝓞 ℚ)))
    (hL : L.Nodup) (f : HeightOneSpectrum (𝓞 ℚ) → M) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∈ L)
    (hf : ∀ v ∈ L, v ≠ w → f v = 1) : (L.map f).prod = f w := by
  induction L with
  | nil => simp at hw
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons]
    rcases List.mem_cons.mp hw with rfl | hwL
    · rw [List.prod_eq_one fun x hx => ?_, mul_one]
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      exact hf u (List.mem_cons_of_mem _ hu) (fun h => hL.1 (h ▸ hu))
    · rw [ih hL.2 hwL (fun u hu hne => hf u (List.mem_cons_of_mem _ hu) hne), hf v (List.mem_cons_self ..)
        (fun h => hL.1 (h ▸ hwL)), one_mul]

private theorem list_prod_map_eq_one_of_forall {M : Type*} [CommMonoid M] (L : List (HeightOneSpectrum (𝓞 ℚ)))
    (f : HeightOneSpectrum (𝓞 ℚ) → M) (hf : ∀ v ∈ L, f v = 1) : (L.map f).prod = 1 := by
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
  exact hf u hu

private theorem evalUnits_uniformizer_prod_of_mem (L : List (HeightOneSpectrum (𝓞 ℚ))) (hL : L.Nodup)
    (m : HeightOneSpectrum (𝓞 ℚ) → ℤ) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∈ L) :
    evalUnits w (L.map fun v => uniformizerIdele ℚ v ^ m v).prod = AdelicLevel.uniformizerUnit ℚ w ^ m w := by
  rw [map_list_prod, List.map_map]
  rw [list_prod_map_eq_of_nodup L hL _ hw]
  · simp only [Function.comp_apply, map_zpow, evalUnits_uniformizerIdele_self]
  · intro v _ hvw
    simp only [Function.comp_apply, map_zpow, evalUnits_uniformizerIdele_of_ne (Ne.symm hvw), _root_.one_zpow]

private theorem evalUnits_uniformizer_prod_of_not_mem (L : List (HeightOneSpectrum (𝓞 ℚ)))
    (m : HeightOneSpectrum (𝓞 ℚ) → ℤ) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∉ L) :
    evalUnits w (L.map fun v => uniformizerIdele ℚ v ^ m v).prod = 1 := by
  rw [map_list_prod, List.map_map]
  refine list_prod_map_eq_one_of_forall L _ fun v hv => ?_
  have hne : w ≠ v := fun h => hw (h ▸ hv)
  simp only [Function.comp_apply, map_zpow, evalUnits_uniformizerIdele_of_ne hne, _root_.one_zpow]

private theorem archUnits_uniformizer_prod (L : List (HeightOneSpectrum (𝓞 ℚ)))
    (m : HeightOneSpectrum (𝓞 ℚ) → ℤ) :
    archUnits (L.map fun v => uniformizerIdele ℚ v ^ m v).prod = 1 := by
  rw [map_list_prod, List.map_map]
  refine list_prod_map_eq_one_of_forall L _ fun v _ => ?_
  simp only [Function.comp_apply, map_zpow, archUnits_uniformizerIdele, _root_.one_zpow]

end UniformizerComponents

section Pointwise

open NumberField.TateGlobal

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

private theorem evalUnits_eq_one_of_coe_eq_one {w : HeightOneSpectrum (𝓞 ℚ)} {b : (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hb : (b : AdeleRing (𝓞 ℚ) ℚ).2 w = 1) : evalUnits w b = 1 :=
  Units.ext (by rw [coe_evalUnits, hb, Units.val_one])

private theorem archUnits_eq_one_of_coe_eq_one {b : (AdeleRing (𝓞 ℚ) ℚ)ˣ} (hb : (b : AdeleRing (𝓞 ℚ) ℚ).1 = 1) :
    archUnits b = 1 :=
  Units.ext (by rw [coe_archUnits, hb, Units.val_one])

private theorem iotaGL_diagUnitGL2_evalUnits_mem_of_mem_unitIdeles (w : HeightOneSpectrum (𝓞 ℚ))
    {u : (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hu : NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) :
    iotaGL (diagUnitGL2 (evalUnits w u)) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
  rw [← IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_empty,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff] at hu
  obtain ⟨h1, h2⟩ := hu w (Set.notMem_empty w)
  refine iotaGL_diagUnitGL2_units_map_mem w u ?_ ?_
  · simpa using h1
  · first
      | exact h2
      | (simp [AdeleRing.finitePartUnits] at h2; exact h2)

private theorem iotaGL_diagUnitGL2_evalUnits_mem_of_mem_unitIdelesOutside (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ} (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ T)
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∉ T) :
    iotaGL (diagUnitGL2 (evalUnits w a)) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff] at ha
  obtain ⟨h1, h2⟩ := ha w hw
  refine iotaGL_diagUnitGL2_units_map_mem w a ?_ ?_
  · simpa using h1
  · first
      | exact h2
      | (simp [AdeleRing.finitePartUnits] at h2; exact h2)

private theorem char_eq_mul_prod (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (L : List (HeightOneSpectrum (𝓞 ℚ)))
    (m : HeightOneSpectrum (𝓞 ℚ) → ℤ) (b u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : χ u = 1) :
    ((χ (b * (L.map fun v => uniformizerIdele ℚ v ^ m v).prod * u) : ℂˣ) : ℂ) =
      ((χ b : ℂˣ) : ℂ) * (L.map fun v => ((χ (uniformizerIdele ℚ v) ^ m v : ℂˣ) : ℂ)).prod := by
  rw [map_mul, map_mul, hu, mul_one, map_list_prod, List.map_map, Units.val_mul, units_val_map_prod]
  congr 1
  exact congrArg List.prod (List.map_congr_left fun v _ => by simp only [Function.comp_apply, map_zpow])

private theorem norm_cpow_eq_mul_prod (L : List (HeightOneSpectrum (𝓞 ℚ))) (m : HeightOneSpectrum (𝓞 ℚ) → ℤ)
    (b u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : ideleNorm ℚ u = 1) (s : ℂ) :
    ((ideleNorm ℚ (b * (L.map fun v => uniformizerIdele ℚ v ^ m v).prod * u) : ℝ) : ℂ) ^ (s - 1) =
      ((ideleNorm ℚ b : ℝ) : ℂ) ^ (s - 1) *
        (L.map fun v => (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ m v : ℝ) : ℂ) ^ (s - 1))).prod := by
  have hprod : ideleNorm ℚ (L.map fun v => uniformizerIdele ℚ v ^ m v).prod =
      (L.map fun v => (((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ m v : ℝ)).prod := by
    rw [ideleNorm_map_prod]
    exact congrArg List.prod (List.map_congr_left fun v _ => by rw [ideleNorm_zpow, ideleNorm_uniformizerIdele])
  have hnn : ∀ v ∈ L, (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ m v := fun v _ =>
    zpow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _
  rw [ideleNorm_mul, ideleNorm_mul, hu, mul_one, hprod, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (ideleNorm_pos b).le (List.prod_nonneg fun x hx => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      exact hnn v hv), ofReal_map_prod_cpow L _ hnn]

end Pointwise

section Measures

private abbrev finBorel : MeasurableSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := borel _

private theorem finBorelSpace : @BorelSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) _ finBorel :=
  letI := finBorel; ⟨rfl⟩

private def integralCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing (𝓞 ℚ) ℚ) where
  carrier := NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ
  isCompact' := AdelicBox.isCompact_integralFiniteAdeles ℚ
  interior_nonempty' := by
    rw [(AdelicBox.isOpen_integralFiniteAdeles ℚ).interior_eq]
    exact ⟨0, fun w => (w.adicCompletionIntegers ℚ).zero_mem⟩

private def finHaar : @Measure (FiniteAdeleRing (𝓞 ℚ) ℚ) finBorel :=
  letI := finBorel
  haveI := finBorelSpace
  Measure.addHaarMeasure integralCompacts

private theorem isAddHaarMeasure_finHaar : @Measure.IsAddHaarMeasure _ _ _ finBorel finHaar := by
  letI := finBorel
  haveI := finBorelSpace
  exact Measure.isAddHaarMeasure_addHaarMeasure integralCompacts

private abbrev locBorel : ∀ v : HeightOneSpectrum (𝓞 ℚ), MeasurableSpace (v.adicCompletion ℚ) :=
  fun v => localBorel ℚ v

private theorem locBorelSpace : ∀ v : HeightOneSpectrum (𝓞 ℚ), @BorelSpace (v.adicCompletion ℚ) _ (locBorel v) :=
  fun v => letI := localBorel ℚ v; ⟨rfl⟩

private theorem isAddHaarMeasure_selfDualHaarAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    @Measure.IsAddHaarMeasure _ _ _ (locBorel v) (selfDualHaarAt ℚ v) := by
  unfold selfDualHaarAt
  apply Measure.IsAddHaarMeasure.nnreal_smul
  exact (NNReal.rpow_pos (Nat.cast_pos.mpr (lt_of_lt_of_le two_pos (two_le_absNorm v)))).ne'

private theorem selfDualHaarAt_real_integers_pos (v : HeightOneSpectrum (𝓞 ℚ)) :
    0 < (selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  haveI := locBorelSpace v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  rw [measureReal_def]
  refine ENNReal.toReal_pos ((Valued.isOpen_valuationSubring _).measure_ne_zero _ ⟨0, Subring.zero_mem _⟩) ?_
  have hc : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts]
    exact (integersPositiveCompacts ℚ v).isCompact
  exact hc.measure_lt_top.ne

end Measures

section LocalMeasure

open NumberField.TateGlobal
open scoped Pointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_eq_one_of_le_one_of_inv_le_one {ε : (v.adicCompletion ℚ)ˣ}
    (h1 : Valued.v (ε : v.adicCompletion ℚ) ≤ 1)
    (h2 : Valued.v ((ε⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1) :
    Valued.v (ε : v.adicCompletion ℚ) = 1 := by
  have hmul : Valued.v (ε : v.adicCompletion ℚ) * Valued.v ((ε⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)
      = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v (ε : v.adicCompletion ℚ) * Valued.v ((ε⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) :=
        hmul.symm
    _ ≤ Valued.v (ε : v.adicCompletion ℚ) * 1 := mul_le_mul_right h2 _
    _ = Valued.v (ε : v.adicCompletion ℚ) := mul_one _

private theorem valued_inv_le_one_of_eq_one {ε : (v.adicCompletion ℚ)ˣ} (hε : Valued.v (ε : v.adicCompletion ℚ) = 1) :
    Valued.v ((ε⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, hε, inv_one]

private theorem valued_evalUnits_eq_one_of_mem_unitIdeles {u : (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hu : NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) :
    Valued.v ((evalUnits v u : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  rw [← IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_empty,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff] at hu
  obtain ⟨h1, h2⟩ := hu v (Set.notMem_empty v)
  refine valued_eq_one_of_le_one_of_inv_le_one v ?_ ?_
  · rw [coe_evalUnits]
    simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using h1
  · rw [coe_evalUnits_inv]
    first
      | exact h2
      | (simp [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, AdeleRing.finitePartUnits] at h2; exact h2)

private theorem valued_evalUnits_eq_one_of_mem_unitIdelesOutside (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ} (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ T) (hv : v ∉ T) :
    Valued.v ((evalUnits v a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff] at ha
  obtain ⟨h1, h2⟩ := ha v hv
  refine valued_eq_one_of_le_one_of_inv_le_one v ?_ ?_
  · rw [coe_evalUnits]
    simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using h1
  · rw [coe_evalUnits_inv]
    first
      | exact h2
      | (simp [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, AdeleRing.finitePartUnits] at h2; exact h2)

private theorem iotaGL_diagUnitGL2_mem_of_valued_eq_one {ε : (v.adicCompletion ℚ)ˣ}
    (hε : Valued.v (ε : v.adicCompletion ℚ) = 1) : iotaGL (diagUnitGL2 ε) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v :=
  iotaGL_diagUnitGL2_mem v hε.le (valued_inv_le_one_of_eq_one v hε)

private theorem norm_eq_one_of_valued_eq_one {ε : v.adicCompletion ℚ} (hε : Valued.v ε = 1) : ‖ε‖ = 1 := by
  have h := ofReal_norm_eq_of_valued_eq v (a := 0) (by simpa using hε)
  simpa using h

private theorem distribHaarChar_eq_one {ε : (v.adicCompletion ℚ)ˣ} (hε : Valued.v (ε : v.adicCompletion ℚ) = 1) :
    distribHaarChar (v.adicCompletion ℚ) ε = 1 := by
  rw [← modulus_coe_units, modulus_adicCompletion_eq_nnnorm]
  ext
  simp [norm_eq_one_of_valued_eq_one v hε]

private theorem regular_selfDualHaarAt : (selfDualHaarAt ℚ v).Regular := by
  unfold selfDualHaarAt
  infer_instance

private theorem map_mul_left_selfDualHaarAt {ε : (v.adicCompletion ℚ)ˣ} (hε : Valued.v (ε : v.adicCompletion ℚ) = 1) :
    Measure.map (fun t : v.adicCompletion ℚ => (ε : v.adicCompletion ℚ) * t) (selfDualHaarAt ℚ v) =
      selfDualHaarAt ℚ v := by
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := regular_selfDualHaarAt v
  haveI := locBorelSpace v
  have hcont : Continuous fun t : v.adicCompletion ℚ => (ε : v.adicCompletion ℚ) * t :=
    continuous_const.mul continuous_id
  ext U hU
  rw [Measure.map_apply hcont.measurable hU]
  have hpre : (fun t : v.adicCompletion ℚ => (ε : v.adicCompletion ℚ) * t) ⁻¹' U =
      (ε⁻¹ : (v.adicCompletion ℚ)ˣ) • U := by
    ext t
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]
  rw [hpre, ← distribHaarChar_mul (selfDualHaarAt ℚ v) ε⁻¹ U, map_inv, distribHaarChar_eq_one v hε, inv_one,
    ENNReal.coe_one, one_mul]

private theorem integral_comp_unit_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ε : (v.adicCompletion ℚ)ˣ}
    (hε : Valued.v (ε : v.adicCompletion ℚ) = 1) (h : v.adicCompletion ℚ → E) :
    ∫ t, h ((ε : v.adicCompletion ℚ) * t) ∂(selfDualHaarAt ℚ v) = ∫ t, h t ∂(selfDualHaarAt ℚ v) := by
  haveI := locBorelSpace v
  let e : v.adicCompletion ℚ ≃ᵐ v.adicCompletion ℚ :=
    (Homeomorph.mulLeft₀ (ε : v.adicCompletion ℚ) ε.ne_zero).toMeasurableEquiv
  have he : ⇑e = fun t : v.adicCompletion ℚ => (ε : v.adicCompletion ℚ) * t := rfl
  have hmap : Measure.map e (selfDualHaarAt ℚ v) = selfDualHaarAt ℚ v := by
    rw [he]
    exact map_mul_left_selfDualHaarAt v hε
  calc ∫ t, h ((ε : v.adicCompletion ℚ) * t) ∂(selfDualHaarAt ℚ v)
      = ∫ t, h (e t) ∂(selfDualHaarAt ℚ v) := rfl
    _ = ∫ t, h t ∂(Measure.map e (selfDualHaarAt ℚ v)) := (integral_map_equiv e h).symm
    _ = ∫ t, h t ∂(selfDualHaarAt ℚ v) := by rw [hmap]

end LocalMeasure

section ShellIntegral

private theorem iotaGL_diagUnitGL2_mul_lowerUnipotent21 {A : Type*} [CommRing A] (ε : Aˣ) (t : A) :
    iotaGL (diagUnitGL2 ε) * lowerUnipotent21 ((ε : A) * t) = lowerUnipotent21 t * iotaGL (diagUnitGL2 ε) := by
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent21, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

private theorem componentAt3_iotaGL_diagUnitGL2 (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 (evalUnits v a)) := by
  rw [componentAt3_eq_map, map_iotaGL_diagUnitGL2]

private theorem archComponent3_iotaGL_diagUnitGL2 (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 (archUnits a)) :=
  map_iotaGL_diagUnitGL2 _ a

private theorem lowerUnipotent21_mem (v : HeightOneSpectrum (𝓞 ℚ)) {t : v.adicCompletion ℚ}
    (ht : t ∈ v.adicCompletionIntegers ℚ) : lowerUnipotent21 t ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have ht' : Valued.v t ≤ 1 := by simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using ht
  have hinv : (lowerUnipotent21 t)⁻¹ = lowerUnipotent21 (-t) := Units.ext rfl
  rw [mem_localMaximalCompact3_iff, hinv]
  simp only [lowerUnipotent21_coe]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;> simp [ht']

variable (v : HeightOneSpectrum (𝓞 ℚ)) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Wv : LocalGL3 v → E)

private theorem integral_mul_unit_eq
    (hKv : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wv (y * k) = Wv y) (b : (v.adicCompletion ℚ)ˣ)
    {ε : (v.adicCompletion ℚ)ˣ} (hε : Valued.v (ε : v.adicCompletion ℚ) = 1) {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    ∫ t, Wv (iotaGL (diagUnitGL2 (b * ε)) * lowerUnipotent21 t * k) ∂(selfDualHaarAt ℚ v) =
      ∫ t, Wv (iotaGL (diagUnitGL2 b) * lowerUnipotent21 t) ∂(selfDualHaarAt ℚ v) := by
  rw [← integral_comp_unit_mul v hε fun t => Wv (iotaGL (diagUnitGL2 (b * ε)) * lowerUnipotent21 t * k)]
  congr 1
  funext t
  rw [iotaGL_diagUnitGL2_mul, mul_assoc (iotaGL (diagUnitGL2 b)), iotaGL_diagUnitGL2_mul_lowerUnipotent21,
    ← mul_assoc, mul_assoc, hKv _ (mul_mem (iotaGL_diagUnitGL2_mem_of_valued_eq_one v hε) hk)]

end ShellIntegral

section Objects

open NumberField.TateGlobal

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
  (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
  (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)

private def nloc (v : HeightOneSpectrum (𝓞 ℚ)) (h : v.adicCompletion ℚ → ℂ) : ℂ :=
  letI := localBorel ℚ v
  (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ)⁻¹ *
    ∫ y, h y ∂(selfDualHaarAt ℚ v)

private def hfam (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ) : ℂ :=
  Wloc v (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) * lowerUnipotent21 t * componentAt3 (𝓞 ℚ) ℚ v g)

private def farch (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (y : mixedEmbedding.mixedSpace ℚ) : ℂ :=
  Warch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
    lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)

private def tIdent (v : HeightOneSpectrum (𝓞 ℚ)) : ℂ := nloc v fun y => Wloc v (lowerUnipotent21 y)

private def zsh (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℤ) (t : v.adicCompletion ℚ) : ℂ :=
  Wloc v (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ m)) * lowerUnipotent21 t)

private def phiSh (s : ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℤ) : ℂ :=
  nloc v (zsh Wloc v m) * ((χ (uniformizerIdele ℚ v) ^ m : ℂˣ) : ℂ) *
    ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ m : ℝ) : ℂ) ^ (s - 1)

private def sPart (s : ℂ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℂ :=
  (∫ y, farch Warch g a y) * (∏ v ∈ S, nloc v (hfam Wloc g a v)) * ((χ a : ℂˣ) : ℂ) *
    ((ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)

private def innerInt (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℂ :=
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  ∫ x : AdeleRing (𝓞 ℚ) ℚ, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g)
    ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)

private def zetaFn (s : ℂ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℂ :=
  innerInt W g a * ((χ a : ℂˣ) : ℂ) * ((ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)

private theorem globalZeta31_eq (s : ℂ) :
    globalZeta31 W χ s g = ∫ a, zetaFn W χ g s a ∂(NumberField.Idele.idelicHaar ℚ) := rfl

private def boxConst : ℂ :=
  ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
    (((2 : ℝ) ^ nrComplexPlaces ℚ / Real.sqrt |(discr ℚ : ℝ)| : ℝ) : ℂ)

private theorem boxConst_ne_zero : boxConst ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · refine Complex.ofReal_ne_zero.mpr ?_
    exact (ENNReal.toReal_pos (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
      (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne).ne'
  · refine Complex.ofReal_ne_zero.mpr ?_
    refine (div_pos (pow_pos two_pos _) (Real.sqrt_pos.mpr (abs_pos.mpr ?_))).ne'
    exact_mod_cast NumberField.discr_ne_zero (K := ℚ)

end Objects

section Additive

open NumberField.TateGlobal

private theorem measurableSet_integralOff (T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    @MeasurableSet (FiniteAdeleRing (𝓞 ℚ) ℚ) finBorel
      {x : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ T → x v ∈ v.adicCompletionIntegers ℚ} := by
  letI := finBorel
  haveI := finBorelSpace
  refine IsOpen.measurableSet ?_
  exact RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (A := fun v : HeightOneSpectrum (𝓞 ℚ) => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    (p := fun v => v ∉ T) Fact.out

private theorem finHaar_integralCompacts : finHaar (integralCompacts : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 := by
  letI := finBorel
  haveI := finBorelSpace
  exact Measure.addHaarMeasure_self

private theorem coe_integralCompacts :
    (integralCompacts : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) = NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ := rfl

private theorem finHaar_integralFiniteAdeles : finHaar (NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) = 1 := by
  rw [← coe_integralCompacts]
  exact finHaar_integralCompacts

private theorem finHaar_real_integralFiniteAdeles :
    finHaar.real (NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) = 1 := by
  rw [measureReal_def, finHaar_integralFiniteAdeles, ENNReal.toReal_one]

private theorem tendsto_setIntegral_exhaust (F : FiniteAdeleRing (𝓞 ℚ) ℚ → ℂ) (hF : Integrable F finHaar)
    (U : ℕ → Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hUmeas : ∀ n, @MeasurableSet (FiniteAdeleRing (𝓞 ℚ) ℚ) finBorel (U n))
    (hUmono : Monotone U) (hUn : ⋃ n, U n = Set.univ) :
    Filter.Tendsto (fun n => ∫ x in U n, F x ∂finHaar) Filter.atTop (nhds (∫ x, F x ∂finHaar)) := by
  letI := finBorel
  have h := tendsto_setIntegral_of_monotone hUmeas hUmono hF.integrableOn
  rwa [hUn, setIntegral_univ] at h

private theorem finHaar_integral_finprod_eq_tprod (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletion ℚ → ℂ)
    (h₁ : ∀ v ∉ T, ∀ y : v.adicCompletion ℚ, y ∈ v.adicCompletionIntegers ℚ → h v y = 1)
    (hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ T} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
          * (∫ y, ‖h v.1 y‖ ∂(selfDualHaarAt ℚ v.1)) - 1) :
    letI := finBorel
    ((finHaar.real (NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) : ℝ) : ℂ)⁻¹ *
        ∫ x, ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), h v (x v) ∂finHaar
      = ∏' v : HeightOneSpectrum (𝓞 ℚ), nloc v (h v) := by
  letI := finBorel
  haveI := finBorelSpace
  haveI : finHaar.IsAddHaarMeasure := isAddHaarMeasure_finHaar
  haveI : ∀ v : HeightOneSpectrum (𝓞 ℚ), BorelSpace (v.adicCompletion ℚ) := locBorelSpace
  haveI : ∀ v : HeightOneSpectrum (𝓞 ℚ), (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt
  by_cases hall : ∀ v : HeightOneSpectrum (𝓞 ℚ), Integrable (h v) (selfDualHaarAt ℚ v)
  · exact (EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod ℚ finHaar T
      (fun v => selfDualHaarAt ℚ v) h h₁ hall hsum).2.trans (tprod_congr fun v => rfl)
  obtain ⟨v₀, hv₀⟩ := not_forall.mp hall
  have hz : nloc v₀ (h v₀) = 0 := by
    simp only [nloc]
    rw [integral_undef hv₀, mul_zero]
  rw [(hasProd_zero_of_exists_eq_zero ⟨v₀, hz⟩).tprod_eq]

  have hset : ∀ T' : Finset (HeightOneSpectrum (𝓞 ℚ)), T ⊆ T' → v₀ ∈ T' →
      (∫ x in {x : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ T' → x v ∈ v.adicCompletionIntegers ℚ},
        ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), h v (x v) ∂finHaar) = 0 := by
    intro T' hTT' hv₀T'
    have hrow := EisensteinGeneral.Factorization.inv_measure_mul_setIntegral_integralOffSet_finprod_eq ℚ finHaar T'
      (fun v => selfDualHaarAt ℚ v) h (fun v hv => h₁ v (fun hvT => hv (hTT' hvT)))
    rw [finHaar_real_integralFiniteAdeles, Complex.ofReal_one, inv_one, one_mul] at hrow
    rw [hrow]
    refine Finset.prod_eq_zero hv₀T' ?_
    rw [integral_undef hv₀, mul_zero]
  by_cases hF : Integrable (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), h v (x v)) finHaar
  ·
    have hA : Summable fun v : HeightOneSpectrum (𝓞 ℚ) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(4 : ℝ)) :=
      NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt ℚ (by norm_num)
    have hfin : ∀ n : ℕ, {v : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm v.asIdeal ≤ n}.Finite := fun n =>
      finite_setOf_le_of_summable_rpow_neg (fun v => le_trans one_le_two (two_le_absNorm v)) hA n
    obtain ⟨Tn, hTn⟩ : ∃ Tn : ℕ → Finset (HeightOneSpectrum (𝓞 ℚ)), Tn = fun n => T ∪ {v₀} ∪ (hfin n).toFinset :=
      ⟨_, rfl⟩
    obtain ⟨U, hU⟩ : ∃ U : ℕ → Set (FiniteAdeleRing (𝓞 ℚ) ℚ), U = fun n =>
        {x | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ Tn n → x v ∈ v.adicCompletionIntegers ℚ} := ⟨_, rfl⟩
    have hUmeas : ∀ n, MeasurableSet (U n) := fun n => by
      rw [hU]
      exact measurableSet_integralOff (Tn n)
    have hUmono : Monotone U := by
      rw [hU]
      refine monotone_nat_of_le_succ fun n x hx v hv => hx v fun hvn => hv ?_
      simp only [hTn, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hvn ⊢
      rcases hvn with (h' | h') | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr h')
      · exact Or.inr (h'.trans (Nat.le_succ n))
    have hUn : ⋃ n, U n = Set.univ := by
      refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
      have hxfin : {v : HeightOneSpectrum (𝓞 ℚ) | x v ∉ v.adicCompletionIntegers ℚ}.Finite :=
        Filter.eventually_cofinite.mp
        (RestrictedProduct.eventually (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
          (fun v : HeightOneSpectrum (𝓞 ℚ) => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) x)
      refine ⟨hxfin.toFinset.sup fun w => Ideal.absNorm w.asIdeal, ?_⟩
      rw [hU]
      intro v hv
      by_contra hxv
      refine hv ?_
      have hle : Ideal.absNorm v.asIdeal ≤ hxfin.toFinset.sup fun w => Ideal.absNorm w.asIdeal :=
        Finset.le_sup (f := fun w : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm w.asIdeal) (hxfin.mem_toFinset.2 hxv)
      have hmem : v ∈ (hfin (hxfin.toFinset.sup fun w => Ideal.absNorm w.asIdeal)).toFinset :=
        (hfin _).mem_toFinset.2 hle
      simp only [hTn]
      exact Finset.mem_union_right _ hmem
    have hlim := tendsto_setIntegral_exhaust _ hF U hUmeas hUmono hUn
    have hzero : ∀ n, (∫ x in U n, ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), h v (x v) ∂finHaar) = 0 := fun n => by
      rw [hU]
      exact hset (Tn n) (fun v hv => by simp [hTn, hv]) (by simp [hTn])
    simp only [hzero] at hlim
    rw [tendsto_nhds_unique hlim tendsto_const_nhds, mul_zero]
  · rw [integral_undef hF, mul_zero]

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
  (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
  (g : AdelicGL 3 (𝓞 ℚ) ℚ)

private theorem hfam_eq_one_of_mem (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v,
      Wloc v (y * k) = Wloc v y) (hW1 : ∀ v, v ∉ S → Wloc v 1 = 1)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L})) (v : HeightOneSpectrum (𝓞 ℚ))
    (hvS : v ∉ S) (hvL : v ∉ L) {t : v.adicCompletion ℚ} (ht : t ∈ v.adicCompletionIntegers ℚ) :
    hfam Wloc g a v t = 1 := by
  have hε := valued_evalUnits_eq_one_of_mem_unitIdelesOutside v _ ha (by simp [hvS, hvL])
  have hmem : componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) * lowerUnipotent21 t * componentAt3 (𝓞 ℚ) ℚ v g ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    rw [componentAt3_iotaGL_diagUnitGL2]
    exact mul_mem (mul_mem (iotaGL_diagUnitGL2_mem_of_valued_eq_one v hε) (lowerUnipotent21_mem v ht)) (hg v hvS)
  have h := hK v hvS _ hmem 1
  rw [one_mul] at h
  simp only [hfam]
  rw [h, hW1 v hvS]

private theorem integral_norm_hfam_eq (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v,
      Wloc v (y * k) = Wloc v y)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L})) (v : HeightOneSpectrum (𝓞 ℚ))
    (hvS : v ∉ S) (hvL : v ∉ L) :
    ∫ t, ‖hfam Wloc g a v t‖ ∂(selfDualHaarAt ℚ v) = ∫ t, ‖Wloc v (lowerUnipotent21 t)‖ ∂(selfDualHaarAt ℚ v) := by
  have hε := valued_evalUnits_eq_one_of_mem_unitIdelesOutside v _ ha (by simp [hvS, hvL])
  have hKn : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, ‖Wloc v (y * k)‖ = ‖Wloc v y‖ :=
    fun k hk y => by rw [hK v hvS k hk y]
  have key := integral_mul_unit_eq v (fun y => ‖Wloc v y‖) hKn 1 hε (hg v hvS)
  simp only [iotaGL_diagUnitGL2_one, one_mul] at key
  simp only [hfam, componentAt3_iotaGL_diagUnitGL2]
  exact key

private theorem integrand_eq_farch_mul_finprod
    (hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W x = Warch (archComponent3 (𝓞 ℚ) ℚ x) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v x))
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hW1 : ∀ v, v ∉ S → Wloc v 1 = 1)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L})) (x : AdeleRing (𝓞 ℚ) ℚ) :
    W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) =
      farch Warch g a (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), hfam Wloc g a v (x.2 v) := by
  have hxfin : {v : HeightOneSpectrum (𝓞 ℚ) | x.2 v ∉ v.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp
      (RestrictedProduct.eventually (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
        (fun v : HeightOneSpectrum (𝓞 ℚ) => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) x.2)
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), T = S ∪ L.toFinset ∪ hxfin.toFinset := ⟨_, rfl⟩
  have hST : S ⊆ T := fun v hv => by simp [hT, hv]
  have hcomp : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Wloc v (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g)) = hfam Wloc g a v (x.2 v) :=
    fun v => by simp only [hfam, map_mul, componentAt3_lowerUnipotent21]
  have hoff : ∀ v, v ∉ T → hfam Wloc g a v (x.2 v) = 1 := by
    intro v hvT
    have hvS : v ∉ S := fun hv => hvT (by simp [hT, hv])
    have hvL : v ∉ L := fun hv => hvT (by simp [hT, hv])
    have hvx : x.2 v ∈ v.adicCompletionIntegers ℚ := by
      by_contra hv
      exact hvT (by simp [hT, hv])
    exact hfam_eq_one_of_mem S Wloc g hK hW1 hg L a ha v hvS hvL hvx
  have hK' : ∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∈
      localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    intro v hvT
    have hvS : v ∉ S := fun hv => hvT (by simp [hT, hv])
    have hvL : v ∉ L := fun hv => hvT (by simp [hT, hv])
    have hvx : x.2 v ∈ v.adicCompletionIntegers ℚ := by
      by_contra hv
      exact hvT (by simp [hT, hv])
    have hε := valued_evalUnits_eq_one_of_mem_unitIdelesOutside v _ ha (by simp [hvS, hvL])
    rw [map_mul, map_mul, componentAt3_iotaGL_diagUnitGL2, componentAt3_lowerUnipotent21]
    exact mul_mem (mul_mem (iotaGL_diagUnitGL2_mem_of_valued_eq_one v hε) (lowerUnipotent21_mem v hvx)) (hg v hvS)
  rw [hfac _ T hST hK']
  have harch : Warch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g)) =
      farch Warch g a (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) := by
    simp only [farch, map_mul, archComponent3_lowerUnipotent21, RingEquiv.symm_apply_apply]
  have hsupp : (Function.mulSupport fun v => hfam Wloc g a v (x.2 v)) ⊆ ↑T := fun v hv => by
    by_contra hvT
    exact hv (hoff v hvT)
  rw [harch, finprod_eq_prod_of_mulSupport_subset _ hsupp]
  congr 1

private theorem innerInt_eq
    (hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W x = Warch (archComponent3 (𝓞 ℚ) ℚ x) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v x))
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hW1 : ∀ v, v ∉ S → Wloc v 1 = 1)
    (hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
          * (∫ y, ‖Wloc v.1 (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L})) :
    innerInt W g a =
      boxConst * (∫ y, farch Warch g a y) * ∏' v : HeightOneSpectrum (𝓞 ℚ), nloc v (hfam Wloc g a v) := by
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  letI := finBorel
  haveI := finBorelSpace
  haveI : finHaar.IsAddHaarMeasure := isAddHaarMeasure_finHaar
  have hpt : (fun x : AdeleRing (𝓞 ℚ) ℚ => W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g)) = fun x =>
      farch Warch g a (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), hfam Wloc g a v (x.2 v) :=
    funext fun x => integrand_eq_farch_mul_finprod S W Warch Wloc g hfac hK hW1 hg L a ha x

  have hfinite := finHaar_integral_finprod_eq_tprod (S ∪ L.toFinset) (hfam Wloc g a)
    (fun v hv y hy => hfam_eq_one_of_mem S Wloc g hK hW1 hg L a ha v (fun h => hv (Finset.mem_union_left _ h))
      (fun h => hv (Finset.mem_union_right _ (List.mem_toFinset.2 h))) hy) ?_
  swap
  · have hinj : Function.Injective fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S ∪ L.toFinset} =>
        (⟨v.1, fun h => v.2 (Finset.mem_union_left _ h)⟩ : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}) := by
      intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext h
    have h := hsum.comp_injective hinj
    refine h.congr fun v => ?_
    have hvS : v.1 ∉ S := fun h' => v.2 (Finset.mem_union_left _ h')
    have hvL : v.1 ∉ L := fun h' => v.2 (Finset.mem_union_right _ (List.mem_toFinset.2 h'))
    simp only [Function.comp]
    rw [integral_norm_hfam_eq S Wloc g hK hg L a ha v.1 hvS hvL]
  simp only [measureReal_def] at hfinite

  have hsplit := NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq ℚ
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) finHaar (farch Warch g a)
    (fun z => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), hfam Wloc g a v (z v))
  rw [hfinite] at hsplit
  have hvol : ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
      (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne).ne'
  simp only [innerInt]
  rw [hpt]
  have h2 := congrArg
    (fun z : ℂ => ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) * z) hsplit
  beta_reduce at h2
  rw [← mul_assoc, mul_inv_cancel₀ hvol, one_mul] at h2
  rw [h2, boxConst]
  ring

end Additive

namespace ModuleInvariance

open scoped NNReal ENNReal Pointwise

variable {K : Type*} [Field K]

private theorem smul_fun_eq (u : Kˣ) : (fun x : K => u • x) = fun x : K => (u : K) * x := by
  funext x
  rw [Units.smul_def, smul_eq_mul]

private theorem preimage_mul_left (u : Kˣ) (s : Set K) : (fun x : K => (u : K) * x) ⁻¹' s = u⁻¹ • s := by
  rw [← smul_fun_eq u]
  exact Set.preimage_smul u s

private theorem preimage_mul_left_inter_compl (u : Kˣ) (s : Set K) :
    (fun x : K => (u : K) * x) ⁻¹' (s ∩ {0}ᶜ) = (fun x : K => (u : K) * x) ⁻¹' s ∩ {0}ᶜ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
    mul_eq_zero, Units.ne_zero, false_or]

section Topology

variable [TopologicalSpace K] [IsTopologicalRing K]

section Module

variable [LocallyCompactSpace K]

private theorem modulus_mul_inv_coe (u : Kˣ) (x : K) :
    ((modulus ((u : K) * x) : ℝ≥0∞))⁻¹ =
      ((distribHaarChar K u : ℝ≥0∞))⁻¹ * ((modulus x : ℝ≥0∞))⁻¹ := by
  rw [modulus_mul, modulus_coe_units, ENNReal.coe_mul,
    ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)]

end Module

section Equiv

variable [MeasurableSpace K] [BorelSpace K]

private def mulLeftEquiv (u : Kˣ) : K ≃ᵐ K :=
  (Homeomorph.mulLeft₀ (u : K) u.ne_zero).toMeasurableEquiv

private theorem coe_mulLeftEquiv (u : Kˣ) : ⇑(mulLeftEquiv u) = fun x : K => (u : K) * x := by
  funext x
  rfl

private theorem measurable_mul_left (u : Kˣ) : Measurable fun x : K => (u : K) * x := by
  rw [← coe_mulLeftEquiv u]
  exact (mulLeftEquiv u).measurable

end Equiv

variable [LocallyCompactSpace K] [MeasurableSpace K]

private theorem mulMeasure_apply (μ : Measure K) {s : Set K} (hs : MeasurableSet s) :
    mulMeasure μ s = ∫⁻ x in s ∩ {0}ᶜ, ((modulus x : ℝ≥0∞))⁻¹ ∂μ := by
  rw [mulMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]

variable [BorelSpace K]

private theorem map_mul_left_eq_smul (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (u : Kˣ) :
    Measure.map (fun x : K => (u : K) * x) μ = ((distribHaarChar K u : ℝ≥0∞))⁻¹ • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_mul_left u) hs, preimage_mul_left u s, Measure.smul_apply, smul_eq_mul,
    ← ENNReal.coe_inv (distribHaarChar_pos.ne'), ← map_inv (distribHaarChar K) u]
  exact (distribHaarChar_mul μ u⁻¹ s).symm

variable [T2Space K]

private theorem setLIntegral_preimage_mul_left (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (u : Kˣ) {s : Set K}
    (hs : MeasurableSet s) (g : K → ℝ≥0∞) :
    ∫⁻ x in (fun x : K => (u : K) * x) ⁻¹' (s ∩ {0}ᶜ), g ((u : K) * x) ∂μ =
      ((distribHaarChar K u : ℝ≥0∞))⁻¹ * ∫⁻ y in s ∩ {0}ᶜ, g y ∂μ := by
  have hsm : MeasurableSet (s ∩ {0}ᶜ) := hs.inter (MeasurableSet.singleton 0).compl
  have key : ∫⁻ y, g y ∂(Measure.map (mulLeftEquiv u) (μ.restrict ((mulLeftEquiv u) ⁻¹' (s ∩ {0}ᶜ)))) =
      ∫⁻ x, g (mulLeftEquiv u x) ∂(μ.restrict ((mulLeftEquiv u) ⁻¹' (s ∩ {0}ᶜ))) :=
    lintegral_map_equiv g (mulLeftEquiv u)
  rw [← Measure.restrict_map (mulLeftEquiv u).measurable hsm, coe_mulLeftEquiv, map_mul_left_eq_smul μ u,
    Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul] at key
  exact key.symm

private theorem map_mul_left_mulMeasure (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (u : Kˣ) :
    Measure.map (fun x : K => (u : K) * x) (mulMeasure μ) = mulMeasure μ := by
  have hΔ0 : ((distribHaarChar K u : ℝ≥0∞)) ≠ 0 := ENNReal.coe_ne_zero.mpr distribHaarChar_pos.ne'
  have hΔt : ((distribHaarChar K u : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
  ext s hs
  rw [Measure.map_apply (measurable_mul_left u) hs, mulMeasure_apply μ (measurable_mul_left u hs),
    mulMeasure_apply μ hs, ← preimage_mul_left_inter_compl u s]

  have hfun : ∀ x : K, ((modulus x : ℝ≥0∞))⁻¹ =
      (distribHaarChar K u : ℝ≥0∞) * ((modulus ((u : K) * x) : ℝ≥0∞))⁻¹ := by
    intro x
    rw [modulus_mul_inv_coe, ← mul_assoc, ENNReal.mul_inv_cancel hΔ0 hΔt, one_mul]
  calc ∫⁻ x in (fun x : K => (u : K) * x) ⁻¹' (s ∩ {0}ᶜ), ((modulus x : ℝ≥0∞))⁻¹ ∂μ
      = ∫⁻ x in (fun x : K => (u : K) * x) ⁻¹' (s ∩ {0}ᶜ),
          (distribHaarChar K u : ℝ≥0∞) * ((modulus ((u : K) * x) : ℝ≥0∞))⁻¹ ∂μ :=
        lintegral_congr fun x => hfun x
    _ = (distribHaarChar K u : ℝ≥0∞) *
          ∫⁻ x in (fun x : K => (u : K) * x) ⁻¹' (s ∩ {0}ᶜ), ((modulus ((u : K) * x) : ℝ≥0∞))⁻¹ ∂μ :=
        lintegral_const_mul' _ _ hΔt
    _ = (distribHaarChar K u : ℝ≥0∞) * (((distribHaarChar K u : ℝ≥0∞))⁻¹ *
          ∫⁻ y in s ∩ {0}ᶜ, ((modulus y : ℝ≥0∞))⁻¹ ∂μ) := by
        rw [setLIntegral_preimage_mul_left μ u hs fun y => ((modulus y : ℝ≥0∞))⁻¹]
    _ = ∫⁻ y in s ∩ {0}ᶜ, ((modulus y : ℝ≥0∞))⁻¹ ∂μ := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hΔ0 hΔt, one_mul]

private theorem mulMeasure_preimage_mul_left (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (u : Kˣ) {s : Set K}
    (hs : MeasurableSet s) :
    mulMeasure μ ((fun x : K => (u : K) * x) ⁻¹' s) = mulMeasure μ s := by
  rw [← Measure.map_apply (measurable_mul_left u) hs, map_mul_left_mulMeasure μ u]

end Topology

end ModuleInvariance

section UnitSphere

open scoped Topology

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

variable (K v) in

private theorem isClosed_unitSphere : IsClosed {u : v.adicCompletion K | Valued.v u = 1} := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro x hx
  have hx' : Valued.v x ≠ 1 := hx
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : ∀ᶠ y in 𝓝 (0 : v.adicCompletion K), Valued.v y < Valued.v (1 : v.adicCompletion K) := by
      rw [Filter.Eventually, Valued.mem_nhds_zero]
      refine ⟨Units.mk0 (Valued.v.restrict (1 : v.adicCompletion K)) ((Valuation.ne_zero_iff _).mpr one_ne_zero),
        fun y hy => ?_⟩
      exact (Valuation.restrict_lt_iff _).mp hy
    filter_upwards [h0] with y hy
    intro hy1
    have hy1' : Valued.v y = 1 := hy1
    rw [map_one, hy1'] at hy
    exact lt_irrefl _ hy
  · have hxv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    filter_upwards [Valued.locally_const hxv] with y hy
    intro hy1
    have hy1' : Valued.v y = 1 := hy1
    exact hx' (by rw [← hy, hy1'])

variable (K v) in

private theorem isCompact_unitSphere : IsCompact {u : v.adicCompletion K | Valued.v u = 1} := by
  have hO : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)
  refine hO.of_isClosed_subset (isClosed_unitSphere K v) fun u hu => ?_
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact le_of_eq hu

variable (K v) in

private theorem isOpen_unitSphere : IsOpen {u : v.adicCompletion K | Valued.v u = 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx1 : Valued.v x = 1 := hx
  have hx0 : Valued.v x ≠ 0 := by
    rw [hx1]
    exact one_ne_zero
  exact Filter.mem_of_superset (Valued.locally_const hx0) fun y hy => by
    show Valued.v y = 1
    rw [← hx1]
    exact hy

end UnitSphere

section UnitSphereMeasure

open scoped ENNReal Pointwise

variable {v : HeightOneSpectrum (𝓞 ℚ)}

variable (v) in
private theorem measurableSet_unitSphere : MeasurableSet {u : v.adicCompletion ℚ | Valued.v u = 1} := by
  haveI := locBorelSpace v
  exact (isClosed_unitSphere ℚ v).measurableSet

variable (μ : Measure (v.adicCompletion ℚ))

variable [μ.IsAddHaarMeasure]

private theorem modulus_eq_one_of_valued_eq_one [μ.Regular] {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) :
    modulus u = 1 := by
  haveI := locBorelSpace v
  have hu0 : u ≠ 0 := fun h => by
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers ℚ) from inferInstance)
  have hO0 : μ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ≠ 0 :=
    (Valued.isOpen_valuationSubring _).measure_ne_zero μ ⟨0, zero_mem _⟩
  have hsmul : (Units.mk0 u hu0) • (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) =
      (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, SetLike.mem_coe, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul,
      Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hu, inv_one, one_mul]
  rw [modulus_of_ne_zero hu0]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hO0 hO.measure_lt_top.ne ?_
  rw [hsmul, ENNReal.coe_one, one_mul]

private theorem mulMeasure_eq_of_subset_unitSphere [μ.Regular] {s : Set (v.adicCompletion ℚ)} (hs : MeasurableSet s)
    (hsub : s ⊆ {u : v.adicCompletion ℚ | Valued.v u = 1}) : mulMeasure μ s = μ s := by
  haveI := locBorelSpace v
  have h0 : (0 : v.adicCompletion ℚ) ∉ s := fun h => by
    have h' : Valued.v (0 : v.adicCompletion ℚ) = 1 := hsub h
    rw [map_zero] at h'
    exact zero_ne_one h'
  have hs0 : s ∩ {0}ᶜ = s := Set.inter_eq_left.mpr fun x hx hx0 => h0 (by
    rw [Set.mem_singleton_iff] at hx0
    rw [hx0] at hx
    exact hx)
  rw [ModuleInvariance.mulMeasure_apply μ hs, hs0]
  calc ∫⁻ x in s, ((modulus x : ℝ≥0∞))⁻¹ ∂μ = ∫⁻ x in s, 1 ∂μ :=
        setLIntegral_congr_fun hs fun x hx => by
          show ((modulus x : ℝ≥0∞))⁻¹ = 1
          rw [modulus_eq_one_of_valued_eq_one μ (hsub hx), ENNReal.coe_one, inv_one]
    _ = μ s := by rw [setLIntegral_const, one_mul]

end UnitSphereMeasure

section Shells

open scoped Pointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def ordU (a : (v.adicCompletion ℚ)ˣ) : ℤ := -WithZero.log (Valued.v (a : v.adicCompletion ℚ))

private theorem valued_eq_exp_neg_ordU (a : (v.adicCompletion ℚ)ˣ) :
    Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-ordU v a) := by
  unfold ordU
  rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr a.ne_zero)]

private theorem ordU_eq_of_valued_eq {a : (v.adicCompletion ℚ)ˣ} {m : ℤ}
    (h : Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-m)) : ordU v a = m := by
  unfold ordU
  rw [h, WithZero.log_exp, neg_neg]

private theorem valued_unitPart (a : (v.adicCompletion ℚ)ˣ) :
    Valued.v ((AdelicLevel.uniformizerUnit ℚ v ^ (-ordU v a) * a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      1 := by
  rw [Units.val_mul, Valuation.map_mul, valued_uniformizerUnit_zpow, valued_eq_exp_neg_ordU, neg_neg,
    ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

private theorem zpow_ordU_mul_unitPart (a : (v.adicCompletion ℚ)ˣ) :
    AdelicLevel.uniformizerUnit ℚ v ^ ordU v a * (AdelicLevel.uniformizerUnit ℚ v ^ (-ordU v a) * a) = a := by
  rw [_root_.zpow_neg, mul_inv_cancel_left]

private theorem setOf_valued_eq_exp (m : ℤ) :
    {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp (-m)} =
      (fun x : v.adicCompletion ℚ =>
          ((AdelicLevel.uniformizerUnit ℚ v ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) ⁻¹'
        {u : v.adicCompletion ℚ | Valued.v u = 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.map_mul, valued_uniformizerUnit_zpow, neg_neg]
  constructor
  · intro hx
    rw [hx, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · intro hx
    have h1 : WithZero.exp m * Valued.v x = WithZero.exp m * WithZero.exp (-m) := by
      rw [hx, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    exact mul_left_cancel₀ WithZero.exp_ne_zero h1

private theorem measurableSet_setOf_valued_eq_exp (m : ℤ) :
    MeasurableSet {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp (-m)} := by
  haveI := locBorelSpace v
  rw [setOf_valued_eq_exp]
  exact (continuous_const.mul continuous_id).measurable (measurableSet_unitSphere v)

private theorem mulMeasure_setOf_valued_eq_exp (m : ℤ) :
    mulMeasure (selfDualHaarAt ℚ v) {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp (-m)} =
      selfDualHaarAt ℚ v {u : v.adicCompletion ℚ | Valued.v u = 1} := by
  haveI := locBorelSpace v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := regular_selfDualHaarAt v
  rw [setOf_valued_eq_exp, ModuleInvariance.mulMeasure_preimage_mul_left _ _ (measurableSet_unitSphere v),
    mulMeasure_eq_of_subset_unitSphere (selfDualHaarAt ℚ v) (measurableSet_unitSphere v) subset_rfl]

private theorem range_units_val :
    Set.range (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

private theorem measurableSet_image_units_val {A : Set (v.adicCompletion ℚ)ˣ} (hA : MeasurableSet A) :
    MeasurableSet (Units.val '' A) := by
  haveI := locBorelSpace v
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  rw [Set.image_preimage_eq_inter_range, range_units_val]
  exact hB.inter (measurableSet_singleton 0).compl

private theorem shell_eq_preimage (m : ℤ) :
    ordU v ⁻¹' {m} = Units.val ⁻¹' {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp (-m)} := by
  ext a
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro rfl
    exact valued_eq_exp_neg_ordU v a
  · exact ordU_eq_of_valued_eq v

private theorem measurableSet_shell (m : ℤ) : MeasurableSet (ordU v ⁻¹' {m}) := by
  rw [shell_eq_preimage]
  exact MeasurableSpace.measurableSet_comap.mpr ⟨_, measurableSet_setOf_valued_eq_exp v m, rfl⟩

private theorem measurable_ordU : Measurable (ordU v) :=
  measurable_to_countable' fun m => measurableSet_shell v m

private theorem image_val_shell (m : ℤ) :
    Units.val '' (ordU v ⁻¹' {m}) = {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp (-m)} := by
  rw [shell_eq_preimage, Set.image_preimage_eq_inter_range, range_units_val]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, and_iff_left_iff_imp]
  intro hx hx0
  rw [hx0, map_zero] at hx
  exact WithZero.exp_ne_zero hx.symm

private theorem map_ordU_singleton (m : ℤ) :
    Measure.map (ordU v) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {m} =
      selfDualHaarAt ℚ v {u : v.adicCompletion ℚ | Valued.v u = 1} := by
  rw [Measure.map_apply (measurable_ordU v) (measurableSet_singleton m),
    Measure.comap_apply Units.val Units.val_injective (fun _ hA => measurableSet_image_units_val v hA) _
      (measurableSet_shell v m),
    image_val_shell, mulMeasure_setOf_valued_eq_exp]

private theorem map_ordU_real_singleton (m : ℤ) :
    (Measure.map (ordU v) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))).real {m} =
      (selfDualHaarAt ℚ v).real {u : v.adicCompletion ℚ | Valued.v u = 1} := by
  rw [measureReal_def, map_ordU_singleton, measureReal_def]

private theorem selfDualHaarAt_real_unitSphere_pos :
    0 < (selfDualHaarAt ℚ v).real {u : v.adicCompletion ℚ | Valued.v u = 1} := by
  haveI := locBorelSpace v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  rw [measureReal_def]
  refine ENNReal.toReal_pos ?_ (isCompact_unitSphere ℚ v).measure_lt_top.ne
  exact (isOpen_unitSphere ℚ v).measure_ne_zero _ ⟨1, by simp⟩

private theorem selfDualHaarAt_unitSphere_lt_top :
    selfDualHaarAt ℚ v {u : v.adicCompletion ℚ | Valued.v u = 1} < ⊤ := by
  haveI := locBorelSpace v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  exact (isCompact_unitSphere ℚ v).measure_lt_top

end Shells

section Local

open NumberField.TateGlobal

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
  (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)

private theorem nloc_hfam_of_not_mem
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hvS : v ∉ S) (hvL : v ∉ L) :
    nloc v (hfam Wloc g a v) = tIdent Wloc v := by
  have hε := valued_evalUnits_eq_one_of_mem_unitIdelesOutside v _ ha (by simp [hvS, hvL])
  have key : (∫ t, Wloc v (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) * lowerUnipotent21 t *
        componentAt3 (𝓞 ℚ) ℚ v g) ∂(selfDualHaarAt ℚ v)) =
      ∫ t, Wloc v (lowerUnipotent21 t) ∂(selfDualHaarAt ℚ v) := by
    rw [componentAt3_iotaGL_diagUnitGL2, ← one_mul (evalUnits v a),
      integral_mul_unit_eq v (Wloc v) (hK v hvS) 1 hε (hg v hvS)]
    simp only [iotaGL_diagUnitGL2_one, one_mul]
  simp only [tIdent, nloc, hfam]
  rw [key]

private theorem nloc_hfam_of_mem
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ))
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ L) :
    nloc v (hfam Wloc g a v) = nloc v (zsh Wloc v (Hν.ord v a)) := by
  have hvS : v ∉ S := hLS v hv
  obtain ⟨u, -, -, huU, hau⟩ := Hν.decomp L hLS hL a ha
  have hcomp : evalUnits v a = AdelicLevel.uniformizerUnit ℚ v ^ Hν.ord v a * evalUnits v u := by
    conv_lhs => rw [hau]
    rw [map_mul, map_mul, evalUnits_eq_one_of_coe_eq_one (Hν.projS_off a v hvS), one_mul,
      evalUnits_uniformizer_prod_of_mem L hL (fun w => Hν.ord w a) hv]
  have hε := valued_evalUnits_eq_one_of_mem_unitIdeles v huU
  have key : (∫ t, Wloc v (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) * lowerUnipotent21 t *
        componentAt3 (𝓞 ℚ) ℚ v g) ∂(selfDualHaarAt ℚ v)) =
      ∫ t, Wloc v (iotaGL (diagUnitGL2 (AdelicLevel.uniformizerUnit ℚ v ^ Hν.ord v a)) * lowerUnipotent21 t)
        ∂(selfDualHaarAt ℚ v) := by
    rw [componentAt3_iotaGL_diagUnitGL2, hcomp, integral_mul_unit_eq v (Wloc v) (hK v hvS) _ hε (hg v hvS)]
  simp only [nloc, hfam, zsh]
  rw [key]

private theorem hfam_projS (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ))
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L})) :
    (∀ v ∈ S, hfam Wloc g (Hν.projS a) v = hfam Wloc g a v) ∧ farch Warch g (Hν.projS a) = farch Warch g a := by
  obtain ⟨u, hu1, huS, -, hau⟩ := Hν.decomp L hLS hL a ha
  refine ⟨fun v hvS => ?_, ?_⟩
  · have hev : evalUnits v (Hν.projS a) = evalUnits v a := by
      conv_rhs => rw [hau]
      rw [map_mul, map_mul, evalUnits_uniformizer_prod_of_not_mem L (fun w => Hν.ord w a) (fun hvL => hLS v hvL hvS),
        evalUnits_eq_one_of_coe_eq_one (huS v hvS), mul_one, mul_one]
    funext t
    simp only [hfam, componentAt3_iotaGL_diagUnitGL2, hev]
  · have harch : archUnits (Hν.projS a) = archUnits a := by
      conv_rhs => rw [hau]
      rw [map_mul, map_mul, archUnits_uniformizer_prod, archUnits_eq_one_of_coe_eq_one hu1, mul_one, mul_one]
    funext y
    simp only [farch, archComponent3_iotaGL_diagUnitGL2, harch]

private theorem localChar_eq_one_of_valued_eq_one
    (hχU : ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 → (∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) →
      NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ →
      χ u = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ S) (ε : (v.adicCompletion ℚ)ˣ)
    (hε : Valued.v (ε : v.adicCompletion ℚ) = 1) :
    localChar χ v ε = 1 := by
  refine hχU (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ)
    (AdelicLevel.localUnit (𝓞 ℚ) ℚ v ε)) ?_ ?_ ?_
  · exact AdelicLevel.finIncl_apply_fst (𝓞 ℚ) ℚ _
  · intro w hw
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    exact (AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ v ε hwv)
  · have hfp : NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ
        (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ)
          (AdelicLevel.localUnit (𝓞 ℚ) ℚ v ε)) = AdelicLevel.localUnit (𝓞 ℚ) ℚ v ε :=
      Units.ext rfl
    rw [hfp, ← IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_empty,
      IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
    intro w _
    rw [← map_inv]
    by_cases hwv : w = v
    · have hinv := valued_inv_le_one_of_eq_one v hε
      rw [hwv, AdelicLevel.localUnit_apply_self, AdelicLevel.localUnit_apply_self]
      exact ⟨by simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hε.le,
        by simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hinv⟩
    · rw [AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ v ε hwv, AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ hwv]
      exact ⟨(w.adicCompletionIntegers ℚ).one_mem, (w.adicCompletionIntegers ℚ).one_mem⟩

private theorem localChar_uniformizerUnit (v : HeightOneSpectrum (𝓞 ℚ)) :
    localChar χ v (AdelicLevel.uniformizerUnit ℚ v) = χ (uniformizerIdele ℚ v) := by
  rfl

private theorem localZeta31_eq_tsum_phiSh
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hχU : ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 → (∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) →
      NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ →
      χ u = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ S) (s : ℂ) :
    (letI := localBorel ℚ v
     ((selfDualHaarAt ℚ v).real {u : v.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
       ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
         localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (Wloc v)
           (localChar χ v) s 1)
      = ∑' m : ℤ, phiSh Wloc χ s v m := by
  haveI := locBorelSpace v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  have hS0 : (((selfDualHaarAt ℚ v).real {u : v.adicCompletion ℚ | Valued.v u = 1} : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (selfDualHaarAt_real_unitSphere_pos v).ne'
  have hO0 : (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (selfDualHaarAt_real_integers_pos v).ne'

  have hG : (fun a : (v.adicCompletion ℚ)ˣ =>
      (∫ x : v.adicCompletion ℚ, Wloc v (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * 1) ∂(selfDualHaarAt ℚ v)) *
        ((localChar χ v a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      fun a => (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) *
        phiSh Wloc χ s v (ordU v a) := by
    funext a
    have hε := valued_unitPart v a
    have hdec := zpow_ordU_mul_unitPart v a
    have hinner : (∫ x : v.adicCompletion ℚ, Wloc v (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * 1)
          ∂(selfDualHaarAt ℚ v)) =
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) *
          nloc v (zsh Wloc v (ordU v a)) := by
      conv_lhs => rw [← hdec]
      rw [integral_mul_unit_eq v (Wloc v) (hK v hv) _ hε (localMaximalCompact3 (𝓞 ℚ) ℚ v).one_mem]
      simp only [nloc, zsh]
      rw [← mul_assoc, mul_inv_cancel₀ hO0, one_mul]
    have hchar : ((localChar χ v a : ℂˣ) : ℂ) = ((χ (uniformizerIdele ℚ v) ^ ordU v a : ℂˣ) : ℂ) := by
      conv_lhs => rw [← hdec]
      rw [map_mul, map_zpow, localChar_uniformizerUnit χ v, localChar_eq_one_of_valued_eq_one S χ hχU v hv _ hε,
        mul_one]
    have hmod : ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) =
        ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ ordU v a : ℝ) : ℂ) := by
      rw [modulus_adicCompletion_eq_nnnorm, coe_nnnorm, ofReal_norm_eq_of_valued_eq v (valued_eq_exp_neg_ordU v a),
        natCard_quot_eq_absNorm]
      push_cast
      rw [_root_.inv_zpow]
    rw [hinner, hchar, hmod, phiSh]
    ring
  have hmap : (∫ m : ℤ, (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) *
        phiSh Wloc χ s v m ∂(Measure.map (ordU v) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))) =
      ∫ a, (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) *
        phiSh Wloc χ s v (ordU v a) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) :=
    integral_map (measurable_ordU v).aemeasurable (measurable_of_countable _).aestronglyMeasurable
  show (((selfDualHaarAt ℚ v).real {u : v.adicCompletion ℚ | Valued.v u = 1} : ℝ) : ℂ)⁻¹ *
      (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ)⁻¹ *
        localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (Wloc v)
          (localChar χ v) s 1 = ∑' m : ℤ, phiSh Wloc χ s v m
  have hz : localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) (Wloc v)
        (localChar χ v) s 1 =
      ∫ a, (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) *
        phiSh Wloc χ s v (ordU v a) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    unfold localZeta31
    exact congrArg (MeasureTheory.integral (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) hG
  rw [hz, ← hmap]
  by_cases hI : Integrable
      (fun m : ℤ => (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) *
        phiSh Wloc χ s v m)
      (Measure.map (ordU v) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
  · rw [integral_countable hI]
    simp only [map_ordU_real_singleton v, Complex.real_smul]
    rw [tsum_mul_left, tsum_mul_left]
    field_simp
  · rw [integral_undef hI, mul_zero]
    refine (tsum_eq_zero_of_not_summable fun hsum => hI ?_).symm
    have hnorm : Summable fun m : ℤ =>
        ‖(((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ) *
          phiSh Wloc χ s v m‖₊ := by
      have h := summable_norm_iff.mpr (hsum.mul_left
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℝ) : ℂ))
      exact NNReal.summable_coe.mp (by simpa only [coe_nnnorm] using h)
    refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_countable']
    simp only [map_ordU_singleton v, enorm_eq_nnnorm]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_lt_top (ENNReal.tsum_coe_ne_top_iff_summable.mpr hnorm).lt_top
      (selfDualHaarAt_unitSphere_lt_top v)

end Local

section ProductMeasure

variable {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
  (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ))

private theorem list_prod_pos : ∀ l : List ℝ, (∀ x ∈ l, 0 < x) → 0 < l.prod
  | [], _ => by simp
  | x :: l, h => by
    rw [List.prod_cons]
    exact mul_pos (h x (by simp)) (list_prod_pos l fun y hy => h y (by simp [hy]))

private theorem list_prod_nonneg : ∀ l : List ℝ, (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.prod
  | [], _ => by simp
  | x :: l, h => by
    rw [List.prod_cons]
    exact mul_nonneg (h x (by simp)) (list_prod_nonneg l fun y hy => h y (by simp [hy]))

private theorem norm_list_prod_map_le (p q : HeightOneSpectrum (𝓞 ℚ) → ℂ) :
    ∀ l : List (HeightOneSpectrum (𝓞 ℚ)), (∀ v ∈ l, ‖p v‖ ≤ ‖q v‖) → ‖(l.map p).prod‖ ≤ ‖(l.map q).prod‖
  | [], _ => by simp
  | v :: l, h => by
    simp only [List.map_cons, List.prod_cons, norm_mul]
    exact mul_le_mul (h v (by simp)) (norm_list_prod_map_le p q l fun w hw => h w (by simp [hw])) (norm_nonneg _)
      (norm_nonneg _)

private theorem ofReal_list_prod_map (r : HeightOneSpectrum (𝓞 ℚ) → ℝ) :
    ∀ l : List (HeightOneSpectrum (𝓞 ℚ)), (l.map fun v => ((r v : ℝ) : ℂ)).prod = (((l.map r).prod : ℝ) : ℂ)
  | [] => by simp
  | v :: l => by
    simp only [List.map_cons, List.prod_cons, ofReal_list_prod_map r l, Complex.ofReal_mul]

private theorem summable_of_integrableOn (f : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (hf : Integrable f Hν.νS)
    (hf0 : ∫ a, ‖f a‖ ∂Hν.νS ≠ 0) (φ : HeightOneSpectrum (𝓞 ℚ) → ℤ → ℂ)
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup) (hφ : ∀ v ∈ L, ∃ m, φ v m ≠ 0)
    (hint : IntegrableOn (fun a => f (Hν.projS a) * (L.map fun v => φ v (Hν.ord v a)).prod)
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)
      (NumberField.Idele.idelicHaar ℚ)) :
    ∀ v ∈ L, Summable fun m : ℤ => ‖φ v m‖ := by
  classical
  intro v₀ hv₀
  have hφ' : ∀ v, ∃ m : ℤ, v ∈ L → φ v m ≠ 0 := fun v => by
    by_cases hv : v ∈ L
    · obtain ⟨m, hm⟩ := hφ v hv
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => (hv h).elim⟩
  choose mv hmv using hφ'

  let r : Finset ℤ → HeightOneSpectrum (𝓞 ℚ) → ℝ := fun M v =>
    if v = v₀ then ∑ m ∈ M, ‖φ v₀ m‖ else ‖φ v (mv v)‖
  let ψ : Finset ℤ → HeightOneSpectrum (𝓞 ℚ) → ℤ → ℂ := fun M v m =>
    if v = v₀ then (if m ∈ M then ((‖φ v₀ m‖ : ℝ) : ℂ) else 0) else (if m = mv v then ((‖φ v m‖ : ℝ) : ℂ) else 0)
  have hψsum : ∀ M : Finset ℤ, ∀ v ∈ L, Summable fun m : ℤ => ‖ψ M v m‖ := by
    intro M v _
    by_cases hv : v = v₀
    · exact summable_of_ne_finset_zero (s := M) fun m hm => by simp [ψ, hv, hm]
    · exact summable_of_ne_finset_zero (s := {mv v}) fun m hm => by
        simp only [Finset.mem_singleton] at hm
        simp [ψ, hv, hm]
  have hψtsum : ∀ M : Finset ℤ, ∀ v, (∑' m : ℤ, ψ M v m) = ((r M v : ℝ) : ℂ) := by
    intro M v
    by_cases hv : v = v₀
    · subst hv
      rw [tsum_eq_sum (s := M) fun m hm => by simp [ψ, hm]]
      simp only [r, if_true, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun m hm => by simp [ψ, hm]
    · rw [tsum_eq_single (mv v) fun m hm => by simp [ψ, hv, hm]]
      simp [ψ, r, hv]
  have hψle : ∀ M : Finset ℤ, ∀ v m, ‖ψ M v m‖ ≤ ‖φ v m‖ := by
    intro M v m
    by_cases hv : v = v₀
    · subst hv
      by_cases hm : m ∈ M <;> simp [ψ, hm]
    · by_cases hm : m = mv v
      · subst hm
        simp [ψ, hv]
      · simp [ψ, hv, hm]
  have hrnn : ∀ M : Finset ℤ, ∀ v, 0 ≤ r M v := fun M v => by
    by_cases hv : v = v₀
    · simp only [r, hv, if_true]
      exact Finset.sum_nonneg fun m _ => norm_nonneg _
    · simp only [r, hv, if_false]
      exact norm_nonneg _
  have hfn : Integrable (fun a => ((‖f a‖ : ℝ) : ℂ)) Hν.νS := hf.norm.ofReal
  have hI : 0 < ∫ a, ‖f a‖ ∂Hν.νS := lt_of_le_of_ne (integral_nonneg fun a => norm_nonneg _) (Ne.symm hf0)

  have hbound : ∀ M : Finset ℤ, Hν.c * (∫ a, ‖f a‖ ∂Hν.νS) * (L.map (r M)).prod ≤
      ∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ),
        ‖f (Hν.projS a) * (L.map fun v => φ v (Hν.ord v a)).prod‖ ∂(NumberField.Idele.idelicHaar ℚ) := by
    intro M
    obtain ⟨-, hEq⟩ := Hν.tonelli L hLS hL (fun a => ((‖f a‖ : ℝ) : ℂ)) (ψ M) hfn (hψsum M)
    have hnorm : ‖∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), ((‖f (Hν.projS a)‖ : ℝ) : ℂ) * (L.map fun v => ψ M v (Hν.ord v a)).prod
          ∂(NumberField.Idele.idelicHaar ℚ)‖ ≤
        ∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ),
          ‖f (Hν.projS a) * (L.map fun v => φ v (Hν.ord v a)).prod‖ ∂(NumberField.Idele.idelicHaar ℚ) := by
      refine norm_integral_le_of_norm_le hint.norm (Filter.Eventually.of_forall fun a => ?_)
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (norm_list_prod_map_le (fun v => ψ M v (Hν.ord v a)) (fun v => φ v (Hν.ord v a)) L fun v _ => hψle M v _)
        (norm_nonneg _)
    rw [hEq, integral_complex_ofReal] at hnorm
    simp only [hψtsum, ofReal_list_prod_map] at hnorm
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.norm_of_nonneg (mul_nonneg (mul_nonneg Hν.c_pos.le hI.le) (list_prod_nonneg _ fun x hx => by
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
        exact hrnn M v))] at hnorm
    exact hnorm

  set R₀ : ℝ := ((L.erase v₀).map fun v => ‖φ v (mv v)‖).prod with hR₀
  have hsplit : ∀ M : Finset ℤ, (L.map (r M)).prod = (∑ m ∈ M, ‖φ v₀ m‖) * R₀ := by
    intro M
    rw [← List.prod_map_erase (r M) hv₀, hR₀]
    congr 1
    · simp [r]
    · refine congrArg List.prod (List.map_congr_left fun v hv => ?_)
      have hne : v ≠ v₀ := (hL.mem_erase_iff.mp hv).1
      simp [r, hne]
  have hR₀pos : 0 < R₀ := list_prod_pos _ fun x hx => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    exact norm_pos_iff.mpr (hmv v (hL.mem_erase_iff.mp hv).2)
  have hKpos : 0 < Hν.c * (∫ a, ‖f a‖ ∂Hν.νS) * R₀ := mul_pos (mul_pos Hν.c_pos hI) hR₀pos
  refine summable_of_sum_le (fun m => norm_nonneg _) (c := (∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ
    (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), ‖f (Hν.projS a) * (L.map fun v => φ v (Hν.ord v a)).prod‖
      ∂(NumberField.Idele.idelicHaar ℚ)) / (Hν.c * (∫ a, ‖f a‖ ∂Hν.νS) * R₀)) fun M => ?_
  rw [le_div_iff₀ hKpos]
  have h := hbound M
  rw [hsplit M] at h
  calc (∑ m ∈ M, ‖φ v₀ m‖) * (Hν.c * (∫ a, ‖f a‖ ∂Hν.νS) * R₀)
      = Hν.c * (∫ a, ‖f a‖ ∂Hν.νS) * ((∑ m ∈ M, ‖φ v₀ m‖) * R₀) := by ring
    _ ≤ _ := h

private theorem ae_eq_zero_of_integral_norm_eq_zero (f : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (hf : Integrable f Hν.νS)
    (hf0 : ∫ a, ‖f a‖ ∂Hν.νS = 0) (L : List (HeightOneSpectrum (𝓞 ℚ))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup) :
    ∀ᵐ a ∂((NumberField.Idele.idelicHaar ℚ).restrict
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)),
      f (Hν.projS a) = 0 := by
  classical

  let w : ℤ → ℝ := fun m => (1 / 2 : ℝ) ^ m.natAbs
  have hwpos : ∀ m, 0 < w m := fun m => pow_pos (by norm_num) _
  have hwsum : Summable w := by
    refine Summable.of_nat_of_neg ?_ ?_ <;> simpa [w] using summable_geometric_two
  let ψ : HeightOneSpectrum (𝓞 ℚ) → ℤ → ℂ := fun _ m => ((w m : ℝ) : ℂ)
  have hψsum : ∀ v ∈ L, Summable fun m : ℤ => ‖ψ v m‖ := fun v _ => by
    refine hwsum.congr fun m => ?_
    simp only [ψ]
    exact (Complex.norm_of_nonneg (hwpos m).le).symm
  have hfn : Integrable (fun a => ((‖f a‖ : ℝ) : ℂ)) Hν.νS := hf.norm.ofReal
  obtain ⟨hI, hEq⟩ := Hν.tonelli L hLS hL (fun a => ((‖f a‖ : ℝ) : ℂ)) ψ hfn hψsum
  rw [integral_complex_ofReal, hf0, Complex.ofReal_zero, mul_zero, zero_mul] at hEq
  obtain ⟨G, hG⟩ : ∃ G : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ,
      G = fun a => ‖f (Hν.projS a)‖ * (L.map fun v => w (Hν.ord v a)).prod := ⟨_, rfl⟩
  have hGpos : ∀ a, 0 < (L.map fun v => w (Hν.ord v a)).prod := fun a => list_prod_pos _ fun x hx => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    exact hwpos _
  have hcast : ∀ a, ((‖f (Hν.projS a)‖ : ℝ) : ℂ) * (L.map fun v => ψ v (Hν.ord v a)).prod = ((G a : ℝ) : ℂ) := by
    intro a
    simp only [ψ, hG]
    rw [ofReal_list_prod_map, Complex.ofReal_mul]
  simp only [hcast] at hI hEq
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hEq
  have hGint : Integrable G ((NumberField.Idele.idelicHaar ℚ).restrict
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)) :=
    by simpa using hI.re
  have hGnn : 0 ≤ G := fun a => by
    rw [hG]
    exact mul_nonneg (norm_nonneg _) (hGpos a).le
  have hG0 := (integral_eq_zero_iff_of_nonneg hGnn hGint).1 hEq
  filter_upwards [hG0] with a ha
  rw [hG] at ha
  simp only [Pi.zero_apply] at ha
  rcases mul_eq_zero.mp ha with h | h
  · exact norm_eq_zero.mp h
  · exact absurd h (hGpos a).ne'

end ProductMeasure

section Factorised

open NumberField.TateGlobal Filter Topology

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
  (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
  (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)

private def tailProd (t : Finset (HeightOneSpectrum (𝓞 ℚ))) : ℂ :=
  ∏' x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t}, tIdent Wloc x.1

private theorem summable_tIdent_sub_one
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hW1 : ∀ v, v ∉ S → Wloc v 1 = 1)
    (hint : ∀ v, v ∉ S → Integrable (fun y => Wloc v (lowerUnipotent21 y)) (selfDualHaarAt ℚ v))
    (hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
          * (∫ y, ‖Wloc v.1 (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => tIdent Wloc v.1 - 1 := by
  refine Summable.of_norm_bounded hsum fun v => ?_
  have hvS := v.2
  have hint_v := hint v.1 hvS
  have hO : (0 : ℝ) < (selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) :=
    selfDualHaarAt_real_integers_pos v.1

  have hone : ∀ y ∈ (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)), Wloc v.1 (lowerUnipotent21 y) = 1 :=
    fun y hy => by
      have h := hK v.1 hvS _ (lowerUnipotent21_mem v.1 hy) 1
      rw [one_mul] at h
      rw [h, hW1 v.1 hvS]
  set O : Set (v.1.adicCompletion ℚ) := (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) with hOdef
  haveI := locBorelSpace v.1
  have hOmeas : MeasurableSet O := (AdelicLevel.isClosed_adicCompletionIntegers v.1).measurableSet
  haveI := isAddHaarMeasure_selfDualHaarAt v.1
  have hOfin : selfDualHaarAt ℚ v.1 O ≠ ⊤ :=
    (isCompact_iff_compactSpace.mpr (show CompactSpace (v.1.adicCompletionIntegers ℚ) from inferInstance) :
      IsCompact O).measure_lt_top.ne
  have hind : Integrable (O.indicator fun _ : v.1.adicCompletion ℚ => (1 : ℂ)) (selfDualHaarAt ℚ v.1) :=
    (integrableOn_const hOfin : IntegrableOn (fun _ => (1 : ℂ)) O (selfDualHaarAt ℚ v.1)).integrable_indicator hOmeas
  have hOint : (∫ y, O.indicator (fun _ => (1 : ℂ)) y ∂(selfDualHaarAt ℚ v.1)) =
      ((selfDualHaarAt ℚ v.1).real O : ℂ) := by
    rw [integral_indicator hOmeas, setIntegral_const, Complex.real_smul, mul_one]
  have hdiff : tIdent Wloc v.1 - 1 = (((selfDualHaarAt ℚ v.1).real O : ℝ) : ℂ)⁻¹ *
      ∫ y, (Wloc v.1 (lowerUnipotent21 y) - O.indicator (fun _ => (1 : ℂ)) y) ∂(selfDualHaarAt ℚ v.1) := by
    rw [integral_sub hint_v hind, hOint, mul_sub, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hO.ne')]
    rfl
  have hptwise : ∀ y, ‖Wloc v.1 (lowerUnipotent21 y) - O.indicator (fun _ => (1 : ℂ)) y‖ =
      ‖Wloc v.1 (lowerUnipotent21 y)‖ - O.indicator (fun _ => (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ O
    · simp [hy, hone y hy]
    · simp [hy]
  have hnormint : (∫ y, ‖Wloc v.1 (lowerUnipotent21 y) - O.indicator (fun _ => (1 : ℂ)) y‖ ∂(selfDualHaarAt ℚ v.1)) =
      (∫ y, ‖Wloc v.1 (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - (selfDualHaarAt ℚ v.1).real O := by
    simp only [hptwise]
    rw [integral_sub hint_v.norm ((integrableOn_const hOfin : IntegrableOn (fun _ => (1 : ℝ)) O
      (selfDualHaarAt ℚ v.1)).integrable_indicator hOmeas), integral_indicator hOmeas,
      setIntegral_const, smul_eq_mul, mul_one]
  rw [hdiff, norm_mul, norm_inv, Complex.norm_of_nonneg hO.le]
  calc ((selfDualHaarAt ℚ v.1).real O)⁻¹ *
        ‖∫ y, (Wloc v.1 (lowerUnipotent21 y) - O.indicator (fun _ => (1 : ℂ)) y) ∂(selfDualHaarAt ℚ v.1)‖
      ≤ ((selfDualHaarAt ℚ v.1).real O)⁻¹ *
        ∫ y, ‖Wloc v.1 (lowerUnipotent21 y) - O.indicator (fun _ => (1 : ℂ)) y‖ ∂(selfDualHaarAt ℚ v.1) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hO.le)
    _ = ((selfDualHaarAt ℚ v.1).real O)⁻¹ * (∫ y, ‖Wloc v.1 (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1 := by
        rw [hnormint, mul_sub, inv_mul_cancel₀ hO.ne']

private theorem tail_injective (t : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSt : S ⊆ t) :
    Function.Injective fun x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t} =>
      (⟨x.1, fun h => x.2 (hSt h)⟩ : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}) := by
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact Subtype.ext h

private theorem multipliable_tail (t : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSt : S ⊆ t)
    (hsumm : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => tIdent Wloc v.1 - 1) :
    Multipliable fun x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t} => tIdent Wloc x.1 := by
  have hfun : (fun x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t} => tIdent Wloc x.1) =
      fun x => 1 + (tIdent Wloc x.1 - 1) := by
    funext x; ring
  rw [hfun]
  have h := hsumm.comp_injective (tail_injective S t hSt)
  have h' : Summable fun x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t} => tIdent Wloc x.1 - 1 := h.congr fun x => rfl
  exact Complex.multipliable_one_add_of_summable h'

private def logIdent (v : HeightOneSpectrum (𝓞 ℚ)) : ℂ :=
  ((↑S : Set (HeightOneSpectrum (𝓞 ℚ)))ᶜ).indicator (fun w => Complex.log (tIdent Wloc w)) v

private theorem tailProd_eq_exp (t : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSt : S ⊆ t)
    (hsumm : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => tIdent Wloc v.1 - 1)
    (hne : ∀ x, x ∉ t → tIdent Wloc x ≠ 0) :
    tailProd Wloc t = Complex.exp (∑' x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t}, logIdent S Wloc x.1) := by
  have hlog : Summable fun x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t} => Complex.log (tIdent Wloc x.1) := by
    have h := Complex.summable_log_one_add_of_summable (hsumm.comp_injective (tail_injective S t hSt))
    refine h.congr fun x => ?_
    simp only [Function.comp, add_sub_cancel]
  rw [tailProd, ← Complex.cexp_tsum_eq_tprod (fun x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t} => hne x.1 x.2) hlog]
  congr 1
  refine tsum_congr fun x => ?_
  have hx : x.1 ∈ (↑S : Set (HeightOneSpectrum (𝓞 ℚ)))ᶜ := fun h => x.2 (hSt h)
  simp only [logIdent, Set.indicator_of_mem hx]

private theorem tailProd_ne_zero (t : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSt : S ⊆ t)
    (hsumm : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => tIdent Wloc v.1 - 1)
    (hne : ∀ x, x ∉ t → tIdent Wloc x ≠ 0) : tailProd Wloc t ≠ 0 := by
  rw [tailProd_eq_exp S Wloc t hSt hsumm hne]
  exact Complex.exp_ne_zero _

private theorem tendsto_tailProd (t : ℕ → Finset (HeightOneSpectrum (𝓞 ℚ))) (hmono : Monotone t)
    (hcov : ∀ v, ∃ n, v ∈ t n) (hSt : ∀ n, S ⊆ t n)
    (hsumm : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => tIdent Wloc v.1 - 1)
    (hne : ∀ n, 1 ≤ n → ∀ x, x ∉ t n → tIdent Wloc x ≠ 0) :
    Tendsto (fun n => tailProd Wloc (t n)) atTop (𝓝 1) := by
  have htails : Tendsto (fun n => ∑' x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t n}, logIdent S Wloc x.1) atTop
      (𝓝 0) :=
    (tendsto_tsum_compl_atTop_zero (logIdent S Wloc)).comp (tendsto_atTop_finset_of_monotone hmono hcov)
  have hexp : Tendsto (fun n => Complex.exp (∑' x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t n}, logIdent S Wloc x.1))
      atTop (𝓝 1) := by
    have h := (Complex.continuous_exp.tendsto 0).comp htails
    rwa [Complex.exp_zero] at h
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (tailProd_eq_exp S Wloc (t n) (hSt n) hsumm (hne n hn)).symm

private theorem tprod_eq_prod_mul (f : HeightOneSpectrum (𝓞 ℚ) → ℂ) (t : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hf : Multipliable fun x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t} => f x.1) :
    ∏' v, f v = (∏ v ∈ t, f v) * ∏' x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ t}, f x.1 := by
  have hfin : HasProd (f ∘ (↑) : (↑t : Set (HeightOneSpectrum (𝓞 ℚ))) → ℂ) (∏ v ∈ t, f v) := by
    convert hasProd_fintype (f ∘ ((↑) : (↑t : Set (HeightOneSpectrum (𝓞 ℚ))) → HeightOneSpectrum (𝓞 ℚ))) using 1
    all_goals try rfl
    exact (Finset.prod_attach t f).symm
  exact (hfin.mul_compl hf.hasProd).tprod_eq

private def tset (L : List (HeightOneSpectrum (𝓞 ℚ))) : Finset (HeightOneSpectrum (𝓞 ℚ)) := S ∪ L.toFinset

private theorem mem_tset (L : List (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ tset S L ↔ v ∈ S ∨ v ∈ L := by
  simp [tset]

private theorem zetaFn_eq
    (hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W x = Warch (archComponent3 (𝓞 ℚ) ℚ x) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v x))
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hW1 : ∀ v, v ∉ S → Wloc v 1 = 1)
    (hint : ∀ v, v ∉ S → Integrable (fun y => Wloc v (lowerUnipotent21 y)) (selfDualHaarAt ℚ v))
    (hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
          * (∫ y, ‖Wloc v.1 (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1)
    (hχU : ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 → (∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) →
      NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ →
      χ u = 1)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ)) (s : ℂ)
    (L : List (HeightOneSpectrum (𝓞 ℚ))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ L})) :
    zetaFn W χ g s a =
      boxConst * tailProd Wloc (tset S L) * sPart S Warch Wloc χ g s (Hν.projS a) *
        (L.map fun v => phiSh Wloc χ s v (Hν.ord v a)).prod := by
  have hsumm := summable_tIdent_sub_one S Wloc hK hW1 hint hsum
  obtain ⟨u, hu1, huS, huU, hau⟩ := Hν.decomp L hLS hL a ha

  have hinner := innerInt_eq S W Warch Wloc g hfac hK hW1 hsum hg L a ha
  have hmult : Multipliable fun x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ tset S L} => nloc x.1 (hfam Wloc g a x.1) := by
    refine (multipliable_tail S Wloc (tset S L) Finset.subset_union_left hsumm).congr fun x => ?_
    have hx := not_or.mp ((mem_tset S L x.1).not.mp x.2)
    exact (nloc_hfam_of_not_mem S Wloc g hK hg L a ha x.1 hx.1 hx.2).symm
  have hsplit := tprod_eq_prod_mul (fun v => nloc v (hfam Wloc g a v)) (tset S L) hmult
  beta_reduce at hsplit
  have htail : (∏' x : {x : HeightOneSpectrum (𝓞 ℚ) // x ∉ tset S L}, nloc x.1 (hfam Wloc g a x.1)) =
      tailProd Wloc (tset S L) := by
    unfold tailProd
    refine tprod_congr fun x => ?_
    have hx := not_or.mp ((mem_tset S L x.1).not.mp x.2)
    exact nloc_hfam_of_not_mem S Wloc g hK hg L a ha x.1 hx.1 hx.2
  have hdisj : Disjoint S L.toFinset := by
    rw [Finset.disjoint_left]
    intro v hvS hvL
    exact hLS v (List.mem_toFinset.mp hvL) hvS
  have hfinite : (∏ v ∈ tset S L, nloc v (hfam Wloc g a v)) =
      (∏ v ∈ S, nloc v (hfam Wloc g a v)) * (L.map fun v => nloc v (zsh Wloc v (Hν.ord v a))).prod := by
    unfold tset
    rw [Finset.prod_union hdisj, List.prod_toFinset _ hL]
    congr 1
    exact congrArg List.prod (List.map_congr_left fun v hv => nloc_hfam_of_mem S Wloc g hK hg Hν L hLS hL a ha v hv)
  obtain ⟨hS_eq, harch_eq⟩ := hfam_projS S Wloc g Warch Hν L hLS hL a ha
  have hSprod : (∏ v ∈ S, nloc v (hfam Wloc g (Hν.projS a) v)) = ∏ v ∈ S, nloc v (hfam Wloc g a v) :=
    Finset.prod_congr rfl fun v hv => by rw [hS_eq v hv]

  have hχ := char_eq_mul_prod χ L (fun v => Hν.ord v a) (Hν.projS a) u (hχU u hu1 huS huU)
  have hN := norm_cpow_eq_mul_prod L (fun v => Hν.ord v a) (Hν.projS a) u
    (ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ u hu1 huU) s
  have hcomb : (L.map fun v => phiSh Wloc χ s v (Hν.ord v a)).prod =
      (L.map fun v => nloc v (zsh Wloc v (Hν.ord v a))).prod *
          (L.map fun v => ((χ (uniformizerIdele ℚ v) ^ Hν.ord v a : ℂˣ) : ℂ)).prod *
        (L.map fun v => (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ Hν.ord v a : ℝ) : ℂ) ^ (s - 1))).prod := by
    rw [← List.prod_map_mul, ← List.prod_map_mul]
    rfl
  calc zetaFn W χ g s a
      = innerInt W g a * ((χ (Hν.projS a * (L.map fun v => uniformizerIdele ℚ v ^ Hν.ord v a).prod * u) : ℂˣ) : ℂ) *
          ((ideleNorm ℚ (Hν.projS a * (L.map fun v => uniformizerIdele ℚ v ^ Hν.ord v a).prod * u) : ℝ) : ℂ) ^
            (s - 1) := by
        simp only [zetaFn]
        rw [← hau]
    _ = _ := by
        rw [hχ, hN, hinner, hsplit, htail, hfinite, hcomb]
        simp only [sPart, harch_eq, hSprod]
        ring

end Factorised

section Fubini

open NumberField.TateGlobal

variable (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℂ)

private theorem integrable_zetaFn
    (hG : letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
      Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
          W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((χ p.1 : ℂˣ) : ℂ) *
            ((ideleNorm ℚ p.1 : ℝ) : ℂ) ^ (s - 1))
        ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) :
    Integrable (zetaFn W χ g s) (NumberField.Idele.idelicHaar ℚ) := by
  letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  have h := hG.integral_prod_left
  refine h.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [zetaFn, innerInt]
  rw [integral_mul_const, integral_mul_const]

end Fubini

section Assembly

open NumberField.TateGlobal Filter Topology

private theorem integral_zetaFn_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W x = Warch (archComponent3 (𝓞 ℚ) ℚ x) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v x))
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hW1 : ∀ v, v ∉ S → Wloc v 1 = 1)
    (hint : ∀ v, v ∉ S → Integrable (fun y => Wloc v (lowerUnipotent21 y)) (selfDualHaarAt ℚ v))
    (hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
          * (∫ y, ‖Wloc v.1 (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχU : ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 → (∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) →
      NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ →
      χ u = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ)) (s : ℂ) (Ls : ℂ)
    (hprod : HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => ∑' m : ℤ, phiSh Wloc χ s v.1 m) Ls)
    (hfS : Integrable (sPart S Warch Wloc χ g s) Hν.νS)
    (hzeta : Integrable (zetaFn W χ g s) (NumberField.Idele.idelicHaar ℚ)) :
    ∫ a, zetaFn W χ g s a ∂(NumberField.Idele.idelicHaar ℚ) =
      (Hν.c : ℂ) * boxConst * (∫ a, sPart S Warch Wloc χ g s a ∂Hν.νS) * Ls := by
  have hsumm := summable_tIdent_sub_one S Wloc hK hW1 hint hsum

  have hEfin : {v : HeightOneSpectrum (𝓞 ℚ) | v ∉ S ∧ tIdent Wloc v = 0}.Finite := by
    have h := hsumm.tendsto_cofinite_zero.eventually (Metric.ball_mem_nhds (0 : ℂ) one_half_pos)
    rw [Filter.eventually_cofinite] at h
    refine (h.image Subtype.val).subset ?_
    rintro v ⟨hvS, hv0⟩
    refine ⟨⟨v, hvS⟩, ?_, rfl⟩
    simp only [Set.mem_setOf_eq, dist_zero_right, hv0, zero_sub, norm_neg, norm_one, not_lt]
    norm_num

  set Nw : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun v => if v ∈ hEfin.toFinset then 1 else Ideal.absNorm v.asIdeal
    with hNw
  have hNw1 : ∀ v, 1 ≤ Nw v := fun v => by
    simp only [hNw]
    split_ifs
    · exact le_rfl
    · have := two_le_absNorm v
      omega
  have hNw_le : ∀ v, Nw v ≤ Ideal.absNorm v.asIdeal := fun v => by
    simp only [hNw]
    split_ifs
    · have := two_le_absNorm v
      omega
    · exact le_rfl
  have hNw_summ : Summable fun v : HeightOneSpectrum (𝓞 ℚ) => ((Nw v : ℕ) : ℝ) ^ (-(4 : ℝ)) := by
    have hA : Summable fun v : HeightOneSpectrum (𝓞 ℚ) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(4 : ℝ)) :=
      NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt ℚ (by norm_num)
    have hB : Summable fun v : HeightOneSpectrum (𝓞 ℚ) => if v ∈ hEfin.toFinset then (1 : ℝ) else 0 :=
      summable_of_ne_finset_zero (s := hEfin.toFinset) fun v hv => if_neg hv
    refine (hA.add hB).of_nonneg_of_le (fun v => by positivity) fun v => ?_
    simp only [hNw]
    split_ifs with hvE
    · simp only [Nat.cast_one, Real.one_rpow]
      have : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(4 : ℝ)) := by positivity
      linarith
    · simp
  have hfin : ∀ n : ℕ, {v : HeightOneSpectrum (𝓞 ℚ) | Nw v ≤ n}.Finite := fun n =>
    finite_setOf_le_of_summable_rpow_neg hNw1 hNw_summ n
  set Lf : ℕ → List (HeightOneSpectrum (𝓞 ℚ)) := fun n => ((hfin n).toFinset.filter fun v => v ∉ S).toList
    with hLf
  have hmem : ∀ (n : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)), v ∈ Lf n ↔ Nw v ≤ n ∧ v ∉ S := fun n v => by
    simp only [hLf, Finset.mem_toList, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hLS : ∀ n : ℕ, ∀ v ∈ Lf n, v ∉ S := fun n v hv => ((hmem n v).1 hv).2
  have hLnd : ∀ n : ℕ, (Lf n).Nodup := fun n => Finset.nodup_toList _
  have hcov : ∀ (n : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)), v ∉ S → Ideal.absNorm v.asIdeal ≤ n → v ∈ Lf n :=
    fun n v hvS hn => (hmem n v).2 ⟨(hNw_le v).trans hn, hvS⟩
  have hmono : ∀ n : ℕ, Lf n ⊆ Lf (n + 1) := fun n v hv => by
    obtain ⟨h1, h2⟩ := (hmem n v).1 hv
    exact (hmem (n + 1) v).2 ⟨h1.trans (Nat.le_succ n), h2⟩
  have hE_mem : ∀ n : ℕ, 1 ≤ n → ∀ v, v ∉ tset S (Lf n) → tIdent Wloc v ≠ 0 := fun n hn v hv h0 => by
    have hvS : v ∉ S := fun hvS => hv ((mem_tset S _ v).2 (Or.inl hvS))
    have hvE : v ∈ hEfin.toFinset := hEfin.mem_toFinset.2 ⟨hvS, h0⟩
    refine hv ((mem_tset S _ v).2 (Or.inr ((hmem n v).2 ⟨?_, hvS⟩)))
    simp only [hNw, if_pos hvE]
    exact hn
  have hUmono := monotone_coe_unitIdelesOutside ℚ S Lf hmono
  have hUn := iUnion_coe_unitIdelesOutside_eq_univ ℚ S Lf hcov
  have hUmeas : ∀ n, MeasurableSet
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) :=
    fun n => Hν.measurableSet (Lf n) (hLS n) (hLnd n)

  have htset_mono : Monotone fun n => tset S (Lf n) := by
    refine monotone_nat_of_le_succ fun n => ?_
    simp only [tset]
    refine Finset.union_subset_union (Finset.Subset.refl S) fun v hv => ?_
    rw [List.mem_toFinset] at hv ⊢
    exact hmono n hv
  have htset_cov : ∀ v, ∃ n, v ∈ tset S (Lf n) := fun v => by
    by_cases hvS : v ∈ S
    · exact ⟨0, (mem_tset S _ v).2 (Or.inl hvS)⟩
    · exact ⟨Ideal.absNorm v.asIdeal, (mem_tset S _ v).2 (Or.inr (hcov _ v hvS le_rfl))⟩
  have htail := tendsto_tailProd S Wloc (fun n => tset S (Lf n)) htset_mono htset_cov
    (fun n => Finset.subset_union_left) hsumm hE_mem

  have hfac_n : ∀ n : ℕ, ∀ a ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) :
        Set (AdeleRing (𝓞 ℚ) ℚ)ˣ),
      zetaFn W χ g s a = boxConst * tailProd Wloc (tset S (Lf n)) * sPart S Warch Wloc χ g s (Hν.projS a) *
        ((Lf n).map fun v => phiSh Wloc χ s v (Hν.ord v a)).prod :=
    fun n a ha => zetaFn_eq S W Warch Wloc χ g hfac hK hW1 hint hsum hχU hg Hν s (Lf n) (hLS n) (hLnd n) a ha

  have hlim : Tendsto (fun n => ∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) :
      Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), zetaFn W χ g s a ∂(NumberField.Idele.idelicHaar ℚ)) atTop
      (𝓝 (∫ a, zetaFn W χ g s a ∂(NumberField.Idele.idelicHaar ℚ))) := by
    have h := tendsto_setIntegral_of_monotone hUmeas hUmono hzeta.integrableOn
    rwa [hUn, setIntegral_univ] at h
  by_cases hf0 : ∫ a, ‖sPart S Warch Wloc χ g s a‖ ∂Hν.νS = 0
  ·
    have hI0 : ∫ a, sPart S Warch Wloc χ g s a ∂Hν.νS = 0 := by
      have h := (integral_eq_zero_iff_of_nonneg (fun a => norm_nonneg _) hfS.norm).1 hf0
      refine integral_eq_zero_of_ae ?_
      filter_upwards [h] with a ha
      simpa using ha
    have hZ0 : ∫ a, zetaFn W χ g s a ∂(NumberField.Idele.idelicHaar ℚ) = 0 := by
      refine integral_eq_zero_of_ae ?_
      have hall : ∀ᵐ a ∂((NumberField.Idele.idelicHaar ℚ).restrict (⋃ n : ℕ,
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ))),
          zetaFn W χ g s a = 0 := by
        rw [ae_restrict_iUnion_iff]
        intro n
        have hae := ae_eq_zero_of_integral_norm_eq_zero Hν _ hfS hf0 (Lf n) (hLS n) (hLnd n)
        rw [ae_restrict_iff' (hUmeas n)] at hae ⊢
        filter_upwards [hae] with a ha haU
        rw [hfac_n n a haU, ha haU]
        simp
      rwa [hUn, Measure.restrict_univ] at hall
    rw [hZ0, hI0]
    ring
  by_cases hzero : ∃ v₀ : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, ∀ m : ℤ, phiSh Wloc χ s v₀.1 m = 0
  ·
    obtain ⟨v₀, hv₀⟩ := hzero
    have hLs : Ls = 0 := by
      refine hprod.unique ?_
      have h0 : (∑' m : ℤ, phiSh Wloc χ s v₀.1 m) = 0 := by simp [hv₀]
      exact hasProd_zero_of_exists_eq_zero ⟨v₀, h0⟩
    have hZ : ∀ a, zetaFn W χ g s a = 0 := fun a => by
      obtain ⟨n₁, hn₁⟩ : ∃ n, a ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) := by
        have : a ∈ ⋃ n : ℕ, (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) := by
          rw [hUn]; trivial
        exact Set.mem_iUnion.1 this
      set n := max n₁ (Ideal.absNorm v₀.1.asIdeal) with hn
      have haU : a ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) := hUmono (le_max_left _ _) hn₁
      have hv₀n : v₀.1 ∈ Lf n := hcov n v₀.1 v₀.2 (le_max_right _ _)
      rw [hfac_n n a haU]
      have : ((Lf n).map fun v => phiSh Wloc χ s v (Hν.ord v a)).prod = 0 :=
        List.prod_eq_zero (List.mem_map.2 ⟨v₀.1, hv₀n, hv₀ _⟩)
      rw [this, mul_zero]
    simp [hZ, hLs]

  have hzero' : ∀ v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, ∃ m : ℤ, phiSh Wloc χ s v.1 m ≠ 0 :=
    fun v => not_forall.mp (not_exists.mp hzero v)
  have hsumφ : ∀ n : ℕ, 1 ≤ n → ∀ v ∈ Lf n, Summable fun m : ℤ => ‖phiSh Wloc χ s v m‖ := fun n hn => by
    have hne : boxConst * tailProd Wloc (tset S (Lf n)) ≠ 0 :=
      mul_ne_zero boxConst_ne_zero
        (tailProd_ne_zero S Wloc (tset S (Lf n)) Finset.subset_union_left hsumm (hE_mem n hn))
    refine summable_of_integrableOn Hν _ hfS hf0 (phiSh Wloc χ s) (Lf n) (hLS n) (hLnd n)
      (fun v hv => hzero' ⟨v, hLS n v hv⟩) ?_
    have h : IntegrableOn (fun a => zetaFn W χ g s a / (boxConst * tailProd Wloc (tset S (Lf n))))
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)
        (NumberField.Idele.idelicHaar ℚ) :=
      hzeta.integrableOn.div_const _
    refine h.congr_fun (fun a ha => ?_) (hUmeas n)
    beta_reduce
    rw [hfac_n n a ha, mul_assoc (boxConst * tailProd Wloc (tset S (Lf n))), mul_comm (boxConst * _), mul_div_assoc,
      div_self hne, mul_one]
  have hvals : ∀ n : ℕ, 1 ≤ n →
      (∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), zetaFn W χ g s a ∂(NumberField.Idele.idelicHaar ℚ)) =
        boxConst * tailProd Wloc (tset S (Lf n)) *
          ((Hν.c : ℂ) * (∫ a, sPart S Warch Wloc χ g s a ∂Hν.νS) *
            ((Lf n).map fun v => ∑' m : ℤ, phiSh Wloc χ s v m).prod) := fun n hn => by
    have hton := (Hν.tonelli (Lf n) (hLS n) (hLnd n) (sPart S Warch Wloc χ g s) (phiSh Wloc χ s) hfS (hsumφ n hn)).2
    rw [← hton, ← integral_const_mul]
    exact setIntegral_congr_fun (hUmeas n) fun a ha => by rw [hfac_n n a ha]; ring
  have hlim' : Tendsto (fun n => boxConst * tailProd Wloc (tset S (Lf n)) *
      ((Hν.c : ℂ) * (∫ a, sPart S Warch Wloc χ g s a ∂Hν.νS) *
        ((Lf n).map fun v => ∑' m : ℤ, phiSh Wloc χ s v m).prod)) atTop
      (𝓝 (boxConst * 1 * ((Hν.c : ℂ) * (∫ a, sPart S Warch Wloc χ g s a ∂Hν.νS) * Ls))) := by
    have hP := tendsto_prod_toList_filter_of_hasProd (fun v => v ∉ S) (fun v => ∑' m : ℤ, phiSh Wloc χ s v m) hprod
      Nw hfin
    exact (tendsto_const_nhds.mul htail).mul ((tendsto_const_nhds.mul tendsto_const_nhds).mul hP)
  have hlim'' : Tendsto (fun n => ∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S ∪ {v | v ∈ Lf n}) :
      Set (AdeleRing (𝓞 ℚ) ℚ)ˣ), zetaFn W χ g s a ∂(NumberField.Idele.idelicHaar ℚ)) atTop
      (𝓝 (boxConst * 1 * ((Hν.c : ℂ) * (∫ a, sPart S Warch Wloc χ g s a ∂Hν.νS) * Ls))) := by
    refine hlim'.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hvals n hn).symm
  rw [tendsto_nhds_unique hlim hlim'']
  ring

end Assembly

end

end LanglandsTunnell.CubicInduction.EulerProductUnipotent

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable.LanglandsTunnell.CubicInduction in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in
attribute [local instance] LanglandsTunnell.TateLocal.localBorel in
open scoped Classical in
theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W x = Warch (archComponent3 (𝓞 ℚ) ℚ x) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v x))
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hW1 : ∀ v, v ∉ S → Wloc v 1 = 1)
    (hint : ∀ v, v ∉ S →
      letI := localBorel ℚ v
      Integrable (fun y => Wloc v (lowerUnipotent21 y)) (selfDualHaarAt ℚ v))
    (hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
          * (∫ y, ‖Wloc v.1 (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχU : ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) →
      NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ →
      χ u = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (σ₀ : ℝ) (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          letI := localBorel ℚ v.1
          ((selfDualHaarAt ℚ v.1).real {u : v.1.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
          ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZeta31 v.1 (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v.1)))
              (selfDualHaarAt ℚ v.1) (Wloc v.1) (TateGlobal.localChar χ v.1) s 1)
        (L s))
    (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ))
    (hS : ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        (∫ y : mixedEmbedding.mixedSpace ℚ,
            Warch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
              lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
          (∏ v ∈ S,
            (letI := localBorel ℚ v
             ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
               ∫ x : v.adicCompletion ℚ,
                 Wloc v (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                   lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                   ∂(selfDualHaarAt ℚ v))) *
          ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
        Hν.νS)
    (hG : ∀ s : ℂ, σ₀ < s.re →
      letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
      Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
        W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((χ p.1 : ℂˣ) : ℂ) *
          ((TateGlobal.ideleNorm ℚ p.1 : ℝ) : ℂ) ^ (s - 1))
        ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) :
    ∀ s : ℂ, σ₀ < s.re →
      globalZeta31 W χ s g =
        (Hν.c : ℂ) * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
          (((2 : ℝ) ^ nrComplexPlaces ℚ / Real.sqrt |(discr ℚ : ℝ)| : ℝ) : ℂ) *
          (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
            (∫ y : mixedEmbedding.mixedSpace ℚ,
                Warch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                  lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
              (∏ v ∈ S,
                (letI := localBorel ℚ v
                 ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                   ∫ x : v.adicCompletion ℚ,
                     Wloc v (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                       lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                       ∂(selfDualHaarAt ℚ v))) *
              ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
            ∂Hν.νS) *
          L s := by
  intro s hs
  have hfun : (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real {u : v.1.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) : ℂ)⁻¹ *
        localZeta31 v.1 (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v.1)))
          (selfDualHaarAt ℚ v.1) (Wloc v.1) (TateGlobal.localChar χ v.1) s 1) =
      fun v => ∑' m : ℤ, EulerProductUnipotent.phiSh Wloc χ s v.1 m :=
    funext fun v => EulerProductUnipotent.localZeta31_eq_tsum_phiSh S Wloc χ hK hχU v.1 v.2 s
  have hprod : HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      ∑' m : ℤ, EulerProductUnipotent.phiSh Wloc χ s v.1 m) (L s) := by
    have h := hL s hs
    rwa [hfun] at h
  have hmain := EulerProductUnipotent.integral_zetaFn_eq S W Warch Wloc hfac hK hW1 hint hsum χ hχU g hg Hν s (L s)
    hprod
    (hS s hs) (EulerProductUnipotent.integrable_zetaFn W χ g s (hG s hs))
  rw [EulerProductUnipotent.globalZeta31_eq, hmain]
  simp only [EulerProductUnipotent.boxConst, EulerProductUnipotent.sPart, EulerProductUnipotent.nloc,
    EulerProductUnipotent.hfam, EulerProductUnipotent.farch, mul_assoc]

end S_LanglandsTunnell_CubicInduction_globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable (solution)
