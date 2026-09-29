-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/19fe7c15-7f03-5eae-9916-40295ead11ec

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

section Algebra

variable {A : Type*} [CommRing A]

private theorem longWeyl3_mul_longWeyl3 : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  simp [transposeInv3, mul_inv_rev, Matrix.transpose_mul]

private theorem transposeInv3_upperUnipotent3 (x y z : A) :
    transposeInv3 (upperUnipotent3 x y z)
      = longWeyl3 * upperUnipotent3 (-y) (-x) (x * y - z) * longWeyl3 := by
  have htr : ((transposeInv3 (upperUnipotent3 x y z) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
      = !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1] := by
    change Matrix.transpose (((upperUnipotent3 x y z : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) :
      Matrix (Fin 3) (Fin 3) A) = _
    rw [show (((upperUnipotent3 x y z : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
        = !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] from rfl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  refine Units.ext ?_
  rw [htr, Units.val_mul, Units.val_mul, longWeyl3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem upperUnipotent3_mul_upperUnipotent3 (x y z x' y' z' : A) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z'
      = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end Algebra

section RationalPoints

private theorem globalPointsGL_longWeyl3 :
    globalPointsGL 3 (𝓞 ℚ) ℚ (longWeyl3 : GL (Fin 3) ℚ)
      = (longWeyl3 : GL (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalPointsGL, Matrix.GeneralLinearGroup.map, longWeyl3]

private theorem globalPointsGL_upperUnipotent3 (a b c : ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (upperUnipotent3 a b c)
      = upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) b)
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalPointsGL, Matrix.GeneralLinearGroup.map, upperUnipotent3]

end RationalPoints

section CharacterContinuity

open MeasureTheory Filter Topology
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]

private theorem addChar_continuous_of_aestronglyMeasurable_restrict
    (μ : Measure G) [μ.IsAddHaarMeasure] [μ.InnerRegular] (ψ : AddChar G ℂ) (S : Set G)
    (hS : MeasurableSet S) (hpos : 0 < μ S) (hψ : AEStronglyMeasurable (fun x => ψ x) (μ.restrict S)) :
    Continuous ψ := by

  set g : G → ℂ := hψ.mk (fun x => ψ x) with hg_def
  have hg : StronglyMeasurable g := hψ.stronglyMeasurable_mk
  have hgm : Measurable g := hg.measurable
  have hae : ∀ᵐ x ∂μ, x ∈ S → ψ x = g x := (ae_restrict_iff' hS).1 hψ.ae_eq_mk
  set B : Set G := {x | ¬ (x ∈ S → ψ x = g x)} with hB_def
  have hB : μ B = 0 := ae_iff.1 hae
  set N : Set G := toMeasurable μ B with hN_def
  have hN0 : μ N = 0 := by rw [hN_def, measure_toMeasurable]; exact hB
  set S' : Set G := S \ N with hS'_def
  have hS'm : MeasurableSet S' := hS.diff (measurableSet_toMeasurable μ B)
  have hS'pos : 0 < μ S' := by rw [hS'_def, measure_diff_null hN0]; exact hpos
  have hS'eq : ∀ x ∈ S', ψ x = g x := by
    intro x hx
    by_contra hne
    exact hx.2 (subset_toMeasurable μ B (fun h => hne (h hx.1)))
  have hψne : ∀ x : G, ψ x ≠ 0 := by
    intro x hx
    have h1 : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hx, zero_mul] at h1
    exact zero_ne_one h1

  have h0 : Tendsto (fun x => ψ x) (𝓝 (0 : G)) (𝓝 (1 : ℂ)) := by
    intro U hU

    have hdiv : Tendsto (fun p : ℂ × ℂ => p.1 / p.2) (𝓝 ((1 : ℂ), (1 : ℂ))) (𝓝 (1 : ℂ)) := by
      have : ContinuousAt (fun p : ℂ × ℂ => p.1 / p.2) ((1 : ℂ), (1 : ℂ)) :=
        continuousAt_fst.div continuousAt_snd one_ne_zero
      simpa using this.tendsto
    obtain ⟨W₁, hW₁, W₂, hW₂, hW₁₂⟩ := mem_nhds_prod_iff.1 (hdiv hU)
    obtain ⟨W, hWsub, hWo, hW1⟩ := mem_nhds_iff.1 (inter_mem hW₁ hW₂)
    have hWdiv : ∀ v ∈ W, ∀ w ∈ W, v / w ∈ U := fun v hv w hw =>
      hW₁₂ (Set.mk_mem_prod (hWsub hv).1 (hWsub hw).2)

    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
    set D' : Set ℂ := {q ∈ D | q ≠ 0} with hD'_def
    have hD'c : D'.Countable := hDc.mono (fun q hq => hq.1)
    set E : ℂ → Set G := fun q => S' ∩ {x | g x / q ∈ W} with hE_def
    have hEm : ∀ q, MeasurableSet (E q) := fun q =>
      hS'm.inter (hWo.measurableSet.preimage (hgm.div_const q))
    have hcover : S' ⊆ ⋃ q ∈ D', E q := by
      intro x hx
      have hgx : g x ≠ 0 := by rw [← hS'eq x hx]; exact hψne x
      have hO : IsOpen ({q : ℂ | q ≠ 0} ∩ (fun q : ℂ => g x / q) ⁻¹' W) :=
        (continuousOn_const.div continuousOn_id (fun q hq => hq)).isOpen_inter_preimage isOpen_ne hWo
      have hOne : ({q : ℂ | q ≠ 0} ∩ (fun q : ℂ => g x / q) ⁻¹' W).Nonempty :=
        ⟨g x, hgx, by simp only [Set.mem_preimage, div_self hgx]; exact hW1⟩
      obtain ⟨q, hqD, hq0, hqW⟩ := hDd.exists_mem_open hO hOne
      exact Set.mem_biUnion (show q ∈ D' from ⟨hqD, hq0⟩) ⟨hx, hqW⟩
    obtain ⟨q, hqD', hEq⟩ : ∃ q ∈ D', 0 < μ (E q) := by
      by_contra hcon
      push Not at hcon
      have hnull : μ (⋃ q ∈ D', E q) = 0 :=
        (measure_biUnion_null_iff hD'c).2 (fun q hq => le_antisymm (hcon q hq) zero_le)
      exact hS'pos.ne' (measure_mono_null hcover hnull)

    have hnhds : E q - E q ∈ 𝓝 (0 : G) :=
      Measure.sub_mem_nhds_zero_of_addHaar_pos μ (E q) (hEm q) hEq
    refine Filter.mem_map.2 (mem_of_superset hnhds ?_)
    rintro z ⟨a, ha, b, hb, rfl⟩
    have hqa : g a / q ∈ W := ha.2
    have hqb : g b / q ∈ W := hb.2
    have hab : ψ (a - b) = (g a / q) / (g b / q) := by
      rw [AddChar.map_sub_eq_div, hS'eq a ha.1, hS'eq b hb.1, div_div_div_cancel_right₀ hqD'.2]
    show ψ (a - b) ∈ U
    rw [hab]
    exact hWdiv _ hqa _ hqb

  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have h1 : Tendsto (fun x => ψ x₀ * ψ (x - x₀)) (𝓝 x₀) (𝓝 (ψ x₀ * 1)) :=
    (h0.comp (by
      simpa using (tendsto_id.sub_const x₀ : Tendsto (fun x : G => x - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀))))).const_mul _
  have h2 : (fun x => ψ x₀ * ψ (x - x₀)) = fun x => ψ x := by
    funext x; rw [← AddChar.map_add_eq_mul, add_sub_cancel]
  rw [h2, mul_one] at h1
  exact h1

end CharacterContinuity

section BoxIntegral

variable (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
  (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)

private theorem regular_adelicAddHaar :
    letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).Regular := by
  letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  exact MeasureTheory.Measure.regular_addHaarMeasure

private theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  have h : ((AdeleRing.principalSubgroup (𝓞 ℚ) ℚ : Set (AdeleRing (𝓞 ℚ) ℚ))).Countable := by
    simpa only [AdeleRing.principalSubgroup, Subring.coe_toAddSubgroup, RingHom.coe_range] using
      Set.countable_range (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))
  exact h.to_subtype

private theorem integral_pins_comp_sub (f : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hf : ∀ (q : ℚ) (t : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + t) = f t)
    (u : AdeleRing (𝓞 ℚ) ℚ) :
    letI := (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).nS
    ∫ t, f (u - t) ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
      = ∫ t, f t ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI : (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).Regular := regular_adelicAddHaar
  haveI := countable_principalSubgroup
  show (∫ t, f (u - t)
        ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)))
      = ∫ t, f t
        ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
  simp only [ProbabilityTheory.cond, MeasureTheory.integral_smul_measure]
  congr 1
  have hφ : MeasureTheory.MeasurePreserving (fun t : AdeleRing (𝓞 ℚ) ℚ => u - t)
      (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
    MeasureTheory.Measure.measurePreserving_sub_left _ u
  have hbox := AdelicBox.isAddFundamentalDomain_adelicBox ℚ (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)

  have hbox' : MeasureTheory.IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)
      ((fun t : AdeleRing (𝓞 ℚ) ℚ => u - t) ⁻¹' AdelicBox.adelicBox ℚ)
      (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
    hbox.preimage_of_equiv hφ.quasiMeasurePreserving (e := fun g => -g) neg_involutive.bijective
      (fun g x => show u - (((-g : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ) + x)
          = (g : AdeleRing (𝓞 ℚ) ℚ) + (u - x) by rw [AddSubgroup.coe_neg]; abel)
  have hinv : ∀ (g : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : AdeleRing (𝓞 ℚ) ℚ),
      f (g +ᵥ x) = f x := by
    intro g x
    have hg : (g : AdeleRing (𝓞 ℚ) ℚ) ∈ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).range := g.2
    obtain ⟨q, hq⟩ := RingHom.mem_range.mp hg
    show f ((g : AdeleRing (𝓞 ℚ) ℚ) + x) = f x
    rw [← hq]
    exact hf q x
  have hpre : (fun t : AdeleRing (𝓞 ℚ) ℚ => u - t) ⁻¹'
      ((fun t : AdeleRing (𝓞 ℚ) ℚ => u - t) ⁻¹' AdelicBox.adelicBox ℚ) = AdelicBox.adelicBox ℚ := by
    ext t
    simp
  calc ∫ t in AdelicBox.adelicBox ℚ, f (u - t) ∂(AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
      = ∫ t in (fun t : AdeleRing (𝓞 ℚ) ℚ => u - t) ⁻¹'
            ((fun t : AdeleRing (𝓞 ℚ) ℚ => u - t) ⁻¹' AdelicBox.adelicBox ℚ),
          f (u - t) ∂(AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by rw [hpre]
    _ = ∫ t in (fun t : AdeleRing (𝓞 ℚ) ℚ => u - t) ⁻¹' AdelicBox.adelicBox ℚ,
          f t ∂(AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
        hφ.setIntegral_preimage_emb (measurableEmbedding_subLeft u) f _
    _ = ∫ t in AdelicBox.adelicBox ℚ, f t ∂(AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
        hbox'.setIntegral_eq hbox hinv

private theorem integral_pins_comp_sub_right (f : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hf : ∀ (q : ℚ) (t : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + t) = f t)
    (v : AdeleRing (𝓞 ℚ) ℚ) :
    letI := (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).nS
    ∫ t, f (t - v) ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
      = ∫ t, f t ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  have hf' : ∀ (q : ℚ) (t : AdeleRing (𝓞 ℚ) ℚ),
      f (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + t)) = f (-t) := by
    intro q t
    rw [neg_add, ← map_neg (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)), hf]
  have h1 := integral_pins_comp_sub D U gen (fun t => f (-t)) hf' v
  have h2 := integral_pins_comp_sub D U gen f hf 0
  simp only [neg_sub, zero_sub] at h1 h2
  exact h1.trans h2

private scoped instance countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
  haveI : Countable Nat.Primes := inferInstanceAs (Countable {p : ℕ // p.Prime})
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective.countable

private scoped instance secondCountable_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  RestrictedProduct.secondCountableTopology (fun v => isOpenAdicCompletionIntegers ℚ v)

private scoped instance secondCountable_infinitePlaceCompletion (v : InfinitePlace ℚ) :
    SecondCountableTopology v.Completion :=
  haveI : Countable (WithAbs v.1) := (WithAbs.equiv (v := v.1)).injective.countable
  haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
  (NumberField.InfinitePlace.Completion.isometry_toCompletion (v := v)).isEmbedding.secondCountableTopology

private scoped instance secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing ℚ)
    :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace ℚ) → v.Completion))

private scoped instance secondCountable_adeleRing : SecondCountableTopology (𝔸) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ))

private theorem continuous_upperUnipotent3_mul (w : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous (fun p : (𝔸 × 𝔸) × 𝔸 => upperUnipotent3 p.1.1 p.1.2 p.2 * w) := by
  refine Continuous.mul ?_ continuous_const
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

private theorem exists_bound_on_box (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ)
    (w : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ M : ℝ, ∀ x ∈ AdelicBox.adelicBox ℚ, ∀ y ∈ AdelicBox.adelicBox ℚ, ∀ z ∈ AdelicBox.adelicBox ℚ,
      ‖Φ (upperUnipotent3 x y z * w)‖ ≤ M := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  obtain ⟨M, hM⟩ := ((hC.prod hC).prod hC).exists_bound_of_continuousOn
    (hΦ.comp (continuous_upperUnipotent3_mul w)).continuousOn
  exact ⟨M, fun x hx y hy z hz => hM ((x, y), z) ⟨⟨hsub hx, hsub hy⟩, hsub hz⟩⟩

private theorem exists_bound_char_on_box (ψ : AddChar (𝔸) ℂ) (hψ : Continuous ψ) :
    ∃ M : ℝ, ∀ x ∈ AdelicBox.adelicBox ℚ, ∀ y ∈ AdelicBox.adelicBox ℚ, ‖ψ (-(x + y))‖ ≤ M := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hc : Continuous (fun p : 𝔸 × 𝔸 => ψ (-(p.1 + p.2))) := hψ.comp (by fun_prop)
  obtain ⟨M, hM⟩ := (hC.prod hC).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨M, fun x hx y hy => hM (x, y) ⟨hsub hx, hsub hy⟩⟩

private theorem isProbabilityMeasure_ν :
    MeasureTheory.IsProbabilityMeasure (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν :=
  isProbabilityMeasure_productionPinsOf_ν ℚ D U gen (AdelicBox.adelicBox ℚ)
    (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne' (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

private theorem ae_prod_mem_box :
    letI := (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).nS
    ∀ᵐ p ∂(((productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν).prod
        (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν),
      p.1 ∈ AdelicBox.adelicBox ℚ ∧ p.2 ∈ AdelicBox.adelicBox ℚ := by
  letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := isProbabilityMeasure_ν D U gen
  have hb : MeasurableSet (AdelicBox.adelicBox ℚ) := AdelicBox.measurableSet_adelicBox ℚ
  have h := (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
    (μ := (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
        (ν := (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
    (s := AdelicBox.adelicBox ℚ ×ˢ AdelicBox.adelicBox ℚ) (hb.prod hb)).mpr
    ((ProbabilityTheory.ae_cond_mem hb).mono fun x hx =>
      (ProbabilityTheory.ae_cond_mem hb).mono fun y hy => Set.mk_mem_prod hx hy)
  exact h

private theorem integral_mul_char_eq_zero_of_not_continuous (ψ : AddChar (𝔸) ℂ)
    (hψ : ¬ Continuous ψ) (c : 𝔸) (H : 𝔸 → ℂ)
    (hH : letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ; MeasureTheory.StronglyMeasurable H) :
    letI := (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).nS
    ∫ y, H y * ψ (-(c + y)) ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν = 0 := by
  letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI : (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).Regular := regular_adelicAddHaar
  haveI : (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).InnerRegular := inferInstance
  set μ : MeasureTheory.Measure (𝔸) := AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ with hμ_def
  have hb : MeasurableSet (AdelicBox.adelicBox ℚ) := AdelicBox.measurableSet_adelicBox ℚ

  set ψ' : AddChar (𝔸) ℂ := ψ.compAddMonoidHom (-(AddMonoidHom.id (𝔸))) with hψ'_def
  have hψ'_apply : ∀ y, ψ' y = ψ (-y) := fun y => by simp [hψ'_def]
  have hsplit : ∀ y, ψ (-(c + y)) = ψ (-c) * ψ' y := fun y => by
    rw [hψ'_apply, ← AddChar.map_add_eq_mul, neg_add]
  have hψ'not : ¬ Continuous ψ' := by
    intro h
    apply hψ
    have : (fun y => ψ y) = fun y => ψ' (-y) := by funext y; rw [hψ'_apply, neg_neg]
    exact (show Continuous (fun y => ψ y) from this ▸ h.comp continuous_neg)
  show ∫ y, H y * ψ (-(c + y)) ∂(ProbabilityTheory.cond μ (AdelicBox.adelicBox ℚ)) = 0
  by_cases hm : MeasureTheory.AEStronglyMeasurable (fun y => H y * ψ (-(c + y)))
      (ProbabilityTheory.cond μ (AdelicBox.adelicBox ℚ))
  swap
  · exact MeasureTheory.integral_non_aestronglyMeasurable hm

  set S : Set (𝔸) := H ⁻¹' {0}ᶜ with hS_def
  have hSm : MeasurableSet S := hH.measurable (MeasurableSet.singleton (0 : ℂ)).compl
  by_cases hS0 : ProbabilityTheory.cond μ (AdelicBox.adelicBox ℚ) S = 0
  ·
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    have hae : ∀ᵐ y ∂(ProbabilityTheory.cond μ (AdelicBox.adelicBox ℚ)), y ∉ S :=
      MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hS0
    filter_upwards [hae] with y hy
    have hy0 : H y = 0 := by
      by_contra h0
      exact hy (show y ∈ S from h0)
    simp [hy0]
  · exfalso
    apply hψ'not

    have hpos : 0 < μ (S ∩ AdelicBox.adelicBox ℚ) := by
      rw [ProbabilityTheory.cond_apply hb μ S, Set.inter_comm] at hS0
      exact pos_iff_ne_zero.2 (fun h => hS0 (by rw [h, mul_zero]))

    have hm₁ : MeasureTheory.AEStronglyMeasurable (fun y => H y * ψ (-(c + y)))
        (μ.restrict (AdelicBox.adelicBox ℚ)) := by
      have hc0 : (μ (AdelicBox.adelicBox ℚ))⁻¹ ≠ 0 :=
        ENNReal.inv_ne_zero.2 (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne
      simp only [ProbabilityTheory.cond] at hm
      exact hm.mono_ac (MeasureTheory.Measure.absolutelyContinuous_smul hc0)
    have hm₂ : MeasureTheory.AEStronglyMeasurable (fun y => H y * ψ (-(c + y)))
        (μ.restrict (S ∩ AdelicBox.adelicBox ℚ)) := by
      rw [← MeasureTheory.Measure.restrict_restrict hSm]
      exact hm₁.restrict
    have hdiv : MeasureTheory.AEStronglyMeasurable
        (fun y => (H y * ψ (-(c + y))) / (H y * ψ (-c))) (μ.restrict (S ∩ AdelicBox.adelicBox ℚ)) :=
      (hm₂.aemeasurable.div (hH.measurable.mul_const _).aemeasurable).aestronglyMeasurable
    have hcne : ψ (-c) ≠ 0 := by
      intro h0
      have h1 : ψ (-c) * ψ c = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    have hae' : (fun y => (H y * ψ (-(c + y))) / (H y * ψ (-c)))
        =ᵐ[μ.restrict (S ∩ AdelicBox.adelicBox ℚ)] fun y => ψ' y := by
      filter_upwards [MeasureTheory.ae_restrict_mem (hSm.inter hb)] with y hy
      have hHy : H y ≠ 0 := hy.1
      rw [hsplit y]
      field_simp
    have hψ'm : MeasureTheory.AEStronglyMeasurable (fun y => ψ' y)
        (μ.restrict (S ∩ AdelicBox.adelicBox ℚ)) := hdiv.congr hae'
    exact addChar_continuous_of_aestronglyMeasurable_restrict μ ψ' (S ∩ AdelicBox.adelicBox ℚ)
      (hSm.inter hb) hpos hψ'm

private theorem continuous_swapped_triple (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ)
    (w : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Continuous (fun q : (𝔸 × 𝔸) × 𝔸 => Φ (upperUnipotent3 q.1.2 q.1.1 q.2 * w)) := by
  refine hΦ.comp ?_
  refine Continuous.mul ?_ continuous_const
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

private theorem integral_integral_swap_box_of_continuous (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hΦ : Continuous Φ) (ψ : AddChar (𝔸) ℂ) (hψ : Continuous ψ)
    (w : AdelicGL 3 (𝓞 ℚ) ℚ) :
    letI := (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).nS
    ∫ x, ∫ y, (∫ z, Φ (upperUnipotent3 y x z * w)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(x + y))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
      = ∫ x, ∫ y, (∫ z, Φ (upperUnipotent3 x y z * w)
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(y + x))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := isProbabilityMeasure_ν D U gen
  have hb : MeasurableSet (AdelicBox.adelicBox ℚ) := AdelicBox.measurableSet_adelicBox ℚ

  set f : 𝔸 → 𝔸 → ℂ := fun x y =>
    (∫ z, Φ (upperUnipotent3 y x z * w) ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
        * ψ (-(x + y)) with hf_def

  haveI : @MeasureTheory.IsProbabilityMeasure 𝔸 (AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
      (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν :=
    isProbabilityMeasure_ν D U gen
  refine (MeasureTheory.integral_integral_swap (f := f) ?_)

  have hF := (continuous_swapped_triple Φ hΦ w).stronglyMeasurable
  have hH : MeasureTheory.StronglyMeasurable
      (fun p : 𝔸 × 𝔸 => ∫ z, Φ (upperUnipotent3 p.2 p.1 z * w)
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) :=
    hF.integral_prod_right'
  have hψm : MeasureTheory.StronglyMeasurable (fun p : 𝔸 × 𝔸 => ψ (-(p.1 + p.2))) :=
    (hψ.comp (by fun_prop)).stronglyMeasurable
  have hmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry f)
      (((productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν).prod
        (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) :=
    (hH.mul hψm).aestronglyMeasurable

  obtain ⟨M₁, hM₁⟩ := exists_bound_on_box Φ hΦ w
  obtain ⟨M₂, hM₂⟩ := exists_bound_char_on_box ψ hψ
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrable_const (max M₁ 0 * max M₂ 0)) hmeas ?_
  refine (ae_prod_mem_box D U gen).mono fun p hp => ?_
  obtain ⟨x, y⟩ := p
  simp only [hf_def, Function.uncurry_apply_pair, norm_mul]
  have hae : ∀ᵐ z ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν,
      ‖Φ (upperUnipotent3 y x z * w)‖ ≤ M₁ :=
    (ProbabilityTheory.ae_cond_mem hb).mono fun z hz => hM₁ y hp.2 x hp.1 z hz
  have h₁ : ‖∫ z, Φ (upperUnipotent3 y x z * w)
      ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν‖ ≤ M₁ := by
    have h := MeasureTheory.norm_integral_le_of_norm_le_const hae
    rwa [MeasureTheory.probReal_univ, mul_one] at h
  exact mul_le_mul (h₁.trans (le_max_left _ _)) ((hM₂ x hp.1 y hp.2).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

private theorem continuous_slice_left (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ)
    (w : AdelicGL 3 (𝓞 ℚ) ℚ) (x : 𝔸) :
    Continuous (fun q : 𝔸 × 𝔸 => Φ (upperUnipotent3 q.1 x q.2 * w)) := by
  refine hΦ.comp ?_
  refine Continuous.mul ?_ continuous_const
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

private theorem continuous_slice_right (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ)
    (w : AdelicGL 3 (𝓞 ℚ) ℚ) (x : 𝔸) :
    Continuous (fun q : 𝔸 × 𝔸 => Φ (upperUnipotent3 x q.1 q.2 * w)) := by
  refine hΦ.comp ?_
  refine Continuous.mul ?_ continuous_const
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

private theorem integral_integral_swap_box (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ)
    (ψ : AddChar (𝔸) ℂ) (w : AdelicGL 3 (𝓞 ℚ) ℚ) :
    letI := (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).nS
    ∫ x, ∫ y, (∫ z, Φ (upperUnipotent3 y x z * w)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(x + y))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
      = ∫ x, ∫ y, (∫ z, Φ (upperUnipotent3 x y z * w)
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(y + x))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  by_cases hψ : Continuous ψ
  · exact integral_integral_swap_box_of_continuous D U gen Φ hΦ ψ hψ w
  ·
    letI := AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
    haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
    haveI := isProbabilityMeasure_ν D U gen

    haveI : @MeasureTheory.IsProbabilityMeasure 𝔸 (AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
        (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν :=
      isProbabilityMeasure_ν D U gen
    have hL : ∀ x : 𝔸, (∫ y, (∫ z, Φ (upperUnipotent3 y x z * w)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(x + y))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) = 0 := by
      intro x
      refine integral_mul_char_eq_zero_of_not_continuous D U gen ψ hψ x _ ?_
      exact (continuous_slice_left Φ hΦ w x).stronglyMeasurable.integral_prod_right'
    have hR : ∀ x : 𝔸, (∫ y, (∫ z, Φ (upperUnipotent3 x y z * w)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(y + x))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) = 0 := by
      intro x
      simp_rw [show ∀ y : 𝔸, -(y + x) = -(x + y) from fun y => by rw [add_comm]]
      refine integral_mul_char_eq_zero_of_not_continuous D U gen ψ hψ x _ ?_
      exact (continuous_slice_right Φ hΦ w x).stronglyMeasurable.integral_prod_right'
    simp only [hL, hR, MeasureTheory.integral_zero]

end BoxIntegral

section FormLemmas

variable {K : Type} [Field K] [NumberField K]
  [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  {D : Set (AdelicGL2 (𝓞 ℚ) ℚ)} {U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)}
  {gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ}
  (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
include X hX

private theorem form_per (a b c : ℚ) (x y z : AdeleRing (𝓞 ℚ) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    X.form (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a + x)
      (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) b + y)
      (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) c + z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y) * h)
      = X.form (upperUnipotent3 x y z * h) := by
  rw [← upperUnipotent3_mul_upperUnipotent3, ← globalPointsGL_upperUnipotent3, mul_assoc,
    hX.automorphic]

private theorem form_per_z (x y : AdeleRing (𝓞 ℚ) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (q : ℚ)
    (z : AdeleRing (𝓞 ℚ) ℚ) :
    X.form (upperUnipotent3 x y (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + z) * h)
      = X.form (upperUnipotent3 x y z * h) := by
  simpa using form_per X hX 0 0 q x y z h

private theorem form_conj (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    X.form (transposeInv3 (upperUnipotent3 x y z * g))
      = X.form (upperUnipotent3 (-y) (-x) (x * y - z) * (longWeyl3 * transposeInv3 g)) := by
  rw [transposeInv3_mul, transposeInv3_upperUnipotent3]
  simp only [mul_assoc]
  nth_rewrite 1 [← globalPointsGL_longWeyl3]
  rw [hX.automorphic]

private theorem integral_G1 (q : ℚ) (a b : AdeleRing (𝓞 ℚ) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∫ z, X.form (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + a) b z * h)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
      = ∫ z, X.form (upperUnipotent3 a b z * h)
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  have h1 : ∀ z : AdeleRing (𝓞 ℚ) ℚ,
      X.form (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + a) b z * h)
        = X.form (upperUnipotent3 a b (z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q * b) * h) := by
    intro z
    have := form_per X hX q 0 0 a b (z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q * b) h
    simpa only [map_zero, zero_add, sub_add_cancel] using this
  simp_rw [h1]
  exact integral_pins_comp_sub_right D U gen (fun z => X.form (upperUnipotent3 a b z * h))
    (fun q' z => form_per_z X hX a b h q' z) _

private theorem integral_G2 (q : ℚ) (a b : AdeleRing (𝓞 ℚ) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∫ z, X.form (upperUnipotent3 a (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + b) z * h)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
      = ∫ z, X.form (upperUnipotent3 a b z * h)
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  have h1 : ∀ z : AdeleRing (𝓞 ℚ) ℚ,
      X.form (upperUnipotent3 a (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + b) z * h)
        = X.form (upperUnipotent3 a b z * h) := by
    intro z
    have := form_per X hX 0 q 0 a b z h
    simpa only [map_zero, zero_add, zero_mul, add_zero] using this
  simp_rw [h1]

private theorem integral_z (w : AdelicGL 3 (𝓞 ℚ) ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ) (c : ℂ) :
    (∫ z, X.form (upperUnipotent3 (-y) (-x) (x * y - z) * w) * c
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
      = ∫ z, X.form (upperUnipotent3 (-y) (-x) z * w) * c
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  have key := integral_pins_comp_sub D U gen
    (fun t => X.form (upperUnipotent3 (-y) (-x) t * w) * c) (fun q t => by simp only [form_per_z X hX])
    (x * y)
  simpa only using key

private theorem integral_y (hψn : ∀ q : ℚ, ψ (-algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q) = 1)
    (w : AdelicGL 3 (𝓞 ℚ) ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) :
    (∫ y, (∫ z, X.form (upperUnipotent3 (-y) (-x) z * w)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (x + y)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
      = ∫ y, (∫ z, X.form (upperUnipotent3 y (-x) z * w)
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(-x + y))
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  have hp : ∀ (q : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ),
      (∫ z, X.form (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + y) (-x) z * w)
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
          * ψ (-(-x + (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + y)))
        = (∫ z, X.form (upperUnipotent3 y (-x) z * w)
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(-x + y)) := by
    intro q y
    rw [integral_G1 X hX, show -(-x + (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + y))
        = -(-x + y) + -algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q by abel,
      AddChar.map_add_eq_mul, hψn, mul_one]
  have key := integral_pins_comp_sub D U gen
    (fun y => (∫ z, X.form (upperUnipotent3 y (-x) z * w)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(-x + y))) hp 0
  simpa only [zero_sub, neg_add_rev, neg_neg, add_comm] using key

private theorem integral_x (hψn : ∀ q : ℚ, ψ (-algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q) = 1)
    (w : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∫ x, ∫ y, (∫ z, X.form (upperUnipotent3 y (-x) z * w)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(-x + y))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
      = ∫ x, ∫ y, (∫ z, X.form (upperUnipotent3 y x z * w)
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(x + y))
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν
              ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
  have hp : ∀ (q : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ),
      (∫ y, (∫ z, X.form (upperUnipotent3 y (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) z * w)
          ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
          * ψ (-((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) + y))
              ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
        = ∫ y, (∫ z, X.form (upperUnipotent3 y x z * w)
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(x + y))
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
    intro q x
    have hψs : ∀ y : AdeleRing (𝓞 ℚ) ℚ,
        ψ (-((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) + y)) = ψ (-(x + y)) := by
      intro y
      rw [show -((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + x) + y)
          = -(x + y) + -algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q by abel,
        AddChar.map_add_eq_mul, hψn, mul_one]
    simp_rw [integral_G2 X hX, hψs]
  have key := integral_pins_comp_sub D U gen
    (fun x => ∫ y, (∫ z, X.form (upperUnipotent3 y x z * w)
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) * ψ (-(x + y))
        ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν) hp 0
  simpa only [zero_sub] using key

private theorem whittaker_eq_zero (q₀ : ℚ) (hq₀ : ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₀) ≠ 1)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) : X.whittaker h = 0 := by
  have h1 := hX.whittaker_law (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₀) 0 0 h
  have h2 : X.whittaker (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₀) 0 0 * h)
      = X.whittaker h := by
    rw [hX.whittaker_eq, hX.whittaker_eq]
    simp only [whittaker3]
    have h3 : ∀ x y z : AdeleRing (𝓞 ℚ) ℚ,
        X.form (upperUnipotent3 x y z
            * (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₀) 0 0 * h))
          = X.form (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₀ + x) y z * h) := by
      intro x y z
      rw [← mul_assoc, upperUnipotent3_mul_upperUnipotent3, add_comm x]
      simp only [add_zero, mul_zero]
    have h4 : ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
        (∫ z, X.form (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₀ + x) y z * h)
            * ψ (-(x + y))
            ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν)
          = ∫ z, X.form (upperUnipotent3 x y z * h) * ψ (-(x + y))
              ∂(productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)).ν := by
      intro x y
      rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const, integral_G1 X hX]
    simp_rw [h3, h4]
  rw [h2, add_zero] at h1
  have h5 : (ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₀) - 1) * X.whittaker h = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  exact (mul_eq_zero.mp h5).resolve_left (sub_ne_zero.mpr hq₀)

private theorem form_eq_zero (q₀ : ℚ) (hq₀ : ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q₀) ≠ 1)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) : X.form h = 0 := by
  have := hX.expansion h
  simp only [whittaker_eq_zero X hX q₀ hq₀] at this
  exact this.unique hasSum_zero

end FormLemmas

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (_hcont : Continuous X.form) :
    X.dualWhittaker = dualWhittakerFn3 X.whittaker := by
  funext g
  by_cases hψ : ∀ q : ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q) = 1
  ·

    have hψn : ∀ q : ℚ, ψ (-algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q) = 1 := by
      intro q
      rw [← map_neg (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))]
      exact hψ (-q)
    rw [hX.dualWhittaker_eq, dualWhittakerFn3_apply, hX.whittaker_eq]
    simp only [whittaker3, dualForm]
    simp_rw [form_conj X hX, AddChar.inv_apply, neg_neg]
    generalize longWeyl3 * transposeInv3 g = w
    simp_rw [integral_z X hX w, MeasureTheory.integral_mul_const]
    simp_rw [integral_y X hX hψn w]
    rw [integral_x X hX hψn w]
    refine (integral_integral_swap_box D U gen X.form _hcont ψ w).trans ?_
    simp only [add_comm]
  ·
    obtain ⟨q₀, hq₀⟩ := not_forall.mp hψ
    rw [hX.dualWhittaker_eq, dualWhittakerFn3_apply, whittaker_eq_zero X hX q₀ hq₀]
    simp [whittaker3, dualForm, form_eq_zero X hX q₀ hq₀]

end S_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn (solution)
