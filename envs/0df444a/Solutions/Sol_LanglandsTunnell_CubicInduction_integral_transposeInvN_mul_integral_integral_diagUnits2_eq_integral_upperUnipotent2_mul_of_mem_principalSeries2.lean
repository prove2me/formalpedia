-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1279c355-2c7c-5d31-9ffd-7c3752f4f849

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory LanglandsTunnell.TateLocal IsDedekindDomain NumberField Topology
open scoped NNReal ENNReal

noncomputable section

namespace LTSectionTransfer

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (v : HeightOneSpectrum (𝓞 ℚ))

scoped instance borelSpace_units_adic : BorelSpace (v.adicCompletion ℚ)ˣ := borelSpace_units

scoped instance measurableMul_units_adic : MeasurableMul (v.adicCompletion ℚ)ˣ := by infer_instance

scoped instance measurableInv_units_adic : MeasurableInv (v.adicCompletion ℚ)ˣ := by infer_instance

scoped instance secondCountable_units_adic : SecondCountableTopology (v.adicCompletion ℚ)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : v.adicCompletion ℚ)).NeBot := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hlt : ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 ℚ) ℚ x)‖ < 1 :=
    (NumberField.FinitePlace.norm_lt_one_iff_mem ℚ v x).mpr hx
  have hne : NumberField.FinitePlace.embedding v (algebraMap (𝓞 ℚ) ℚ x) ≠ 0 := by
    intro h
    apply hx0
    have h1 : algebraMap (𝓞 ℚ) ℚ x = 0 := (RingHom.injective _) (by rw [h, map_zero])
    exact (FaithfulSMul.algebraMap_injective (𝓞 ℚ) ℚ) (by rw [h1, map_zero])
  letI : NontriviallyNormedField (v.adicCompletion ℚ) :=
    NontriviallyNormedField.ofNormNeOne ⟨_, hne, hlt.ne⟩
  exact NormedField.nhdsNE_neBot 0

theorem measure_zero_singleton (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure] :
    ν {0} = 0 := by
  haveI := nhdsNE_zero_neBot v
  haveI : NullSingletonClass ν := Measure.IsAddHaarMeasure.nullSingletonClass ν
  exact measure_singleton 0

def unitsMeasure (ν : Measure (v.adicCompletion ℚ)) : Measure (v.adicCompletion ℚ)ˣ :=
  Measure.comap Units.val (mulMeasure ν)

scoped instance isHaarMeasure_unitsMeasure (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure] :
    (unitsMeasure v ν).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure ℚ v ν

scoped instance isInvInvariant_unitsMeasure (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure] :
    (unitsMeasure v ν).IsInvInvariant := by
  infer_instance

theorem modulus_eq_nnnorm (x : v.adicCompletion ℚ) : modulus x = ‖x‖₊ :=
  modulus_adicCompletion_eq_nnnorm ℚ v x

theorem measurable_modulus : Measurable (fun x : v.adicCompletion ℚ => modulus x) := by
  have : (fun x : v.adicCompletion ℚ => modulus x) = fun x => ‖x‖₊ := funext (modulus_eq_nnnorm v)
  rw [this]
  exact measurable_nnnorm

theorem modulus_inv (x : v.adicCompletion ℚ) : modulus x⁻¹ = (modulus x)⁻¹ := by
  rw [modulus_eq_nnnorm, modulus_eq_nnnorm, nnnorm_inv]

theorem modulus_neg (x : v.adicCompletion ℚ) : modulus (-x) = modulus x := by
  rw [modulus_eq_nnnorm, modulus_eq_nnnorm, nnnorm_neg]

theorem measurableEmbedding_val :
    MeasurableEmbedding (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) where
  injective := Units.val_injective
  measurable := comap_measurable Units.val
  measurableSet_image' := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have : Units.val '' (Units.val ⁻¹' t) = t ∩ {x : v.adicCompletion ℚ | x ≠ 0} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨hu, u.ne_zero⟩
      · rintro ⟨hx, hx0⟩; exact ⟨Units.mk0 x hx0, hx, rfl⟩
    rw [this]
    exact ht.inter (measurableSet_singleton (0 : v.adicCompletion ℚ)).compl

theorem range_val : Set.range (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩; exact u.ne_zero
  · intro hx; exact ⟨Units.mk0 x hx, rfl⟩

theorem mulMeasure_restrict (ν : Measure (v.adicCompletion ℚ)) :
    (mulMeasure ν).restrict {0}ᶜ = mulMeasure ν := by
  have hm : MeasurableSet ({0}ᶜ : Set (v.adicCompletion ℚ)) := (measurableSet_singleton _).compl
  unfold mulMeasure
  rw [restrict_withDensity hm, Measure.restrict_restrict hm, Set.inter_self]

theorem integral_mulMeasure_eq (ν : Measure (v.adicCompletion ℚ)) (H : v.adicCompletion ℚ → ℂ) :
    ∫ x, H x ∂(mulMeasure ν) = ∫ u, H (u : v.adicCompletion ℚ) ∂(unitsMeasure v ν) := by
  have hmap : Measure.map Units.val (unitsMeasure v ν) = mulMeasure ν := by
    rw [unitsMeasure, (measurableEmbedding_val v).map_comap, range_val, mulMeasure_restrict]
  rw [← (measurableEmbedding_val v).integral_map, hmap]

theorem integral_eq_integral_modulus_smul (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
    (G : v.adicCompletion ℚ → ℂ) :
    ∫ y, G y ∂ν = ∫ x, (modulus x : ℝ≥0) • G x ∂(mulMeasure ν) := by
  have hm : MeasurableSet ({0}ᶜ : Set (v.adicCompletion ℚ)) := (measurableSet_singleton _).compl
  have hmeas : Measurable (fun x : v.adicCompletion ℚ => ((modulus x : ℝ≥0) : ℝ≥0∞)) :=
    (measurable_modulus v).coe_nnreal_ennreal
  have hmeas' : Measurable (fun x : v.adicCompletion ℚ => ((modulus x : ℝ≥0) : ℝ≥0∞)⁻¹) := hmeas.inv
  have hν : ν = (mulMeasure ν).withDensity (fun x => ((modulus x : ℝ≥0) : ℝ≥0∞)) := by
    unfold mulMeasure
    rw [← withDensity_mul _ hmeas' hmeas]
    have hae : ((fun x : v.adicCompletion ℚ => ((modulus x : ℝ≥0) : ℝ≥0∞)⁻¹) *
        fun x => ((modulus x : ℝ≥0) : ℝ≥0∞)) =ᵐ[ν.restrict {0}ᶜ] 1 := by
      filter_upwards [ae_restrict_mem hm] with x hx
      have hx0 : x ≠ 0 := hx
      have hne : ((modulus x : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (modulus_ne_zero hx0)
      simp only [Pi.mul_apply, Pi.one_apply]
      exact ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top
    rw [withDensity_congr_ae hae, withDensity_one]
    exact (Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not, Set.setOf_eq_eq_singleton]
      exact measure_zero_singleton v ν)).symm
  conv_lhs => rw [hν]
  exact integral_withDensity_eq_integral_smul (measurable_modulus v) G

theorem integral_units_neg_inv (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
    (H : (v.adicCompletion ℚ)ˣ → ℂ) :
    ∫ u, H (-u⁻¹) ∂(unitsMeasure v ν) = ∫ u, H u ∂(unitsMeasure v ν) := by
  set θ : (v.adicCompletion ℚ)ˣ ≃ᵐ (v.adicCompletion ℚ)ˣ :=
    (MeasurableEquiv.inv (v.adicCompletion ℚ)ˣ).trans (MeasurableEquiv.mulLeft (-1)) with hθ
  have hpres : MeasurePreserving θ (unitsMeasure v ν) (unitsMeasure v ν) :=
    (Measure.measurePreserving_inv (unitsMeasure v ν)).trans (measurePreserving_mul_left _ (-1))
  have h := hpres.integral_comp' H
  have hθ' : ∀ u, θ u = -u⁻¹ := fun u => by
    simp [hθ, MeasurableEquiv.trans_apply, MeasurableEquiv.inv, MeasurableEquiv.coe_mulLeft]
  simp only [hθ'] at h
  exact h

theorem integral_comp_neg_inv (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
    (G : v.adicCompletion ℚ → ℂ) :
    ∫ y, G y ∂ν = ∫ u, (((modulus u : ℝ) : ℂ)⁻¹ ^ 2) * G (-u⁻¹) ∂ν := by
  have key : ∫ y, G y ∂ν = ∫ u, ((modulus u)⁻¹ ^ 2 : ℝ≥0) • G (-u⁻¹) ∂ν := by
    rw [integral_eq_integral_modulus_smul v ν G, integral_mulMeasure_eq,
      ← integral_units_neg_inv v ν (fun u => (modulus (u : v.adicCompletion ℚ) : ℝ≥0) • G u),
      integral_eq_integral_modulus_smul v ν, integral_mulMeasure_eq]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [Units.val_neg, Units.val_inv_eq_inv_val, modulus_neg, modulus_inv, smul_smul]
    congr 1
    have h0 : modulus (u : v.adicCompletion ℚ) ≠ 0 := modulus_ne_zero u.ne_zero
    rw [sq, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
  rw [key]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  dsimp only
  rw [NNReal.smul_def, Complex.real_smul]
  push_cast
  ring

section GL2

open LanglandsTunnell.CubicInduction

variable {v}

def lowerUnipotent2 (c : v.adicCompletion ℚ) : LocalGL2 v where
  val := !![1, 0; c, 1]
  inv := !![1, 0; -c, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem lowerUnipotent2_coe (c : v.adicCompletion ℚ) :
    ((lowerUnipotent2 c : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, 0; c, 1] := rfl

theorem coe_inv_upperUnipotent2 (y : v.adicCompletion ℚ) :
    (((upperUnipotent2 v y)⁻¹ : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, -y; 0, 1] := rfl

variable (w₀p : LocalGL2 v) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0])
include hw₀p

theorem w₀p_mul_self : w₀p * w₀p = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, hw₀p, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem w₀p_inv : w₀p⁻¹ = w₀p := inv_eq_of_mul_eq_one_right (w₀p_mul_self w₀p hw₀p)

theorem coe_inv_w₀p : ((w₀p⁻¹ : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0] := by
  rw [w₀p_inv w₀p hw₀p, hw₀p]

theorem w₀p_mul_transposeInvN (y : v.adicCompletion ℚ) :
    w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * upperUnipotent2 v y) = lowerUnipotent2 (-y) := by
  refine Units.ext ?_
  rw [Units.val_mul, AutomorphicForm.coe_transposeInvN, _root_.mul_inv_rev, Units.val_mul, coe_inv_upperUnipotent2,
    coe_inv_w₀p w₀p hw₀p, hw₀p, lowerUnipotent2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem lowerUnipotent2_eq (u : (v.adicCompletion ℚ)ˣ) :
    lowerUnipotent2 (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) =
      upperUnipotent2 v (u : v.adicCompletion ℚ) *
        (diagonal2 v ![-u, u⁻¹] * (w₀p * upperUnipotent2 v (u : v.adicCompletion ℚ))) := by
  refine Units.ext ?_
  simp only [Units.val_mul, lowerUnipotent2_coe, upperUnipotent2_coe, diagonal2_coe, hw₀p]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem section_lower (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (f : LocalGL2 v → ℂ)
    (hf : f ∈ principalSeries2 v χ) (u : (v.adicCompletion ℚ)ˣ) :
    f (lowerUnipotent2 (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ))) =
      ((χ 0 (-1) : ℂˣ) : ℂ) * ((χ 0 u : ℂˣ) : ℂ) * ((χ 1 u : ℂˣ) : ℂ)⁻¹ * ((‖(u : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
        f (w₀p * upperUnipotent2 v (u : v.adicCompletion ℚ)) := by
  obtain ⟨-, hN, hT⟩ := mem_principalSeries2_iff.mp hf
  rw [lowerUnipotent2_eq w₀p hw₀p, hN, hT]
  have hχ : torusChar2 v χ ![-u, u⁻¹] = ((χ 0 (-1) : ℂˣ) : ℂ) * ((χ 0 u : ℂˣ) : ℂ) * ((χ 1 u : ℂˣ) : ℂ)⁻¹ := by
    simp only [torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (-u : (v.adicCompletion ℚ)ˣ) = -1 * u by rw [neg_one_mul], map_mul, map_inv, Units.val_mul,
      Units.val_inv_eq_inv_val]
  have hm : halfModulus2 v ![-u, u⁻¹] = ((‖(u : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
    simp only [halfModulus2, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_neg,
      Units.val_inv_eq_inv_val, norm_neg, norm_inv, div_inv_eq_mul]
    rw [Real.sqrt_mul_self (norm_nonneg _)]
  rw [hχ, hm]

end GL2

end LTSectionTransfer
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2.LTSectionTransfer"

open LanglandsTunnell.CubicInduction LTSectionTransfer

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (W : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : LocalGL3 p),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (f : LocalGL2 p → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀p : LocalGL2 p) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) :
    letI := localBorel ℚ p
    ∀ (μ : Measure (p.adicCompletion ℚ)ˣ) [μ.IsMulLeftInvariant]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∫ y : p.adicCompletion ℚ,
          f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * upperUnipotent2 p y)) *
            (∫ a : (p.adicCompletion ℚ)ˣ, ∫ t : (p.adicCompletion ℚ)ˣ,
              ((((χ 1) a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
                ((((χ 0) t : ℂˣ) : ℂ) * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
              W (iotaGL (diagUnits2 (t * a) a) *
                (longWeyl3 * upperUnipotent3 0 0 (-y) * longWeyl3 * weylPrime3)) ∂μ ∂μ) ∂ν) =
        ∫ y : p.adicCompletion ℚ,
          f (w₀p * upperUnipotent2 p y) *
            (∫ a : (p.adicCompletion ℚ)ˣ, ∫ t : (p.adicCompletion ℚ)ˣ,
              ((((χ 1) a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
                ((((χ 0) t : ℂˣ) : ℂ) * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
              W (iotaGL (diagUnits2 (t * a) a) *
                (longWeyl3 * upperUnipotent3 0 0 y * weylPrime3)) ∂μ ∂μ) ∂ν := by
  intro μ _ ν _

  set L : (p.adicCompletion ℚ) → ℂ := fun c =>
    ∫ a : (p.adicCompletion ℚ)ˣ, ∫ t : (p.adicCompletion ℚ)ˣ,
      ((((χ 1) a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
        ((((χ 0) t : ℂˣ) : ℂ) * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
      W (iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 c * weylPrime3)) ∂μ ∂μ with hL
  set R : (p.adicCompletion ℚ) → ℂ := fun c =>
    ∫ a : (p.adicCompletion ℚ)ˣ, ∫ t : (p.adicCompletion ℚ)ˣ,
      ((((χ 1) a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
        ((((χ 0) t : ℂˣ) : ℂ) * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
      W (iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 c * longWeyl3 * weylPrime3)) ∂μ ∂μ with hR

  have hC : ∀ u : (p.adicCompletion ℚ)ˣ,
      L (u : p.adicCompletion ℚ) =
        ((χ 0 (-1) : ℂˣ) : ℂ) * ((χ 0 u : ℂˣ) : ℂ) * ((χ 1 u : ℂˣ) : ℂ)⁻¹ *
          (((modulus (u : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ * R (((u⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) := by
    intro u
    simp only [hL, hR]
    exact integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central μ ψ W hW ω hω (χ 0) (χ 1) s u

  change (∫ y : p.adicCompletion ℚ,
      f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * upperUnipotent2 p y)) * R (-y) ∂ν) =
    ∫ y : p.adicCompletion ℚ, f (w₀p * upperUnipotent2 p y) * L y ∂ν

  rw [integral_comp_neg_inv p ν (fun y => f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * upperUnipotent2 p y)) * R (-y))]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ u ∂ν, u ≠ (0 : p.adicCompletion ℚ) := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_zero_singleton p ν
  filter_upwards [hae] with x hx

  set u : (p.adicCompletion ℚ)ˣ := Units.mk0 x hx with hu
  have hxu : x = (u : p.adicCompletion ℚ) := by rw [hu, Units.val_mk0]
  simp only [neg_neg]
  rw [hxu, w₀p_mul_transposeInvN w₀p hw₀p, neg_neg, ← Units.val_inv_eq_inv_val,
    section_lower w₀p hw₀p χ f hf u, hC u]

  have hmod : ((modulus (u : p.adicCompletion ℚ) : ℝ) : ℂ) = ((‖(u : p.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
    rw [modulus_eq_nnnorm p, coe_nnnorm]
  have hn0 : ((‖(u : p.adicCompletion ℚ)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr u.ne_zero)
  rw [hmod]
  field_simp

end
end S_LanglandsTunnell_CubicInduction_integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2 (solution)
