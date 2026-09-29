-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fd7b07e5-e030-5b75-a1c1-4356ed7bbcad

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Mathlib
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Topology
open scoped ENNReal NNReal Pointwise

namespace BigCell

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "Fˣ" => ((HeightOneSpectrum.adicCompletion ℚ p)ˣ)
local notation "Mat" => (Fin 2 → Fin 2 → (HeightOneSpectrum.adicCompletion ℚ p))

theorem modulus_eq_nnnorm (x : F) : modulus x = ‖x‖₊ :=
  LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x

theorem continuous_modulus : Continuous fun x : F => modulus x := by
  have : (fun x : F => modulus x) = fun x : F => ‖x‖₊ := funext (modulus_eq_nnnorm p)
  rw [this]; exact continuous_nnnorm

theorem modulus_units_ne_zero (u : Fˣ) : modulus (u : F) ≠ 0 := modulus_ne_zero u.ne_zero

theorem modulusE_units_ne_zero (u : Fˣ) : (modulus (u : F) : ℝ≥0∞) ≠ 0 :=
  ENNReal.coe_ne_zero.mpr (modulus_units_ne_zero p u)

theorem modulusE_units_ne_top (u : Fˣ) : (modulus (u : F) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top

theorem modulus_units_inv (u : Fˣ) : modulus (((u⁻¹ : Fˣ)) : F) = (modulus (u : F))⁻¹ := by
  have h : modulus (((u⁻¹ : Fˣ)) : F) * modulus (u : F) = 1 := by
    rw [← modulus_mul, Units.inv_mul, modulus_one]
  exact eq_inv_of_mul_eq_one_left h

theorem modulusE_units_inv (u : Fˣ) : (modulus (((u⁻¹ : Fˣ)) : F) : ℝ≥0∞) = (modulus (u : F) : ℝ≥0∞)⁻¹ := by
  rw [modulus_units_inv, ENNReal.coe_inv (modulus_units_ne_zero p u)]

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

theorem smul_set_eq_preimage {c : F} (hc : c ≠ 0) (T : Set F) :
    c • T = (fun y => c⁻¹ * y) ⁻¹' T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

section Haar

variable [MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ p)] [BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)]

theorem map_mul_left_eq_smul (ν : Measure F) [ν.IsAddHaarMeasure] (u : Fˣ) :
    ν.map (fun x : F => (u : F) * x) = ((modulus (u : F) : ℝ≥0∞))⁻¹ • ν := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : F => (u : F) * x) ⁻¹' s = ((u⁻¹ : Fˣ) : F) • s := by
    rw [smul_set_eq_preimage p (u⁻¹).ne_zero, Units.val_inv_eq_inv_val, inv_inv]
  rw [hpre]
  have h := distribHaarChar_mul ν (u⁻¹) s
  rw [show ((u⁻¹ : Fˣ) • s : Set F) = ((u⁻¹ : Fˣ) : F) • s from rfl] at h
  rw [← h, map_inv, modulus_coe_units, ENNReal.coe_inv (distribHaarChar_pos).ne']

theorem lintegral_comp_mul_units (ν : Measure F) [ν.IsAddHaarMeasure] (a : Fˣ) (H : F → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ z, H (z * (a : F)) ∂ν = ((modulus (a : F) : ℝ≥0∞))⁻¹ * ∫⁻ t, H t ∂ν := by
  have h1 : (fun z : F => H (z * (a : F))) = fun z => H ((a : F) * z) := by
    funext z; rw [mul_comm]
  rw [h1, ← lintegral_map hH (measurable_const_mul _), map_mul_left_eq_smul p ν a, lintegral_smul_measure, smul_eq_mul]

theorem lintegral_units_eq (ν : Measure F) (G : F → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ b, G ((b : Fˣ) : F) ∂(Measure.comap Units.val (mulMeasure ν)) =
      ∫⁻ t, ({0}ᶜ : Set F).indicator (fun t => ((modulus t : ℝ≥0∞))⁻¹ * G t) t ∂ν := by
  haveI : BorelSpace Fˣ := borelSpace_units
  have hme : MeasurableEmbedding (Units.val : Fˣ → F) :=
    (Units.isEmbedding_val₀ (G₀ := F)).measurableEmbedding ?_
  swap
  ·
    have : Set.range (Units.val : Fˣ → F) = {0}ᶜ := by
      ext x
      simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
    rw [this]; exact isOpen_compl_singleton.measurableSet
  have hrange : Set.range (Units.val : Fˣ → F) = ({0}ᶜ : Set F) := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  have hmeas0 : MeasurableSet ({0}ᶜ : Set F) := isOpen_compl_singleton.measurableSet
  calc ∫⁻ b, G ((b : Fˣ) : F) ∂(Measure.comap Units.val (mulMeasure ν))
      = ∫⁻ t, G t ∂((Measure.comap Units.val (mulMeasure ν)).map Units.val) :=
        (lintegral_map hG hme.measurable).symm
    _ = ∫⁻ t, G t ∂((mulMeasure ν).restrict ({0}ᶜ : Set F)) := by rw [hme.map_comap, hrange]
    _ = ∫⁻ t, G t ∂((ν.restrict ({0}ᶜ : Set F)).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹) := by
        rw [show mulMeasure ν = (ν.restrict ({0}ᶜ : Set F)).withDensity (fun x => ((modulus x : ℝ≥0∞))⁻¹) from rfl,
          restrict_withDensity hmeas0, Measure.restrict_restrict hmeas0, Set.inter_self]
    _ = ∫⁻ t, ((modulus t : ℝ≥0∞))⁻¹ * G t ∂(ν.restrict ({0}ᶜ : Set F)) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ ?_ hG]
        · rfl
        · exact ((continuous_modulus p).measurable.coe_nnreal_ennreal).inv
    _ = ∫⁻ t, ({0}ᶜ : Set F).indicator (fun t => ((modulus t : ℝ≥0∞))⁻¹ * G t) t ∂ν := by
        rw [← lintegral_indicator hmeas0]

theorem lintegral_comp_add_left (ν : Measure F) [ν.IsAddHaarMeasure] (c : F) (H : F → ℝ≥0∞) :
    ∫⁻ t, H (c + t) ∂ν = ∫⁻ t, H t ∂ν := lintegral_add_left_eq_self _ c

theorem norm_eq_zpow_of_valued {x : F} {k : ℤ} (hx : Valued.v x = WithZero.exp k) :
    ‖x‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ k := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp k) = ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem measure_zero_singleton (ν : Measure F) [ν.IsAddHaarMeasure] : ν {0} = 0 := by
  set u : Fˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hu
  have hvu : Valued.v (u : F) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  have hN1 : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
    have h2 : 2 ≤ Ideal.absNorm p.asIdeal := by
      have hne1 : Ideal.absNorm p.asIdeal ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
      have hne0 : Ideal.absNorm p.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
      omega
    exact_mod_cast h2
  have hmu : (modulus (u : F) : ℝ≥0∞) ≠ 1 := by
    intro h
    have h' : ‖(u : F)‖ = 1 := by
      have := congrArg (fun t : ℝ≥0∞ => t.toNNReal) h
      simp only [ENNReal.toNNReal_coe, ENNReal.toNNReal_one] at this
      rw [modulus_eq_nnnorm] at this
      have := congrArg (fun t : ℝ≥0 => (t : ℝ)) this
      simpa using this
    rw [norm_eq_zpow_of_valued p hvu, zpow_neg_one] at h'
    have : (Ideal.absNorm p.asIdeal : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hN1
    exact absurd h' this.ne
  have hpre : (fun x : F => (u : F) * x) ⁻¹' ({0} : Set F) = {0} := by
    ext x; simp [u.ne_zero]
  have h1 : ν {0} = ((modulus (u : F) : ℝ≥0∞))⁻¹ * ν {0} := by
    have := congrArg (fun μ : Measure F => μ {0}) (map_mul_left_eq_smul p ν u)
    simp only [Measure.smul_apply, smul_eq_mul] at this
    rwa [Measure.map_apply (measurable_const_mul _) (measurableSet_singleton 0), hpre] at this
  have hfin : ν {0} ≠ ⊤ := (isCompact_singleton.measure_lt_top).ne
  by_contra h0
  have h2 : (1 : ℝ≥0∞) * ν {0} = ((modulus (u : F) : ℝ≥0∞))⁻¹ * ν {0} := by rw [one_mul]; exact h1
  have h3 : (1 : ℝ≥0∞) = ((modulus (u : F) : ℝ≥0∞))⁻¹ :=
    (ENNReal.mul_left_inj h0 hfin).mp h2
  exact hmu (by rw [← inv_inv ((modulus (u : F) : ℝ≥0∞)), ← h3, inv_one])

end Haar

section PiPi

theorem lintegral_pi_fin_two {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (H : (Fin 2 → α) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ r, H r ∂(Measure.pi fun _ : Fin 2 => μ) = ∫⁻ x, ∫⁻ y, H ![x, y] ∂μ ∂μ := by
  have hmp : MeasurePreserving (MeasurableEquiv.piFinTwo fun _ : Fin 2 => α) (Measure.pi fun _ : Fin 2 => μ) (μ.prod μ) :=
    measurePreserving_piFinTwo _
  have h1 : ∫⁻ r, H r ∂(Measure.pi fun _ : Fin 2 => μ) =
      ∫⁻ q, H ((MeasurableEquiv.piFinTwo fun _ : Fin 2 => α).symm q) ∂(μ.prod μ) := by
    rw [← hmp.map_eq, lintegral_map_equiv]
    simp only [MeasurableEquiv.symm_apply_apply]
  rw [h1, lintegral_prod (fun q => H ((MeasurableEquiv.piFinTwo fun _ : Fin 2 => α).symm q))
    (hH.comp (MeasurableEquiv.piFinTwo fun _ : Fin 2 => α).symm.measurable).aemeasurable]
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  rfl

theorem measurable_vecCons2 {α : Type*} [MeasurableSpace α] :
    Measurable fun q : α × α => (![q.1, q.2] : Fin 2 → α) :=
  measurable_pi_iff.mpr fun i => by fin_cases i <;> simp <;> fun_prop

end PiPi

section Key

variable [MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ p)] [BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)]

theorem measurable_modulusE : Measurable fun x : F => (modulus x : ℝ≥0∞) :=
  (continuous_modulus p).measurable.coe_nnreal_ennreal

def M4 (t y u s : F) : Mat := ![![t, y], ![u, s]]

theorem M4_eq (t y u s : F) : (M4 p t y u s : Mat) = (!![t, y; u, s] : Matrix (Fin 2) (Fin 2) F) := rfl

theorem measurable_M4 : Measurable fun q : F × F × F × F => M4 p q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [M4] <;> fun_prop

theorem lintegral_comp_mul_units_left (ν : Measure F) [ν.IsAddHaarMeasure] (a : Fˣ) (H : F → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ z, H ((a : F) * z) ∂ν = ((modulus (a : F) : ℝ≥0∞))⁻¹ * ∫⁻ t, H t ∂ν := by
  rw [← lintegral_map hH (measurable_const_mul _), map_mul_left_eq_smul p ν a, lintegral_smul_measure, smul_eq_mul]

theorem lintegral_pi_pi (ν : Measure F) [SigmaFinite ν] (H : Mat → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ X, H X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => ν) =
      ∫⁻ t, ∫⁻ y, ∫⁻ u, ∫⁻ s, H (M4 p t y u s) ∂ν ∂ν ∂ν ∂ν := by
  rw [lintegral_pi_fin_two (Measure.pi fun _ : Fin 2 => ν) H hH]
  have hrow2 : ∀ r₀ : Fin 2 → F, Measurable fun r₁ : Fin 2 → F => H ![r₀, r₁] := fun r₀ =>
    hH.comp (measurable_pi_iff.mpr fun i => by fin_cases i <;> simp <;> fun_prop)
  have h2 : ∀ r₀ : Fin 2 → F, ∫⁻ r₁, H ![r₀, r₁] ∂(Measure.pi fun _ : Fin 2 => ν) = ∫⁻ u, ∫⁻ s, H ![r₀, ![u, s]] ∂ν ∂ν :=
    fun r₀ => lintegral_pi_fin_two ν _ (hrow2 r₀)
  simp_rw [h2]
  have hmeasUS : Measurable fun q : (Fin 2 → F) × F × F => H ![q.1, ![q.2.1, q.2.2]] :=
    hH.comp (measurable_pi_iff.mpr fun i => by
      fin_cases i
      · simp; fun_prop
      · simp; exact measurable_pi_iff.mpr fun j => by fin_cases j <;> simp <;> fun_prop)
  have hG : Measurable fun r₀ : Fin 2 → F => ∫⁻ u, ∫⁻ s, H ![r₀, ![u, s]] ∂ν ∂ν := by
    refine Measurable.lintegral_prod_right' (f := fun q : (Fin 2 → F) × F => ∫⁻ s, H ![q.1, ![q.2, s]] ∂ν) ?_
    exact Measurable.lintegral_prod_right' (f := fun q : ((Fin 2 → F) × F) × F => H ![q.1.1, ![q.1.2, q.2]])
      (hmeasUS.comp ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  rw [lintegral_pi_fin_two ν _ hG]
  rfl

def mE (t : F) : ℝ≥0∞ := (modulus t : ℝ≥0∞)

theorem measurable_mE : Measurable (mE p) := measurable_modulusE p
theorem mE_ne_zero {t : F} (ht : t ≠ 0) : mE p t ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero ht)
theorem mE_ne_top (t : F) : mE p t ≠ ⊤ := ENNReal.coe_ne_top
theorem mE_mul (s t : F) : mE p (s * t) = mE p s * mE p t := by simp only [mE, modulus_mul, ENNReal.coe_mul]
theorem mE_units_inv (u : Fˣ) : mE p (((u⁻¹ : Fˣ)) : F) = (mE p (u : F))⁻¹ := modulusE_units_inv p u
theorem mE_inv (a : Fˣ) : mE p (((a : F))⁻¹) = (mE p (a : F))⁻¹ := by
  rw [← Units.val_inv_eq_inv_val]; exact mE_units_inv p a

theorem measurable_M4_of {α : Type*} [MeasurableSpace α] {t y u s : α → F}
    (ht : Measurable t) (hy : Measurable y) (hu : Measurable u) (hs : Measurable s) :
    Measurable fun v => M4 p (t v) (y v) (u v) (s v) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;> simpa [M4]

theorem mE_neg (t : F) : mE p (-t) = mE p t := by
  simp only [mE, modulus_eq_nnnorm, nnnorm_neg]

theorem modulusE_neg (t : F) : (modulus (-t) : ℝ≥0∞) = (modulus t : ℝ≥0∞) := by
  rw [modulus_eq_nnnorm, modulus_eq_nnnorm, nnnorm_neg]

theorem mE_units_ne_zero (u : Fˣ) : mE p (u : F) ≠ 0 := mE_ne_zero p u.ne_zero

variable (ν : Measure (HeightOneSpectrum.adicCompletion ℚ p)) [ν.IsAddHaarMeasure] [SigmaFinite ν]

theorem stepA (f : Mat → ℝ≥0∞) (hf : Measurable f) (b : Fˣ) (x y : F) :
    ∫⁻ a : Fˣ, mE p (b : F) ^ 4 * mE p (a : F) *
        f (M4 p ((b : F) * x) ((b : F) * (x * y + (a : F))) (-(b : F)) (-((b : F) * y)))
        ∂(Measure.comap Units.val (mulMeasure ν)) =
      mE p (b : F) ^ 4 * ((mE p (b : F))⁻¹ *
        ∫⁻ t, f (M4 p ((b : F) * x) t (-(b : F)) (-((b : F) * y))) ∂ν) := by
  have hν0 : ν {0} = 0 := measure_zero_singleton p ν
  have h4top : mE p (b : F) ^ 4 ≠ ⊤ := ENNReal.pow_ne_top (mE_ne_top p _)
  have hmeasG0 : Measurable fun t : F => mE p t * f (M4 p ((b : F) * x) ((b : F) * (x * y + t)) (-(b : F)) (-((b : F) * y))) :=
    (measurable_mE p).mul (hf.comp (measurable_M4_of p measurable_const
      (measurable_const.mul (measurable_const.add measurable_id)) measurable_const measurable_const))
  have hmeasH : Measurable fun t : F => f (M4 p ((b : F) * x) ((b : F) * x * y + t) (-(b : F)) (-((b : F) * y))) :=
    hf.comp (measurable_M4_of p measurable_const (measurable_const.add measurable_id) measurable_const measurable_const)
  have hassoc : ∀ a : Fˣ, mE p (b : F) ^ 4 * mE p (a : F) *
        f (M4 p ((b : F) * x) ((b : F) * (x * y + (a : F))) (-(b : F)) (-((b : F) * y))) =
      mE p (b : F) ^ 4 * (mE p (a : F) *
        f (M4 p ((b : F) * x) ((b : F) * (x * y + (a : F))) (-(b : F)) (-((b : F) * y)))) := fun a => mul_assoc _ _ _
  rw [lintegral_congr hassoc, lintegral_const_mul' _ _ h4top]
  congr 1
  calc ∫⁻ a : Fˣ, mE p (a : F) * f (M4 p ((b : F) * x) ((b : F) * (x * y + (a : F))) (-(b : F)) (-((b : F) * y)))
          ∂(Measure.comap Units.val (mulMeasure ν))
      = ∫⁻ t, ({0}ᶜ : Set F).indicator
            (fun t => (mE p t)⁻¹ * (mE p t * f (M4 p ((b : F) * x) ((b : F) * (x * y + t)) (-(b : F)) (-((b : F) * y))))) t ∂ν := by
          rw [lintegral_units_eq p ν _ hmeasG0]; rfl
    _ = ∫⁻ t, f (M4 p ((b : F) * x) ((b : F) * x * y + (b : F) * t) (-(b : F)) (-((b : F) * y))) ∂ν := by
          refine lintegral_congr_ae ?_
          have hae : ∀ᵐ t ∂ν, t ∈ ({0}ᶜ : Set F) := compl_mem_ae_iff.mpr hν0
          filter_upwards [hae] with t ht
          have ht0 : t ≠ 0 := ht
          rw [Set.indicator_of_mem ht, ← mul_assoc, ENNReal.inv_mul_cancel (mE_ne_zero p ht0) (mE_ne_top p t), one_mul,
            mul_add, ← mul_assoc]
    _ = (mE p (b : F))⁻¹ * ∫⁻ t, f (M4 p ((b : F) * x) ((b : F) * x * y + t) (-(b : F)) (-((b : F) * y))) ∂ν :=
          lintegral_comp_mul_units_left p ν b _ hmeasH
    _ = (mE p (b : F))⁻¹ * ∫⁻ t, f (M4 p ((b : F) * x) t (-(b : F)) (-((b : F) * y))) ∂ν := by
          rw [lintegral_add_left_eq_self (μ := ν)
            (fun t => f (M4 p ((b : F) * x) t (-(b : F)) (-((b : F) * y)))) ((b : F) * x * y)]

theorem stepS (f : Mat → ℝ≥0∞) (hf : Measurable f) (b : Fˣ) (x : F) (C : ℝ≥0∞) (hC : C ≠ ⊤) :
    ∫⁻ y, C * ∫⁻ t, f (M4 p ((b : F) * x) t (-(b : F)) (-((b : F) * y))) ∂ν ∂ν =
      C * ((mE p (b : F))⁻¹ * ∫⁻ s, ∫⁻ t, f (M4 p ((b : F) * x) t (-(b : F)) s) ∂ν ∂ν) := by
  have hΦ : Measurable fun s : F => ∫⁻ t, f (M4 p ((b : F) * x) t (-(b : F)) s) ∂ν := by
    have hin : Measurable fun v : F × F => f (M4 p ((b : F) * x) v.2 (-(b : F)) v.1) :=
      hf.comp (measurable_M4_of p measurable_const measurable_snd measurable_const measurable_fst)
    exact hin.lintegral_prod_right'
  rw [lintegral_const_mul' _ _ hC]
  congr 1
  have hre : ∀ y : F, -((b : F) * y) = (((-b : Fˣ)) : F) * y := fun y => by rw [Units.val_neg, neg_mul]
  simp_rw [hre]
  rw [lintegral_comp_mul_units_left p ν (-b) _ hΦ, Units.val_neg, modulusE_neg]
  rfl

theorem stepT (f : Mat → ℝ≥0∞) (hf : Measurable f) (b : Fˣ) (C : ℝ≥0∞) (hC : C ≠ ⊤) :
    ∫⁻ x, C * ∫⁻ s, ∫⁻ t, f (M4 p ((b : F) * x) t (-(b : F)) s) ∂ν ∂ν ∂ν =
      C * ((mE p (b : F))⁻¹ * ∫⁻ r, ∫⁻ s, ∫⁻ t, f (M4 p r t (-(b : F)) s) ∂ν ∂ν ∂ν) := by
  have hΨ : Measurable fun r : F => ∫⁻ s, ∫⁻ t, f (M4 p r t (-(b : F)) s) ∂ν ∂ν := by
    have hin : Measurable fun v : (F × F) × F => f (M4 p v.1.1 v.2 (-(b : F)) v.1.2) :=
      hf.comp (measurable_M4_of p (measurable_fst.comp measurable_fst) measurable_snd measurable_const
        (measurable_snd.comp measurable_fst))
    exact hin.lintegral_prod_right'.lintegral_prod_right'
  rw [lintegral_const_mul' _ _ hC]
  congr 1
  exact lintegral_comp_mul_units_left p ν b _ hΨ

theorem stepB (K : F → ℝ≥0∞) (hK : Measurable K) :
    ∫⁻ b : Fˣ, mE p (b : F) * K (-(b : F)) ∂(Measure.comap Units.val (mulMeasure ν)) = ∫⁻ u, K u ∂ν := by
  have hν0 : ν {0} = 0 := measure_zero_singleton p ν
  have hKn : Measurable fun u : F => K (-u) := hK.comp measurable_neg
  calc ∫⁻ b : Fˣ, mE p (b : F) * K (-(b : F)) ∂(Measure.comap Units.val (mulMeasure ν))
      = ∫⁻ u, ({0}ᶜ : Set F).indicator (fun u => (mE p u)⁻¹ * (mE p u * K (-u))) u ∂ν := by
          rw [lintegral_units_eq p ν (fun u => mE p u * K (-u)) ((measurable_mE p).mul hKn)]; rfl
    _ = ∫⁻ u, K (-u) ∂ν := by
          refine lintegral_congr_ae ?_
          have hae : ∀ᵐ u ∂ν, u ∈ ({0}ᶜ : Set F) := compl_mem_ae_iff.mpr hν0
          filter_upwards [hae] with u hu
          have hu0 : u ≠ 0 := hu
          rw [Set.indicator_of_mem hu, ← mul_assoc, ENNReal.inv_mul_cancel (mE_ne_zero p hu0) (mE_ne_top p u), one_mul]
    _ = ∫⁻ u, K ((((-1 : Fˣ)) : F) * u) ∂ν := by
          refine lintegral_congr fun u => ?_
          rw [Units.val_neg, Units.val_one, neg_one_mul]
    _ = ∫⁻ u, K u ∂ν := by
          rw [lintegral_comp_mul_units_left p ν (-1) K hK, Units.val_neg, Units.val_one, modulusE_neg, modulus_one,
            ENNReal.coe_one, inv_one, one_mul]

theorem mE_pow_four_mul_inv_three (b : Fˣ) :
    mE p (b : F) ^ 4 * (mE p (b : F))⁻¹ * (mE p (b : F))⁻¹ * (mE p (b : F))⁻¹ = mE p (b : F) := by
  have h0 : mE p (b : F) ≠ 0 := mE_units_ne_zero p b
  have ht : mE p (b : F) ≠ ⊤ := mE_ne_top p _
  calc mE p (b : F) ^ 4 * (mE p (b : F))⁻¹ * (mE p (b : F))⁻¹ * (mE p (b : F))⁻¹
      = mE p (b : F) * (mE p (b : F) * (mE p (b : F))⁻¹) * (mE p (b : F) * (mE p (b : F))⁻¹) *
          (mE p (b : F) * (mE p (b : F))⁻¹) := by ring
    _ = mE p (b : F) := by rw [ENNReal.mul_inv_cancel h0 ht, mul_one, mul_one, mul_one]

theorem reorder (f : Mat → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u, ∫⁻ r, ∫⁻ s, ∫⁻ t, f (M4 p r t u s) ∂ν ∂ν ∂ν ∂ν = ∫⁻ r, ∫⁻ t, ∫⁻ u, ∫⁻ s, f (M4 p r t u s) ∂ν ∂ν ∂ν ∂ν := by

  have h1 : Measurable fun v : (F × F) × F × F => f (M4 p v.1.2 v.2.2 v.1.1 v.2.1) :=
    hf.comp (measurable_M4_of p (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)
      (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd))
  have h1' : Measurable fun w : ((F × F) × F) × F => f (M4 p w.1.1.2 w.2 w.1.1.1 w.1.2) :=
    hf.comp (measurable_M4_of p (measurable_snd.comp (measurable_fst.comp measurable_fst)) measurable_snd
      (measurable_fst.comp (measurable_fst.comp measurable_fst)) (measurable_snd.comp measurable_fst))
  have hUR : Measurable fun v : F × F => ∫⁻ s, ∫⁻ t, f (M4 p v.2 t v.1 s) ∂ν ∂ν :=
    h1'.lintegral_prod_right'.lintegral_prod_right'
  rw [lintegral_lintegral_swap (f := fun u r => ∫⁻ s, ∫⁻ t, f (M4 p r t u s) ∂ν ∂ν) hUR.aemeasurable]
  refine lintegral_congr fun r => ?_

  have h2 : ∀ u : F, Measurable fun v : F × F => f (M4 p r v.2 u v.1) := fun u =>
    hf.comp (measurable_M4_of p measurable_const measurable_snd measurable_const measurable_fst)
  have hst : ∀ u : F, ∫⁻ s, ∫⁻ t, f (M4 p r t u s) ∂ν ∂ν = ∫⁻ t, ∫⁻ s, f (M4 p r t u s) ∂ν ∂ν := fun u =>
    lintegral_lintegral_swap (f := fun s t => f (M4 p r t u s)) (h2 u).aemeasurable
  simp_rw [hst]
  have h3 : Measurable fun w : (F × F) × F => f (M4 p r w.1.2 w.1.1 w.2) :=
    hf.comp (measurable_M4_of p measurable_const (measurable_snd.comp measurable_fst)
      (measurable_fst.comp measurable_fst) measurable_snd)
  have hUT : Measurable fun v : F × F => ∫⁻ s, f (M4 p r v.2 v.1 s) ∂ν := h3.lintegral_prod_right'
  exact lintegral_lintegral_swap (f := fun u t => ∫⁻ s, f (M4 p r t u s) ∂ν) hUT.aemeasurable

theorem keyC (f : Mat → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, mE p ((q.1 : Fˣ) : F) ^ 4 * mE p ((q.2.2.1 : Fˣ) : F) *
        f (M4 p ((q.1 : F) * q.2.1) ((q.1 : F) * (q.2.1 * q.2.2.2 + (q.2.2.1 : F))) (-(q.1 : F)) (-((q.1 : F) * q.2.2.2)))
      ∂((Measure.comap Units.val (mulMeasure ν)).prod (ν.prod ((Measure.comap Units.val (mulMeasure ν)).prod ν))) =
    ∫⁻ X, f X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => ν) := by
  haveI : BorelSpace Fˣ := borelSpace_units
  haveI : SecondCountableTopology Fˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hrange : Set.range (Units.val : Fˣ → F) = ({0}ᶜ : Set F) := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  have hoe : Topology.IsOpenEmbedding (Units.val : Fˣ → F) :=
    ⟨Units.isEmbedding_val₀, by rw [hrange]; exact isOpen_compl_singleton⟩
  haveI : LocallyCompactSpace Fˣ := hoe.locallyCompactSpace
  haveI hτH : (Measure.comap Units.val (mulMeasure ν) : Measure Fˣ).IsHaarMeasure :=
    LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p ν
  set τ : Measure Fˣ := Measure.comap Units.val (mulMeasure ν) with hτ
  have hval : Measurable (Units.val : Fˣ → F) := Units.continuous_val.measurable

  set G : Fˣ × F × Fˣ × F → ℝ≥0∞ := fun q => mE p ((q.1 : Fˣ) : F) ^ 4 * mE p ((q.2.2.1 : Fˣ) : F) *
      f (M4 p ((q.1 : F) * q.2.1) ((q.1 : F) * (q.2.1 * q.2.2.2 + (q.2.2.1 : F))) (-(q.1 : F)) (-((q.1 : F) * q.2.2.2)))
    with hGdef
  have hGof : ∀ {α : Type} [MeasurableSpace α] (b : α → Fˣ) (x : α → F) (a : α → Fˣ) (y : α → F),
      Measurable b → Measurable x → Measurable a → Measurable y →
      Measurable fun v => G (b v, (x v, (a v, y v))) := by
    intro α _ b x a y hb hx ha hy
    have ha' : Measurable fun v => ((a v : Fˣ) : F) := hval.comp ha
    have hb' : Measurable fun v => ((b v : Fˣ) : F) := hval.comp hb
    have h1 : Measurable fun v => mE p ((b v : Fˣ) : F) ^ 4 * mE p ((a v : Fˣ) : F) :=
      (((measurable_mE p).comp hb').pow_const 4).mul ((measurable_mE p).comp ha')
    have h2 : Measurable fun v => f (M4 p ((b v : F) * x v) ((b v : F) * (x v * y v + (a v : F))) (-(b v : F))
        (-((b v : F) * y v))) :=
      hf.comp (measurable_M4_of p (hb'.mul hx) (hb'.mul ((hx.mul hy).add ha')) hb'.neg (hb'.mul hy).neg)
    exact h1.mul h2
  have hGm : Measurable G :=
    hGof (fun q : Fˣ × F × Fˣ × F => q.1) (fun q => q.2.1) (fun q => q.2.2.1) (fun q => q.2.2.2)
      measurable_fst (measurable_fst.comp measurable_snd) (measurable_fst.comp (measurable_snd.comp measurable_snd))
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hG1 : ∀ b : Fˣ, Measurable fun r : F × Fˣ × F => G (b, r) := fun b =>
    hGof (fun _ => b) (fun r : F × Fˣ × F => r.1) (fun r => r.2.1) (fun r => r.2.2)
      measurable_const measurable_fst (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  have hG2 : ∀ (b : Fˣ) (x : F), Measurable fun w : Fˣ × F => G (b, (x, w)) := fun b x =>
    hGof (fun _ => b) (fun _ => x) (fun w : Fˣ × F => w.1) (fun w => w.2)
      measurable_const measurable_const measurable_fst measurable_snd
  have hGpt : ∀ (b : Fˣ) (x : F) (a : Fˣ) (y : F), G (b, (x, (a, y))) =
      mE p (b : F) ^ 4 * mE p (a : F) *
        f (M4 p ((b : F) * x) ((b : F) * (x * y + (a : F))) (-(b : F)) (-((b : F) * y))) := fun _ _ _ _ => rfl
  have hK : Measurable fun u : F => ∫⁻ r, ∫⁻ s, ∫⁻ t, f (M4 p r t u s) ∂ν ∂ν ∂ν := by
    have hin : Measurable fun w : ((F × F) × F) × F => f (M4 p w.1.1.2 w.2 w.1.1.1 w.1.2) :=
      hf.comp (measurable_M4_of p (measurable_snd.comp (measurable_fst.comp measurable_fst)) measurable_snd
        (measurable_fst.comp (measurable_fst.comp measurable_fst)) (measurable_snd.comp measurable_fst))
    exact hin.lintegral_prod_right'.lintegral_prod_right'.lintegral_prod_right'
  have hCtop : ∀ b : Fˣ, mE p (b : F) ^ 4 * (mE p (b : F))⁻¹ ≠ ⊤ := fun b =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (mE_ne_top p _)) (ENNReal.inv_ne_top.mpr (mE_units_ne_zero p b))
  have hC2top : ∀ b : Fˣ, mE p (b : F) ^ 4 * (mE p (b : F))⁻¹ * (mE p (b : F))⁻¹ ≠ ⊤ := fun b =>
    ENNReal.mul_ne_top (hCtop b) (ENNReal.inv_ne_top.mpr (mE_units_ne_zero p b))

  calc ∫⁻ q, G q ∂(τ.prod (ν.prod (τ.prod ν)))
      = ∫⁻ b, ∫⁻ r, G (b, r) ∂(ν.prod (τ.prod ν)) ∂τ := lintegral_prod G hGm.aemeasurable
    _ = ∫⁻ b, ∫⁻ x, ∫⁻ w, G (b, (x, w)) ∂(τ.prod ν) ∂ν ∂τ :=
        lintegral_congr fun b => lintegral_prod _ (hG1 b).aemeasurable
    _ = ∫⁻ b, ∫⁻ x, ∫⁻ a, ∫⁻ y, G (b, (x, (a, y))) ∂ν ∂τ ∂ν ∂τ :=
        lintegral_congr fun b => lintegral_congr fun x => lintegral_prod _ (hG2 b x).aemeasurable
    _ = ∫⁻ b, ∫⁻ x, ∫⁻ y, ∫⁻ a, G (b, (x, (a, y))) ∂τ ∂ν ∂ν ∂τ := by
        refine lintegral_congr fun b => lintegral_congr fun x => ?_
        exact lintegral_lintegral_swap (f := fun a y => G (b, (x, (a, y)))) (hG2 b x).aemeasurable
    _ = ∫⁻ b, ∫⁻ x, ∫⁻ y, mE p (b : F) ^ 4 * ((mE p (b : F))⁻¹ *
          ∫⁻ t, f (M4 p ((b : F) * x) t (-(b : F)) (-((b : F) * y))) ∂ν) ∂ν ∂ν ∂τ := by
        refine lintegral_congr fun b => lintegral_congr fun x => lintegral_congr fun y => ?_
        rw [hτ]
        exact stepA p ν f hf b x y
    _ = ∫⁻ b, ∫⁻ x, (mE p (b : F) ^ 4 * (mE p (b : F))⁻¹) * ((mE p (b : F))⁻¹ *
          ∫⁻ s, ∫⁻ t, f (M4 p ((b : F) * x) t (-(b : F)) s) ∂ν ∂ν) ∂ν ∂τ := by
        refine lintegral_congr fun b => lintegral_congr fun x => ?_
        simp only [← mul_assoc]
        have := stepS p ν f hf b x (mE p (b : F) ^ 4 * (mE p (b : F))⁻¹) (hCtop b)
        simp only [← mul_assoc] at this
        exact this
    _ = ∫⁻ b, (mE p (b : F) ^ 4 * (mE p (b : F))⁻¹ * (mE p (b : F))⁻¹) * ((mE p (b : F))⁻¹ *
          ∫⁻ r, ∫⁻ s, ∫⁻ t, f (M4 p r t (-(b : F)) s) ∂ν ∂ν ∂ν) ∂τ := by
        refine lintegral_congr fun b => ?_
        have := stepT p ν f hf b (mE p (b : F) ^ 4 * (mE p (b : F))⁻¹ * (mE p (b : F))⁻¹) (hC2top b)
        simp only [← mul_assoc] at this ⊢
        exact this
    _ = ∫⁻ b, mE p (b : F) * ∫⁻ r, ∫⁻ s, ∫⁻ t, f (M4 p r t (-(b : F)) s) ∂ν ∂ν ∂ν ∂τ := by
        refine lintegral_congr fun b => ?_
        rw [← mul_assoc, mE_pow_four_mul_inv_three]
    _ = ∫⁻ u, ∫⁻ r, ∫⁻ s, ∫⁻ t, f (M4 p r t u s) ∂ν ∂ν ∂ν ∂ν := by
        rw [hτ]; exact stepB p ν _ hK
    _ = ∫⁻ r, ∫⁻ t, ∫⁻ u, ∫⁻ s, f (M4 p r t u s) ∂ν ∂ν ∂ν ∂ν := reorder p ν f hf
    _ = ∫⁻ X, f X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => ν) := (lintegral_pi_pi p ν f hf).symm

end Key

theorem isAddHaarMeasure_selfDualHaarAt' (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal K v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt K v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts K v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

end BigCell

end

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
open scoped ENNReal

open scoped NNReal

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    MeasureTheory.Measure.map (β := Fin 2 → Fin 2 → p.adicCompletion ℚ)
        (fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
          !![(q.1 : p.adicCompletion ℚ) * q.2.1, (q.1 : p.adicCompletion ℚ) * (q.2.1 * q.2.2.2 + (q.2.2.1 : p.adicCompletion ℚ));
             -(q.1 : p.adicCompletion ℚ), -((q.1 : p.adicCompletion ℚ) * q.2.2.2)])
        (((MeasureTheory.Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
            ((selfDualHaarAt ℚ p).prod
              ((MeasureTheory.Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (selfDualHaarAt ℚ p)))).withDensity
          fun q => (modulus (q.1 : p.adicCompletion ℚ) : ℝ≥0∞) ^ 4 * (modulus (q.2.2.1 : p.adicCompletion ℚ) : ℝ≥0∞)) =
      (MeasureTheory.Measure.pi fun _ : Fin 2 => MeasureTheory.Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by
  letI ims : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := BigCell.isAddHaarMeasure_selfDualHaarAt' ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := BigCell.borelSpace_units

  set Θ : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ →
      (Fin 2 → Fin 2 → p.adicCompletion ℚ) :=
    fun q => !![(q.1 : p.adicCompletion ℚ) * q.2.1, (q.1 : p.adicCompletion ℚ) * (q.2.1 * q.2.2.2 + (q.2.2.1 : p.adicCompletion ℚ));
             -(q.1 : p.adicCompletion ℚ), -((q.1 : p.adicCompletion ℚ) * q.2.2.2)] with hΘdef
  have hΘpt : ∀ q, Θ q = BigCell.M4 p ((q.1 : p.adicCompletion ℚ) * q.2.1)
      ((q.1 : p.adicCompletion ℚ) * (q.2.1 * q.2.2.2 + (q.2.2.1 : p.adicCompletion ℚ)))
      (-(q.1 : p.adicCompletion ℚ)) (-((q.1 : p.adicCompletion ℚ) * q.2.2.2)) := fun q => rfl
  have hΘeq : Θ = fun q => BigCell.M4 p ((q.1 : p.adicCompletion ℚ) * q.2.1)
      ((q.1 : p.adicCompletion ℚ) * (q.2.1 * q.2.2.2 + (q.2.2.1 : p.adicCompletion ℚ)))
      (-(q.1 : p.adicCompletion ℚ)) (-((q.1 : p.adicCompletion ℚ) * q.2.2.2)) := funext hΘpt
  have hval : Measurable (Units.val : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ) := Units.continuous_val.measurable
  have hb : Measurable fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
      ((q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) := hval.comp measurable_fst
  have hx : Measurable fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
      q.2.1 := measurable_fst.comp measurable_snd
  have ha : Measurable fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
      ((q.2.2.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) := hval.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hy : Measurable fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
      q.2.2.2 := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hΘm : Measurable Θ := by
    rw [hΘeq]
    exact BigCell.measurable_M4_of p (hb.mul hx) (hb.mul ((hx.mul hy).add ha)) hb.neg (hb.mul hy).neg
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hΘm hS, withDensity_apply _ (hΘm hS), ← lintegral_indicator (hΘm hS),
    ← lintegral_indicator_one hS]
  have hSi : Measurable (S.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hS
  have key' := BigCell.keyC p (selfDualHaarAt ℚ p) (S.indicator fun _ => (1 : ℝ≥0∞)) hSi
  have hL : ∀ q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ,
      (Θ ⁻¹' S).indicator (fun q => (modulus (q.1 : p.adicCompletion ℚ) : ℝ≥0∞) ^ 4 *
          (modulus (q.2.2.1 : p.adicCompletion ℚ) : ℝ≥0∞)) q =
      BigCell.mE p ((q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ^ 4 *
        BigCell.mE p ((q.2.2.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) *
        S.indicator (fun _ => (1 : ℝ≥0∞)) (BigCell.M4 p ((q.1 : p.adicCompletion ℚ) * q.2.1)
          ((q.1 : p.adicCompletion ℚ) * (q.2.1 * q.2.2.2 + (q.2.2.1 : p.adicCompletion ℚ)))
          (-(q.1 : p.adicCompletion ℚ)) (-((q.1 : p.adicCompletion ℚ) * q.2.2.2))) := by
    intro q
    rw [← hΘpt q]
    by_cases h : q ∈ Θ ⁻¹' S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.mp h), mul_one]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_preimage.mpr h')), mul_zero]
  rw [lintegral_congr hL, key']
  rfl

end S_LanglandsTunnell_RankinSelberg_map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_map_bigCellWeyl_withDensity_eq_pi_selfDualHaarAt (solution)
