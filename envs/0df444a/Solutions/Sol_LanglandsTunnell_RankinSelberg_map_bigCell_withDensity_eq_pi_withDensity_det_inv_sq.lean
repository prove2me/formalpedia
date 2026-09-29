-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.map_bigCell_withDensity_eq_pi_withDensity_det_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8507651f-4885-5e82-a595-4adb91f65a12

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

namespace P2MW.S_LanglandsTunnell_RankinSelberg_map_bigCell_withDensity_eq_pi_withDensity_det_inv_sq

set_option autoImplicit false
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

theorem coe_cellMap (x : F) (b a : Fˣ) (z : F) :
    ((lowerUnipotentGL2 z * diagUnits2 a b * unipotentGL2 x : GL (Fin 2) F) : Mat) =
      !![(a : F), (a : F) * x; z * (a : F), z * (a : F) * x + (b : F)] := by
  simp only [Units.val_mul, lowerUnipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnits2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

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

def Dn (X : Mat) : ℝ≥0∞ := {X : Mat | Matrix.det X ≠ 0}.indicator (fun X => (((modulus (Matrix.det X) : ℝ≥0∞)) ^ 2)⁻¹) X

theorem measurable_modulusE : Measurable fun x : F => (modulus x : ℝ≥0∞) :=
  (continuous_modulus p).measurable.coe_nnreal_ennreal

theorem measurable_det2 : Measurable fun X : Mat => Matrix.det X := by
  have : (fun X : Mat => Matrix.det X) = fun X => X 0 0 * X 1 1 - X 0 1 * X 1 0 := by
    funext X; exact Matrix.det_fin_two X
  rw [this]
  fun_prop

theorem measurable_Dn : Measurable (Dn p) := by
  unfold Dn
  refine Measurable.indicator ?_ ?_
  · exact ((measurable_modulusE p).comp (measurable_det2 p)).pow_const 2 |>.inv
  · exact (measurable_det2 p) (measurableSet_singleton 0).compl

def M4 (t y u s : F) : Mat := ![![t, y], ![u, s]]

theorem M4_eq (t y u s : F) : (M4 p t y u s : Mat) = (!![t, y; u, s] : Matrix (Fin 2) (Fin 2) F) := rfl

theorem measurable_M4 : Measurable fun q : F × F × F × F => M4 p q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [M4] <;> fun_prop

theorem det_M4 (t y u s : F) : Matrix.det (M4 p t y u s) = t * s - y * u := by
  rw [M4_eq, Matrix.det_fin_two_of]

end Key

section Key2

variable [MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ p)] [BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)]

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

def mm (t : F) : ℝ≥0∞ := ({0}ᶜ : Set F).indicator (fun t => (mE p t)⁻¹ * (mE p t)⁻¹) t

theorem measurable_mm : Measurable (mm p) :=
  ((measurable_mE p).inv.mul (measurable_mE p).inv).indicator (measurableSet_singleton 0).compl

theorem mm_eq (a : Fˣ) (y u s : F) :
    mm p (s - u * ((a : F))⁻¹ * y) = mE p (a : F) ^ 2 * Dn p (M4 p (a : F) y u s) := by
  have hdet : Matrix.det (M4 p (a : F) y u s) = (a : F) * s - y * u := det_M4 p _ _ _ _
  have hkey : s - u * ((a : F))⁻¹ * y = Matrix.det (M4 p (a : F) y u s) * ((a : F))⁻¹ := by
    rw [hdet]; field_simp
  by_cases h0 : Matrix.det (M4 p (a : F) y u s) = 0
  · have : s - u * ((a : F))⁻¹ * y = 0 := by rw [hkey, h0, zero_mul]
    rw [this, mm, Set.indicator_of_notMem (by simp), Dn, Set.indicator_of_notMem (by simpa using h0), mul_zero]
  · have hne : s - u * ((a : F))⁻¹ * y ≠ 0 := by
      rw [hkey]; exact mul_ne_zero h0 (inv_ne_zero a.ne_zero)
    rw [mm, Set.indicator_of_mem (by simpa using hne), Dn, Set.indicator_of_mem (by simpa using h0), hkey, mE_mul, mE_inv]
    simp only [mE]
    have ha0 : (modulus (a : F) : ℝ≥0∞) ≠ 0 := modulusE_units_ne_zero p a
    have hat : (modulus (a : F) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hd0 : (modulus (Matrix.det (M4 p (↑a) y u s)) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero h0)
    have hdt : (modulus (Matrix.det (M4 p (↑a) y u s)) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt), inv_inv, sq, sq, ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt)]
    ring

variable (ν : Measure (HeightOneSpectrum.adicCompletion ℚ p)) [ν.IsAddHaarMeasure] [SigmaFinite ν]

def Ic (f : Mat → ℝ≥0∞) (t : F) : ℝ≥0∞ :=
  ∫⁻ u, ∫⁻ y, ∫⁻ s, Dn p (M4 p t y u s) * f (M4 p t y u s) ∂ν ∂ν ∂ν

theorem measurable_M4c (a : F) : Measurable fun v : F × F × F => M4 p a v.1 v.2.1 v.2.2 :=
  (measurable_M4 p).comp (measurable_const.prodMk (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))))

theorem measurable_M4_of {α : Type*} [MeasurableSpace α] {t y u s : α → F}
    (ht : Measurable t) (hy : Measurable y) (hu : Measurable u) (hs : Measurable s) :
    Measurable fun v => M4 p (t v) (y v) (u v) (s v) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;> simpa [M4]

theorem measurable_DnMul_of {α : Type*} [MeasurableSpace α] (f : Mat → ℝ≥0∞) (hf : Measurable f) {t y u s : α → F}
    (ht : Measurable t) (hy : Measurable y) (hu : Measurable u) (hs : Measurable s) :
    Measurable fun v => Dn p (M4 p (t v) (y v) (u v) (s v)) * f (M4 p (t v) (y v) (u v) (s v)) :=
  ((measurable_Dn p).mul hf).comp (measurable_M4_of p ht hy hu hs)

theorem measurable_J4 (f : Mat → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun v : F × F × F × F => Dn p (M4 p v.1 v.2.1 v.2.2.1 v.2.2.2) * f (M4 p v.1 v.2.1 v.2.2.1 v.2.2.2) :=
  (((measurable_Dn p).mul hf)).comp (measurable_M4 p)

theorem measurable_J4' (f : Mat → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun v : ((F × F) × F) × F => Dn p (M4 p v.1.1.1 v.1.2 v.1.1.2 v.2) * f (M4 p v.1.1.1 v.1.2 v.1.1.2 v.2) :=
  measurable_DnMul_of p f hf (measurable_fst.comp (measurable_fst.comp measurable_fst)) (measurable_snd.comp measurable_fst)
    (measurable_snd.comp (measurable_fst.comp measurable_fst)) measurable_snd

theorem measurable_Ic2 (f : Mat → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun v : (F × F) × F => ∫⁻ s, Dn p (M4 p v.1.1 v.2 v.1.2 s) * f (M4 p v.1.1 v.2 v.1.2 s) ∂ν :=
  (measurable_J4' p f hf).lintegral_prod_right'

theorem measurable_Ic1 (f : Mat → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun v : F × F => ∫⁻ y, ∫⁻ s, Dn p (M4 p v.1 y v.2 s) * f (M4 p v.1 y v.2 s) ∂ν ∂ν :=
  (measurable_Ic2 p ν f hf).lintegral_prod_right'

theorem measurable_Ic (f : Mat → ℝ≥0∞) (hf : Measurable f) : Measurable (Ic p ν f) :=
  (measurable_Ic1 p ν f hf).lintegral_prod_right'

theorem stepF (f : Mat → ℝ≥0∞) (hf : Measurable f) (a : Fˣ) (z x : F) :
    ∫⁻ b : Fˣ, mE p (a : F) * ((mE p (b : F))⁻¹ * f (M4 p (a : F) ((a : F) * x) (z * (a : F)) (z * (a : F) * x + (b : F))))
        ∂(Measure.comap Units.val (mulMeasure ν)) =
      mE p (a : F) * ∫⁻ s, mm p (s - z * (a : F) * x) * f (M4 p (a : F) ((a : F) * x) (z * (a : F)) s) ∂ν := by
  set c : F := z * (a : F) * x with hc
  have hmeasG0 : Measurable fun t : F => (mE p t)⁻¹ * f (M4 p (a : F) ((a : F) * x) (z * (a : F)) (c + t)) :=
    (measurable_mE p).inv.mul (hf.comp (measurable_M4_of p measurable_const measurable_const measurable_const
      (measurable_const.add measurable_id)))
  rw [lintegral_const_mul' _ _ (mE_ne_top p _)]
  congr 1
  calc ∫⁻ b : Fˣ, (mE p (b : F))⁻¹ * f (M4 p (a : F) ((a : F) * x) (z * (a : F)) (c + (b : F)))
          ∂(Measure.comap Units.val (mulMeasure ν))
      = ∫⁻ t, ({0}ᶜ : Set F).indicator
            (fun t => (mE p t)⁻¹ * ((mE p t)⁻¹ * f (M4 p (a : F) ((a : F) * x) (z * (a : F)) (c + t)))) t ∂ν := by
          rw [lintegral_units_eq p ν _ hmeasG0]; rfl
    _ = ∫⁻ t, mm p (c + t - c) * f (M4 p (a : F) ((a : F) * x) (z * (a : F)) (c + t)) ∂ν := by
          refine lintegral_congr fun t => ?_
          rw [add_sub_cancel_left, mm]
          by_cases ht : t = 0
          · rw [Set.indicator_of_notMem (by simp [ht]), Set.indicator_of_notMem (by simp [ht]), zero_mul]
          · rw [Set.indicator_of_mem (by simp [ht]), Set.indicator_of_mem (by simp [ht]), mul_assoc]
    _ = ∫⁻ s, mm p (s - c) * f (M4 p (a : F) ((a : F) * x) (z * (a : F)) s) ∂ν :=
          lintegral_add_left_eq_self (μ := ν) (fun s => mm p (s - c) * f (M4 p (a : F) ((a : F) * x) (z * (a : F)) s)) c

theorem stepI (f : Mat → ℝ≥0∞) (hf : Measurable f) (a : Fˣ) :
    (mE p (a : F))⁻¹ * ∫⁻ u, ((mE p (a : F))⁻¹ * ∫⁻ y, (mE p (a : F) * ∫⁻ s,
        mm p (s - u * ((a : F))⁻¹ * y) * f (M4 p (a : F) y u s) ∂ν) ∂ν) ∂ν = mE p (a : F) * Ic p ν f (a : F) := by
  have ha0 : mE p (a : F) ≠ 0 := mE_ne_zero p a.ne_zero
  have hat : mE p (a : F) ≠ ⊤ := mE_ne_top p _
  have hinv_top : (mE p (a : F))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr ha0
  have hsq_top : mE p (a : F) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hat
  have h1 : ∀ u y : F, ∫⁻ s, mm p (s - u * ((a : F))⁻¹ * y) * f (M4 p (a : F) y u s) ∂ν =
      mE p (a : F) ^ 2 * ∫⁻ s, Dn p (M4 p (a : F) y u s) * f (M4 p (a : F) y u s) ∂ν := by
    intro u y
    rw [← lintegral_const_mul' _ _ hsq_top]
    refine lintegral_congr fun s => ?_
    rw [mm_eq p a y u s, mul_assoc]
  simp_rw [h1]
  have h2 : ∀ u : F, ∫⁻ y, mE p (a : F) * (mE p (a : F) ^ 2 * ∫⁻ s, Dn p (M4 p (a : F) y u s) * f (M4 p (a : F) y u s) ∂ν) ∂ν =
      (mE p (a : F) * mE p (a : F) ^ 2) * ∫⁻ y, ∫⁻ s, Dn p (M4 p (a : F) y u s) * f (M4 p (a : F) y u s) ∂ν ∂ν := by
    intro u
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hat hsq_top)]
    refine lintegral_congr fun y => ?_
    rw [mul_assoc]
  simp_rw [h2]
  have h3 : ∫⁻ u, (mE p (a : F))⁻¹ * ((mE p (a : F) * mE p (a : F) ^ 2) *
        ∫⁻ y, ∫⁻ s, Dn p (M4 p (a : F) y u s) * f (M4 p (a : F) y u s) ∂ν ∂ν) ∂ν =
      ((mE p (a : F))⁻¹ * (mE p (a : F) * mE p (a : F) ^ 2)) *
        ∫⁻ u, ∫⁻ y, ∫⁻ s, Dn p (M4 p (a : F) y u s) * f (M4 p (a : F) y u s) ∂ν ∂ν ∂ν := by
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hinv_top (ENNReal.mul_ne_top hat hsq_top))]
    exact lintegral_congr fun u => (mul_assoc _ _ _).symm
  rw [h3, ← mul_assoc, Ic]
  congr 1
  rw [sq]
  calc (mE p ↑a)⁻¹ * ((mE p ↑a)⁻¹ * (mE p ↑a * (mE p ↑a * mE p ↑a)))
      = ((mE p ↑a)⁻¹ * mE p ↑a) * ((mE p ↑a)⁻¹ * mE p ↑a) * mE p ↑a := by ring
    _ = mE p ↑a := by rw [ENNReal.inv_mul_cancel ha0 hat, one_mul, one_mul]

theorem stepJ (f : Mat → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ a : Fˣ, mE p (a : F) * Ic p ν f (a : F) ∂(Measure.comap Units.val (mulMeasure ν)) =
      ∫⁻ X, Dn p X * f X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => ν) := by
  have hν0 : ν {0} = 0 := measure_zero_singleton p ν
  have hDf : Measurable fun X : Mat => Dn p X * f X := (measurable_Dn p).mul hf
  have hswapI : ∀ t : F, Measurable fun w : (F × F) × F => Dn p (M4 p t w.1.2 w.1.1 w.2) * f (M4 p t w.1.2 w.1.1 w.2) := fun t =>
    measurable_DnMul_of p f hf measurable_const (measurable_snd.comp measurable_fst) (measurable_fst.comp measurable_fst) measurable_snd
  calc ∫⁻ a : Fˣ, mE p (a : F) * Ic p ν f (a : F) ∂(Measure.comap Units.val (mulMeasure ν))
      = ∫⁻ t, ({0}ᶜ : Set F).indicator (fun t => (mE p t)⁻¹ * (mE p t * Ic p ν f t)) t ∂ν := by
        rw [lintegral_units_eq p ν (fun t => mE p t * Ic p ν f t) ((measurable_mE p).mul (measurable_Ic p ν f hf))]; rfl
    _ = ∫⁻ t, Ic p ν f t ∂ν := by
        refine lintegral_congr_ae ?_
        have hae : ∀ᵐ t ∂ν, t ∈ ({0}ᶜ : Set F) := compl_mem_ae_iff.mpr hν0
        filter_upwards [hae] with t ht
        have ht0 : t ≠ 0 := ht
        rw [Set.indicator_of_mem ht, ← mul_assoc, ENNReal.inv_mul_cancel (mE_ne_zero p ht0) (mE_ne_top p t), one_mul]
    _ = ∫⁻ t, ∫⁻ y, ∫⁻ u, ∫⁻ s, Dn p (M4 p t y u s) * f (M4 p t y u s) ∂ν ∂ν ∂ν ∂ν := by
        refine lintegral_congr fun t => ?_
        exact lintegral_lintegral_swap (f := fun u y => ∫⁻ s, Dn p (M4 p t y u s) * f (M4 p t y u s) ∂ν)
          ((hswapI t).lintegral_prod_right').aemeasurable
    _ = ∫⁻ X, Dn p X * f X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => ν) :=
        (lintegral_pi_pi p ν (fun X => Dn p X * f X) hDf).symm

theorem key (f : Mat → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, mE p (((q.2.2.1 * (q.2.1)⁻¹ : Fˣ)) : F) *
        f (M4 p (q.2.2.1 : F) ((q.2.2.1 : F) * q.1) (q.2.2.2 * (q.2.2.1 : F)) (q.2.2.2 * (q.2.2.1 : F) * q.1 + (q.2.1 : F)))
      ∂(ν.prod ((Measure.comap Units.val (mulMeasure ν)).prod ((Measure.comap Units.val (mulMeasure ν)).prod ν))) =
    ∫⁻ X, Dn p X * f X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => ν) := by
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

  set G : F × Fˣ × Fˣ × F → ℝ≥0∞ := fun q => mE p (((q.2.2.1 * (q.2.1)⁻¹ : Fˣ)) : F) *
      f (M4 p (q.2.2.1 : F) ((q.2.2.1 : F) * q.1) (q.2.2.2 * (q.2.2.1 : F)) (q.2.2.2 * (q.2.2.1 : F) * q.1 + (q.2.1 : F))) with hGdef

  have hGof : ∀ {α : Type} [MeasurableSpace α] (x : α → F) (b a : α → Fˣ) (z : α → F),
      Measurable x → Measurable b → Measurable a → Measurable z →
      Measurable fun v => G (x v, (b v, (a v, z v))) := by
    intro α _ x b a z hx hb ha hz
    have ha' : Measurable fun v => ((a v : Fˣ) : F) := hval.comp ha
    have hb' : Measurable fun v => ((b v : Fˣ) : F) := hval.comp hb
    have h1 : Measurable fun v => mE p ((((a v) * (b v)⁻¹ : Fˣ)) : F) := (measurable_mE p).comp (hval.comp (ha.mul hb.inv))
    have h2 : Measurable fun v => f (M4 p (a v : F) ((a v : F) * x v) (z v * (a v : F)) (z v * (a v : F) * x v + (b v : F))) :=
      hf.comp (measurable_M4_of p ha' (ha'.mul hx) (hz.mul ha') (((hz.mul ha').mul hx).add hb'))
    exact h1.mul h2
  have hGm : Measurable G := by
    have := hGof (fun q : F × Fˣ × Fˣ × F => q.1) (fun q => q.2.1) (fun q => q.2.2.1) (fun q => q.2.2.2)
      measurable_fst (measurable_fst.comp measurable_snd) (measurable_fst.comp (measurable_snd.comp measurable_snd))
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
    exact this
  have hKin : Measurable fun w : (Fˣ × Fˣ × F) × F => G (w.2, w.1) :=
    hGof (fun w : (Fˣ × Fˣ × F) × F => w.2) (fun w => w.1.1) (fun w => w.1.2.1) (fun w => w.1.2.2)
      measurable_snd (measurable_fst.comp measurable_fst) (measurable_fst.comp (measurable_snd.comp measurable_fst))
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hK : Measurable fun r : Fˣ × Fˣ × F => ∫⁻ x, G (x, r) ∂ν := hKin.lintegral_prod_right'
  have hLin : Measurable fun v : ((Fˣ × F) × Fˣ) × F => G (v.2, (v.1.2, (v.1.1.1, v.1.1.2))) :=
    hGof (fun v : ((Fˣ × F) × Fˣ) × F => v.2) (fun v => v.1.2) (fun v => v.1.1.1) (fun v => v.1.1.2)
      measurable_snd (measurable_snd.comp measurable_fst) (measurable_fst.comp (measurable_fst.comp measurable_fst))
      (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hL : Measurable fun w : Fˣ × F => ∫⁻ b, ∫⁻ x, G (x, (b, w)) ∂ν ∂τ :=
    (hLin.lintegral_prod_right').lintegral_prod_right'
  have hGbx : ∀ (a : Fˣ) (z : F), Measurable fun bx : Fˣ × F => G (bx.2, (bx.1, (a, z))) := fun a z =>
    hGof (fun bx : Fˣ × F => bx.2) (fun bx => bx.1) (fun _ => a) (fun _ => z)
      measurable_snd measurable_fst measurable_const measurable_const
  have hGpt : ∀ (x : F) (b a : Fˣ) (z : F), G (x, (b, (a, z))) =
      mE p (a : F) * ((mE p (b : F))⁻¹ * f (M4 p (a : F) ((a : F) * x) (z * (a : F)) (z * (a : F) * x + (b : F)))) := by
    intro x b a z
    show mE p (((a * b⁻¹ : Fˣ)) : F) * _ = _
    rw [Units.val_mul, mE_mul, mE_units_inv, mul_assoc]

  have hΦ : ∀ (a : Fˣ) (z : F), Measurable fun y : F => mE p (a : F) * ∫⁻ s, mm p (s - z * y) * f (M4 p (a : F) y (z * (a : F)) s) ∂ν := by
    intro a z
    have hin : Measurable fun v : F × F => mm p (v.2 - z * v.1) * f (M4 p (a : F) v.1 (z * (a : F)) v.2) :=
      ((measurable_mm p).comp (measurable_snd.sub (measurable_fst.const_mul z))).mul
        (hf.comp (measurable_M4_of p measurable_const measurable_fst measurable_const measurable_snd))
    exact hin.lintegral_prod_right'.const_mul _
  have hΨ : ∀ (a : Fˣ), Measurable fun u : F => (mE p (a : F))⁻¹ * ∫⁻ y, (mE p (a : F) * ∫⁻ s,
      mm p (s - u * ((a : F))⁻¹ * y) * f (M4 p (a : F) y u s) ∂ν) ∂ν := by
    intro a
    have hin : Measurable fun w : (F × F) × F => mm p (w.2 - w.1.1 * ((a : F))⁻¹ * w.1.2) * f (M4 p (a : F) w.1.2 w.1.1 w.2) :=
      ((measurable_mm p).comp (measurable_snd.sub
        ((((measurable_fst.comp measurable_fst).mul_const _).mul (measurable_snd.comp measurable_fst))))).mul
        (hf.comp (measurable_M4_of p measurable_const (measurable_snd.comp measurable_fst) (measurable_fst.comp measurable_fst)
          measurable_snd))
    have hmid : Measurable fun v : F × F => mE p (a : F) * ∫⁻ s, mm p (s - v.1 * ((a : F))⁻¹ * v.2) * f (M4 p (a : F) v.2 v.1 s) ∂ν :=
      hin.lintegral_prod_right'.const_mul _
    exact hmid.lintegral_prod_right'.const_mul _

  calc ∫⁻ q, G q ∂(ν.prod (τ.prod (τ.prod ν)))
      = ∫⁻ x, ∫⁻ r, G (x, r) ∂(τ.prod (τ.prod ν)) ∂ν := lintegral_prod G hGm.aemeasurable
    _ = ∫⁻ r, ∫⁻ x, G (x, r) ∂ν ∂(τ.prod (τ.prod ν)) :=
        lintegral_lintegral_swap (f := fun x r => G (x, r)) hGm.aemeasurable
    _ = ∫⁻ b, ∫⁻ w, ∫⁻ x, G (x, (b, w)) ∂ν ∂(τ.prod ν) ∂τ :=
        lintegral_prod (fun r => ∫⁻ x, G (x, r) ∂ν) hK.aemeasurable
    _ = ∫⁻ w, ∫⁻ b, ∫⁻ x, G (x, (b, w)) ∂ν ∂τ ∂(τ.prod ν) :=
        lintegral_lintegral_swap (f := fun b w => ∫⁻ x, G (x, (b, w)) ∂ν) hK.aemeasurable
    _ = ∫⁻ a, ∫⁻ z, ∫⁻ b, ∫⁻ x, G (x, (b, (a, z))) ∂ν ∂τ ∂ν ∂τ :=
        lintegral_prod (fun w => ∫⁻ b, ∫⁻ x, G (x, (b, w)) ∂ν ∂τ) hL.aemeasurable
    _ = ∫⁻ a, ∫⁻ z, ∫⁻ x, ∫⁻ b, G (x, (b, (a, z))) ∂τ ∂ν ∂ν ∂τ := by
        refine lintegral_congr fun a => lintegral_congr fun z => ?_
        exact lintegral_lintegral_swap (f := fun b x => G (x, (b, (a, z)))) (hGbx a z).aemeasurable
    _ = ∫⁻ a, ∫⁻ z, ∫⁻ x, mE p (a : F) * ∫⁻ s, mm p (s - z * (a : F) * x) *
          f (M4 p (a : F) ((a : F) * x) (z * (a : F)) s) ∂ν ∂ν ∂ν ∂τ := by
        refine lintegral_congr fun a => lintegral_congr fun z => lintegral_congr fun x => ?_
        rw [← stepF p ν f hf a z x, hτ]
        exact lintegral_congr fun b => hGpt x b a z
    _ = ∫⁻ a, ∫⁻ z, (mE p (a : F))⁻¹ * ∫⁻ y, (mE p (a : F) * ∫⁻ s, mm p (s - z * y) *
          f (M4 p (a : F) y (z * (a : F)) s) ∂ν) ∂ν ∂ν ∂τ := by
        refine lintegral_congr fun a => lintegral_congr fun z => ?_
        have h := lintegral_comp_mul_units_left p ν a _ (hΦ a z)
        simp only [← mul_assoc] at h
        exact h
    _ = ∫⁻ a, (mE p (a : F))⁻¹ * ∫⁻ u, ((mE p (a : F))⁻¹ * ∫⁻ y, (mE p (a : F) * ∫⁻ s,
          mm p (s - u * ((a : F))⁻¹ * y) * f (M4 p (a : F) y u s) ∂ν) ∂ν) ∂ν ∂τ := by
        refine lintegral_congr fun a => ?_
        have h := lintegral_comp_mul_units p ν a _ (hΨ a)
        simp only [mul_inv_cancel_right₀ a.ne_zero] at h
        exact h
    _ = ∫⁻ a, mE p (a : F) * Ic p ν f (a : F) ∂τ := lintegral_congr fun a => stepI p ν f hf a
    _ = ∫⁻ X, Dn p X * f X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => ν) := by
        rw [hτ]; exact stepJ p ν f hf

end Key2

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
        (fun q : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
          ((lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1 : GL (Fin 2) (p.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
        (((selfDualHaarAt ℚ p).prod
            ((MeasureTheory.Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
              ((MeasureTheory.Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (selfDualHaarAt ℚ p)))).withDensity
          fun q => (modulus (((q.2.2.1 * (q.2.1)⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) : ℝ≥0∞)) =
      (MeasureTheory.Measure.pi fun _ : Fin 2 => MeasureTheory.Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p).withDensity
        fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
          {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | X.det ≠ 0}.indicator
            (fun X => (((modulus X.det : ℝ≥0∞)) ^ 2)⁻¹) X := by
  letI ims : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := BigCell.isAddHaarMeasure_selfDualHaarAt' ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := BigCell.borelSpace_units

  set Θ : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ → (Fin 2 → Fin 2 → p.adicCompletion ℚ) :=
    fun q => ((lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1 : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) with hΘdef
  set D : (Fin 2 → Fin 2 → p.adicCompletion ℚ) → ℝ≥0∞ := fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
      {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | X.det ≠ 0}.indicator
        (fun X => (((modulus X.det : ℝ≥0∞)) ^ 2)⁻¹) X with hDdef
  have hDeq : D = BigCell.Dn p := rfl
  have hΘpt : ∀ q, Θ q = BigCell.M4 p (q.2.2.1 : p.adicCompletion ℚ) ((q.2.2.1 : p.adicCompletion ℚ) * q.1)
      (q.2.2.2 * (q.2.2.1 : p.adicCompletion ℚ)) (q.2.2.2 * (q.2.2.1 : p.adicCompletion ℚ) * q.1 + (q.2.1 : p.adicCompletion ℚ)) := by
    intro q
    rw [hΘdef, BigCell.M4_eq]
    exact BigCell.coe_cellMap p q.1 q.2.1 q.2.2.1 q.2.2.2
  have hΘeq : Θ = fun q => BigCell.M4 p (q.2.2.1 : p.adicCompletion ℚ) ((q.2.2.1 : p.adicCompletion ℚ) * q.1)
      (q.2.2.2 * (q.2.2.1 : p.adicCompletion ℚ)) (q.2.2.2 * (q.2.2.1 : p.adicCompletion ℚ) * q.1 + (q.2.1 : p.adicCompletion ℚ)) :=
    funext hΘpt
  have hval : Measurable (Units.val : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ) := Units.continuous_val.measurable
  have ha : Measurable fun q : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
      ((q.2.2.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) := hval.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hb : Measurable fun q : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
      ((q.2.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) := hval.comp (measurable_fst.comp measurable_snd)
  have hx : Measurable fun q : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => q.1 :=
    measurable_fst
  have hz : Measurable fun q : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => q.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hΘm : Measurable Θ := by
    rw [hΘeq]
    exact BigCell.measurable_M4_of p ha (ha.mul hx) (hz.mul ha) (((hz.mul ha).mul hx).add hb)
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hΘm hS, withDensity_apply _ (hΘm hS), ← lintegral_indicator (hΘm hS),
    withDensity_apply _ hS, ← lintegral_indicator hS]
  have hSi : Measurable (S.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hS
  have key' := BigCell.key p (selfDualHaarAt ℚ p) (S.indicator fun _ => (1 : ℝ≥0∞)) hSi
  have hL : ∀ q : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ,
      (Θ ⁻¹' S).indicator (fun q => (modulus (((q.2.2.1 * (q.2.1)⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) : ℝ≥0∞)) q =
      BigCell.mE p (((q.2.2.1 * (q.2.1)⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) *
        S.indicator (fun _ => (1 : ℝ≥0∞)) (BigCell.M4 p (q.2.2.1 : p.adicCompletion ℚ) ((q.2.2.1 : p.adicCompletion ℚ) * q.1)
          (q.2.2.2 * (q.2.2.1 : p.adicCompletion ℚ)) (q.2.2.2 * (q.2.2.1 : p.adicCompletion ℚ) * q.1 + (q.2.1 : p.adicCompletion ℚ))) := by
    intro q
    rw [← hΘpt q]
    by_cases h : q ∈ Θ ⁻¹' S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.mp h), mul_one]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_preimage.mpr h')), mul_zero]
  have hR : ∀ X : Fin 2 → Fin 2 → p.adicCompletion ℚ,
      S.indicator D X = BigCell.Dn p X * S.indicator (fun _ => (1 : ℝ≥0∞)) X := by
    intro X
    rw [hDeq]
    by_cases h : X ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [lintegral_congr hL, lintegral_congr hR]
  exact key'

end S_LanglandsTunnell_RankinSelberg_map_bigCell_withDensity_eq_pi_withDensity_det_inv_sq
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_map_bigCell_withDensity_eq_pi_withDensity_det_inv_sq (solution)
