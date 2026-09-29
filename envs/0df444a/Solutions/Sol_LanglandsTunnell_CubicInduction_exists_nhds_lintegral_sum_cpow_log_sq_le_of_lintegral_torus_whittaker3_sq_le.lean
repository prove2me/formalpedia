-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d2153485-c867-5e44-ac56-333e8ad5b173

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction
open Set
open scoped ENNReal

namespace KcTorusBox

theorem nnnorm_sq_eq_ofReal' (z : ℂ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ← enorm_eq_nnnorm, ← ofReal_norm]

theorem coe_nnnorm_ennreal (z : ℂ) : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

def dg (d : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then d i else 0

noncomputable def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : InfinitePlace ℚ =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = StandardKernel.ofReal r := rfl

noncomputable def adeleOf (r : ℝ) : AdeleRing (𝓞 ℚ) ℚ :=
  ((StandardKernel.ofReal r, (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)

theorem adeleOf_mul (r s : ℝ) : adeleOf (r * s) = adeleOf r * adeleOf s := by
  unfold adeleOf
  rw [← ofRealHom_apply, map_mul]
  refine Prod.ext rfl ?_
  change (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 * 1
  rw [mul_one]

theorem adeleOf_one : adeleOf 1 = 1 := by
  unfold adeleOf
  rw [← ofRealHom_apply, map_one]
  rfl

theorem adeleOf_zero_fst : adeleOf 0 = ((0, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  unfold adeleOf
  rw [← ofRealHom_apply, map_zero]

theorem continuous_adeleOf : Continuous adeleOf := by
  unfold adeleOf
  exact StandardKernel.continuous_ofReal.prodMk continuous_const

theorem archRealMat3_dg (d : Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (dg d) = Matrix.diagonal fun i => adeleOf (d i) := by
  refine Matrix.ext fun i j => ?_
  change ((StandardKernel.ofReal (dg d i j), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
      InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) = _
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    simp only [dg, if_true]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    simp only [dg, if_neg h]
    rw [← ofRealHom_apply, map_zero]
    rfl

theorem isUnit_adeleOf {r : ℝ} (hr : r ≠ 0) : IsUnit (adeleOf r) := by
  refine IsUnit.of_mul_eq_one (adeleOf r⁻¹) ?_
  rw [← adeleOf_mul, mul_inv_cancel₀ hr, adeleOf_one]

theorem isUnit_archRealMat3_dg {d : Fin 3 → ℝ} (hd : ∀ i, d i ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 (dg d)) := by
  rw [archRealMat3_dg, Matrix.isUnit_diagonal]
  exact Pi.isUnit_iff.mpr fun i => isUnit_adeleOf (hd i)

theorem archRealLift3_dg_coe {d : Fin 3 → ℝ} (hd : ∀ i, d i ≠ 0) :
    ((WhittakerBlock.archRealLift3 (dg d) : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = Matrix.diagonal fun i => adeleOf (d i) := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3_dg hd), IsUnit.unit_spec, archRealMat3_dg]

theorem archRealLift3_dg_mul {d d' : Fin 3 → ℝ} (hd : ∀ i, d i ≠ 0) (hd' : ∀ i, d' i ≠ 0) :
    WhittakerBlock.archRealLift3 (dg d) * WhittakerBlock.archRealLift3 (dg d') =
      WhittakerBlock.archRealLift3 (dg fun i => d i * d' i) := by
  apply Units.ext
  rw [Units.val_mul, archRealLift3_dg_coe hd, archRealLift3_dg_coe hd',
    archRealLift3_dg_coe (fun i => mul_ne_zero (hd i) (hd' i)), Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [adeleOf_mul]

theorem archRealLift3_dg_one : WhittakerBlock.archRealLift3 (dg fun _ => (1 : ℝ)) = 1 := by
  apply Units.ext
  rw [archRealLift3_dg_coe (fun _ => one_ne_zero), Units.val_one]
  have : (fun _ : Fin 3 => adeleOf ((fun _ : Fin 3 => (1 : ℝ)) 0)) = fun _ => (1 : AdeleRing (𝓞 ℚ) ℚ) := by
    funext i; exact adeleOf_one
  simp only [adeleOf_one, Matrix.diagonal_one]

theorem archRealLift3_dg_inv {d : Fin 3 → ℝ} (hd : ∀ i, d i ≠ 0) :
    (WhittakerBlock.archRealLift3 (dg d))⁻¹ = WhittakerBlock.archRealLift3 (dg fun i => (d i)⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, archRealLift3_dg_mul hd (fun i => inv_ne_zero (hd i))]
  have : (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℝ) := funext fun i => mul_inv_cancel₀ (hd i)
  rw [this, archRealLift3_dg_one]

noncomputable def zc (z : ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ := WhittakerBlock.archRealLift3 (dg fun _ => z)

theorem continuousOn_zc : ContinuousOn zc (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  rw [Units.continuous_iff]
  constructor
  · have h : ∀ z : Set.Ioi (0 : ℝ), ((zc z : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
        Matrix.diagonal fun _ => adeleOf (z : ℝ) := fun z =>
      archRealLift3_dg_coe (fun _ => ne_of_gt z.2)
    have h' : (fun z : Set.Ioi (0 : ℝ) => ((zc z : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun z : Set.Ioi (0 : ℝ) => Matrix.diagonal fun _ : Fin 3 => adeleOf (z : ℝ) := funext h
    change Continuous fun z : Set.Ioi (0 : ℝ) => ((zc z : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    rw [h']
    exact (continuous_pi fun _ => continuous_adeleOf.comp continuous_subtype_val).matrix_diagonal
  · have h : ∀ z : Set.Ioi (0 : ℝ), (((zc z)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
        Matrix.diagonal fun _ => adeleOf ((z : ℝ)⁻¹) := fun z => by
      change (((WhittakerBlock.archRealLift3 (dg fun _ => (z : ℝ)))⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = _
      rw [archRealLift3_dg_inv (fun _ => ne_of_gt z.2), archRealLift3_dg_coe (fun _ => inv_ne_zero (ne_of_gt z.2))]
    have h' : (fun z : Set.Ioi (0 : ℝ) => (((zc z)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun z : Set.Ioi (0 : ℝ) => Matrix.diagonal fun _ : Fin 3 => adeleOf ((z : ℝ)⁻¹) := funext h
    change Continuous fun z : Set.Ioi (0 : ℝ) => (((zc z)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    rw [h']
    refine (continuous_pi fun _ => continuous_adeleOf.comp ?_).matrix_diagonal
    exact (continuousOn_inv₀.comp_continuous continuous_subtype_val fun z => ne_of_gt z.2)

theorem continuousOn_zc_mul :
    ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => zc p.1 * p.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  refine ContinuousOn.mul ?_ continuousOn_snd
  exact continuousOn_zc.comp continuousOn_fst fun p hp => hp.1

theorem torus_mul_zc {y₁ y₂ z : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hz : 0 < z) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * zc z =
      WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂ * z, y₂ * z, z] i else 0) := by
  have h1 : ∀ i, ![y₁ * y₂, y₂, 1] i ≠ 0 := by
    intro i; fin_cases i <;> simp [hy₁.ne', hy₂.ne']
  have h := archRealLift3_dg_mul h1 (fun _ => ne_of_gt hz) (d' := fun _ => z)
  change WhittakerBlock.archRealLift3 (dg ![y₁ * y₂, y₂, 1]) * WhittakerBlock.archRealLift3 (dg fun _ => z) =
    WhittakerBlock.archRealLift3 (dg ![y₁ * y₂ * z, y₂ * z, z])
  rw [h]
  congr 2
  funext i
  fin_cases i <;> simp

theorem mem_pi3 {Z Y I : Set ℝ} {v : Fin 3 → ℝ} :
    v ∈ Set.pi Set.univ ![Z, Y, I] ↔ v 0 ∈ Z ∧ v 1 ∈ Y ∧ v 2 ∈ I := by
  simp [Fin.forall_fin_succ]

theorem lintegral_pi3_eq_iter (G : (Fin 3 → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ v, G v = ∫⁻ z : ℝ, ∫⁻ y : ℝ, ∫⁻ x : ℝ, G ![z, y, x] := by

  have e0 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h1 : ∫⁻ v, G v = ∫⁻ p : ℝ × (Fin 2 → ℝ), G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm p) := by
    rw [← e0.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  rw [h1, MeasureTheory.Measure.volume_eq_prod,
    lintegral_prod (fun p : ℝ × (Fin 2 → ℝ) => G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm p))
      (hG.comp (MeasurableEquiv.measurable _)).aemeasurable]
  refine lintegral_congr fun z => ?_

  have e1 := volume_preserving_finTwoArrow ℝ
  have hGz : Measurable fun w : Fin 2 → ℝ =>
      G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm (z, w)) :=
    (hG.comp (MeasurableEquiv.measurable _)).comp measurable_prodMk_left
  have h2 : ∫⁻ w : Fin 2 → ℝ, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm (z, w)) =
      ∫⁻ q : ℝ × ℝ, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
        (z, MeasurableEquiv.finTwoArrow.symm q)) := by
    rw [← e1.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  rw [h2, MeasureTheory.Measure.volume_eq_prod,
    lintegral_prod (fun q : ℝ × ℝ => G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
        (z, MeasurableEquiv.finTwoArrow.symm q))) ((hGz.comp (MeasurableEquiv.measurable _)).aemeasurable)]
  refine lintegral_congr fun y => lintegral_congr fun x => ?_
  congr 1
  funext i
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, MeasurableEquiv.finTwoArrow_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero']
  rfl

theorem setLIntegral_pi3_eq_iter (F : (Fin 3 → ℝ) → ℝ≥0∞) (hF : Measurable F) {Z Y I : Set ℝ}
    (hZ : MeasurableSet Z) (hY : MeasurableSet Y) (hI : MeasurableSet I) :
    ∫⁻ v in Set.pi Set.univ ![Z, Y, I], F v = ∫⁻ z in Z, ∫⁻ y in Y, ∫⁻ x in I, F ![z, y, x] := by
  have hS : MeasurableSet (Set.pi Set.univ ![Z, Y, I]) := by
    refine MeasurableSet.univ_pi ?_
    intro i; fin_cases i <;> simpa
  rw [← lintegral_indicator hS, lintegral_pi3_eq_iter _ (hF.indicator hS), ← lintegral_indicator hZ]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ Z
  · rw [Set.indicator_of_mem hz, ← lintegral_indicator hY]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ Y
    · rw [Set.indicator_of_mem hy, ← lintegral_indicator hI]
      refine lintegral_congr fun x => ?_
      by_cases hx : x ∈ I
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (mem_pi3.mpr ⟨hz, hy, hx⟩)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        exact fun h => hx (mem_pi3.mp h).2.2
    · rw [Set.indicator_of_notMem hy]
      have : ∀ x : ℝ, (Set.pi Set.univ ![Z, Y, I]).indicator F ![z, y, x] = 0 := fun x =>
        Set.indicator_of_notMem (fun h => hy (mem_pi3.mp h).2.1) _
      simp_rw [this, lintegral_zero]
  · rw [Set.indicator_of_notMem hz]
    have : ∀ y x : ℝ, (Set.pi Set.univ ![Z, Y, I]).indicator F ![z, y, x] = 0 := fun y x =>
      Set.indicator_of_notMem (fun h => hz (mem_pi3.mp h).1) _
    simp_rw [this, lintegral_zero]

def T (v : Fin 3 → ℝ) : Fin 3 → ℝ := ![v 2 * v 1 * v 0, v 1 * v 0, v 0]

noncomputable def Tinv (a : Fin 3 → ℝ) : Fin 3 → ℝ := ![a 2, a 1 / a 2, a 0 / a 1]

@[scoped simp] theorem T_apply_zero (v : Fin 3 → ℝ) : T v 0 = v 2 * v 1 * v 0 := rfl
@[scoped simp] theorem T_apply_one (v : Fin 3 → ℝ) : T v 1 = v 1 * v 0 := rfl
@[scoped simp] theorem T_apply_two (v : Fin 3 → ℝ) : T v 2 = v 0 := rfl
@[scoped simp] theorem Tinv_apply_zero (a : Fin 3 → ℝ) : Tinv a 0 = a 2 := rfl
@[scoped simp] theorem Tinv_apply_one (a : Fin 3 → ℝ) : Tinv a 1 = a 1 / a 2 := rfl
@[scoped simp] theorem Tinv_apply_two (a : Fin 3 → ℝ) : Tinv a 2 = a 0 / a 1 := rfl

theorem Tinv_T {v : Fin 3 → ℝ} (h0 : v 0 ≠ 0) (h1 : v 1 ≠ 0) : Tinv (T v) = v := by
  funext i
  fin_cases i
  · simp
  · simp; field_simp
  · simp; field_simp

theorem T_Tinv {a : Fin 3 → ℝ} (h1 : a 1 ≠ 0) (h2 : a 2 ≠ 0) : T (Tinv a) = a := by
  funext i
  fin_cases i
  · simp; field_simp
  · simp; field_simp
  · simp

theorem measurable_Tinv : Measurable Tinv := by
  unfold Tinv
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · simpa using measurable_pi_apply 2
  · simp
    exact (measurable_pi_apply 1).div (measurable_pi_apply 2)
  · simp
    exact (measurable_pi_apply 0).div (measurable_pi_apply 1)

def Jmat (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![v 2 * v 1, v 2 * v 0, v 1 * v 0; v 1, v 0, 0; 1, 0, 0]

theorem det_Jmat (v : Fin 3 → ℝ) : (Jmat v).det = -(v 0 ^ 2 * v 1) := by
  simp [Jmat, Matrix.det_fin_three]; ring

noncomputable def Tderiv (v : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Jmat v))

theorem Tderiv_apply (v h : Fin 3 → ℝ) : Tderiv v h = (Jmat v).mulVec h := by
  simp [Tderiv]

theorem det_Tderiv (v : Fin 3 → ℝ) : (Tderiv v).det = -(v 0 ^ 2 * v 1) := by
  rw [Tderiv, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin',
    det_Jmat]

theorem hasFDerivAt_T (v : Fin 3 → ℝ) : HasFDerivAt T (Tderiv v) v := by
  rw [hasFDerivAt_pi']
  intro i
  have h0 : HasFDerivAt (fun w : Fin 3 → ℝ => w 0) (ContinuousLinearMap.proj 0) v :=
      hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 v
  have h1 : HasFDerivAt (fun w : Fin 3 → ℝ => w 1) (ContinuousLinearMap.proj 1) v :=
      hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 v
  have h2 : HasFDerivAt (fun w : Fin 3 → ℝ => w 2) (ContinuousLinearMap.proj 2) v :=
      hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 v
  fin_cases i
  ·
    have h := (h2.mul h1).mul h0
    refine HasFDerivAt.congr_fderiv (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => rfl)) ?_
    ext w
    simp [Tderiv_apply, Jmat, dotProduct, Fin.sum_univ_three]
    ring
  · have h := h1.mul h0
    refine HasFDerivAt.congr_fderiv (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => rfl)) ?_
    ext w
    simp [Tderiv_apply, Jmat, dotProduct, Fin.sum_univ_three]
  · refine HasFDerivAt.congr_fderiv (h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => rfl)) ?_
    ext w
    simp [Tderiv_apply, Jmat, dotProduct, Fin.sum_univ_three]

theorem lintegral_image_T (S : Set (Fin 3 → ℝ)) (hS : MeasurableSet S)
    (h01 : ∀ v ∈ S, v 0 ≠ 0 ∧ v 1 ≠ 0) (g : (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ a in T '' S, g a = ∫⁻ v in S, ENNReal.ofReal (v 0 ^ 2 * |v 1|) * g (T v) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun v _ => (hasFDerivAt_T v).hasFDerivWithinAt) ?_ g]
  · refine setLIntegral_congr_fun hS fun v _ => ?_
    rw [det_Tderiv, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg _)]
  · intro v hv w hw h
    have := congrArg Tinv h
    rwa [Tinv_T (h01 v hv).1 (h01 v hv).2, Tinv_T (h01 w hw).1 (h01 w hw).2] at this

theorem image_T_eq (S : Set (Fin 3 → ℝ)) (h01 : ∀ v ∈ S, v 0 ≠ 0 ∧ v 1 ≠ 0) :
    T '' S = {a | a 1 ≠ 0 ∧ a 2 ≠ 0 ∧ Tinv a ∈ S} := by
  ext a
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · simp; exact ⟨(h01 v hv).2, (h01 v hv).1⟩
    · simpa using (h01 v hv).1
    · rw [Tinv_T (h01 v hv).1 (h01 v hv).2]; exact hv
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Tinv a, h3, T_Tinv h1 h2⟩

theorem measurableSet_image_T (S : Set (Fin 3 → ℝ)) (hS : MeasurableSet S)
    (h01 : ∀ v ∈ S, v 0 ≠ 0 ∧ v 1 ≠ 0) : MeasurableSet (T '' S) := by
  rw [image_T_eq S h01]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (measurable_Tinv hS))
  · exact (measurable_pi_apply 1) (measurableSet_singleton 0).compl
  · exact (measurable_pi_apply 2) (measurableSet_singleton 0).compl

theorem rpow_le_of_mem_Icc {u B t Tm : ℝ} (hB : 1 ≤ B) (hu : u ∈ Icc B⁻¹ B) (ht : |t| ≤ Tm) :
    u ^ t ≤ B ^ Tm := by
  have hBpos : 0 < B := by linarith
  have hupos : 0 < u := lt_of_lt_of_le (inv_pos.mpr hBpos) hu.1
  rw [Real.rpow_def_of_pos hupos, Real.rpow_def_of_pos hBpos, Real.exp_le_exp]
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have h1 : Real.log u ≤ Real.log B := Real.log_le_log hupos hu.2
  have h2 : -Real.log B ≤ Real.log u := by
    rw [← Real.log_inv]
    exact Real.log_le_log (inv_pos.mpr hBpos) hu.1
  have habs : |Real.log u| ≤ Real.log B := abs_le.mpr ⟨h2, h1⟩
  have hTm : 0 ≤ Tm := (abs_nonneg t).trans ht
  calc Real.log u * t = t * Real.log u := mul_comm _ _
    _ ≤ |t * Real.log u| := le_abs_self _
    _ = |t| * |Real.log u| := abs_mul _ _
    _ ≤ Tm * Real.log B := mul_le_mul ht habs (abs_nonneg _) hTm
    _ = Real.log B * Tm := mul_comm _ _

theorem weight_identity {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (σ : ℝ) :
    x ^ (σ - 3) * (z ^ 2 * y)⁻¹ =
      ((x * y * z) ^ (σ - 3) * (y * z) ^ (σ - 1) * z ^ (σ + 1)) * (y ^ (3 - 2 * σ) * z ^ (1 - 3 * σ)) := by
  have hxyz : 0 < x * y * z := by positivity
  have hyz : 0 < y * z := by positivity
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hxyz, Real.rpow_def_of_pos hyz, Real.rpow_def_of_pos hz,
    Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hz, Real.log_mul (by positivity) hz.ne',
    Real.log_mul hx.ne' hy.ne', Real.log_mul hy.ne' hz.ne']
  have hzy : (z ^ 2 * y)⁻¹ = Real.exp (-(2 * Real.log z + Real.log y)) := by
    rw [Real.exp_neg, Real.exp_add, show (2 : ℝ) * Real.log z = ((2 : ℕ) : ℝ) * Real.log z by norm_num,
      Real.exp_nat_mul, Real.exp_log hz, Real.exp_log hy]
  rw [hzy, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem lintegral_Ioc_rpow (c r : ℝ) (hc : 0 ≤ c) (hr : -1 < r) :
    ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (c * x ^ r) = ENNReal.ofReal (c / (r + 1)) := by
  have hint : IntegrableOn (fun x : ℝ => c * x ^ r) (Ioc 0 1) :=
    ((intervalIntegral.intervalIntegrable_rpow' hr (a := 0) (b := 1)).1).const_mul c
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr),
      Real.one_rpow, Real.zero_rpow (by linarith)]
    rw [sub_zero, mul_one_div]
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => ?_)
    exact mul_nonneg hc (Real.rpow_nonneg hx.1.le _)

theorem real_core {nm nw x y z σ τ Cp φ₀ φv b b₀ : ℝ} (hnm : 0 ≤ nm) (hnw : 0 ≤ nw)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hCp : 0 ≤ Cp) (hφ₀ : 0 < φ₀) (hφ : φ₀ ≤ φv)
    (hb : 1 ≤ b) (hb₀ : 1 < b₀) (hyI : y ∈ Icc b⁻¹ b) (hzI : z ∈ Icc b₀⁻¹ b₀) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hm_le : nm ≤ nw + Cp * x ^ τ) :
    nm ^ 2 * (x ^ (σ - 3) * (z ^ 2 * y)⁻¹) ≤
      (2 * b * b₀ ^ (5 : ℝ) / φ₀) * (nw ^ 2 * φv * ((x * y * z) ^ (σ - 3) * (y * z) ^ (σ - 1) * z ^ (σ + 1))) +
        2 * Cp ^ 2 * x ^ (2 * τ + σ - 3) * (z ^ 2 * y)⁻¹ := by
  set wσ : ℝ := (x * y * z) ^ (σ - 3) * (y * z) ^ (σ - 1) * z ^ (σ + 1) with hwσ
  have hxτ : 0 ≤ x ^ τ := Real.rpow_nonneg hx.le _
  have hm_sq : nm ^ 2 ≤ 2 * nw ^ 2 + 2 * Cp ^ 2 * x ^ (2 * τ) := by
    have hx2 : x ^ (2 * τ) = (x ^ τ) ^ 2 := by
      rw [mul_comm, Real.rpow_mul hx.le, Real.rpow_two]
    rw [hx2]
    nlinarith [mul_nonneg hCp hxτ, sq_nonneg (nw - Cp * x ^ τ)]
  have hwσ' : x ^ (σ - 3) * (z ^ 2 * y)⁻¹ = wσ * (y ^ (3 - 2 * σ) * z ^ (1 - 3 * σ)) :=
    weight_identity hx hy hz σ
  have hwσpos : 0 ≤ wσ := by positivity
  have hbnd1 : y ^ (3 - 2 * σ) ≤ b := by
    have := rpow_le_of_mem_Icc (t := 3 - 2 * σ) (Tm := 1) hb hyI (by rw [abs_le]; constructor <;> linarith)
    rwa [Real.rpow_one] at this
  have hbnd2 : z ^ (1 - 3 * σ) ≤ b₀ ^ (5 : ℝ) :=
    rpow_le_of_mem_Icc (t := 1 - 3 * σ) (Tm := 5) hb₀.le hzI (by rw [abs_le]; constructor <;> linarith)
  have hbpos : 0 < b := by linarith
  have hcorr : y ^ (3 - 2 * σ) * z ^ (1 - 3 * σ) ≤ b * b₀ ^ (5 : ℝ) :=
    mul_le_mul hbnd1 hbnd2 (Real.rpow_nonneg hz.le _) hbpos.le
  set corr : ℝ := y ^ (3 - 2 * σ) * z ^ (1 - 3 * σ) with hcorr_def
  have hcorr0 : 0 ≤ corr := by positivity
  rw [hwσ']
  have hA : 2 * nw ^ 2 * (wσ * corr) ≤ (2 * b * b₀ ^ (5 : ℝ) / φ₀) * (nw ^ 2 * φv * wσ) := by
    have h3 : wσ * corr ≤ wσ * (b * b₀ ^ (5 : ℝ)) := mul_le_mul_of_nonneg_left hcorr hwσpos
    have h5 : (1 : ℝ) ≤ φv / φ₀ := by rw [le_div_iff₀ hφ₀]; linarith
    have h7 : 2 * nw ^ 2 * (wσ * (b * b₀ ^ (5 : ℝ))) ≤ 2 * nw ^ 2 * (wσ * (b * b₀ ^ (5 : ℝ))) * (φv / φ₀) := by
      have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * nw ^ 2 * (wσ * (b * b₀ ^ (5 : ℝ))))
      linarith
    have h8 : 2 * nw ^ 2 * (wσ * (b * b₀ ^ (5 : ℝ))) * (φv / φ₀) =
        (2 * b * b₀ ^ (5 : ℝ) / φ₀) * (nw ^ 2 * φv * wσ) := by
      field_simp
    have h9 : 2 * nw ^ 2 * (wσ * corr) ≤ 2 * nw ^ 2 * (wσ * (b * b₀ ^ (5 : ℝ))) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hB' : 2 * Cp ^ 2 * x ^ (2 * τ) * (wσ * corr) = 2 * Cp ^ 2 * x ^ (2 * τ + σ - 3) * (z ^ 2 * y)⁻¹ := by
    rw [← hwσ', show 2 * τ + σ - 3 = 2 * τ + (σ - 3) by ring, Real.rpow_add hx]
    ring
  have hpos : 0 ≤ wσ * corr := by positivity
  have h10 : nm ^ 2 * (wσ * corr) ≤ (2 * nw ^ 2 + 2 * Cp ^ 2 * x ^ (2 * τ)) * (wσ * corr) :=
    mul_le_mul_of_nonneg_right hm_sq hpos
  have h11 : (2 * nw ^ 2 + 2 * Cp ^ 2 * x ^ (2 * τ)) * (wσ * corr) =
      2 * nw ^ 2 * (wσ * corr) + 2 * Cp ^ 2 * x ^ (2 * τ) * (wσ * corr) := by ring
  rw [h11, hB'] at h10
  linarith

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable def msum {n J : ℕ} (e : Fin n → ℂ) (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (y₂ : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (y₁ : ℝ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin J, c i j y₂ g * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))

theorem zc_eq (z : ℝ) : zc z = WhittakerBlock.archRealLift3 (fun i' j' => if i' = j' then z else 0) := rfl

theorem continuousOn_msum {n J : ℕ} (e : Fin n → ℂ) (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1})
    (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContinuousOn (fun v : Fin 3 → ℝ => msum e c (v 1) (zc (v 0) * k) (v 2))
      {v | 0 < v 0 ∧ 0 < v 1 ∧ 0 < v 2} := by
  unfold msum
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ ?_)
  · have hg : ContinuousOn (fun v : Fin 3 → ℝ => (v 1, zc (v 0) * k)) {v | 0 < v 0 ∧ 0 < v 1 ∧ 0 < v 2} := by
      refine ContinuousOn.prodMk (continuous_apply 1).continuousOn ?_
      refine ContinuousOn.mul ?_ continuousOn_const
      exact continuousOn_zc.comp (continuous_apply 0).continuousOn fun v hv => hv.1
    exact (hcont i j).comp hg fun v hv => by simpa using hv.2.1
  · intro v hv
    have hc2 : ContinuousAt (fun p : Fin 3 → ℝ => p 2) v := (continuous_apply 2).continuousAt
    exact (ContinuousAt.comp (f := fun p : Fin 3 → ℝ => p 2) (x := v)
      (Complex.continuousAt_ofReal_cpow_const (v 2) (e i) (Or.inr hv.2.2.ne')) hc2).continuousWithinAt
  · refine ContinuousOn.pow ?_ _
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact Real.continuousOn_log.comp (continuous_apply 2).continuousOn fun v hv => hv.2.2.ne'

end KcTorusBox
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le.KcTorusBox"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

set_option maxHeartbeats 6400000 in
open KcTorusBox in
theorem torusBox_main
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e)
    (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1})
    (τ : ℝ) (hτ : 1 / 2 < τ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ F
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ)
    (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (b₀ : ℝ) (hb₀ : 1 < b₀) (φ₀ : ℝ) (hφ₀ : 0 < φ₀)
    (hΦ : ∀ k ∈ B, ∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) → b₀⁻¹ ≤ a 2 → a 2 ≤ b₀ →
      φ₀ ≤ ‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                    AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖)
    (hZ : ∃ C' : ℝ, ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
        (letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
          ∫⁻ k in B, (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
              (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                    NumberField.StandardAddChar.psiQ F
                    (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖₊ : ℝ≥0∞) ^ 2 *
                (‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                    AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
                ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) ∂volume)
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤
            ENNReal.ofReal (C' / (σ - 1))))
    (k₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₀ : k₀ ∈ interior B) (b : ℝ) (hb : 1 ≤ b) :
    ∃ N : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact N ∧ N ∈ nhds k₀ ∧ N ⊆ B ∧ ∃ C'' : ℝ, ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
      ∫⁻ k in N, ∫⁻ z in Set.Icc b₀⁻¹ b₀, ∫⁻ y₂ in Set.Icc b⁻¹ b, ∫⁻ y₁ in Set.Ioc (0 : ℝ) 1,
          (‖∑ i : Fin n, ∑ j : Fin J,
              c i j y₂ (WhittakerBlock.archRealLift3 (fun i' j' => if i' = j' then z else 0) * k) *
                ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖₊ : ℝ≥0∞) ^ 2 *
            ENNReal.ofReal (y₁ ^ (σ - 3)) ∂volume ∂volume ∂volume
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤ ENNReal.ofReal (C'' / (σ - 1)) := by
  classical

  set W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ F with hWdef
  set μ : Measure (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ with hμ
  haveI hHaar : μ.IsHaarMeasure := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨C', hC'⟩ := hZ

  obtain ⟨N, hNnhds, hNsub, hNc⟩ := local_compact_nhds (isOpen_interior.mem_nhds hk₀)
  have hNB : N ⊆ B := hNsub.trans interior_subset
  have hNmeas : MeasurableSet N := hNc.isClosed.measurableSet
  have hμN : μ N < ⊤ := hNc.measure_lt_top

  set Kc : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => zc p.1 * p.2) '' (Icc b₀⁻¹ b₀ ×ˢ N)
    with hKc
  have hb₀pos : 0 < b₀ := by linarith
  have hb₀inv : 0 < b₀⁻¹ := inv_pos.mpr hb₀pos
  have hbpos : 0 < b := by linarith
  have hbinv : 0 < b⁻¹ := inv_pos.mpr hbpos
  have hKc_cpt : IsCompact Kc := by
    refine (isCompact_Icc.prod hNc).image_of_continuousOn (continuousOn_zc_mul.mono ?_)
    exact Set.prod_mono (fun z hz => lt_of_lt_of_le hb₀inv hz.1) (Set.subset_univ _)
  obtain ⟨C, hC⟩ := hexp Kc hKc_cpt b hb
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _

  set M₁ : ℝ := 2 * b * b₀ ^ (5 : ℝ) / φ₀ with hM₁
  have hM₁pos : 0 < M₁ := by positivity
  set R₁ : ℝ := (b₀ - b₀⁻¹) * ((b - b⁻¹) * (2 * Cp ^ 2 / (2 * τ - 2 + 1))) with hR₁
  have h2τ : 0 < 2 * τ - 2 + 1 := by linarith
  have hR₁0 : 0 ≤ R₁ := by
    have : b₀⁻¹ ≤ b₀ := by
      rw [inv_le_iff_one_le_mul₀ hb₀pos]; nlinarith
    have : b⁻¹ ≤ b := by
      rw [inv_le_iff_one_le_mul₀ hbpos]; nlinarith
    positivity
  refine ⟨N, hNc, hNnhds, hNB, M₁ * max C' 0 + R₁ * (μ N).toReal, ?_⟩
  intro σ hσ
  have hσ1 : 1 < σ := hσ.1
  have hσ2 : σ ≤ 2 := hσ.2

  set S : Set (Fin 3 → ℝ) := Set.pi Set.univ ![Icc b₀⁻¹ b₀, Icc b⁻¹ b, Ioc (0 : ℝ) 1] with hS
  have hSmeas : MeasurableSet S := by
    refine MeasurableSet.univ_pi ?_
    intro i; fin_cases i <;> simp
  have hSpos : ∀ v ∈ S, 0 < v 0 ∧ 0 < v 1 ∧ 0 < v 2 ∧ v 2 ≤ 1 ∧ v 0 ∈ Icc b₀⁻¹ b₀ ∧ v 1 ∈ Icc b⁻¹ b := by
    intro v hv
    obtain ⟨h0, h1, h2⟩ := mem_pi3.mp hv
    exact ⟨lt_of_lt_of_le hb₀inv h0.1, lt_of_lt_of_le hbinv h1.1, h2.1, h2.2, h0, h1⟩
  have hS01 : ∀ v ∈ S, v 0 ≠ 0 ∧ v 1 ≠ 0 := fun v hv => ⟨(hSpos v hv).1.ne', (hSpos v hv).2.1.ne'⟩

  set Hz : AdelicGL 3 (𝓞 ℚ) ℚ → (Fin 3 → ℝ) → ℝ≥0∞ := fun k a =>
    (‖W (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖₊ : ℝ≥0∞) ^ 2 *
      (‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
          AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
      ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) with hHz

  set Q : (Fin 3 → ℝ) → ℝ≥0∞ := fun a =>
    ENNReal.ofReal (2 * Cp ^ 2 * (a 0 / a 1) ^ (2 * τ + σ - 3) * (a 2 ^ 2 * (a 1 / a 2))⁻¹) with hQ
  have hQmeas : Measurable Q := by
    refine Measurable.ennreal_ofReal ?_
    refine Measurable.mul (Measurable.mul measurable_const ?_) ?_
    · exact ((measurable_pi_apply 0).div (measurable_pi_apply 1)).pow_const _
    · exact (((measurable_pi_apply 2).pow_const _).mul ((measurable_pi_apply 1).div (measurable_pi_apply 2))).inv

  have hstep : ∀ k ∈ N,
      (∫⁻ z in Set.Icc b₀⁻¹ b₀, ∫⁻ y₂ in Set.Icc b⁻¹ b, ∫⁻ y₁ in Set.Ioc (0 : ℝ) 1,
          (‖msum e c y₂ (zc z * k) y₁‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (y₁ ^ (σ - 3))) ≤
        ENNReal.ofReal M₁ * (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)), Hz k a) +
          ENNReal.ofReal R₁ := by
    intro k hk

    set U : Set (Fin 3 → ℝ) := {v | 0 < v 0 ∧ 0 < v 1 ∧ 0 < v 2} with hU
    have hUopen : IsOpen U := by
      have h0 : IsOpen {v : Fin 3 → ℝ | 0 < v 0} := isOpen_lt continuous_const (continuous_apply 0)
      have h1 : IsOpen {v : Fin 3 → ℝ | 0 < v 1} := isOpen_lt continuous_const (continuous_apply 1)
      have h2 : IsOpen {v : Fin 3 → ℝ | 0 < v 2} := isOpen_lt continuous_const (continuous_apply 2)
      exact (h0.inter (h1.inter h2))
    have hSU : S ⊆ U := fun v hv => ⟨(hSpos v hv).1, (hSpos v hv).2.1, (hSpos v hv).2.2.1⟩
    set mt : (Fin 3 → ℝ) → ℂ := U.piecewise (fun v => msum e c (v 1) (zc (v 0) * k) (v 2)) 0 with hmt
    have hmt_meas : Measurable mt :=
      ContinuousOn.measurable_piecewise (continuousOn_msum e c hcont k) continuousOn_const hUopen.measurableSet
    have hmt_eq : ∀ v ∈ S, mt v = msum e c (v 1) (zc (v 0) * k) (v 2) := fun v hv =>
      Set.piecewise_eq_of_mem _ _ _ (hSU hv)
    set Fm : (Fin 3 → ℝ) → ℝ≥0∞ := fun v => (‖mt v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (v 2 ^ (σ - 3)) with hFm
    have hFm_meas : Measurable Fm :=
      ((measurable_coe_nnreal_ennreal.comp hmt_meas.nnnorm).pow_const 2).mul
        ((measurable_pi_apply 2).pow_const _).ennreal_ofReal
    have hFm_eq : ∀ v ∈ S, Fm v = (‖msum e c (v 1) (zc (v 0) * k) (v 2)‖₊ : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (v 2 ^ (σ - 3)) := fun v hv => by
      simp only [hFm, hmt_eq v hv]

    have hiter : (∫⁻ z in Set.Icc b₀⁻¹ b₀, ∫⁻ y₂ in Set.Icc b⁻¹ b, ∫⁻ y₁ in Set.Ioc (0 : ℝ) 1,
          (‖msum e c y₂ (zc z * k) y₁‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (y₁ ^ (σ - 3))) = ∫⁻ v in S, Fm v := by
      rw [hS, setLIntegral_pi3_eq_iter Fm hFm_meas measurableSet_Icc measurableSet_Icc measurableSet_Ioc]
      refine setLIntegral_congr_fun measurableSet_Icc fun z hz => ?_
      refine setLIntegral_congr_fun measurableSet_Icc fun y hy => ?_
      refine setLIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      rw [hFm_eq _ (mem_pi3.mpr ⟨by simpa using hz, by simpa using hy, by simpa using hx⟩)]
      simp

    set g : (Fin 3 → ℝ) → ℝ≥0∞ := fun a => Fm (Tinv a) * ENNReal.ofReal ((a 2 ^ 2 * (a 1 / a 2))⁻¹) with hg
    have hsub : ∫⁻ v in S, Fm v = ∫⁻ a in T '' S, g a := by
      rw [lintegral_image_T S hSmeas hS01 g]
      refine setLIntegral_congr_fun hSmeas fun v hv => ?_
      obtain ⟨h0, h1, -, -, -, -⟩ := hSpos v hv
      simp only [hg]
      rw [Tinv_T h0.ne' h1.ne', T_apply_two, T_apply_one, abs_of_pos h1]
      have hjac : v 0 ^ 2 * (v 1 * v 0 / v 0) = v 0 ^ 2 * v 1 := by field_simp
      rw [hjac, mul_comm (Fm v), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

    have hpt : ∀ a ∈ T '' S, g a ≤ ENNReal.ofReal M₁ * Hz k a + Q a := by
      rintro a ⟨v, hv, rfl⟩
      obtain ⟨h0, h1, h2, h2', hz, hy⟩ := hSpos v hv

      have hkk : zc (v 0) * k ∈ Kc := ⟨(v 0, k), ⟨hz, hk⟩, rfl⟩
      have hexp' := hC _ hkk (v 1) hy.1 hy.2 (v 2) h2 h2'

      have htor : WhittakerBlock.archRealLift3 (fun i j => if i = j then ![v 2 * v 1, v 1, 1] i else 0) *
          (zc (v 0) * k) = WhittakerBlock.archRealLift3 (fun i j => if i = j then T v i else 0) * k := by
        rw [← mul_assoc, torus_mul_zc h2 h1 h0]
        rfl
      rw [htor] at hexp'
      change ‖W (WhittakerBlock.archRealLift3 (fun i j => if i = j then T v i else 0) * k) -
        msum e c (v 1) (zc (v 0) * k) (v 2)‖ ≤ C * v 2 ^ τ at hexp'
      set w := W (WhittakerBlock.archRealLift3 (fun i j => if i = j then T v i else 0) * k) with hw
      set m := msum e c (v 1) (zc (v 0) * k) (v 2) with hm
      set φv : ℝ := ‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then T v i else 0) * k :
          AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖ with hφv
      have hφ : φ₀ ≤ φv := by
        refine hΦ k (hNB hk) (T v) ?_ ?_ ?_
        · intro i; fin_cases i <;> simp <;> positivity
        · simpa using hz.1
        · simpa using hz.2
      have hφvpos : 0 < φv := lt_of_lt_of_le hφ₀ hφ

      have hxτ : 0 ≤ v 2 ^ τ := Real.rpow_nonneg h2.le _
      have hm_le : ‖m‖ ≤ ‖w‖ + Cp * v 2 ^ τ := by
        have h1' : ‖m‖ ≤ ‖w‖ + ‖w - m‖ := by
          calc ‖m‖ = ‖w - (w - m)‖ := by rw [sub_sub_cancel]
            _ ≤ ‖w‖ + ‖w - m‖ := norm_sub_le _ _
        have h2'' : C * v 2 ^ τ ≤ Cp * v 2 ^ τ := mul_le_mul_of_nonneg_right (le_max_left _ _) hxτ
        linarith
      set wσ : ℝ := (T v) 0 ^ (σ - 3) * (T v) 1 ^ (σ - 1) * (T v) 2 ^ (σ + 1) with hwσ
      have hwσT : wσ = (v 2 * v 1 * v 0) ^ (σ - 3) * (v 1 * v 0) ^ (σ - 1) * v 0 ^ (σ + 1) := by
        rw [hwσ, T_apply_zero, T_apply_one, T_apply_two]

      have hgTv : g (T v) = ENNReal.ofReal (‖m‖ ^ 2 * (v 2 ^ (σ - 3) * (v 0 ^ 2 * v 1)⁻¹)) := by
        simp only [hg]
        rw [Tinv_T h0.ne' h1.ne', hFm_eq v hv, T_apply_two, T_apply_one, nnnorm_sq_eq_ofReal',
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : v 0 ^ 2 * (v 1 * v 0 / v 0) = v 0 ^ 2 * v 1 := by field_simp
        rw [this]; ring

      have hreal : ‖m‖ ^ 2 * (v 2 ^ (σ - 3) * (v 0 ^ 2 * v 1)⁻¹) ≤
          M₁ * (‖w‖ ^ 2 * φv * wσ) + 2 * Cp ^ 2 * v 2 ^ (2 * τ + σ - 3) * (v 0 ^ 2 * v 1)⁻¹ := by
        have h := real_core (norm_nonneg m) (norm_nonneg w) h2 h1 h0 hCp0 hφ₀ hφ hb hb₀ hy hz hσ1 hσ2 hm_le
        have e1 : v 2 * v 1 * v 0 = v 2 * v 1 * v 0 := rfl
        rw [hwσT, hM₁]
        have e2 : (v 2 * v 1 * v 0) ^ (σ - 3) * (v 1 * v 0) ^ (σ - 1) * v 0 ^ (σ + 1) =
            (v 2 * v 1 * v 0) ^ (σ - 3) * (v 1 * v 0) ^ (σ - 1) * v 0 ^ (σ + 1) := rfl
        simpa only [mul_comm (v 1) (v 0), mul_comm (v 0 ^ 2) (v 1)] using h

      rw [hgTv]
      have hφv0 : 0 ≤ φv := le_of_lt hφvpos
      have hwσ0 : 0 ≤ wσ := by rw [hwσT]; positivity
      have hHz' : ENNReal.ofReal M₁ * Hz k (T v) = ENNReal.ofReal (M₁ * (‖w‖ ^ 2 * φv * wσ)) := by
        simp only [hHz]
        rw [nnnorm_sq_eq_ofReal', coe_nnnorm_ennreal, ← hw, ← hφv, ← hwσ,
          ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hφv0),
          ← ENNReal.ofReal_mul hM₁pos.le]
      have hQ' : Q (T v) = ENNReal.ofReal (2 * Cp ^ 2 * v 2 ^ (2 * τ + σ - 3) * (v 0 ^ 2 * v 1)⁻¹) := by
        simp only [hQ, T_apply_zero, T_apply_one, T_apply_two]
        congr 1
        have : v 2 * v 1 * v 0 / (v 1 * v 0) = v 2 := by field_simp
        have h' : v 0 ^ 2 * (v 1 * v 0 / v 0) = v 0 ^ 2 * v 1 := by field_simp
        rw [this, h']
      rw [hHz', hQ', ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal hreal

    have hTS_meas : MeasurableSet (T '' S) := measurableSet_image_T S hSmeas hS01
    have hTS_sub : T '' S ⊆ Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)) := by
      rintro a ⟨v, hv, rfl⟩
      obtain ⟨h0, h1, h2, -, -, -⟩ := hSpos v hv
      simp only [Set.mem_univ_pi, Set.mem_Ioi]
      intro i; fin_cases i <;> simp <;> positivity
    have h5 : ∫⁻ a in T '' S, g a ≤ ENNReal.ofReal M₁ * (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)), Hz k a) +
        ∫⁻ a in T '' S, Q a := by
      calc ∫⁻ a in T '' S, g a ≤ ∫⁻ a in T '' S, (ENNReal.ofReal M₁ * Hz k a + Q a) :=
            setLIntegral_mono' hTS_meas hpt
        _ = ENNReal.ofReal M₁ * (∫⁻ a in T '' S, Hz k a) + ∫⁻ a in T '' S, Q a := by
            rw [lintegral_add_right _ hQmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ _ := add_le_add (mul_le_mul_right (lintegral_mono_set hTS_sub) _) le_rfl

    have h6 : ∫⁻ a in T '' S, Q a ≤ ENNReal.ofReal R₁ := by
      rw [lintegral_image_T S hSmeas hS01 Q]
      have hQT : ∀ v ∈ S, ENNReal.ofReal (v 0 ^ 2 * |v 1|) * Q (T v) =
          ENNReal.ofReal (2 * Cp ^ 2 * v 2 ^ (2 * τ + σ - 3)) := by
        intro v hv
        obtain ⟨h0, h1, h2, -, -, -⟩ := hSpos v hv
        simp only [hQ, T_apply_zero, T_apply_one, T_apply_two]
        rw [abs_of_pos h1, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      rw [setLIntegral_congr_fun hSmeas hQT]
      calc ∫⁻ v in S, ENNReal.ofReal (2 * Cp ^ 2 * v 2 ^ (2 * τ + σ - 3))
          ≤ ∫⁻ v in S, ENNReal.ofReal (2 * Cp ^ 2 * v 2 ^ (2 * τ - 2)) := by
            refine setLIntegral_mono' hSmeas fun v hv => ?_
            obtain ⟨-, -, h2, h2', -, -⟩ := hSpos v hv
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
            exact Real.rpow_le_rpow_of_exponent_ge h2 h2' (by linarith)
        _ = ∫⁻ z in Set.Icc b₀⁻¹ b₀, ∫⁻ y in Set.Icc b⁻¹ b, ∫⁻ x in Set.Ioc (0 : ℝ) 1,
              ENNReal.ofReal (2 * Cp ^ 2 * x ^ (2 * τ - 2)) := by
            rw [hS, setLIntegral_pi3_eq_iter _ ?_ measurableSet_Icc measurableSet_Icc measurableSet_Ioc]
            · simp
            · exact (measurable_const.mul ((measurable_pi_apply 2).pow_const _)).ennreal_ofReal
        _ = ENNReal.ofReal R₁ := by
            rw [lintegral_Ioc_rpow _ _ (by positivity) (by linarith), setLIntegral_const, setLIntegral_const,
              Real.volume_Icc, Real.volume_Icc, hR₁, ENNReal.ofReal_mul (by
                rw [sub_nonneg, inv_le_iff_one_le_mul₀ hb₀pos]; nlinarith),
              ENNReal.ofReal_mul (by rw [sub_nonneg, inv_le_iff_one_le_mul₀ hbpos]; nlinarith)]
            ring

    rw [hiter, hsub]
    exact h5.trans (add_le_add le_rfl h6)

  have hstep' : ∀ k ∈ N,
      (∫⁻ z in Set.Icc b₀⁻¹ b₀, ∫⁻ y₂ in Set.Icc b⁻¹ b, ∫⁻ y₁ in Set.Ioc (0 : ℝ) 1,
          (‖∑ i : Fin n, ∑ j : Fin J,
              c i j y₂ (WhittakerBlock.archRealLift3 (fun i' j' => if i' = j' then z else 0) * k) *
                ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖₊ : ℝ≥0∞) ^ 2 *
            ENNReal.ofReal (y₁ ^ (σ - 3))) ≤
        ENNReal.ofReal M₁ * (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)), Hz k a) +
          ENNReal.ofReal R₁ := fun k hk => hstep k hk
  calc (∫⁻ k in N, ∫⁻ z in Set.Icc b₀⁻¹ b₀, ∫⁻ y₂ in Set.Icc b⁻¹ b, ∫⁻ y₁ in Set.Ioc (0 : ℝ) 1,
          (‖∑ i : Fin n, ∑ j : Fin J,
              c i j y₂ (WhittakerBlock.archRealLift3 (fun i' j' => if i' = j' then z else 0) * k) *
                ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖₊ : ℝ≥0∞) ^ 2 *
            ENNReal.ofReal (y₁ ^ (σ - 3)) ∂volume ∂volume ∂volume ∂μ)
      ≤ ∫⁻ k in N, (ENNReal.ofReal M₁ * (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)), Hz k a) +
          ENNReal.ofReal R₁) ∂μ := setLIntegral_mono' hNmeas hstep'
    _ = ENNReal.ofReal M₁ * (∫⁻ k in N, ∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)), Hz k a ∂volume ∂μ) +
          ENNReal.ofReal R₁ * μ N := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal M₁ * ENNReal.ofReal (C' / (σ - 1)) + ENNReal.ofReal R₁ * μ N := by
        gcongr
        exact (lintegral_mono_set hNB).trans (hC' σ hσ)
    _ ≤ ENNReal.ofReal ((M₁ * max C' 0 + R₁ * (μ N).toReal) / (σ - 1)) := by
        have hσpos : 0 < σ - 1 := by linarith
        set t : ℝ := (μ N).toReal with ht
        have hμN' : μ N = ENNReal.ofReal t := (ENNReal.ofReal_toReal hμN.ne).symm
        rw [hμN', ← ENNReal.ofReal_mul hR₁0]
        have h1 : ENNReal.ofReal M₁ * ENNReal.ofReal (C' / (σ - 1)) ≤ ENNReal.ofReal (M₁ * (max C' 0 / (σ - 1))) := by
          rw [← ENNReal.ofReal_mul hM₁pos.le]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hM₁pos.le)
          exact div_le_div_of_nonneg_right (le_max_left _ _) hσpos.le
        have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
        have h2 : ENNReal.ofReal (R₁ * t) ≤ ENNReal.ofReal (R₁ * t / (σ - 1)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [le_div_iff₀ hσpos]
          have : 0 ≤ R₁ * t := mul_nonneg hR₁0 ht0
          nlinarith
        refine (add_le_add h1 h2).trans ?_
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        field_simp

set_option maxHeartbeats 3200000 in
theorem solution
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e)
    (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1})
    (τ : ℝ) (hτ : 1 / 2 < τ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ F
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ)
    (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (b₀ : ℝ) (hb₀ : 1 < b₀) (φ₀ : ℝ) (hφ₀ : 0 < φ₀)
    (hΦ : ∀ k ∈ B, ∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) → b₀⁻¹ ≤ a 2 → a 2 ≤ b₀ →
      φ₀ ≤ ‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                    AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖)
    (hZ : ∃ C' : ℝ, ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
        (letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
          ∫⁻ k in B, (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
              (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                    NumberField.StandardAddChar.psiQ F
                    (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖₊ : ℝ≥0∞) ^ 2 *
                (‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                    AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
                ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) ∂volume)
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤
            ENNReal.ofReal (C' / (σ - 1))))
    (k₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₀ : k₀ ∈ interior B) (b : ℝ) (hb : 1 ≤ b) :
    ∃ N : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact N ∧ N ∈ nhds k₀ ∧ N ⊆ B ∧ ∃ C'' : ℝ, ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
      ∫⁻ k in N, ∫⁻ z in Set.Icc b₀⁻¹ b₀, ∫⁻ y₂ in Set.Icc b⁻¹ b, ∫⁻ y₁ in Set.Ioc (0 : ℝ) 1,
          (‖∑ i : Fin n, ∑ j : Fin J,
              c i j y₂ (WhittakerBlock.archRealLift3 (fun i' j' => if i' = j' then z else 0) * k) *
                ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖₊ : ℝ≥0∞) ^ 2 *
            ENNReal.ofReal (y₁ ^ (σ - 3)) ∂volume ∂volume ∂volume
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤ ENNReal.ofReal (C'' / (σ - 1)) :=
  torusBox_main F n J e he c hcont τ hτ hexp B Φ b₀ hb₀ φ₀ hφ₀ hΦ hZ k₀ hk₀ b hb

end S_LanglandsTunnell_CubicInduction_exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_nhds_lintegral_sum_cpow_log_sq_le_of_lintegral_torus_whittaker3_sq_le (solution)
