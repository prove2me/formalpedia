-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b5da6b65-33a2-515c-bb99-c2aa478095cc

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_contDiff_hasCompactSupport_eq_integral_archRealLift3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
p2m_attr_erase "instance" "WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.componentAt3 CubicInduction.archComponent3 CubicInduction.orth3 CubicInduction.archPlaceComponent3 CubicInduction.matrixSize CubicInduction.matrixSize_nonneg CubicInduction.matrixSupSize CubicInduction.archGauge3 CubicInduction.finGauge3 CubicInduction.gauge3 CubicInduction.one_le_gauge3 CubicInduction.gauge3_pos CubicInduction.one_le_archGauge3 CubicInduction.IsModerateGrowth3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL componentAt3 archComponent3 orth3 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 one_le_gauge3 gauge3_pos one_le_archGauge3 IsModerateGrowth3 exists_contDiff_hasCompactSupport_eq_integral_archRealLift3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal
p2m_open "LanglandsTunnell.CubicInduction.WhittakerBlock"

private def realToArch : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v =>
    ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (NumberField.IsTotallyReal.isReal v)).symm :
      ℝ →+* v.Completion)

private theorem archRealMat3_eq (e : Matrix (Fin 3) (Fin 3) ℝ) :
    WhittakerBlock.archRealMat3 e = AutomorphicForm.archMatrixInclN (Fin 3) ℚ (realToArch.mapMatrix e) :=
  rfl

private theorem archRealMat3_mul (e e' : Matrix (Fin 3) (Fin 3) ℝ) :
    WhittakerBlock.archRealMat3 (e * e') = WhittakerBlock.archRealMat3 e * WhittakerBlock.archRealMat3 e' := by
  rw [archRealMat3_eq, archRealMat3_eq, archRealMat3_eq, _root_.map_mul, AutomorphicForm.archMatrixInclN_mul]

private theorem archRealMat3_one : WhittakerBlock.archRealMat3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  rw [archRealMat3_eq, _root_.map_one, AutomorphicForm.archMatrixInclN_one]

private def archUnit (e e' : Matrix (Fin 3) (Fin 3) ℝ) (h : e * e' = 1) (h' : e' * e = 1) : AdelicGL 3 (𝓞 ℚ) ℚ where
  val := WhittakerBlock.archRealMat3 e
  inv := WhittakerBlock.archRealMat3 e'
  val_inv := by rw [← archRealMat3_mul, h, archRealMat3_one]
  inv_val := by rw [← archRealMat3_mul, h', archRealMat3_one]

private theorem archRealLift3_eq_archUnit (e e' : Matrix (Fin 3) (Fin 3) ℝ) (h : e * e' = 1) (h' : e' * e = 1) :
    WhittakerBlock.archRealLift3 e = archUnit e e' h h' := by
  have hu : IsUnit (WhittakerBlock.archRealMat3 e) := ⟨archUnit e e' h h', rfl⟩
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos hu]
  exact Units.ext hu.unit_spec

private theorem coe_archRealLift3_of_inv (e e' : Matrix (Fin 3) (Fin 3) ℝ) (h : e * e' = 1) (h' : e' * e = 1) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  rw [archRealLift3_eq_archUnit e e' h h']
  rfl

private theorem archRealLift3_mul_of_inv (e₁ e₁' e₂ e₂' : Matrix (Fin 3) (Fin 3) ℝ) (h₁ : e₁ * e₁' = 1)
    (h₁' : e₁' * e₁ = 1) (h₂ : e₂ * e₂' = 1) (h₂' : e₂' * e₂ = 1) :
    WhittakerBlock.archRealLift3 (e₁ * e₂) =
      WhittakerBlock.archRealLift3 e₁ * WhittakerBlock.archRealLift3 e₂ := by
  have h₁₂ : (e₁ * e₂) * (e₂' * e₁') = 1 := by
    rw [_root_.mul_assoc, ← _root_.mul_assoc e₂, h₂, _root_.one_mul, h₁]
  have h₁₂' : (e₂' * e₁') * (e₁ * e₂) = 1 := by
    rw [_root_.mul_assoc, ← _root_.mul_assoc e₁', h₁', _root_.one_mul, h₂']
  refine Units.ext ?_
  rw [coe_archRealLift3_of_inv _ _ h₁₂ h₁₂', Units.val_mul, coe_archRealLift3_of_inv _ _ h₁ h₁',
    coe_archRealLift3_of_inv _ _ h₂ h₂', archRealMat3_mul]

private def rootMat (i j : Fin 3) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

private theorem adeleMatrix_ext {A B : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix A =
      (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix B)
    (h₂ : (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix A =
      (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix B) :
    A = B := by
  ext i j
  refine Prod.ext ?_ ?_
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) => M i j) h₁
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) => M i j) h₂

private theorem adeleArch_mapMatrix_archRealMat3 (e : Matrix (Fin 3) (Fin 3) ℝ) :
    (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (WhittakerBlock.archRealMat3 e) = realToArch.mapMatrix e :=
  Matrix.ext fun _ _ => rfl

private theorem adeleFin_mapMatrix_archRealMat3 (e : Matrix (Fin 3) (Fin 3) ℝ) :
    (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (WhittakerBlock.archRealMat3 e) = 1 :=
  Matrix.ext fun _ _ => rfl

private theorem mul_archRealLift3_comm (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk : LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ k = 1) (e e' : Matrix (Fin 3) (Fin 3) ℝ)
    (h : e * e' = 1) (h' : e' * e = 1) :
    k * WhittakerBlock.archRealLift3 e = WhittakerBlock.archRealLift3 e * k := by
  have hk' : (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
      (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := congrArg Units.val hk
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_archRealLift3_of_inv _ _ h h']
  refine adeleMatrix_ext ?_ ?_
  · rw [_root_.map_mul, _root_.map_mul, hk', adeleArch_mapMatrix_archRealMat3, _root_.one_mul, _root_.mul_one]
  · rw [_root_.map_mul, _root_.map_mul, adeleFin_mapMatrix_archRealMat3, _root_.one_mul, _root_.mul_one]

private def gaugeEntrySum {L : Type*} [NormedField L] (M : Matrix (Fin 3) (Fin 3) L) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ‖M i j‖

private theorem gaugeEntrySum_nonneg {L : Type*} [NormedField L] (M : Matrix (Fin 3) (Fin 3) L) :
    0 ≤ gaugeEntrySum M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem gaugeEntrySum_mul_le {L : Type*} [NormedField L] (M N : Matrix (Fin 3) (Fin 3) L) :
    gaugeEntrySum (M * N) ≤ gaugeEntrySum M * gaugeEntrySum N := by
  unfold gaugeEntrySum
  calc ∑ i, ∑ j, ‖(M * N) i j‖
      ≤ ∑ i, ∑ j, ∑ l, ‖M i l‖ * ‖N l j‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)
    _ = ∑ i, ∑ l, ‖M i l‖ * ∑ j, ‖N l j‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ l, ‖M i l‖ * ∑ l', ∑ j, ‖N l' j‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun l' => ∑ j, ‖N l' j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ l)
    _ = (∑ i, ∑ l, ‖M i l‖) * ∑ l', ∑ j, ‖N l' j‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]

private theorem gaugeMatrixSize_eq {L : Type*} [NormedField L] (k : GL (Fin 3) L) :
    LanglandsTunnell.CubicInduction.matrixSize k = gaugeEntrySum (k : Matrix (Fin 3) (Fin 3) L) +
      gaugeEntrySum ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
  unfold LanglandsTunnell.CubicInduction.matrixSize gaugeEntrySum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib

private theorem gaugeMatrixSize_mul_le {L : Type*} [NormedField L] (k₁ k₂ : GL (Fin 3) L) :
    LanglandsTunnell.CubicInduction.matrixSize (k₁ * k₂) ≤
      LanglandsTunnell.CubicInduction.matrixSize k₁ * LanglandsTunnell.CubicInduction.matrixSize k₂ := by
  rw [gaugeMatrixSize_eq, gaugeMatrixSize_eq, gaugeMatrixSize_eq, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  have h₁ := gaugeEntrySum_mul_le (k₁ : Matrix (Fin 3) (Fin 3) L) (k₂ : Matrix (Fin 3) (Fin 3) L)
  have h₂ := gaugeEntrySum_mul_le ((k₂⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
    ((k₁⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
  have n₁ := gaugeEntrySum_nonneg (k₁ : Matrix (Fin 3) (Fin 3) L)
  have n₂ := gaugeEntrySum_nonneg (k₂ : Matrix (Fin 3) (Fin 3) L)
  have n₃ := gaugeEntrySum_nonneg ((k₁⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
  have n₄ := gaugeEntrySum_nonneg ((k₂⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
  nlinarith [mul_nonneg n₁ n₄, mul_nonneg n₃ n₂]

private theorem gaugeMatrixSize_le_of_forall_le {L : Type*} [NormedField L] (k : GL (Fin 3) L) {C C' : ℝ}
    (hC : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ C)
    (hC' : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ C') :
    LanglandsTunnell.CubicInduction.matrixSize k ≤ 9 * (C + C') := by
  unfold LanglandsTunnell.CubicInduction.matrixSize
  calc ∑ i : Fin 3, ∑ j : Fin 3, (‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ +
        ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖)
      ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (C + C') :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => add_le_add (hC i j) (hC' i j)
    _ = 9 * (C + C') := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

private theorem gaugeArch_mul_le (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    LanglandsTunnell.CubicInduction.archGauge3 ℚ (g * h) ≤
      LanglandsTunnell.CubicInduction.archGauge3 ℚ g * LanglandsTunnell.CubicInduction.archGauge3 ℚ h := by
  unfold LanglandsTunnell.CubicInduction.archGauge3
  have hA : 0 ≤ ∑ w : NumberField.InfinitePlace ℚ, LanglandsTunnell.CubicInduction.matrixSize
      (LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w g) :=
    Finset.sum_nonneg fun w _ => LanglandsTunnell.CubicInduction.matrixSize_nonneg _
  have hB : 0 ≤ ∑ w : NumberField.InfinitePlace ℚ, LanglandsTunnell.CubicInduction.matrixSize
      (LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w h) :=
    Finset.sum_nonneg fun w _ => LanglandsTunnell.CubicInduction.matrixSize_nonneg _
  have h1 : ∑ w : NumberField.InfinitePlace ℚ, LanglandsTunnell.CubicInduction.matrixSize
      (LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w (g * h)) ≤
      ∑ w : NumberField.InfinitePlace ℚ, LanglandsTunnell.CubicInduction.matrixSize
        (LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w g) *
        ∑ w' : NumberField.InfinitePlace ℚ, LanglandsTunnell.CubicInduction.matrixSize
          (LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w' h) := by
    refine Finset.sum_le_sum fun w _ => ?_
    rw [_root_.map_mul]
    refine (gaugeMatrixSize_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_
      (LanglandsTunnell.CubicInduction.matrixSize_nonneg _))
    exact Finset.single_le_sum (f := fun w' => LanglandsTunnell.CubicInduction.matrixSize
      (LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w' h))
      (fun _ _ => LanglandsTunnell.CubicInduction.matrixSize_nonneg _) (Finset.mem_univ w)
  rw [← Finset.sum_mul] at h1
  nlinarith [mul_nonneg hA hB]

private theorem gaugeUltrametric (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    IsUltrametricDist (v.adicCompletion ℚ) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (Valued.isNonarchimedean_norm (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)))

private theorem gaugeNNNorm_le_one_of_mem (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    {t : v.adicCompletion ℚ} (ht : t ∈ v.adicCompletionIntegers ℚ) : ‖t‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact Valued.toNormedField.norm_le_one_iff.mpr ht

private theorem gaugeFin_congr {g g' : AdelicGL 3 (𝓞 ℚ) ℚ}
    (h : ∀ v,
      LanglandsTunnell.CubicInduction.matrixSupSize (LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ v g) =
      LanglandsTunnell.CubicInduction.matrixSupSize (LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ v g')) :
    LanglandsTunnell.CubicInduction.finGauge3 ℚ g = LanglandsTunnell.CubicInduction.finGauge3 ℚ g' := by
  unfold LanglandsTunnell.CubicInduction.finGauge3
  exact finprod_congr fun v => by rw [h v]

private theorem gaugeFin_nonneg (g : AdelicGL 3 (𝓞 ℚ) ℚ) : 0 ≤ LanglandsTunnell.CubicInduction.finGauge3 ℚ g := by
  unfold LanglandsTunnell.CubicInduction.finGauge3
  exact finprod_nonneg fun v => NNReal.coe_nonneg _

private theorem gaugeComponentAt3_archRealLift3 (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (e e' : Matrix (Fin 3) (Fin 3) ℝ) (h : e * e' = 1) (h' : e' * e = 1) :
    LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ v (WhittakerBlock.archRealLift3 e) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_one]
  show (NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v) ((NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ)
    (((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)) =
    (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
  rw [coe_archRealLift3_of_inv e e' h h', NumberField.AdelicLevel.finAdeleEval_apply,
    NumberField.AdelicLevel.adeleFin_apply]
  change ((1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) v =
    (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem gaugeFin_mul_archRealLift3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) (e e' : Matrix (Fin 3) (Fin 3) ℝ) (h : e * e' = 1)
    (h' : e' * e = 1) :
    LanglandsTunnell.CubicInduction.finGauge3 ℚ (g * WhittakerBlock.archRealLift3 e) =
      LanglandsTunnell.CubicInduction.finGauge3 ℚ g :=
  gaugeFin_congr fun v => by rw [_root_.map_mul, gaugeComponentAt3_archRealLift3 v e e' h h', _root_.mul_one]

private theorem gaugeNorm_realSymm (w : NumberField.InfinitePlace ℚ) (t : ℝ) :
    ‖(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (NumberField.IsTotallyReal.isReal w)).symm t‖ =
      |t| := by
  have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (NumberField.IsTotallyReal.isReal w)).norm_map_of_map_zero (_root_.map_zero _)
    ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (NumberField.IsTotallyReal.isReal w)).symm t)
  rw [← h, ← NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply,
    Real.norm_eq_abs]

private theorem gaugeNorm_archPlace_archRealLift3 (w : NumberField.InfinitePlace ℚ) (e e' : Matrix (Fin 3) (Fin 3) ℝ)
    (h : e * e' = 1) (h' : e' * e = 1) (i j : Fin 3) :
    ‖(LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w (WhittakerBlock.archRealLift3 e) :
        Matrix (Fin 3) (Fin 3) w.Completion) i j‖ = |e i j| ∧
      ‖(((LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w (WhittakerBlock.archRealLift3 e))⁻¹ :
        GL (Fin 3) w.Completion) : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ = |e' i j| := by
  rw [← _root_.map_inv, archRealLift3_eq_archUnit e e' h h']
  exact ⟨gaugeNorm_realSymm w (e i j), gaugeNorm_realSymm w (e' i j)⟩

private theorem gaugeArch_archRealLift3_le (e e' : Matrix (Fin 3) (Fin 3) ℝ) (h : e * e' = 1) (h' : e' * e = 1)
    {C C' : ℝ} (hC : ∀ i j, |e i j| ≤ C) (hC' : ∀ i j, |e' i j| ≤ C') :
    LanglandsTunnell.CubicInduction.archGauge3 ℚ (WhittakerBlock.archRealLift3 e) ≤ 1 + 9 * (C + C') := by
  unfold LanglandsTunnell.CubicInduction.archGauge3
  rw [Fintype.sum_unique]
  refine add_le_add le_rfl (gaugeMatrixSize_le_of_forall_le
    (LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ default (WhittakerBlock.archRealLift3 e))
    (fun i j => ?_) (fun i j => ?_))
  · rw [(gaugeNorm_archPlace_archRealLift3 default e e' h h' i j).1]
    exact hC i j
  · rw [(gaugeNorm_archPlace_archRealLift3 default e e' h h' i j).2]
    exact hC' i j

private theorem continuous_mul_kernel {E : Type*} [TopologicalSpace E] {U : Set E} (hU : IsOpen U) {F : E → ℂ}
    (hF : ContinuousOn F U) {K : Set E} (hK : IsClosed K) (hKU : K ⊆ U) {β : E → ℂ} (hβ : Continuous β)
    (hsupp : ∀ e, e ∉ K → β e = 0) : Continuous fun e => F e * β e := by
  rw [continuous_iff_continuousAt]
  intro e
  by_cases he : e ∈ U
  · exact (hF.continuousAt (hU.mem_nhds he)).mul hβ.continuousAt
  · have heK : e ∈ Kᶜ := fun h => he (hKU h)
    have h0 : (fun _ : E => (0 : ℂ)) =ᶠ[nhds e] fun x => F x * β x := by
      filter_upwards [hK.isOpen_compl.mem_nhds heK] with x hx
      simp [hsupp x hx]
    exact continuousAt_const.congr h0

private theorem hasDerivAt_integral_mul_kernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {U : Set E} (hU : IsOpen U) {F : E → ℂ}
    (hF : ContinuousOn F U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) {δ : ℝ} (hδ : 0 < δ) (β β' : ℝ → E → ℂ)
    (hβ : ContinuousOn (Function.uncurry β) (Set.Ioo (-δ) δ ×ˢ Set.univ))
    (hβ' : ContinuousOn (Function.uncurry β') (Set.Ioo (-δ) δ ×ˢ Set.univ))
    (hd : ∀ s ∈ Set.Ioo (-δ) δ, ∀ e : E, HasDerivAt (fun t => β t e) (β' s e) s)
    (hsupp : ∀ s ∈ Set.Ioo (-δ) δ, ∀ e, e ∉ K → β s e = 0)
    (hsupp' : ∀ s ∈ Set.Ioo (-δ) δ, ∀ e, e ∉ K → β' s e = 0) :
    HasDerivAt (fun s => ∫ e, F e * β s e ∂μ) (∫ e, F e * β' 0 e ∂μ) 0 := by
  obtain ⟨MF, hMF⟩ := hK.exists_bound_of_continuousOn (hF.mono hKU)
  have hIK : IsCompact (Set.Icc (-(δ / 2)) (δ / 2) ×ˢ K) := isCompact_Icc.prod hK
  have hIsub : Set.Icc (-(δ / 2)) (δ / 2) ×ˢ K ⊆ Set.Ioo (-δ) δ ×ˢ (Set.univ : Set E) :=
    Set.prod_mono (Set.Icc_subset_Ioo (by linarith) (by linarith)) (Set.subset_univ K)
  obtain ⟨Mβ, hMβ⟩ := hIK.exists_bound_of_continuousOn (hβ'.mono hIsub)
  have hnhds : Set.Ioo (-(δ / 2)) (δ / 2) ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
  have hsub : ∀ s ∈ Set.Ioo (-(δ / 2)) (δ / 2), s ∈ Set.Ioo (-δ) δ := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h0 : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hβs : ∀ s ∈ Set.Ioo (-δ) δ, Continuous fun e => β s e := fun s hs =>
    hβ.comp_continuous (continuous_const.prodMk continuous_id) fun e => ⟨hs, Set.mem_univ e⟩
  have hβ's : ∀ s ∈ Set.Ioo (-δ) δ, Continuous fun e => β' s e := fun s hs =>
    hβ'.comp_continuous (continuous_const.prodMk continuous_id) fun e => ⟨hs, Set.mem_univ e⟩
  have hcont : ∀ s ∈ Set.Ioo (-δ) δ, Continuous fun e => F e * β s e := fun s hs =>
    continuous_mul_kernel hU hF hK.isClosed hKU (hβs s hs) (hsupp s hs)
  have hcont' : ∀ s ∈ Set.Ioo (-δ) δ, Continuous fun e => F e * β' s e := fun s hs =>
    continuous_mul_kernel hU hF hK.isClosed hKU (hβ's s hs) (hsupp' s hs)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun s e => F e * β s e)
    (F' := fun s e => F e * β' s e) (bound := K.indicator fun _ => MF * Mβ) hnhds ?_ ?_
    (hcont' 0 h0).aestronglyMeasurable ?_ ?_ ?_).2
  · filter_upwards [hnhds] with s hs
    exact (hcont s (hsub s hs)).aestronglyMeasurable
  · refine (hcont 0 h0).integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact hK ?_)
    intro e he
    by_contra heK
    exact he (by simp [hsupp 0 h0 e heK])
  · refine Filter.Eventually.of_forall fun e s hs => ?_
    show ‖F e * β' s e‖ ≤ K.indicator (fun _ => MF * Mβ) e
    by_cases he : e ∈ K
    · rw [Set.indicator_of_mem he, norm_mul]
      exact mul_le_mul (hMF e he) (hMβ (s, e) ⟨⟨hs.1.le, hs.2.le⟩, he⟩) (norm_nonneg _)
        ((norm_nonneg _).trans (hMF e he))
    · rw [Set.indicator_of_notMem he, hsupp' s (hsub s hs) e he, mul_zero, norm_zero]
  · exact (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const (hs := hK.measure_lt_top.ne))
  · exact Filter.Eventually.of_forall fun e s hs => (hd s (hsub s hs) e).const_mul (F e)

private theorem integral_comp_linearMap_eq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] E)
    (hL : LinearMap.det L ≠ 0) {h : E → ℂ} (hh : AEStronglyMeasurable h μ) :
    ∫ e, h (L e) ∂μ = |(LinearMap.det L)⁻¹| • ∫ e, h e ∂μ := by
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hL
  rw [← integral_map hLm.aemeasurable (by rw [hmap]; exact hh.smul_measure _), hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)]

private theorem contDiff_det_id_add_smul {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (N : E →ₗ[ℝ] E) : ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => LinearMap.det (LinearMap.id + s • N) := by
  classical
  let b := Module.finBasis ℝ E
  have hrw : (fun s : ℝ => LinearMap.det (LinearMap.id + s • N)) = fun s =>
      Matrix.det (LinearMap.toMatrix b b LinearMap.id + s • LinearMap.toMatrix b b N) := by
    funext s
    rw [← LinearMap.det_toMatrix b, map_add, map_smul]
  rw [hrw]
  simp only [Matrix.det_apply', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

private theorem det_ne_zero_of_rightInverse {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] E) (R : E → E) (hR : ∀ e, L (R e) = e) : LinearMap.det L ≠ 0 := by
  have hsurj : Function.Surjective L := fun e => ⟨R e, hR e⟩
  have hbij : Function.Bijective L := ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  have := LinearEquiv.isUnit_det' (LinearEquiv.ofBijective L hbij)
  simp [LinearEquiv.ofBijective, isUnit_iff_ne_zero] at this
  exact this

private theorem fderiv_apply_eq_zero_of_eventually_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : X → ℂ} {p : X} (h : ∀ᶠ q in nhds p, G q = 0) (v : X) : fderiv ℝ G p v = 0 := by
  have h' : G =ᶠ[nhds p] fun _ => (0 : ℂ) := h
  rw [h'.fderiv_eq, fderiv_const_apply]
  rfl

private theorem exists_kernel_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U)
    (N : E →ₗ[ℝ] E) (hstab : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ e ∈ U, (LinearMap.id + s • N : E →ₗ[ℝ] E) e ∈ U)
    (R : ℝ → E → E)
    (hR : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry R) (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ))
    (hRN : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ e, (LinearMap.id + s • N : E →ₗ[ℝ] E) (R s e) = e)
    (hNR : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ e, R s ((LinearMap.id + s • N : E →ₗ[ℝ] E) e) = e)
    {α : E → ℂ} (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hαc : HasCompactSupport α) (hαU : tsupport α ⊆ U) :
    ∃ α₁ : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) α₁ ∧ tsupport α₁ ⊆ tsupport α ∧ ∀ F : E → ℂ, ContinuousOn F U →
      HasDerivAt (fun s : ℝ => ∫ e, F ((LinearMap.id + s • N : E →ₗ[ℝ] E) e) * α e ∂μ)
        (∫ e, F e * α₁ e ∂μ) 0 := by
  set I : Set ℝ := Set.Ioo (-1 : ℝ) 1 with hI
  have hIopen : IsOpen I := isOpen_Ioo
  have h0I : (0 : ℝ) ∈ I := by simp [hI]
  set D : Set (ℝ × E) := I ×ˢ Set.univ with hD
  have hDopen : IsOpen D := hIopen.prod isOpen_univ

  have hdet : ∀ s ∈ I, LinearMap.det (LinearMap.id + s • N) ≠ 0 := fun s hs =>
    det_ne_zero_of_rightInverse _ (R s) (hRN s hs)
  set c : ℝ → ℝ := fun s => |(LinearMap.det (LinearMap.id + s • N))⁻¹| with hc
  have hcI : ContDiffOn ℝ (⊤ : ℕ∞) c I := by
    refine ContDiffOn.abs ((contDiff_det_id_add_smul N).contDiffOn.inv hdet) ?_
    intro s hs
    exact inv_ne_zero (hdet s hs)

  set G : ℝ × E → ℂ := fun p => (c p.1 : ℂ) * α (R p.1 p.2) with hG
  have hGD : ContDiffOn ℝ (⊤ : ℕ∞) G D := by
    refine ContDiffOn.mul ?_ (hα.comp_contDiffOn hR)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hcI.comp contDiffOn_fst fun p hp => hp.1)
  set β : ℝ → E → ℂ := fun s e => G (s, e) with hβ
  set β' : ℝ → E → ℂ := fun s e => fderiv ℝ G (s, e) ((1 : ℝ), (0 : E)) with hβ'
  have hβc : ContinuousOn (Function.uncurry β) D := hGD.continuousOn
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ G) D := hGD.fderiv_of_isOpen hDopen (by simp)
  have hβ'c : ContinuousOn (Function.uncurry β') D := hfd.continuousOn.clm_apply continuousOn_const
  have hd : ∀ s ∈ I, ∀ e : E, HasDerivAt (fun t => β t e) (β' s e) s := by
    intro s hs e
    have h1 : HasFDerivAt G (fderiv ℝ G (s, e)) (s, e) :=
      ((hGD.differentiableOn (by simp)).differentiableAt (hDopen.mem_nhds ⟨hs, Set.mem_univ e⟩)).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => (t, e)) ((1 : ℝ), (0 : E)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s e)
    exact h1.comp_hasDerivAt s h2

  set K₀ : Set E := tsupport α with hK₀
  have hK₀c : IsCompact K₀ := hαc
  set K : Set E :=
    (fun p : ℝ × E => (LinearMap.id + p.1 • N : E →ₗ[ℝ] E) p.2) '' (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ K₀) with hK
  have hKc : IsCompact K := by
    refine (isCompact_Icc.prod hK₀c).image ?_
    have : Continuous fun p : ℝ × E => p.2 + p.1 • N p.2 :=
      continuous_snd.add (continuous_fst.smul (N.continuous_of_finiteDimensional.comp continuous_snd))
    simpa [LinearMap.add_apply, LinearMap.smul_apply] using this
  have hhalf : ∀ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), s ∈ I := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hKU : K ⊆ U := by
    rintro _ ⟨⟨s, k⟩, ⟨hs, hk⟩, rfl⟩
    exact hstab s ⟨by linarith [hs.1], by linarith [hs.2]⟩ k (hαU hk)

  have hGzero : ∀ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), ∀ e, e ∉ K → G (s, e) = 0 := by
    intro s hs e he
    have hR0 : R s e ∉ K₀ := by
      intro hmem
      exact he ⟨(s, R s e), ⟨⟨hs.1.le, hs.2.le⟩, hmem⟩, hRN s (hhalf s hs) e⟩
    have : α (R s e) = 0 := image_eq_zero_of_notMem_tsupport hR0
    simp [hG, this]
  have hsupp : ∀ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), ∀ e, e ∉ K → β s e = 0 := hGzero
  have hsupp' : ∀ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), ∀ e, e ∉ K → β' s e = 0 := by
    intro s hs e he
    refine fderiv_apply_eq_zero_of_eventually_zero ?_ _
    have hopen : IsOpen (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Kᶜ) := isOpen_Ioo.prod hKc.isClosed.isOpen_compl
    filter_upwards [hopen.mem_nhds (⟨hs, he⟩ : (s, e) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Kᶜ)] with q hq
    exact hGzero q.1 hq.1 q.2 hq.2
  have hhalfD : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set E) ⊆ D :=
    Set.prod_mono (fun s hs => hhalf s hs) le_rfl

  refine ⟨β' 0, ?_, ?_, fun F hF => ?_⟩
  · have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : E => fderiv ℝ G (0, e)) Set.univ :=
      hfd.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun e _ => ⟨h0I, Set.mem_univ e⟩
    exact contDiffOn_univ.1 (h1.clm_apply contDiffOn_const)
  · refine closure_minimal ?_ (isClosed_tsupport α)
    intro e he
    by_contra heK
    apply he
    refine fderiv_apply_eq_zero_of_eventually_zero ?_ _
    have hRcont : ContinuousOn (Function.uncurry R) D := hR.continuousOn
    have hR0e : R 0 e = e := by simpa using hNR 0 h0I e
    have hpre : ∀ᶠ q in nhds ((0 : ℝ), e), Function.uncurry R q ∈ K₀ᶜ := by
      have hcont_at : ContinuousAt (Function.uncurry R) (0, e) :=
        hRcont.continuousAt (hDopen.mem_nhds ⟨h0I, Set.mem_univ e⟩)
      have : Function.uncurry R (0, e) ∈ K₀ᶜ := by simpa [Function.uncurry, hR0e] using heK
      exact hcont_at (hK₀c.isClosed.isOpen_compl.mem_nhds this)
    filter_upwards [hpre] with q hq
    have : α (R q.1 q.2) = 0 := image_eq_zero_of_notMem_tsupport hq
    simp [hG, this]
  ·
    have hmain := hasDerivAt_integral_mul_kernel μ hU hF hKc hKU (by norm_num : (0 : ℝ) < 1 / 2) β β'
      (hβc.mono (by simpa using hhalfD)) (hβ'c.mono (by simpa using hhalfD))
      (fun s hs e => hd s (hhalf s hs) e) hsupp hsupp'
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards [hIopen.mem_nhds h0I] with s hs
    symm
    have hLs := hdet s hs
    have hKs : IsCompact ((LinearMap.id + s • N : E →ₗ[ℝ] E) '' K₀) :=
      hK₀c.image (LinearMap.id + s • N : E →ₗ[ℝ] E).continuous_of_finiteDimensional
    have hKsU : (LinearMap.id + s • N : E →ₗ[ℝ] E) '' K₀ ⊆ U := by
      rintro _ ⟨k, hk, rfl⟩
      exact hstab s hs k (hαU hk)
    have hRs : Continuous fun e => α (R s e) :=
      hα.continuous.comp (hR.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        fun e => ⟨hs, Set.mem_univ e⟩)
    have hmeas : AEStronglyMeasurable (fun e => F e * α (R s e)) μ := by
      refine (continuous_mul_kernel hU hF hKs.isClosed hKsU hRs ?_).aestronglyMeasurable
      intro e he
      refine image_eq_zero_of_notMem_tsupport fun hmem => he ⟨R s e, hmem, hRN s hs e⟩
    have hcov := integral_comp_linearMap_eq_smul μ (LinearMap.id + s • N : E →ₗ[ℝ] E) hLs hmeas
    simp only [hNR s hs] at hcov
    calc ∫ e, F e * β s e ∂μ = ∫ e, (c s : ℂ) * (F e * α (R s e)) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
          simp only [hβ, hG]
          ring
      _ = (c s : ℂ) * ∫ e, F e * α (R s e) ∂μ := integral_const_mul _ _
      _ = ∫ e, F ((LinearMap.id + s • N : E →ₗ[ℝ] E) e) * α e ∂μ := by
          rw [hcov, Complex.real_smul]

private def letterEndo (i j : Fin 3) : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ) where
  toFun e := fun a b => if a = i then e j b else 0
  map_add' e e' := by
    funext a b
    by_cases h : a = i <;> simp [h]
  map_smul' r e := by
    funext a b
    by_cases h : a = i <;> simp [h]

private theorem letterEndo_apply (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) (a b : Fin 3) :
    letterEndo i j e a b = if a = i then e j b else 0 :=
  rfl

private theorem rootMat_mul_of (i j : Fin 3) (s : ℝ) (e : Fin 3 → Fin 3 → ℝ) :
    rootMat i j s * Matrix.of e =
      Matrix.of ((LinearMap.id + s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ)) e) := by
  ext a b
  simp only [Matrix.mul_apply, rootMat, Matrix.of_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, letterEndo_apply, add_mul,
    Finset.sum_add_distrib]
  congr 1
  · simp [ite_mul]
  · by_cases h : a = i
    · subst h
      simp [ite_mul, Finset.sum_ite_eq']
    · simp [h]

private noncomputable def letterInvParam (i j : Fin 3) (s : ℝ) : ℝ :=
  if i = j then -s / (1 + s) else -s

private theorem letterInvParam_contDiffOn (i j : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (letterInvParam i j) (Set.Ioo (-1 : ℝ) 1) := by
  unfold letterInvParam
  split_ifs
  · refine ContDiffOn.div contDiff_neg.contDiffOn (contDiff_const.add contDiff_id).contDiffOn ?_
    intro s hs
    have := hs.1
    show (1 : ℝ) + s ≠ 0
    intro h
    linarith
  · exact contDiff_neg.contDiffOn

private theorem letter_comp_inv (i j : Fin 3) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) (e : Fin 3 → Fin 3 → ℝ) :
    (LinearMap.id + s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ))
        ((LinearMap.id + letterInvParam i j s • letterEndo i j :
          (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ)) e) = e := by
  have h1 : (1 : ℝ) + s ≠ 0 := by have := hs.1; intro h; linarith
  funext a b
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, letterEndo_apply, letterInvParam]
  by_cases hai : a = i
  · subst hai
    by_cases hji : j = a
    · subst hji
      simp only [if_true]
      field_simp
      ring
    · simp [hji, Ne.symm hji]
  · simp [hai]

private theorem inv_comp_letter (i j : Fin 3) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) (e : Fin 3 → Fin 3 → ℝ) :
    (LinearMap.id + letterInvParam i j s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ))
        ((LinearMap.id + s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ)) e) = e := by
  have h1 : (1 : ℝ) + s ≠ 0 := by have := hs.1; intro h; linarith
  funext a b
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, letterEndo_apply, letterInvParam]
  by_cases hai : a = i
  · subst hai
    by_cases hji : j = a
    · subst hji
      simp only [if_true]
      field_simp
      ring
    · simp [hji, Ne.symm hji]
  · simp [hai]

private theorem letterInverse_contDiffOn (i j : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry fun (s : ℝ) (e : Fin 3 → Fin 3 → ℝ) =>
        (LinearMap.id + letterInvParam i j s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ)) e)
      (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ) := by
  have hN : ContDiff ℝ (⊤ : ℕ∞) (letterEndo i j) := (letterEndo i j).toContinuousLinearMap.contDiff
  have hσ : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin 3 → Fin 3 → ℝ) => letterInvParam i j p.1)
      (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ) :=
    (letterInvParam_contDiffOn i j).comp contDiffOn_fst fun p hp => hp.1
  have hNe : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × (Fin 3 → Fin 3 → ℝ) => letterEndo i j p.2 := hN.comp contDiff_snd
  refine (contDiff_snd.contDiffOn.add (hσ.smul hNe.contDiffOn)).congr fun p _ => ?_
  simp [Function.uncurry]

private theorem letter_mem_invertible (i j : Fin 3) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1)
    {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    (LinearMap.id + s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ)) e ∈
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have hM : rootMat i j s * rootMat i j (letterInvParam i j s) = 1 := by
    have e1 : rootMat i j (letterInvParam i j s) =
        Matrix.of ((LinearMap.id + letterInvParam i j s • letterEndo i j :
          (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ)) fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) := by
      rw [← mul_one (rootMat i j (letterInvParam i j s))]
      exact rootMat_mul_of i j _ _
    calc rootMat i j s * rootMat i j (letterInvParam i j s)
        = rootMat i j s * Matrix.of ((LinearMap.id + letterInvParam i j s • letterEndo i j :
            (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ)) fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) := by
          rw [e1]
      _ = Matrix.of ((LinearMap.id + s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ))
            ((LinearMap.id + letterInvParam i j s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ))
              fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b)) := rootMat_mul_of i j s _
      _ = Matrix.of fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b := by rw [letter_comp_inv i j hs]
      _ = 1 := rfl
  have hdet : (rootMat i j s).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hM
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  show (Matrix.of _).det ≠ 0
  rw [← rootMat_mul_of, Matrix.det_mul]
  exact mul_ne_zero hdet he

private theorem isOpen_det_ne_zero : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
  isOpen_ne_fun ((continuous_id.matrix_det (R := ℝ) (n := Fin 3)).comp continuous_id) continuous_const

private theorem exists_kernel_hasDerivAt_rootMat (i j : Fin 3) {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hαc : HasCompactSupport α)
    (hαU : tsupport α ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    ∃ α₁ : (Fin 3 → Fin 3 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) α₁ ∧ tsupport α₁ ⊆ tsupport α ∧
      ∀ F : (Fin 3 → Fin 3 → ℝ) → ℂ, ContinuousOn F {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} →
        HasDerivAt (fun s : ℝ => ∫ e : Fin 3 → Fin 3 → ℝ, F (rootMat i j s * Matrix.of e) * α e)
          (∫ e : Fin 3 → Fin 3 → ℝ, F e * α₁ e) 0 := by
  obtain ⟨α₁, h₁, h₂, h₃⟩ := exists_kernel_hasDerivAt (MeasureTheory.volume : Measure (Fin 3 → Fin 3 → ℝ))
    isOpen_det_ne_zero (letterEndo i j) (fun s hs e he => letter_mem_invertible i j hs he)
    (fun s e => (LinearMap.id + letterInvParam i j s • letterEndo i j :
      (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ)) e)
    (letterInverse_contDiffOn i j) (fun s hs e => letter_comp_inv i j hs e) (fun s hs e => inv_comp_letter i j hs e)
    hα hαc hαU
  refine ⟨α₁, h₁, h₂, fun F hF => ?_⟩
  have := h₃ F hF
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [rootMat_mul_of]
  rfl

private noncomputable def kernelIntegral (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (β : (Fin 3 → Fin 3 → ℝ) → ℂ) :
    AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun g => ∫ h : Fin 3 → Fin 3 → ℝ, f (g * WhittakerBlock.archRealLift3 h) * β h

private theorem rootMat_eq_of_letter (i j : Fin 3) (t : ℝ) :
    rootMat i j t = Matrix.of ((LinearMap.id + t • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ))
      fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) := by
  rw [← mul_one (rootMat i j t)]
  exact rootMat_mul_of i j t _

private theorem rootMat_mul_rootMat_letterInv (i j : Fin 3) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    rootMat i j s * rootMat i j (letterInvParam i j s) = 1 := by
  calc rootMat i j s * rootMat i j (letterInvParam i j s)
      = rootMat i j s * Matrix.of ((LinearMap.id + letterInvParam i j s • letterEndo i j :
          (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ)) fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) := by
        rw [rootMat_eq_of_letter i j (letterInvParam i j s)]
    _ = Matrix.of ((LinearMap.id + s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ))
          ((LinearMap.id + letterInvParam i j s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ))
            fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b)) := rootMat_mul_of i j s _
    _ = Matrix.of fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b := by rw [letter_comp_inv i j hs]
    _ = 1 := rfl

private theorem rootMat_letterInv_mul_rootMat (i j : Fin 3) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    rootMat i j (letterInvParam i j s) * rootMat i j s = 1 := by
  calc rootMat i j (letterInvParam i j s) * rootMat i j s
      = rootMat i j (letterInvParam i j s) * Matrix.of ((LinearMap.id + s • letterEndo i j :
          (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ)) fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) := by
        rw [rootMat_eq_of_letter i j s]
    _ = Matrix.of ((LinearMap.id + letterInvParam i j s • letterEndo i j :
          (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ))
          ((LinearMap.id + s • letterEndo i j : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ))
            fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b)) := rootMat_mul_of i j _ _
    _ = Matrix.of fun a b => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b := by rw [inv_comp_letter i j hs]
    _ = 1 := rfl

private theorem archRealLift3_rootMat_mul_of (i j : Fin 3) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1)
    {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    WhittakerBlock.archRealLift3 (rootMat i j s * Matrix.of e) =
      WhittakerBlock.archRealLift3 (rootMat i j s) * WhittakerBlock.archRealLift3 e :=
  archRealLift3_mul_of_inv _ _ _ _ (rootMat_mul_rootMat_letterInv i j hs) (rootMat_letterInv_mul_rootMat i j hs)
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 he)) (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 he))

private theorem exists_archDeriv_kernelIntegral_eq (i j : Fin 3) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 f) {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    (hαc : HasCompactSupport α) (hαU : tsupport α ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    ∃ α₁ : (Fin 3 → Fin 3 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) α₁ ∧ tsupport α₁ ⊆ tsupport α ∧
      archDeriv i j (kernelIntegral f α) = kernelIntegral f α₁ := by
  obtain ⟨α₁, h₁, h₂, h₃⟩ := exists_kernel_hasDerivAt_rootMat i j hα hαc hαU
  refine ⟨α₁, h₁, h₂, ?_⟩
  funext g
  have hF := h₃ (fun e => f (g * WhittakerBlock.archRealLift3 e)) (hsa g).continuousOn
  have hfun : (fun s : ℝ => kernelIntegral f α (g * WhittakerBlock.archRealLift3 (rootMat i j s))) =ᶠ[nhds 0]
      fun s : ℝ => ∫ e : Fin 3 → Fin 3 → ℝ,
        f (g * WhittakerBlock.archRealLift3 (rootMat i j s * Matrix.of e)) * α e := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with s hs
    unfold kernelIntegral
    refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
    by_cases he : e ∈ tsupport α
    · simp only
      rw [archRealLift3_rootMat_mul_of i j hs (hαU he), mul_assoc]
    · simp [image_eq_zero_of_notMem_tsupport he]
  show deriv (fun s : ℝ => kernelIntegral f α (g * WhittakerBlock.archRealLift3 (rootMat i j s))) 0 = _
  rw [(hF.congr_of_eventuallyEq hfun).deriv]
  rfl

private theorem exists_kernel_foldr_eq (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 f)
    (α : (Fin 3 → Fin 3 → ℝ) → ℂ) (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hαc : HasCompactSupport α)
    (hαU : tsupport α ⊆ {e | (Matrix.of e).det ≠ 0})
    (hconv : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      f g = ∫ h : Fin 3 → Fin 3 → ℝ, f (g * WhittakerBlock.archRealLift3 h) * α h)
    (w : List (Fin 3 × Fin 3)) :
    ∃ β : (Fin 3 → Fin 3 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) β ∧ HasCompactSupport β ∧
      tsupport β ⊆ {e | (Matrix.of e).det ≠ 0} ∧ tsupport β ⊆ tsupport α ∧
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) f w g =
        ∫ h : Fin 3 → Fin 3 → ℝ, f (g * WhittakerBlock.archRealLift3 h) * β h := by
  induction w with
  | nil => exact ⟨α, hα, hαc, hαU, subset_rfl, fun g => hconv g⟩
  | cons q w ih =>
    obtain ⟨β, hβ, hβc, hβU, hβα, hβw⟩ := ih
    obtain ⟨β₁, hβ₁, hβ₁β, hd⟩ := exists_archDeriv_kernelIntegral_eq q.1 q.2 f hsa hβ hβc hβU
    refine ⟨β₁, hβ₁, IsCompact.of_isClosed_subset hβc (isClosed_tsupport β₁) hβ₁β, hβ₁β.trans hβU,
      hβ₁β.trans hβα, fun g => ?_⟩
    have hw : List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) f w = kernelIntegral f β := funext hβw
    show archDeriv q.1 q.2 (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) f w) g = _
    rw [hw, hd]
    rfl

private theorem max_one_mul_le_max_one_mul (x : ℝ) {L : ℝ} (hL : 1 ≤ L) : max 1 (x * L) ≤ max 1 x * L := by
  rw [max_mul_of_nonneg _ _ (zero_le_one.trans hL), one_mul]
  exact max_le_max hL le_rfl

private theorem exists_entry_bounds_of_isCompact {K : Set (Fin 3 → Fin 3 → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    ∃ C C' : ℝ, ∀ k ∈ K, (∀ a b, |Matrix.of k a b| ≤ C) ∧ ∀ a b, |(Matrix.of k)⁻¹ a b| ≤ C' := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  have hinv : ContinuousOn (fun k : Fin 3 → Fin 3 → ℝ => fun a b => (Matrix.of k)⁻¹ a b)
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
    intro k hk
    have h : ContinuousAt (Inv.inv : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ) (Matrix.of k) := by
      refine continuousAt_matrix_inv (Matrix.of k) ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hk
    exact h.continuousWithinAt
  obtain ⟨C', hC'⟩ := hK.exists_bound_of_continuousOn (hinv.mono hKU)
  refine ⟨C, C', fun k hk => ⟨fun a b => ?_, fun a b => ?_⟩⟩
  · have h1 := hC k hk
    simp only [id] at h1
    exact (Real.norm_eq_abs (k a b)).symm.le.trans
      (((norm_le_pi_norm (k a) b).trans (norm_le_pi_norm k a)).trans h1)
  · have h1 := hC' k hk
    exact (Real.norm_eq_abs _).symm.le.trans
      (((norm_le_pi_norm (fun b => (Matrix.of k)⁻¹ a b) b).trans
        (norm_le_pi_norm (fun a b => (Matrix.of k)⁻¹ a b) a)).trans h1)

private theorem norm_integral_mul_kernel_le {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {β : E → ℂ}
    (hβ : Continuous β) (hβc : HasCompactSupport β) (F : E → ℂ) {M : ℝ} (hM : ∀ e ∈ tsupport β, ‖F e‖ ≤ M) :
    ‖∫ e, F e * β e ∂μ‖ ≤ M * ∫ e, ‖β e‖ ∂μ := by
  have hint : Integrable (fun e => M * ‖β e‖) μ :=
    (hβ.integrable_of_hasCompactSupport hβc).norm.const_mul M
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun e => ?_)
  rw [norm_mul]
  by_cases he : e ∈ tsupport β
  · exact mul_le_mul_of_nonneg_right (hM e he) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport he]

private theorem le_max_mul_pow_of_le {v x y L C₀ : ℝ} {N : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y * L) (hv : v ≤ C₀ * x ^ N) :
    v ≤ max C₀ 0 * (y * L) ^ N := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  calc v ≤ C₀ * x ^ N := hv
    _ ≤ max C₀ 0 * x ^ N := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx0 N)
    _ ≤ max C₀ 0 * (y * L) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hxy N) (le_max_right _ _)

private theorem max_mul_pow_mul_eq (C₀ y L m : ℝ) (N : ℕ) :
    max C₀ 0 * (y * L) ^ N * m = max C₀ 0 * L ^ N * m * y ^ N := by
  rw [mul_pow]
  ring

private theorem gauge3_mul_archRealLift3_le (g : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : (Matrix.of e).det ≠ 0) {C C' : ℝ} (hC : ∀ a b, |Matrix.of e a b| ≤ C)
    (hC' : ∀ a b, |(Matrix.of e)⁻¹ a b| ≤ C') :
    LanglandsTunnell.CubicInduction.gauge3 ℚ (g * WhittakerBlock.archRealLift3 e) ≤
      LanglandsTunnell.CubicInduction.gauge3 ℚ g * max 1 (1 + 9 * (C + C')) := by
  have hu : IsUnit (Matrix.of e).det := isUnit_iff_ne_zero.2 he
  have h1 := Matrix.mul_nonsing_inv (Matrix.of e) hu
  have h2 := Matrix.nonsing_inv_mul (Matrix.of e) hu
  have hfin : LanglandsTunnell.CubicInduction.finGauge3 ℚ (g * WhittakerBlock.archRealLift3 e) =
      LanglandsTunnell.CubicInduction.finGauge3 ℚ g :=
    gaugeFin_mul_archRealLift3 g _ _ h1 h2
  have harch : LanglandsTunnell.CubicInduction.archGauge3 ℚ (g * WhittakerBlock.archRealLift3 e) ≤
      LanglandsTunnell.CubicInduction.archGauge3 ℚ g * max 1 (1 + 9 * (C + C')) :=
    (gaugeArch_mul_le _ _).trans (mul_le_mul_of_nonneg_left
      ((gaugeArch_archRealLift3_le _ _ h1 h2 hC hC').trans (le_max_right _ _))
      (zero_le_one.trans (LanglandsTunnell.CubicInduction.one_le_archGauge3 ℚ g)))
  show max 1 _ ≤ max 1 _ * _
  rw [hfin]
  refine le_trans (max_le_max le_rfl ?_) (max_one_mul_le_max_one_mul _ (le_max_left _ _))
  calc LanglandsTunnell.CubicInduction.archGauge3 ℚ (g * WhittakerBlock.archRealLift3 e) *
        LanglandsTunnell.CubicInduction.finGauge3 ℚ g
      ≤ LanglandsTunnell.CubicInduction.archGauge3 ℚ g * max 1 (1 + 9 * (C + C')) *
          LanglandsTunnell.CubicInduction.finGauge3 ℚ g :=
        mul_le_mul_of_nonneg_right harch (gaugeFin_nonneg g)
    _ = LanglandsTunnell.CubicInduction.archGauge3 ℚ g * LanglandsTunnell.CubicInduction.finGauge3 ℚ g *
          max 1 (1 + 9 * (C + C')) := by ring

private theorem isModerateGrowth3_iterate_of_reproducing (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 f) (hmg : LanglandsTunnell.CubicInduction.IsModerateGrowth3 ℚ f)
    (α : (Fin 3 → Fin 3 → ℝ) → ℂ) (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hαc : HasCompactSupport α)
    (hαU : tsupport α ⊆ {e | (Matrix.of e).det ≠ 0})
    (hconv : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      f g = ∫ h : Fin 3 → Fin 3 → ℝ, f (g * WhittakerBlock.archRealLift3 h) * α h) :
    ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) f w g‖ ≤ C * LanglandsTunnell.CubicInduction.gauge3 ℚ g ^ N := by
  obtain ⟨C₀, N, hC₀⟩ := hmg
  obtain ⟨B, B', hB⟩ := exists_entry_bounds_of_isCompact hαc hαU
  refine ⟨N, fun w => ?_⟩
  obtain ⟨β, hβ, hβc, -, hβα, hβw⟩ := exists_kernel_foldr_eq f hsa α hα hαc hαU hconv w
  refine ⟨max C₀ 0 * max 1 (1 + 9 * (B + B')) ^ N * ∫ e : Fin 3 → Fin 3 → ℝ, ‖β e‖, fun g => ?_⟩
  rw [hβw g]
  have hpt : ∀ e ∈ tsupport β, ‖f (g * WhittakerBlock.archRealLift3 e)‖ ≤
      max C₀ 0 * (LanglandsTunnell.CubicInduction.gauge3 ℚ g * max 1 (1 + 9 * (B + B'))) ^ N := by
    intro e he
    obtain ⟨hB1, hB2⟩ := hB e (hβα he)
    exact le_max_mul_pow_of_le (LanglandsTunnell.CubicInduction.one_le_gauge3 ℚ _)
      (gauge3_mul_archRealLift3_le g (hαU (hβα he)) hB1 hB2) (hC₀ _ (Set.mem_univ _))
  exact (norm_integral_mul_kernel_le MeasureTheory.volume hβ.continuous hβc _ hpt).trans_eq
    (max_mul_pow_mul_eq _ _ _ _ N)

private theorem lone_continuous_archRealMat3 :
    Continuous fun e : Fin 3 → Fin 3 → ℝ => WhittakerBlock.archRealMat3 e := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun e : Fin 3 → Fin 3 → ℝ =>
    ((AutomorphicForm.StandardKernel.ofReal (e i j), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
      InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  exact (AutomorphicForm.StandardKernel.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))).prodMk
    continuous_const

private theorem lone_isOpen_invertibles : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have hdet : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id : Continuous fun e : Matrix (Fin 3) (Fin 3) ℝ => e).matrix_det
  exact isOpen_ne_fun hdet continuous_const

private theorem lone_continuousOn_inv :
    ContinuousOn (fun e : Matrix (Fin 3) (Fin 3) ℝ => e⁻¹) {e : Matrix (Fin 3) (Fin 3) ℝ | e.det ≠ 0} := by
  intro e he
  refine (continuousAt_matrix_inv e ?_).continuousWithinAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ he

private theorem lone_continuousOn_archRealLift3 :
    ContinuousOn WhittakerBlock.archRealLift3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  have hval : ∀ x : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
      ((WhittakerBlock.archRealLift3 x.1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
        WhittakerBlock.archRealMat3 x.1 :=
    fun x => coe_archRealLift3_of_inv x.1 (x.1 : Matrix (Fin 3) (Fin 3) ℝ)⁻¹
      (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 x.2)) (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 x.2))
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (lone_continuous_archRealMat3.comp continuous_subtype_val).congr fun x => (hval x).symm
  · refine (lone_continuous_archRealMat3.comp
      (lone_continuousOn_inv.comp_continuous continuous_subtype_val fun x => x.2)).congr fun x => ?_
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    simp only [Set.restrict_apply, Function.comp_apply]
    rw [hval x, ← archRealMat3_mul,
      Matrix.mul_nonsing_inv (x.1 : Matrix (Fin 3) (Fin 3) ℝ) (isUnit_iff_ne_zero.2 x.2), archRealMat3_one]

private theorem lone_integrable_of_compact {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure ν] {C : Set Y}
    (hC : IsCompact C) (hν : ∀ᵐ y ∂ν, y ∈ C) {φ : Y → ℂ} (hφ : Continuous φ) : MeasureTheory.Integrable φ ν := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hφ.continuousOn
  exact MeasureTheory.Integrable.of_bound hφ.aestronglyMeasurable M (hν.mono fun y hy => hM y hy)

private theorem lone_integral_param {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure ν]
    {C : Set Y} (hC : IsCompact C) (hν : ∀ᵐ y ∂ν, y ∈ C) (F : X → Y → ℂ)
    (hF : Continuous fun q : X × Y => F q.1 q.2) : Continuous fun x => ∫ y, F x y ∂ν := by
  have hint : ∀ x, MeasureTheory.Integrable (F x) ν := fun x =>
    lone_integrable_of_compact ν hC hν (hF.comp (continuous_const.prodMk continuous_id))
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ0, hδm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * ν.real Set.univ < ε := by
    refine ⟨ε / (2 * (ν.real Set.univ + 1)), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [MeasureTheory.measureReal_nonneg (μ := ν) (s := Set.univ), mul_nonneg hε.le
      (MeasureTheory.measureReal_nonneg (μ := ν) (s := Set.univ))]
  have hG : Continuous fun z : X × Y => dist (F z.1 z.2) (F x₀ z.2) :=
    hF.dist (hF.comp (continuous_const.prodMk continuous_snd))
  have hunif : ∀ᶠ x in nhds x₀, ∀ y ∈ C, dist (F x y) (F x₀ y) < δ := by
    refine hC.eventually_forall_of_forall_eventually fun y _ => ?_
    exact hG.continuousAt.eventually_lt continuousAt_const (by simpa using hδ0)
  refine hunif.mono fun x hx => ?_
  rw [dist_eq_norm, ← MeasureTheory.integral_sub (hint x) (hint x₀)]
  refine lt_of_le_of_lt (MeasureTheory.norm_integral_le_of_norm_le_const ?_) hδm
  exact hν.mono fun y hy => by
    rw [← dist_eq_norm]
    exact (hx y hy).le

private theorem lone_continuous_kernel_integrand (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβU : tsupport β ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    Continuous fun q : AdelicGL 3 (𝓞 ℚ) ℚ × (Fin 3 → Fin 3 → ℝ) =>
      f (q.1 * WhittakerBlock.archRealLift3 q.2) * β q.2 := by
  refine continuous_iff_continuousAt.2 fun q₀ => ?_
  by_cases hq : q₀.2 ∈ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}
  · have hlift : ContinuousAt WhittakerBlock.archRealLift3 q₀.2 :=
      lone_continuousOn_archRealLift3.continuousAt (lone_isOpen_invertibles.mem_nhds hq)
    exact (hc.continuousAt.comp (continuousAt_fst.mul (hlift.comp continuousAt_snd))).mul
      (hβ.continuous.continuousAt.comp continuousAt_snd)
  · have hmem : (Prod.snd ⁻¹' (tsupport β)ᶜ : Set (AdelicGL 3 (𝓞 ℚ) ℚ × (Fin 3 → Fin 3 → ℝ))) ∈ nhds q₀ :=
      ((isClosed_tsupport β).isOpen_compl.preimage continuous_snd).mem_nhds fun hq' => hq (hβU hq')
    refine Filter.EventuallyEq.continuousAt (y := 0) (Filter.eventually_of_mem hmem fun q hq' => ?_)
    show f (q.1 * WhittakerBlock.archRealLift3 q.2) * β q.2 = 0
    rw [image_eq_zero_of_notMem_tsupport hq', mul_zero]

private theorem lone_continuous_integral_kernel (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβc : HasCompactSupport β)
    (hβU : tsupport β ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}) :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ∫ h : Fin 3 → Fin 3 → ℝ, f (g * WhittakerBlock.archRealLift3 h) * β h := by
  have hK : IsCompact (tsupport β) := hβc
  haveI : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (tsupport β)) :=
    MeasureTheory.isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hcont : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ∫ h in tsupport β, f (g * WhittakerBlock.archRealLift3 h) * β h :=
    lone_integral_param (MeasureTheory.volume.restrict (tsupport β)) hK
      (MeasureTheory.ae_restrict_mem (isClosed_tsupport β).measurableSet)
      (fun g h => f (g * WhittakerBlock.archRealLift3 h) * β h) (lone_continuous_kernel_integrand f hc β hβ hβU)
  refine hcont.congr fun g => ?_
  exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => by
    rw [image_eq_zero_of_notMem_tsupport hh, mul_zero]

private theorem lone_v_continuous (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f) (n : ℕ) (c : Fin n → ℂ)
    (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) : Continuous fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ∑ i, c i * f (x * t i) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (hc.comp (continuous_mul_const (t i)))

private theorem lone_adeleFin_mapMatrix_eq_one (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ p k = 1) :
    (NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
  ext i j p
  have hp : (NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix
      ((NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) = 1 :=
    congrArg Units.val (hk p)
  have h1 : (NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix
      (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 :=
    _root_.map_one _
  calc ((NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) p
      = (NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix
          ((NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
            (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) i j := rfl
    _ = (NumberField.AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix
          (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j := by
        rw [hp, h1]
    _ = ((1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) p := rfl

private theorem lone_mul_comm_of_components (k t : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ p k = 1)
    (ht : LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ t = 1) : k * t = t * k := by
  have hk' := lone_adeleFin_mapMatrix_eq_one k hk
  have ht' : (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
      (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 :=
    congrArg Units.val ht
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  refine adeleMatrix_ext ?_ ?_
  · rw [_root_.map_mul, _root_.map_mul, ht', _root_.one_mul, _root_.mul_one]
  · rw [_root_.map_mul, _root_.map_mul, hk', _root_.one_mul, _root_.mul_one]

private theorem lone_v_isArchSmooth3 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 f) (n : ℕ)
    (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ)
    (ht : ∀ i, LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    WhittakerBlock.IsArchSmooth3 fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ∑ i, c i * f (x * t i) := by
  intro g
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun e : Fin 3 → Fin 3 → ℝ => ∑ i, c i * f (g * t i * WhittakerBlock.archRealLift3 e))
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    ContDiffOn.sum fun i _ => contDiffOn_const.mul (hsa (g * t i))
  refine hsum.congr fun e he => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.mul_assoc, ← mul_archRealLift3_comm (t i) (ht i) e (Matrix.of e)⁻¹
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 he)) (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 he)),
    ← _root_.mul_assoc]

private theorem lone_v_kFinite (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ p k = 1) →
        LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ k ∈ LanglandsTunnell.CubicInduction.orth3 →
          (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ)
    (ht : ∀ i, LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ p k = 1) →
        LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ k ∈ LanglandsTunnell.CubicInduction.orth3 →
          (fun g => ∑ i, c i * f (g * k * t i)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
  classical
  obtain ⟨s, hs⟩ := hKf
  refine ⟨Finset.univ.biUnion fun i => s.image fun φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ => fun g => φ (g * t i),
    fun k hk hk' => ?_⟩
  have hψ := hs k hk hk'
  have hfun : (fun g => ∑ i, c i * f (g * k * t i)) =
      ∑ i, c i • LinearMap.funLeft ℂ ℂ (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => g * t i) (fun g => f (g * k)) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.mul_assoc, lone_mul_comm_of_components k (t i) hk (ht i), ← _root_.mul_assoc]
  rw [hfun]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have hmap : LinearMap.funLeft ℂ ℂ (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => g * t i) (fun g => f (g * k)) ∈
      Submodule.span ℂ
        (LinearMap.funLeft ℂ ℂ (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => g * t i) '' (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) := by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem hψ
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨φ, hφ, rfl⟩
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image.2 ⟨φ, hφ, rfl⟩⟩)

private theorem rtEntry_le_supSize {L : Type*} [NormedField L] (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ LanglandsTunnell.CubicInduction.matrixSupSize k :=
  (le_max_left _ _).trans (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 =>
    max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊)
      (Finset.mem_univ (i, j)))

private theorem rtInvEntry_le_supSize {L : Type*} [NormedField L] (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ LanglandsTunnell.CubicInduction.matrixSupSize k :=
  (le_max_right _ _).trans (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 =>
    max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊ ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊)
      (Finset.mem_univ (i, j)))

private theorem rtSupSize_mul_le {L : Type*} [NormedField L] [IsUltrametricDist L] (m k : GL (Fin 3) L) :
    LanglandsTunnell.CubicInduction.matrixSupSize (m * k) ≤
      LanglandsTunnell.CubicInduction.matrixSupSize m * LanglandsTunnell.CubicInduction.matrixSupSize k := by
  refine Finset.sup_le fun ij _ => max_le ?_ ?_
  · rw [Units.val_mul, Matrix.mul_apply]
    refine (Finset.nnnorm_sum_le_sup_nnnorm _ _).trans (Finset.sup_le fun l _ => ?_)
    rw [nnnorm_mul]
    exact mul_le_mul (rtEntry_le_supSize m _ _) (rtEntry_le_supSize k _ _) zero_le zero_le
  · rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    refine (Finset.nnnorm_sum_le_sup_nnnorm _ _).trans (Finset.sup_le fun l _ => ?_)
    rw [nnnorm_mul]
    exact (mul_le_mul (rtInvEntry_le_supSize k _ _) (rtInvEntry_le_supSize m _ _) zero_le
      zero_le).trans_eq (_root_.mul_comm _ _)

private theorem rtOne_le_supSize {L : Type*} [NormedField L] [IsUltrametricDist L] (k : GL (Fin 3) L) :
    1 ≤ LanglandsTunnell.CubicInduction.matrixSupSize k := by
  by_contra h
  rw [not_le] at h
  have h1 : ‖((k : Matrix (Fin 3) (Fin 3) L) * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) 0 0‖₊ = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq, nnnorm_one]
  have h2 : ‖((k : Matrix (Fin 3) (Fin 3) L) * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) 0 0‖₊ ≤
      LanglandsTunnell.CubicInduction.matrixSupSize k * LanglandsTunnell.CubicInduction.matrixSupSize k := by
    rw [Matrix.mul_apply]
    refine (Finset.nnnorm_sum_le_sup_nnnorm _ _).trans (Finset.sup_le fun l _ => ?_)
    rw [nnnorm_mul]
    exact mul_le_mul (rtEntry_le_supSize k _ _) (rtInvEntry_le_supSize k _ _) zero_le zero_le
  rw [h1] at h2
  exact absurd h2 (not_le.2 (mul_lt_one_of_nonneg_of_lt_one_left zero_le h h.le))

private def rtLocal (x : AdelicGL 3 (𝓞 ℚ) ℚ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) : ℝ :=
  ((LanglandsTunnell.CubicInduction.matrixSupSize (LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ v x) :
    NNReal) : ℝ)

private theorem rtFinGauge3_eq (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    LanglandsTunnell.CubicInduction.finGauge3 ℚ x = ∏ᶠ v, rtLocal x v :=
  rfl

private theorem rtComponentAt3_apply (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (x : AdelicGL 3 (𝓞 ℚ) ℚ)
    (i j : Fin 3) :
    ((LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ v x : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
      ((x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v :=
  rfl

private theorem rtMulSupport_finite (g : AdelicGL 3 (𝓞 ℚ) ℚ) : (Function.mulSupport (rtLocal g)).Finite := by
  have hint : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ ij : Fin 3 × Fin 3,
      ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) ij.1 ij.2).2 v ∈ v.adicCompletionIntegers ℚ ∧
        (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) ij.1 ij.2).2 v ∈
          v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun ij =>
      (RestrictedProduct.eventually _ _ ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) ij.1 ij.2).2).and
        (RestrictedProduct.eventually _ _
          (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) ij.1 ij.2).2)
  refine (Filter.eventually_cofinite.1 hint).subset fun v hv hall => hv ?_
  haveI := gaugeUltrametric v
  have hle : LanglandsTunnell.CubicInduction.matrixSupSize
      (LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ v g) ≤ 1 := by
    refine Finset.sup_le fun ij _ => max_le ?_ ?_
    · rw [rtComponentAt3_apply]
      exact gaugeNNNorm_le_one_of_mem v (hall ij).1
    · rw [← _root_.map_inv, rtComponentAt3_apply]
      exact gaugeNNNorm_le_one_of_mem v (hall ij).2
  show ((LanglandsTunnell.CubicInduction.matrixSupSize
    (LanglandsTunnell.CubicInduction.componentAt3 (𝓞 ℚ) ℚ v g) : NNReal) : ℝ) = 1
  rw [le_antisymm hle (rtOne_le_supSize _), NNReal.coe_one]

private theorem rtFinGauge3_mul_le (g t : AdelicGL 3 (𝓞 ℚ) ℚ) :
    LanglandsTunnell.CubicInduction.finGauge3 ℚ (g * t) ≤
      LanglandsTunnell.CubicInduction.finGauge3 ℚ g * LanglandsTunnell.CubicInduction.finGauge3 ℚ t := by
  obtain ⟨S, hg, ht, hgt⟩ : ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
      Function.mulSupport (rtLocal g) ⊆ ↑S ∧ Function.mulSupport (rtLocal t) ⊆ ↑S ∧
        Function.mulSupport (rtLocal (g * t)) ⊆ ↑S :=
    ⟨(((rtMulSupport_finite g).union (rtMulSupport_finite t)).union (rtMulSupport_finite (g * t))).toFinset,
      fun v hv => (Set.Finite.mem_toFinset _).2 (Or.inl (Or.inl hv)),
      fun v hv => (Set.Finite.mem_toFinset _).2 (Or.inl (Or.inr hv)),
      fun v hv => (Set.Finite.mem_toFinset _).2 (Or.inr hv)⟩
  rw [rtFinGauge3_eq, rtFinGauge3_eq, rtFinGauge3_eq, finprod_eq_prod_of_mulSupport_subset _ hgt,
    finprod_eq_prod_of_mulSupport_subset _ hg, finprod_eq_prod_of_mulSupport_subset _ ht,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => NNReal.coe_nonneg _) fun v _ => ?_
  haveI := gaugeUltrametric v
  show ((LanglandsTunnell.CubicInduction.matrixSupSize _ : NNReal) : ℝ) ≤
    ((LanglandsTunnell.CubicInduction.matrixSupSize _ : NNReal) : ℝ) *
      ((LanglandsTunnell.CubicInduction.matrixSupSize _ : NNReal) : ℝ)
  rw [← NNReal.coe_mul, NNReal.coe_le_coe, _root_.map_mul]
  exact rtSupSize_mul_le _ _

private theorem rtOne_le_finGauge3 (t : AdelicGL 3 (𝓞 ℚ) ℚ) : 1 ≤ LanglandsTunnell.CubicInduction.finGauge3 ℚ t := by
  rw [rtFinGauge3_eq, finprod_eq_prod_of_mulSupport_subset (rtLocal t) (s := (rtMulSupport_finite t).toFinset)
    fun v hv => (Set.Finite.mem_toFinset _).2 hv]
  refine Finset.one_le_prod fun v _ => ?_
  haveI := gaugeUltrametric v
  exact NNReal.one_le_coe.2 (rtOne_le_supSize _)

private theorem rtArchPlace_mul (w : NumberField.InfinitePlace ℚ) (g t : AdelicGL 3 (𝓞 ℚ) ℚ)
    (ht : LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ t = 1) :
    LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w (g * t) =
      LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w g := by
  have h1 : LanglandsTunnell.CubicInduction.archPlaceComponent3 ℚ w t = 1 := by
    show Matrix.GeneralLinearGroup.map (NumberField.AdelicLevel.archEval ℚ w)
      (LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ t) = 1
    rw [ht, _root_.map_one]
  rw [_root_.map_mul, h1, _root_.mul_one]

private theorem rtArchGauge3_mul (g t : AdelicGL 3 (𝓞 ℚ) ℚ)
    (ht : LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ t = 1) :
    LanglandsTunnell.CubicInduction.archGauge3 ℚ (g * t) = LanglandsTunnell.CubicInduction.archGauge3 ℚ g := by
  unfold LanglandsTunnell.CubicInduction.archGauge3
  congr 1
  exact Finset.sum_congr rfl fun w _ => by rw [rtArchPlace_mul w g t ht]

private theorem rtMax_one_mul_le (x : ℝ) {L : ℝ} (hL : 1 ≤ L) : max 1 (x * L) ≤ max 1 x * L := by
  rw [max_mul_of_nonneg _ _ (zero_le_one.trans hL), _root_.one_mul]
  exact max_le_max hL le_rfl

private theorem rtGauge3_mul_le (g t : AdelicGL 3 (𝓞 ℚ) ℚ)
    (ht : LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ t = 1) :
    LanglandsTunnell.CubicInduction.gauge3 ℚ (g * t) ≤
      LanglandsTunnell.CubicInduction.gauge3 ℚ g * LanglandsTunnell.CubicInduction.finGauge3 ℚ t := by
  have hF := rtFinGauge3_mul_le g t
  have hA : 0 ≤ LanglandsTunnell.CubicInduction.archGauge3 ℚ g :=
    zero_le_one.trans (LanglandsTunnell.CubicInduction.one_le_archGauge3 ℚ g)
  show max 1 _ ≤ max 1 _ * _
  rw [rtArchGauge3_mul g t ht]
  calc max 1 (LanglandsTunnell.CubicInduction.archGauge3 ℚ g * LanglandsTunnell.CubicInduction.finGauge3 ℚ (g * t))
      ≤ max 1 (LanglandsTunnell.CubicInduction.archGauge3 ℚ g * LanglandsTunnell.CubicInduction.finGauge3 ℚ g *
          LanglandsTunnell.CubicInduction.finGauge3 ℚ t) := by
        refine max_le_max le_rfl ?_
        rw [_root_.mul_assoc]
        exact mul_le_mul_of_nonneg_left hF hA
    _ ≤ max 1 (LanglandsTunnell.CubicInduction.archGauge3 ℚ g * LanglandsTunnell.CubicInduction.finGauge3 ℚ g) *
          LanglandsTunnell.CubicInduction.finGauge3 ℚ t := rtMax_one_mul_le _ (rtOne_le_finGauge3 t)

private theorem rtNorm_translate_le {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {C₀ : ℝ} {N : ℕ}
    (hC₀ : ∀ g ∈ (Set.univ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)), ‖f g‖ ≤ C₀ * LanglandsTunnell.CubicInduction.gauge3 ℚ g ^ N)
    (t : AdelicGL 3 (𝓞 ℚ) ℚ) (ht : LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ t = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ‖f (g * t)‖ ≤ max C₀ 0 * LanglandsTunnell.CubicInduction.finGauge3 ℚ t ^ N *
      LanglandsTunnell.CubicInduction.gauge3 ℚ g ^ N := by
  have h0 : 0 ≤ LanglandsTunnell.CubicInduction.gauge3 ℚ (g * t) := (LanglandsTunnell.CubicInduction.gauge3_pos ℚ _).le
  calc ‖f (g * t)‖ ≤ C₀ * LanglandsTunnell.CubicInduction.gauge3 ℚ (g * t) ^ N := hC₀ _ (Set.mem_univ _)
    _ ≤ max C₀ 0 * LanglandsTunnell.CubicInduction.gauge3 ℚ (g * t) ^ N :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 N)
    _ ≤ max C₀ 0 * (LanglandsTunnell.CubicInduction.gauge3 ℚ g * LanglandsTunnell.CubicInduction.finGauge3 ℚ t) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (rtGauge3_mul_le g t ht) N) (le_max_right _ _)
    _ = max C₀ 0 * LanglandsTunnell.CubicInduction.finGauge3 ℚ t ^ N *
          LanglandsTunnell.CubicInduction.gauge3 ℚ g ^ N := by rw [mul_pow]; ring

private theorem lone_v_isModerateGrowth3 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hmg : LanglandsTunnell.CubicInduction.IsModerateGrowth3 ℚ f)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ)
    (ht : ∀ i, LanglandsTunnell.CubicInduction.archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    LanglandsTunnell.CubicInduction.IsModerateGrowth3 ℚ fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ∑ i, c i * f (x * t i) := by
  obtain ⟨C₀, N, hC₀⟩ := hmg
  unfold LanglandsTunnell.CubicInduction.IsModerateGrowth3 AutomorphicForm.IsSlowlyIncreasingOn
  refine ⟨∑ i, ‖c i‖ * (max C₀ 0 * LanglandsTunnell.CubicInduction.finGauge3 ℚ (t i) ^ N), N, fun g _ => ?_⟩
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, _root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left (rtNorm_translate_le hC₀ (t i) (ht i) g) (norm_nonneg _)

private theorem continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (hmg : IsModerateGrowth3 ℚ f)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite (fun x => ∑ i, c i * f (x * t i))) :
    (∀ w : List (Fin 3 × Fin 3),
        Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w)) ∧
      ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w g‖ ≤
          C * gauge3 ℚ g ^ N := by
  obtain ⟨α, hα, hαc, hαU, hconv⟩ := exists_contDiff_hasCompactSupport_eq_integral_archRealLift3 _
    (lone_v_isArchSmooth3 f hsa n c t ht) (lone_v_kFinite f hKf n c t ht) hz
  refine ⟨fun w => ?_, isModerateGrowth3_iterate_of_reproducing _ (lone_v_isArchSmooth3 f hsa n c t ht)
    (lone_v_isModerateGrowth3 f hmg n c t ht) α hα hαc hαU hconv⟩
  obtain ⟨β, hβ, hβc, hβU, -, hβw⟩ :=
    exists_kernel_foldr_eq _ (lone_v_isArchSmooth3 f hsa n c t ht) α hα hαc hαU hconv w
  exact (lone_continuous_integral_kernel _ (lone_v_continuous f hc n c t) β hβ hβc hβU).congr fun g => (hβw g).symm

end
end LanglandsTunnell.CubicInduction

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite.LanglandsTunnell.CubicInduction in

theorem solution
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (hmg : IsModerateGrowth3 ℚ f)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite (fun x => ∑ i, c i * f (x * t i))) :
    (∀ w : List (Fin 3 × Fin 3),
        Continuous
          (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w)) ∧
      ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w g‖ ≤
          C * gauge3 ℚ g ^ N := by
  exact continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite f hc hmg hsa hKf n c t ht hz

end S_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite (solution)
