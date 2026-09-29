-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_whittaker3_diag_mul_transport_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/719a37d9-c11b-5c03-93d2-e5368a87d098

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Fin.Rev
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker3_diag_mul_transport_of_isCompact

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell LanglandsTunnell.CubicInduction

section ArchFurniture

noncomputable section

open Matrix MeasureTheory

private noncomputable def archOfRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : NumberField.InfinitePlace ℚ =>
    ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      (NumberField.IsTotallyReal.isReal v)).symm : ℝ →+* v.Completion)

private theorem archRealMat3_eq_mapMatrix (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e =
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ (archOfRealHom.mapMatrix (Matrix.of e)) := by
  unfold WhittakerBlock.archRealMat3
  congr 1

private theorem archRealMat3_of_mul (e d : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ) =
      WhittakerBlock.archRealMat3 e * WhittakerBlock.archRealMat3 d := by
  rw [archRealMat3_eq_mapMatrix, archRealMat3_eq_mapMatrix, archRealMat3_eq_mapMatrix,
    ← AutomorphicForm.archMatrixInclN_mul, ← map_mul archOfRealHom.mapMatrix]
  rfl

private theorem isUnit_archRealMat3_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  rw [archRealMat3_eq_mapMatrix]
  have h1 : IsUnit (Matrix.of e) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 he)
  exact (h1.map archOfRealHom.mapMatrix).map (AutomorphicForm.archMatrixInclHomN (Fin 3) ℚ)

private theorem coe_archRealLift3_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3_of_det_ne_zero he)]
  exact IsUnit.unit_spec _

private theorem archRealLift3_of_mul {e d : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0)
    (hd : (Matrix.of d).det ≠ 0) :
    WhittakerBlock.archRealLift3 (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ) =
      WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 d := by
  have hed : (Matrix.of (Matrix.of e * Matrix.of d : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
    show (Matrix.of e * Matrix.of d).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero he hd
  apply Units.ext
  rw [Units.val_mul, coe_archRealLift3_of_det_ne_zero he, coe_archRealLift3_of_det_ne_zero hd,
    coe_archRealLift3_of_det_ne_zero hed, archRealMat3_of_mul]

private theorem archRealLift3_one_array : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  apply Units.ext
  rw [coe_archRealLift3_of_det_ne_zero (by show (1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0; simp),
    archRealMat3_eq_mapMatrix, Units.val_one]
  have h1 : archOfRealHom.mapMatrix (Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1 := by
    rw [show Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ) = (1 : Matrix (Fin 3) (Fin 3) ℝ) from rfl, map_one]
  rw [h1, AutomorphicForm.archMatrixInclN_one]

private theorem isOpen_detSet : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have h : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id (X := Matrix (Fin 3) (Fin 3) ℝ)).matrix_det
  exact isOpen_compl_singleton.preimage h

private theorem exists_closedBall_subset_detSet {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall e r ⊆ {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 isOpen_detSet e he
  exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub⟩

private theorem contDiff_det_of : ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

private theorem contDiff_adjugate_of (k l : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).adjugate k l := by
  fin_cases k <;> fin_cases l <;>
    simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    fun_prop

private theorem contDiffOn_inv_entry (k l : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e)⁻¹ k l)
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have h : ∀ e : Fin 3 → Fin 3 → ℝ, (Matrix.of e)⁻¹ k l = ((Matrix.of e).det)⁻¹ * (Matrix.of e).adjugate k l := by
    intro e
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  simp only [h]
  exact (contDiff_det_of.contDiffOn.inv fun e he => he).mul (contDiff_adjugate_of k l).contDiffOn

private theorem continuous_archRealMat3 : Continuous WhittakerBlock.archRealMat3 := by
  refine continuous_matrix fun i j => ?_
  unfold WhittakerBlock.archRealMat3
  simp only [AutomorphicForm.archMatrixInclN, Matrix.of_apply]
  exact (AutomorphicForm.StandardKernel.continuous_ofReal.comp
    ((continuous_apply j).comp (continuous_apply i))).prodMk continuous_const

private theorem det_of_inv_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (Matrix.of ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
  show ((Matrix.of e)⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

private theorem archRealLift3_inv_of_det_ne_zero {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e)⁻¹ =
      WhittakerBlock.archRealLift3 ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h1 : (Matrix.of e * Matrix.of ((Matrix.of e)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    show Matrix.of e * (Matrix.of e)⁻¹ = 1
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 he)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← archRealLift3_of_mul he (det_of_inv_ne_zero he), h1, archRealLift3_one_array]

private theorem continuousOn_archRealLift3_detSet :
    ContinuousOn WhittakerBlock.archRealLift3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
        ((WhittakerBlock.archRealLift3 e.1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          WhittakerBlock.archRealMat3 e.1 :=
      fun e => coe_archRealLift3_of_det_ne_zero e.2
    simp only [Set.domRestrict_apply, Function.comp_def, h]
    exact continuous_archRealMat3.comp continuous_subtype_val
  · have h : ∀ e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0},
        (((WhittakerBlock.archRealLift3 e.1)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          WhittakerBlock.archRealMat3 ((Matrix.of e.1)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) := by
      intro e
      rw [archRealLift3_inv_of_det_ne_zero e.2]
      exact coe_archRealLift3_of_det_ne_zero (det_of_inv_ne_zero e.2)
    simp only [Set.domRestrict_apply, h]
    refine continuous_archRealMat3.comp ?_
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (contDiffOn_inv_entry k l).continuousOn.comp_continuous continuous_subtype_val fun e => e.2

end

end ArchFurniture

section PassageFurniture

open AutomorphicForm

private noncomputable def archAdele (r : ℝ) : AdeleRing (𝓞 ℚ) ℚ :=
  ((StandardKernel.ofReal r, 0) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)

private theorem archOfRealHom_apply (r : ℝ) : archOfRealHom r = StandardKernel.ofReal r := rfl

private theorem archAdele_eq (r : ℝ) :
    archAdele r = ((archOfRealHom r, 0) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

private theorem adele_one_eq :
    (((1 : InfiniteAdeleRing ℚ), (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (1 : AdeleRing (𝓞 ℚ) ℚ) := rfl

private theorem adele_zero_eq :
    (((0 : InfiniteAdeleRing ℚ), (0 : FiniteAdeleRing (𝓞 ℚ) ℚ)) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (0 : AdeleRing (𝓞 ℚ) ℚ) := rfl

private theorem archRealLift3_unipotent (x y z : ℝ) :
    WhittakerBlock.archRealLift3 (fun i j => (!![1, x, z; 0, 1, y; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) i j) =
      upperUnipotent3 (archAdele x) (archAdele y) (archAdele z) := by
  have hdet : (Matrix.of fun i j => (!![1, x, z; 0, 1, y; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) i j).det ≠ 0 := by
    simp [Matrix.det_fin_three]
  apply Units.ext
  rw [coe_archRealLift3_of_det_ne_zero hdet, archRealMat3_eq_mapMatrix, upperUnipotent3_coe]
  ext i j
  simp only [archMatrixInclN, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [archAdele_eq, map_one, map_zero, adele_one_eq, adele_zero_eq]

private theorem archRealLift3_diag_mul_unipotent (y₁ y₂ x y z : ℝ) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
        upperUnipotent3 (archAdele x) (archAdele y) (archAdele z) =
      upperUnipotent3 (archAdele (y₁ * x)) (archAdele (y₂ * y)) (archAdele (y₁ * y₂ * z)) *
        WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) := by
  have hD : (Matrix.of fun i j : Fin 3 => if i = j then ![y₁ * y₂, y₂, 1] i else (0 : ℝ)).det ≠ 0 := by
    have h1 : (Matrix.of fun i j : Fin 3 => if i = j then ![y₁ * y₂, y₂, 1] i else (0 : ℝ)) =
        Matrix.diagonal ![y₁ * y₂, y₂, 1] := rfl
    rw [h1, Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    positivity
  have hN : ∀ a b c : ℝ,
      (Matrix.of fun i j => (!![1, a, c; 0, 1, b; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) i j).det ≠ 0 := by
    intro a b c
    simp [Matrix.det_fin_three]
  rw [← archRealLift3_unipotent, ← archRealLift3_unipotent, WhittakerBlock.archRealLift3_mul hD (hN _ _ _),
    WhittakerBlock.archRealLift3_mul (hN _ _ _) hD]
  congr 1
  funext a b
  have hmat : (Matrix.of fun i j : Fin 3 => if i = j then ![y₁ * y₂, y₂, 1] i else (0 : ℝ)) *
      Matrix.of (fun i j => (!![1, x, z; 0, 1, y; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) i j) =
      Matrix.of (fun i j => (!![1, y₁ * x, y₁ * y₂ * z; 0, 1, y₂ * y; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) i j) *
        Matrix.of fun i j : Fin 3 => if i = j then ![y₁ * y₂, y₂, 1] i else (0 : ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
    ring
  rw [hmat]

private theorem exists_archRealLift3_scalar_eq_centralScalarGL (c : ℝ) (hc : c ≠ 0) :
    ∃ ζ : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      WhittakerBlock.archRealLift3 (fun i j => if i = j then c else 0) = centralScalarGL 3 (𝓞 ℚ) ℚ ζ := by
  have hdet : (Matrix.of fun i j : Fin 3 => if i = j then c else (0 : ℝ)).det ≠ 0 := by
    have h1 : (Matrix.of fun i j : Fin 3 => if i = j then c else (0 : ℝ)) = Matrix.diagonal (fun _ => c) := rfl
    rw [h1, Matrix.det_diagonal, Fin.prod_univ_three]
    exact mul_ne_zero (mul_ne_zero hc hc) hc

  set s : AdeleRing (𝓞 ℚ) ℚ := ((StandardKernel.ofReal c, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
    with hs
  set s' : AdeleRing (𝓞 ℚ) ℚ :=
    ((StandardKernel.ofReal c⁻¹, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) with hs'
  have hss' : s * s' = 1 := by
    rw [hs, hs']
    show ((archOfRealHom c, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) *
      ((archOfRealHom c⁻¹, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (1 : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [Prod.mk_mul_mk, ← map_mul, mul_inv_cancel₀ hc, map_one, mul_one, Prod.mk_one_one]
  have hs's : s' * s = 1 := by
    rw [hs, hs']
    show ((archOfRealHom c⁻¹, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) *
      ((archOfRealHom c, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (1 : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [Prod.mk_mul_mk, ← map_mul, inv_mul_cancel₀ hc, map_one, mul_one, Prod.mk_one_one]
  refine ⟨⟨s, s', hss', hs's⟩, ?_⟩
  apply Units.ext
  rw [coe_archRealLift3_of_det_ne_zero hdet, archRealMat3_eq_mapMatrix]
  show archMatrixInclN (Fin 3) ℚ _ = Matrix.scalar (Fin 3) s
  ext i j
  simp only [archMatrixInclN, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply, hs]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply_eq, archOfRealHom_apply]
  · simp [hij, Matrix.one_apply_ne hij, map_zero, adele_zero_eq]

private theorem archRealLift3_realMat (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    WhittakerBlock.archRealLift3 (fun i j => StandardKernel.realMat h i j) = archInclN (Fin 3) ℚ h := by
  have hdet : (Matrix.of fun i j => StandardKernel.realMat h i j).det ≠ 0 := by
    show (StandardKernel.realGL h).val.det ≠ 0
    exact Matrix.GeneralLinearGroup.det_ne_zero _
  apply Units.ext
  rw [coe_archRealLift3_of_det_ne_zero hdet, archRealMat3_eq_mapMatrix]
  show archMatrixInclN (Fin 3) ℚ _ = archMatrixInclN (Fin 3) ℚ (h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, archOfRealHom_apply,
    StandardKernel.realMat_eq]
  exact StandardKernel.ofReal_realCoord _

private theorem whittaker3_centralScalarGL_mul (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h3 : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (ζ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ u (centralScalarGL 3 (𝓞 ℚ) ℚ ζ * g) =
      (ω ζ : ℂ) * whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ u g := by
  have hcomm : ∀ x y z : AdeleRing (𝓞 ℚ) ℚ,
      upperUnipotent3 x y z * (centralScalarGL 3 (𝓞 ℚ) ℚ ζ * g) =
        centralScalarGL 3 (𝓞 ℚ) ℚ ζ * (upperUnipotent3 x y z * g) := by
    intro x y z
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    apply Units.ext
    show (upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) *
        Matrix.scalar (Fin 3) (ζ : AdeleRing (𝓞 ℚ) ℚ) =
      Matrix.scalar (Fin 3) (ζ : AdeleRing (𝓞 ℚ) ℚ) * upperUnipotent3 x y z
    exact ((Matrix.scalar_commute (ζ : AdeleRing (𝓞 ℚ) ℚ) (fun r => Commute.all _ r) _).symm).eq
  simp only [whittaker3, hcomm, h3, mul_assoc, MeasureTheory.integral_const_mul]

private theorem isCompact_orthMat :
    IsCompact {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).transpose * Matrix.of e = 1} := by
  have hcont : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).transpose * Matrix.of e :=
    (Continuous.matrix_transpose continuous_id).matrix_mul continuous_id
  have hclosed : IsClosed {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).transpose * Matrix.of e = 1} :=
    isClosed_eq hcont continuous_const
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin 3 → Fin 3 → ℝ)) (r := 1)).subset fun e he => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  have h1 : ((Matrix.of e).transpose * Matrix.of e) j j = 1 := by
    rw [he]; exact Matrix.one_apply_eq j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply] at h1
  have h2 : e i j * e i j ≤ ∑ k, (Matrix.of e).transpose j k * Matrix.of e k j := by
    refine Finset.single_le_sum (f := fun k => (Matrix.of e).transpose j k * Matrix.of e k j)
      (fun k _ => ?_) (Finset.mem_univ i)
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact mul_self_nonneg _
  simp only [Matrix.transpose_apply, Matrix.of_apply] at h2
  rw [h1] at h2
  rw [Real.norm_eq_abs]
  exact abs_le_one_iff_mul_self_le_one.2 h2

private theorem archComponent3_archRealLift3_mem_orth3 (e : Fin 3 → Fin 3 → ℝ)
    (he : (Matrix.of e).transpose * Matrix.of e = 1) :
    archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 e) ∈ orth3 := by
  have hdet : (Matrix.of e).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det he
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hmat : ((archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 e) : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = archOfRealHom.mapMatrix (Matrix.of e) := by
    ext i j
    show AdelicLevel.adeleArch (𝓞 ℚ) ℚ
      (((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) =
      _
    rw [coe_archRealLift3_of_det_ne_zero hdet, archRealMat3_eq_mapMatrix, adeleArch_archMatrixInclN]
  show ((archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 e) : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * _ = 1
  rw [hmat, RingHom.mapMatrix_apply, ← Matrix.transpose_map, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, ← map_mul, he, map_one]

open NumberField.StandardAddChar in

private theorem psiQ_archAdele (s : ℝ) :
    psiQ (archAdele s) = Complex.exp (2 * Real.pi * Complex.I * s) := by
  rw [psiQ_apply]
  show psiArch (StandardKernel.ofReal s) * psiFin 0 = _
  rw [AddChar.map_zero_eq_one, mul_one, psiArch_apply, finprod_unique, psiArchPlace_apply]
  congr 2
  exact congrArg (fun r : ℝ => (r : ℂ))
    ((InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal (default : InfinitePlace ℚ))).apply_symm_apply s)

end PassageFurniture

section Passage

open AutomorphicForm

section PassA

open Matrix InnerProductSpace

private theorem exists_unipotent_mul_diagonal_mul_orthogonal_of_det_ne_zero
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det ≠ 0) (R : ℝ) (hR : ∀ i j, |M i j| ≤ R) :
    ∃ (N T K : Matrix (Fin 3) (Fin 3) ℝ), M = N * T * K ∧
      (∀ i, N i i = 1) ∧ (∀ i j, j < i → N i j = 0) ∧
      (∀ i j, i ≠ j → T i j = 0) ∧ (∀ i, 0 < T i i) ∧ K.transpose * K = 1 ∧
      (∀ i, T i i ≤ 3 * R) ∧ (∀ i, |M.det| / (3 * R) ^ 2 ≤ T i i) ∧
      (∀ i j, |N i j| ≤ 3 * R * (3 * R) ^ 2 / |M.det|) := by

  have hRpos : 0 < R := by
    rcases le_or_gt R 0 with hle | hpos
    · exfalso
      have h0 : M = 0 := by
        ext i j
        exact abs_nonpos_iff.mp ((hR i j).trans hle)
      exact hM (by rw [h0, Matrix.det_zero])
    · exact hpos
  have h3R : 0 < 3 * R := by linarith
  have hdet_pos : 0 < |M.det| := abs_pos.mpr hM

  obtain ⟨f, hf⟩ : ∃ f : Fin 3 → EuclideanSpace ℝ (Fin 3),
      f = fun m => WithLp.toLp 2 (M (Fin.rev m)) := ⟨_, rfl⟩
  have hfrev : ∀ i, f (Fin.rev i) = WithLp.toLp 2 (M i) := by
    intro i; rw [hf]; simp only [Fin.rev_rev]
  have hLIrow : LinearIndependent ℝ M.row :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM))
  have hLI : LinearIndependent ℝ f := by
    have h1 := (hLIrow.comp Fin.rev Fin.rev_injective).map'
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap (LinearEquiv.ker _)
    rw [hf]
    exact h1
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = Fintype.card (Fin 3) := by simp

  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
      b = gramSchmidtOrthonormalBasis (𝕜 := ℝ) hcard f := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
      b' = b.reindex Fin.revPerm := ⟨_, rfl⟩
  have hb'_apply : ∀ j, b' j = b (Fin.rev j) := by
    intro j; rw [hb', OrthonormalBasis.reindex_apply, Fin.revPerm_symm]; rfl

  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin 3) (Fin 3) ℝ,
      U = fun i j => inner ℝ (b' j) (WithLp.toLp 2 (M i)) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin 3) (Fin 3) ℝ, K = fun j l => b' j l := ⟨_, rfl⟩

  have hUtri : ∀ i j, j < i → U i j = 0 := by
    intro i j hij
    have h1 : Fin.rev i < Fin.rev j := Fin.rev_lt_rev.mpr hij
    have h2 := gramSchmidtOrthonormalBasis_inv_triangular (𝕜 := ℝ) hcard f h1
    rw [← hb, hfrev, ← hb'_apply] at h2
    rw [hU]; exact h2

  have hgs_inner : ∀ m, inner ℝ (gramSchmidt ℝ f m) (f m) = ‖gramSchmidt ℝ f m‖ ^ 2 := by
    intro m
    have hd := gramSchmidt_def'' ℝ f m
    conv_lhs => rw [hd]
    rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq, Finset.sum_eq_zero, add_zero]
    intro i hi
    rw [real_inner_smul_right, gramSchmidt_orthogonal ℝ f (Finset.mem_Iio.mp hi).ne', mul_zero]
  have hUpos : ∀ i, 0 < U i i := by
    intro i
    have hm : gramSchmidtNormed ℝ f (Fin.rev i) ≠ 0 := by
      intro h0
      have h1 := gramSchmidtNormed_unit_length (𝕜 := ℝ) (Fin.rev i) hLI
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hbapp : b (Fin.rev i) = gramSchmidtNormed ℝ f (Fin.rev i) := by
      rw [hb]; exact gramSchmidtOrthonormalBasis_apply (𝕜 := ℝ) hcard hm
    have hne : gramSchmidt ℝ f (Fin.rev i) ≠ 0 := gramSchmidt_ne_zero (𝕜 := ℝ) (Fin.rev i) hLI
    have hnorm : 0 < ‖gramSchmidt ℝ f (Fin.rev i)‖ := norm_pos_iff.mpr hne
    have hpos2 : 0 < inner ℝ (gramSchmidt ℝ f (Fin.rev i)) (f (Fin.rev i)) := by
      rw [hgs_inner]; exact pow_pos hnorm 2
    rw [hU]
    show 0 < inner ℝ (b' i) (WithLp.toLp 2 (M i))
    rw [hb'_apply, ← hfrev i, hbapp, gramSchmidtNormed, real_inner_smul_left]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    exact mul_pos (inv_pos.mpr hnorm) hpos2

  have hrow_norm : ∀ i, ‖(WithLp.toLp 2 (M i) : EuclideanSpace ℝ (Fin 3))‖ ≤ 3 * R := by
    intro i
    have hsq : ∑ l, ‖(WithLp.toLp 2 (M i) : EuclideanSpace ℝ (Fin 3)) l‖ ^ 2 ≤ (3 * R) ^ 2 := by
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
      have e0 := sq_le_sq' (abs_le.mp (hR i 0)).1 (abs_le.mp (hR i 0)).2
      have e1 := sq_le_sq' (abs_le.mp (hR i 1)).1 (abs_le.mp (hR i 1)).2
      have e2 := sq_le_sq' (abs_le.mp (hR i 2)).1 (abs_le.mp (hR i 2)).2
      have h9 : (3 * R) ^ 2 = 9 * R ^ 2 := by ring
      rw [h9]
      linarith [sq_nonneg R]
    calc ‖(WithLp.toLp 2 (M i) : EuclideanSpace ℝ (Fin 3))‖
        = Real.sqrt (∑ l, ‖(WithLp.toLp 2 (M i) : EuclideanSpace ℝ (Fin 3)) l‖ ^ 2) :=
          EuclideanSpace.norm_eq _
      _ ≤ Real.sqrt ((3 * R) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 3 * R := Real.sqrt_sq h3R.le
  have hUbound : ∀ i j, |U i j| ≤ 3 * R := by
    intro i j
    rw [hU]
    show |inner ℝ (b' j) (WithLp.toLp 2 (M i))| ≤ 3 * R
    have h1 := abs_real_inner_le_norm (b' j) (WithLp.toLp 2 (M i))
    rw [b'.orthonormal.1 j, one_mul] at h1
    exact h1.trans (hrow_norm i)
  have hUdiag_le : ∀ i, U i i ≤ 3 * R := fun i => (le_abs_self _).trans (hUbound i i)

  have hMUK : M = U * K := by
    ext i l
    have hexp := b'.sum_repr' (WithLp.toLp 2 (M i))
    have hl : (WithLp.toLp 2 (M i) : EuclideanSpace ℝ (Fin 3)) l
        = ∑ j, inner ℝ (b' j) (WithLp.toLp 2 (M i)) * b' j l := by
      conv_lhs => rw [← hexp]
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Matrix.mul_apply, hU, hK]
    simpa only [WithLp.ofLp_toLp] using hl

  have hKK : K * Kᵀ = 1 := by
    ext j j'
    have h := (orthonormal_iff_ite.mp b'.orthonormal) j j'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hK]
    rw [← h]
    show ∑ x, (b' j).ofLp x * (b' j').ofLp x = (b' j').ofLp ⬝ᵥ star (b' j).ofLp
    simp only [dotProduct, star_trivial]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hKtK : Kᵀ * K = 1 := mul_eq_one_comm.mp hKK

  have hdetK : |K.det| = 1 := by
    have h2 : K.det * K.det = 1 := by
      have h3 : Kᵀ.det * K.det = 1 := by rw [← Matrix.det_mul, hKtK, Matrix.det_one]
      rwa [Matrix.det_transpose] at h3
    have h4 : |K.det| ^ 2 = 1 := by rw [sq_abs, sq, h2]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).mp h4
  have hUblock : U.BlockTriangular id := fun i j hij => hUtri i j hij
  have hdetU : U.det = ∏ i, U i i := Matrix.det_of_upperTriangular hUblock
  have hprod_pos : 0 < ∏ i, U i i := Finset.prod_pos fun i _ => hUpos i
  have hdetM : |M.det| = ∏ i, U i i := by
    rw [hMUK, Matrix.det_mul, abs_mul, hdetK, mul_one, hdetU, abs_of_pos hprod_pos]

  have hUlow : ∀ i, |M.det| / (3 * R) ^ 2 ≤ U i i := by
    intro i
    have hprod : ∏ j ∈ Finset.univ.erase i, U j j ≤ (3 * R) ^ 2 := by
      calc ∏ j ∈ Finset.univ.erase i, U j j ≤ ∏ j ∈ Finset.univ.erase i, (3 * R) :=
            Finset.prod_le_prod (fun j _ => (hUpos j).le) (fun j _ => hUdiag_le j)
        _ = (3 * R) ^ 2 := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
              Finset.card_univ, Fintype.card_fin]
    have hsplit : |M.det| = (∏ j ∈ Finset.univ.erase i, U j j) * U i i := by
      rw [hdetM]
      exact (Finset.prod_erase_mul Finset.univ (fun j => U j j) (Finset.mem_univ i)).symm
    rw [div_le_iff₀ (pow_pos h3R 2), hsplit]
    calc (∏ j ∈ Finset.univ.erase i, U j j) * U i i ≤ (3 * R) ^ 2 * U i i :=
          mul_le_mul_of_nonneg_right hprod (hUpos i).le
      _ = U i i * (3 * R) ^ 2 := mul_comm _ _

  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin 3) (Fin 3) ℝ, T = Matrix.diagonal (fun i => U i i) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 3) (Fin 3) ℝ,
      N = U * Matrix.diagonal (fun i => (U i i)⁻¹) := ⟨_, rfl⟩
  have hdiag1 : (fun i => (U i i)⁻¹ * U i i) = fun _ => (1 : ℝ) :=
    funext fun i => inv_mul_cancel₀ (hUpos i).ne'
  have hNT : N * T = U := by
    rw [hN, hT, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, hdiag1, Matrix.diagonal_one,
      Matrix.mul_one]
  refine ⟨N, T, K, ?_, ?_, ?_, ?_, ?_, hKtK, ?_, ?_, ?_⟩
  · rw [hMUK, hNT]
  · intro i
    rw [hN, Matrix.mul_diagonal]
    exact mul_inv_cancel₀ (hUpos i).ne'
  · intro i j hij
    rw [hN, Matrix.mul_diagonal, hUtri i j hij, zero_mul]
  · intro i j hij
    rw [hT, Matrix.diagonal_apply_ne _ hij]
  · intro i
    rw [hT, Matrix.diagonal_apply_eq]
    exact hUpos i
  · intro i
    rw [hT, Matrix.diagonal_apply_eq]
    exact hUdiag_le i
  · intro i
    rw [hT, Matrix.diagonal_apply_eq]
    exact hUlow i
  · intro i j
    rw [hN, Matrix.mul_diagonal]
    show |U i j * (U j j)⁻¹| ≤ 3 * R * (3 * R) ^ 2 / |M.det|
    rw [abs_mul, abs_inv, abs_of_pos (hUpos j)]
    have hinv : (U j j)⁻¹ ≤ (3 * R) ^ 2 / |M.det| := by
      rw [← inv_div]
      exact inv_anti₀ (div_pos hdet_pos (pow_pos h3R 2)) (hUlow j)
    calc |U i j| * (U j j)⁻¹ ≤ 3 * R * ((3 * R) ^ 2 / |M.det|) :=
          mul_le_mul (hUbound i j) hinv (inv_nonneg.mpr (hUpos j).le) h3R.le
      _ = 3 * R * (3 * R) ^ 2 / |M.det| := by rw [mul_div_assoc]

end PassA

private theorem continuous_realMat_archComponent3 :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) := by
  have hreal : Continuous StandardKernel.realCoord :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
      (continuous_apply Rat.infinitePlace)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hentry : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) :=
    (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ).comp (Units.continuous_val.matrix_elem i j)
  exact hreal.comp hentry

private theorem exists_bounds_on_compact (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK : IsCompact K) :
    ∃ R c₀ : ℝ, 1 ≤ R ∧ 0 < c₀ ∧ ∀ g ∈ K,
      (∀ i j, |StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) i j| ≤ R) ∧
      c₀ ≤ |(StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g)).det| := by
  classical
  set M : AdelicGL 3 (𝓞 ℚ) ℚ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun g => StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) with hM
  have hMc : Continuous M := continuous_realMat_archComponent3
  have hsum : Continuous fun g => ∑ i : Fin 3, ∑ j : Fin 3, |M g i j| := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (hMc.matrix_elem i j).abs
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn hsum.continuousOn
  have hdet : Continuous fun g => |(M g).det| := hMc.matrix_det.abs
  have hdetpos : ∀ g, 0 < |(M g).det| := by
    intro g
    rw [abs_pos]
    exact Matrix.GeneralLinearGroup.det_ne_zero (StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ g))
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, 1, le_rfl, one_pos, fun g hg => ?_⟩
    rw [hKe] at hg
    exact absurd hg (Set.notMem_empty g)
  obtain ⟨g₀, -, hg₀min⟩ := hK.exists_isMinOn hKne hdet.continuousOn
  refine ⟨max R₀ 1, |(M g₀).det|, le_max_right _ _, hdetpos g₀, fun g hg => ⟨fun i j => ?_, hg₀min hg⟩⟩
  have h1 := hR₀ g hg
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg (M g i j))] at h1
  have h2 : |M g i j| ≤ ∑ j : Fin 3, |M g i j| :=
    Finset.single_le_sum (f := fun j => |M g i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h3 : ∑ j : Fin 3, |M g i j| ≤ ∑ i : Fin 3, ∑ j : Fin 3, |M g i j| :=
    Finset.single_le_sum (f := fun i => ∑ j : Fin 3, |M g i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  exact (h2.trans (h3.trans h1)).trans (le_max_left _ _)

private theorem diag_mul_eq_of_iwasawa (g : AdelicGL 3 (𝓞 ℚ) ℚ) (Nm T Km : Matrix (Fin 3) (Fin 3) ℝ)
    (hMeq : StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) = Nm * T * Km)
    (hN1 : ∀ i, Nm i i = 1) (hN0 : ∀ i j, j < i → Nm i j = 0)
    (hT0 : ∀ i j, i ≠ j → T i j = 0) (hTpos : ∀ i, 0 < T i i) (hKm : Km.transpose * Km = 1)
    (y₁ y₂ : ℝ) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    ∃ ζ : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      WhittakerBlock.archRealLift3 (fun i j => if i = j then T 2 2 else 0) = centralScalarGL 3 (𝓞 ℚ) ℚ ζ ∧
      WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * g =
        upperUnipotent3 (archAdele (y₁ * Nm 0 1)) (archAdele (y₂ * Nm 1 2)) (archAdele (y₁ * y₂ * Nm 0 2)) *
          (centralScalarGL 3 (𝓞 ℚ) ℚ ζ *
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then
                ![y₁ * (T 0 0 / T 1 1) * (y₂ * (T 1 1 / T 2 2)), y₂ * (T 1 1 / T 2 2), 1] i else 0) *
              (WhittakerBlock.archRealLift3 (fun i j => Km i j) *
                ((WhittakerBlock.archRealLift3
                  (fun i j => StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) i j))⁻¹ * g)))) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_archRealLift3_scalar_eq_centralScalarGL (T 2 2) (hTpos 2).ne'
  refine ⟨ζ, hζ, ?_⟩
  have ht0 := hTpos 0
  have ht1 := hTpos 1
  have ht2 := hTpos 2

  have h10 := hN0 1 0 (by decide)
  have h20 := hN0 2 0 (by decide)
  have h21 := hN0 2 1 (by decide)
  have hNlit : (fun i j => Nm i j) =
      fun i j => (!![1, Nm 0 1, Nm 0 2; 0, 1, Nm 1 2; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [hN1, h10, h20, h21]
  have hTlit : (fun i j => T i j) = fun i j : Fin 3 => if i = j then ![T 0 0, T 1 1, T 2 2] i else (0 : ℝ) := by
    funext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp
    · rw [if_neg hij]
      exact hT0 i j hij

  have hdetN : (Matrix.of fun i j => Nm i j).det ≠ 0 := by
    rw [hNlit]
    simp [Matrix.det_fin_three]
  have hdetT : (Matrix.of fun i j => T i j).det ≠ 0 := by
    rw [hTlit]
    have h1 : (Matrix.of fun i j : Fin 3 => if i = j then ![T 0 0, T 1 1, T 2 2] i else (0 : ℝ)) =
        Matrix.diagonal ![T 0 0, T 1 1, T 2 2] := rfl
    rw [h1, Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    positivity
  have hdetK : (Matrix.of fun i j => Km i j).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hKm
    rw [Matrix.det_mul, Matrix.det_transpose] at h1
    have h2 : (Matrix.of fun i j => Km i j) = Km := rfl
    rw [h2] at h0
    rw [h0, mul_zero, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hdetTK : (Matrix.of fun a b => (Matrix.of (fun i j => T i j) * Matrix.of fun i j => Km i j) a b).det ≠ 0 := by
    have h1 : (Matrix.of fun a b => (Matrix.of (fun i j => T i j) * Matrix.of fun i j => Km i j) a b) =
        Matrix.of (fun i j => T i j) * Matrix.of fun i j => Km i j := rfl
    rw [h1, Matrix.det_mul]
    exact mul_ne_zero hdetT hdetK
  have hdetD : ∀ d₁ d₂ : ℝ, 0 < d₁ → 0 < d₂ →
      (Matrix.of fun i j : Fin 3 => if i = j then ![d₁, d₂, 1] i else (0 : ℝ)).det ≠ 0 := by
    intro d₁ d₂ hd₁ hd₂
    have h1 : (Matrix.of fun i j : Fin 3 => if i = j then ![d₁, d₂, 1] i else (0 : ℝ)) =
        Matrix.diagonal ![d₁, d₂, 1] := rfl
    rw [h1, Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    positivity
  have hdetS : (Matrix.of fun i j : Fin 3 => if i = j then T 2 2 else (0 : ℝ)).det ≠ 0 := by
    have h1 : (Matrix.of fun i j : Fin 3 => if i = j then T 2 2 else (0 : ℝ)) = Matrix.diagonal (fun _ => T 2 2) :=
      rfl
    rw [h1, Matrix.det_diagonal, Fin.prod_univ_three]
    positivity

  have hsplit : WhittakerBlock.archRealLift3 (fun i j => StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) i j) =
      WhittakerBlock.archRealLift3 (fun i j => Nm i j) *
        (WhittakerBlock.archRealLift3 (fun i j => T i j) * WhittakerBlock.archRealLift3 (fun i j => Km i j)) := by
    rw [WhittakerBlock.archRealLift3_mul hdetT hdetK, WhittakerBlock.archRealLift3_mul hdetN hdetTK]
    congr 1
    funext a b
    show StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) a b = (Nm * (T * Km)) a b
    rw [hMeq, Matrix.mul_assoc]

  have hdiagT : WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
      WhittakerBlock.archRealLift3 (fun i j => T i j) =
      WhittakerBlock.archRealLift3 (fun i j => if i = j then T 2 2 else 0) *
        WhittakerBlock.archRealLift3 (fun i j => if i = j then
          ![y₁ * (T 0 0 / T 1 1) * (y₂ * (T 1 1 / T 2 2)), y₂ * (T 1 1 / T 2 2), 1] i else 0) := by
    rw [hTlit, WhittakerBlock.archRealLift3_mul (hdetD _ _ (by positivity) hy₂) (by rw [← hTlit]; exact hdetT),
      WhittakerBlock.archRealLift3_mul hdetS (hdetD _ _ (by positivity) (by positivity))]
    congr 1
    funext a b
    have hmat : (Matrix.of fun i j : Fin 3 => if i = j then ![y₁ * y₂, y₂, 1] i else (0 : ℝ)) *
        Matrix.of (fun i j : Fin 3 => if i = j then ![T 0 0, T 1 1, T 2 2] i else (0 : ℝ)) =
        Matrix.of (fun i j : Fin 3 => if i = j then T 2 2 else (0 : ℝ)) *
          Matrix.of (fun i j : Fin 3 => if i = j then
            ![y₁ * (T 0 0 / T 1 1) * (y₂ * (T 1 1 / T 2 2)), y₂ * (T 1 1 / T 2 2), 1] i else (0 : ℝ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> field_simp
    exact congrFun (congrFun hmat a) b

  have hconj := archRealLift3_diag_mul_unipotent y₁ y₂ (Nm 0 1) (Nm 1 2) (Nm 0 2) hy₁ hy₂
  have hNlift : WhittakerBlock.archRealLift3 (fun i j => Nm i j) =
      upperUnipotent3 (archAdele (Nm 0 1)) (archAdele (Nm 1 2)) (archAdele (Nm 0 2)) := by
    rw [hNlit]
    exact archRealLift3_unipotent _ _ _

  set gf' : AdelicGL 3 (𝓞 ℚ) ℚ :=
    (WhittakerBlock.archRealLift3 (fun i j => StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) i j))⁻¹ * g
    with hgf'
  calc WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * g
      = WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
          (WhittakerBlock.archRealLift3 (fun i j => StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) i j) * gf') := by
        rw [hgf', mul_inv_cancel_left]
    _ = WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
          (upperUnipotent3 (archAdele (Nm 0 1)) (archAdele (Nm 1 2)) (archAdele (Nm 0 2)) *
            (WhittakerBlock.archRealLift3 (fun i j => T i j) * WhittakerBlock.archRealLift3 (fun i j => Km i j))) *
          gf' := by
        rw [hsplit, hNlift]
        simp only [mul_assoc]
    _ = _ := by
        simp only [mul_assoc]
        rw [← mul_assoc (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))
            (upperUnipotent3 (archAdele (Nm 0 1)) (archAdele (Nm 1 2)) (archAdele (Nm 0 2))),
          hconj,
          mul_assoc (upperUnipotent3 (archAdele (y₁ * Nm 0 1)) (archAdele (y₂ * Nm 1 2))
            (archAdele (y₁ * y₂ * Nm 0 2))),
          ← mul_assoc (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))
            (WhittakerBlock.archRealLift3 (fun i j => T i j)),
          hdiagT, ← hζ]
        simp only [mul_assoc]

end Passage

open AutomorphicForm in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : Continuous u)
    (h2 : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (h3 : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK : IsCompact K) :
    ∃ (lam₀ nB Ω : ℝ) (K₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)), 0 < lam₀ ∧ lam₀ ≤ 1 ∧ 0 ≤ nB ∧ 0 ≤ Ω ∧ IsCompact K₀ ∧
      (∀ k' ∈ K₀, archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3) ∧
      ∀ g ∈ K, ∃ (lam τ n₁ n₂ : ℝ) (κ₁ : ℂ) (k' : AdelicGL 3 (𝓞 ℚ) ℚ), k' ∈ K₀ ∧
        lam₀ ≤ lam ∧ lam ≤ lam₀⁻¹ ∧ lam₀ ≤ τ ∧ τ ≤ lam₀⁻¹ ∧ |n₁| ≤ nB ∧ |n₂| ≤ nB ∧ ‖κ₁‖ ≤ Ω ∧
        ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * g) =
            κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) *
              whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                NumberField.StandardAddChar.psiQ u
                (WhittakerBlock.archRealLift3
                    (fun i j => if i = j then ![lam * y₁ * (τ * y₂), τ * y₂, 1] i else 0) * k') := by
  classical

  obtain ⟨R, c₀, hR1, hc₀, hbd⟩ := exists_bounds_on_compact K hK
  set M : AdelicGL 3 (𝓞 ℚ) ℚ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun g => StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) with hM
  have hMdet : ∀ g, (M g).det ≠ 0 := fun g =>
    Matrix.GeneralLinearGroup.det_ne_zero (StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ g))
  have hR0 : 0 < R := by linarith

  have hIw : ∀ g ∈ K, ∃ NTK : Matrix (Fin 3) (Fin 3) ℝ × Matrix (Fin 3) (Fin 3) ℝ × Matrix (Fin 3) (Fin 3) ℝ,
      M g = NTK.1 * NTK.2.1 * NTK.2.2 ∧ (∀ i, NTK.1 i i = 1) ∧ (∀ i j, j < i → NTK.1 i j = 0) ∧
      (∀ i j, i ≠ j → NTK.2.1 i j = 0) ∧ (∀ i, 0 < NTK.2.1 i i) ∧ NTK.2.2.transpose * NTK.2.2 = 1 ∧
      (∀ i, NTK.2.1 i i ≤ 3 * R) ∧ (∀ i, |(M g).det| / (3 * R) ^ 2 ≤ NTK.2.1 i i) ∧
      (∀ i j, |NTK.1 i j| ≤ 3 * R * (3 * R) ^ 2 / |(M g).det|) := by
    intro g hg
    obtain ⟨Nm, T, Km, h⟩ :=
      exists_unipotent_mul_diagonal_mul_orthogonal_of_det_ne_zero (M g) (hMdet g) R (hbd g hg).1
    exact ⟨(Nm, T, Km), h⟩
  choose! NTK hIw using hIw

  set tmin : ℝ := c₀ / (3 * R) ^ 2 with htmin
  set tmax : ℝ := 3 * R with htmax
  set nB : ℝ := 3 * R * (3 * R) ^ 2 / c₀ with hnB
  have htmin_pos : 0 < tmin := by positivity
  have htmax_pos : 0 < tmax := by positivity
  have hnB_pos : 0 < nB := by positivity
  have hT_ge : ∀ g ∈ K, ∀ i, tmin ≤ (NTK g).2.1 i i := by
    intro g hg i
    refine le_trans ?_ ((hIw g hg).2.2.2.2.2.2.2.1 i)
    exact div_le_div_of_nonneg_right (hbd g hg).2 (by positivity)
  have hT_le : ∀ g ∈ K, ∀ i, (NTK g).2.1 i i ≤ tmax := fun g hg i => (hIw g hg).2.2.2.2.2.2.1 i
  have hN_le : ∀ g ∈ K, ∀ i j, |(NTK g).1 i j| ≤ nB := by
    intro g hg i j
    refine ((hIw g hg).2.2.2.2.2.2.2.2 i j).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) hc₀ (hbd g hg).2

  set gf : AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ :=
    fun g => (WhittakerBlock.archRealLift3 (fun i j => M g i j))⁻¹ * g with hgf
  set Φ : (Fin 3 → Fin 3 → ℝ) × AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ :=
    fun p => WhittakerBlock.archRealLift3 p.1 * gf p.2 with hΦ
  set orthMat : Set (Fin 3 → Fin 3 → ℝ) := {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).transpose * Matrix.of e = 1}
    with horthMat
  set K₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := Φ '' (orthMat ×ˢ K) with hK₀def
  have hgf_cont : ContinuousOn gf K := by
    have h1 : ContinuousOn (fun g => WhittakerBlock.archRealLift3 (fun i j => M g i j)) K := by
      refine continuousOn_archRealLift3_detSet.comp ?_ ?_
      · exact continuous_realMat_archComponent3.continuousOn
      · intro g _
        exact hMdet g
    exact h1.inv.mul continuousOn_id
  have hΦ_cont : ContinuousOn Φ (orthMat ×ˢ K) := by
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_archRealLift3_detSet.comp continuousOn_fst ?_
      rintro ⟨e, g⟩ ⟨he, -⟩
      show (Matrix.of e).det ≠ 0
      intro h0
      have h1 := congrArg Matrix.det he
      rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero, Matrix.det_one] at h1
      exact zero_ne_one h1
    · exact hgf_cont.comp continuousOn_snd fun p hp => hp.2
  have hK₀ : IsCompact K₀ := (isCompact_orthMat.prod hK).image_of_continuousOn hΦ_cont
  have harch_gf : ∀ g, archComponent3 (𝓞 ℚ) ℚ (gf g) = 1 := by
    intro g
    show archComponent3 (𝓞 ℚ) ℚ ((WhittakerBlock.archRealLift3 (fun i j => M g i j))⁻¹ * g) = 1
    rw [map_mul, map_inv, archRealLift3_realMat, archComponentN_archInclN, inv_mul_cancel]
  have horth : ∀ k ∈ K₀, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 := by
    rintro k ⟨⟨e, g⟩, ⟨he, -⟩, rfl⟩
    show archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 e * gf g) ∈ orth3
    rw [map_mul, harch_gf, mul_one]
    exact archComponent3_archRealLift3_mem_orth3 e he

  set lam₀ : ℝ := min (tmin / tmax) 1 with hlam₀
  have hlam₀pos : 0 < lam₀ := lt_min (by positivity) one_pos
  have hlam₀le1 : lam₀ ≤ 1 := min_le_right _ _
  have hlam₀inv : tmax / tmin ≤ lam₀⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hlam₀pos, inv_div]
    exact min_le_left _ _
  have harchAdele_add : ∀ x y : ℝ, archAdele (x + y) = archAdele x + archAdele y := by
    intro x y
    show ((archOfRealHom (x + y), 0) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) =
      ((archOfRealHom x, 0) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) +
        ((archOfRealHom y, 0) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [Prod.mk_add_mk, map_add, add_zero]

  have hgeom : ∀ g ∈ K,
      lam₀ ≤ (NTK g).2.1 0 0 / (NTK g).2.1 1 1 ∧ (NTK g).2.1 0 0 / (NTK g).2.1 1 1 ≤ lam₀⁻¹ ∧
      lam₀ ≤ (NTK g).2.1 1 1 / (NTK g).2.1 2 2 ∧ (NTK g).2.1 1 1 / (NTK g).2.1 2 2 ≤ lam₀⁻¹ := by
    intro g hg
    obtain ⟨-, -, -, -, hTpos, -, -, -, -⟩ := hIw g hg
    have ht0 := hTpos 0
    have ht1 := hTpos 1
    have ht2 := hTpos 2
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (min_le_left _ _).trans ?_
      rw [div_le_div_iff₀ htmax_pos ht1]
      calc tmin * (NTK g).2.1 1 1 ≤ (NTK g).2.1 0 0 * (NTK g).2.1 1 1 :=
            mul_le_mul_of_nonneg_right (hT_ge g hg 0) ht1.le
        _ ≤ (NTK g).2.1 0 0 * tmax := mul_le_mul_of_nonneg_left (hT_le g hg 1) ht0.le
    · refine le_trans ?_ hlam₀inv
      rw [div_le_div_iff₀ ht1 htmin_pos]
      calc (NTK g).2.1 0 0 * tmin ≤ tmax * tmin := mul_le_mul_of_nonneg_right (hT_le g hg 0) htmin_pos.le
        _ ≤ tmax * (NTK g).2.1 1 1 := mul_le_mul_of_nonneg_left (hT_ge g hg 1) htmax_pos.le
    · refine (min_le_left _ _).trans ?_
      rw [div_le_div_iff₀ htmax_pos ht2]
      calc tmin * (NTK g).2.1 2 2 ≤ (NTK g).2.1 1 1 * (NTK g).2.1 2 2 :=
            mul_le_mul_of_nonneg_right (hT_ge g hg 1) ht2.le
        _ ≤ (NTK g).2.1 1 1 * tmax := mul_le_mul_of_nonneg_left (hT_le g hg 2) ht1.le
    · refine le_trans ?_ hlam₀inv
      rw [div_le_div_iff₀ ht2 htmin_pos]
      calc (NTK g).2.1 1 1 * tmin ≤ tmax * tmin := mul_le_mul_of_nonneg_right (hT_le g hg 1) htmin_pos.le
        _ ≤ tmax * (NTK g).2.1 2 2 := mul_le_mul_of_nonneg_left (hT_ge g hg 2) htmax_pos.le

  by_cases hu0 : u = 0
  · refine ⟨lam₀, nB, 0, K₀, hlam₀pos, hlam₀le1, hnB_pos.le, le_rfl, hK₀, horth, ?_⟩
    intro g hg
    obtain ⟨hMeq, hN1, hN0, hT0, hTpos, hKorth, -, -, -⟩ := hIw g hg
    obtain ⟨hl1, hl2, hl3, hl4⟩ := hgeom g hg
    refine ⟨(NTK g).2.1 0 0 / (NTK g).2.1 1 1, (NTK g).2.1 1 1 / (NTK g).2.1 2 2, (NTK g).1 0 1, (NTK g).1 1 2,
      0, WhittakerBlock.archRealLift3 (fun i j => (NTK g).2.2 i j) * gf g, ?_, hl1, hl2, hl3, hl4,
      hN_le g hg 0 1, hN_le g hg 1 2, by simp, fun y₁ y₂ _ _ => ?_⟩
    · exact ⟨(fun i j => (NTK g).2.2 i j, g), ⟨hKorth, hg⟩, rfl⟩
    · subst hu0
      simp [LanglandsTunnell.CubicInduction.whittaker3]

  obtain ⟨g₁, hg₁⟩ : ∃ g₁, u g₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : ℝ, ∀ t : ℝ, tmin ≤ t → t ≤ tmax → ∀ ζ : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      WhittakerBlock.archRealLift3 (fun i j => if i = j then t else 0) = centralScalarGL 3 (𝓞 ℚ) ℚ ζ →
      ‖(ω ζ : ℂ)‖ ≤ Ω := by
    have hφ : ContinuousOn (fun t : ℝ => u (WhittakerBlock.archRealLift3 (fun i j => if i = j then t else 0) * g₁))
        (Set.Icc tmin tmax) := by
      refine hu.comp_continuousOn (ContinuousOn.mul ?_ continuousOn_const)
      refine continuousOn_archRealLift3_detSet.comp ?_ ?_
      · exact (continuous_pi fun i => continuous_pi fun j => by split_ifs <;> fun_prop).continuousOn
      · intro t ht
        show (Matrix.of fun i j : Fin 3 => if i = j then t else (0 : ℝ)).det ≠ 0
        have h1' : (Matrix.of fun i j : Fin 3 => if i = j then t else (0 : ℝ)) = Matrix.diagonal (fun _ => t) := rfl
        rw [h1', Matrix.det_diagonal, Fin.prod_univ_three]
        have : 0 < t := htmin_pos.trans_le ht.1
        positivity
    obtain ⟨Φ₀, hΦ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
    refine ⟨Φ₀ / ‖u g₁‖, fun t htl htu ζ hζ => ?_⟩
    have h := h3 ζ g₁
    rw [← hζ] at h
    have h' := hΦ₀ t ⟨htl, htu⟩
    rw [h, norm_mul] at h'
    exact (le_div_iff₀ (norm_pos_iff.2 hg₁)).2 h'
  have hωeq : ∀ ζ ζ' : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      centralScalarGL 3 (𝓞 ℚ) ℚ ζ = centralScalarGL 3 (𝓞 ℚ) ℚ ζ' → (ω ζ : ℂ) = ω ζ' := by
    intro ζ ζ' h
    have h1' := h3 ζ g₁
    have h2' := h3 ζ' g₁
    rw [h] at h1'
    exact mul_right_cancel₀ hg₁ (h1'.symm.trans h2')
  refine ⟨lam₀, nB, max Ω 0, K₀, hlam₀pos, hlam₀le1, hnB_pos.le, le_max_right _ _, hK₀, horth, ?_⟩
  intro g hg
  obtain ⟨hMeq, hN1, hN0, hT0, hTpos, hKorth, -, -, -⟩ := hIw g hg
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hgeom g hg

  obtain ⟨ζ₁, hζ₁⟩ := exists_archRealLift3_scalar_eq_centralScalarGL ((NTK g).2.1 2 2) (hTpos 2).ne'
  set k' : AdelicGL 3 (𝓞 ℚ) ℚ := WhittakerBlock.archRealLift3 (fun i j => (NTK g).2.2 i j) * gf g with hk'
  refine ⟨(NTK g).2.1 0 0 / (NTK g).2.1 1 1, (NTK g).2.1 1 1 / (NTK g).2.1 2 2, (NTK g).1 0 1, (NTK g).1 1 2,
    (ω ζ₁ : ℂ), k', ⟨(fun i j => (NTK g).2.2 i j, g), ⟨hKorth, hg⟩, rfl⟩, hl1, hl2, hl3, hl4,
    hN_le g hg 0 1, hN_le g hg 1 2, (hΩ _ (hT_ge g hg 2) (hT_le g hg 2) ζ₁ hζ₁).trans (le_max_left _ _),
    fun y₁ y₂ hy₁ hy₂ => ?_⟩

  obtain ⟨ζ, hζ, hid⟩ := diag_mul_eq_of_iwasawa g (NTK g).1 (NTK g).2.1 (NTK g).2.2 hMeq hN1 hN0 hT0 hTpos hKorth
    y₁ y₂ hy₁ hy₂
  have harr : (fun i j => if i = j then
      ![y₁ * ((NTK g).2.1 0 0 / (NTK g).2.1 1 1) * (y₂ * ((NTK g).2.1 1 1 / (NTK g).2.1 2 2)),
        y₂ * ((NTK g).2.1 1 1 / (NTK g).2.1 2 2), 1] i else (0 : ℝ)) =
      fun i j => if i = j then ![(NTK g).2.1 0 0 / (NTK g).2.1 1 1 * y₁ * ((NTK g).2.1 1 1 / (NTK g).2.1 2 2 * y₂),
        (NTK g).2.1 1 1 / (NTK g).2.1 2 2 * y₂, 1] i else 0 := by
    funext i j
    rw [mul_comm y₁ ((NTK g).2.1 0 0 / (NTK g).2.1 1 1), mul_comm y₂ ((NTK g).2.1 1 1 / (NTK g).2.1 2 2)]
  rw [hid, harr,
    (LanglandsTunnell.CubicInduction.whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
      u h2).1, whittaker3_centralScalarGL_mul u ω h3, hωeq ζ ζ₁ (hζ.symm.trans hζ₁), ← harchAdele_add,
    psiQ_archAdele]
  ring

end S_LanglandsTunnell_CubicInduction_exists_whittaker3_diag_mul_transport_of_isCompact
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker3_diag_mul_transport_of_isCompact (solution)
