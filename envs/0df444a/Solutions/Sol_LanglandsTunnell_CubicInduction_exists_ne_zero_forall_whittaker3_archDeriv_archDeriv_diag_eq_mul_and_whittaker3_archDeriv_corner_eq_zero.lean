-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3455e8ad-6086-519a-99fb-dd6eb488731a

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

noncomputable section

namespace WsC
namespace QW

open MeasureTheory NumberField.StandardAddChar
open AutomorphicForm.StandardKernel (ofReal)

private theorem ofReal_mul (r s : ℝ) : ofReal (r * s) = ofReal r * ofReal s :=
  funext fun _ => map_mul _ r s

private theorem ofReal_one : ofReal 1 = 1 :=
  funext fun _ => map_one _

private theorem ofReal_zero : ofReal 0 = 0 :=
  funext fun _ => map_zero _

private theorem ofReal_add (r s : ℝ) : ofReal (r + s) = ofReal r + ofReal s :=
  funext fun _ => map_add _ r s

private noncomputable def archAdele (u : ℝ) : AdeleRing (𝓞 ℚ) ℚ :=
  (⟨ofReal u, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)

private theorem archAdele_add (u v : ℝ) : archAdele (u + v) = archAdele u + archAdele v := by
  apply Prod.ext
  · exact ofReal_add u v
  · exact (add_zero (0 : FiniteAdeleRing (𝓞 ℚ) ℚ)).symm

private theorem archAdele_zero : archAdele 0 = 0 :=
  Prod.ext ofReal_zero rfl

private noncomputable def archScalarIdele (r : ℝ) (hr : r ≠ 0) : (AdeleRing (𝓞 ℚ) ℚ)ˣ where
  val := (⟨ofReal r, 1⟩ : AdeleRing (𝓞 ℚ) ℚ)
  inv := (⟨ofReal r⁻¹, 1⟩ : AdeleRing (𝓞 ℚ) ℚ)
  val_inv := by
    apply Prod.ext
    · show ofReal r * ofReal r⁻¹ = 1
      rw [← ofReal_mul, mul_inv_cancel₀ hr, ofReal_one]
    · exact mul_one _
  inv_val := by
    apply Prod.ext
    · show ofReal r⁻¹ * ofReal r = 1
      rw [← ofReal_mul, inv_mul_cancel₀ hr, ofReal_one]
    · exact mul_one _

private theorem archScalarIdele_mul_inv_smul_archAdele (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (u : ℝ) :
    (archScalarIdele r hr * (archScalarIdele s hs)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) • archAdele u =
      archAdele (r * s⁻¹ * u) := by
  rw [Units.smul_def, smul_eq_mul, Units.val_mul]
  apply Prod.ext
  · change ofReal r * ofReal s⁻¹ * ofReal u = ofReal (r * s⁻¹ * u)
    rw [ofReal_mul, ofReal_mul]
  · change (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * 1 * 0 = 0
    rw [mul_zero]

private theorem archRealMat3_diagonal (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    WhittakerBlock.archRealMat3 (fun i j => if i = j then a i else 0) =
      Matrix.diagonal fun i =>
        ((archScalarIdele (a i) (ha i) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) := by
  ext i j
  unfold WhittakerBlock.archRealMat3 AutomorphicForm.archMatrixInclN
  by_cases h : i = j
  · subst h
    simp only [Matrix.of_apply, if_true, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · simp only [Matrix.of_apply, if_neg h, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h, ofReal_zero]
    rfl

private theorem isUnit_archRealMat3_diagonal (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 (fun i j => if i = j then a i else 0)) := by
  rw [archRealMat3_diagonal a ha, Matrix.isUnit_diagonal]
  exact isUnit_iff_exists_inv.mpr ⟨fun i => ((archScalarIdele (a i) (ha i))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ),
    funext fun i => (archScalarIdele (a i) (ha i)).mul_inv⟩

private theorem coe_archRealLift3_diagonal (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      Matrix.diagonal fun i =>
        ((archScalarIdele (a i) (ha i) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3_diagonal a ha), IsUnit.unit_spec, archRealMat3_diagonal a ha]

private theorem archRealLift3_diagonal_eq (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) =
      ⟨Matrix.diagonal fun i =>
          ((archScalarIdele (a i) (ha i) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ),
        Matrix.diagonal fun i =>
          (((archScalarIdele (a i) (ha i))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ),
        by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact Units.mul_inv _,
        by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact Units.inv_mul _⟩ :=
  Units.ext (coe_archRealLift3_diagonal a ha)

private theorem coe_inv_archRealLift3_diagonal (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    (((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0))⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      Matrix.diagonal fun i =>
        (((archScalarIdele (a i) (ha i))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) := by
  rw [archRealLift3_diagonal_eq a ha]; rfl

private theorem diagonal_mul_upperUnipotent3_mul_diagonal_inv {A : Type*} [CommRing A] (d : Fin 3 → Aˣ)
    (x y z : A) :
    Matrix.diagonal (fun i => (d i : A)) * (upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) A) *
        Matrix.diagonal (fun i => (((d i)⁻¹ : Aˣ) : A)) =
      (upperUnipotent3 ((d 0 : A) * (((d 1)⁻¹ : Aˣ) : A) * x) ((d 1 : A) * (((d 2)⁻¹ : Aˣ) : A) * y)
          ((d 0 : A) * (((d 2)⁻¹ : Aˣ) : A) * z) : Matrix (Fin 3) (Fin 3) A) := by
  rw [upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, Units.mul_inv] <;> ring

private theorem archRealLift3_mul_upperUnipotent3_mul_inv (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0)
    (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * upperUnipotent3 x y z *
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0))⁻¹ =
      upperUnipotent3
        ((archScalarIdele (a 0) (ha 0) * (archScalarIdele (a 1) (ha 1))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) • x)
        ((archScalarIdele (a 1) (ha 1) * (archScalarIdele (a 2) (ha 2))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) • y)
        ((archScalarIdele (a 0) (ha 0) * (archScalarIdele (a 2) (ha 2))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) •
          z) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_archRealLift3_diagonal a ha, coe_inv_archRealLift3_diagonal a ha,
    diagonal_mul_upperUnipotent3_mul_diagonal_inv]
  rfl

private theorem archRealMat3_apply (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    WhittakerBlock.archRealMat3 e i j =
      (⟨ofReal (e i j), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j⟩ :
        AdeleRing (𝓞 ℚ) ℚ) :=
  rfl

private theorem adele_fst_one : (1 : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := rfl

private theorem adele_snd_one : (1 : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := rfl

private theorem adele_fst_zero : (0 : AdeleRing (𝓞 ℚ) ℚ).1 = 0 := rfl

private theorem adele_snd_zero : (0 : AdeleRing (𝓞 ℚ) ℚ).2 = 0 := rfl

private theorem archRealMat3_mul (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    WhittakerBlock.archRealMat3 (M * N) = WhittakerBlock.archRealMat3 M * WhittakerBlock.archRealMat3 N := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, archRealMat3_apply]
  apply Prod.ext
  · show ofReal (M i 0 * N 0 j + M i 1 * N 1 j + M i 2 * N 2 j) =
      ofReal (M i 0) * ofReal (N 0 j) + ofReal (M i 1) * ofReal (N 1 j) + ofReal (M i 2) * ofReal (N 2 j)
    rw [ofReal_add, ofReal_add, ofReal_mul, ofReal_mul, ofReal_mul]
  · show (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j =
      (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i 0 *
            (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 0 j +
          (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i 1 *
            (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 j +
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i 2 *
          (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 2 j
    simp only [Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp

private theorem archRealMat3_one : WhittakerBlock.archRealMat3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext i j
  rw [archRealMat3_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq, ofReal_one]
    rfl
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, Matrix.one_apply_ne h, ofReal_zero]
    rfl

private def flowMat (i j : Fin 3) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

private theorem flowMat_apply (i j : Fin 3) (s : ℝ) (a b : Fin 3) :
    flowMat i j s a b = (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0 :=
  rfl

private theorem flowMat_eq (i j : Fin 3) (s : ℝ) :
    (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) = flowMat i j s :=
  rfl

private theorem flowMat_mul (i j : Fin 3) (hij : i ≠ j) (s u : ℝ) :
    flowMat i j s * flowMat i j u = flowMat i j (s + u) := by
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_three, flowMat_apply]
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | (fin_cases a <;> fin_cases b <;> simp <;> ring)

private theorem flowMat_zero (i j : Fin 3) : flowMat i j 0 = 1 := by
  ext a b
  rw [flowMat_apply, Matrix.one_apply, ite_self, add_zero]

private theorem archRealMat3_flowMat_mul (i j : Fin 3) (hij : i ≠ j) (s u : ℝ) :
    WhittakerBlock.archRealMat3 (flowMat i j s) * WhittakerBlock.archRealMat3 (flowMat i j u) =
      WhittakerBlock.archRealMat3 (flowMat i j (s + u)) := by
  rw [← archRealMat3_mul, flowMat_mul i j hij]

private theorem archRealMat3_flowMat_zero (i j : Fin 3) : WhittakerBlock.archRealMat3 (flowMat i j 0) = 1 := by
  rw [flowMat_zero, archRealMat3_one]

private theorem isUnit_archRealMat3_flowMat (i j : Fin 3) (hij : i ≠ j) (s : ℝ) :
    IsUnit (WhittakerBlock.archRealMat3 (flowMat i j s)) :=
  isUnit_iff_exists_inv.mpr ⟨WhittakerBlock.archRealMat3 (flowMat i j (-s)), by
    rw [archRealMat3_flowMat_mul i j hij, add_neg_cancel]; exact archRealMat3_flowMat_zero i j⟩

private theorem coe_archRealLift3_flowMat (i j : Fin 3) (hij : i ≠ j) (s : ℝ) :
    ((WhittakerBlock.archRealLift3 (flowMat i j s) : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = WhittakerBlock.archRealMat3 (flowMat i j s) := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3_flowMat i j hij s), IsUnit.unit_spec]

private theorem archRealLift3_flowMat_mul (i j : Fin 3) (hij : i ≠ j) (s u : ℝ) :
    WhittakerBlock.archRealLift3 (flowMat i j s) * WhittakerBlock.archRealLift3 (flowMat i j u) =
      WhittakerBlock.archRealLift3 (flowMat i j (s + u)) :=
  Units.ext (by rw [Units.val_mul, coe_archRealLift3_flowMat i j hij s, coe_archRealLift3_flowMat i j hij u,
    coe_archRealLift3_flowMat i j hij (s + u), archRealMat3_flowMat_mul i j hij])

private theorem archRealLift3_flowMat_zero (i j : Fin 3) (hij : i ≠ j) :
    WhittakerBlock.archRealLift3 (flowMat i j 0) = 1 :=
  Units.ext (by rw [coe_archRealLift3_flowMat i j hij 0, Units.val_one]; exact archRealMat3_flowMat_zero i j)

private theorem archRealLift3_flow_mul (i j : Fin 3) (hij : i ≠ j) (s u : ℝ) :
    WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) *
        WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0) =
      WhittakerBlock.archRealLift3
        (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s + u else 0) :=
  archRealLift3_flowMat_mul i j hij s u

private theorem archRealLift3_flow_zero (i j : Fin 3) (hij : i ≠ j) :
    WhittakerBlock.archRealLift3
        (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then (0 : ℝ) else 0) = 1 :=
  archRealLift3_flowMat_zero i j hij

private theorem coe_archRealLift3_flow (i j : Fin 3) (hij : i ≠ j) (s : ℝ) :
    ((WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) :=
  coe_archRealLift3_flowMat i j hij s

private theorem archRealMat3_flowMat01 (s : ℝ) :
    WhittakerBlock.archRealMat3 (flowMat 0 1 s) =
      ((upperUnipotent3 (archAdele s) 0 0 : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rw [archRealMat3_apply, flowMat_apply, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> apply Prod.ext <;>
    simp [archAdele, ofReal_one, ofReal_zero, adele_fst_one, adele_snd_one, adele_fst_zero, adele_snd_zero]

private theorem archRealLift3_flow01 (s : ℝ) :
    WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = 0 ∧ b = 1 then s else 0) =
      upperUnipotent3 (archAdele s) 0 0 :=
  Units.ext ((coe_archRealLift3_flowMat 0 1 (by decide) s).trans (archRealMat3_flowMat01 s))

private theorem archRealMat3_flowMat12 (s : ℝ) :
    WhittakerBlock.archRealMat3 (flowMat 1 2 s) =
      ((upperUnipotent3 0 (archAdele s) 0 : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rw [archRealMat3_apply, flowMat_apply, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> apply Prod.ext <;>
    simp [archAdele, ofReal_one, ofReal_zero, adele_fst_one, adele_snd_one, adele_fst_zero, adele_snd_zero]

private theorem archRealLift3_flow12 (s : ℝ) :
    WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = 1 ∧ b = 2 then s else 0) =
      upperUnipotent3 0 (archAdele s) 0 :=
  Units.ext ((coe_archRealLift3_flowMat 1 2 (by decide) s).trans (archRealMat3_flowMat12 s))

private theorem diag_mul_flow01 (y₁ y₂ : ℝ) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (s : ℝ) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
        upperUnipotent3 (archAdele s) 0 0 =
      upperUnipotent3 (archAdele (y₁ * s)) 0 0 *
        WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) := by
  have ha : ∀ i, (![y₁ * y₂, y₂, 1] : Fin 3 → ℝ) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hy₁.ne', hy₂.ne']
  have h := archRealLift3_mul_upperUnipotent3_mul_inv ![y₁ * y₂, y₂, 1] ha (archAdele s) 0 0
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [h, archScalarIdele_mul_inv_smul_archAdele, smul_zero, smul_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_inv_cancel_right₀ hy₂.ne']

private theorem diag_mul_flow12 (y₁ y₂ : ℝ) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (s : ℝ) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
        upperUnipotent3 0 (archAdele s) 0 =
      upperUnipotent3 0 (archAdele (y₂ * s)) 0 *
        WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) := by
  have ha : ∀ i, (![y₁ * y₂, y₂, 1] : Fin 3 → ℝ) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hy₁.ne', hy₂.ne']
  have h := archRealLift3_mul_upperUnipotent3_mul_inv ![y₁ * y₂, y₂, 1] ha 0 (archAdele s) 0
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [h, archScalarIdele_mul_inv_smul_archAdele, smul_zero, smul_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    inv_one, mul_one]

private theorem archRealMat3_flowMat02 (s : ℝ) :
    WhittakerBlock.archRealMat3 (flowMat 0 2 s) =
      ((upperUnipotent3 0 0 (archAdele s) : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rw [archRealMat3_apply, flowMat_apply, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> apply Prod.ext <;>
    simp [archAdele, ofReal_one, ofReal_zero, adele_fst_one, adele_snd_one, adele_fst_zero, adele_snd_zero]

private theorem archRealLift3_flow02 (s : ℝ) :
    WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = 0 ∧ b = 2 then s else 0) =
      upperUnipotent3 0 0 (archAdele s) :=
  Units.ext ((coe_archRealLift3_flowMat 0 2 (by decide) s).trans (archRealMat3_flowMat02 s))

private theorem diag_mul_flow02 (y₁ y₂ : ℝ) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (s : ℝ) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
        upperUnipotent3 0 0 (archAdele s) =
      upperUnipotent3 0 0 (archAdele (y₁ * y₂ * s)) *
        WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) := by
  have ha : ∀ i, (![y₁ * y₂, y₂, 1] : Fin 3 → ℝ) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hy₁.ne', hy₂.ne']
  have h := archRealLift3_mul_upperUnipotent3_mul_inv ![y₁ * y₂, y₂, 1] ha 0 0 (archAdele s)
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [h, archScalarIdele_mul_inv_smul_archAdele, smul_zero, smul_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    inv_one, mul_one]

theorem main :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), WhittakerBlock.IsArchSmooth3 φ →
      (∀ w : List (Fin 3 × Fin 3),
        Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) →
      ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 1 2 φ))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) =
        lam ^ 2 * (y₁ : ℂ) * (y₂ : ℂ) *
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) ∧
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 2 φ)
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) = 0 := by
  obtain ⟨lam, hlam, H⟩ :=
    LanglandsTunnell.CubicInduction.exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv
  refine ⟨lam, hlam, fun φ hsa hD hleft y₁ y₂ hy₁ hy₂ => ⟨?_, ?_⟩⟩
  ·
    have hsaψ : WhittakerBlock.IsArchSmooth3 (WhittakerBlock.archDeriv 1 2 φ) :=
      LanglandsTunnell.CubicInduction.WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.1
        φ hsa 1 2
    have hDψ : ∀ w : List (Fin 3 × Fin 3),
        Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ)
          (WhittakerBlock.archDeriv 1 2 φ) w) := by
      intro w
      have := hD (w ++ [((1 : Fin 3), (2 : Fin 3))])
      rwa [List.foldr_append, List.foldr_cons, List.foldr_nil] at this
    have hleftψ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        WhittakerBlock.archDeriv 1 2 φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) =
          WhittakerBlock.archDeriv 1 2 φ g := by
      intro γ g
      simp only [WhittakerBlock.archDeriv, mul_assoc, hleft]
    have h1 := (H φ hsa hD hleft y₁ y₂ hy₁ hy₂).2
    have h2 := (H (WhittakerBlock.archDeriv 1 2 φ) hsaψ hDψ hleftψ y₁ y₂ hy₁ hy₂).1
    rw [← h2, ← h1]
    ring
  ·
    have hcomm :=
      (LanglandsTunnell.CubicInduction.whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3 φ hsa hD).1
        [((0 : Fin 3), (2 : Fin 3))]
    simp only [List.foldr_cons, List.foldr_nil] at hcomm
    rw [hcomm]
    have hU :=
      (LanglandsTunnell.CubicInduction.whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
        φ hleft).1
    show deriv (fun s : ℝ => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
          WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = 0 ∧ b = 2 then s else 0)) 0 = 0
    have hconst : (fun s : ℝ => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
          WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = 0 ∧ b = 2 then s else 0)) =
        fun _ => psiQ (0 + 0) *
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) := by
      funext s
      rw [archRealLift3_flow02, diag_mul_flow02 y₁ y₂ hy₁ hy₂, hU]
    rw [hconst, deriv_const]

end WsC.QW

end

theorem solution :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), WhittakerBlock.IsArchSmooth3 φ →
      (∀ w : List (Fin 3 × Fin 3),
        Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) →
      ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 1 2 φ))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) =
        lam ^ 2 * (y₁ : ℂ) * (y₂ : ℂ) *
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) ∧
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 2 φ)
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) = 0 := by
  exact WsC.QW.main

end S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero (solution)
