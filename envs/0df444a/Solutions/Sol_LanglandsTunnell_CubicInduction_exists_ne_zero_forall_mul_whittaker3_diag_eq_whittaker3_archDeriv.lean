-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/984c4dbb-3e98-57c6-8f98-ae0da1014107

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Theorems.Thm_NumberField_StandardAddChar_exists_ne_zero_and_hasDerivAt_psiQ_ofReal
import Mathlib.Analysis.Calculus.ParametricIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL globalPointsGL upperUnipotent3 upperUnipotent3_coe whittaker3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul"
namespace WhittakerTorusDeriv
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

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

private theorem hasDerivAt_psiQ_archAdele_mul {lam : ℂ}
    (hlam : HasDerivAt
      (fun s : ℝ => NumberField.StandardAddChar.psiQ
        ((AutomorphicForm.StandardKernel.ofReal s, 0) : AdeleRing (𝓞 ℚ) ℚ)) lam 0)
    (c : ℝ) :
    HasDerivAt (fun s : ℝ => psiQ (archAdele (c * s))) (lam * c) 0 := by
  have hl : HasDerivAt (fun s : ℝ => c * s) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have h0 : HasDerivAt
      (fun s : ℝ => NumberField.StandardAddChar.psiQ
        ((AutomorphicForm.StandardKernel.ofReal s, 0) : AdeleRing (𝓞 ℚ) ℚ)) lam (c * 0) := by
    rw [mul_zero]
    exact hlam
  exact (HasDerivAt.scomp (x := (0 : ℝ)) (hg := h0) (hh := hl)).congr_deriv
    (by simp [Complex.real_smul, mul_comm])

private theorem continuous_upperUnipotent3 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun p : A × A × A => upperUnipotent3 p.1 p.2.1 p.2.2 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun p : A × A × A =>
      (Matrix.of ![![1, p.1, p.2.2], ![0, 1, p.2.1], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun p : A × A × A =>
      (Matrix.of ![![1, -p.1, p.1 * p.2.1 - p.2.2], ![0, 1, -p.2.1], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem isProbabilityMeasure_productionPins_ν :
    @IsProbabilityMeasure _ (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
  isProbabilityMeasure_productionPinsOf_ν ℚ _ _ _ _ (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
    (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

private theorem borelSpace_productionPins_nS :
    @BorelSpace (AdeleRing (𝓞 ℚ) ℚ) _
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS := by
  rw [productionPinsOf_nS]
  exact AdelicHaar.borelSpace_adeleBorel _ _

private theorem ae_mem_adelicBox_productionPins_ν :
    ∀ᵐ a ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν,
      a ∈ AdelicBox.adelicBox ℚ := by
  rw [productionPinsOf_ν]
  unfold ProbabilityTheory.cond
  exact MeasureTheory.Measure.ae_smul_measure (ae_restrict_mem (AdelicBox.measurableSet_adelicBox ℚ)) _

private theorem aestronglyMeasurable_unipotent_integrand [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)]
    [OpensMeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] (ν : Measure (AdeleRing (𝓞 ℚ) ℚ))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ) :
    AEStronglyMeasurable (fun z : AdeleRing (𝓞 ℚ) ℚ => Φ (upperUnipotent3 x y z * h) * ψ (-(x + y))) ν := by
  have h₁ : Continuous fun z : AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 x y z :=
    continuous_upperUnipotent3.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have h₂ : Continuous fun z : AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 x y z * h := h₁.mul continuous_const
  have h₃ : Continuous fun z : AdeleRing (𝓞 ℚ) ℚ => Φ (upperUnipotent3 x y z * h) := hΦ.comp h₂
  exact (h₃.mul continuous_const).aestronglyMeasurable

private theorem archRealLift3_flow_inv (i j : Fin 3) (hij : i ≠ j) (s : ℝ) :
    (WhittakerBlock.archRealLift3
        (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))⁻¹ =
      WhittakerBlock.archRealLift3
        (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then -s else 0) := by
  apply inv_eq_of_mul_eq_one_right
  rw [archRealLift3_flow_mul i j hij s (-s), add_neg_cancel]
  exact archRealLift3_flow_zero i j hij

private theorem continuous_flow_entry (i j a b : Fin 3) :
    Continuous fun s : ℝ => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0 := by
  refine continuous_const.add ?_
  by_cases hab : a = i ∧ b = j
  · simp only [if_pos hab]
    exact continuous_id
  · simp only [if_neg hab]
    exact continuous_const

private theorem continuous_archRealMat3_flow (i j : Fin 3) :
    Continuous fun s : ℝ =>
      WhittakerBlock.archRealMat3
        (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) := by
  refine continuous_matrix fun a b => ?_
  simp only [archRealMat3_apply]
  have hp : Continuous fun s : ℝ =>
      ((ofReal ((if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0),
          (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) :
        InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (AutomorphicForm.StandardKernel.continuous_ofReal.comp (continuous_flow_entry i j a b)).prodMk continuous_const
  exact hp

private theorem continuous_archRealLift3_flow (i j : Fin 3) (hij : i ≠ j) :
    Continuous fun s : ℝ =>
      (WhittakerBlock.archRealLift3
        (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun s : ℝ =>
      ((WhittakerBlock.archRealLift3
            (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) : AdelicGL 3 (𝓞 ℚ) ℚ) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    simp only [coe_archRealLift3_flow i j hij]
    exact continuous_archRealMat3_flow i j
  · show Continuous fun s : ℝ =>
      (((WhittakerBlock.archRealLift3
            (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    simp only [archRealLift3_flow_inv i j hij, coe_archRealLift3_flow i j hij]
    exact (continuous_archRealMat3_flow i j).comp continuous_neg

private theorem det_flowMat_ne_zero (i j : Fin 3) (hij : i ≠ j) (u : ℝ) : (flowMat i j u).det ≠ 0 := by
  have h : flowMat i j u * flowMat i j (-u) = 1 := by
    rw [flowMat_mul i j hij u (-u), add_neg_cancel]
    exact flowMat_zero i j
  exact Matrix.det_ne_zero_of_right_inverse h

private theorem differentiableAt_flow (i j : Fin 3) (u₀ : ℝ) :
    DifferentiableAt ℝ
      (fun u : ℝ => fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0) u₀ := by
  refine differentiableAt_pi.mpr fun a => differentiableAt_pi.mpr fun b => ?_
  show DifferentiableAt ℝ (fun u : ℝ => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0) u₀
  refine (differentiableAt_const _).add ?_
  by_cases hab : a = i ∧ b = j
  · simp only [if_pos hab]
    exact differentiableAt_id
  · simp only [if_neg hab]
    exact differentiableAt_const _

private theorem differentiableAt_comp_flow (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (i j : Fin 3) (hij : i ≠ j) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (u₀ : ℝ) :
    DifferentiableAt ℝ
      (fun u : ℝ =>
        φ (h * WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0))) u₀ := by
  have hof : Continuous fun e : Fin 3 → Fin 3 → ℝ => Matrix.of e :=
    continuous_matrix fun a b => (continuous_apply b).comp (continuous_apply a)
  have hopen : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    isOpen_ne_fun hof.matrix_det continuous_const
  have hmem : (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u₀ else 0) ∈
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    det_flowMat_ne_zero i j hij u₀
  have hφ : DifferentiableAt ℝ (fun e : Fin 3 → Fin 3 → ℝ => φ (h * WhittakerBlock.archRealLift3 e))
      (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u₀ else 0) :=
    ((hsa h).differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)
  have hcomp := hφ.comp u₀ (differentiableAt_flow i j u₀)
  exact hcomp

private theorem hasDerivAt_comp_flow (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (i j : Fin 3) (hij : i ≠ j) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        φ (h * WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0)))
      (WhittakerBlock.archDeriv i j φ
        (h * WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) s := by
  have hfun :
      (fun v : ℝ =>
        φ (h * WhittakerBlock.archRealLift3
            (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) *
          WhittakerBlock.archRealLift3
            (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then v else 0))) =
      fun v : ℝ =>
        φ (h * WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s + v else 0)) := by
    funext v
    rw [mul_assoc, archRealLift3_flow_mul i j hij s v]
  have hkey :
      WhittakerBlock.archDeriv i j φ
          (h * WhittakerBlock.archRealLift3
            (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)) =
        deriv
          (fun u : ℝ =>
            φ (h * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0))) s := by
    show deriv
        (fun v : ℝ =>
          φ (h * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) *
            WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then v else 0))) 0 = _
    rw [hfun, deriv_comp_const_add
      (fun u : ℝ =>
        φ (h * WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0))) s 0, add_zero]
  rw [hkey]
  exact (differentiableAt_comp_flow φ hsa i j hij h s).hasDerivAt

private theorem hasDerivAt_integral_ball {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (G G' : ℝ → α → ℂ) (M₀ M : ℝ) (hG : ∀ s ∈ Metric.ball (0 : ℝ) 1, AEStronglyMeasurable (G s) μ)
    (hG' : ∀ s ∈ Metric.ball (0 : ℝ) 1, AEStronglyMeasurable (G' s) μ)
    (hGb : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ᵐ a ∂μ, ‖G s a‖ ≤ M₀)
    (hdiff : ∀ᵐ a ∂μ, ∀ s ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (fun u => G u a) (G' s a) s)
    (hG'b : ∀ᵐ a ∂μ, ∀ s ∈ Metric.ball (0 : ℝ) 1, ‖G' s a‖ ≤ M) :
    (∀ s ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (fun u => ∫ a, G u a ∂μ) (∫ a, G' s a ∂μ) s) ∧
      (∀ s ∈ Metric.ball (0 : ℝ) 1, ‖∫ a, G s a ∂μ‖ ≤ M₀) ∧
        ∀ s ∈ Metric.ball (0 : ℝ) 1, ‖∫ a, G' s a ∂μ‖ ≤ M := by
  refine ⟨fun s₀ hs₀ => ?_, fun s₀ hs₀ => ?_, fun s₀ hs₀ => ?_⟩
  · have hball : Metric.ball (0 : ℝ) 1 ∈ nhds s₀ := Metric.isOpen_ball.mem_nhds hs₀
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => M) hball
      (Filter.eventually_of_mem hball hG) (Integrable.of_bound (hG s₀ hs₀) M₀ (hGb s₀ hs₀)) (hG' s₀ hs₀) hG'b
      (integrable_const M) hdiff).2
  · simpa using norm_integral_le_of_norm_le_const (hGb s₀ hs₀)
  · have hb : ∀ᵐ a ∂μ, ‖G' s₀ a‖ ≤ M := hG'b.mono fun a ha => ha s₀ hs₀
    simpa using norm_integral_le_of_norm_le_const hb

private theorem continuous_integral_of_continuous {β : Type*} [TopologicalSpace β] {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α)
    (hC : IsCompact C) (hae : ∀ᵐ a ∂μ, a ∈ C) (H : β → α → ℂ) (hH : Continuous fun q : β × α => H q.1 q.2) :
    Continuous fun b => ∫ a, H b a ∂μ := by
  have hslice : ∀ b : β, Continuous fun a => H b a := fun b => hH.comp (Continuous.prodMk_right b)
  have hint : ∀ b : β, Integrable (fun a => H b a) μ := by
    intro b
    obtain ⟨Mb, hMb⟩ := hC.exists_bound_of_continuousOn (hslice b).continuousOn
    exact Integrable.of_bound (hslice b).aestronglyMeasurable Mb (hae.mono fun a ha => hMb a ha)
  refine continuous_iff_continuousAt.mpr fun b₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hH₀ : Continuous fun q : β × α => H b₀ q.2 :=
    hH.comp ((continuous_const : Continuous fun _ : β × α => b₀).prodMk continuous_snd)
  have hdist : Continuous fun q : β × α => ‖H q.1 q.2 - H b₀ q.2‖ := (hH.sub hH₀).norm
  have htube : ∀ᶠ b in nhds b₀, ∀ a ∈ C, ‖H b a - H b₀ a‖ < ε / 2 := by
    refine hC.eventually_forall_of_forall_eventually fun a _ => ?_
    refine hdist.continuousAt.eventually_lt continuous_const.continuousAt ?_
    show ‖H b₀ a - H b₀ a‖ < ε / 2
    rw [sub_self, norm_zero]
    exact half_pos hε
  refine htube.mono fun b hb => ?_
  rw [dist_eq_norm, ← integral_sub (hint b) (hint b₀)]
  have hbound : ∀ᵐ a ∂μ, ‖H b a - H b₀ a‖ ≤ ε / 2 := hae.mono fun a ha => (hb a ha).le
  calc ‖∫ a, H b a - H b₀ a ∂μ‖ ≤ ε / 2 * μ.real Set.univ := norm_integral_le_of_norm_le_const hbound
    _ = ε / 2 := by simp
    _ < ε := half_lt_self hε

private theorem hasDerivAt_comp_flow_assoc (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (i j : Fin 3) (hij : i ≠ j) (n g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        φ (n * (g * WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0))))
      (WhittakerBlock.archDeriv i j φ
        (n * (g * WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)))) s := by
  simpa only [mul_assoc] using hasDerivAt_comp_flow φ hsa i j hij (n * g) s

private theorem exists_bound_flow_integrand (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) (hij : i ≠ j)
    (C : Set (AdeleRing (𝓞 ℚ) ℚ)) (hC : IsCompact C) :
    ∃ M : ℝ, ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖Φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y))‖ ≤ M := by
  have hn : Continuous fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × ℝ =>
      upperUnipotent3 q.1.1 q.1.2.1 q.1.2.2 :=
    (continuous_upperUnipotent3 (A := AdeleRing (𝓞 ℚ) ℚ)).comp continuous_fst
  have hX : Continuous fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × ℝ =>
      g * WhittakerBlock.archRealLift3
        (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then q.2 else 0) :=
    continuous_const.mul ((continuous_archRealLift3_flow i j hij).comp continuous_snd)
  have hΦq : Continuous fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × ℝ =>
      Φ (upperUnipotent3 q.1.1 q.1.2.1 q.1.2.2 *
        (g * WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then q.2 else 0))) :=
    hΦ.comp (hn.mul hX)
  have hψq : Continuous fun q : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × ℝ =>
      ψ (-(q.1.1 + q.1.2.1)) :=
    hψ.comp ((continuous_fst.fst.add continuous_fst.snd.fst).neg)
  have hK : IsCompact ((C ×ˢ (C ×ˢ C)) ×ˢ Metric.closedBall (0 : ℝ) 1) :=
    (hC.prod (hC.prod hC)).prod (isCompact_closedBall (0 : ℝ) 1)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hΦq.mul hψq).continuousOn
  refine ⟨M, fun x hx y hy z hz s hs => ?_⟩
  exact hM ((x, (y, z)), s)
    (Set.mk_mem_prod (Set.mk_mem_prod hx (Set.mk_mem_prod hy hz)) (Metric.ball_subset_closedBall hs))

private theorem hasDerivAt_inner_integral {m : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)}
    [OpensMeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] (ν : Measure (AdeleRing (𝓞 ℚ) ℚ)) [IsProbabilityMeasure ν]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (i j : Fin 3) (hij : i ≠ j) (hφc : Continuous φ) (hdc : Continuous (WhittakerBlock.archDeriv i j φ))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (M₀ M : ℝ) (C : Set (AdeleRing (𝓞 ℚ) ℚ))
    (hb₀ : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y))‖ ≤ M₀)
    (hb₁ : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y))‖ ≤ M)
    (hae : ∀ᵐ a ∂ν, a ∈ C)
    (x : AdeleRing (𝓞 ℚ) ℚ) (hx : x ∈ C) (y : AdeleRing (𝓞 ℚ) ℚ) (hy : y ∈ C) :
    (∀ s ∈ Metric.ball (0 : ℝ) 1,
        HasDerivAt
          (fun u : ℝ =>
            ∫ z, φ (upperUnipotent3 x y z *
                  (g * WhittakerBlock.archRealLift3
                    (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0))) *
                ψ (-(x + y)) ∂ν)
          (∫ z, WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
                (g * WhittakerBlock.archRealLift3
                  (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
              ψ (-(x + y)) ∂ν) s) ∧
      (∀ s ∈ Metric.ball (0 : ℝ) 1,
        ‖∫ z, φ (upperUnipotent3 x y z *
              (g * WhittakerBlock.archRealLift3
                (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
            ψ (-(x + y)) ∂ν‖ ≤ M₀) ∧
        ∀ s ∈ Metric.ball (0 : ℝ) 1,
          ‖∫ z, WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
                (g * WhittakerBlock.archRealLift3
                  (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
              ψ (-(x + y)) ∂ν‖ ≤ M :=
  hasDerivAt_integral_ball ν
    (fun (s : ℝ) (z : AdeleRing (𝓞 ℚ) ℚ) =>
      φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y)))
    (fun (s : ℝ) (z : AdeleRing (𝓞 ℚ) ℚ) =>
      WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y))) M₀ M
    (fun s _ => aestronglyMeasurable_unipotent_integrand ν ψ φ hφc
      (g * WhittakerBlock.archRealLift3
        (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)) x y)
    (fun s _ => aestronglyMeasurable_unipotent_integrand ν ψ (WhittakerBlock.archDeriv i j φ) hdc
      (g * WhittakerBlock.archRealLift3
        (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)) x y)
    (fun s hs => hae.mono fun z hz => hb₀ x hx y hy z hz s hs)
    (Filter.Eventually.of_forall fun z s _ =>
      (hasDerivAt_comp_flow_assoc φ hsa i j hij (upperUnipotent3 x y z) g s).mul_const (ψ (-(x + y))))
    (hae.mono fun z hz s hs => hb₁ x hx y hy z hz s hs)

private theorem hasDerivAt_middle_integral {m : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)}
    [OpensMeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] (ν : Measure (AdeleRing (𝓞 ℚ) ℚ)) [IsProbabilityMeasure ν]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ) (i j : Fin 3) (hij : i ≠ j) (hφc : Continuous φ)
    (hdc : Continuous (WhittakerBlock.archDeriv i j φ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (M₀ M : ℝ)
    (C : Set (AdeleRing (𝓞 ℚ) ℚ)) (hC : IsCompact C)
    (hb₀ : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y))‖ ≤ M₀)
    (hb₁ : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y))‖ ≤ M)
    (hae : ∀ᵐ a ∂ν, a ∈ C)
    (x : AdeleRing (𝓞 ℚ) ℚ) (hx : x ∈ C) :
    (∀ s ∈ Metric.ball (0 : ℝ) 1,
        HasDerivAt
          (fun u : ℝ =>
            ∫ y, ∫ z, φ (upperUnipotent3 x y z *
                  (g * WhittakerBlock.archRealLift3
                    (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0))) *
                ψ (-(x + y)) ∂ν ∂ν)
          (∫ y, ∫ z, WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
                (g * WhittakerBlock.archRealLift3
                  (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
              ψ (-(x + y)) ∂ν ∂ν) s) ∧
      (∀ s ∈ Metric.ball (0 : ℝ) 1,
        ‖∫ y, ∫ z, φ (upperUnipotent3 x y z *
              (g * WhittakerBlock.archRealLift3
                (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
            ψ (-(x + y)) ∂ν ∂ν‖ ≤ M₀) ∧
        ∀ s ∈ Metric.ball (0 : ℝ) 1,
          ‖∫ y, ∫ z, WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
                (g * WhittakerBlock.archRealLift3
                  (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
              ψ (-(x + y)) ∂ν ∂ν‖ ≤ M := by
  have hmeas : ∀ Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous Φ → ∀ s : ℝ,
      AEStronglyMeasurable
        (fun y : AdeleRing (𝓞 ℚ) ℚ =>
          ∫ z, Φ (upperUnipotent3 x y z *
                  (g * WhittakerBlock.archRealLift3
                    (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
                ψ (-(x + y)) ∂ν) ν := by
    intro Φ hΦ s
    have hx' : Continuous fun _ : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => x := continuous_const
    have hn : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 x q.1 q.2 :=
      (continuous_upperUnipotent3 (A := AdeleRing (𝓞 ℚ) ℚ)).comp
        (hx'.prodMk (continuous_fst.prodMk continuous_snd))
    have hX : Continuous fun _ : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        g * WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) :=
      continuous_const
    have hΦq : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        Φ (upperUnipotent3 x q.1 q.2 *
          (g * WhittakerBlock.archRealLift3
            (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) :=
      hΦ.comp (hn.mul hX)
    have hψq : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => ψ (-(x + q.1)) :=
      hψ.comp ((hx'.add continuous_fst).neg)
    exact (continuous_integral_of_continuous ν C hC hae
      (fun (y : AdeleRing (𝓞 ℚ) ℚ) (z : AdeleRing (𝓞 ℚ) ℚ) =>
        Φ (upperUnipotent3 x y z *
              (g * WhittakerBlock.archRealLift3
                (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
            ψ (-(x + y))) (hΦq.mul hψq)).aestronglyMeasurable
  have L3 := hasDerivAt_inner_integral ν ψ φ hsa i j hij hφc hdc g M₀ M C hb₀ hb₁ hae x hx
  exact hasDerivAt_integral_ball ν
    (fun (s : ℝ) (y : AdeleRing (𝓞 ℚ) ℚ) =>
      ∫ z, φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y)) ∂ν)
    (fun (s : ℝ) (y : AdeleRing (𝓞 ℚ) ℚ) =>
      ∫ z, WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y)) ∂ν) M₀ M
    (fun s _ => hmeas φ hφc s) (fun s _ => hmeas (WhittakerBlock.archDeriv i j φ) hdc s)
    (fun s hs => hae.mono fun y hy => (L3 y hy).2.1 s hs)
    (hae.mono fun y hy => (L3 y hy).1)
    (hae.mono fun y hy => (L3 y hy).2.2)

private theorem hasDerivAt_outer_integral {m : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)}
    [OpensMeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] (ν : Measure (AdeleRing (𝓞 ℚ) ℚ)) [IsProbabilityMeasure ν]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ) (i j : Fin 3) (hij : i ≠ j) (hφc : Continuous φ)
    (hdc : Continuous (WhittakerBlock.archDeriv i j φ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (M₀ M : ℝ)
    (C : Set (AdeleRing (𝓞 ℚ) ℚ)) (hC : IsCompact C)
    (hb₀ : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y))‖ ≤ M₀)
    (hb₁ : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y))‖ ≤ M)
    (hae : ∀ᵐ a ∂ν, a ∈ C) :
    (∀ s ∈ Metric.ball (0 : ℝ) 1,
        HasDerivAt
          (fun u : ℝ =>
            ∫ x, ∫ y, ∫ z, φ (upperUnipotent3 x y z *
                  (g * WhittakerBlock.archRealLift3
                    (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then u else 0))) *
                ψ (-(x + y)) ∂ν ∂ν ∂ν)
          (∫ x, ∫ y, ∫ z, WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
                (g * WhittakerBlock.archRealLift3
                  (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
              ψ (-(x + y)) ∂ν ∂ν ∂ν) s) ∧
      (∀ s ∈ Metric.ball (0 : ℝ) 1,
        ‖∫ x, ∫ y, ∫ z, φ (upperUnipotent3 x y z *
              (g * WhittakerBlock.archRealLift3
                (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
            ψ (-(x + y)) ∂ν ∂ν ∂ν‖ ≤ M₀) ∧
        ∀ s ∈ Metric.ball (0 : ℝ) 1,
          ‖∫ x, ∫ y, ∫ z, WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
                (g * WhittakerBlock.archRealLift3
                  (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
              ψ (-(x + y)) ∂ν ∂ν ∂ν‖ ≤ M := by
  have hmeas : ∀ Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous Φ → ∀ s : ℝ,
      AEStronglyMeasurable
        (fun x : AdeleRing (𝓞 ℚ) ℚ =>
          ∫ y, ∫ z, Φ (upperUnipotent3 x y z *
                  (g * WhittakerBlock.archRealLift3
                    (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
                ψ (-(x + y)) ∂ν ∂ν) ν := by
    intro Φ hΦ s
    have hn : Continuous fun p : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
        upperUnipotent3 p.1.1 p.1.2 p.2 :=
      (continuous_upperUnipotent3 (A := AdeleRing (𝓞 ℚ) ℚ)).comp
        (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
    have hX : Continuous fun _ : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
        g * WhittakerBlock.archRealLift3
          (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) :=
      continuous_const
    have hΦp : Continuous fun p : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
        Φ (upperUnipotent3 p.1.1 p.1.2 p.2 *
          (g * WhittakerBlock.archRealLift3
            (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) :=
      hΦ.comp (hn.mul hX)
    have hψp : Continuous fun p : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ =>
        ψ (-(p.1.1 + p.1.2)) :=
      hψ.comp ((continuous_fst.fst.add continuous_fst.snd).neg)
    have hinner : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        ∫ z, Φ (upperUnipotent3 q.1 q.2 z *
                (g * WhittakerBlock.archRealLift3
                  (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
              ψ (-(q.1 + q.2)) ∂ν :=
      continuous_integral_of_continuous ν C hC hae
        (fun (q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) (z : AdeleRing (𝓞 ℚ) ℚ) =>
          Φ (upperUnipotent3 q.1 q.2 z *
                (g * WhittakerBlock.archRealLift3
                  (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
              ψ (-(q.1 + q.2))) (hΦp.mul hψp)
    exact (continuous_integral_of_continuous ν C hC hae
      (fun (x : AdeleRing (𝓞 ℚ) ℚ) (y : AdeleRing (𝓞 ℚ) ℚ) =>
        ∫ z, Φ (upperUnipotent3 x y z *
              (g * WhittakerBlock.archRealLift3
                (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
            ψ (-(x + y)) ∂ν) hinner).aestronglyMeasurable
  have L2 := hasDerivAt_middle_integral ν ψ hψ φ hsa i j hij hφc hdc g M₀ M C hC hb₀ hb₁ hae
  exact hasDerivAt_integral_ball ν
    (fun (s : ℝ) (x : AdeleRing (𝓞 ℚ) ℚ) =>
      ∫ y, ∫ z, φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y)) ∂ν ∂ν)
    (fun (s : ℝ) (x : AdeleRing (𝓞 ℚ) ℚ) =>
      ∫ y, ∫ z, WhittakerBlock.archDeriv i j φ (upperUnipotent3 x y z *
            (g * WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))) *
          ψ (-(x + y)) ∂ν ∂ν) M₀ M
    (fun s _ => hmeas φ hφc s) (fun s _ => hmeas (WhittakerBlock.archDeriv i j φ) hdc s)
    (fun s hs => hae.mono fun x hx => (L2 x hx).2.1 s hs)
    (hae.mono fun x hx => (L2 x hx).1)
    (hae.mono fun x hx => (L2 x hx).2.2)

private theorem hasDerivAt_whittaker3_mul_flow (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hcw : ∀ w : List (Fin 3 × Fin 3),
      Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) (hij : i ≠ j) :
    HasDerivAt
      (fun s : ℝ =>
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ
          (g * WhittakerBlock.archRealLift3
            (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)))
      (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ
        (WhittakerBlock.archDeriv i j φ) g) 0 := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) :=
    (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
  haveI := borelSpace_productionPins_nS
  haveI := isProbabilityMeasure_productionPins_ν
  obtain ⟨C, hC, hBC⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hae : ∀ᵐ a ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν, a ∈ C :=
    ae_mem_adelicBox_productionPins_ν.mono fun a ha => hBC ha
  have hφc : Continuous φ := hcw []
  have hdc : Continuous (WhittakerBlock.archDeriv i j φ) := hcw [(i, j)]
  obtain ⟨M₀, hb₀⟩ :=
    exists_bound_flow_integrand psiQ NumberField.StandardAddChar.continuous_psiQ φ hφc g i j hij C hC
  obtain ⟨M, hb₁⟩ :=
    exists_bound_flow_integrand psiQ NumberField.StandardAddChar.continuous_psiQ (WhittakerBlock.archDeriv i j φ) hdc
      g i j hij C hC
  have hL := (hasDerivAt_outer_integral (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν psiQ
    NumberField.StandardAddChar.continuous_psiQ φ hsa i j hij hφc hdc g M₀ M C hC hb₀ hb₁ hae).1 0
    (Metric.mem_ball_self zero_lt_one)
  simp only [archRealLift3_flow_zero i j hij, mul_one] at hL
  unfold whittaker3
  exact hL

end LanglandsTunnell.CubicInduction.WhittakerTorusDeriv

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.WhittakerTorusDeriv NumberField.StandardAddChar in
theorem solution :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), WhittakerBlock.IsArchSmooth3 φ →
      (∀ w : List (Fin 3 × Fin 3),
        Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) →
      ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      lam * (y₁ : ℂ) * whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) =
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 1 φ)
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) ∧
      lam * (y₂ : ℂ) * whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) =
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 1 2 φ)
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) := by
  obtain ⟨lam, hlam0, hlam⟩ := NumberField.StandardAddChar.exists_ne_zero_and_hasDerivAt_psiQ_ofReal
  refine ⟨lam, hlam0, ?_⟩
  intro φ hsa hcw haut y₁ y₂ hy₁ hy₂
  have hψ :=
    (LanglandsTunnell.CubicInduction.whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
      φ haut).1
  refine ⟨?_, ?_⟩
  · have h1 := hasDerivAt_whittaker3_mul_flow φ hsa hcw
      (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) 0 1 (by decide)
    have h2 : (fun s : ℝ =>
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
            WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = 0 ∧ b = 1 then s else 0))) =
        fun s : ℝ => psiQ (archAdele (y₁ * s)) *
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) := by
      funext s
      rw [archRealLift3_flow01, diag_mul_flow01 y₁ y₂ hy₁ hy₂, hψ, add_zero]
    rw [h2] at h1
    exact (h1.unique ((hasDerivAt_psiQ_archAdele_mul hlam y₁).mul_const _)).symm
  · have h1 := hasDerivAt_whittaker3_mul_flow φ hsa hcw
      (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) 1 2 (by decide)
    have h2 : (fun s : ℝ =>
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
            WhittakerBlock.archRealLift3
              (fun a b => (if a = b then (1 : ℝ) else 0) + if a = 1 ∧ b = 2 then s else 0))) =
        fun s : ℝ => psiQ (archAdele (y₂ * s)) *
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ φ
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) := by
      funext s
      rw [archRealLift3_flow12, diag_mul_flow12 y₁ y₂ hy₁ hy₂, hψ, zero_add]
    rw [h2] at h1
    exact (h1.unique ((hasDerivAt_psiQ_archAdele_mul hlam y₂).mul_const _)).symm

end

end S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv (solution)
