-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/640eeaa5-ac22-5300-a668-17b6828dff58

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level
import Theorems.Thm_LanglandsTunnell_CubicInduction_sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level
import Theorems.Thm_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.principalSeries3 CubicInduction.rightTranslate_mem_principalSeries3 CubicInduction.gl3AmbientRightTranslate CubicInduction.upperUnipotent3 CubicInduction.radicalP21 CubicInduction.iotaGL CubicInduction.LocalGL3 TateLocal.higherUnitsAt CubicInduction.diagUnitGL2 CubicInduction.lowerUnipotent21 CubicInduction.exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 CubicInduction.apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level CubicInduction.sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level CubicInduction.sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3AmbientRightTranslate upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 lowerUnipotent21_coe longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe weylPrime3_inv exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level"
namespace JacquetVanishing
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp LanglandsTunnell"

p2m_open "Matrix LanglandsTunnell.CubicInduction~exists_valued_eq_exp P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction"

section GL2

variable {A : Type*} [CommRing A]

def weyl : GL (Fin 2) A where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_weyl : ((weyl : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0] := rfl

@[scoped simp] theorem coe_weyl_inv : (((weyl : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0] := rfl

def repMid (e : A) : GL (Fin 2) A where
  val := !![0, 1; 1, e]
  inv := !![-e, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_repMid (e : A) : ((repMid e : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, e] := rfl

@[scoped simp] theorem coe_repMid_inv (e : A) :
    (((repMid e)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![-e, 1; 1, 0] := rfl

theorem iotaGL_weyl_mul_radicalP21 (z y : A) :
    iotaGL (weyl : GL (Fin 2) A) * radicalP21 ![z, y] = radicalP21 ![y, z] * iotaGL (weyl : GL (Fin 2) A) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, radicalP21_coe, radicalP21_coe, coe_iotaGL, coe_weyl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

end GL2

section Local

variable {v : HeightOneSpectrum (𝓞 ℚ)}

def IsInt (k : GL (Fin 2) (v.adicCompletion ℚ)) : Prop :=
  (∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) ∧
    ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1

theorem valued_mul_apply_le_one {a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (ha : ∀ i j, Valued.v (a i j) ≤ 1) (hb : ∀ i j, Valued.v (b i j) ≤ 1) (i j : Fin 2) :
    Valued.v ((a * b) i j) ≤ 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (ha _ _) (hb _ _)

theorem isInt_mul {k₁ k₂ : GL (Fin 2) (v.adicCompletion ℚ)} (h₁ : IsInt k₁) (h₂ : IsInt k₂) : IsInt (k₁ * k₂) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]
    exact valued_mul_apply_le_one h₁.1 h₂.1 i j
  · rw [_root_.mul_inv_rev, Units.val_mul]
    exact valued_mul_apply_le_one h₂.2 h₁.2 i j

theorem isInt_weyl : IsInt (weyl : GL (Fin 2) (v.adicCompletion ℚ)) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_weyl]
    fin_cases i <;> fin_cases j <;> simp
  · rw [coe_weyl_inv]
    fin_cases i <;> fin_cases j <;> simp

theorem isInt_repMid {e : v.adicCompletion ℚ} (he : Valued.v e ≤ 1) : IsInt (repMid e) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_repMid]
    fin_cases i <;> fin_cases j <;> simp [he]
  · rw [coe_repMid_inv]
    fin_cases i <;> fin_cases j <;> simp [he]

theorem isInt_unipotent {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) : IsInt (AutomorphicForm.unipotentGL2 x) := by
  have hinv : (((AutomorphicForm.unipotentGL2 x)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, -x; 0, 1] := rfl
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [AutomorphicForm.unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [hinv]
    fin_cases i <;> fin_cases j <;> simp [hx]

set_option maxHeartbeats 4000000 in

theorem middle_param_of_corner (x : LocalGL3 v)
    (h20 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0)
    (hle : Valued.v ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1) ≤
      Valued.v ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0))
    (hminor : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 * (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 -
      (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 * (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0) :
    ∃ (u : LocalGL3 v) (y₀ : v.adicCompletion ℚ) (k' : GL (Fin 2) (v.adicCompletion ℚ)),
      (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧ (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
      (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧ IsInt k' ∧
      x = u * (weylPrime3 * radicalP21 ![0, y₀] * iotaGL k') := by
  set X := (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) with hX
  set e := X 2 1 / X 2 0 with he
  set y₀ := X 2 2 / X 2 0 with hy₀
  set T : LocalGL3 v := weylPrime3 * radicalP21 ![0, y₀] * iotaGL (repMid e) with hT
  have hTinv : (((T⁻¹ : LocalGL3 v)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![-e, -y₀, 1; 1, 0, 0; 0, 1, 0] := by
    rw [hT, _root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv, coe_iotaGL,
      coe_repMid_inv, weylPrime3_inv, weylPrime3_coe]
    rw [show (((radicalP21 ![(0 : v.adicCompletion ℚ), y₀])⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3)
      (v.adicCompletion ℚ)) = !![1, 0, 0; 0, 1, -y₀; 0, 0, 1] from by
        change (upperUnipotent3 (0 : v.adicCompletion ℚ) y₀ 0).inv = _
        simp [upperUnipotent3]]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]
  have hentry : ∀ i : Fin 3, ((x * T⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 0 =
      X i 0 * (-e) + X i 1 ∧
      ((x * T⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 1 = X i 0 * (-y₀) + X i 2 := by
    intro i
    rw [Units.val_mul, hTinv, ← hX]
    constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  refine ⟨x * T⁻¹, y₀, repMid e, ?_, ?_, ?_, isInt_repMid ?_, by rw [inv_mul_cancel_right]⟩
  · rw [(hentry 1).1, he]
    field_simp
    linear_combination -hminor
  · rw [(hentry 2).1, he]
    field_simp
    ring
  · rw [(hentry 2).2, hy₀]
    field_simp
    ring
  · rw [he, map_div₀]
    exact div_le_one_of_le₀ hle zero_le'

set_option maxHeartbeats 4000000 in

theorem open_param_of_corner (x : LocalGL3 v)
    (h20 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0)
    (hle : Valued.v ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1) ≤
      Valued.v ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0))
    (hminor : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 * (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 -
      (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 * (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0) :
    ∃ (u : LocalGL3 v) (Y₀ : Fin 2 → v.adicCompletion ℚ) (k' : GL (Fin 2) (v.adicCompletion ℚ)),
      (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧ (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
      (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧ IsInt k' ∧
      x = u * (longWeyl3 * iotaGL k' * radicalP21 Y₀) := by
  set X := (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) with hX
  set e := X 2 1 / X 2 0 with he
  set y₀ := (X 1 0 * X 2 2 - X 1 2 * X 2 0) / (X 1 0 * X 2 1 - X 1 1 * X 2 0) with hy₀
  set z₀ := X 2 2 / X 2 0 - e * y₀ with hz₀
  set T : LocalGL3 v := longWeyl3 * iotaGL (AutomorphicForm.unipotentGL2 e) * radicalP21 ![z₀, y₀] with hT
  have hTinv : (((T⁻¹ : LocalGL3 v)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![-z₀, -e, 1; -y₀, 1, 0; 1, 0, 0] := by
    have hw : ((longWeyl3 : LocalGL3 v)⁻¹ : LocalGL3 v) = longWeyl3 := by
      refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
      rw [Units.val_mul, longWeyl3_coe, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    rw [hT, _root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv, coe_iotaGL, hw,
      longWeyl3_coe]
    rw [show (((AutomorphicForm.unipotentGL2 e)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2)
      (v.adicCompletion ℚ)) = !![1, -e; 0, 1] from rfl,
      show (((radicalP21 ![z₀, y₀])⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3)
      (v.adicCompletion ℚ)) = !![1, 0, -z₀; 0, 1, -y₀; 0, 0, 1] from by
        change (upperUnipotent3 (0 : v.adicCompletion ℚ) y₀ z₀).inv = _
        simp [upperUnipotent3]]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have hentry : ∀ i : Fin 3, ((x * T⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 0 =
      X i 0 * (-z₀) + X i 1 * (-y₀) + X i 2 ∧
      ((x * T⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 1 = X i 0 * (-e) + X i 1 := by
    intro i
    rw [Units.val_mul, hTinv, ← hX]
    constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  refine ⟨x * T⁻¹, ![z₀, y₀], AutomorphicForm.unipotentGL2 e, ?_, ?_, ?_, isInt_unipotent ?_,
    by rw [inv_mul_cancel_right]⟩
  · rw [(hentry 1).1, hz₀]
    have h1 : X 1 0 * e - X 1 1 = (X 1 0 * X 2 1 - X 1 1 * X 2 0) / X 2 0 := by
      rw [he]; field_simp
    have h2 : (X 1 0 * e - X 1 1) * y₀ = X 1 0 * X 2 2 / X 2 0 - X 1 2 := by
      rw [h1, hy₀]; field_simp
    linear_combination h2
  · rw [(hentry 2).1, hz₀, hy₀, he]
    field_simp
    ring
  · rw [(hentry 2).2, he]
    field_simp
    ring
  · rw [he, map_div₀]
    exact div_le_one_of_le₀ hle zero_le'

end Local

section MoreIdentities

variable {A : Type*} [CommRing A]

theorem iotaGL_mul_radicalP21 (h : GL (Fin 2) A) (Y : Fin 2 → A) :
    iotaGL h * radicalP21 Y = radicalP21 ((h : Matrix (Fin 2) (Fin 2) A) *ᵥ Y) * iotaGL h := by
  refine Units.ext ?_
  ext i j
  simp only [Units.val_mul, coe_iotaGL, radicalP21_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

theorem radicalP21_mul_iotaGL (h : GL (Fin 2) A) (Y : Fin 2 → A) :
    radicalP21 Y * iotaGL h = iotaGL h * radicalP21 (((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) *ᵥ Y) := by
  rw [iotaGL_mul_radicalP21, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem vec2_add (a b c d : A) : (![a, b] : Fin 2 → A) + ![c, d] = ![a + c, b + d] := by
  ext i
  fin_cases i <;> simp

theorem vec2_eta (Y : Fin 2 → A) : (![Y 0, Y 1] : Fin 2 → A) = Y := by
  ext i
  fin_cases i <;> rfl

theorem mulVec_vec2 (M : Matrix (Fin 2) (Fin 2) A) (s s' : A) :
    M *ᵥ ![s, s'] = ![M 0 0 * s + M 0 1 * s', M 1 0 * s + M 1 1 * s'] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem radicalP21_split (z y : A) : radicalP21 ![z, y] = radicalP21 ![z, 0] * radicalP21 ![0, y] := by
  rw [← radicalP21_add, vec2_add, add_zero, zero_add]

theorem weylPrime3_mul_radicalP21_zero (z : A) :
    (weylPrime3 : GL (Fin 3) A) * radicalP21 ![z, 0] = upperUnipotent3 z 0 0 * weylPrime3 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, weylPrime3_coe, radicalP21_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem upperUnipotent3_mul_radicalP21 (t z y : A) :
    upperUnipotent3 t 0 0 * radicalP21 ![z, y] = radicalP21 ![t * y + z, y] * upperUnipotent3 t 0 0 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, radicalP21_coe, radicalP21_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem lowerUnipotent21_mul_radicalP21 (t z y : A) :
    lowerUnipotent21 t * radicalP21 ![z, y] = radicalP21 ![z, t * z + y] * lowerUnipotent21 t := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, radicalP21_coe, radicalP21_coe, lowerUnipotent21_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem mul_radicalP21_apply_two (x : GL (Fin 3) A) (Y : Fin 2 → A) :
    ((x * radicalP21 Y : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) 2 0 = (x : Matrix (Fin 3) (Fin 3) A) 2 0 ∧
      ((x * radicalP21 Y : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) 2 1 = (x : Matrix (Fin 3) (Fin 3) A) 2 1 := by
  rw [Units.val_mul, radicalP21_coe]
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end MoreIdentities

section LocalIdentities

variable {v : HeightOneSpectrum (𝓞 ℚ)} {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}

theorem iotaGL_diagUnitGL2_mul_radicalP21 (u : (v.adicCompletion ℚ)ˣ) (z y : v.adicCompletion ℚ) :
    (iotaGL (diagUnitGL2 u) : LocalGL3 v) * radicalP21 ![z, y] =
      radicalP21 ![(u : v.adicCompletion ℚ) * z, y] * iotaGL (diagUnitGL2 u) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, radicalP21_coe, radicalP21_coe, coe_iotaGL, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

theorem valued_row_one_eq_one {k : GL (Fin 2) (v.adicCompletion ℚ)} (hk : IsInt k) :
    Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 0) = 1 ∨ Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 1) = 1 := by
  by_contra h
  push Not at h
  have h0 : Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 0) < 1 := lt_of_le_of_ne (hk.1 1 0) h.1
  have h1 : Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 1) < 1 := lt_of_le_of_ne (hk.1 1 1) h.2
  have hone : ((k : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 *
        (((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 +
      ((k : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 *
        (((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) => M 1 1)
      (show ((k : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        (((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1 by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hlt : Valued.v (((k : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 *
        (((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 +
      ((k : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 *
        (((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le h0 (hk.2 0 1)
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le h1 (hk.2 1 1)
  rw [hone, map_one] at hlt
  exact lt_irrefl _ hlt

theorem det_coe_ne_zero (g : LocalGL3 v) : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det g).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h

theorem diag_ne_zero_of_upper (g : LocalGL3 v) (h10 : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) :
    (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 ≠ 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 ≠ 0 := by
  have hdet := det_coe_ne_zero g
  rw [Matrix.det_fin_three, h10, h20, h21] at hdet
  have h : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 *
      (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 ≠ 0 := by
    intro h0
    apply hdet
    linear_combination h0
  exact ⟨fun h0 => h (by rw [h0]; ring), fun h1 => h (by rw [h1]; ring), fun h2 => h (by rw [h2]; ring)⟩

theorem exists_eq_diagonal3_mul_upperUnipotent3 (u : LocalGL3 v)
    (h10 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0)
    (h20 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) :
    ∃ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ),
      u = diagonal3 v a * upperUnipotent3 x y z := by
  obtain ⟨h0, h1, h2⟩ := diag_ne_zero_of_upper u h10 h20 h21
  refine ⟨![Units.mk0 _ h0, Units.mk0 _ h1, Units.mk0 _ h2],
    (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 / (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0,
    (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2 / (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1,
    (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2 / (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0,
    ?_⟩
  refine Units.ext ?_
  refine Matrix.ext fun i j => ?_
  rw [Units.val_mul, diagonal3_coe, upperUnipotent3_coe, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j
  · simp
  · simp [mul_div_cancel₀ _ h0]
  · simp [mul_div_cancel₀ _ h0]
  · simp [h10]
  · simp
  · simp [mul_div_cancel₀ _ h1]
  · simp [h20]
  · simp [h21]
  · simp

theorem exists_apply_upper_mul {Θ : LocalGL3 v → ℂ} (hΘ : Θ ∈ principalSeries3 v χ) (u : LocalGL3 v)
    (h10 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0)
    (h20 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) :
    ∃ c : ℂ, ∀ r : LocalGL3 v, Θ (u * r) = c * Θ r := by
  obtain ⟨a, x, y, z, rfl⟩ := exists_eq_diagonal3_mul_upperUnipotent3 u h10 h20 h21
  refine ⟨torusChar3 v χ a * halfModulus3 v a, fun r => ?_⟩
  rw [mul_assoc (diagonal3 v a), apply_diagonal3_mul_of_mem_principalSeries3 hΘ,
    apply_upperUnipotent3_mul_of_mem_principalSeries3 hΘ]

theorem middle_param (x : LocalGL3 v)
    (hne : ¬ ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧ (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0))
    (hminor : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 * (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 -
      (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 * (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0) :
    ∃ (u : LocalGL3 v) (y₀ : v.adicCompletion ℚ) (k' : GL (Fin 2) (v.adicCompletion ℚ)),
      (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧ (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
      (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧ IsInt k' ∧
      x = u * (weylPrime3 * radicalP21 ![0, y₀] * iotaGL k') := by
  rcases le_or_gt (Valued.v ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1))
    (Valued.v ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0)) with hle | hlt
  · have h20 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0 := by
      intro h
      apply hne
      refine ⟨h, ?_⟩
      rw [h, map_zero, le_zero_iff, map_eq_zero] at hle
      exact hle
    exact middle_param_of_corner x h20 hle hminor
  ·
    have h21 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 ≠ 0 := by
      intro h
      rw [h, map_zero] at hlt
      exact not_lt_zero hlt
    set x' : LocalGL3 v := x * iotaGL (weyl : GL (Fin 2) (v.adicCompletion ℚ)) with hx'
    have hcol : ∀ i : Fin 3, (x' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 0 = (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 1 ∧
        (x' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 1 = (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 0 := by
      intro i
      rw [hx', Units.val_mul, coe_iotaGL, coe_weyl]
      constructor <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]
    obtain ⟨u, y₀, k', hu10, hu20, hu21, hk', hfac⟩ := middle_param_of_corner x'
      (by rw [(hcol 2).1]; exact h21) (by rw [(hcol 2).1, (hcol 2).2]; exact hlt.le)
      (by rw [(hcol 1).1, (hcol 2).2, (hcol 1).2, (hcol 2).1]; linear_combination -hminor)
    refine ⟨u, y₀, k' * weyl, hu10, hu20, hu21, isInt_mul hk' isInt_weyl, ?_⟩
    have hx : x = x' * iotaGL (weyl : GL (Fin 2) (v.adicCompletion ℚ)) := by
      rw [hx', mul_assoc, ← map_mul, weyl_mul_weyl_eq_one, map_one, mul_one]
    rw [hx, hfac, map_mul]
    simp only [mul_assoc]
  where
    weyl_mul_weyl_eq_one : (weyl : GL (Fin 2) (v.adicCompletion ℚ)) * weyl = 1 := by
      refine Units.ext ?_
      rw [Units.val_mul, coe_weyl, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem open_param (x : LocalGL3 v)
    (hminor : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 * (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 -
      (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 * (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0) :
    ∃ (u : LocalGL3 v) (Y₀ : Fin 2 → v.adicCompletion ℚ) (k' : GL (Fin 2) (v.adicCompletion ℚ)),
      (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧ (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
      (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧ IsInt k' ∧
      x = u * (longWeyl3 * iotaGL k' * radicalP21 Y₀) := by
  rcases le_or_gt (Valued.v ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1))
    (Valued.v ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0)) with hle | hlt
  · have h20 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0 := by
      intro h
      rw [h, map_zero, le_zero_iff, map_eq_zero] at hle
      apply hminor
      rw [h, hle]; ring
    exact open_param_of_corner x h20 hle hminor
  · have h21 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 ≠ 0 := by
      intro h
      rw [h, map_zero] at hlt
      exact not_lt_zero hlt
    set x' : LocalGL3 v := x * iotaGL (weyl : GL (Fin 2) (v.adicCompletion ℚ)) with hx'
    have hcol : ∀ i : Fin 3, (x' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 0 = (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 1 ∧
        (x' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 1 = (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 0 := by
      intro i
      rw [hx', Units.val_mul, coe_iotaGL, coe_weyl]
      constructor <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]
    obtain ⟨u, Y₀, k', hu10, hu20, hu21, hk', hfac⟩ := open_param_of_corner x'
      (by rw [(hcol 2).1]; exact h21) (by rw [(hcol 2).1, (hcol 2).2]; exact hlt.le)
      (by rw [(hcol 1).1, (hcol 2).2, (hcol 1).2, (hcol 2).1]; intro h; apply hminor; linear_combination -h)
    refine ⟨u, ![Y₀ 1, Y₀ 0], k' * weyl, hu10, hu20, hu21, isInt_mul hk' isInt_weyl, ?_⟩
    have hx : x = x' * iotaGL (weyl : GL (Fin 2) (v.adicCompletion ℚ)) := by
      rw [hx', mul_assoc, ← map_mul, middle_param.weyl_mul_weyl_eq_one, map_one, mul_one]
    rw [hx, hfac, map_mul, mul_assoc, mul_assoc (longWeyl3 * iotaGL k'), ← vec2_eta Y₀, ← iotaGL_weyl_mul_radicalP21,
      vec2_eta]
    simp only [mul_assoc]

end LocalIdentities

section Residue

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem exists_valued_eq_exp (n : ℤ) :
    ∃ t : v.adicCompletion ℚ, t ≠ 0 ∧ Valued.v t = WithZero.exp n := by
  refine ⟨((NumberField.AdelicLevel.uniformizerUnit ℚ v ^ (-n) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
    Units.ne_zero _, ?_⟩
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem isOpen_ball (n : ℤ) : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp (v := v) n
  rw [← hvt]
  exact NumberField.AdelicLevel.isOpen_setOf_valued_le v t ht

theorem isCompact_ball (n : ℤ) : IsCompact {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp (v := v) n
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers ℚ)))
  have himage : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} =
      (fun y => y * t) '' (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← hvt, NumberField.AdelicLevel.setOf_valued_le_eq_preimage v t ht]
    ext x
    simp only [Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
    constructor
    · intro hx
      exact ⟨x * t⁻¹, hx, by rw [inv_mul_cancel_right₀ ht]⟩
    · rintro ⟨y, hy, rfl⟩
      rwa [mul_inv_cancel_right₀ ht]
  rw [himage]
  exact hO.image (continuous_id.mul continuous_const)

def ball (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) : AddSubgroup (v.adicCompletion ℚ) where
  carrier := {x | Valued.v x ≤ WithZero.exp n}
  add_mem' {a b} ha hb := show Valued.v (a + b) ≤ WithZero.exp n from (Valuation.map_add _ a b).trans (max_le ha hb)
  zero_mem' := show Valued.v (0 : v.adicCompletion ℚ) ≤ WithZero.exp n by simp
  neg_mem' {a} ha := show Valued.v (-a) ≤ WithZero.exp n by rwa [Valuation.map_neg]

theorem mem_ball {n : ℤ} {x : v.adicCompletion ℚ} : x ∈ ball v n ↔ Valued.v x ≤ WithZero.exp n := Iff.rfl

theorem exists_residueSystem (c lo : ℤ) (hle : lo ≤ c) :
    ∃ S : Finset (v.adicCompletion ℚ), (∀ s ∈ S, Valued.v s ≤ WithZero.exp c) ∧
      ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp c →
        ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp lo := by
  classical
  set H : AddSubgroup ↥(ball v c) := (ball v lo).addSubgroupOf (ball v c) with hH
  haveI : CompactSpace ↥(ball v c) := isCompact_iff_compactSpace.mp (isCompact_ball c)
  have hHopen : IsOpen (H : Set ↥(ball v c)) := (isOpen_ball lo).preimage continuous_subtype_val
  haveI : Finite (↥(ball v c) ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hHopen
  haveI : Fintype (↥(ball v c) ⧸ H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : ↥(ball v c) ⧸ H => ((q.out : ↥(ball v c)) : v.adicCompletion ℚ), ?_, ?_⟩
  · intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hs
    exact (q.out).2
  · intro y hy
    set y' : ↥(ball v c) := ⟨y, hy⟩ with hy'
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H y'
    refine ⟨(((QuotientAddGroup.mk y' : ↥(ball v c) ⧸ H).out : ↥(ball v c)) : v.adicCompletion ℚ), ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · rw [hh]
      change Valued.v (y - (y + ((h : ↥(ball v c)) : v.adicCompletion ℚ))) ≤ _
      rw [sub_add_cancel_left, Valuation.map_neg]
      exact h.2
    · rintro s ⟨hs, hclose⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hs

      have h1 : Valued.v (y - (((QuotientAddGroup.mk y' : ↥(ball v c) ⧸ H).out : ↥(ball v c)) :
          v.adicCompletion ℚ)) ≤ WithZero.exp lo := by
        rw [hh]
        change Valued.v (y - (y + ((h : ↥(ball v c)) : v.adicCompletion ℚ))) ≤ _
        rw [sub_add_cancel_left, Valuation.map_neg]
        exact h.2
      have hdiff : -(q.out : ↥(ball v c)) + (QuotientAddGroup.mk y' : ↥(ball v c) ⧸ H).out ∈ H := by
        change Valued.v (((-(q.out : ↥(ball v c)) + (QuotientAddGroup.mk y' : ↥(ball v c) ⧸ H).out :
          ↥(ball v c)) : v.adicCompletion ℚ)) ≤ WithZero.exp lo
        have hrew : (((-(q.out : ↥(ball v c)) + (QuotientAddGroup.mk y' : ↥(ball v c) ⧸ H).out :
            ↥(ball v c)) : v.adicCompletion ℚ)) =
            (y - (((QuotientAddGroup.mk y' : ↥(ball v c) ⧸ H).out : ↥(ball v c)) : v.adicCompletion ℚ)) * (-1) +
              (y - ((q.out : ↥(ball v c)) : v.adicCompletion ℚ)) := by
          push_cast
          ring
        rw [hrew]
        refine (Valuation.map_add _ _ _).trans (max_le ?_ hclose)
        rw [map_mul, Valuation.map_neg, map_one, mul_one]
        exact h1
      have hq : (QuotientAddGroup.mk (q.out : ↥(ball v c)) : ↥(ball v c) ⧸ H) =
          QuotientAddGroup.mk ((QuotientAddGroup.mk y' : ↥(ball v c) ⧸ H).out) :=
        QuotientAddGroup.eq.mpr hdiff
      rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at hq
      rw [hq]

def IsPer (lo : ℤ) (f : v.adicCompletion ℚ → ℂ) : Prop :=
  ∀ y h : v.adicCompletion ℚ, Valued.v h ≤ WithZero.exp lo → f (y + h) = f y

theorem sum_comp_eq {S : Finset (v.adicCompletion ℚ)} {c lo : ℤ}
    (hS : ∀ s ∈ S, Valued.v s ≤ WithZero.exp c)
    (hS' : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp c → ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp lo)
    {f : v.adicCompletion ℚ → ℂ} (hf : IsPer lo f) (φ : v.adicCompletion ℚ → v.adicCompletion ℚ)
    (hφc : ∀ y, Valued.v y ≤ WithZero.exp c → Valued.v (φ y) ≤ WithZero.exp c)
    (hφiso : ∀ y y', Valued.v (φ y - φ y') = Valued.v (y - y')) :
    ∑ s ∈ S, f (φ s) = ∑ s ∈ S, f s := by
  classical

  have hex : ∀ s ∈ S, ∃ s', s' ∈ S ∧ Valued.v (φ s - s') ≤ WithZero.exp lo := fun s hs =>
    (hS' (φ s) (hφc s (hS s hs))).exists
  choose! σ hσS hσclose using hex
  have hval : ∀ s ∈ S, f (φ s) = f (σ s) := fun s hs => by
    have h := hf (σ s) (φ s - σ s) (hσclose s hs)
    rwa [add_sub_cancel] at h
  have hinj : Set.InjOn σ S := by
    intro s₁ h₁ s₂ h₂ heq
    have hd : Valued.v (s₁ - s₂) ≤ WithZero.exp lo := by
      rw [← hφiso]
      have hrew : φ s₁ - φ s₂ = (φ s₁ - σ s₁) + (φ s₂ - σ s₂) * (-1) := by rw [heq]; ring
      rw [hrew]
      refine (Valuation.map_add _ _ _).trans (max_le (hσclose s₁ h₁) ?_)
      rw [map_mul, Valuation.map_neg, map_one, mul_one]
      exact hσclose s₂ h₂
    obtain ⟨s, -, huniq⟩ := hS' s₁ (hS s₁ h₁)
    have e1 : s₁ = s := huniq s₁ ⟨h₁, by simp⟩
    have e2 : s₂ = s := huniq s₂ ⟨h₂, hd⟩
    rw [e1, e2]
  have hsurj : Set.SurjOn σ S S := by
    intro s' hs'
    obtain ⟨s, hs, hEq⟩ := Finset.surj_on_of_inj_on_of_card_le (fun s _ => σ s) (fun s hs => hσS s hs)
      (fun a₁ a₂ h₁ h₂ heq => hinj h₁ h₂ heq) le_rfl s' hs'
    exact ⟨s, hs, hEq.symm⟩
  rw [Finset.sum_nbij σ hσS hinj hsurj hval]

theorem sum_add_left_eq {S : Finset (v.adicCompletion ℚ)} {c lo : ℤ}
    (hS : ∀ s ∈ S, Valued.v s ≤ WithZero.exp c)
    (hS' : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp c → ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp lo)
    {f : v.adicCompletion ℚ → ℂ} (hf : IsPer lo f) {a : v.adicCompletion ℚ} (ha : Valued.v a ≤ WithZero.exp c) :
    ∑ s ∈ S, f (a + s) = ∑ s ∈ S, f s :=
  sum_comp_eq hS hS' hf (fun y => a + y) (fun y hy => (Valuation.map_add _ _ _).trans (max_le ha hy))
    (fun y y' => by rw [add_sub_add_left_eq_sub])

theorem sum_mul_left_eq {S : Finset (v.adicCompletion ℚ)} {c lo : ℤ}
    (hS : ∀ s ∈ S, Valued.v s ≤ WithZero.exp c)
    (hS' : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp c → ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp lo)
    {f : v.adicCompletion ℚ → ℂ} (hf : IsPer lo f) {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) :
    ∑ s ∈ S, f (u * s) = ∑ s ∈ S, f s :=
  sum_comp_eq hS hS' hf (fun y => u * y) (fun y hy => by rw [map_mul, hu, one_mul]; exact hy)
    (fun y y' => by rw [← mul_sub, map_mul, hu, one_mul])

theorem apply_eq_apply_of_close {lo : ℤ} {f : v.adicCompletion ℚ → ℂ} (hf : IsPer lo f) {y s : v.adicCompletion ℚ}
    (h : Valued.v (y - s) ≤ WithZero.exp lo) : f y = f s := by
  have h' := hf s (y - s) h
  rwa [add_sub_cancel] at h'

end Residue

section Average

variable {v : HeightOneSpectrum (𝓞 ℚ)} {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}

noncomputable def Rsub (g : LocalGL3 v) : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ) :=
  (gl3AmbientRightTranslate (R := ℂ) g).restrict fun _ hF => rightTranslate_mem_principalSeries3 hF g

@[scoped simp] theorem coe_Rsub_apply (g : LocalGL3 v) (F : ↥(principalSeries3 v χ)) (x : LocalGL3 v) :
    (Rsub g F : LocalGL3 v → ℂ) x = (F : LocalGL3 v → ℂ) (x * g) := rfl

noncomputable def avgV (T : Finset (v.adicCompletion ℚ)) (Θ : ↥(principalSeries3 v χ)) : ↥(principalSeries3 v χ) :=
  ∑ t ∈ T, ∑ t' ∈ T, Rsub (radicalP21 ![t, t']) Θ

theorem coe_avgV_apply (T : Finset (v.adicCompletion ℚ)) (Θ : ↥(principalSeries3 v χ)) (x : LocalGL3 v) :
    (avgV T Θ : LocalGL3 v → ℂ) x = ∑ t ∈ T, ∑ t' ∈ T, (Θ : LocalGL3 v → ℂ) (x * radicalP21 ![t, t']) := by
  simp only [avgV, Submodule.coe_sum, Finset.sum_apply, coe_Rsub_apply]

theorem apply_avgV {T : Finset (v.adicCompletion ℚ)} {c : ℕ} (hT : ∀ t ∈ T, Valued.v t ≤ WithZero.exp (c : ℤ))
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ (F : ↥(principalSeries3 v χ)) (Y : Fin 2 → v.adicCompletion ℚ),
      (∀ i, Valued.v (Y i) ≤ WithZero.exp (c : ℤ)) →
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (radicalP21 Y) F, rightTranslate_mem_principalSeries3 F.2 _⟩ = Λ F)
    (Θ : ↥(principalSeries3 v χ)) :
    Λ (avgV T Θ) = ((T.card : ℂ) ^ 2) * Λ Θ := by
  simp only [avgV, map_sum]
  have h : ∀ t ∈ T, ∀ t' ∈ T, Λ (Rsub (radicalP21 ![t, t']) Θ) = Λ Θ := fun t ht t' ht' =>
    hΛ Θ ![t, t'] (fun i => by fin_cases i <;> simp [hT t ht, hT t' ht'])
  rw [Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun t' ht' => h t ht t' ht']
  simp [Finset.sum_const, sq, mul_assoc]

end Average

end LanglandsTunnell.CubicInduction.JacquetVanishing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction.JacquetVanishing"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.LanglandsTunnell"

set_option maxHeartbeats 8000000 in
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp" in open _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.JacquetVanishing in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ : ∀ i, ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ i u ≠ 1)
    (Φ : LanglandsTunnell.CubicInduction.LocalGL3 v → ℂ)
    (hΦ : Φ ∈ LanglandsTunnell.CubicInduction.principalSeries3 v χ)
    (hdiag : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 →
      Φ (g * LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 u)) = Φ g)
    (hupper : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.upperUnipotent3 s 0 0) = Φ g)
    (hlower : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.lowerUnipotent21 s) = Φ g) :
    ∃ c : ℕ, ∀ Λ : ↥(LanglandsTunnell.CubicInduction.principalSeries3 v χ) →ₗ[ℂ] ℂ,
      (∀ (F : ↥(LanglandsTunnell.CubicInduction.principalSeries3 v χ)) (Y : Fin 2 → v.adicCompletion ℚ),
        (∀ i, Valued.v (Y i) ≤ WithZero.exp (c : ℤ)) →
        Λ ⟨LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate (R := ℂ)
              (LanglandsTunnell.CubicInduction.radicalP21 Y) F,
            LanglandsTunnell.CubicInduction.rightTranslate_mem_principalSeries3 F.2 _⟩ = Λ F) →
      Λ ⟨Φ, hΦ⟩ = 0 := by
  classical

  obtain ⟨m, hm0⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ Φ hΦ
  have hm : ∀ κ : LocalGL3 v, (∀ i j, Valued.v ((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
      ∀ g : LocalGL3 v, Φ (g * κ) = Φ g := fun κ hκ g => congrFun (hm0 κ hκ) g

  have hperz : ∀ (Θ : LocalGL3 v → ℂ) (n : ℕ),
      (∀ κ : LocalGL3 v, (∀ i j, Valued.v ((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(n : ℤ))) → ∀ g, Θ (g * κ) = Θ g) →
      ∀ (g : LocalGL3 v) (y : v.adicCompletion ℚ), IsPer (-(n : ℤ)) fun z => Θ (g * radicalP21 ![z, y]) := by
    intro Θ n hΘ g y z h hh
    dsimp only
    rw [show (![z + h, y] : Fin 2 → v.adicCompletion ℚ) = ![z, y] + ![h, 0] by rw [vec2_add, add_zero],
      radicalP21_add, ← mul_assoc, hΘ _ ?_ _]
    intro i j
    rw [radicalP21_coe]
    fin_cases i <;> fin_cases j <;> simp
    simpa using hh
  have hpery : ∀ (Θ : LocalGL3 v → ℂ) (n : ℕ),
      (∀ κ : LocalGL3 v, (∀ i j, Valued.v ((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(n : ℤ))) → ∀ g, Θ (g * κ) = Θ g) →
      ∀ (g : LocalGL3 v) (z : v.adicCompletion ℚ), IsPer (-(n : ℤ)) fun y => Θ (g * radicalP21 ![z, y]) := by
    intro Θ n hΘ g z y h hh
    dsimp only
    rw [show (![z, y + h] : Fin 2 → v.adicCompletion ℚ) = ![z, y] + ![0, h] by rw [vec2_add, add_zero],
      radicalP21_add, ← mul_assoc, hΘ _ ?_ _]
    intro i j
    rw [radicalP21_coe]
    fin_cases i <;> fin_cases j <;> simp
    simpa using hh

  obtain ⟨S₂, hS₂, hS₂'⟩ := exists_residueSystem (v := v) (m : ℤ) (-(m : ℤ)) (by omega)
  set ΨV : ↥(principalSeries3 v χ) := avgV S₂ ⟨Φ, hΦ⟩ with hΨVdef
  set Ψ : LocalGL3 v → ℂ := (ΨV : LocalGL3 v → ℂ) with hΨdef
  have hΨmem : Ψ ∈ principalSeries3 v χ := ΨV.2
  have hΨapp : ∀ x, Ψ x = ∑ s ∈ S₂, ∑ s' ∈ S₂, Φ (x * radicalP21 ![s, s']) := fun x => coe_avgV_apply S₂ ⟨Φ, hΦ⟩ x
  have hb1 : ∀ {t : v.adicCompletion ℚ}, Valued.v t ≤ WithZero.exp (-(b : ℤ)) → Valued.v t ≤ 1 := fun ht =>
    ht.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)

  have hΨdiag : ∀ (g : LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ), Valued.v (u : v.adicCompletion ℚ) = 1 →
      Ψ (g * iotaGL (diagUnitGL2 u)) = Ψ g := by
    intro g u hu
    have hterm : ∀ s s', Φ (g * iotaGL (diagUnitGL2 u) * radicalP21 ![s, s']) =
        Φ (g * radicalP21 ![(u : v.adicCompletion ℚ) * s, s']) := fun s s' => by
      rw [mul_assoc, iotaGL_diagUnitGL2_mul_radicalP21, ← mul_assoc]; exact hdiag _ u hu
    rw [hΨapp, hΨapp]
    simp only [hterm]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s' _ => sum_mul_left_eq hS₂ hS₂' (hperz Φ m hm g s') hu
  have hΨupper : ∀ (g : LocalGL3 v) (t : v.adicCompletion ℚ), Valued.v t ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * upperUnipotent3 t 0 0) = Ψ g := by
    intro g t ht
    have hterm : ∀ s s', Φ (g * upperUnipotent3 t 0 0 * radicalP21 ![s, s']) = Φ (g * radicalP21 ![t * s' + s, s']) :=
      fun s s' => by rw [mul_assoc, upperUnipotent3_mul_radicalP21, ← mul_assoc]; exact hupper _ t ht
    rw [hΨapp, hΨapp]
    simp only [hterm]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    refine sum_add_left_eq hS₂ hS₂' (hperz Φ m hm g s') ?_
    rw [map_mul]
    exact (mul_le_mul' (hb1 ht) (hS₂ s' hs')).trans_eq (one_mul _)
  have hΨlower : ∀ (g : LocalGL3 v) (t : v.adicCompletion ℚ), Valued.v t ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * lowerUnipotent21 t) = Ψ g := by
    intro g t ht
    have hterm : ∀ s s', Φ (g * lowerUnipotent21 t * radicalP21 ![s, s']) = Φ (g * radicalP21 ![s, t * s + s']) :=
      fun s s' => by rw [mul_assoc, lowerUnipotent21_mul_radicalP21, ← mul_assoc]; exact hlower _ t ht
    rw [hΨapp, hΨapp]
    simp only [hterm]
    refine Finset.sum_congr rfl fun s hs => ?_
    refine sum_add_left_eq hS₂ hS₂' (hpery Φ m hm g s) ?_
    rw [map_mul]
    exact (mul_le_mul' (hb1 ht) (hS₂ s hs)).trans_eq (one_mul _)

  have hΦP : ∀ x : LocalGL3 v, (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
      (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → Φ x = 0 := fun x h20 h21 =>
    LanglandsTunnell.CubicInduction.apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level v χ b
      (hχ 0) (hχ 1) Φ hΦ hdiag hupper hlower x h20 h21
  have hΨP : ∀ x : LocalGL3 v, (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
      (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → Ψ x = 0 := by
    intro x h20 h21
    rw [hΨapp]
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => hΦP _ ?_ ?_
    · rw [(mul_radicalP21_apply_two x _).1]; exact h20
    · rw [(mul_radicalP21_apply_two x _).2]; exact h21

  have hmiddle_pt : ∀ {Θ : LocalGL3 v → ℂ}, Θ ∈ principalSeries3 v χ → ∀ (k' : GL (Fin 2) (v.adicCompletion ℚ))
      (y₀ s s' : v.adicCompletion ℚ), Θ (weylPrime3 * radicalP21 ![0, y₀] * iotaGL k' * radicalP21 ![s, s']) =
      Θ (weylPrime3 * radicalP21 ![0, y₀ + ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 * s +
        (k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 * s')] * iotaGL k') := by
    intro Θ hΘ k' y₀ s s'
    rw [mul_assoc, iotaGL_mul_radicalP21, mulVec_vec2, ← mul_assoc, mul_assoc weylPrime3, ← radicalP21_add, vec2_add,
      zero_add, radicalP21_split, ← mul_assoc, weylPrime3_mul_radicalP21_zero, mul_assoc (upperUnipotent3 _ _ _),
      mul_assoc (upperUnipotent3 _ _ _), apply_upperUnipotent3_mul_of_mem_principalSeries3 hΘ]
  have hΨmid : ∀ k' : GL (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, Valued.v ((k' : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k'⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      ∀ y₀ : v.adicCompletion ℚ, Ψ (weylPrime3 * radicalP21 ![0, y₀] * iotaGL k') = 0 := by
    intro k' hk' hk'inv y₀

    obtain ⟨hsupp2, hsum2⟩ :=
      LanglandsTunnell.CubicInduction.sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level v χ b hχ Φ hΦ
        hdiag hupper hlower m hm k' hk' hk'inv
    have hzero : ∑ s ∈ S₂, Φ (weylPrime3 * radicalP21 ![0, s] * iotaGL k') = 0 := hsum2 m S₂ le_rfl hS₂ hS₂'

    have hperP : IsPer (-(m : ℤ)) fun y => Φ (weylPrime3 * radicalP21 ![0, y] * iotaGL k') := by
      intro y h hh
      dsimp only
      rw [show (![0, y + h] : Fin 2 → v.adicCompletion ℚ) = ![0, y] + ![0, h] by rw [vec2_add, add_zero],
        radicalP21_add, mul_assoc, mul_assoc, radicalP21_mul_iotaGL k' ![0, h], ← mul_assoc, ← mul_assoc, hm _ ?_ _]
      intro i j
      have hent : ∀ l : Fin 2, Valued.v (((k'⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2)
          (v.adicCompletion ℚ)) l 1) * Valued.v h ≤ WithZero.exp (-(m : ℤ)) := fun l =>
        (mul_le_mul' (hk'inv l 1) hh).trans_eq (one_mul _)
      rw [radicalP21_coe]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · simpa using hent 0
      · simpa using hent 1

    have hinner : ∀ (a e : v.adicCompletion ℚ), Valued.v a ≤ WithZero.exp (m : ℤ) → Valued.v e = 1 →
        ∑ s ∈ S₂, Φ (weylPrime3 * radicalP21 ![0, a + e * s] * iotaGL k') = 0 := by
      intro a e ha he
      have hpa : IsPer (-(m : ℤ)) fun y => Φ (weylPrime3 * radicalP21 ![0, a + y] * iotaGL k') := fun y h hh => by
        dsimp only; rw [← add_assoc]; exact hperP (a + y) h hh
      rw [sum_mul_left_eq hS₂ hS₂' hpa he, sum_add_left_eq hS₂ hS₂' hperP ha, hzero]
    have houter : ∀ (a w : v.adicCompletion ℚ), WithZero.exp (m : ℤ) < Valued.v a → Valued.v w ≤ WithZero.exp (m : ℤ) →
        Φ (weylPrime3 * radicalP21 ![0, a + w] * iotaGL k') = 0 := by
      intro a w ha hw
      refine hsupp2 (a + w) ?_
      rw [Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hw ha)]
      exact ha.le
    have hbound : ∀ (e s : v.adicCompletion ℚ), Valued.v e ≤ 1 → s ∈ S₂ → Valued.v (e * s) ≤ WithZero.exp (m : ℤ) :=
      fun e s he hs => by rw [map_mul]; exact (mul_le_mul' he (hS₂ s hs)).trans_eq (one_mul _)
    rw [hΨapp]
    simp only [hmiddle_pt hΦ k' y₀]
    rcases valued_row_one_eq_one ⟨hk', hk'inv⟩ with h10 | h11
    ·
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s' hs' => ?_
      by_cases hy : Valued.v y₀ ≤ WithZero.exp (m : ℤ)
      · have h := hinner (y₀ + (k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 * s')
          ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0)
          ((Valuation.map_add _ _ _).trans (max_le hy (hbound _ _ (hk' 1 1) hs'))) h10
        rw [← h]
        refine Finset.sum_congr rfl fun s _ => ?_
        congr 3
        ext i; fin_cases i <;> simp; ring
      · push Not at hy
        refine Finset.sum_eq_zero fun s hs => ?_
        rw [← add_assoc] at *
        have h := houter y₀ ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 * s +
          (k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 * s') hy
          ((Valuation.map_add _ _ _).trans (max_le (hbound _ _ (hk' 1 0) hs) (hbound _ _ (hk' 1 1) hs')))
        rw [← add_assoc] at h
        exact h
    ·
      refine Finset.sum_eq_zero fun s hs => ?_
      by_cases hy : Valued.v y₀ ≤ WithZero.exp (m : ℤ)
      · have h := hinner (y₀ + (k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 * s)
          ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)
          ((Valuation.map_add _ _ _).trans (max_le hy (hbound _ _ (hk' 1 0) hs))) h11
        rw [← h]
        refine Finset.sum_congr rfl fun s' _ => ?_
        congr 3
        ext i; fin_cases i <;> simp; ring
      · push Not at hy
        refine Finset.sum_eq_zero fun s' hs' => ?_
        have h := houter y₀ ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 * s +
          (k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 * s') hy
          ((Valuation.map_add _ _ _).trans (max_le (hbound _ _ (hk' 1 0) hs) (hbound _ _ (hk' 1 1) hs')))
        exact h

  obtain ⟨m₂, hm₂0⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ Ψ hΨmem
  have hm₂ : ∀ κ : LocalGL3 v, (∀ i j, Valued.v ((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m₂ : ℤ))) →
      ∀ g : LocalGL3 v, Ψ (g * κ) = Ψ g := fun κ hκ g => congrFun (hm₂0 κ hκ) g
  obtain ⟨S₃, hS₃, hS₃'⟩ := exists_residueSystem (v := v) (m₂ : ℤ) (-(m₂ : ℤ)) (by omega)
  have hopen : ∀ k' : GL (Fin 2) (v.adicCompletion ℚ), IsInt k' →
      (∀ Y : Fin 2 → v.adicCompletion ℚ, WithZero.exp (m₂ : ℤ) ≤ max (Valued.v (Y 0)) (Valued.v (Y 1)) →
        Ψ (longWeyl3 * iotaGL k' * radicalP21 Y) = 0) ∧
      ∑ t ∈ S₃, ∑ t' ∈ S₃, Ψ (longWeyl3 * iotaGL k' * radicalP21 ![t, t']) = 0 := by
    intro k' hk'
    obtain ⟨h1, h2⟩ :=
      LanglandsTunnell.CubicInduction.sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level v χ b hχ Ψ hΨmem
        hΨdiag hΨupper hΨlower m₂ hm₂ hΨmid k' hk'.1 hk'.2
    exact ⟨h1, h2 m₂ S₃ le_rfl hS₃ hS₃'⟩

  have hΨ₂ : ∀ x : LocalGL3 v, ∑ t ∈ S₃, ∑ t' ∈ S₃, Ψ (x * radicalP21 ![t, t']) = 0 := by
    intro x
    by_cases hP : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧ (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0
    ·
      refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun t' _ => hΨP _ ?_ ?_
      · rw [(mul_radicalP21_apply_two x _).1]; exact hP.1
      · rw [(mul_radicalP21_apply_two x _).2]; exact hP.2
    by_cases hminor : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 * (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 -
        (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 * (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0
    ·
      obtain ⟨u, y₀, k', hu10, hu20, hu21, hk', rfl⟩ := middle_param x hP hminor
      obtain ⟨cu, hcu⟩ := exists_apply_upper_mul hΨmem u hu10 hu20 hu21
      refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun t' _ => ?_
      rw [mul_assoc, hcu, hmiddle_pt hΨmem k' y₀, hΨmid k' hk'.1 hk'.2, mul_zero]
    ·
      obtain ⟨u, Y₀, k', hu10, hu20, hu21, hk', rfl⟩ := open_param x hminor
      obtain ⟨cu, hcu⟩ := exists_apply_upper_mul hΨmem u hu10 hu20 hu21
      obtain ⟨hsupp3, hsum3⟩ := hopen k' hk'
      have hterm : ∀ t t', Ψ (u * (longWeyl3 * iotaGL k' * radicalP21 Y₀) * radicalP21 ![t, t']) =
          cu * Ψ (longWeyl3 * iotaGL k' * radicalP21 ![Y₀ 0 + t, Y₀ 1 + t']) := fun t t' => by
        rw [mul_assoc, hcu, mul_assoc, ← radicalP21_add, ← vec2_eta Y₀, vec2_add, vec2_eta]
      simp only [hterm, ← Finset.mul_sum]
      refine mul_eq_zero_of_right _ ?_
      by_cases h0 : Valued.v (Y₀ 0) ≤ WithZero.exp (m₂ : ℤ)
      · by_cases h1 : Valued.v (Y₀ 1) ≤ WithZero.exp (m₂ : ℤ)
        ·
          rw [Finset.sum_congr rfl fun t _ => sum_add_left_eq hS₃ hS₃' (hpery Ψ m₂ hm₂ _ _) h1, Finset.sum_comm,
            Finset.sum_congr rfl fun t' _ => sum_add_left_eq hS₃ hS₃' (hperz Ψ m₂ hm₂ _ _) h0, Finset.sum_comm]
          exact hsum3
        · push Not at h1
          refine Finset.sum_eq_zero fun t ht => Finset.sum_eq_zero fun t' ht' => hsupp3 _ ?_
          refine le_trans h1.le (le_trans ?_ (le_max_right _ _))
          rw [show (![Y₀ 0 + t, Y₀ 1 + t'] : Fin 2 → v.adicCompletion ℚ) 1 = Y₀ 1 + t' from rfl,
            Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt (hS₃ t' ht') h1)]
      · push Not at h0
        refine Finset.sum_eq_zero fun t ht => Finset.sum_eq_zero fun t' ht' => hsupp3 _ ?_
        refine le_trans h0.le (le_trans ?_ (le_max_left _ _))
        rw [show (![Y₀ 0 + t, Y₀ 1 + t'] : Fin 2 → v.adicCompletion ℚ) 0 = Y₀ 0 + t from rfl,
          Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt (hS₃ t ht) h0)]

  refine ⟨max m m₂, fun Λ hΛ => ?_⟩
  have hΛm : ∀ (F : ↥(principalSeries3 v χ)) (Y : Fin 2 → v.adicCompletion ℚ),
      (∀ i, Valued.v (Y i) ≤ WithZero.exp (m : ℤ)) →
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (radicalP21 Y) F, rightTranslate_mem_principalSeries3 F.2 _⟩ = Λ F :=
    fun F Y hY => hΛ F Y fun i => (hY i).trans (WithZero.exp_le_exp.mpr (by simp))
  have hΛm₂ : ∀ (F : ↥(principalSeries3 v χ)) (Y : Fin 2 → v.adicCompletion ℚ),
      (∀ i, Valued.v (Y i) ≤ WithZero.exp (m₂ : ℤ)) →
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (radicalP21 Y) F, rightTranslate_mem_principalSeries3 F.2 _⟩ = Λ F :=
    fun F Y hY => hΛ F Y fun i => (hY i).trans (WithZero.exp_le_exp.mpr (by simp))
  have h1 : Λ ΨV = ((S₂.card : ℂ) ^ 2) * Λ ⟨Φ, hΦ⟩ := apply_avgV hS₂ Λ hΛm ⟨Φ, hΦ⟩
  have h2 : Λ (avgV S₃ ΨV) = ((S₃.card : ℂ) ^ 2) * Λ ΨV := apply_avgV hS₃ Λ hΛm₂ ΨV
  have h3 : avgV S₃ ΨV = 0 := by
    refine Subtype.ext (funext fun x => ?_)
    rw [coe_avgV_apply]
    exact hΨ₂ x
  have hne : ∀ {S : Finset (v.adicCompletion ℚ)} {c lo : ℤ},
      (∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp c → ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp lo) →
      (S.card : ℂ) ≠ 0 := by
    intro S c lo hS'
    obtain ⟨s, ⟨hs, -⟩, -⟩ := hS' 0 (by simp)
    exact Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨s, hs⟩).ne'
  rw [h3, map_zero, h1] at h2
  have h4 : ((S₃.card : ℂ) ^ 2 * (S₂.card : ℂ) ^ 2) * Λ ⟨Φ, hΦ⟩ = 0 := by rw [mul_assoc]; exact h2.symm
  exact (mul_eq_zero.mp h4).resolve_left (mul_ne_zero (pow_ne_zero _ (hne hS₃')) (pow_ne_zero _ (hne hS₂')))

end S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3 (solution)
