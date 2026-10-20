-- Prove2me | solution 1 for OAI.SingleFold.DuplicationBound.small_points
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:15:08.467202+00:00
-- url     : https://prove2.me/submissions/04b64409-8c4e-4840-a282-161b6de1aafc

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Duplication.lean:L130-L164
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.DuplicationBound.small_points. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication

-- ---- from OAI.NumberTheory.SingleFold.Duplication ----
namespace OAI

namespace SingleFold.DuplicationBound

lemma denominator_square {x y : ℚ} (he : y^2=x^3-25*x) : IsSquare x.den := by
  let a := x.num
  let b : ℤ := x.den
  have hb : 0 < b := by dsimp [b]; exact_mod_cast x.den_pos
  have hbq : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hcop : IsCoprime (a^3-25*a*b^2) (b^3) := by
    apply IsCoprime.pow_right
    have hh := (x.isCoprime_num_den.pow_left (m:=3)).add_mul_right_left (-25*a*b)
    have hn : a^3-25*a*b^2=x.num^3+(-25*a*b)*(x.den:ℤ) := by dsimp [a,b]; ring
    rw [hn]
    exact hh
  have hf : y^2=((a^3-25*a*b^2:ℤ):ℚ)/(b^3:ℤ) := by
    rw [he]
    conv_lhs => rw [←x.num_div_den]
    dsimp [a,b]
    push_cast
    field_simp
  have hd := Rat.den_div_eq_of_coprime (pow_pos hb 3) (Int.isCoprime_iff_nat_coprime.mp hcop)
  rw [←hf,Rat.den_pow] at hd
  dsimp [b] at hd
  have hd' : (y.den:ℚ)^2=(x.den:ℚ)^3 := by exact_mod_cast hd
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨(y.den:ℚ)/x.den,?_⟩
  field_simp
  nlinarith only [hd']

lemma bounded_points (i : Fin 19) (j : Fin 20) (k : Fin 13) :
    let x : ℚ := (20*(i.val:ℤ)+(j.val:ℤ)-184) / ((k.val+1:ℕ):ℚ)^2
    IsSquare (x^3-25*x) → x=0 ∨ x=5 ∨ x= -5 ∨ x= -4 ∨ x=45 ∨ x=25/4 ∨ x= -5/9 := by
  fin_cases k <;> fin_cases i <;> revert j <;> decide +kernel

lemma small_points {x y : ℚ} (he : y^2=x^3-25*x) (hH : height x < 185) :
    x=0 ∨ x=5 ∨ x= -5 ∨ x= -4 ∨ x=45 ∨ x=25/4 ∨ x= -5/9 := by
  obtain ⟨k,hk⟩ := denominator_square he
  have hnum : x.num.natAbs < 185 := lt_of_le_of_lt (le_max_left _ _) hH
  have hden : x.den < 185 := lt_of_le_of_lt (le_max_right _ _) hH
  have hkpos : 0 < k := by have := x.den_pos; rw [hk] at this; nlinarith
  have hklt : k < 14 := by rw [hk] at hden; nlinarith
  let a := (x.num+184).toNat
  have ha : (a:ℤ)=x.num+184 := Int.toNat_of_nonneg (by
    have hh' : -(184:ℤ) ≤ x.num := by
      have : (x.num.natAbs:ℤ) ≤ 184 := by exact_mod_cast (show x.num.natAbs ≤ 184 by omega)
      rw [Int.natCast_natAbs] at this
      exact (abs_le.mp this).1
    omega)
  have halt : a < 369 := by
    have hh' : x.num ≤ 184 := by
      have : (x.num.natAbs:ℤ) ≤ 184 := by exact_mod_cast (show x.num.natAbs ≤ 184 by omega)
      rw [Int.natCast_natAbs] at this
      exact (abs_le.mp this).2
    omega
  have harr : 20*(a/20)+a%20=a := by omega
  have hv : (20*(a/20:ℕ)+(a%20:ℕ)-184:ℚ) / ((k-1+1:ℕ):ℚ)^2 = x := by
    rw [show k-1+1=k by omega]
    have hh : (20*(a/20:ℕ)+(a%20:ℕ)-184:ℚ) = (x.num:ℚ) := by
      have haQ : (a:ℚ)=(x.num:ℚ)+184 := by exact_mod_cast ha
      have hrQ : 20*(a/20:ℕ)+(a%20:ℕ)=(a:ℚ) := by exact_mod_cast harr
      linarith
    calc
      _=(x.num:ℚ)/x.den := by rw [hh,hk]; push_cast; ring
      _=x := x.num_div_den
  have h := bounded_points ⟨a/20,by omega⟩ ⟨a%20,by omega⟩ ⟨k-1,by omega⟩
  dsimp only at h
  simp only [Int.cast_natCast] at h
  rw [hv] at h
  exact h ⟨y,by nlinarith only [he]⟩

end SingleFold.DuplicationBound

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.DuplicationBound


theorem solution : type_of% @_root_.OAI.SingleFold.DuplicationBound.small_points := @_root_.OAI.SingleFold.DuplicationBound.small_points
