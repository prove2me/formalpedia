-- Prove2me | solution 1 for GlobalTheory.BigCell.bigCell_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:29:59.503174+00:00
-- url     : https://prove2.me/submissions/46a94dfc-e029-4cb1-b473-891962f19b05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BigCellFactorisationDoubledUnitaryGroup
import Theorems.Thm_GlobalTheory_BigCell_e1
import Theorems.Thm_GlobalTheory_BigCell_e2
import Theorems.Thm_GlobalTheory_BigCell_mem_unitary
import Theorems.Thm_GlobalTheory_BigCell_mul_inv_eq
import Theorems.Thm_GlobalTheory_BigCell_q_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
open scoped Matrix
open Matrix
open GlobalTheory GlobalTheory.BigCell
variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
namespace GlobalTheory.BigCell
theorem _root_.solution : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (c : R →ₐ[A] R) [Invertible (2 : R)]
    (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β R) (g : UG c (dbl J)),
    IsUnit (Matrix.fromCols (1 : Matrix β β R) (-1 : Matrix β β R) * ((g : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) *
      Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R)).det →
    ∃ (p q : UG c (dbl J)) (t s : GL β R),
      ((p : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (1 : Matrix β β R) =
        Matrix.fromRows (1 : Matrix β β R) (1 : Matrix β β R) * (t : Matrix β β R) ∧
      ((q : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R) =
        Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R) * (s : Matrix β β R) ∧ g = p * q := by
  intro A R _ _ _ c _ β _ _ J g hdet
  set G : Matrix (β ⊕ β) (β ⊕ β) R := ((g : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) with hGdef
  set f : R →+* R := (c : R →+* R) with hf
  have hG : Gᵀ * dbl J * G.map f = dbl J := g.2
  have h1 : (1 : Matrix β β R).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix β β R).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R)ᵀ = fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R)ᵀ = fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R).map f = fromRows 1 1 := by rw [fromRows_map, h1]
  have hNf : (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R).map f = fromRows 1 (-1) := by
    rw [fromRows_map, h1, hm1]
  have hΔtf : (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R).map f = fromCols 1 1 := by rw [fromCols_map, h1]
  have hNtf : (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R).map f = fromCols 1 (-1) := by
    rw [fromCols_map, h1, hm1]
  set D : Matrix β β R := (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) * G *
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) with hDdef
  have hD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hD' : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ hdet
  set M : Matrix (β ⊕ β) (β ⊕ β) R := (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) *
    ((fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * G * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) *
      D⁻¹) * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R)
    (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) e1
    ((fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) * G * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * D⁻¹)
  have hmem := mem_unitary f J (dbl J) G _ _ _ _ D⁻¹ hG hΔT hNT hΔf hΔtf hNf hNtf (e3 J) (e4 J) (e5 J) (e6 J) (e7 J) hD
  let P : GL (β ⊕ β) R := ⟨1 + ⅟(2 : R) • M, 1 - ⅟(2 : R) • M, hinv.1, hinv.2⟩
  let p : UG c (dbl J) := ⟨P, hmem⟩
  have hdetS : IsUnit (⅟(2 : R) • D).det := by
    rw [det_smul]
    exact ((isUnit_of_invertible (⅟(2 : R))).pow _).mul hdet
  let s : GL β R := ((Matrix.isUnit_iff_isUnit_det _).mpr hdetS).unit
  refine ⟨p, p⁻¹ * g, 1, s, ?_, ?_, (mul_inv_cancel_left p g).symm⟩
  · show (1 + ⅟(2 : R) • M) * (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) = _
    rw [Units.val_one, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _
      (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R), e1, Matrix.mul_zero, smul_zero, add_zero]
  · show (1 - ⅟(2 : R) • M) * G * (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) = _
    rw [IsUnit.unit_spec]
    exact q_col G _ _ _ _ D⁻¹ (e2) hD'
end GlobalTheory.BigCell
