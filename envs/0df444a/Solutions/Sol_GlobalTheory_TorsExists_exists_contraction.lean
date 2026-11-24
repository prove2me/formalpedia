-- Prove2me | solution 1 for GlobalTheory.TorsExists.exists_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:00:08.672799+00:00
-- url     : https://prove2.me/submissions/2674a8b0-6825-4333-92ec-532b9aeb2995

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField
import Theorems.Thm_GlobalTheory_TorsExists_exists_isUnit_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsExists
variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]
namespace GlobalTheory.TorsExists
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R] (D : Matrix Ix Ix R) (hD : D * D = 0)
    (hex : ∀ v : Ix → IsLocalRing.ResidueField R, (D.map (IsLocalRing.residue R)).mulVec v = 0 →
      ∃ w, (D.map (IsLocalRing.residue R)).mulVec w = v) :
    ∃ h : Matrix Ix Ix R, D * h + h * D = 1 := by
  obtain ⟨G, hG⟩ := exists_isUnit_field (D.map (IsLocalRing.residue R))
    (by rw [← Matrix.map_mul, hD]; simp) hex
  choose H hH using fun p q => IsLocalRing.residue_surjective (R := R) (G p q)
  have hHG : (Matrix.of H).map (IsLocalRing.residue R) = G := by ext p q; exact hH p q
  set A := D * Matrix.of H + Matrix.of H * D with hA
  have hu : IsUnit A.det := by
    have : IsLocalRing.residue R A.det = (D.map (IsLocalRing.residue R) * G + G * D.map (IsLocalRing.residue R)).det := by
      rw [RingHom.map_det, ← hHG, hA]
      simp [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_add]
    rw [← this] at hG
    exact (isUnit_map_iff _ _).1 hG
  have hc : A * D = D * A := by
    rw [hA, add_mul, mul_add, mul_assoc (Matrix.of H), hD, ← mul_assoc D D, hD]; simp [mul_assoc]
  have hc' : A⁻¹ * D = D * A⁻¹ := by
    calc A⁻¹ * D = A⁻¹ * D * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, mul_one]
      _ = A⁻¹ * (A * D) * A⁻¹ := by rw [hc]; simp only [mul_assoc]
      _ = D * A⁻¹ := by rw [← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul]
  refine ⟨Matrix.of H * A⁻¹, ?_⟩
  rw [mul_assoc, hc', ← mul_assoc, ← mul_assoc, ← add_mul, ← hA, Matrix.mul_nonsing_inv _ hu]
end GlobalTheory.TorsExists
