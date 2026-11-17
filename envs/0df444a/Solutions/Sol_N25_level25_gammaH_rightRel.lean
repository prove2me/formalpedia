-- Prove2me | solution 1 for N25.level25_gammaH_rightRel
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:53.484466+00:00
-- url     : https://prove2.me/submissions/40da5616-fac1-4bc2-a0ef-92f01c7e6ff8

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

open scoped MatrixGroups

namespace N25

/-- Equality of right cosets is exactly common scaling of the reduced bottom rows. -/
theorem _root_.solution (H : Subgroup (ZMod 25)ˣ) (A B : SL(2, ℤ)) :
    QuotientGroup.rightRel (CohCarrier.GammaH 25 H) A B ↔
      ∃ u : (ZMod 25)ˣ, u ∈ H ∧
        (B 1 0 : ZMod 25) = (u : ZMod 25) * (A 1 0 : ZMod 25) ∧
        (B 1 1 : ZMod 25) = (u : ZMod 25) * (A 1 1 : ZMod 25) := by
  have hmul (C D : SL(2, ℤ)) (i j : Fin 2) :
      ((C * D) i j : ZMod 25) =
        (C i 0 : ZMod 25) * (D 0 j : ZMod 25) +
        (C i 1 : ZMod 25) * (D 1 j : ZMod 25) := by
    change (((C : Matrix (Fin 2) (Fin 2) ℤ) *
      (D : Matrix (Fin 2) (Fin 2) ℤ)) i j : ZMod 25) = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul]
  rw [QuotientGroup.rightRel_apply]
  constructor
  · intro h
    obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp h
    let u := CohCarrier.gamma0Units 25 ⟨B * A⁻¹, h0⟩
    have hu : (u : ZMod 25) = ((B * A⁻¹) 1 1 : ZMod 25) := rfl
    have hz : ((B * A⁻¹) 1 0 : ZMod 25) = 0 :=
      CongruenceSubgroup.Gamma0_mem.mp h0
    refine ⟨u, hH, ?_, ?_⟩
    · have h := hmul (B * A⁻¹) A 1 0
      rw [hz, ← hu, zero_mul, zero_add] at h
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
    · have h := hmul (B * A⁻¹) A 1 1
      rw [hz, ← hu, zero_mul, zero_add] at h
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  · rintro ⟨u, hu, hc, hd⟩
    have hi0 : (A⁻¹ 0 0 : ZMod 25) = (A 1 1 : ZMod 25) := by
      change (((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 25) = _
      rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
      rfl
    have hi1 : (A⁻¹ 1 0 : ZMod 25) = -(A 1 0 : ZMod 25) := by
      change (((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 25) = _
      rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
      simp
    have hj0 : (A⁻¹ 0 1 : ZMod 25) = -(A 0 1 : ZMod 25) := by
      change (((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod 25) = _
      rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
      simp
    have hj1 : (A⁻¹ 1 1 : ZMod 25) = (A 0 0 : ZMod 25) := by
      change (((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod 25) = _
      rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
      rfl
    have hz : ((B * A⁻¹) 1 0 : ZMod 25) = 0 := by
      rw [hmul, hi0, hi1, hc, hd]
      ring
    have hdet : (A 0 0 : ZMod 25) * (A 1 1 : ZMod 25) -
        (A 0 1 : ZMod 25) * (A 1 0 : ZMod 25) = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe A
      rw [Matrix.det_fin_two] at h
      have hcast := congrArg (fun z : ℤ => (z : ZMod 25)) h
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using hcast
    have hdiag : ((B * A⁻¹) 1 1 : ZMod 25) = (u : ZMod 25) := by
      rw [hmul, hj0, hj1, hc, hd]
      calc
        _ = (u : ZMod 25) * ((A 0 0 : ZMod 25) * (A 1 1 : ZMod 25) -
          (A 0 1 : ZMod 25) * (A 1 0 : ZMod 25)) := by ring
        _ = ↑u := by rw [hdet, mul_one]
    have h0 : B * A⁻¹ ∈ CongruenceSubgroup.Gamma0 25 :=
      CongruenceSubgroup.Gamma0_mem.mpr hz
    apply CohCarrier.mem_GammaH_iff.mpr
    refine ⟨h0, ?_⟩
    have heq : CohCarrier.gamma0Units 25 ⟨B * A⁻¹, h0⟩ = u := Units.ext hdiag
    simpa [heq] using hu

end N25
