-- Prove2me | solution 1 for GlobalTheory.LeadingMinorInv.exists_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:08.832924+00:00
-- url     : https://prove2.me/submissions/45dabf71-fa4e-4e5e-bebc-21fb57486e23

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
import Theorems.Thm_GlobalTheory_LeadingMinorInv_mul_flagMat
import Theorems.Thm_GlobalTheory_LeadingMinorInv_exists_N

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.LeadingMinorInv
open Formalism.QuantumDeterminants
namespace GlobalTheory.LeadingMinorInv
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) :
    sᴴ * Hpk k r * s = Hpk k r ∧ ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, UpUni U ∧ s * flagMat k r z = flagMat k r z * U := by
  simp only [Sset, Set.mem_setOf_eq] at hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨U, hU, hmF⟩ := exists_N k r z hz m hm
  simp only [UWset, Set.mem_setOf_eq] at hh
  obtain ⟨hhU, hfix, hhz⟩ := hh
  have hmU : mᴴ * Hpk k r * m = Hpk k r := by
    simp only [Nset, Set.mem_setOf_eq] at hm
    exact hm.1
  have hhU' : hᴴ * Hpk k r * h = Hpk k r := hhU
  refine ⟨?_, U, hU, ?_⟩
  · calc (h * m)ᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hhU', hmU]
  · have hF : h * flagMat k r z = flagMat k r z := by
      ext i b
      rw [mul_flagMat]
      simp only [flagMat, Matrix.of_apply]
      by_cases hb : b.val < r
      · simp only [fvec, dif_pos hb]
        rw [(hfix ⟨b.val, hb⟩).1]
      · simp only [fvec, dif_neg hb]
        rw [hhz]
    rw [Matrix.mul_assoc, hmF, ← Matrix.mul_assoc, hF]
end GlobalTheory.LeadingMinorInv
