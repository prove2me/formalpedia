-- Prove2me | solution 1 for GlobalTheory.UnRep.finite_not_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:59:02.018569+00:00
-- url     : https://prove2.me/submissions/bab6ff9f-9d72-4752-97b9-c9849f1a8ac3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
import Theorems.Thm_GlobalTheory_UnRep_finite_det_one_add_smul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution {E R : Type} [Field E] [CommRing R] (φ : E →+* R) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) R) (ε : R) (hε : ε * ε = ε)
    (hfin : {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}.Finite) :
    {l : E | ¬ IsUnit (1 + φ l • (ε • g + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R))).det}.Finite := by
  set G := ε • g + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) with hG
  have key : ∀ (M : Ideal R) (l : E), Ideal.Quotient.mk M (1 + φ l • G).det =
      (1 + ((Ideal.Quotient.mk M).comp φ) l • G.map (Ideal.Quotient.mk M)).det := by
    intro M l
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h1 : ∀ M ∈ {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}, {l : E | (1 + φ l • G).det ∈ M}.Finite := by
    rintro M ⟨hM, -⟩
    letI := Ideal.Quotient.field M
    refine (finite_det_one_add_smul_eq_zero ((Ideal.Quotient.mk M).comp φ)
      (G.map (Ideal.Quotient.mk M))).subset fun l hl => ?_
    rw [Set.mem_setOf_eq, ← key, Ideal.Quotient.eq_zero_iff_mem]
    exact hl
  refine ((hfin.biUnion h1).union (Set.finite_singleton (-1))).subset fun l hl => ?_
  obtain ⟨M, hM, hl⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hl)
  have h0 : ε * (1 - ε) ∈ M := by
    rw [mul_sub, mul_one, hε, sub_self]; exact M.zero_mem
  rcases hM.isPrime.mem_or_mem h0 with h | h
  · right
    letI := Ideal.Quotient.field M
    have h2 := Ideal.Quotient.eq_zero_iff_mem.2 hl
    have h3 := Ideal.Quotient.eq_zero_iff_mem.2 h
    have h4 : G.map (Ideal.Quotient.mk M) = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hG, hij, Matrix.one_apply, h3]
    rw [key, h4] at h2
    have h5 : (1 + ((Ideal.Quotient.mk M).comp φ) l • (1 : Matrix (Fin n) (Fin n) (R ⧸ M))) =
        ((Ideal.Quotient.mk M).comp φ) (1 + l) • 1 := by
      rw [map_add, map_one, add_smul, one_smul]
    rw [h5, Matrix.det_smul, Matrix.det_one, mul_one] at h2
    have h6 := (map_eq_zero _).1 (pow_eq_zero_iff (by
      intro h; rw [h] at h2; simp at h2) |>.1 h2)
    exact eq_neg_of_add_eq_zero_right h6
  · left
    exact Set.mem_biUnion (s := {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}) ⟨hM, h⟩ hl
end GlobalTheory.UnRep
