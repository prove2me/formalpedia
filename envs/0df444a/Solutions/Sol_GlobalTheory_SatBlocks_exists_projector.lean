-- Prove2me | solution 1 for GlobalTheory.SatBlocks.exists_projector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:02.783944+00:00
-- url     : https://prove2.me/submissions/c4ec5915-92f9-419e-a501-37b9644d03a9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SaturatedBlocksSummand
import Theorems.Thm_GlobalTheory_SatBlocks_ne_zero_of_val_zero
import Theorems.Thm_GlobalTheory_SatBlocks_inv_mem_of_val_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.SatBlocks
namespace GlobalTheory.SatBlocks
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {O A : Type}
    [DecidableEq A] {n : A → ℕ} {d : ℕ} (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C)
    (u : (Σ a : A, Fin (n a)) → Fin d → C)
    (hM : ∀ x i j, M x i j ∈ intRing v) (he : ∀ a x, em a x ∈ intRing v)
    (hu : ∀ x q, (M x).mulVec (u q) = em q.1 x • u q)
    (hs : ∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) (a : A) (S : Finset A) (ha : a ∉ S) :
    ∃ (P : Matrix (Fin d) (Fin d) C) (c : A → C), (∀ i j, P i j ∈ intRing v) ∧
      (∀ q, P.mulVec (u q) = c q.1 • u q) ∧ c a = 1 ∧ ∀ b ∈ S, c b = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 1, ?_, by simp, rfl, by simp⟩
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | insert b S hb ih =>
    rw [Finset.mem_insert, not_or] at ha
    obtain ⟨P, c, hP, hPu, hca, hcS⟩ := ih ha.2
    obtain ⟨x, hx⟩ := hs a b ha.1
    refine ⟨((em a x - em b x)⁻¹ • (M x - em b x • (1 : Matrix (Fin d) (Fin d) C))) * P,
      fun e => (em a x - em b x)⁻¹ * (em e x - em b x) * c e, ?_, ?_, ?_, ?_⟩
    · intro i j
      rw [Matrix.mul_apply]
      refine sum_mem fun k _ => mul_mem ?_ (hP k j)
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      refine mul_mem (inv_mem_of_val_zero v hx) (sub_mem (hM x i k) (mul_mem (he b x) ?_))
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro q
      rw [← Matrix.mulVec_mulVec, hPu, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, hu]
      ext k
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    · simp only [hca, mul_one]
      exact inv_mul_cancel₀ (ne_zero_of_val_zero v hx)
    · intro e he'
      rcases Finset.mem_insert.1 he' with rfl | h
      · simp
      · simp [hcS e h]
end GlobalTheory.SatBlocks
