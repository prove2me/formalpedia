-- Prove2me | solution 1 for GlobalTheory.UnitaryChar.char_eq_det_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:24:34.78348+00:00
-- url     : https://prove2.me/submissions/1e0aa69f-4bca-47f3-83af-3388b5cc800c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CircleHomEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpow
import Theorems.Thm_GlobalTheory_UnitaryChar_coe_diagHom
import Theorems.Thm_GlobalTheory_UnitaryChar_continuous_diagHom
import Theorems.Thm_GlobalTheory_UnitaryChar_exists_conj_diagHom
import Theorems.Thm_GlobalTheory_UnitaryChar_exists_conj_perm
import Theorems.Thm_GlobalTheory_circle_hom_eq_zpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitaryChar
variable {n : ℕ}
namespace GlobalTheory.UnitaryChar
theorem _root_.solution : ∀ (n : ℕ) (c : Matrix.unitaryGroup (Fin n) ℂ →* Circle), Continuous c → ∃ m : ℤ, ∀ u : Matrix.unitaryGroup (Fin n) ℂ, ((c u : Circle) : ℂ) = (Matrix.det (u : Matrix (Fin n) (Fin n) ℂ)) ^ m := by
  intro n c hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun u => ?_⟩
    have : u = 1 := Subtype.ext (Subsingleton.elim _ _)
    simp [this]
  set i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨m, hm⟩ := GlobalTheory.circle_hom_eq_zpow
    (c.comp ((diagHom n).comp (MonoidHom.mulSingle (fun _ : Fin n => Circle) i₀)))
    (hc.comp (continuous_diagHom.comp (continuous_mulSingle (A := fun _ : Fin n => Circle) i₀)))
  have hi : ∀ i z, c (diagHom n (Pi.mulSingle i z)) = z ^ m := fun i z => by
    obtain ⟨P, hP⟩ := exists_conj_perm (Equiv.swap i₀ i) (Pi.mulSingle i₀ z)
    have h1 : (Pi.mulSingle i₀ z : Fin n → Circle) ∘ (Equiv.swap i₀ i) = Pi.mulSingle i z := by
      ext j
      simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff,
        Equiv.swap_apply_left]
    have h2 := congrArg c hP
    rw [h1, map_mul, map_mul, mul_comm] at h2
    rw [← mul_right_cancel h2]
    exact hm z
  refine ⟨m, fun u => ?_⟩
  obtain ⟨V, t, h⟩ := exists_conj_diagHom u
  have h1 : c u = c (diagHom n t) := by
    rw [← h, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have h2 : (u : Matrix (Fin n) (Fin n) ℂ).det = ∏ i, (t i : ℂ) := by
    rw [← det_diagonal, ← coe_diagHom, ← h]
    have h3 : (V : Matrix (Fin n) (Fin n) ℂ) * star (V : Matrix (Fin n) (Fin n) ℂ) = 1 := V.2.2
    change _ = (star (V : Matrix (Fin n) (Fin n) ℂ) * u * V).det
    rw [det_mul_comm, ← mul_assoc, h3, one_mul]
  have h4 : c (diagHom n t) = (∏ i, t i) ^ m := by
    have h5 := map_prod (c.comp (diagHom n)) (fun i => Pi.mulSingle i (t i)) Finset.univ
    rw [Finset.univ_prod_mulSingle] at h5
    simp only [MonoidHom.comp_apply, hi] at h5
    rw [h5, Finset.prod_zpow]
  rw [h1, h2, h4, Circle.coe_zpow]
  congr 1
  exact map_prod Circle.coeHom _ _
end GlobalTheory.UnitaryChar
