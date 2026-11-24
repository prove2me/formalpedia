-- Prove2me | solution 1 for GlobalTheory.QNorm.relIndex_sqs_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:58:51.91293+00:00
-- url     : https://prove2.me/submissions/274d72c0-537c-461e-aa24-aa4516d02206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresLeTwoMulOfSubgroup
import Theorems.Thm_GlobalTheory_QNorm_relIndex_le_two_of_coset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (G : Type) [CommGroup G] (U H : Subgroup G) (ε : G), H ≤ U → H.relIndex U ≠ 0 →
      (∀ a : G, a ^ 2 = 1 → a = 1 ∨ a = ε) → (sqs H).relIndex H ≠ 0 →
      (sqs U).relIndex U ≠ 0 ∧ (sqs U).relIndex U ≤ 2 * (sqs H).relIndex H := by
  intro G _ U H ε hHU hfin hε hsq
  have hle : ∀ V : Subgroup G, sqs V ≤ V := by
    rintro V x ⟨y, hy, rfl⟩
    exact V.pow_mem hy 2
  have hmono : sqs H ≤ sqs U := Subgroup.map_mono hHU
  have h1 := Subgroup.relIndex_mul_relIndex (sqs H) H U (hle H) hHU
  have h2 := Subgroup.relIndex_mul_relIndex (sqs H) (sqs U) U hmono (hle U)
  set H' : Subgroup G := (sqs H).comap (powMonoidHom 2) with hH'
  have h3 : H'.relIndex U = (sqs H).relIndex (sqs U) := by
    rw [hH', Subgroup.relIndex_comap]; rfl
  have hHH' : H ≤ H' ⊓ U := le_inf (Subgroup.le_comap_map _ _) hHU
  have h4 := Subgroup.relIndex_mul_relIndex H (H' ⊓ U) U hHH' inf_le_right
  rw [Subgroup.inf_relIndex_right, h3] at h4
  have h5 : H.relIndex (H' ⊓ U) ≤ 2 := by
    apply relIndex_le_two_of_coset H _ ε
    rintro x ⟨⟨y, hy, hxy⟩, -⟩
    simp only [powMonoidHom_apply] at hxy
    have : (x * y⁻¹) ^ 2 = 1 := by rw [mul_pow, ← hxy, inv_pow, mul_inv_cancel]
    rcases hε _ this with h | h
    · left
      rw [mul_inv_eq_one] at h
      rw [h]; exact hy
    · right
      have e : x * ε⁻¹ = y := by
        rw [← h, mul_inv_rev, inv_inv, mul_comm y, mul_inv_cancel_left]
      rw [e]; exact hy
  have hne : (sqs H).relIndex (sqs U) * (sqs U).relIndex U ≠ 0 := by
    rw [h2, ← h1]; exact mul_ne_zero hsq hfin
  obtain ⟨hb, ha⟩ := mul_ne_zero_iff.mp hne
  refine ⟨ha, ?_⟩
  apply Nat.le_of_mul_le_mul_left _ (Nat.pos_of_ne_zero hb)
  rw [h2, ← h1, ← h4]
  calc (sqs H).relIndex H * (H.relIndex (H' ⊓ U) * (sqs H).relIndex (sqs U))
      ≤ (sqs H).relIndex H * (2 * (sqs H).relIndex (sqs U)) := by gcongr
    _ = _ := by ring
end GlobalTheory.QNorm
