-- Prove2me | solution 1 for GlobalTheory.Phase.GaussSum.pow_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:41:27.316256+00:00
-- url     : https://prove2.me/submissions/e677675a-1a57-4d7e-8269-943b7d029004

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum
import Theorems.Thm_GlobalTheory_Phase_GaussSum_twist
import Theorems.Thm_GlobalTheory_Phase_GaussSum_quat_add
import Theorems.Thm_GlobalTheory_Phase_GaussSum_quat_conj
import Theorems.Thm_GlobalTheory_Phase_GaussSum_quat_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.GaussSum
namespace GlobalTheory.Phase.GaussSum
theorem _root_.solution {M W : Type} [AddCommGroup M] [Fintype M] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (q : M → W) (β : M →+ M →+ W) (hq : ∀ x y, q (x + y) = q x + q y + β x y) :
    (∑ x, e (q x)) ^ 4 = 0 ∨ ∃ a : Fin 4 → M,
      (∑ x, e (q x)) ^ 4 = (∏ i, e (q (a i))) * conj ((∑ x, e (q x)) ^ 4) := by
  classical
  set n := Fintype.card M with hn
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hnx : ∀ x : M, (n : ℤ) • x = 0 := fun x => by
    rw [natCast_zsmul]; exact card_nsmul_eq_zero
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares (n - 1)
  have hm : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (n : ℤ) - 1 := by
    have h := congrArg (fun t : ℕ => (t : ℤ)) habcd
    push_cast [Nat.cast_sub hn1] at h
    exact h
  have hinj : Function.Injective (quat (M := M) (a : ℤ) b c d) := by
    intro x y hxy
    funext i
    have hx := quat_conj (a : ℤ) b c d x i
    have hy := quat_conj (a : ℤ) b c d y i
    rw [hm, sub_smul, hnx, one_smul, zero_sub] at hx hy
    rw [← neg_inj, ← hx, ← hy, hxy]
  have hbij := hinj.bijective_of_finite
  have hprod : ∀ y : Fin 4 → W, e (∑ i, y i) = ∏ i, e (y i) := by
    intro y; simp only [Fin.sum_univ_four, Fin.prod_univ_four, he]
  have hS4 : (∑ x, e (q x)) ^ 4 = ∑ x : Fin 4 → M, e (∑ i, q (x i)) := by
    rw [Finset.sum_pow', Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun x _ => (hprod (fun i => q (x i))).symm)
  let B : (Fin 4 → M) →+ (Fin 4 → M) →+ W := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => ∑ i, β (x i) (y i))
      (fun y z => by simp [Finset.sum_add_distrib]))
    (fun x y => by ext z; simp [Finset.sum_add_distrib])
  have hB : ∀ x y, B x y = ∑ i, β (x i) (y i) := fun _ _ => rfl
  have hQ : ∀ x y : Fin 4 → M, ∑ i, q ((x + y) i) = ∑ i, q (x i) + ∑ i, q (y i) + B x y := by
    intro x y
    simp only [hB, Pi.add_apply, hq, Finset.sum_add_distrib]
  have hnB : ∀ x y, (n : ℤ) • B x y = 0 := by
    intro x y
    rw [← map_zsmul]
    have : (n : ℤ) • y = 0 := funext fun i => hnx (y i)
    rw [this, map_zero]
  let ψ : (Fin 4 → M) →+ W := AddMonoidHom.mk'
    (fun x => ∑ i, q (quat (a : ℤ) b c d x i) + ∑ i, q (x i)) (by
      intro x y
      rw [quat_add, hQ, hQ, hB (quat _ _ _ _ _), quat_form, hm, ← hB, sub_smul, hnB, one_smul]
      abel)
  have := twist e he hc h0 (fun x : Fin 4 → M => ∑ i, q (x i)) B hQ ψ (by
    rw [← hbij.sum_comp (fun x => e (∑ i, q (x i)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    simp [ψ])
  rw [← hS4] at this
  simpa only [hprod] using this
end GlobalTheory.Phase.GaussSum
