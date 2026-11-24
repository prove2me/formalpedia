-- Prove2me | solution 1 for GlobalTheory.BK.exists_eq_mul_add_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:34:13.69582+00:00
-- url     : https://prove2.me/submissions/1747811a-34fe-44cf-ae7a-42f82a7ab4c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
namespace GlobalTheory.BK
theorem _root_.solution {R : Type} [CommRing R] (t : R)
    [IsAdicComplete (Ideal.span {t}) R] (T : R →+ R) (hT : ∀ x, T (t * x) = t * T x) (w : R) :
    ∃ x, x = t * T x + w := by
  have hS (n : ℕ) (x y : R) : x ≡ y [SMOD (Ideal.span {t} ^ n • ⊤ : Ideal R)] ↔ t ^ n ∣ x - y := by
    simp [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hd (n : ℕ) (x : R) (h : t ^ n ∣ x) : t ^ (n + 1) ∣ t * T x := by
    obtain ⟨y, rfl⟩ := h
    have : T (t ^ n * y) = t ^ n * T y := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', mul_assoc, hT, ih, mul_assoc]
    exact ⟨T y, by rw [this]; ring⟩
  let f : ℕ → R := fun n => (fun x => t * T x + w)^[n] 0
  have hf (n : ℕ) : f (n + 1) = t * T (f n) + w := Function.iterate_succ_apply' _ _ _
  have h1 (n : ℕ) : t ^ n ∣ f (n + 1) - f n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hf (n + 1), hf n, add_sub_add_right_eq_sub, ← mul_sub, ← map_sub, ← hf]
      exact hd _ _ ih
  obtain ⟨x, hx⟩ := IsPrecomplete.prec' (I := Ideal.span {t}) f (fun {m n} hmn => by
    rw [hS]
    induction hmn with
    | refl => simp
    | step h ih =>
      have := dvd_sub ih ((pow_dvd_pow t h).trans (h1 _))
      convert this using 1
      simp)
  refine ⟨x, sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {t}) _ fun n => ?_)⟩
  rw [hS, sub_zero]
  have := dvd_sub (hd n _ ((hS _ _ _).1 (hx n))) ((hS _ _ _).1 (hx (n + 1)))
  refine (pow_dvd_pow t n.le_succ).trans ?_
  convert this using 1
  rw [hf, map_sub]
  ring
end GlobalTheory.BK
