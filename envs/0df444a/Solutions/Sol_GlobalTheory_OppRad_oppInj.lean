-- Prove2me | solution 1 for GlobalTheory.OppRad.oppInj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:50:16.42036+00:00
-- url     : https://prove2.me/submissions/eb936546-109d-46ad-899a-287888a27cd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_un_val
import Theorems.Thm_GlobalTheory_OppRad_un_mem
import Theorems.Thm_GlobalTheory_OppRad_S_apply
import Theorems.Thm_GlobalTheory_OppRad_S_right
import Theorems.Thm_GlobalTheory_OppRad_eq_zero_of_S
import Theorems.Thm_GlobalTheory_OppRad_S_U
import Theorems.Thm_GlobalTheory_OppRad_step
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.OppRad.un_val

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R V : Type} [Ring R] [Finite R] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ Rˣ V}
namespace GlobalTheory.OppRad
theorem _root_.solution (hreg : ∀ x : R, ∃ y, x * y * x = x) {p q : R} (pp : p * p = p) (qq : q * q = q)
    (pq : p * q = 0) (qp : q * p = 0) : OppInj π p q := by
  generalize hn : {x : R | (p + q) * x = x}.ncard = n
  induction n using Nat.strong_induction_on generalizing p q with
  | _ n ih =>
  intro v hv h0
  haveI := Fintype.ofFinite (U q p)
  have h1 : S π (U p q) (S π (U q p) v) = 0 := by rw [h0, map_zero]
  rw [S_apply π (U q p), map_sum, Finset.sum_eq_single 1 (fun u _ hu => ?_) (by simp)] at h1
  · exact eq_zero_of_S hv (by simpa using h1)
  obtain ⟨X, hX⟩ : ∃ X, u.1.val = 1 + X := ⟨u.1.val - 1, by simp⟩
  have X0 : X ≠ 0 := fun e => hu (Subtype.ext (Units.ext (by simpa [e] using hX)))
  have qX : q * X = X := by simpa [hX] using u.2.1
  have Xp : X * p = X := by simpa [hX] using u.2.2
  obtain ⟨y, hy⟩ := hreg X
  have t : ∀ {x y z : R}, x * y = z → ∀ r, x * (y * r) = z * r := fun h r => by rw [← mul_assoc, h]
  obtain ⟨Y, pY, Yq, XYX, YXY⟩ : ∃ Y, p * Y = Y ∧ Y * q = Y ∧ X * (Y * X) = X ∧ Y * (X * Y) = Y := by
    have hy' : ∀ r, X * (y * (X * r)) = X * r := fun r => by rw [← mul_assoc, ← mul_assoc, hy]
    have hy'' : X * (y * X) = X := by rw [← mul_assoc, hy]
    refine ⟨p * (y * (X * (y * q))), ?_, ?_, ?_, ?_⟩ <;> simp [mul_assoc, t pp, qq, qX, t qX, t Xp, hy', hy'']
  have pX : p * X = 0 := by rw [← qX, t pq, zero_mul]
  have Xq : X * q = 0 := by rw [← Xp, mul_assoc, pq, mul_zero]
  have qY : q * Y = 0 := by rw [← pY, t qp, zero_mul]
  have Yp : Y * p = 0 := by rw [← Yq, mul_assoc, qp, mul_zero]
  have XX : X * X = 0 := by rw [← t Xp X, pX, mul_zero]
  have YY : Y * Y = 0 := by rw [← t Yq Y, qY, mul_zero]
  have XYX' : ∀ r, X * (Y * (X * r)) = X * r := fun r => by rw [← mul_assoc Y, t XYX]
  have YXY' : ∀ r, Y * (X * (Y * r)) = Y * r := fun r => by rw [← mul_assoc X, t YXY]
  have H := And.intro (And.intro (And.intro (And.intro pp (t pp)) (And.intro qq (t qq)))
      (And.intro (And.intro pq (t pq)) (And.intro qp (t qp))))
    (And.intro (And.intro (And.intro (And.intro (And.intro qX (t qX)) (And.intro Xp (t Xp)))
      (And.intro (And.intro pY (t pY)) (And.intro Yq (t Yq))))
      (And.intro (And.intro (And.intro pX (t pX)) (And.intro Xq (t Xq)))
      (And.intro (And.intro qY (t qY)) (And.intro Yp (t Yp)))))
      (And.intro (And.intro (And.intro XX (t XX)) (And.intro YY (t YY)))
      (And.intro (And.intro XYX XYX') (And.intro YXY YXY'))))
  have lt : ∀ {r s : R}, (p + q) * r = r → (p + q) * s = s → r * s = 0 → s ≠ 0 →
      {x : R | r * x = x}.ncard < n := fun {r s} a1 a2 a3 a4 => by
    rw [← hn]
    refine Set.ncard_lt_ncard ⟨fun x (hx : r * x = x) => ?_, fun h => a4 ?_⟩
    · show (p + q) * x = x
      rw [← hx, t a1]
    · exact (h (show s ∈ {x | (p + q) * x = x} from a2)).symm.trans a3
  have e1 : p - Y * X + Y * X = p := sub_add_cancel _ _
  have e2 : X * Y + (q - X * Y) = q := add_sub_cancel _ _
  have key := step (π := π) (a := p - Y * X) (b := Y * X) (c := X * Y) (d := q - X * Y) (v := v)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (ih _ (lt (s := Y * X) ?_ ?_ ?_ fun e => X0 (by rw [← XYX, e, mul_zero])) ?_ ?_ ?_ ?_ rfl)
    (ih _ (lt (s := X * Y) ?_ ?_ ?_ fun e => X0 (by rw [← XYX, ← mul_assoc, e, zero_mul])) ?_ ?_ ?_ ?_ rfl)
    (by rwa [e1, e2]) (by rwa [e1, e2])
  · have m : un Y YY ∈ U p q := un_mem YY pY Yq
    have e : u.1 = un Y YY * (((un Y YY)⁻¹ * u.1 * (un Y YY)⁻¹) * un Y YY) := by group
    have hw : ((un Y YY)⁻¹ * u.1 * (un Y YY)⁻¹).val = (1 - Y) * (1 + X) * (1 - Y) := by
      rw [Units.val_mul, Units.val_mul, hX]; rfl
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, S_right m, hv _ m,
      ← S_U (p' := p - Y * X + X * Y) (q' := Y * X + (q - X * Y)), key, map_zero] <;>
    · rw [hw]
      simp [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, H]
      try abel
  all_goals simp [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, H]
end GlobalTheory.OppRad
