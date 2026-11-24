-- Prove2me | solution 1 for GlobalTheory.OppRad.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:36:30.250097+00:00
-- url     : https://prove2.me/submissions/262f2bf6-ecf7-4d49-a298-f7a4360f4319

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_mem_U
import Theorems.Thm_GlobalTheory_OppRad_un_val
import Theorems.Thm_GlobalTheory_OppRad_conj_mem
import Theorems.Thm_GlobalTheory_OppRad_U_comm
import Theorems.Thm_GlobalTheory_OppRad_S_apply
import Theorems.Thm_GlobalTheory_OppRad_S_right
import Theorems.Thm_GlobalTheory_OppRad_S_left
import Theorems.Thm_GlobalTheory_OppRad_S_comm
import Theorems.Thm_GlobalTheory_OppRad_S_S
import Theorems.Thm_GlobalTheory_OppRad_eq_zero_of_S
import Theorems.Thm_GlobalTheory_OppRad_S_U
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
theorem _root_.solution {a b c d : R} (aa : a * a = a) (bb : b * b = b) (cc : c * c = c) (dd : d * d = d)
    (ab : a * b = 0) (ac : a * c = 0) (ad : a * d = 0) (ba : b * a = 0) (bc : b * c = 0) (bd : b * d = 0)
    (ca : c * a = 0) (cb : c * b = 0) (cd : c * d = 0) (da : d * a = 0) (db : d * b = 0) (dc : d * c = 0)
    (h1 : OppInj π a c) (h2 : OppInj π (a + b) d) {v : V} (hv : ∀ u ∈ U (a + b) (c + d), π u v = v)
    (h0 : S π (U (c + d) (a + b)) v = 0) : S π (U (a + c) (b + d)) v = 0 := by
  have t : ∀ {x y z : R}, x * y = z → ∀ r, x * (y * r) = z * r := fun h r => by rw [← mul_assoc, h]
  have dec : ∀ {p q : R} {u : Rˣ}, u ∈ U p q → ∃ x, u.val = 1 + p * (x * q) := fun {p q u} hu =>
    ⟨u.val - 1, by rw [hu.2, hu.1, add_sub_cancel]⟩
  have H := And.intro (And.intro (And.intro (And.intro aa (t aa)) (And.intro bb (t bb)))
      (And.intro (And.intro cc (t cc)) (And.intro dd (t dd))))
    (And.intro (And.intro (And.intro (And.intro (And.intro ab (t ab)) (And.intro ac (t ac)))
      (And.intro (And.intro ad (t ad)) (And.intro ba (t ba))))
      (And.intro (And.intro (And.intro bc (t bc)) (And.intro bd (t bd)))
      (And.intro (And.intro ca (t ca)) (And.intro cb (t cb)))))
      (And.intro (And.intro (And.intro cd (t cd)) (And.intro da (t da)))
      (And.intro (And.intro db (t db)) (And.intro dc (t dc)))))
  set z := S π (U (a + c) (b + d)) v with hz
  have k1 : ∀ u ∈ U a c, π u z = z := fun u hu => by
    obtain ⟨x, hx⟩ := dec hu
    rw [hz, S_U (p := a + c) (q := b + d), hv u] <;>
      simp [mem_U, hx, mul_add, add_mul, mul_assoc, H] <;> abel
  have k2 : ∀ u ∈ U (a + b + c) d, π u z = z := fun u hu => by
    obtain ⟨x, hx⟩ := dec hu
    have e : u = un (b * (x * d)) (by simp [mul_assoc, H]) *
        un ((a + c) * (x * d)) (by simp [mul_add, add_mul, mul_assoc, H]) :=
      Units.ext (by simp [hx, mul_add, add_mul, mul_assoc, H]; abel)
    rw [e, map_mul, Module.End.mul_apply, hz, S_left, S_U (p := a + c) (q := b + d), hv] <;>
      simp [mem_U, mul_add, add_mul, mul_assoc, H] <;> abel
  have k3 : S π (U (c + d) (a + b)) z = 0 := by
    haveI := Fintype.ofFinite (U (a + c) (b + d))
    rw [hz, S_apply π (U (a + c) (b + d)), map_sum]
    refine Finset.sum_eq_zero fun u _ => ?_
    obtain ⟨x, hx⟩ := dec u.2
    have e : u.1 = un (c * (x * b)) (by simp [mul_assoc, H]) *
        (un (a * (x * b) + c * (x * d)) (by simp [mul_add, add_mul, mul_assoc, H]) *
          un (a * (x * d)) (by simp [mul_assoc, H])) :=
      Units.ext (by simp [hx, mul_add, add_mul, mul_assoc, H]; abel)
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, S_right, hv,
      ← S_U (p' := c + d) (q' := a + b), h0, map_zero] <;>
      simp [mem_U, mul_add, add_mul, mul_assoc, H] <;> abel
  have hqp : (a + b) * (c + d) = 0 := by simp [mul_add, add_mul, H]
  have l1 : U c a ≤ U (c + d) (a + b) := fun u hu => by
    obtain ⟨x, hx⟩ := dec hu
    simp [mem_U, hx, mul_add, add_mul, mul_assoc, H]
  have l2 : U d (a + b) ≤ U (c + d) (a + b) := fun u hu => by
    obtain ⟨x, hx⟩ := dec hu
    simp [mem_U, hx, mul_add, add_mul, mul_assoc, H]
  refine h1 z k1 (h2 _ (fun u hu => ?_) (eq_zero_of_S (fun u hu => ?_) (S_S l2 (S_S l1 k3))))
  · haveI := Fintype.ofFinite (U c a)
    rw [S_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨x, hx⟩ := dec hu
    obtain ⟨y, hy⟩ := dec (inv_mem k.2)
    have : k.1⁻¹ * u * k.1⁻¹⁻¹ ∈ U (a + b + c) d := by
      refine conj_mem (p' := a + b + c) (q' := d) ?_ ?_ ?_ <;>
        simp [mem_U, hx, hy, mul_add, add_mul, mul_assoc, H] <;> abel
    conv_rhs => rw [← k2 _ this]
    simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
  · obtain ⟨x, hx⟩ := dec hu
    have e : u = un (d * (x * (a + b))) (by simp [mul_add, add_mul, mul_assoc, H]) *
        (un (c * (x * a)) (by simp [mul_assoc, H]) * un (c * (x * b)) (by simp [mul_assoc, H])) :=
      Units.ext (by simp [hx, mul_add, add_mul, mul_assoc, H]; abel)
    have m1 : un (c * (x * a)) (by simp [mul_assoc, H]) ∈ U c a := by simp [mem_U, mul_assoc, H]
    have m2 : un (c * (x * b)) (by simp [mul_assoc, H]) ∈ U (c + d) (a + b) := by
      simp [mem_U, mul_add, add_mul, mul_assoc, H]
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      S_comm fun w hw => U_comm hqp m2 (l2 hw), S_comm fun w hw => U_comm hqp m2 (l1 hw),
      S_comm fun w hw => U_comm hqp (l1 m1) (l2 hw), S_left m1, hz, S_left, S_left] <;>
      simp [mem_U, mul_add, add_mul, mul_assoc, H]
end GlobalTheory.OppRad
