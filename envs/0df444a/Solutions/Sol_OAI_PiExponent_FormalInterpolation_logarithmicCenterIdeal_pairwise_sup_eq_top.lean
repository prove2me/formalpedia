-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_pairwise_sup_eq_top
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:01:19.632056+00:00
-- url     : https://prove2.me/submissions/e66fac7a-67cf-4e32-b795-17de75f54080

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.FormalInterpolation

theorem solution : ¬ (∀ {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (j k : Fin K) (hjk : j ≠ k),
    logarithmicCenterIdeal (c j) (fun _ => e 0) e ⊔
      logarithmicCenterIdeal (c k) (fun _ => e 0) e = ⊤) := by
  intro h
  let c : Fin 2 → Fin 0 → Complex := fun _ i => Fin.elim0 i
  let e : Fin (0 + 1) → Nat := fun _ => 1
  have hc : ∀ i : Fin 0, Function.Injective (fun j : Fin 2 => c j i) := by
    intro i
    exact Fin.elim0 i
  have he : ∀ i : Fin (0 + 1), 0 < e i := by
    intro i
    simp [e]
  let j : Fin 2 := 0
  let k : Fin 2 := 1
  have hjk : j ≠ k := by decide
  have htop := h (m := 0) (K := 2) c hc e he j k hjk
  let x : Fin (0 + 1) → Complex := fun _ => 1
  let ev := MvPolynomial.eval x
  have hleft : logarithmicCenterIdeal (c j) (fun _ => e 0) e ≤ RingHom.ker ev := by
    apply Ideal.span_le.2
    rintro p ⟨i, rfl⟩
    apply RingHom.mem_ker.mpr
    fin_cases i
    simp [ev, x, logarithmicCoordinate, e]
  have hright : logarithmicCenterIdeal (c k) (fun _ => e 0) e ≤ RingHom.ker ev := by
    apply Ideal.span_le.2
    rintro p ⟨i, rfl⟩
    apply RingHom.mem_ker.mpr
    fin_cases i
    simp [ev, x, logarithmicCoordinate, e]
  have hsum :
      logarithmicCenterIdeal (c j) (fun _ => e 0) e ⊔
        logarithmicCenterIdeal (c k) (fun _ => e 0) e ≤ RingHom.ker ev :=
    sup_le hleft hright
  have hone : (1 : MvPolynomial (Fin (0 + 1)) Complex) ∈
      logarithmicCenterIdeal (c j) (fun _ => e 0) e ⊔
        logarithmicCenterIdeal (c k) (fun _ => e 0) e := by
    rw [htop]
    simp
  have hev : ev 1 = 0 := RingHom.mem_ker.mp (hsum hone)
  have hzero : (1 : Complex) = 0 := by simpa [ev] using hev
  exact one_ne_zero hzero