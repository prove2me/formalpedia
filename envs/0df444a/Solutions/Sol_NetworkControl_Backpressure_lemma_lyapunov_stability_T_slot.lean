-- Prove2me | solution 1 for NetworkControl.Backpressure.lemma_lyapunov_stability_T_slot
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:20:29.372355+00:00
-- url     : https://prove2.me/submissions/21242b03-7a43-4638-8d10-ad3cf05f0edb

import Mathlib
import Definitions.Def_NetworkControl_Backpressure_StronglyStable
import Definitions.Def_NetworkControl_Backpressure_lyapunovL

namespace NetworkControl.Backpressure

open MeasureTheory

/-- The deterministic counterexample backlog: `U(0) = 2`, `U(t) = 0` for `t ≥ 1`. -/
noncomputable def aux_lsT_U : ℕ → Unit → Fin 1 → ℝ := fun t _ _ => if t = 0 then 2 else 0

theorem aux_lsT_drift (t0 : ℕ) :
    lyapunovL (aux_lsT_U (t0 + 1) ()) - lyapunovL (aux_lsT_U t0 ()) ≤
      1 - 1 * ∑ i : Fin 1, aux_lsT_U t0 () i := by
  rcases Nat.eq_zero_or_pos t0 with h | h
  · subst h; simp [aux_lsT_U, lyapunovL]; norm_num
  · have h0 : t0 ≠ 0 := Nat.pos_iff_ne_zero.mp h
    simp [aux_lsT_U, lyapunovL, h0]

end NetworkControl.Backpressure

open NetworkControl.Backpressure
open MeasureTheory

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {L : ℕ} (U : ℕ → Ω → Fin L → ℝ) (T : ℕ) (hT : 0 < T) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hIntegInit : ∀ τ : ℕ, τ < T → ∀ i : Fin L, Integrable (fun ω => U τ ω i) P)
    (hMeas : ∀ t : ℕ, ∀ i : Fin L, Measurable (fun ω => U t ω i))
    (hIntegU : ∀ t : ℕ, ∀ i : Fin L, Integrable (fun ω => U t ω i) P)
    (hIntegDrift : ∀ t0 : ℕ,
      Integrable (fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω)) P)
    (hdrift : ∀ t0 : ℕ,
      (P[(fun ω => lyapunovL (U (t0 + T) ω) - lyapunovL (U t0 ω))
          | MeasurableSpace.comap (U t0) inferInstance])
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin L, U t0 ω i)),
    NetworkStronglyStable (fun i t => ∫ ω, U t ω i ∂P) ∧
      ∀ t : ℕ, (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin L, ∫ ω, U τ ω i ∂P ≤ B / ε) := by
  intro H
  have hm : ∀ t : ℕ, MeasurableSpace.comap (aux_lsT_U t) inferInstance ≤
      (inferInstance : MeasurableSpace Unit) :=
    fun t => (measurable_const).comap_le
  have hc : ∀ t0 : ℕ,
      (fun ω : Unit => lyapunovL (aux_lsT_U (t0 + 1) ω) - lyapunovL (aux_lsT_U t0 ω))
        = fun _ => lyapunovL (aux_lsT_U (t0 + 1) ()) - lyapunovL (aux_lsT_U t0 ()) :=
    fun _ => rfl
  have h1 := (H (Ω := Unit) (P := Measure.dirac ()) (L := 1) aux_lsT_U 1 one_pos 1 1
    one_pos one_pos
    (fun _ _ _ => integrable_const _) (fun _ _ => measurable_const)
    (fun _ _ => integrable_const _) (fun t0 => by rw [hc t0]; exact integrable_const _)
    (fun t0 => by
      rw [hc t0, condExp_const (hm t0)]
      exact Filter.Eventually.of_forall (fun ω => aux_lsT_drift t0))).2 1
  simp [aux_lsT_U] at h1
