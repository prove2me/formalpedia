-- Prove2me | solution 1 for NetworkControl.Backpressure.lemma_lyapunov_stability
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:25:04.532421+00:00
-- url     : https://prove2.me/submissions/7669d091-c483-4ddc-8458-8cbc54579fd1

import Mathlib
import Definitions.Def_NetworkControl_Backpressure_StronglyStable
import Definitions.Def_NetworkControl_Backpressure_lyapunovL

namespace NetworkControl.Backpressure

open MeasureTheory

/-- Deterministic backlog: `U(0) = 10`, `U(t) = 0` for `t ≥ 1`, one queue. -/
noncomputable def aux_lls_U : ℕ → Unit → Fin 1 → ℝ :=
  fun t _ _ => if t = 0 then 10 else 0

theorem aux_lls_drift (t : ℕ) :
    lyapunovL (aux_lls_U (t + 1) ()) - lyapunovL (aux_lls_U t ())
      ≤ 1 - 1 * ∑ i : Fin 1, aux_lls_U t () i := by
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; simp [aux_lls_U, lyapunovL]; norm_num
  · have : t ≠ 0 := Nat.pos_iff_ne_zero.mp h
    simp [aux_lls_U, lyapunovL, this]

end NetworkControl.Backpressure

open NetworkControl.Backpressure MeasureTheory

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {L : ℕ} (U : ℕ → Ω → Fin L → ℝ) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hMeas : ∀ t : ℕ, ∀ i : Fin L, Measurable (fun ω => U t ω i))
    (hIntegU : ∀ t : ℕ, ∀ i : Fin L, Integrable (fun ω => U t ω i) P)
    (hIntegDrift : ∀ t : ℕ, Integrable (fun ω => lyapunovL (U (t + 1) ω) - lyapunovL (U t ω)) P)
    (hdrift : ∀ t : ℕ,
      (P[(fun ω => lyapunovL (U (t + 1) ω) - lyapunovL (U t ω))
          | MeasurableSpace.comap (U t) inferInstance])
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin L, U t ω i)),
    NetworkStronglyStable (fun i t => ∫ ω, U t ω i ∂P) ∧
      ∀ t : ℕ, (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin L, ∫ ω, U τ ω i ∂P ≤ B / ε) := by
  intro H
  have key := H (Ω := Unit) (P := Measure.dirac ()) (L := 1) aux_lls_U 1 1 one_pos one_pos
    (fun t i => measurable_const)
    (fun t i => integrable_const _)
    (fun t => Integrable.of_finite)
    (fun t => by
      have hm : MeasurableSpace.comap (aux_lls_U t) inferInstance ≤ (inferInstance : MeasurableSpace Unit) := by
        intro s _; exact MeasurableSpace.measurableSet_top
      have hc : (fun ω : Unit => lyapunovL (aux_lls_U (t + 1) ω) - lyapunovL (aux_lls_U t ω))
          = fun _ => lyapunovL (aux_lls_U (t + 1) ()) - lyapunovL (aux_lls_U t ()) := by
        funext ω; cases ω; rfl
      rw [hc, condExp_const hm]
      refine Filter.Eventually.of_forall (fun ω => ?_)
      cases ω
      exact aux_lls_drift t)
  have h1 := key.2 1
  simp [aux_lls_U] at h1
