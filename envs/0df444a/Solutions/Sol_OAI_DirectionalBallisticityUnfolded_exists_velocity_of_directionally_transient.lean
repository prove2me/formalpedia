-- Prove2me | solution 1 for OAI.DirectionalBallisticityUnfolded.exists_velocity_of_directionally_transient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:10:36.156898+00:00
-- url     : https://prove2.me/submissions/d7bfbb4d-080f-49d9-a610-3659875f58a1

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Theorems.Thm_OAI_DirectionalTransience_directional_transience_implies_ballisticity

namespace Q245Dev

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

theorem exists_velocity_dev {d : ℕ} (hd : 2 ≤ d)
    (ν : Measure {p : (Fin d × Bool) → ℝ≥0 // ∑ e, p e = 1}) [IsProbabilityMeasure ν]
    (hue : ∃ κ : ℝ≥0, 0 < κ ∧ ∀ᵐ p ∂ν, ∀ e, κ ≤ p.1 e)
    (ℓ : Fin d → ℝ) (hℓ : ∑ i, ℓ i * ℓ i = 1)
    (K : Kernel (((Fin d → ℤ) → {p : (Fin d × Bool) → ℝ≥0 // ∑ e, p e = 1}) × (Fin d → ℤ))
      (((Fin d → ℤ) → {p : (Fin d × Bool) → ℝ≥0 // ∑ e, p e = 1}) × (Fin d → ℤ)))
    [IsMarkovKernel K]
    (hK : ∀ z, K z = ∑ e : Fin d × Bool,
      ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 +
        (fun i => if i = e.1 then (if e.2 then (1 : ℤ) else -1) else 0)))
    (P : Measure (ℕ → Fin d → ℤ))
    (hP : P = (@Kernel.trajMeasure
      (fun _ => ((Fin d → ℤ) → {p : (Fin d × Bool) → ℝ≥0 // ∑ e, p e = 1}) × (Fin d → ℤ)) _
      ((Measure.infinitePi (fun _ : (Fin d → ℤ) => ν)).map (fun ω => (ω, (0 : Fin d → ℤ))))
      (fun n => K.comap (fun z : ((i : Finset.Iic n) → _) => z ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _)) _).map (fun z n => (z n).2))
    (htrans : ∀ᵐ X ∂P, Tendsto (fun n => ∑ i, (X n i : ℝ) * ℓ i) atTop atTop) :
    ∃ v : Fin d → ℝ, 0 < ∑ i, v i * ℓ i ∧
      ∀ᵐ X ∂P, Tendsto (fun n : ℕ => fun i => (X n i : ℝ) / (n : ℝ)) atTop (𝓝 v) := by
  have hKt : K = OAI.DirectionalTransience.transition := by
    ext z : 1
    rw [hK z]; rfl
  subst hKt
  subst hP
  exact OAI.DirectionalTransience.directional_transience_implies_ballisticity d hd ν inferInstance hue ℓ hℓ htrans

end Q245Dev

theorem solution : type_of% @Q245Dev.exists_velocity_dev := @Q245Dev.exists_velocity_dev
