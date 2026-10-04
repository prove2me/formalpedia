-- Prove2me | solution 1 for GravesWillems.Serial.expected_backlog_transfer_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:17:04.17785+00:00
-- url     : https://prove2.me/submissions/a88c7a82-a8db-46a7-8fbb-e03f1ca36284

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP

set_option autoImplicit false

namespace P2M_ff79220d

open MeasureTheory GravesWillems.Serial

theorem agreeAux (T : ℕ → ℕ) (B B' : ℕ → ℝ) (d : ℤ → ℝ) :
    ∀ (r i : ℕ) (t : ℤ), (∀ j, i ≤ j → B' j = B j) →
      backlogAux T B' d r i t = backlogAux T B d r i t := by
  intro r
  induction r with
  | zero => intro i t _; rfl
  | succ r ih =>
    intro i t h
    simp only [backlogAux]
    rw [h i le_rfl, ih (i + 1) _ (fun j hj => h j (by omega))]

theorem backlog_succ (N : ℕ) (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) (i : ℕ) (t : ℤ)
    (hi : i ≤ N) :
    backlog N T B d i t = max 0 (windowDemand d (t - (T i : ℤ)) t
      + backlog N T B d (i + 1) (t - (T i : ℤ)) - B i) := by
  unfold backlog
  rw [show N + 1 - i = (N + 1 - (i + 1)) + 1 by omega]
  rfl

theorem transfer_ne (B : ℕ → ℝ) (k : ℕ) (Δ : ℝ) (j : ℕ) (h1 : j ≠ k) (h2 : j ≠ k + 1) :
    transfer B k Δ j = B j := by
  simp [transfer, h1, h2]

theorem transfer_k (B : ℕ → ℝ) (k : ℕ) (Δ : ℝ) : transfer B k Δ k = B k - Δ := by
  simp [transfer]

theorem transfer_k1 (B : ℕ → ℝ) (k : ℕ) (Δ : ℝ) :
    transfer B k Δ (k + 1) = B (k + 1) + Δ := by
  simp [transfer]

theorem maxbounds (a b Δ : ℝ) (hΔ : 0 ≤ Δ) (h1 : a ≤ b) (h2 : b ≤ a + Δ) :
    max 0 a ≤ max 0 b ∧ max 0 b ≤ max 0 a + Δ :=
  ⟨max_le_max le_rfl h1,
    max_le (by linarith [le_max_left (0:ℝ) a]) (by linarith [le_max_right (0:ℝ) a])⟩

theorem stage_k1 (N : ℕ) (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) (k : ℕ) (hkN : k + 1 ≤ N)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (t : ℤ) :
    backlog N T (transfer B k Δ) d (k + 1) t ≤ backlog N T B d (k + 1) t ∧
      backlog N T B d (k + 1) t - Δ ≤ backlog N T (transfer B k Δ) d (k + 1) t := by
  rw [backlog_succ N T _ d _ t hkN, backlog_succ N T B d _ t hkN, transfer_k1]
  have hag : backlog N T (transfer B k Δ) d (k + 1 + 1) (t - (T (k + 1) : ℤ))
      = backlog N T B d (k + 1 + 1) (t - (T (k + 1) : ℤ)) := by
    unfold backlog
    exact agreeAux T B _ d _ _ _ (fun j hj => transfer_ne B k Δ j (by omega) (by omega))
  rw [hag]
  set x := windowDemand d (t - (T (k + 1) : ℤ)) t
      + backlog N T B d (k + 1 + 1) (t - (T (k + 1) : ℤ)) - B (k + 1)
  have hx : windowDemand d (t - (T (k + 1) : ℤ)) t
      + backlog N T B d (k + 1 + 1) (t - (T (k + 1) : ℤ)) - (B (k + 1) + Δ) = x - Δ := by
    simp only [x]; ring
  rw [hx]
  refine ⟨max_le_max le_rfl (by linarith), ?_⟩
  rw [sub_le_iff_le_add]
  exact max_le (by linarith [le_max_left (0:ℝ) (x - Δ)])
    (by linarith [le_max_right (0:ℝ) (x - Δ)])

theorem stage_low (N : ℕ) (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) (k : ℕ) (hkN : k + 1 ≤ N)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    ∀ (n i : ℕ) (t : ℤ), i + n = k →
      backlog N T B d i t ≤ backlog N T (transfer B k Δ) d i t ∧
        backlog N T (transfer B k Δ) d i t ≤ backlog N T B d i t + Δ := by
  intro n
  induction n with
  | zero =>
    intro i t hi
    have hik : i = k := by omega
    subst hik
    rw [backlog_succ N T (transfer B i Δ) d i t (by omega), backlog_succ N T B d i t (by omega),
      transfer_k]
    have h := stage_k1 N T B d i hkN Δ hΔ (t - (T i : ℤ))
    apply maxbounds _ _ Δ hΔ <;> linarith [h.1, h.2]
  | succ n ih =>
    intro i t hi
    rw [backlog_succ N T (transfer B k Δ) d i t (by omega), backlog_succ N T B d i t (by omega),
      transfer_ne B k Δ i (by omega) (by omega)]
    have h := ih (i + 1) (t - (T i : ℤ)) (by omega)
    apply maxbounds _ _ Δ hΔ <;> linarith [h.1, h.2]

theorem intAux {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (T : ℕ → ℕ) (B : ℕ → ℝ) :
    ∀ (r i : ℕ) (t : ℤ), Integrable (fun ω => backlogAux T B (d ω) r i t) μ := by
  intro r
  induction r with
  | zero => intro i t; simp only [backlogAux]; exact integrable_zero _ _ _
  | succ r ih =>
    intro i t
    simp only [backlogAux]
    have hw : Integrable (fun ω => windowDemand (d ω) (t - (T i : ℤ)) t) μ := by
      unfold windowDemand
      exact integrable_finsetSum _ (fun τ _ => hd τ)
    have h2 := (hw.add (ih (i + 1) (t - (T i : ℤ)))).sub (integrable_const (B i))
    have h3 := (integrable_zero Ω ℝ μ).sup h2
    convert h3 using 1
    funext ω
    simp only [Pi.sup_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply]

end P2M_ff79220d

open MeasureTheory GravesWillems.Serial in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (N : ℕ) (T : ℕ → ℕ) (B : ℕ → ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k + 1 ≤ N)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (t : ℤ) :
    (∀ i ∈ Finset.Icc 1 N, k + 1 < i →
      ∫ ω, backlog N T (transfer B k Δ) (d ω) i t ∂μ = ∫ ω, backlog N T B (d ω) i t ∂μ) ∧
    (∀ i ∈ Finset.Icc 1 N, i < k + 1 →
      ∫ ω, backlog N T B (d ω) i t ∂μ ≤ ∫ ω, backlog N T (transfer B k Δ) (d ω) i t ∂μ ∧
      ∫ ω, backlog N T (transfer B k Δ) (d ω) i t ∂μ ≤ ∫ ω, backlog N T B (d ω) i t ∂μ + Δ) ∧
    (∫ ω, backlog N T (transfer B k Δ) (d ω) (k + 1) t ∂μ
        ≤ ∫ ω, backlog N T B (d ω) (k + 1) t ∂μ ∧
      ∫ ω, backlog N T B (d ω) (k + 1) t ∂μ - Δ
        ≤ ∫ ω, backlog N T (transfer B k Δ) (d ω) (k + 1) t ∂μ) := by
  have hint : ∀ (B' : ℕ → ℝ) (i : ℕ),
      Integrable (fun ω => backlog N T B' (d ω) i t) μ := by
    intro B' i
    unfold backlog
    exact P2M_ff79220d.intAux μ d hd T B' _ _ _
  have hcA : ∀ (f : Ω → ℝ), Integrable f μ → ∫ ω, (f ω + Δ) ∂μ = ∫ ω, f ω ∂μ + Δ := by
    intro f hf
    rw [integral_add hf (integrable_const Δ), integral_const]
    simp
  have hcS : ∀ (f : Ω → ℝ), Integrable f μ → ∫ ω, (f ω - Δ) ∂μ = ∫ ω, f ω ∂μ - Δ := by
    intro f hf
    rw [integral_sub hf (integrable_const Δ), integral_const]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro i _ hi
    congr 1
    funext ω
    unfold backlog
    exact P2M_ff79220d.agreeAux T B _ (d ω) _ _ _
      (fun j hj => P2M_ff79220d.transfer_ne B k Δ j (by omega) (by omega))
  · intro i _ hi
    have hp := fun ω => P2M_ff79220d.stage_low N T B (d ω) k hkN Δ hΔ (k - i) i t (by omega)
    refine ⟨integral_mono (hint _ _) (hint _ _) (fun ω => (hp ω).1), ?_⟩
    rw [← hcA _ (hint B i)]
    exact integral_mono (hint _ _) ((hint B i).add (integrable_const Δ)) (fun ω => (hp ω).2)
  · have hp := fun ω => P2M_ff79220d.stage_k1 N T B (d ω) k hkN Δ hΔ t
    refine ⟨integral_mono (hint _ _) (hint _ _) (fun ω => (hp ω).1), ?_⟩
    rw [← hcS _ (hint B (k + 1))]
    exact integral_mono ((hint B _).sub (integrable_const Δ)) (hint _ _) (fun ω => (hp ω).2)
