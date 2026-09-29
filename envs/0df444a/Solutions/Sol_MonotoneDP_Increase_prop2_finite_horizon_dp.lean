-- Prove2me | solution 1 for MonotoneDP.Increase.prop2_finite_horizon_dp
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:26:03.829827+00:00
-- url     : https://prove2.me/submissions/f4e94374-0cbc-410a-ac5e-d822716101ca

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

namespace Model

variable {S C : Type*} (m : Model S C)

theorem aux_p2f_Tmu_mono (μ : m.Selector) {J J' : S → EReal} (h : J ≤ J') :
    m.Tmu μ J ≤ m.Tmu μ J' := fun x => m.mono x (μ.1 x) (μ.2 x) J J' h

theorem aux_p2f_T_mono {J J' : S → EReal} (h : J ≤ J') : m.T J ≤ m.T J' := by
  intro x
  unfold T
  exact iInf₂_mono fun u hu => m.mono x u hu J J' h

theorem aux_p2f_T_le_Tmu (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J := by
  intro x
  unfold T Tmu
  exact iInf₂_le (μ.1 x) (μ.2 x)

theorem aux_p2f_comp_mono (π : m.Policy) :
    ∀ N : ℕ, ∀ {J J' : S → EReal}, J ≤ J' → m.comp π N J ≤ m.comp π N J' := by
  intro N
  induction N with
  | zero => intro J J' h; exact h
  | succ N ih =>
    intro J J' h
    exact ih (aux_p2f_Tmu_mono m (π N) h)

theorem aux_p2f_iter_le_comp (π : m.Policy) :
    ∀ N : ℕ, ∀ J : S → EReal, (m.T)^[N] J ≤ m.comp π N J := by
  intro N
  induction N with
  | zero => intro J; exact le_rfl
  | succ N ih =>
    intro J
    rw [Function.iterate_succ_apply]
    exact le_trans (ih (m.T J)) (aux_p2f_comp_mono m π N (aux_p2f_T_le_Tmu m (π N) J))

theorem aux_p2f_comp_succ (π : m.Policy) :
    ∀ N : ℕ, ∀ J : S → EReal,
      m.comp π (N + 1) J = m.Tmu (π 0) (m.comp (fun k => π (k + 1)) N J) := by
  intro N
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show m.comp π (N + 1) (m.Tmu (π (N + 1)) J) = _
    rw [ih]
    rfl

theorem aux_p2f_Jbar_le_iter (hI : m.AssumptionI) : ∀ N : ℕ, m.Jbar ≤ (m.T)^[N] m.Jbar := by
  intro N
  induction N with
  | zero => exact le_rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    refine le_trans ?_ (aux_p2f_T_mono m ih)
    intro x
    unfold T
    exact le_iInf₂ fun u hu => hI x u hu

theorem aux_p2f_select (J : S → EReal) (hJ : ∀ y, m.T J y ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : m.Selector, ∀ y, m.Tmu μ J y ≤ m.T J y + (ε : EReal) := by
  have key : ∀ y, ∃ u, u ∈ m.U y ∧ m.H y u J ≤ m.T J y + (ε : EReal) := by
    intro y
    have hy := hJ y
    induction h : m.T J y using EReal.rec with
    | bot => exact absurd h hy
    | top =>
      obtain ⟨u, hu⟩ := m.U_nonempty y
      refine ⟨u, hu, ?_⟩
      rw [EReal.top_add_coe]
      exact le_top
    | coe r =>
      have hlt : m.T J y < ((r + ε : ℝ) : EReal) := by
        rw [h]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
      unfold T at hlt
      rw [iInf_lt_iff] at hlt
      obtain ⟨u, hu⟩ := hlt
      rw [iInf_lt_iff] at hu
      obtain ⟨hu, hlt⟩ := hu
      refine ⟨u, hu, ?_⟩
      rw [← EReal.coe_add]
      exact hlt.le
  choose f hf using key
  exact ⟨⟨f, fun y => (hf y).1⟩, fun y => (hf y).2⟩

theorem aux_p2f_main (hI : m.AssumptionI) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ π : m.Policy, ∀ x, m.comp π N m.Jbar x ≤ (m.T)^[N] m.Jbar x + (ε : EReal) := by
  obtain ⟨α, hα, hI2⟩ := hI2
  intro N
  induction N with
  | zero =>
    intro ε hε
    obtain ⟨μ, hμ⟩ : ∃ μ : m.Selector, True := by
      choose f hf using m.U_nonempty
      exact ⟨⟨f, hf⟩, trivial⟩
    refine ⟨m.stationary μ, fun x => ?_⟩
    show m.Jbar x ≤ m.Jbar x + (ε : EReal)
    exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr hε.le)
  | succ N ih =>
    intro ε hε
    obtain ⟨π', hπ'⟩ := ih (ε / (2 * α)) (by positivity)
    have hne : ∀ y, m.T ((m.T)^[N] m.Jbar) y ≠ ⊥ := by
      intro y
      have h1 := aux_p2f_Jbar_le_iter m hI (N + 1) y
      rw [Function.iterate_succ_apply'] at h1
      intro hb
      rw [hb, le_bot_iff] at h1
      exact m.Jbar_ne_bot y h1
    obtain ⟨μ, hμ⟩ := aux_p2f_select m ((m.T)^[N] m.Jbar) hne (ε / 2) (by positivity)
    let π : m.Policy := fun k => Nat.casesOn k μ π'
    refine ⟨π, fun x => ?_⟩
    rw [aux_p2f_comp_succ m π N m.Jbar, Function.iterate_succ_apply']
    have hshift : (fun k => π (k + 1)) = π' := rfl
    have hπ0 : π 0 = μ := rfl
    rw [hshift, hπ0]
    have hJ : m.Jbar ≤ (m.T)^[N] m.Jbar := aux_p2f_Jbar_le_iter m hI N
    have step1 : m.Tmu μ (m.comp π' N m.Jbar) x ≤
        m.Tmu μ (fun y => (m.T)^[N] m.Jbar y + ((ε / (2 * α) : ℝ) : EReal)) x :=
      aux_p2f_Tmu_mono m μ (fun y => hπ' y) x
    have step2 := (hI2 (ε / (2 * α)) (by positivity) ((m.T)^[N] m.Jbar) hJ x (μ.1 x) (μ.2 x)).2
    have hαr : α * (ε / (2 * α)) = ε / 2 := by field_simp
    rw [hαr] at step2
    have step3 := hμ x
    calc m.Tmu μ (m.comp π' N m.Jbar) x
        ≤ m.Tmu μ (fun y => (m.T)^[N] m.Jbar y + ((ε / (2 * α) : ℝ) : EReal)) x := step1
      _ ≤ m.Tmu μ ((m.T)^[N] m.Jbar) x + ((ε / 2 : ℝ) : EReal) := step2
      _ ≤ m.T ((m.T)^[N] m.Jbar) x + ((ε / 2 : ℝ) : EReal) + ((ε / 2 : ℝ) : EReal) := by
          gcongr
      _ = m.T ((m.T)^[N] m.Jbar) x + (ε : EReal) := by
          rw [add_assoc, ← EReal.coe_add]
          congr 2
          ring

theorem aux_p2f_le_of_forall {a b : EReal} (h : ∀ ε : ℝ, 0 < ε → a ≤ b + (ε : EReal)) :
    a ≤ b := by
  induction b using EReal.rec with
  | bot =>
    have := h 1 one_pos
    simpa using this
  | top => exact le_top
  | coe r =>
    apply EReal.le_of_forall_lt_iff_le.mp
    intro z hz
    have hz' : r < z := EReal.coe_lt_coe_iff.mp hz
    have := h (z - r) (by linarith)
    rw [← EReal.coe_add] at this
    simpa using this

end Model

end MonotoneDP.Increase

open MonotoneDP.Increase

theorem solution {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ∀ N : ℕ, 1 ≤ N → m.JN N = (m.T)^[N] m.Jbar := by
  intro N _
  funext x
  apply le_antisymm
  · apply Model.aux_p2f_le_of_forall
    intro ε hε
    obtain ⟨π, hπ⟩ := Model.aux_p2f_main m hI hI2 N ε hε
    exact iInf_le_of_le π (hπ x)
  · exact le_iInf fun π => Model.aux_p2f_iter_le_comp m π N m.Jbar x
