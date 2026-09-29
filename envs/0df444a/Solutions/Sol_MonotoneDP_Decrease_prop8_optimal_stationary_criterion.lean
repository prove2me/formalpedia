-- Prove2me | solution 1 for MonotoneDP.Decrease.prop8_optimal_stationary_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:02:25.727783+00:00
-- url     : https://prove2.me/submissions/9535c29a-9302-48f6-b70d-e8aa1d699ac3

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace MonotoneDP.Decrease

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

theorem aux_p8_monoT : Monotone m.T := by
  intro J J' h x
  exact iInf₂_mono fun u hu => m.mono x u hu J J' h

theorem aux_p8_monoTmu (μ : m.Selector) : Monotone (m.Tmu μ) := by
  intro J J' h x
  exact m.mono x (μ.1 x) (μ.2 x) J J' h

theorem aux_p8_T_le_Tmu (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J := by
  intro x
  exact iInf₂_le (μ.1 x) (μ.2 x)

theorem aux_p8_comp_mono (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => intro J J' h; exact h
  | succ N ih =>
    intro J J' h
    exact ih (m.aux_p8_monoTmu (π N) h)

theorem aux_p8_comp_succ (π : m.Policy) (N : ℕ) (J : S → EReal) :
    m.comp π (N + 1) J = m.Tmu (π 0) (m.comp (fun k => π (k + 1)) N J) := by
  induction N generalizing J with
  | zero => rfl
  | succ N ih =>
    show m.comp π (N + 1) (m.Tmu (π (N + 1)) J) = _
    rw [ih]
    rfl

theorem aux_p8_comp_anti (hD : m.AssumptionD) (π : m.Policy) (N : ℕ) :
    m.comp π (N + 1) m.Jbar ≤ m.comp π N m.Jbar := by
  show m.comp π N (m.Tmu (π N) m.Jbar) ≤ _
  apply m.aux_p8_comp_mono π N
  intro x
  exact hD x _ ((π N).2 x)

theorem aux_p8_tendsto (hD : m.AssumptionD) (π : m.Policy) (x : S) :
    Tendsto (fun N => m.comp π N m.Jbar x) atTop (𝓝 (m.Jpi π x)) := by
  have hanti : Antitone (fun N => m.comp π N m.Jbar x) :=
    antitone_nat_of_succ_le fun n => m.aux_p8_comp_anti hD π n x
  have h := tendsto_atTop_iInf hanti
  have : m.Jpi π x = ⨅ N, m.comp π N m.Jbar x := h.limUnder_eq
  rw [this]
  exact h

theorem aux_p8_Jpi_eq (hD : m.AssumptionD) (π : m.Policy) (x : S) :
    m.Jpi π x = ⨅ N, m.comp π N m.Jbar x :=
  (tendsto_atTop_iInf (antitone_nat_of_succ_le fun n => m.aux_p8_comp_anti hD π n x)).limUnder_eq

theorem aux_p8_comp_le_Jbar (hD : m.AssumptionD) (π : m.Policy) (N : ℕ) :
    m.comp π N m.Jbar ≤ m.Jbar := by
  induction N with
  | zero => exact le_rfl
  | succ N ih => exact (m.aux_p8_comp_anti hD π N).trans ih

theorem aux_p8_Jpi_shift (hD : m.AssumptionD) (hD1 : m.AssumptionD1) (π : m.Policy) :
    m.Jpi π = m.Tmu (π 0) (m.Jpi (fun k => π (k + 1))) := by
  funext x
  have h1 : Tendsto (fun N => m.comp π (N + 1) m.Jbar x) atTop (𝓝 (m.Jpi π x)) :=
    (tendsto_add_atTop_iff_nat 1).2 (m.aux_p8_tendsto hD π x)
  have h2 : (fun N => m.comp π (N + 1) m.Jbar x) =
      fun N => m.H x ((π 0).1 x) (m.comp (fun k => π (k + 1)) N m.Jbar) := by
    funext N
    rw [m.aux_p8_comp_succ]
    rfl
  rw [h2] at h1
  have h3 := hD1 (fun k => m.comp (fun k => π (k + 1)) k m.Jbar)
    (fun k => m.aux_p8_comp_le_Jbar hD _ k) (fun k => m.aux_p8_comp_anti hD _ k)
    x ((π 0).1 x) ((π 0).2 x)
  rw [h1.limUnder_eq] at h3
  exact h3

theorem aux_p8_Jmu_fixed (hD : m.AssumptionD) (hD1 : m.AssumptionD1) (μ : m.Selector) :
    m.Jmu μ = m.Tmu μ (m.Jmu μ) :=
  m.aux_p8_Jpi_shift hD hD1 (m.stationary μ)

theorem aux_p8_iter_le_comp (π : m.Policy) (N : ℕ) (J : S → EReal) :
    (m.T)^[N] J ≤ m.comp π N J := by
  induction N generalizing J with
  | zero => exact le_rfl
  | succ N ih =>
    show (m.T)^[N] (m.T J) ≤ m.comp π N (m.Tmu (π N) J)
    exact ((m.aux_p8_monoT.iterate N) (m.aux_p8_T_le_Tmu (π N) J)).trans (ih _)

theorem aux_p8_maximal (hD : m.AssumptionD) (J : S → EReal) (hJ : J ≤ m.Jbar)
    (hT : J ≤ m.T J) : J ≤ m.Jstar := by
  have hiter : ∀ N, J ≤ (m.T)^[N] J := by
    intro N
    induction N with
    | zero => exact le_rfl
    | succ N ih =>
      rw [Function.iterate_succ_apply']
      exact hT.trans (m.aux_p8_monoT ih)
  intro x
  refine le_iInf fun π => ?_
  rw [m.aux_p8_Jpi_eq hD π x]
  refine le_iInf fun N => ?_
  exact ((hiter N).trans ((m.aux_p8_iter_le_comp π N J).trans
    (m.aux_p8_comp_mono π N hJ))) x

end Model

end MonotoneDP.Decrease

open MonotoneDP.Decrease

theorem solution {S C : Type*} (m : Model S C)
    (hD : m.AssumptionD) (hD1 : m.AssumptionD1) (μ : m.Selector) :
    m.Jmu μ = m.Jstar ↔ m.Tmu μ (m.Jmu μ) = m.T (m.Jmu μ) := by
  classical
  have hfix := m.aux_p8_Jmu_fixed hD hD1 μ
  constructor
  · intro h
    funext x
    refine le_antisymm ?_ (m.aux_p8_T_le_Tmu μ _ x)
    rw [← hfix]
    refine le_iInf₂ fun u hu => ?_
    let μ' : m.Selector :=
      Subtype.mk (p := fun f : S → C => ∀ y, f y ∈ m.U y)
        (fun y => if y = x then u else μ.1 y)
        (fun y => by
          by_cases hy : y = x
          · subst hy; simpa using hu
          · simpa [hy] using μ.2 y)
    let π : m.Policy := fun k => match k with
      | 0 => μ'
      | _ + 1 => μ
    have hπ : m.Jpi π = m.Tmu μ' (m.Jmu μ) := m.aux_p8_Jpi_shift hD hD1 π
    have hle : m.Jstar x ≤ m.Jpi π x := iInf_le (fun π => m.Jpi π x) π
    rw [hπ] at hle
    have hμ' : m.Tmu μ' (m.Jmu μ) x = m.H x u (m.Jmu μ) := by
      show m.H x (if x = x then u else μ.1 x) (m.Jmu μ) = _
      simp
    rw [h]
    rw [hμ'] at hle
    rw [← h]
    rw [← h] at hle
    exact hle
  · intro h
    have hT : m.Jmu μ = m.T (m.Jmu μ) := hfix.trans h
    have hle : m.Jmu μ ≤ m.Jbar := by
      intro x
      rw [Model.Jmu, m.aux_p8_Jpi_eq hD]
      exact iInf_le (fun N => m.comp (m.stationary μ) N m.Jbar x) 0
    funext x
    refine le_antisymm ?_ (iInf_le (fun π => m.Jpi π x) (m.stationary μ))
    exact m.aux_p8_maximal hD _ hle hT.le x
