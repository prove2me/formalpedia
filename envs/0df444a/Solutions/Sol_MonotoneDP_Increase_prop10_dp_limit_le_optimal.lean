-- Prove2me | solution 1 for MonotoneDP.Increase.prop10_dp_limit_le_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T08:06:30.600975+00:00
-- url     : https://prove2.me/submissions/751671a2-6317-48af-b441-0cb2ecfe13aa

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

theorem aux_p10_Tmu_mono (μ : m.Selector) : Monotone (m.Tmu μ) := by
  intro J J' h x
  exact m.mono x (μ.1 x) (μ.2 x) J J' h

theorem aux_p10_T_mono : Monotone m.T := by
  intro J J' h x
  unfold T
  exact iInf₂_mono (fun u hu => m.mono x u hu J J' h)

theorem aux_p10_comp_mono (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => intro J J' h; simpa [comp] using h
  | succ N ih =>
    intro J J' h
    simp only [comp]
    exact ih (m.aux_p10_Tmu_mono (π N) h)

theorem aux_p10_T_le_Tmu (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J := by
  intro x
  exact iInf₂_le (μ.1 x) (μ.2 x)

theorem aux_p10_iter_le_comp (π : m.Policy) (N : ℕ) : ∀ J, (m.T)^[N] J ≤ m.comp π N J := by
  induction N with
  | zero => intro J; simp [comp]
  | succ N ih =>
    intro J
    rw [Function.iterate_succ_apply]
    simp only [comp]
    calc (m.T)^[N] (m.T J) ≤ (m.T)^[N] (m.Tmu (π N) J) :=
          (m.aux_p10_T_mono.iterate N) (m.aux_p10_T_le_Tmu _ _)
      _ ≤ _ := ih _

/-- The shifted policy `{μ₁, μ₂, …}`. -/
def aux_p10_shift (π : m.Policy) : m.Policy := fun k => π (k + 1)

theorem aux_p10_comp_succ (π : m.Policy) (N : ℕ) : ∀ J,
    m.comp π (N + 1) J = m.Tmu (π 0) (m.comp (m.aux_p10_shift π) N J) := by
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show m.comp π (N + 1) (m.Tmu (π (N + 1)) J) = _
    rw [ih]
    rfl

variable {m}

theorem aux_p10_Jbar_le_Tmu (hI : m.AssumptionI) (μ : m.Selector) :
    m.Jbar ≤ m.Tmu μ m.Jbar :=
  fun x => hI x (μ.1 x) (μ.2 x)

theorem aux_p10_Jbar_le_T (hI : m.AssumptionI) : m.Jbar ≤ m.T m.Jbar :=
  fun x => le_iInf₂ (fun u hu => hI x u hu)

theorem aux_p10_comp_Jbar_mono (hI : m.AssumptionI) (π : m.Policy) :
    Monotone (fun N => m.comp π N m.Jbar) := by
  apply monotone_nat_of_le_succ
  intro N
  show m.comp π N m.Jbar ≤ m.comp π N (m.Tmu (π N) m.Jbar)
  exact m.aux_p10_comp_mono π N (aux_p10_Jbar_le_Tmu hI _)

theorem aux_p10_Jpi_eq (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x = ⨆ N, m.comp π N m.Jbar x := by
  unfold Jpi
  apply Tendsto.limUnder_eq
  apply tendsto_atTop_iSup
  intro a b hab
  exact aux_p10_comp_Jbar_mono hI π hab x

theorem aux_p10_iter_mono (hI : m.AssumptionI) : Monotone (fun N => (m.T)^[N] m.Jbar) :=
  Monotone.monotone_iterate_of_le_map m.aux_p10_T_mono (aux_p10_Jbar_le_T hI)

theorem aux_p10_Jinf_eq (hI : m.AssumptionI) (x : S) :
    m.Jinf x = ⨆ N, (m.T)^[N] m.Jbar x := by
  unfold Jinf
  apply Tendsto.limUnder_eq
  apply tendsto_atTop_iSup
  intro a b hab
  exact aux_p10_iter_mono hI hab x

theorem aux_p10_Jbar_le_Jpi (hI : m.AssumptionI) (π : m.Policy) : m.Jbar ≤ m.Jpi π := by
  intro x
  rw [aux_p10_Jpi_eq hI]
  exact le_iSup (fun N => m.comp π N m.Jbar x) 0

theorem aux_p10_Jbar_le_Jstar (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar :=
  fun x => le_iInf (fun π => aux_p10_Jbar_le_Jpi hI π x)

theorem aux_p10_Jbar_le_Jinf (hI : m.AssumptionI) : m.Jbar ≤ m.Jinf := by
  intro x
  rw [aux_p10_Jinf_eq hI]
  exact le_iSup (fun N => (m.T)^[N] m.Jbar x) 0

theorem aux_p10_Jinf_le_Jstar (hI : m.AssumptionI) : m.Jinf ≤ m.Jstar := by
  intro x
  rw [aux_p10_Jinf_eq hI]
  refine iSup_le (fun N => le_iInf (fun π => ?_))
  rw [aux_p10_Jpi_eq hI]
  exact le_trans (m.aux_p10_iter_le_comp π N m.Jbar x)
    (le_iSup (fun N => m.comp π N m.Jbar x) N)

theorem aux_p10_Jinf_le_TJinf (hI : m.AssumptionI) : m.Jinf ≤ m.T m.Jinf := by
  intro x
  rw [aux_p10_Jinf_eq hI]
  refine iSup_le (fun N => ?_)
  have hle : (m.T)^[N] m.Jbar ≤ m.Jinf := by
    intro y
    rw [aux_p10_Jinf_eq hI]
    exact le_iSup (fun N => (m.T)^[N] m.Jbar y) N
  calc (m.T)^[N] m.Jbar x ≤ (m.T)^[N + 1] m.Jbar x := aux_p10_iter_mono hI (Nat.le_succ N) x
    _ = m.T ((m.T)^[N] m.Jbar) x := by rw [Function.iterate_succ_apply']
    _ ≤ m.T m.Jinf x := m.aux_p10_T_mono hle x

theorem aux_p10_TJstar_le (hI : m.AssumptionI) (hI1 : m.AssumptionI1) :
    m.T m.Jstar ≤ m.Jstar := by
  intro x
  refine le_iInf (fun π => ?_)
  set π' := m.aux_p10_shift π with hπ'
  set u := (π 0).1 x with hu_def
  have hu : u ∈ m.U x := (π 0).2 x
  have hmono := aux_p10_comp_Jbar_mono hI π'
  have hlim := hI1 (fun k => m.comp π' k m.Jbar) (fun k => hmono (Nat.zero_le k))
    (fun k => hmono (Nat.le_succ k)) x u hu
  have hsup : limUnder atTop (fun k => m.H x u (m.comp π' k m.Jbar)) =
      ⨆ k, m.H x u (m.comp π' k m.Jbar) := by
    apply Tendsto.limUnder_eq
    apply tendsto_atTop_iSup
    intro a b hab
    exact m.mono x u hu _ _ (hmono hab)
  calc m.T m.Jstar x ≤ m.H x u m.Jstar := iInf₂_le u hu
    _ ≤ m.H x u (m.Jpi π') := m.mono x u hu _ _ (fun y => iInf_le (fun π => m.Jpi π y) π')
    _ = ⨆ k, m.H x u (m.comp π' k m.Jbar) := by rw [← hsup, hlim]; rfl
    _ ≤ m.Jpi π x := by
      rw [aux_p10_Jpi_eq hI]
      refine iSup_le (fun k => ?_)
      have : m.comp π (k + 1) m.Jbar x = m.H x u (m.comp π' k m.Jbar) := by
        rw [aux_p10_comp_succ]; rfl
      rw [← this]
      exact le_iSup (fun N => m.comp π N m.Jbar x) (k + 1)

theorem aux_p10_min (hI : m.AssumptionI) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) (J' : S → EReal)
    (hbar : m.Jbar ≤ J') (hT : m.T J' ≤ J') : m.Jstar ≤ J' := by
  obtain ⟨α, hα, hI2⟩ := hI2
  intro x
  have key : ∀ ε : ℝ, 0 < ε → m.Jstar x ≤ J' x + (ε : EReal) := by
    intro ε hε
    set a : ℕ → ℝ := fun k => ε / (α + 1) ^ k with ha
    set δ : ℕ → ℝ := fun k => ε / (α + 1) ^ (k + 1) with hδ
    have hapos : ∀ k, 0 < a k := fun k => by simp only [ha]; positivity
    have hδpos : ∀ k, 0 < δ k := fun k => by simp only [hδ]; positivity
    have hrel : ∀ k, δ k + α * a (k + 1) = a k := by
      intro k
      simp only [ha, hδ]
      have h1 : (0 : ℝ) < α + 1 := by linarith
      field_simp
      ring
    have hex : ∀ k y, ∃ u ∈ m.U y, m.H y u J' ≤ J' y + (δ k : EReal) := by
      intro k y
      by_cases htop : J' y = ⊤
      · obtain ⟨u, hu⟩ := m.U_nonempty y
        exact ⟨u, hu, by rw [htop, EReal.top_add_coe]; exact le_top⟩
      · have hbot : J' y ≠ ⊥ := ne_bot_of_le_ne_bot (m.Jbar_ne_bot y) (hbar y)
        have hlt0 : J' y < J' y + (δ k : EReal) := by
          rw [← EReal.coe_toReal htop hbot, ← EReal.coe_add]
          exact_mod_cast (by linarith [hδpos k] : (J' y).toReal < (J' y).toReal + δ k)
        have hlt : m.T J' y < J' y + (δ k : EReal) := lt_of_le_of_lt (hT y) hlt0
        obtain ⟨u, hu, h⟩ : ∃ u ∈ m.U y, m.H y u J' < J' y + (δ k : EReal) := by
          simpa [T, iInf_lt_iff] using hlt
        exact ⟨u, hu, h.le⟩
    choose f hfU hfH using hex
    let π : m.Policy := fun k => ⟨f k, hfU k⟩
    have hstep : ∀ k, m.Tmu (π k) (fun y => J' y + (a (k + 1) : EReal)) ≤
        fun y => J' y + (a k : EReal) := by
      intro k y
      have h1 := (hI2 (a (k + 1)) (hapos _) J' hbar y (f k y) (hfU k y)).2
      calc m.Tmu (π k) (fun y => J' y + (a (k + 1) : EReal)) y
          = m.H y (f k y) (fun y => J' y + (a (k + 1) : EReal)) := rfl
        _ ≤ m.H y (f k y) J' + ((α * a (k + 1) : ℝ) : EReal) := h1
        _ ≤ (J' y + (δ k : EReal)) + ((α * a (k + 1) : ℝ) : EReal) := by
          gcongr
          exact hfH k y
        _ = J' y + (a k : EReal) := by rw [add_assoc, ← EReal.coe_add, hrel]
    have hind : ∀ N, m.comp π N (fun y => J' y + (a N : EReal)) ≤
        fun y => J' y + (a 0 : EReal) := by
      intro N
      induction N with
      | zero => exact le_refl _
      | succ N ih =>
        calc m.comp π (N + 1) (fun y => J' y + (a (N + 1) : EReal))
            = m.comp π N (m.Tmu (π N) (fun y => J' y + (a (N + 1) : EReal))) := rfl
          _ ≤ m.comp π N (fun y => J' y + (a N : EReal)) := m.aux_p10_comp_mono π N (hstep N)
          _ ≤ _ := ih
    have hJ'le : ∀ N, J' ≤ fun y => J' y + (a N : EReal) := by
      intro N y
      exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (hapos N).le)
    calc m.Jstar x ≤ m.Jpi π x := iInf_le (fun π => m.Jpi π x) π
      _ = ⨆ N, m.comp π N m.Jbar x := aux_p10_Jpi_eq hI π x
      _ ≤ J' x + (a 0 : EReal) := by
        refine iSup_le (fun N => ?_)
        exact (m.aux_p10_comp_mono π N (hbar.trans (hJ'le N))).trans (hind N) x
      _ = J' x + (ε : EReal) := by simp [ha]
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  have htop : J' x ≠ ⊤ := ne_top_of_lt hz
  have hbot : J' x ≠ ⊥ := ne_bot_of_le_ne_bot (m.Jbar_ne_bot x) (hbar x)
  have hz' : (J' x).toReal < z := by
    rw [← EReal.coe_toReal htop hbot] at hz
    exact_mod_cast hz
  have := key (z - (J' x).toReal) (by linarith)
  rw [← EReal.coe_toReal htop hbot, ← EReal.coe_add] at this
  simpa using this

theorem aux_p10_TJstar_eq (hI : m.AssumptionI) (hI1 : m.AssumptionI1)
    (hI2 : ∃ α : ℝ, m.AssumptionI2 α) : m.T m.Jstar = m.Jstar := by
  have h1 := aux_p10_TJstar_le hI hI1
  apply le_antisymm h1
  apply aux_p10_min hI hI2
  · exact (aux_p10_Jbar_le_T hI).trans (m.aux_p10_T_mono (aux_p10_Jbar_le_Jstar hI))
  · exact m.aux_p10_T_mono h1

end Model

end MonotoneDP.Increase

open MonotoneDP.Increase

theorem solution {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (m.Jinf ≤ m.T m.Jinf ∧ m.T m.Jinf ≤ m.T m.Jstar ∧ m.T m.Jstar = m.Jstar) ∧
      ((m.Jinf = m.T m.Jinf ∧ m.T m.Jinf = m.T m.Jstar ∧ m.T m.Jstar = m.Jstar) ↔
        m.Jinf = m.T m.Jinf) := by
  have hstar := Model.aux_p10_TJstar_eq hI hI1 hI2
  have hle := Model.aux_p10_Jinf_le_Jstar hI
  refine ⟨⟨Model.aux_p10_Jinf_le_TJinf hI, m.aux_p10_T_mono hle, hstar⟩, ?_⟩
  constructor
  · exact fun h => h.1
  · intro h
    have hge : m.Jstar ≤ m.Jinf :=
      Model.aux_p10_min hI hI2 m.Jinf (Model.aux_p10_Jbar_le_Jinf hI) (le_of_eq h.symm)
    have heq : m.Jinf = m.Jstar := le_antisymm hle hge
    exact ⟨h, by rw [heq], hstar⟩
