-- Prove2me | solution 1 for MonotoneDP.Increase.prop4_eps_optimal_policy
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:54:59.817064+00:00
-- url     : https://prove2.me/submissions/ce98bb63-94ac-48ca-bde9-d4f32628dfe0

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

theorem aux_p4e_comp_mono (π : m.Policy) :
    ∀ N (J J' : S → EReal), J ≤ J' → m.comp π N J ≤ m.comp π N J' := by
  intro N
  induction N with
  | zero => intro J J' h; exact h
  | succ N ih =>
    intro J J' h
    show m.comp π N (m.Tmu (π N) J) ≤ m.comp π N (m.Tmu (π N) J')
    apply ih
    intro x
    exact m.mono x _ ((π N).2 x) J J' h

theorem aux_p4e_Tmu_ge (hI : m.AssumptionI) (μ : m.Selector) (J : S → EReal)
    (hJ : m.Jbar ≤ J) : m.Jbar ≤ m.Tmu μ J := by
  intro x
  exact le_trans (hI x _ (μ.2 x)) (m.mono x _ (μ.2 x) _ _ hJ)

theorem aux_p4e_comp_ge (hI : m.AssumptionI) (π : m.Policy) :
    ∀ N (J : S → EReal), m.Jbar ≤ J → m.Jbar ≤ m.comp π N J := by
  intro N
  induction N with
  | zero => intro J h; exact h
  | succ N ih =>
    intro J h
    exact ih _ (aux_p4e_Tmu_ge m hI (π N) J h)

theorem aux_p4e_comp_succ_mono (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    Monotone (fun N => m.comp π N m.Jbar x) := by
  apply monotone_nat_of_le_succ
  intro N
  show m.comp π N m.Jbar x ≤ m.comp π N (m.Tmu (π N) m.Jbar) x
  exact aux_p4e_comp_mono m π N _ _ (aux_p4e_Tmu_ge m hI (π N) _ le_rfl) x

theorem aux_p4e_Jpi_eq_iSup (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x = ⨆ N, m.comp π N m.Jbar x :=
  (tendsto_atTop_iSup (aux_p4e_comp_succ_mono m hI π x)).limUnder_eq

theorem aux_p4e_Jbar_le_Jpi (hI : m.AssumptionI) (π : m.Policy) : m.Jbar ≤ m.Jpi π := by
  intro x
  rw [aux_p4e_Jpi_eq_iSup m hI π x]
  exact le_iSup_of_le 0 le_rfl

theorem aux_p4e_Jbar_le_Jstar (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar := by
  intro x
  exact le_iInf fun π => aux_p4e_Jbar_le_Jpi m hI π x

theorem aux_p4e_comp_succ' (π : m.Policy) :
    ∀ N (J : S → EReal), m.comp π (N + 1) J =
      m.Tmu (π 0) (m.comp (fun k => π (k + 1)) N J) := by
  intro N
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show m.comp π (N + 1) (m.Tmu (π (N + 1)) J) = _
    rw [ih]
    rfl

theorem aux_p4e_Jpi_eq_H (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (π : m.Policy) (x : S) :
    m.Jpi π x = m.H x ((π 0).1 x) (m.Jpi (fun k => π (k + 1))) := by
  set g : ℕ → EReal := fun k => m.comp π (k + 1) m.Jbar x with hg
  have hgmono : Monotone g := fun a b hab =>
    aux_p4e_comp_succ_mono m hI π x (Nat.succ_le_succ hab)
  have ht : Tendsto g atTop (𝓝 (⨆ k, g k)) := tendsto_atTop_iSup hgmono
  have hI1' := hI1 (fun k => m.comp (fun k => π (k + 1)) k m.Jbar)
    (fun k => aux_p4e_comp_ge m hI _ k _ le_rfl)
    (fun k y => aux_p4e_comp_succ_mono m hI (fun k => π (k + 1)) y (Nat.le_succ k))
    x ((π 0).1 x) ((π 0).2 x)
  have hgeq : g = fun k => m.H x ((π 0).1 x) (m.comp (fun k => π (k + 1)) k m.Jbar) := by
    funext k
    simp only [hg]
    rw [aux_p4e_comp_succ']
    rfl
  have hlim : limUnder atTop g = m.H x ((π 0).1 x) (m.Jpi (fun k => π (k + 1))) := by
    rw [hgeq]
    exact hI1'
  rw [ht.limUnder_eq] at hlim
  rw [hlim] at ht
  have ht2 : Tendsto (fun N => m.comp π N m.Jbar x) atTop
      (𝓝 (m.H x ((π 0).1 x) (m.Jpi (fun k => π (k + 1))))) :=
    (tendsto_add_atTop_iff_nat 1).mp ht
  exact ht2.limUnder_eq

theorem aux_p4e_select (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ : m.Selector, ∀ x, m.Tmu μ m.Jstar x ≤ m.Jstar x + (δ : EReal) := by
  have key : ∀ x, ∃ u, u ∈ m.U x ∧ m.H x u m.Jstar ≤ m.Jstar x + (δ : EReal) := by
    intro x
    by_cases htop : m.Jstar x = ⊤
    · obtain ⟨u, hu⟩ := m.U_nonempty x
      refine ⟨u, hu, ?_⟩
      rw [htop, EReal.top_add_coe]
      exact le_top
    · have hbot : m.Jstar x ≠ ⊥ := by
        intro h
        have := aux_p4e_Jbar_le_Jstar m hI x
        rw [h, le_bot_iff] at this
        exact m.Jbar_ne_bot x this
      have hlt : m.Jstar x < m.Jstar x + (δ : EReal) := by
        rw [← EReal.coe_toReal htop hbot, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        linarith
      have hlt' : (⨅ π : m.Policy, m.Jpi π x) < m.Jstar x + (δ : EReal) := hlt
      obtain ⟨π, hπ⟩ := iInf_lt_iff.mp hlt'
      refine ⟨(π 0).1 x, (π 0).2 x, ?_⟩
      have h1 : m.H x ((π 0).1 x) m.Jstar ≤ m.H x ((π 0).1 x) (m.Jpi (fun k => π (k + 1))) :=
        m.mono x _ ((π 0).2 x) _ _ (fun y => iInf_le (fun π => m.Jpi π y) _)
      rw [← aux_p4e_Jpi_eq_H m hI hI1 π x] at h1
      exact le_trans h1 hπ.le
  choose f hfU hf using key
  exact ⟨⟨f, hfU⟩, hf⟩

theorem aux_p4e_comp_add (hI : m.AssumptionI) (α : ℝ) (hI2 : m.AssumptionI2 α)
    (π : m.Policy) : ∀ N (J : S → EReal) (r : ℝ), m.Jbar ≤ J → 0 < r →
      m.comp π N (fun y => J y + (r : EReal)) ≤
        fun y => m.comp π N J y + ((α ^ N * r : ℝ) : EReal) := by
  intro N
  induction N with
  | zero =>
    intro J r _ _ y
    simp [comp]
  | succ N ih =>
    intro J r hJ hr
    show m.comp π N (m.Tmu (π N) (fun y => J y + (r : EReal))) ≤
      fun y => m.comp π N (m.Tmu (π N) J) y + ((α ^ (N + 1) * r : ℝ) : EReal)
    have h1 : m.Tmu (π N) (fun y => J y + (r : EReal)) ≤
        fun y => m.Tmu (π N) J y + ((α * r : ℝ) : EReal) := by
      intro x
      exact ((hI2.2 r hr J hJ x _ ((π N).2 x)).2)
    have h2 := aux_p4e_comp_mono m π N _ _ h1
    have h3 := ih (m.Tmu (π N) J) (α * r) (aux_p4e_Tmu_ge m hI (π N) J hJ)
      (mul_pos hI2.1 hr)
    have heq : α ^ N * (α * r) = α ^ (N + 1) * r := by ring
    rw [heq] at h3
    exact le_trans h2 h3

theorem aux_p4e_comp_bound (hI : m.AssumptionI) (α : ℝ) (hI2 : m.AssumptionI2 α)
    (π : m.Policy) (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k)
    (hsel : ∀ k x, m.Tmu (π k) m.Jstar x ≤ m.Jstar x + (δ k : EReal))
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbs : ∀ N, b N + α ^ N * δ N ≤ b (N + 1)) :
    ∀ N, m.comp π N m.Jstar ≤ fun x => m.Jstar x + (b N : EReal) := by
  intro N
  induction N with
  | zero =>
    intro x
    simp [comp, hb0]
  | succ N ih =>
    show m.comp π N (m.Tmu (π N) m.Jstar) ≤ _
    have h1 := aux_p4e_comp_mono m π N _ _ (fun x => hsel N x)
    have h2 := aux_p4e_comp_add m hI α hI2 π N m.Jstar (δ N)
      (aux_p4e_Jbar_le_Jstar m hI) (hδ N)
    intro x
    calc m.comp π N (m.Tmu (π N) m.Jstar) x
        ≤ m.comp π N (fun y => m.Jstar y + (δ N : EReal)) x := h1 x
      _ ≤ m.comp π N m.Jstar x + ((α ^ N * δ N : ℝ) : EReal) := h2 x
      _ ≤ (m.Jstar x + (b N : EReal)) + ((α ^ N * δ N : ℝ) : EReal) := by
          gcongr
          exact ih x
      _ = m.Jstar x + ((b N + α ^ N * δ N : ℝ) : EReal) := by
          rw [add_assoc, EReal.coe_add]
      _ ≤ m.Jstar x + (b (N + 1) : EReal) := by
          gcongr
          exact hbs N

theorem aux_p4e_final (hI : m.AssumptionI) (π : m.Policy) (b : ℕ → ℝ) (ε : ℝ)
    (hb : ∀ N, m.comp π N m.Jstar ≤ fun x => m.Jstar x + (b N : EReal))
    (hbε : ∀ N, b N ≤ ε) :
    m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal) := by
  intro x
  rw [aux_p4e_Jpi_eq_iSup m hI π x]
  apply iSup_le
  intro N
  calc m.comp π N m.Jbar x ≤ m.comp π N m.Jstar x :=
        aux_p4e_comp_mono m π N _ _ (aux_p4e_Jbar_le_Jstar m hI) x
    _ ≤ m.Jstar x + (b N : EReal) := hb N x
    _ ≤ m.Jstar x + (ε : EReal) := by
        gcongr
        exact hbε N

end Model

end MonotoneDP.Increase

open MonotoneDP.Increase

theorem solution {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (α : ℝ) (hI2 : m.AssumptionI2 α) :
    (∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
        m.Jstar ≤ m.Jpi π ∧ m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal)) ∧
    (α < 1 → ∀ ε : ℝ, 0 < ε → ∃ μ : m.Selector,
        m.Jstar ≤ m.Jmu μ ∧ m.Jmu μ ≤ fun x => m.Jstar x + (ε : EReal)) := by
  have hα := hI2.1
  constructor
  · intro ε hε
    let δ : ℕ → ℝ := fun k => ε * (1 / 2) ^ (k + 1) / α ^ k
    have hδ : ∀ k, 0 < δ k := fun k => by
      simp only [δ]
      positivity
    have hsel : ∀ k, ∃ μ : m.Selector, ∀ x, m.Tmu μ m.Jstar x ≤ m.Jstar x + (δ k : EReal) :=
      fun k => Model.aux_p4e_select m hI hI1 (δ k) (hδ k)
    choose π hπ using hsel
    refine ⟨π, fun x => iInf_le (fun π => m.Jpi π x) π, ?_⟩
    apply Model.aux_p4e_final m hI π (fun N => ε * (1 - (1 / 2) ^ N)) ε
    · apply Model.aux_p4e_comp_bound m hI α hI2 π δ hδ hπ
      · simp
      · intro N
        simp only [δ]
        have hαN : α ^ N ≠ 0 := pow_ne_zero _ hα.ne'
        rw [le_iff_eq_or_lt]
        left
        field_simp
        ring
    · intro N
      have : (0 : ℝ) < (1 / 2) ^ N := by positivity
      nlinarith
  · intro hα1 ε hε
    have hδ : 0 < ε * (1 - α) := mul_pos hε (by linarith)
    obtain ⟨μ, hμ⟩ := Model.aux_p4e_select m hI hI1 (ε * (1 - α)) hδ
    refine ⟨μ, fun x => iInf_le (fun π => m.Jpi π x) (m.stationary μ), ?_⟩
    apply Model.aux_p4e_final m hI (m.stationary μ) (fun N => ε * (1 - α ^ N)) ε
    · apply Model.aux_p4e_comp_bound m hI α hI2 (m.stationary μ) (fun _ => ε * (1 - α))
        (fun _ => hδ) (fun _ x => hμ x)
      · simp
      · intro N
        rw [le_iff_eq_or_lt]
        left
        ring
    · intro N
      have : (0 : ℝ) < α ^ N := by positivity
      nlinarith
