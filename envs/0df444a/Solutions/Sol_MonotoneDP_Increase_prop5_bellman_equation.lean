-- Prove2me | solution 1 for MonotoneDP.Increase.prop5_bellman_equation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:10:00.046557+00:00
-- url     : https://prove2.me/submissions/bd3e13e0-724a-4cb2-bcd7-137e7c683efa

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

theorem aux_p5_Tmu_mono (μ : m.Selector) {J J' : S → EReal} (h : J ≤ J') :
    m.Tmu μ J ≤ m.Tmu μ J' := fun x => m.mono x (μ.1 x) (μ.2 x) J J' h

theorem aux_p5_T_mono {J J' : S → EReal} (h : J ≤ J') : m.T J ≤ m.T J' := by
  intro x
  exact iInf₂_mono fun u hu => m.mono x u hu J J' h

theorem aux_p5_comp_mono (π : m.Policy) (N : ℕ) : ∀ {J J' : S → EReal}, J ≤ J' →
    m.comp π N J ≤ m.comp π N J' := by
  induction N with
  | zero => intro J J' h; exact h
  | succ N ih => intro J J' h; exact ih (m.aux_p5_Tmu_mono (π N) h)

theorem aux_p5_comp_succ (π : m.Policy) (N : ℕ) : ∀ J : S → EReal,
    m.comp π (N+1) J = m.Tmu (π 0) (m.comp (fun k => π (k+1)) N J) := by
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show m.comp π (N+1) (m.Tmu (π (N+1)) J) = _
    rw [ih]
    rfl

theorem aux_p5_comp_le_succ (hI : m.AssumptionI) (π : m.Policy) (N : ℕ) :
    m.comp π N m.Jbar ≤ m.comp π (N+1) m.Jbar := by
  show m.comp π N m.Jbar ≤ m.comp π N (m.Tmu (π N) m.Jbar)
  apply m.aux_p5_comp_mono
  intro x
  exact hI x _ ((π N).2 x)

theorem aux_p5_comp_monotone (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    Monotone (fun N => m.comp π N m.Jbar x) :=
  monotone_nat_of_le_succ fun N => m.aux_p5_comp_le_succ hI π N x

theorem aux_p5_Jpi_eq (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x = ⨆ N, m.comp π N m.Jbar x :=
  (tendsto_atTop_iSup (m.aux_p5_comp_monotone hI π x)).limUnder_eq

theorem aux_p5_Jbar_le_Jpi (hI : m.AssumptionI) (π : m.Policy) : m.Jbar ≤ m.Jpi π := by
  intro x
  rw [m.aux_p5_Jpi_eq hI π x]
  exact le_iSup (fun N => m.comp π N m.Jbar x) 0

theorem aux_p5_Jbar_le_Jstar (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar := by
  intro x
  exact le_iInf fun π => m.aux_p5_Jbar_le_Jpi hI π x

theorem aux_p5_Jpi_shift (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (π : m.Policy) (x : S) :
    m.Jpi π x = m.H x ((π 0).1 x) (m.Jpi (fun k => π (k+1))) := by
  set π' : m.Policy := fun k => π (k+1) with hπ'
  have h1 := hI1 (fun k => m.comp π' k m.Jbar)
    (fun k y => m.aux_p5_comp_monotone hI π' y (Nat.zero_le k))
    (fun k => m.aux_p5_comp_le_succ hI π' k) x ((π 0).1 x) ((π 0).2 x)
  have h2 : (fun y => limUnder atTop (fun k => m.comp π' k m.Jbar y)) = m.Jpi π' := rfl
  rw [h2] at h1
  rw [← h1]
  have ht : Tendsto (fun N => m.comp π N m.Jbar x) atTop (𝓝 (⨆ N, m.comp π N m.Jbar x)) :=
    tendsto_atTop_iSup (m.aux_p5_comp_monotone hI π x)
  have ht' : Tendsto (fun k => m.H x ((π 0).1 x) (m.comp π' k m.Jbar)) atTop
      (𝓝 (⨆ N, m.comp π N m.Jbar x)) := by
    have := ht.comp (tendsto_add_atTop_nat 1)
    refine this.congr ?_
    intro k
    simp only [Function.comp]
    rw [m.aux_p5_comp_succ π k]
    rfl
  rw [ht'.limUnder_eq, m.aux_p5_Jpi_eq hI π x]

theorem aux_p5_T_Jstar_le (hI : m.AssumptionI) (hI1 : m.AssumptionI1) :
    m.T m.Jstar ≤ m.Jstar := by
  intro x
  refine le_iInf fun π => ?_
  rw [m.aux_p5_Jpi_shift hI hI1 π x]
  calc m.T m.Jstar x ≤ m.H x ((π 0).1 x) m.Jstar :=
        iInf₂_le (f := fun u _ => m.H x u m.Jstar) _ ((π 0).2 x)
    _ ≤ _ := m.mono x _ ((π 0).2 x) _ _ (fun y => iInf_le (fun π => m.Jpi π y) _)

theorem aux_p5_selector (J' : S → EReal) (hJ' : m.Jbar ≤ J') (hT : m.T J' ≤ J') (δ : ℝ)
    (hδ : 0 < δ) : ∃ μ : m.Selector, ∀ x, m.H x (μ.1 x) J' ≤ J' x + (δ : EReal) := by
  have h : ∀ x, ∃ u ∈ m.U x, m.H x u J' ≤ J' x + (δ : EReal) := by
    intro x
    by_cases htop : J' x = ⊤
    · obtain ⟨u, hu⟩ := m.U_nonempty x
      refine ⟨u, hu, ?_⟩
      rw [htop, EReal.top_add_coe]
      exact le_top
    · have hbot : J' x ≠ ⊥ := by
        intro hb
        have := hJ' x
        rw [hb, le_bot_iff] at this
        exact m.Jbar_ne_bot x this
      have hlt : J' x < J' x + (δ : EReal) := by
        obtain ⟨a, ha⟩ : ∃ a : ℝ, J' x = a := ⟨(J' x).toReal, (EReal.coe_toReal htop hbot).symm⟩
        rw [ha, ← EReal.coe_add]
        exact_mod_cast (by linarith : a < a + δ)
      have hlt2 : m.T J' x < J' x + δ := lt_of_le_of_lt (hT x) hlt
      simp only [T, iInf_lt_iff] at hlt2
      obtain ⟨u, hu, hlt'⟩ := hlt2
      exact ⟨u, hu, hlt'.le⟩
  choose f hf using h
  exact ⟨⟨f, fun x => (hf x).1⟩, fun x => (hf x).2⟩

theorem aux_p5_min (hI : m.AssumptionI) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) (J' : S → EReal)
    (hJ' : m.Jbar ≤ J') (hT : m.T J' ≤ J') : m.Jstar ≤ J' := by
  obtain ⟨α, hα, hI2⟩ := hI2
  have key : ∀ ε : ℝ, 0 < ε → m.Jstar ≤ fun y => J' y + (ε : EReal) := by
    intro ε hε
    set c : ℕ → ℝ := fun N => ε / (2 * α) ^ N with hcdef
    have hc : ∀ N, 0 < c N := fun N => by
      simp only [hcdef]
      positivity
    have hrec : ∀ N, c N / 2 + α * c (N+1) = c N := by
      intro N
      simp only [hcdef]
      rw [pow_succ]
      field_simp
      ring
    choose μ hμ using fun N => m.aux_p5_selector J' hJ' hT (c N / 2) (by linarith [hc N])
    let π : m.Policy := μ
    have claim : ∀ N, ∀ J : S → EReal, J ≤ (fun y => J' y + (c N : EReal)) →
        m.comp π N J ≤ fun y => J' y + (c 0 : EReal) := by
      intro N
      induction N with
      | zero => intro J h; exact h
      | succ N ih =>
        intro J h
        apply ih
        intro y
        calc m.Tmu (π N) J y = m.H y ((μ N).1 y) J := rfl
          _ ≤ m.H y ((μ N).1 y) (fun z => J' z + (c (N+1) : EReal)) :=
              m.mono y _ ((μ N).2 y) _ _ h
          _ ≤ m.H y ((μ N).1 y) J' + ((α * c (N+1) : ℝ) : EReal) :=
              (hI2 (c (N+1)) (hc _) J' hJ' y _ ((μ N).2 y)).2
          _ ≤ (J' y + ((c N / 2 : ℝ) : EReal)) + ((α * c (N+1) : ℝ) : EReal) := by
              gcongr
              exact hμ N y
          _ = J' y + ((c N / 2 + α * c (N+1) : ℝ) : EReal) := by
              rw [add_assoc, EReal.coe_add]
          _ = J' y + (c N : EReal) := by rw [hrec N]
    intro x
    have hc0 : c 0 = ε := by simp [hcdef]
    calc m.Jstar x ≤ m.Jpi π x := iInf_le (fun π => m.Jpi π x) π
      _ = ⨆ N, m.comp π N m.Jbar x := m.aux_p5_Jpi_eq hI π x
      _ ≤ J' x + (ε : EReal) := by
          refine iSup_le fun N => ?_
          have h1 : m.comp π N m.Jbar x ≤ m.comp π N J' x := m.aux_p5_comp_mono π N hJ' x
          have h2 : m.comp π N J' x ≤ J' x + (c 0 : EReal) := by
            refine claim N J' ?_ x
            intro y
            exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (hc N).le)
          rw [hc0] at h2
          exact h1.trans h2
  intro x
  by_cases htop : J' x = ⊤
  · rw [htop]; exact le_top
  have hbot : J' x ≠ ⊥ := by
    intro hb
    have := hJ' x
    rw [hb, le_bot_iff] at this
    exact m.Jbar_ne_bot x this
  obtain ⟨a, ha⟩ : ∃ a : ℝ, J' x = a := ⟨(J' x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  rw [ha]
  refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
  have hz' : a < z := by exact_mod_cast hz
  have := key (z - a) (by linarith) x
  simp only at this
  rw [ha, ← EReal.coe_add] at this
  simpa using this

end Model

end MonotoneDP.Increase

open MonotoneDP.Increase

theorem solution {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    m.Jstar = m.T m.Jstar ∧
      ∀ J' : S → EReal, m.Jbar ≤ J' → m.T J' ≤ J' → m.Jstar ≤ J' := by
  refine ⟨?_, fun J' hJ' hT => m.aux_p5_min hI hI2 J' hJ' hT⟩
  refine le_antisymm ?_ (m.aux_p5_T_Jstar_le hI hI1)
  apply m.aux_p5_min hI hI2
  · intro x
    refine le_iInf₂ fun u hu => ?_
    exact (hI x u hu).trans (m.mono x u hu _ _ (m.aux_p5_Jbar_le_Jstar hI))
  · exact m.aux_p5_T_mono (m.aux_p5_T_Jstar_le hI hI1)
