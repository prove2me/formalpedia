-- Prove2me | solution 1 for InfoBargaining.Monotone.proposition1_optSet_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T17:37:59.91081+00:00
-- url     : https://prove2.me/submissions/dba4dfe4-a48d-4ad9-b229-98796ed55e73

import Mathlib
import Definitions.Def_InfoBargaining_Monotone_Setting
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

set_option autoImplicit false

namespace InfoBargaining.Monotone.P1Aux

open MeasureTheory Supermodularity.Lattices InfoBargaining.Monotone

/-- Topkis on the real line with weakly increasing differences. -/
theorem topkis (f g : ℝ → ℝ) (lo hi : ℝ)
    (hID : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, b ≤ a → g b - f b ≤ g a - f a) :
    InducedSetOrder {α | α ∈ Set.Icc lo hi ∧ ∀ α' ∈ Set.Icc lo hi, f α' ≤ f α}
      {α | α ∈ Set.Icc lo hi ∧ ∀ α' ∈ Set.Icc lo hi, g α' ≤ g α} := by
  intro a ha b hb
  rcases le_total a b with hab | hab
  · rw [inf_eq_left.2 hab, sup_eq_right.2 hab]
    exact ⟨ha, hb⟩
  · rw [inf_eq_right.2 hab, sup_eq_left.2 hab]
    have h := hID a ha.1 b hb.1 hab
    have h1 := ha.2 b hb.1
    have h2 := hb.2 a ha.1
    refine ⟨⟨hb.1, fun α' hα' => ?_⟩, ⟨ha.1, fun α' hα' => ?_⟩⟩
    · have := ha.2 α' hα'
      linarith
    · have := hb.2 α' hα'
      linarith

theorem integrable_F (M : Model) (α c : ℝ) :
    Integrable (fun w => max (M.postMean α w - c) 0) M.μ := by
  have h : Integrable (fun w : ℝ => α * w + (1 - α) * M.uhat - c) M.μ :=
    ((M.integrable.const_mul α).add (integrable_const _)).sub (integrable_const c)
  unfold Model.postMean
  exact h.pos_part

theorem integral_le_of (M : Model) (F G : ℝ → ℝ) (hF : Integrable F M.μ)
    (hG : Integrable G M.μ) (t : ℝ) (h : ∀ w, F w + t * (w - M.uhat) ≤ G w) :
    ∫ w, F w ∂M.μ ≤ ∫ w, G w ∂M.μ := by
  have hL : Integrable (fun w : ℝ => t * (w - M.uhat)) M.μ :=
    (M.integrable.sub (integrable_const _)).const_mul t
  have h0 : ∫ w, t * (w - M.uhat) ∂M.μ = 0 := by
    rw [integral_const_mul, integral_sub M.integrable (integrable_const _)]
    simp [Model.uhat]
  calc ∫ w, F w ∂M.μ = ∫ w, (F w + t * (w - M.uhat)) ∂M.μ := by
        rw [integral_add hF hL, h0, add_zero]
    _ ≤ ∫ w, G w ∂M.μ := integral_mono (hF.add hL) hG h

/-- Position facts for the posterior mean. -/
theorem pos_facts (M : Model) (α β w : ℝ) (hα : 0 ≤ α) (hab : α ≤ β) :
    (w ≤ M.uhat → M.postMean β w ≤ M.postMean α w ∧ M.postMean α w ≤ M.uhat) ∧
    (M.uhat ≤ w → M.postMean α w ≤ M.postMean β w ∧ M.uhat ≤ M.postMean α w) := by
  simp only [Model.postMean]
  refine ⟨fun hw => ⟨?_, ?_⟩, fun hw => ⟨?_, ?_⟩⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

theorem A_mono (M : Model) (c α β : ℝ) (hα : 0 ≤ α) (hab : α ≤ β) :
    M.A α c ≤ M.A β c := by
  unfold Model.A
  rcases le_total c M.uhat with hc | hc
  · refine integral_le_of M _ _ (integrable_F M α c) (integrable_F M β c) (β - α) (fun w => ?_)
    have hp := pos_facts M α β w hα hab
    have hd : M.postMean β w - M.postMean α w = (β - α) * (w - M.uhat) := by
      simp only [Model.postMean]; ring
    rcases le_total w M.uhat with hw | hw
    · obtain ⟨h1, h2⟩ := hp.1 hw
      have : (β - α) * (w - M.uhat) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      simp only [max_def]; split_ifs <;> linarith
    · obtain ⟨h1, h2⟩ := hp.2 hw
      simp only [max_def]; split_ifs <;> linarith
  · refine integral_le_of M _ _ (integrable_F M α c) (integrable_F M β c) 0 (fun w => ?_)
    have hp := pos_facts M α β w hα hab
    rcases le_total w M.uhat with hw | hw
    · obtain ⟨h1, h2⟩ := hp.1 hw
      simp only [max_def]; split_ifs <;> linarith
    · obtain ⟨h1, h2⟩ := hp.2 hw
      simp only [max_def]; split_ifs <;> linarith

theorem A_diff_low (M : Model) (c c' α β : ℝ) (hcc : c ≤ c') (hc' : c' ≤ M.uhat)
    (hα : 0 ≤ α) (hab : α ≤ β) :
    M.A α c' - M.A α c ≤ M.A β c' - M.A β c := by
  have key : ∫ w, (max (M.postMean α w - c') 0 + max (M.postMean β w - c) 0) ∂M.μ ≤
      ∫ w, (max (M.postMean β w - c') 0 + max (M.postMean α w - c) 0) ∂M.μ := by
    refine integral_le_of M _ _ ((integrable_F M α c').add (integrable_F M β c))
      ((integrable_F M β c').add (integrable_F M α c)) 0 (fun w => ?_)
    have hp := pos_facts M α β w hα hab
    rcases le_total w M.uhat with hw | hw
    · obtain ⟨h1, h2⟩ := hp.1 hw
      simp only [max_def]; split_ifs <;> linarith
    · obtain ⟨h1, h2⟩ := hp.2 hw
      simp only [max_def]; split_ifs <;> linarith
  rw [integral_add (integrable_F M α c') (integrable_F M β c),
    integral_add (integrable_F M β c') (integrable_F M α c)] at key
  unfold Model.A
  linarith

theorem A_diff_high (M : Model) (c c' α β : ℝ) (hcc : c ≤ c') (hc : M.uhat ≤ c)
    (hα : 0 ≤ α) (hab : α ≤ β) :
    M.A β c' - M.A β c ≤ M.A α c' - M.A α c := by
  have key : ∫ w, (max (M.postMean β w - c') 0 + max (M.postMean α w - c) 0) ∂M.μ ≤
      ∫ w, (max (M.postMean α w - c') 0 + max (M.postMean β w - c) 0) ∂M.μ := by
    refine integral_le_of M _ _ ((integrable_F M β c').add (integrable_F M α c))
      ((integrable_F M α c').add (integrable_F M β c)) 0 (fun w => ?_)
    have hp := pos_facts M α β w hα hab
    rcases le_total w M.uhat with hw | hw
    · obtain ⟨h1, h2⟩ := hp.1 hw
      simp only [max_def]; split_ifs <;> linarith
    · obtain ⟨h1, h2⟩ := hp.2 hw
      simp only [max_def]; split_ifs <;> linarith
  rw [integral_add (integrable_F M β c') (integrable_F M α c),
    integral_add (integrable_F M α c') (integrable_F M β c)] at key
  unfold Model.A
  linarith

theorem main (M : Model) :
    (∀ θb ∈ Set.Ioo (0 : ℝ) 1, ∀ θb' ∈ Set.Ioo (0 : ℝ) 1, ∀ c : ℝ, θb ≤ θb' →
      (M.optSet θb c).Nonempty → (M.optSet θb' c).Nonempty →
      InducedSetOrder (M.optSet θb c) (M.optSet θb' c)) ∧
    (∀ θb ∈ Set.Ioo (0 : ℝ) 1, ∀ c c' : ℝ, c ≤ c' → c' ≤ M.uhat →
      (M.optSet θb c).Nonempty → (M.optSet θb c').Nonempty →
      InducedSetOrder (M.optSet θb c) (M.optSet θb c')) ∧
    (∀ θb ∈ Set.Ioo (0 : ℝ) 1, ∀ c c' : ℝ, M.uhat ≤ c → c ≤ c' →
      (M.optSet θb c).Nonempty → (M.optSet θb c').Nonempty →
      InducedSetOrder (M.optSet θb c') (M.optSet θb c)) := by
  have hlo : 0 ≤ M.αlo := le_of_lt M.αlo_pos
  refine ⟨?_, ?_, ?_⟩
  · intro θb _ θb' _ c hθ _ _
    refine topkis (M.Ub θb c) (M.Ub θb' c) M.αlo M.αhi (fun a ha b hb hba => ?_)
    have h := A_mono M c b a (le_trans hlo hb.1) hba
    have h2 := mul_le_mul_of_nonneg_left h (sub_nonneg.2 hθ)
    simp only [Model.Ub]
    nlinarith
  · intro θb hθ c c' hcc hc' _ _
    refine topkis (M.Ub θb c) (M.Ub θb c') M.αlo M.αhi (fun a ha b hb hba => ?_)
    have h := A_diff_low M c c' b a hcc hc' (le_trans hlo hb.1) hba
    have h2 := mul_le_mul_of_nonneg_left h (le_of_lt hθ.1)
    simp only [Model.Ub]
    nlinarith
  · intro θb hθ c c' hc hcc _ _
    refine topkis (M.Ub θb c') (M.Ub θb c) M.αlo M.αhi (fun a ha b hb hba => ?_)
    have h := A_diff_high M c c' b a hcc hc (le_trans hlo hb.1) hba
    have h2 := mul_le_mul_of_nonneg_left h (le_of_lt hθ.1)
    simp only [Model.Ub]
    nlinarith

end InfoBargaining.Monotone.P1Aux

open InfoBargaining.Monotone Supermodularity.Lattices in
theorem solution (M : Model) :
    (∀ θb ∈ Set.Ioo (0 : ℝ) 1, ∀ θb' ∈ Set.Ioo (0 : ℝ) 1, ∀ c : ℝ, θb ≤ θb' →
      (M.optSet θb c).Nonempty → (M.optSet θb' c).Nonempty →
      InducedSetOrder (M.optSet θb c) (M.optSet θb' c)) ∧
    (∀ θb ∈ Set.Ioo (0 : ℝ) 1, ∀ c c' : ℝ, c ≤ c' → c' ≤ M.uhat →
      (M.optSet θb c).Nonempty → (M.optSet θb c').Nonempty →
      InducedSetOrder (M.optSet θb c) (M.optSet θb c')) ∧
    (∀ θb ∈ Set.Ioo (0 : ℝ) 1, ∀ c c' : ℝ, M.uhat ≤ c → c ≤ c' →
      (M.optSet θb c).Nonempty → (M.optSet θb c').Nonempty →
      InducedSetOrder (M.optSet θb c') (M.optSet θb c)) := by
  exact InfoBargaining.Monotone.P1Aux.main M
