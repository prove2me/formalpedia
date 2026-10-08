-- Prove2me | solution 1 for MechanismDesign.DominantExamples.fixed_price
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:42:52.989853+00:00
-- url     : https://prove2.me/submissions/8e4c902c-ba10-44f0-9568-ab66b8be35a8

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade

open Filter Topology

namespace MechanismDesign.DominantExamples

theorem fixed_price_core {E : TradeSetting} (M : TradeMechanism E)
    (hclosed : IsClosed {θ : ℝ × ℝ | θ ∈ E.typeSpace ∧ M.q θ = 1}) :
    (M.IsDSIC ∧ M.IsEPIR ∧ M.IsExactlyBudgetBalanced) ↔
      ((∀ θ ∈ E.typeSpace, M.q θ = 0 ∧ M.tS θ = 0 ∧ M.tB θ = 0) ∨
        ∃ θhat : ℝ, ∀ θ ∈ E.typeSpace,
          ((θ.1 ≤ θhat ∧ θhat ≤ θ.2) → M.q θ = 1 ∧ M.tS θ = θhat ∧ M.tB θ = θhat) ∧
          ((θhat < θ.1 ∨ θ.2 < θhat) → M.q θ = 0 ∧ M.tS θ = 0 ∧ M.tB θ = 0)) := by
  constructor
  · rintro ⟨⟨hS, hB⟩, hIR, hBB⟩
    have notT : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loB E.hiB, M.q (a, b) = 0 →
        M.tS (a, b) = 0 ∧ M.tB (a, b) = 0 := by
      intro a ha b hb hq
      have h1 := hIR (a, b) ⟨ha, hb⟩
      have h2 := hBB (a, b) ⟨ha, hb⟩
      simp only [TradeMechanism.uS, TradeMechanism.uB, hq] at h1 h2
      constructor <;> linarith [h1.1, h1.2]
    have inT : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loB E.hiB, M.q (a, b) = 1 →
        a ≤ M.tS (a, b) ∧ M.tB (a, b) ≤ b := by
      intro a ha b hb hq
      have h1 := hIR (a, b) ⟨ha, hb⟩
      simp only [TradeMechanism.uS, TradeMechanism.uB, hq] at h1
      constructor <;> linarith [h1.1, h1.2]
    have q01 : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loB E.hiB,
        M.q (a, b) ≠ 1 → M.q (a, b) = 0 := by
      intro a ha b hb h
      exact (M.q_mem (a, b) ⟨ha, hb⟩).resolve_right h
    have F3 : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loS E.hiS, ∀ y ∈ Set.Icc E.loB E.hiB,
        M.q (a, y) = 1 → M.q (b, y) = 0 → M.tS (a, y) ≤ b := by
      intro a ha b hb y hy h1 h0
      have d := hS (b, y) ⟨hb, hy⟩ a ha
      have z := notT b hb y hy h0
      simp only [TradeMechanism.uS, h1, h0, z.1] at d
      linarith
    have F4 : ∀ x ∈ Set.Icc E.loS E.hiS, ∀ a ∈ Set.Icc E.loB E.hiB, ∀ b ∈ Set.Icc E.loB E.hiB,
        M.q (x, a) = 1 → M.q (x, b) = 0 → b ≤ M.tB (x, a) := by
      intro x hx a ha b hb h1 h0
      have d := hB (x, b) ⟨hx, hb⟩ a ha
      have z := notT x hx b hb h0
      simp only [TradeMechanism.uB, h1, h0, z.2] at d
      linarith
    have F5 : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loS E.hiS, ∀ y ∈ Set.Icc E.loB E.hiB,
        M.q (a, y) = 1 → M.q (b, y) = 1 → M.tS (a, y) = M.tS (b, y) := by
      intro a ha b hb y hy h1 h2
      have d1 := hS (a, y) ⟨ha, hy⟩ b hb
      have d2 := hS (b, y) ⟨hb, hy⟩ a ha
      simp only [TradeMechanism.uS, h1, h2] at d1 d2
      linarith
    have F6 : ∀ x ∈ Set.Icc E.loS E.hiS, ∀ a ∈ Set.Icc E.loB E.hiB, ∀ b ∈ Set.Icc E.loB E.hiB,
        M.q (x, a) = 1 → M.q (x, b) = 1 → M.tB (x, a) = M.tB (x, b) := by
      intro x hx a ha b hb h1 h2
      have d1 := hB (x, a) ⟨hx, ha⟩ b hb
      have d2 := hB (x, b) ⟨hx, hb⟩ a ha
      simp only [TradeMechanism.uB, h1, h2] at d1 d2
      linarith
    by_cases hall : ∀ θ ∈ E.typeSpace, M.q θ = 0
    · left
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      have hq := hall (a, b) ⟨ha, hb⟩
      exact ⟨hq, notT a ha b hb hq⟩
    right
    push_neg at hall
    obtain ⟨⟨a0, b0⟩, ⟨ha0, hb0⟩, hq0'⟩ := hall
    have hq0 : M.q (a0, b0) = 1 := (M.q_mem _ ⟨ha0, hb0⟩).resolve_left hq0'
    have hloS : E.loS ∈ Set.Icc E.loS E.hiS := ⟨le_rfl, E.loS_lt_hiS.le⟩
    have Down : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ y ∈ Set.Icc E.loB E.hiB, M.q (a, y) = 1 →
        ∀ x ∈ Set.Icc E.loS E.hiS, x ≤ a → M.q (x, y) = 1 := by
      intro a ha y hy h1 x hx hxa
      by_contra hc
      have h0 := q01 x hx y hy hc
      have e1 := F3 a ha x hx y hy h1 h0
      have e2 := (inT a ha y hy h1).1
      have : x = a := le_antisymm hxa (by linarith)
      rw [this, h1] at h0; norm_num at h0
    have Up : ∀ x ∈ Set.Icc E.loS E.hiS, ∀ a ∈ Set.Icc E.loB E.hiB, M.q (x, a) = 1 →
        ∀ y ∈ Set.Icc E.loB E.hiB, a ≤ y → M.q (x, y) = 1 := by
      intro x hx a ha h1 y hy hay
      by_contra hc
      have h0 := q01 x hx y hy hc
      have e1 := F4 x hx a ha y hy h1 h0
      have e2 := (inT x hx a ha h1).2
      have : y = a := le_antisymm (by linarith) hay
      rw [this, h1] at h0; norm_num at h0
    set θhat := M.tS (a0, b0) with hθhat
    have price : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loB E.hiB, M.q (a, b) = 1 →
        M.tS (a, b) = θhat ∧ M.tB (a, b) = θhat := by
      intro a ha b hb h1
      have l1 := Down a ha b hb h1 E.loS hloS ha.1
      have l0 := Down a0 ha0 b0 hb0 hq0 E.loS hloS ha0.1
      have e1 := F5 a ha E.loS hloS b hb h1 l1
      have e2 := hBB (E.loS, b) ⟨hloS, hb⟩
      have e3 := F6 E.loS hloS b hb b0 hb0 l1 l0
      have e4 := hBB (E.loS, b0) ⟨hloS, hb0⟩
      have e5 := F5 a0 ha0 E.loS hloS b0 hb0 hq0 l0
      have e6 := hBB (a, b) ⟨ha, hb⟩
      constructor <;> linarith
    have bounds : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loB E.hiB, M.q (a, b) = 1 →
        a ≤ θhat ∧ θhat ≤ b := by
      intro a ha b hb h1
      have := inT a ha b hb h1
      have := price a ha b hb h1
      constructor <;> linarith
    have Rw : ∀ x0 ∈ Set.Icc E.loS E.hiS, ∀ y ∈ Set.Icc E.loB E.hiB, M.q (x0, y) = 1 →
        ∀ x ∈ Set.Icc E.loS E.hiS, x < θhat → M.q (x, y) = 1 := by
      intro x0 hx0 y hy h1 x hx hlt
      by_contra hc
      have h0 := q01 x hx y hy hc
      have := F3 x0 hx0 x hx y hy h1 h0
      rw [(price x0 hx0 y hy h1).1] at this
      linarith
    have Cl : ∀ x ∈ Set.Icc E.loS E.hiS, ∀ y0 ∈ Set.Icc E.loB E.hiB, M.q (x, y0) = 1 →
        ∀ y ∈ Set.Icc E.loB E.hiB, θhat < y → M.q (x, y) = 1 := by
      intro x hx y0 hy0 h1 y hy hlt
      by_contra hc
      have h0 := q01 x hx y hy hc
      have := F4 x hx y0 hy0 y hy h1 h0
      rw [(price x hx y0 hy0 h1).2] at this
      linarith
    have closL : ∀ x ∈ Set.Icc E.loS E.hiS, ∀ y ∈ Set.Icc E.loB E.hiB, ∀ a', E.loS ≤ a' →
        a' < x → (∀ x' ∈ Set.Ioo a' x, M.q (x', y) = 1) → M.q (x, y) = 1 := by
      intro x hx y hy a' ha' hax h
      have ht : Tendsto (fun x' : ℝ => (x', y)) (𝓝[<] x) (𝓝 (x, y)) :=
        ((continuous_id.prodMk continuous_const).tendsto x).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ x' in 𝓝[<] x,
          (fun x' : ℝ => (x', y)) x' ∈ {θ : ℝ × ℝ | θ ∈ E.typeSpace ∧ M.q θ = 1} := by
        filter_upwards [Ioo_mem_nhdsLT hax] with x' hx'
        exact ⟨⟨⟨by linarith [hx'.1], by linarith [hx'.2, hx.2]⟩, hy⟩, h x' hx'⟩
      exact (hclosed.mem_of_tendsto ht hev).2
    have closR : ∀ x ∈ Set.Icc E.loS E.hiS, ∀ y ∈ Set.Icc E.loB E.hiB, ∀ b', b' ≤ E.hiB →
        y < b' → (∀ y' ∈ Set.Ioo y b', M.q (x, y') = 1) → M.q (x, y) = 1 := by
      intro x hx y hy b' hb' hyb h
      have ht : Tendsto (fun y' : ℝ => (x, y')) (𝓝[>] y) (𝓝 (x, y)) :=
        ((continuous_const.prodMk continuous_id).tendsto y).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ y' in 𝓝[>] y,
          (fun y' : ℝ => (x, y')) y' ∈ {θ : ℝ × ℝ | θ ∈ E.typeSpace ∧ M.q θ = 1} := by
        filter_upwards [Ioo_mem_nhdsGT hyb] with y' hy'
        exact ⟨⟨hx, ⟨by linarith [hy'.1, hy.1], by linarith [hy'.2]⟩⟩, h y' hy'⟩
      exact (hclosed.mem_of_tendsto ht hev).2
    have claim1 : ∀ x ∈ Set.Icc E.loS E.hiS, x ≤ θhat → M.q (x, b0) = 1 := by
      intro x hx hxt
      rcases le_or_gt x a0 with h | h
      · exact Down a0 ha0 b0 hb0 hq0 x hx h
      rcases lt_or_eq_of_le hxt with h' | h'
      · exact Rw a0 ha0 b0 hb0 hq0 x hx h'
      · apply closL x hx b0 hb0 a0 ha0.1 h
        intro x' hx'
        exact Rw a0 ha0 b0 hb0 hq0 x' ⟨by linarith [hx'.1, ha0.1], by linarith [hx'.2, hx.2]⟩
          (by linarith [hx'.2])
    have claim2 : ∀ x ∈ Set.Icc E.loS E.hiS, x ≤ θhat → ∀ y ∈ Set.Icc E.loB E.hiB,
        θhat ≤ y → M.q (x, y) = 1 := by
      intro x hx hxt y hy hyt
      have c1 := claim1 x hx hxt
      rcases le_or_gt b0 y with h | h
      · exact Up x hx b0 hb0 c1 y hy h
      rcases lt_or_eq_of_le hyt with h' | h'
      · exact Cl x hx b0 hb0 c1 y hy h'
      · apply closR x hx y hy b0 hb0.2 h
        intro y' hy'
        exact Cl x hx b0 hb0 c1 y' ⟨by linarith [hy'.1, hy.1], by linarith [hy'.2, hb0.2]⟩
          (by linarith [hy'.1])
    refine ⟨θhat, ?_⟩
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · have h1 := claim2 a ha hc.1 b hb hc.2
      exact ⟨h1, price a ha b hb h1⟩
    · have hn : M.q (a, b) ≠ 1 := by
        intro h1
        have := bounds a ha b hb h1
        simp only at hc
        rcases hc with hc | hc <;> linarith [this.1, this.2]
      have h0 := q01 a ha b hb hn
      exact ⟨h0, notT a ha b hb h0⟩
  · rintro (hall | ⟨θhat, hθ⟩)
    · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rintro ⟨a, b⟩ ⟨ha, hb⟩ x hx
        have h1 := hall (x, b) ⟨hx, hb⟩
        have h2 := hall (a, b) ⟨ha, hb⟩
        simp only [TradeMechanism.uS, h1.1, h1.2.1, h2.1, h2.2.1]
        exact le_refl _
      · rintro ⟨a, b⟩ ⟨ha, hb⟩ y hy
        have h1 := hall (a, y) ⟨ha, hy⟩
        have h2 := hall (a, b) ⟨ha, hb⟩
        simp only [TradeMechanism.uB, h1.1, h1.2.2, h2.1, h2.2.2]
        exact le_refl _
      · rintro ⟨a, b⟩ hab
        have h2 := hall (a, b) hab
        simp only [TradeMechanism.uS, TradeMechanism.uB, h2.1, h2.2.1, h2.2.2]
        norm_num
      · intro θ h
        have h2 := hall θ h
        rw [h2.2.1, h2.2.2]
    · have outc : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loB E.hiB,
          (a ≤ θhat ∧ θhat ≤ b ∧ M.q (a, b) = 1 ∧ M.tS (a, b) = θhat ∧ M.tB (a, b) = θhat) ∨
          ((θhat < a ∨ b < θhat) ∧ M.q (a, b) = 0 ∧ M.tS (a, b) = 0 ∧ M.tB (a, b) = 0) := by
        intro a ha b hb
        by_cases hc : a ≤ θhat ∧ θhat ≤ b
        · exact Or.inl ⟨hc.1, hc.2, (hθ (a, b) ⟨ha, hb⟩).1 hc⟩
        · have hc' : θhat < a ∨ b < θhat := by
            by_contra hh; push_neg at hh; exact hc ⟨hh.1, hh.2⟩
          exact Or.inr ⟨hc', (hθ (a, b) ⟨ha, hb⟩).2 hc'⟩
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rintro ⟨a, b⟩ ⟨ha, hb⟩ x hx
        simp only [TradeMechanism.uS]
        rcases outc x hx b hb with ⟨l1, l2, q1, s1, _⟩ | ⟨l1, q1, s1, _⟩ <;>
          rcases outc a ha b hb with ⟨m1, m2, q2, s2, _⟩ | ⟨m1, q2, s2, _⟩ <;>
          rw [q1, s1, q2, s2] <;> (try rcases l1 with l1 | l1) <;> (try rcases m1 with m1 | m1)
        all_goals first | linarith | nlinarith
      · rintro ⟨a, b⟩ ⟨ha, hb⟩ y hy
        simp only [TradeMechanism.uB]
        rcases outc a ha y hy with ⟨l1, l2, q1, _, s1⟩ | ⟨l1, q1, _, s1⟩ <;>
          rcases outc a ha b hb with ⟨m1, m2, q2, _, s2⟩ | ⟨m1, q2, _, s2⟩ <;>
          rw [q1, s1, q2, s2] <;> (try rcases l1 with l1 | l1) <;> (try rcases m1 with m1 | m1)
        all_goals first | linarith | nlinarith
      · rintro ⟨a, b⟩ ⟨ha, hb⟩
        simp only [TradeMechanism.uS, TradeMechanism.uB]
        rcases outc a ha b hb with ⟨m1, m2, q2, s2, t2⟩ | ⟨m1, q2, s2, t2⟩ <;>
          rw [q2, s2, t2] <;> constructor <;> linarith
      · rintro ⟨a, b⟩ ⟨ha, hb⟩
        rcases outc a ha b hb with ⟨m1, m2, q2, s2, t2⟩ | ⟨m1, q2, s2, t2⟩ <;>
          rw [s2, t2]

end MechanismDesign.DominantExamples

open MechanismDesign.DominantExamples


theorem solution {E : TradeSetting} (M : TradeMechanism E)
    (hclosed : IsClosed {θ : ℝ × ℝ | θ ∈ E.typeSpace ∧ M.q θ = 1}) :
    (M.IsDSIC ∧ M.IsEPIR ∧ M.IsExactlyBudgetBalanced) ↔
      ((∀ θ ∈ E.typeSpace, M.q θ = 0 ∧ M.tS θ = 0 ∧ M.tB θ = 0) ∨
        ∃ θhat : ℝ, ∀ θ ∈ E.typeSpace,
          ((θ.1 ≤ θhat ∧ θhat ≤ θ.2) → M.q θ = 1 ∧ M.tS θ = θhat ∧ M.tB θ = θhat) ∧
          ((θhat < θ.1 ∨ θ.2 < θhat) → M.q θ = 0 ∧ M.tS θ = 0 ∧ M.tB θ = 0)) := by
  exact fixed_price_core M hclosed
