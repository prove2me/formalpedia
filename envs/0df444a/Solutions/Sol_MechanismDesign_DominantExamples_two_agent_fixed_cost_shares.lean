-- Prove2me | solution 1 for MechanismDesign.DominantExamples.two_agent_fixed_cost_shares
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:46:38.623189+00:00
-- url     : https://prove2.me/submissions/11483f49-d2bd-442f-ac72-c7b699a1b41d

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_PublicGood

open Filter Topology

namespace MechanismDesign.DominantExamples

lemma two_upd0 (a b x : ℝ) : Function.update ![a, b] 0 x = ![x, b] := by
  funext j; fin_cases j <;> simp

lemma two_upd1 (a b y : ℝ) : Function.update ![a, b] 1 y = ![a, y] := by
  funext j; fin_cases j <;> simp

lemma two_eta (θ : Fin 2 → ℝ) : ∃ a b : ℝ, θ = ![a, b] :=
  ⟨θ 0, θ 1, by funext j; fin_cases j <;> rfl⟩

lemma two_mem {E : PublicGoodSetting} (a b : ℝ) :
    ![a, b] ∈ E.typeSpace (Fin 2) ↔ a ∈ Set.Icc E.lo E.hi ∧ b ∈ Set.Icc E.lo E.hi := by
  unfold PublicGoodSetting.typeSpace
  rw [Set.mem_univ_pi, Fin.forall_fin_two]
  simp

lemma two_cont0 (y : ℝ) : Continuous (fun x : ℝ => ![x, y]) := by
  apply continuous_pi
  intro i; fin_cases i <;> simp <;> first | exact continuous_id' | exact continuous_const

lemma two_cont1 (x : ℝ) : Continuous (fun y : ℝ => ![x, y]) := by
  apply continuous_pi
  intro i; fin_cases i <;> simp <;> first | exact continuous_id' | exact continuous_const

theorem two_agent_core {E : PublicGoodSetting} (M : PublicGoodMechanism E (Fin 2))
    (hclosed : IsClosed {θ : Fin 2 → ℝ | θ ∈ E.typeSpace (Fin 2) ∧ M.q θ = 1}) :
    (M.IsDSIC ∧ M.IsEPIR ∧ M.IsBudgetBalanced) ↔
      ∃ τ : Fin 2 → ℝ, τ 0 + τ 1 = E.c ∧ ∀ θ ∈ E.typeSpace (Fin 2),
        ((τ 0 ≤ θ 0 ∧ τ 1 ≤ θ 1) → M.q θ = 1 ∧ ∀ i, M.t i θ = τ i) ∧
        (¬ (τ 0 ≤ θ 0 ∧ τ 1 ≤ θ 1) → M.q θ = 0 ∧ ∀ i, M.t i θ = 0) := by
  set I := Set.Icc E.lo E.hi with hI
  constructor
  · rintro ⟨hD, hIR, hBB⟩
    have D0 : ∀ a ∈ I, ∀ b ∈ I, ∀ x ∈ I,
        a * M.q ![x, b] - M.t 0 ![x, b] ≤ a * M.q ![a, b] - M.t 0 ![a, b] := by
      intro a ha b hb x hx
      have := hD 0 ![a, b] ((two_mem a b).2 ⟨ha, hb⟩) x hx
      simpa [two_upd0] using this
    have D1 : ∀ a ∈ I, ∀ b ∈ I, ∀ y ∈ I,
        b * M.q ![a, y] - M.t 1 ![a, y] ≤ b * M.q ![a, b] - M.t 1 ![a, b] := by
      intro a ha b hb y hy
      have := hD 1 ![a, b] ((two_mem a b).2 ⟨ha, hb⟩) y hy
      simpa [two_upd1] using this
    have IR0 : ∀ a ∈ I, ∀ b ∈ I, 0 ≤ a * M.q ![a, b] - M.t 0 ![a, b] := by
      intro a ha b hb
      simpa using hIR 0 ![a, b] ((two_mem a b).2 ⟨ha, hb⟩)
    have IR1 : ∀ a ∈ I, ∀ b ∈ I, 0 ≤ b * M.q ![a, b] - M.t 1 ![a, b] := by
      intro a ha b hb
      simpa using hIR 1 ![a, b] ((two_mem a b).2 ⟨ha, hb⟩)
    have BB : ∀ a ∈ I, ∀ b ∈ I, M.t 0 ![a, b] + M.t 1 ![a, b] = E.c * M.q ![a, b] := by
      intro a ha b hb
      have := hBB ![a, b] ((two_mem a b).2 ⟨ha, hb⟩)
      rwa [Fin.sum_univ_two] at this
    have q01 : ∀ a ∈ I, ∀ b ∈ I, M.q ![a, b] ≠ 1 → M.q ![a, b] = 0 := fun a ha b hb h =>
      (M.q_mem _ ((two_mem a b).2 ⟨ha, hb⟩)).resolve_right h
    have notT : ∀ a ∈ I, ∀ b ∈ I, M.q ![a, b] = 0 →
        M.t 0 ![a, b] = 0 ∧ M.t 1 ![a, b] = 0 := by
      intro a ha b hb h0
      have h1 := IR0 a ha b hb; have h2 := IR1 a ha b hb; have h3 := BB a ha b hb
      rw [h0] at h1 h2 h3
      constructor <;> linarith
    have inT : ∀ a ∈ I, ∀ b ∈ I, M.q ![a, b] = 1 →
        M.t 0 ![a, b] ≤ a ∧ M.t 1 ![a, b] ≤ b := by
      intro a ha b hb h1
      have h1' := IR0 a ha b hb; have h2 := IR1 a ha b hb
      rw [h1] at h1' h2
      constructor <;> linarith
    have F3 : ∀ a ∈ I, ∀ b ∈ I, ∀ y ∈ I, M.q ![a, y] = 1 → M.q ![b, y] = 0 →
        b ≤ M.t 0 ![a, y] := by
      intro a ha b hb y hy h1 h0
      have d := D0 b hb y hy a ha
      have z := notT b hb y hy h0
      rw [h1, h0, z.1] at d; linarith
    have F4 : ∀ x ∈ I, ∀ a ∈ I, ∀ b ∈ I, M.q ![x, a] = 1 → M.q ![x, b] = 0 →
        b ≤ M.t 1 ![x, a] := by
      intro x hx a ha b hb h1 h0
      have d := D1 x hx b hb a ha
      have z := notT x hx b hb h0
      rw [h1, h0, z.2] at d; linarith
    have F5 : ∀ a ∈ I, ∀ b ∈ I, ∀ y ∈ I, M.q ![a, y] = 1 → M.q ![b, y] = 1 →
        M.t 0 ![a, y] = M.t 0 ![b, y] := by
      intro a ha b hb y hy h1 h2
      have d1 := D0 a ha y hy b hb
      have d2 := D0 b hb y hy a ha
      rw [h1, h2] at d1 d2; linarith
    have F6 : ∀ x ∈ I, ∀ a ∈ I, ∀ b ∈ I, M.q ![x, a] = 1 → M.q ![x, b] = 1 →
        M.t 1 ![x, a] = M.t 1 ![x, b] := by
      intro x hx a ha b hb h1 h2
      have d1 := D1 x hx a ha b hb
      have d2 := D1 x hx b hb a ha
      rw [h1, h2] at d1 d2; linarith
    by_cases hall : ∀ a ∈ I, ∀ b ∈ I, M.q ![a, b] = 0
    · refine ⟨![E.hi + 1, E.c - (E.hi + 1)], by simp, ?_⟩
      intro θ hθ
      obtain ⟨a, b, rfl⟩ := two_eta θ
      obtain ⟨ha, hb⟩ := (two_mem a b).1 hθ
      refine ⟨fun h => ?_, fun _ => ?_⟩
      · simp at h; linarith [h.1, ha.2]
      · refine ⟨hall a ha b hb, ?_⟩
        rw [Fin.forall_fin_two]
        exact notT a ha b hb (hall a ha b hb)
    push_neg at hall
    obtain ⟨a0, ha0, b0, hb0, hq0'⟩ := hall
    have hq0 : M.q ![a0, b0] = 1 :=
      (M.q_mem _ ((two_mem a0 b0).2 ⟨ha0, hb0⟩)).resolve_left hq0'
    have hhi : E.hi ∈ I := ⟨E.lo_lt_hi.le, le_rfl⟩
    have Up0 : ∀ a ∈ I, ∀ y ∈ I, M.q ![a, y] = 1 → ∀ x ∈ I, a ≤ x → M.q ![x, y] = 1 := by
      intro a ha y hy h1 x hx hax
      by_contra hc
      have h0 := q01 x hx y hy hc
      have e1 := F3 a ha x hx y hy h1 h0
      have e2 := (inT a ha y hy h1).1
      have : x = a := le_antisymm (by linarith) hax
      rw [this, h1] at h0; norm_num at h0
    have Up1 : ∀ x ∈ I, ∀ a ∈ I, M.q ![x, a] = 1 → ∀ y ∈ I, a ≤ y → M.q ![x, y] = 1 := by
      intro x hx a ha h1 y hy hay
      by_contra hc
      have h0 := q01 x hx y hy hc
      have e1 := F4 x hx a ha y hy h1 h0
      have e2 := (inT x hx a ha h1).2
      have : y = a := le_antisymm (by linarith) hay
      rw [this, h1] at h0; norm_num at h0
    set τ0 := M.t 0 ![a0, b0] with hτ0
    set τ1 := M.t 1 ![a0, b0] with hτ1
    have hsum : τ0 + τ1 = E.c := by
      have := BB a0 ha0 b0 hb0; rw [hq0] at this; linarith
    have price : ∀ a ∈ I, ∀ b ∈ I, M.q ![a, b] = 1 →
        M.t 0 ![a, b] = τ0 ∧ M.t 1 ![a, b] = τ1 := by
      intro a ha b hb h1
      have l1 := Up0 a ha b hb h1 E.hi hhi ha.2
      have l0 := Up0 a0 ha0 b0 hb0 hq0 E.hi hhi ha0.2
      have e1 := F5 a ha E.hi hhi b hb h1 l1
      have e2 := BB E.hi hhi b hb
      have e3 := F6 E.hi hhi b hb b0 hb0 l1 l0
      have e4 := BB E.hi hhi b0 hb0
      have e5 := F5 a0 ha0 E.hi hhi b0 hb0 hq0 l0
      have e6 := BB a ha b hb
      rw [l1] at e2; rw [l0] at e4; rw [h1] at e6
      constructor <;> linarith
    have bounds : ∀ a ∈ I, ∀ b ∈ I, M.q ![a, b] = 1 → τ0 ≤ a ∧ τ1 ≤ b := by
      intro a ha b hb h1
      have := inT a ha b hb h1
      have := price a ha b hb h1
      constructor <;> linarith
    have Rw : ∀ x0 ∈ I, ∀ y ∈ I, M.q ![x0, y] = 1 → ∀ x ∈ I, τ0 < x → M.q ![x, y] = 1 := by
      intro x0 hx0 y hy h1 x hx hlt
      by_contra hc
      have h0 := q01 x hx y hy hc
      have := F3 x0 hx0 x hx y hy h1 h0
      rw [(price x0 hx0 y hy h1).1] at this
      linarith
    have Cl : ∀ x ∈ I, ∀ y0 ∈ I, M.q ![x, y0] = 1 → ∀ y ∈ I, τ1 < y → M.q ![x, y] = 1 := by
      intro x hx y0 hy0 h1 y hy hlt
      by_contra hc
      have h0 := q01 x hx y hy hc
      have := F4 x hx y0 hy0 y hy h1 h0
      rw [(price x hx y0 hy0 h1).2] at this
      linarith
    have clos0 : ∀ x ∈ I, ∀ y ∈ I, ∀ a', a' ≤ E.hi → x < a' →
        (∀ x' ∈ Set.Ioo x a', M.q ![x', y] = 1) → M.q ![x, y] = 1 := by
      intro x hx y hy a' ha' hxa h
      have ht : Tendsto (fun x' : ℝ => ![x', y]) (𝓝[>] x) (𝓝 ![x, y]) :=
        ((two_cont0 y).tendsto x).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ x' in 𝓝[>] x, (fun x' : ℝ => ![x', y]) x' ∈
          {θ : Fin 2 → ℝ | θ ∈ E.typeSpace (Fin 2) ∧ M.q θ = 1} := by
        filter_upwards [Ioo_mem_nhdsGT hxa] with x' hx'
        exact ⟨(two_mem x' y).2 ⟨⟨by linarith [hx'.1, hx.1], by linarith [hx'.2]⟩, hy⟩,
          h x' hx'⟩
      exact (hclosed.mem_of_tendsto ht hev).2
    have clos1 : ∀ x ∈ I, ∀ y ∈ I, ∀ b', b' ≤ E.hi → y < b' →
        (∀ y' ∈ Set.Ioo y b', M.q ![x, y'] = 1) → M.q ![x, y] = 1 := by
      intro x hx y hy b' hb' hyb h
      have ht : Tendsto (fun y' : ℝ => ![x, y']) (𝓝[>] y) (𝓝 ![x, y]) :=
        ((two_cont1 x).tendsto y).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ y' in 𝓝[>] y, (fun y' : ℝ => ![x, y']) y' ∈
          {θ : Fin 2 → ℝ | θ ∈ E.typeSpace (Fin 2) ∧ M.q θ = 1} := by
        filter_upwards [Ioo_mem_nhdsGT hyb] with y' hy'
        exact ⟨(two_mem x y').2 ⟨hx, ⟨by linarith [hy'.1, hy.1], by linarith [hy'.2]⟩⟩,
          h y' hy'⟩
      exact (hclosed.mem_of_tendsto ht hev).2
    have claim1 : ∀ x ∈ I, τ0 ≤ x → M.q ![x, b0] = 1 := by
      intro x hx hxt
      rcases le_or_gt a0 x with h | h
      · exact Up0 a0 ha0 b0 hb0 hq0 x hx h
      rcases lt_or_eq_of_le hxt with h' | h'
      · exact Rw a0 ha0 b0 hb0 hq0 x hx h'
      · apply clos0 x hx b0 hb0 a0 ha0.2 h
        intro x' hx'
        exact Rw a0 ha0 b0 hb0 hq0 x' ⟨by linarith [hx'.1, hx.1], by linarith [hx'.2, ha0.2]⟩
          (by linarith [hx'.1])
    have claim2 : ∀ x ∈ I, τ0 ≤ x → ∀ y ∈ I, τ1 ≤ y → M.q ![x, y] = 1 := by
      intro x hx hxt y hy hyt
      have c1 := claim1 x hx hxt
      rcases le_or_gt b0 y with h | h
      · exact Up1 x hx b0 hb0 c1 y hy h
      rcases lt_or_eq_of_le hyt with h' | h'
      · exact Cl x hx b0 hb0 c1 y hy h'
      · apply clos1 x hx y hy b0 hb0.2 h
        intro y' hy'
        exact Cl x hx b0 hb0 c1 y' ⟨by linarith [hy'.1, hy.1], by linarith [hy'.2, hb0.2]⟩
          (by linarith [hy'.1])
    refine ⟨![τ0, τ1], by simpa using hsum, ?_⟩
    intro θ hθ
    obtain ⟨a, b, rfl⟩ := two_eta θ
    obtain ⟨ha, hb⟩ := (two_mem a b).1 hθ
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.head_cons]
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · have h1 := claim2 a ha hc.1 b hb hc.2
      refine ⟨h1, ?_⟩
      rw [Fin.forall_fin_two]
      simpa using price a ha b hb h1
    · have hn : M.q ![a, b] ≠ 1 := fun h1 => hc (bounds a ha b hb h1)
      have h0 := q01 a ha b hb hn
      refine ⟨h0, ?_⟩
      rw [Fin.forall_fin_two]
      exact notT a ha b hb h0
  · rintro ⟨τ, hτ, hθ⟩
    have outc : ∀ θ ∈ E.typeSpace (Fin 2),
        (τ 0 ≤ θ 0 ∧ τ 1 ≤ θ 1 ∧ M.q θ = 1 ∧ M.t 0 θ = τ 0 ∧ M.t 1 θ = τ 1) ∨
        ((θ 0 < τ 0 ∨ θ 1 < τ 1) ∧ M.q θ = 0 ∧ M.t 0 θ = 0 ∧ M.t 1 θ = 0) := by
      intro θ hθm
      by_cases hc : τ 0 ≤ θ 0 ∧ τ 1 ≤ θ 1
      · have := (hθ θ hθm).1 hc
        exact Or.inl ⟨hc.1, hc.2, this.1, this.2 0, this.2 1⟩
      · have := (hθ θ hθm).2 hc
        have hc' : θ 0 < τ 0 ∨ θ 1 < τ 1 := by
          by_contra hh; push_neg at hh; exact hc hh
        exact Or.inr ⟨hc', this.1, this.2 0, this.2 1⟩
    refine ⟨?_, ?_, ?_⟩
    · unfold PublicGoodMechanism.IsDSIC
      intro i θ hθm x hx
      obtain ⟨a, b, rfl⟩ := two_eta θ
      obtain ⟨ha, hb⟩ := (two_mem a b).1 hθm
      fin_cases i
      · simp only [Fin.zero_eta, two_upd0, Matrix.cons_val_zero]
        rcases outc ![x, b] ((two_mem x b).2 ⟨hx, hb⟩) with
          ⟨l1, l2, q1, s1, _⟩ | ⟨l1, q1, s1, _⟩ <;>
          rcases outc ![a, b] hθm with ⟨m1, m2, q2, s2, _⟩ | ⟨m1, q2, s2, _⟩ <;>
          (try simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            Matrix.head_cons] at *) <;>
          rw [q1, s1, q2, s2] <;> (try rcases l1 with l1 | l1) <;>
          (try rcases m1 with m1 | m1) <;> linarith
      · simp only [Fin.mk_one, two_upd1, Matrix.cons_val_one, Matrix.head_cons]
        rcases outc ![a, x] ((two_mem a x).2 ⟨ha, hx⟩) with
          ⟨l1, l2, q1, _, s1⟩ | ⟨l1, q1, _, s1⟩ <;>
          rcases outc ![a, b] hθm with ⟨m1, m2, q2, _, s2⟩ | ⟨m1, q2, _, s2⟩ <;>
          (try simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            Matrix.head_cons] at *) <;>
          rw [q1, s1, q2, s2] <;> (try rcases l1 with l1 | l1) <;>
          (try rcases m1 with m1 | m1) <;> linarith
    · unfold PublicGoodMechanism.IsEPIR
      intro i θ hθm
      rcases outc θ hθm with ⟨m1, m2, q2, s2, t2⟩ | ⟨m1, q2, s2, t2⟩
      · fin_cases i
        · simp only [Fin.zero_eta]; rw [q2, s2]; linarith
        · simp only [Fin.mk_one]; rw [q2, t2]; linarith
      · fin_cases i
        · simp only [Fin.zero_eta]; rw [q2, s2]; ring_nf; rfl
        · simp only [Fin.mk_one]; rw [q2, t2]; ring_nf; rfl
    · intro θ hθm
      rw [Fin.sum_univ_two]
      rcases outc θ hθm with ⟨m1, m2, q2, s2, t2⟩ | ⟨m1, q2, s2, t2⟩
      · rw [q2, s2, t2, hτ]; ring
      · rw [q2, s2, t2]; ring

end MechanismDesign.DominantExamples

open MechanismDesign.DominantExamples


theorem solution {E : PublicGoodSetting} (M : PublicGoodMechanism E (Fin 2))
    (hclosed : IsClosed {θ : Fin 2 → ℝ | θ ∈ E.typeSpace (Fin 2) ∧ M.q θ = 1}) :
    (M.IsDSIC ∧ M.IsEPIR ∧ M.IsBudgetBalanced) ↔
      ∃ τ : Fin 2 → ℝ, τ 0 + τ 1 = E.c ∧ ∀ θ ∈ E.typeSpace (Fin 2),
        ((τ 0 ≤ θ 0 ∧ τ 1 ≤ θ 1) → M.q θ = 1 ∧ ∀ i, M.t i θ = τ i) ∧
        (¬ (τ 0 ≤ θ 0 ∧ τ 1 ≤ θ 1) → M.q θ = 0 ∧ ∀ i, M.t i θ = 0) := by
  exact two_agent_core M hclosed
