-- Prove2me | solution 1 for MechanismDesign.DominantExamples.pg_dsic_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:35:32.240578+00:00
-- url     : https://prove2.me/submissions/97934a4f-8256-424f-be78-9ac275a68a22

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_PublicGood



namespace MechanismDesign.DominantExamples

lemma od_outcome {lo hi : ℝ} {g t : ℝ → ℝ} {θhat τ τhat : ℝ}
    (P1 : ∀ x ∈ Set.Icc lo hi, x < θhat → g x = 0 ∧ t x = τ)
    (P2 : ∀ x ∈ Set.Icc lo hi, θhat < x → g x = 1 ∧ t x = τhat)
    (P3 : ∀ x ∈ Set.Icc lo hi, x = θhat → (g x = 0 ∧ t x = τ) ∨ (g x = 1 ∧ t x = τhat))
    {x : ℝ} (hx : x ∈ Set.Icc lo hi) :
    (g x = 0 ∧ t x = τ ∧ x ≤ θhat) ∨ (g x = 1 ∧ t x = τhat ∧ θhat ≤ x) := by
  rcases lt_trichotomy x θhat with h | h | h
  · exact Or.inl ⟨(P1 x hx h).1, (P1 x hx h).2, h.le⟩
  · rcases P3 x hx h with h' | h'
    · exact Or.inl ⟨h'.1, h'.2, h.le⟩
    · exact Or.inr ⟨h'.1, h'.2, h.ge⟩
  · exact Or.inr ⟨(P2 x hx h).1, (P2 x hx h).2, h.le⟩

lemma od_iff (lo hi : ℝ) (g t : ℝ → ℝ) (hg : ∀ x ∈ Set.Icc lo hi, g x = 0 ∨ g x = 1) :
    (∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, a * g b - t b ≤ a * g a - t a) ↔
    ∃ θhat τ τhat : ℝ,
      (∀ x ∈ Set.Icc lo hi, x < θhat → g x = 0 ∧ t x = τ) ∧
      (∀ x ∈ Set.Icc lo hi, θhat < x → g x = 1 ∧ t x = τhat) ∧
      (∀ x ∈ Set.Icc lo hi, x = θhat → (g x = 0 ∧ t x = τ) ∨ (g x = 1 ∧ t x = τhat)) ∧
      τhat - τ = θhat := by
  constructor
  · intro h
    have c0 : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, g a = 0 → g b = 0 → t a = t b := by
      intro a ha b hb h1 h2
      have e1 := h a ha b hb; have e2 := h b hb a ha
      rw [h1, h2] at e1 e2; linarith
    have c1 : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, g a = 1 → g b = 1 → t a = t b := by
      intro a ha b hb h1 h2
      have e1 := h a ha b hb; have e2 := h b hb a ha
      rw [h1, h2] at e1 e2; linarith
    by_cases h0 : ∃ x0 ∈ Set.Icc lo hi, g x0 = 0
    · obtain ⟨x0, hx0, gx0⟩ := h0
      by_cases h1 : ∃ x1 ∈ Set.Icc lo hi, g x1 = 1
      · obtain ⟨x1, hx1, gx1⟩ := h1
        have up : ∀ x ∈ Set.Icc lo hi, g x = 1 → t x1 - t x0 ≤ x := by
          intro x hx gx
          have e := h x hx x0 hx0
          rw [gx, gx0, c1 x hx x1 hx1 gx gx1] at e; linarith
        have dn : ∀ x ∈ Set.Icc lo hi, g x = 0 → x ≤ t x1 - t x0 := by
          intro x hx gx
          have e := h x hx x1 hx1
          rw [gx, gx1, c0 x hx x0 hx0 gx gx0] at e; linarith
        refine ⟨t x1 - t x0, t x0, t x1, ?_, ?_, ?_, rfl⟩
        · intro x hx hlt
          rcases hg x hx with g0 | g1
          · exact ⟨g0, c0 x hx x0 hx0 g0 gx0⟩
          · have := up x hx g1; linarith
        · intro x hx hlt
          rcases hg x hx with g0 | g1
          · have := dn x hx g0; linarith
          · exact ⟨g1, c1 x hx x1 hx1 g1 gx1⟩
        · intro x hx _
          rcases hg x hx with g0 | g1
          · exact Or.inl ⟨g0, c0 x hx x0 hx0 g0 gx0⟩
          · exact Or.inr ⟨g1, c1 x hx x1 hx1 g1 gx1⟩
      · push_neg at h1
        have all0 : ∀ x ∈ Set.Icc lo hi, g x = 0 := fun x hx =>
          (hg x hx).resolve_right (h1 x hx)
        refine ⟨hi + 1, t x0, t x0 + (hi + 1), ?_, ?_, ?_, by ring⟩
        · intro x hx _; exact ⟨all0 x hx, c0 x hx x0 hx0 (all0 x hx) gx0⟩
        · intro x hx hlt; linarith [hx.2]
        · intro x hx he; linarith [hx.2]
    · push_neg at h0
      by_cases h1 : ∃ x1 ∈ Set.Icc lo hi, g x1 = 1
      · obtain ⟨x1, hx1, gx1⟩ := h1
        have all1 : ∀ x ∈ Set.Icc lo hi, g x = 1 := fun x hx =>
          (hg x hx).resolve_left (h0 x hx)
        refine ⟨lo - 1, t x1 - (lo - 1), t x1, ?_, ?_, ?_, by ring⟩
        · intro x hx hlt; linarith [hx.1]
        · intro x hx _; exact ⟨all1 x hx, c1 x hx x1 hx1 (all1 x hx) gx1⟩
        · intro x hx he; linarith [hx.1]
      · push_neg at h1
        refine ⟨0, 0, 0, ?_, ?_, ?_, by ring⟩
        · intro x hx _; exact absurd ((hg x hx).resolve_left (h0 x hx)) (h1 x hx)
        · intro x hx _; exact absurd ((hg x hx).resolve_left (h0 x hx)) (h1 x hx)
        · intro x hx _; exact absurd ((hg x hx).resolve_left (h0 x hx)) (h1 x hx)
  · rintro ⟨θhat, τ, τhat, P1, P2, P3, hP⟩ a ha b hb
    rcases od_outcome P1 P2 P3 ha with ⟨ga, ta, la⟩ | ⟨ga, ta, la⟩ <;>
      rcases od_outcome P1 P2 P3 hb with ⟨gb, tb, lb⟩ | ⟨gb, tb, lb⟩ <;>
      rw [ga, ta, gb, tb] <;> linarith

lemma pg_upd_mem {ι : Type*} [DecidableEq ι] {E : PublicGoodSetting} {θ : ι → ℝ}
    (hθ : θ ∈ E.typeSpace ι) (i : ι) {x : ℝ} (hx : x ∈ Set.Icc E.lo E.hi) :
    Function.update θ i x ∈ E.typeSpace ι := by
  intro j _
  by_cases hj : j = i
  · subst hj; simpa using hx
  · simp [Function.update_of_ne hj]; exact hθ j trivial

theorem pg_dsic_iff_core {ι : Type*} [Fintype ι] [DecidableEq ι] {E : PublicGoodSetting}
    (M : PublicGoodMechanism E ι) :
    M.IsDSIC ↔ ∀ i, ∀ θ ∈ E.typeSpace ι, ∃ θhat τ τhat : ℝ,
      (∀ x ∈ Set.Icc E.lo E.hi, x < θhat →
        M.q (Function.update θ i x) = 0 ∧ M.t i (Function.update θ i x) = τ) ∧
      (∀ x ∈ Set.Icc E.lo E.hi, θhat < x →
        M.q (Function.update θ i x) = 1 ∧ M.t i (Function.update θ i x) = τhat) ∧
      (∀ x ∈ Set.Icc E.lo E.hi, x = θhat →
        (M.q (Function.update θ i x) = 0 ∧ M.t i (Function.update θ i x) = τ) ∨
        (M.q (Function.update θ i x) = 1 ∧ M.t i (Function.update θ i x) = τhat)) ∧
      τhat - τ = θhat := by
  constructor
  · intro h i θ hθ
    apply (od_iff E.lo E.hi (fun x => M.q (Function.update θ i x))
      (fun x => M.t i (Function.update θ i x))
      (fun x hx => M.q_mem _ (pg_upd_mem hθ i hx))).1
    intro a ha b hb
    have := h i (Function.update θ i a) (pg_upd_mem hθ i ha) b hb
    simpa [Function.update_idem] using this
  · intro h i θ hθ x hx
    have := (od_iff E.lo E.hi (fun x => M.q (Function.update θ i x))
      (fun x => M.t i (Function.update θ i x))
      (fun x hx => M.q_mem _ (pg_upd_mem hθ i hx))).2 (h i θ hθ) (θ i) (hθ i trivial) x hx
    simpa [Function.update_eq_self] using this

theorem pg_epir_iff_core {ι : Type*} [Fintype ι] [DecidableEq ι] {E : PublicGoodSetting}
    (M : PublicGoodMechanism E ι) (hM : M.IsDSIC) :
    M.IsEPIR ↔ ∀ i, ∀ θ ∈ E.typeSpace ι,
      M.t i (Function.update θ i E.lo) ≤ E.lo * M.q (Function.update θ i E.lo) := by
  have hlo : E.lo ∈ Set.Icc E.lo E.hi := ⟨le_rfl, E.lo_lt_hi.le⟩
  constructor
  · intro h i θ hθ
    have := h i _ (pg_upd_mem hθ i hlo)
    simp only [Function.update_self] at this
    linarith
  · intro h i θ hθ
    have h1 := hM i θ hθ E.lo hlo
    have h2 := h i θ hθ
    have hq : 0 ≤ M.q (Function.update θ i E.lo) := by
      rcases M.q_mem _ (pg_upd_mem hθ i hlo) with h | h <;> rw [h] <;> norm_num
    have hθi : E.lo ≤ θ i := (hθ i trivial).1
    nlinarith

section CanonPG
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pg_sum_upd (ψ : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι) (x : ℝ) :
    ∑ j ∈ Finset.univ.erase i, ψ j (Function.update θ i x j) =
      ∑ j ∈ Finset.univ.erase i, ψ j (θ j) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma pg_q_eq (E : PublicGoodSetting) (ψ : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι) (x : ℝ) :
    canonicalPGQ E ψ (Function.update θ i x) =
      if E.c ≤ ψ i x + ∑ j ∈ Finset.univ.erase i, ψ j (θ j) then 1 else 0 := by
  unfold canonicalPGQ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self, pg_sum_upd]

lemma pg_t_eq (E : PublicGoodSetting) (ψ : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι) (x : ℝ) :
    canonicalPGT E ψ i (Function.update θ i x) =
      (if E.c ≤ ψ i x + ∑ j ∈ Finset.univ.erase i, ψ j (θ j) then 1 else 0) *
        sInf {x' | x' ∈ Set.Icc E.lo E.hi ∧
          E.c ≤ ψ i x' + ∑ j ∈ Finset.univ.erase i, ψ j (θ j)} := by
  unfold canonicalPGT
  rw [pg_q_eq, pg_sum_upd]
  split_ifs <;> simp_all

lemma pg_key (E : PublicGoodSetting) (ψ : ι → ℝ → ℝ) {i : ι}
    (hψ : StrictMonoOn (ψ i) (Set.Icc E.lo E.hi)) (R : ℝ)
    {a : ℝ} (ha : a ∈ Set.Icc E.lo E.hi) {x : ℝ} (hx : x ∈ Set.Icc E.lo E.hi) :
    let xs := sInf {x' | x' ∈ Set.Icc E.lo E.hi ∧ E.c ≤ ψ i x' + R}
    (if E.c ≤ ψ i x + R then (1:ℝ) else 0) * (a - xs) ≤
        (if E.c ≤ ψ i a + R then (1:ℝ) else 0) * (a - xs) ∧
      0 ≤ (if E.c ≤ ψ i a + R then (1:ℝ) else 0) * (a - xs) := by
  intro xs
  set X := {x' | x' ∈ Set.Icc E.lo E.hi ∧ E.c ≤ ψ i x' + R} with hXdef
  have hbdd : BddBelow X := ⟨E.lo, fun y hy => hy.1.1⟩
  have hmem : ∀ y ∈ Set.Icc E.lo E.hi, E.c ≤ ψ i y + R → xs ≤ y :=
    fun y hy h => csInf_le hbdd ⟨hy, h⟩
  have hnn : 0 ≤ (if E.c ≤ ψ i a + R then (1:ℝ) else 0) * (a - xs) := by
    split_ifs with h
    · rw [one_mul]; exact sub_nonneg.2 (hmem a ha h)
    · rw [zero_mul]
  refine ⟨?_, hnn⟩
  by_cases hxq : E.c ≤ ψ i x + R
  · rw [if_pos hxq, one_mul]
    rcases le_or_gt a xs with hle | hlt
    · linarith
    · obtain ⟨x', hx'X, hx'lt⟩ := exists_lt_of_csInf_lt (show X.Nonempty from ⟨x, hx, hxq⟩) hlt
      have hlt2 : ψ i x' < ψ i a := hψ hx'X.1 ha hx'lt
      rw [if_pos (by linarith [hx'X.2]), one_mul]
  · rw [if_neg hxq, zero_mul]; exact hnn

end CanonPG

theorem canonical_pg_core {ι : Type*} [Fintype ι] [DecidableEq ι] {E : PublicGoodSetting}
    (M : PublicGoodMechanism E ι) (hM : M.IsCanonical) :
    M.IsDSIC ∧ M.IsEPIR ∧
      ∀ i, ∀ θ ∈ E.typeSpace ι, M.u i (Function.update θ i E.lo) = 0 := by
  obtain ⟨ψ, hψ, hMψ⟩ := hM
  have hval : ∀ θ ∈ E.typeSpace ι, ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ a : ℝ,
      a * M.q (Function.update θ i x) - M.t i (Function.update θ i x) =
        (if E.c ≤ ψ i x + ∑ j ∈ Finset.univ.erase i, ψ j (θ j) then (1:ℝ) else 0) *
          (a - sInf {x' | x' ∈ Set.Icc E.lo E.hi ∧
            E.c ≤ ψ i x' + ∑ j ∈ Finset.univ.erase i, ψ j (θ j)}) := by
    intro θ hθ i x hx a
    obtain ⟨h1, h2⟩ := hMψ _ (pg_upd_mem hθ i hx)
    rw [h1, h2 i, pg_q_eq, pg_t_eq]; ring
  have hθi : ∀ θ ∈ E.typeSpace ι, ∀ i, θ i ∈ Set.Icc E.lo E.hi := fun θ hθ i => hθ i trivial
  refine ⟨?_, ?_, ?_⟩
  · intro i θ hθ x hx
    have e1 := hval θ hθ i x hx (θ i)
    have e2 := hval θ hθ i (θ i) (hθi θ hθ i) (θ i)
    simp only [Function.update_eq_self] at e2
    rw [e1, e2]
    exact (pg_key E ψ (hψ i).1 _ (hθi θ hθ i) hx).1
  · intro i θ hθ
    have e2 := hval θ hθ i (θ i) (hθi θ hθ i) (θ i)
    simp only [Function.update_eq_self] at e2
    rw [e2]
    exact (pg_key E ψ (hψ i).1 _ (hθi θ hθ i) (hθi θ hθ i)).2
  · intro i θ hθ
    have hlo : E.lo ∈ Set.Icc E.lo E.hi := ⟨le_rfl, E.lo_lt_hi.le⟩
    unfold PublicGoodMechanism.u
    have e2 := hval θ hθ i E.lo hlo E.lo
    simp only [Function.update_self]
    rw [e2]
    set R := ∑ j ∈ Finset.univ.erase i, ψ j (θ j)
    set X := {x' | x' ∈ Set.Icc E.lo E.hi ∧ E.c ≤ ψ i x' + R} with hXdef
    split_ifs with h
    · have hle : sInf X ≤ E.lo := csInf_le ⟨E.lo, fun y hy => hy.1.1⟩ ⟨hlo, h⟩
      have hge : E.lo ≤ sInf X := le_csInf ⟨E.lo, hlo, h⟩ (fun y hy => hy.1.1)
      rw [show E.lo - sInf X = 0 by linarith, mul_zero]
    · rw [zero_mul]

end MechanismDesign.DominantExamples

open MechanismDesign.DominantExamples


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {E : PublicGoodSetting}
    (M : PublicGoodMechanism E ι) :
    M.IsDSIC ↔ ∀ i, ∀ θ ∈ E.typeSpace ι, ∃ θhat τ τhat : ℝ,
      (∀ x ∈ Set.Icc E.lo E.hi, x < θhat →
        M.q (Function.update θ i x) = 0 ∧ M.t i (Function.update θ i x) = τ) ∧
      (∀ x ∈ Set.Icc E.lo E.hi, θhat < x →
        M.q (Function.update θ i x) = 1 ∧ M.t i (Function.update θ i x) = τhat) ∧
      (∀ x ∈ Set.Icc E.lo E.hi, x = θhat →
        (M.q (Function.update θ i x) = 0 ∧ M.t i (Function.update θ i x) = τ) ∨
        (M.q (Function.update θ i x) = 1 ∧ M.t i (Function.update θ i x) = τhat)) ∧
      τhat - τ = θhat := by
  exact pg_dsic_iff_core M
