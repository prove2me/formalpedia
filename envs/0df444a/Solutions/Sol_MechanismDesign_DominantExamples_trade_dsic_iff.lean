-- Prove2me | solution 1 for MechanismDesign.DominantExamples.trade_dsic_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:39:56.159578+00:00
-- url     : https://prove2.me/submissions/fefccf79-c050-4a99-a1ed-1acc966e9382

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade



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

lemma od_seller (lo hi : ℝ) (g s : ℝ → ℝ) (hg : ∀ x ∈ Set.Icc lo hi, g x = 0 ∨ g x = 1) :
    (∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, a * (1 - g b) + s b ≤ a * (1 - g a) + s a) ↔
    ∃ θhat τS τhatS : ℝ,
      (∀ x ∈ Set.Icc lo hi, x < θhat → g x = 1 ∧ s x = τhatS) ∧
      (∀ x ∈ Set.Icc lo hi, θhat < x → g x = 0 ∧ s x = τS) ∧
      (∀ x ∈ Set.Icc lo hi, x = θhat → (g x = 0 ∧ s x = τS) ∨ (g x = 1 ∧ s x = τhatS)) ∧
      τhatS - τS = θhat := by
  have hg' : ∀ x ∈ Set.Icc lo hi, (fun x => 1 - g x) x = 0 ∨ (fun x => 1 - g x) x = 1 := by
    intro x hx
    rcases hg x hx with h | h
    · right; simp [h]
    · left; simp [h]
  have key := od_iff lo hi (fun x => 1 - g x) (fun x => - s x) hg'
  constructor
  · intro h
    obtain ⟨θhat, τ, τhat, P1, P2, P3, e⟩ := key.1 (by
      intro a ha b hb; have := h a ha b hb; linarith)
    refine ⟨θhat, -τhat, -τ, ?_, ?_, ?_, by linarith⟩
    · intro x hx hl
      obtain ⟨h1, h2⟩ := P1 x hx hl
      constructor <;> linarith
    · intro x hx hl
      obtain ⟨h1, h2⟩ := P2 x hx hl
      constructor <;> linarith
    · intro x hx hl
      rcases P3 x hx hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; constructor <;> linarith
      · left; constructor <;> linarith
  · rintro ⟨θhat, τS, τhatS, P1, P2, P3, e⟩
    have := key.2 ⟨θhat, -τhatS, -τS, ?_, ?_, ?_, by linarith⟩
    · intro a ha b hb; have := this a ha b hb; linarith
    · intro x hx hl
      obtain ⟨h1, h2⟩ := P1 x hx hl
      constructor <;> linarith
    · intro x hx hl
      obtain ⟨h1, h2⟩ := P2 x hx hl
      constructor <;> linarith
    · intro x hx hl
      rcases P3 x hx hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; constructor <;> linarith
      · left; constructor <;> linarith

theorem trade_dsic_iff_core {E : TradeSetting} (M : TradeMechanism E) :
    M.IsDSIC ↔
      (∀ θB ∈ Set.Icc E.loB E.hiB, ∃ θhatS τS τhatS : ℝ,
        (∀ θS ∈ Set.Icc E.loS E.hiS, θS < θhatS →
          M.q (θS, θB) = 1 ∧ M.tS (θS, θB) = τhatS) ∧
        (∀ θS ∈ Set.Icc E.loS E.hiS, θhatS < θS →
          M.q (θS, θB) = 0 ∧ M.tS (θS, θB) = τS) ∧
        (∀ θS ∈ Set.Icc E.loS E.hiS, θS = θhatS →
          (M.q (θS, θB) = 0 ∧ M.tS (θS, θB) = τS) ∨
          (M.q (θS, θB) = 1 ∧ M.tS (θS, θB) = τhatS)) ∧
        τhatS - τS = θhatS) ∧
      (∀ θS ∈ Set.Icc E.loS E.hiS, ∃ θhatB τB τhatB : ℝ,
        (∀ θB ∈ Set.Icc E.loB E.hiB, θB < θhatB →
          M.q (θS, θB) = 0 ∧ M.tB (θS, θB) = τB) ∧
        (∀ θB ∈ Set.Icc E.loB E.hiB, θhatB < θB →
          M.q (θS, θB) = 1 ∧ M.tB (θS, θB) = τhatB) ∧
        (∀ θB ∈ Set.Icc E.loB E.hiB, θB = θhatB →
          (M.q (θS, θB) = 0 ∧ M.tB (θS, θB) = τB) ∨
          (M.q (θS, θB) = 1 ∧ M.tB (θS, θB) = τhatB)) ∧
        τhatB - τB = θhatB) := by
  unfold TradeMechanism.IsDSIC
  constructor
  · rintro ⟨hS, hB⟩
    refine ⟨fun θB hθB => ?_, fun θS hθS => ?_⟩
    · apply (od_seller E.loS E.hiS (fun x => M.q (x, θB)) (fun x => M.tS (x, θB))
        (fun x hx => M.q_mem _ ⟨hx, hθB⟩)).1
      intro a ha b hb
      have := hS (a, θB) ⟨ha, hθB⟩ b hb
      simpa [TradeMechanism.uS] using this
    · apply (od_iff E.loB E.hiB (fun y => M.q (θS, y)) (fun y => M.tB (θS, y))
        (fun y hy => M.q_mem _ ⟨hθS, hy⟩)).1
      intro a ha b hb
      have := hB (θS, a) ⟨hθS, ha⟩ b hb
      simpa [TradeMechanism.uB] using this
  · rintro ⟨hS, hB⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨a, b⟩ hθ x hx
      have := (od_seller E.loS E.hiS (fun x => M.q (x, b)) (fun x => M.tS (x, b))
        (fun x hx => M.q_mem _ ⟨hx, hθ.2⟩)).2 (hS b hθ.2) a hθ.1 x hx
      simpa [TradeMechanism.uS] using this
    · rintro ⟨a, b⟩ hθ y hy
      have := (od_iff E.loB E.hiB (fun y => M.q (a, y)) (fun y => M.tB (a, y))
        (fun y hy => M.q_mem _ ⟨hθ.1, hy⟩)).2 (hB a hθ.1) b hθ.2 y hy
      simpa [TradeMechanism.uB] using this

lemma tq_nonneg {E : TradeSetting} (M : TradeMechanism E) {θ : ℝ × ℝ} (hθ : θ ∈ E.typeSpace) :
    0 ≤ M.q θ := by
  rcases M.q_mem θ hθ with h | h <;> rw [h] <;> norm_num

theorem trade_epir_iff_core {E : TradeSetting} (M : TradeMechanism E) (hM : M.IsDSIC) :
    M.IsEPIR ↔
      (∀ θB ∈ Set.Icc E.loB E.hiB, E.hiS * M.q (E.hiS, θB) ≤ M.tS (E.hiS, θB)) ∧
      (∀ θS ∈ Set.Icc E.loS E.hiS, M.tB (θS, E.loB) ≤ E.loB * M.q (θS, E.loB)) := by
  have hhi : E.hiS ∈ Set.Icc E.loS E.hiS := ⟨E.loS_lt_hiS.le, le_rfl⟩
  have hlo : E.loB ∈ Set.Icc E.loB E.hiB := ⟨le_rfl, E.loB_lt_hiB.le⟩
  constructor
  · intro h
    refine ⟨fun θB hθB => ?_, fun θS hθS => ?_⟩
    · have := (h (E.hiS, θB) ⟨hhi, hθB⟩).1
      simp only [TradeMechanism.uS] at this; linarith
    · have := (h (θS, E.loB) ⟨hθS, hlo⟩).2
      simp only [TradeMechanism.uB] at this; linarith
  · rintro ⟨h1, h2⟩ ⟨a, b⟩ hθ
    constructor
    · have d := hM.1 (a, b) hθ E.hiS hhi
      have e := h1 b hθ.2
      have hq := tq_nonneg M (θ := (E.hiS, b)) ⟨hhi, hθ.2⟩
      have ha : a ≤ E.hiS := hθ.1.2
      simp only at d e ⊢
      nlinarith
    · have d := hM.2 (a, b) hθ E.loB hlo
      have e := h2 a hθ.1
      have hq := tq_nonneg M (θ := (a, E.loB)) ⟨hθ.1, hlo⟩
      have hb : E.loB ≤ b := hθ.2.1
      simp only at d e ⊢
      nlinarith

section Keys

lemma keyInf (lo hi : ℝ) (φ : ℝ → ℝ) (hφ : StrictMonoOn φ (Set.Icc lo hi)) (C : ℝ)
    {a : ℝ} (ha : a ∈ Set.Icc lo hi) {x : ℝ} (hx : x ∈ Set.Icc lo hi) :
    let ys := sInf {y | y ∈ Set.Icc lo hi ∧ C ≤ φ y}
    (if C ≤ φ x then (1:ℝ) else 0) * (a - ys) ≤ (if C ≤ φ a then (1:ℝ) else 0) * (a - ys) ∧
      0 ≤ (if C ≤ φ a then (1:ℝ) else 0) * (a - ys) := by
  intro ys
  set X := {y | y ∈ Set.Icc lo hi ∧ C ≤ φ y} with hXdef
  have hbdd : BddBelow X := ⟨lo, fun y hy => hy.1.1⟩
  have hmem : ∀ y ∈ Set.Icc lo hi, C ≤ φ y → ys ≤ y := fun y hy h => csInf_le hbdd ⟨hy, h⟩
  have hnn : 0 ≤ (if C ≤ φ a then (1:ℝ) else 0) * (a - ys) := by
    split_ifs with h
    · rw [one_mul]; exact sub_nonneg.2 (hmem a ha h)
    · rw [zero_mul]
  refine ⟨?_, hnn⟩
  by_cases hxq : C ≤ φ x
  · rw [if_pos hxq, one_mul]
    rcases le_or_gt a ys with hle | hlt
    · linarith
    · obtain ⟨x', hx'X, hx'lt⟩ := exists_lt_of_csInf_lt (show X.Nonempty from ⟨x, hx, hxq⟩) hlt
      have hlt2 : φ x' < φ a := hφ hx'X.1 ha hx'lt
      rw [if_pos (by linarith [hx'X.2]), one_mul]
  · rw [if_neg hxq, zero_mul]; exact hnn

lemma keyInf_lo (lo hi : ℝ) (hlh : lo ≤ hi) (φ : ℝ → ℝ) (C : ℝ) :
    (if C ≤ φ lo then (1:ℝ) else 0) * (lo - sInf {y | y ∈ Set.Icc lo hi ∧ C ≤ φ y}) = 0 := by
  have hlo : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlh⟩
  split_ifs with h
  · have hle := csInf_le (⟨lo, fun y hy => hy.1.1⟩ : BddBelow {y | y ∈ Set.Icc lo hi ∧ C ≤ φ y})
      (⟨hlo, h⟩ : lo ∈ {y | y ∈ Set.Icc lo hi ∧ C ≤ φ y})
    have hge := le_csInf (⟨lo, hlo, h⟩ : {y | y ∈ Set.Icc lo hi ∧ C ≤ φ y}.Nonempty)
      (fun y (hy : y ∈ {y | y ∈ Set.Icc lo hi ∧ C ≤ φ y}) => hy.1.1)
    rw [show lo - sInf {y | y ∈ Set.Icc lo hi ∧ C ≤ φ y} = 0 by linarith, mul_zero]
  · rw [zero_mul]

lemma keySup (lo hi : ℝ) (φ : ℝ → ℝ) (hφ : StrictMonoOn φ (Set.Icc lo hi)) (C : ℝ)
    {a : ℝ} (ha : a ∈ Set.Icc lo hi) {x : ℝ} (hx : x ∈ Set.Icc lo hi) :
    let xs := sSup {y | y ∈ Set.Icc lo hi ∧ φ y ≤ C}
    (if φ x ≤ C then (1:ℝ) else 0) * (xs - a) ≤ (if φ a ≤ C then (1:ℝ) else 0) * (xs - a) ∧
      0 ≤ (if φ a ≤ C then (1:ℝ) else 0) * (xs - a) := by
  intro xs
  set X := {y | y ∈ Set.Icc lo hi ∧ φ y ≤ C} with hXdef
  have hbdd : BddAbove X := ⟨hi, fun y hy => hy.1.2⟩
  have hmem : ∀ y ∈ Set.Icc lo hi, φ y ≤ C → y ≤ xs := fun y hy h => le_csSup hbdd ⟨hy, h⟩
  have hnn : 0 ≤ (if φ a ≤ C then (1:ℝ) else 0) * (xs - a) := by
    split_ifs with h
    · rw [one_mul]; exact sub_nonneg.2 (hmem a ha h)
    · rw [zero_mul]
  refine ⟨?_, hnn⟩
  by_cases hxq : φ x ≤ C
  · rw [if_pos hxq, one_mul]
    rcases le_or_gt xs a with hle | hlt
    · linarith
    · obtain ⟨x', hx'X, hx'lt⟩ := exists_lt_of_lt_csSup (show X.Nonempty from ⟨x, hx, hxq⟩) hlt
      have hlt2 : φ a < φ x' := hφ ha hx'X.1 hx'lt
      rw [if_pos (by linarith [hx'X.2]), one_mul]
  · rw [if_neg hxq, zero_mul]; exact hnn

lemma keySup_hi (lo hi : ℝ) (hlh : lo ≤ hi) (φ : ℝ → ℝ) (C : ℝ) :
    (if φ hi ≤ C then (1:ℝ) else 0) * (sSup {y | y ∈ Set.Icc lo hi ∧ φ y ≤ C} - hi) = 0 := by
  have hhi : hi ∈ Set.Icc lo hi := ⟨hlh, le_rfl⟩
  split_ifs with h
  · have hle := le_csSup (⟨hi, fun y hy => hy.1.2⟩ : BddAbove {y | y ∈ Set.Icc lo hi ∧ φ y ≤ C})
      (⟨hhi, h⟩ : hi ∈ {y | y ∈ Set.Icc lo hi ∧ φ y ≤ C})
    have hge := csSup_le (⟨hi, hhi, h⟩ : {y | y ∈ Set.Icc lo hi ∧ φ y ≤ C}.Nonempty)
      (fun y (hy : y ∈ {y | y ∈ Set.Icc lo hi ∧ φ y ≤ C}) => hy.1.2)
    rw [show sSup {y | y ∈ Set.Icc lo hi ∧ φ y ≤ C} - hi = 0 by linarith, mul_zero]
  · rw [zero_mul]

end Keys

theorem canonical_trade_core {E : TradeSetting} (M : TradeMechanism E) (hM : M.IsCanonical) :
    M.IsDSIC ∧ M.IsEPIR ∧
      (∀ θB ∈ Set.Icc E.loB E.hiB, M.uS (E.hiS, θB) = E.hiS) ∧
      (∀ θS ∈ Set.Icc E.loS E.hiS, M.uB (θS, E.loB) = 0) := by
  obtain ⟨ψS, ψB, hSm, _, hBm, _, hMψ⟩ := hM
  -- seller value
  have hvS : ∀ a, ∀ x ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loB E.hiB,
      a * (1 - M.q (x, b)) + M.tS (x, b) =
        a + (if ψS x ≤ ψB b then (1:ℝ) else 0) *
          (sSup {y | y ∈ Set.Icc E.loS E.hiS ∧ ψS y ≤ ψB b} - a) := by
    intro a x hx b hb
    obtain ⟨h1, h2, _⟩ := hMψ (x, b) ⟨hx, hb⟩
    rw [h1, h2]
    unfold canonicalTradeTS canonicalTradeQ
    simp only
    split_ifs <;> simp_all
  have hvB : ∀ b, ∀ a ∈ Set.Icc E.loS E.hiS, ∀ y ∈ Set.Icc E.loB E.hiB,
      b * M.q (a, y) - M.tB (a, y) =
        (if ψS a ≤ ψB y then (1:ℝ) else 0) *
          (b - sInf {z | z ∈ Set.Icc E.loB E.hiB ∧ ψS a ≤ ψB z}) := by
    intro b a ha y hy
    obtain ⟨h1, _, h3⟩ := hMψ (a, y) ⟨ha, hy⟩
    rw [h1, h3]
    unfold canonicalTradeTB canonicalTradeQ
    simp only
    split_ifs <;> simp_all
  have uS_eq : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loB E.hiB,
      M.uS (a, b) = a + (if ψS a ≤ ψB b then (1:ℝ) else 0) *
          (sSup {y | y ∈ Set.Icc E.loS E.hiS ∧ ψS y ≤ ψB b} - a) := by
    intro a ha b hb
    unfold TradeMechanism.uS; exact hvS a a ha b hb
  have uB_eq : ∀ a ∈ Set.Icc E.loS E.hiS, ∀ b ∈ Set.Icc E.loB E.hiB,
      M.uB (a, b) = (if ψS a ≤ ψB b then (1:ℝ) else 0) *
          (b - sInf {z | z ∈ Set.Icc E.loB E.hiB ∧ ψS a ≤ ψB z}) := by
    intro a ha b hb
    unfold TradeMechanism.uB; exact hvB b a ha b hb
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩ x hx
    simp only
    rw [hvS a x hx b hb, uS_eq a ha b hb]
    have := (keySup E.loS E.hiS ψS hSm (ψB b) ha hx).1
    linarith
  · rintro ⟨a, b⟩ ⟨ha, hb⟩ y hy
    simp only
    rw [hvB b a ha y hy, uB_eq a ha b hb]
    exact (keyInf E.loB E.hiB ψB hBm (ψS a) hb hy).1
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    simp only
    rw [uS_eq a ha b hb, uB_eq a ha b hb]
    have h1 := (keySup E.loS E.hiS ψS hSm (ψB b) ha ha).2
    have h2 := (keyInf E.loB E.hiB ψB hBm (ψS a) hb hb).2
    constructor <;> linarith
  · intro b hb
    rw [uS_eq E.hiS ⟨E.loS_lt_hiS.le, le_rfl⟩ b hb,
      keySup_hi E.loS E.hiS E.loS_lt_hiS.le ψS (ψB b), add_zero]
  · intro a ha
    rw [uB_eq a ha E.loB ⟨le_rfl, E.loB_lt_hiB.le⟩,
      keyInf_lo E.loB E.hiB E.loB_lt_hiB.le ψB (ψS a)]

end MechanismDesign.DominantExamples

open MechanismDesign.DominantExamples


theorem solution {E : TradeSetting} (M : TradeMechanism E) :
    M.IsDSIC ↔
      (∀ θB ∈ Set.Icc E.loB E.hiB, ∃ θhatS τS τhatS : ℝ,
        (∀ θS ∈ Set.Icc E.loS E.hiS, θS < θhatS →
          M.q (θS, θB) = 1 ∧ M.tS (θS, θB) = τhatS) ∧
        (∀ θS ∈ Set.Icc E.loS E.hiS, θhatS < θS →
          M.q (θS, θB) = 0 ∧ M.tS (θS, θB) = τS) ∧
        (∀ θS ∈ Set.Icc E.loS E.hiS, θS = θhatS →
          (M.q (θS, θB) = 0 ∧ M.tS (θS, θB) = τS) ∨
          (M.q (θS, θB) = 1 ∧ M.tS (θS, θB) = τhatS)) ∧
        τhatS - τS = θhatS) ∧
      (∀ θS ∈ Set.Icc E.loS E.hiS, ∃ θhatB τB τhatB : ℝ,
        (∀ θB ∈ Set.Icc E.loB E.hiB, θB < θhatB →
          M.q (θS, θB) = 0 ∧ M.tB (θS, θB) = τB) ∧
        (∀ θB ∈ Set.Icc E.loB E.hiB, θhatB < θB →
          M.q (θS, θB) = 1 ∧ M.tB (θS, θB) = τhatB) ∧
        (∀ θB ∈ Set.Icc E.loB E.hiB, θB = θhatB →
          (M.q (θS, θB) = 0 ∧ M.tB (θS, θB) = τB) ∨
          (M.q (θS, θB) = 1 ∧ M.tB (θS, θB) = τhatB)) ∧
        τhatB - τB = θhatB) := by
  exact trade_dsic_iff_core M
