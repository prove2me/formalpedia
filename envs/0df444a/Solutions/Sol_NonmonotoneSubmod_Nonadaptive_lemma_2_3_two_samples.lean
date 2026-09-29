-- Prove2me | solution 1 for NonmonotoneSubmod.Nonadaptive.lemma_2_3_two_samples
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T03:14:18.453527+00:00
-- url     : https://prove2.me/submissions/ee5a2986-a27c-4947-b489-ff7318e1e419

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

open NonmonotoneSubmod.Shared

/-- The weight `p^|T| (1-p)^{|A \ T|}` of a subset `T ⊆ A`. -/
private def wt {X : Type} [Fintype X] [DecidableEq X] (p : ℝ) (A T : Finset X) : ℝ :=
  p ^ T.card * (1 - p) ^ (A \ T).card

private theorem wt_nonneg {X : Type} [Fintype X] [DecidableEq X] (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (A T : Finset X) : 0 ≤ wt p A T := by
  have : (0:ℝ) ≤ 1 - p := by linarith
  unfold wt
  positivity

/-- Shifting a submodular function by a fixed set keeps it submodular. -/
private theorem submodular_union {X : Type} [Fintype X] [DecidableEq X]
    {g : Finset X → ℝ} (hg : Submodular g) (C : Finset X) :
    Submodular (fun T => g (C ∪ T)) := by
  intro S T
  have h1 : (C ∪ S) ∪ (C ∪ T) = C ∪ (S ∪ T) := by
    ext a; simp [Finset.mem_union]; tauto
  have h2 : (C ∪ S) ∩ (C ∪ T) = C ∪ (S ∩ T) := by
    ext a; simp [Finset.mem_union, Finset.mem_inter]; tauto
  have := hg (C ∪ S) (C ∪ T)
  rw [h1, h2] at this
  exact this

/-- Lemma 2.2 of Feige–Mirrokni–Vondrák. -/
private theorem sample_core {X : Type} [Fintype X] [DecidableEq X] (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ A : Finset X, ∀ g : Finset X → ℝ, Submodular g →
      (1 - p) * g ∅ + p * g A ≤ ∑ T ∈ A.powerset, wt p A T * g T := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro g hg
    simp [wt]
    ring_nf
    simp
  | insert a s has ih =>
    intro g hg
    have hq0 : (0:ℝ) ≤ 1 - p := by linarith
    -- split the powerset of `insert a s`
    have hsplit : ∑ T ∈ (insert a s).powerset, wt p (insert a s) T * g T
        = (1 - p) * (∑ T ∈ s.powerset, wt p s T * g T)
          + p * (∑ T ∈ s.powerset, wt p s T * g (insert a T)) := by
      rw [Finset.powerset_insert, Finset.sum_union]
      · have h1 : ∑ T ∈ s.powerset, wt p (insert a s) T * g T
            = (1 - p) * ∑ T ∈ s.powerset, wt p s T * g T := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun T hT => ?_
          have hTs : T ⊆ s := Finset.mem_powerset.mp hT
          have hcard : (insert a s \ T).card = (s \ T).card + 1 := by
            have : insert a s \ T = insert a (s \ T) := by
              ext b
              simp only [Finset.mem_sdiff, Finset.mem_insert]
              constructor
              · rintro ⟨hb | hb, hb2⟩
                · exact Or.inl hb
                · exact Or.inr ⟨hb, hb2⟩
              · rintro (rfl | ⟨hb, hb2⟩)
                · exact ⟨Or.inl rfl, fun hc => has (hTs hc)⟩
                · exact ⟨Or.inr hb, hb2⟩
            rw [this, Finset.card_insert_of_notMem (by simp [has] : a ∉ s \ T)]
          unfold wt
          rw [hcard, pow_succ]
          ring
        have h2 : ∑ T ∈ s.powerset.image (insert a), wt p (insert a s) T * g T
            = p * ∑ T ∈ s.powerset, wt p s T * g (insert a T) := by
          rw [Finset.sum_image, Finset.mul_sum]
          · refine Finset.sum_congr rfl fun T hT => ?_
            have hTs : T ⊆ s := Finset.mem_powerset.mp hT
            have haT : a ∉ T := fun h => has (hTs h)
            have hcard1 : (insert a T).card = T.card + 1 :=
              Finset.card_insert_of_notMem haT
            have hcard2 : (insert a s \ insert a T) = s \ T := by
              ext b
              simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
              constructor
              · rintro ⟨hb | hb, hb2⟩
                · exact absurd hb hb2.1
                · exact ⟨hb, hb2.2⟩
              · rintro ⟨hb, hb2⟩
                refine ⟨Or.inr hb, ?_, hb2⟩
                intro hc
                exact has (hc ▸ hb)
            unfold wt
            rw [hcard1, hcard2, pow_succ]
            ring
          · intro T hT T' hT' heq
            have hTs : T ⊆ s := Finset.mem_powerset.mp hT
            have hT's : T' ⊆ s := Finset.mem_powerset.mp hT'
            have haT : a ∉ T := fun h => has (hTs h)
            have haT' : a ∉ T' := fun h => has (hT's h)
            ext b
            constructor
            · intro hb
              have : b ∈ insert a T' := heq ▸ Finset.mem_insert_of_mem hb
              rcases Finset.mem_insert.mp this with rfl | hb'
              · exact absurd hb haT
              · exact hb'
            · intro hb
              have : b ∈ insert a T := heq ▸ Finset.mem_insert_of_mem hb
              rcases Finset.mem_insert.mp this with rfl | hb'
              · exact absurd hb haT'
              · exact hb'
        rw [h1, h2]
      · rw [Finset.disjoint_right]
        intro T hT hT2
        obtain ⟨T', hT', rfl⟩ := Finset.mem_image.mp hT
        have : a ∈ insert a T' := Finset.mem_insert_self a T'
        exact has (Finset.mem_powerset.mp hT2 this)
    rw [hsplit]
    -- the two inductive bounds
    have hga : Submodular (fun T => g ({a} ∪ T)) := submodular_union hg {a}
    have ih1 := ih g hg
    have ih2 := ih (fun T => g ({a} ∪ T)) hga
    have hins : ∀ T : Finset X, ({a} ∪ T : Finset X) = insert a T := by
      intro T; ext b; simp [Finset.mem_union, Finset.mem_insert]
    simp only [hins] at ih2
    -- submodularity of `g` at `s` and `{a}`
    have hsub : g (insert a s) + g ∅ ≤ g s + g ({a} : Finset X) := by
      have h := hg s {a}
      have h1 : s ∪ ({a} : Finset X) = insert a s := by
        ext b; simp [Finset.mem_insert]
      have h2 : s ∩ ({a} : Finset X) = ∅ := by
        ext b
        simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false,
          not_and]
        intro hb
        intro hc
        exact has (hc ▸ hb)
      rw [h1, h2] at h
      exact h
    have hea : g (insert a (∅ : Finset X)) = g ({a} : Finset X) := by
      congr 1
    rw [hea] at ih2
    nlinarith [ih1, ih2, hsub, hp0, hq0, mul_nonneg hp0 hq0]

/-- Lemma 2.3 of Feige–Mirrokni–Vondrák. -/
private theorem two_sample_core {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : Submodular f) (A B : Finset X) (p q : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - p) * (1 - q) * f ∅ + p * (1 - q) * f A + (1 - p) * q * f B + p * q * f (A ∪ B) ≤
      ∑ S ∈ A.powerset, ∑ T ∈ B.powerset, wt p A S * wt q B T * f (S ∪ T) := by
  have hq0' : (0:ℝ) ≤ 1 - q := by linarith
  -- inner sum: apply Lemma 2.2 to `T ↦ f (S ∪ T)`
  have hinner : ∀ S ∈ A.powerset,
      (1 - q) * f S + q * f (S ∪ B) ≤ ∑ T ∈ B.powerset, wt q B T * f (S ∪ T) := by
    intro S _
    have h := sample_core q hq0 hq1 B (fun T => f (S ∪ T)) (submodular_union hf S)
    have h0 : (S ∪ (∅ : Finset X)) = S := by simp
    rw [h0] at h
    exact h
  have hstep1 : ∑ S ∈ A.powerset, wt p A S * ((1 - q) * f S + q * f (S ∪ B))
      ≤ ∑ S ∈ A.powerset, ∑ T ∈ B.powerset, wt p A S * wt q B T * f (S ∪ T) := by
    refine Finset.sum_le_sum fun S hS => ?_
    have h1 := hinner S hS
    have h2 : ∑ T ∈ B.powerset, wt p A S * wt q B T * f (S ∪ T)
        = wt p A S * ∑ T ∈ B.powerset, wt q B T * f (S ∪ T) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (wt_nonneg p hp0 hp1 A S)
  -- outer sums: apply Lemma 2.2 to `f` and to `S ↦ f (S ∪ B)`
  have hA1 := sample_core p hp0 hp1 A f hf
  have hsubB : Submodular (fun S => f (B ∪ S)) := submodular_union hf B
  have hA2 := sample_core p hp0 hp1 A (fun S => f (B ∪ S)) hsubB
  have hcomm : ∀ S : Finset X, (B ∪ S) = (S ∪ B) := fun S => Finset.union_comm B S
  simp only [hcomm] at hA2
  have hBe : ((∅ : Finset X) ∪ B) = B := by simp
  rw [hBe] at hA2
  have hexp : ∑ S ∈ A.powerset, wt p A S * ((1 - q) * f S + q * f (S ∪ B))
      = (1 - q) * (∑ S ∈ A.powerset, wt p A S * f S)
        + q * (∑ S ∈ A.powerset, wt p A S * f (S ∪ B)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => by ring
  rw [hexp] at hstep1
  nlinarith [hstep1, hA1, hA2, hq0, hq0', mul_nonneg hp0 hq0]

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) (A B : Finset X) (p q : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - p) * (1 - q) * f ∅ + p * (1 - q) * f A + (1 - p) * q * f B + p * q * f (A ∪ B) ≤
      ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
        (p ^ S.card * (1 - p) ^ (A \ S).card) * (q ^ T.card * (1 - q) ^ (B \ T).card) *
          f (S ∪ T) := by
  have h := two_sample_core f hf A B p q hp0 hp1 hq0 hq1
  simpa [wt] using h
