-- Prove2me | solution 1 for NashBargaining.nash_bargaining_solution_unique
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:27:18.445339+00:00
-- url     : https://prove2.me/submissions/8833ff1f-88c6-457f-b11b-2de5100662db

import Mathlib
import Theorems.Thm_NashBargainingProblem_Axiomatic_nash_product_maximizer_exists_unique
import Theorems.Thm_NashBargainingProblem_Axiomatic_nash_axioms_force_nash_product_max

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NashWork

theorem nash_product_maximizer_exists_unique (S : Set (ℝ × ℝ))
    (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) (hS_zero : ((0 : ℝ), (0 : ℝ)) ∈ S)
    (hS_gain : ∃ s ∈ S, 0 < s.1 ∧ 0 < s.2) :
    ∃! p : ℝ × ℝ, p ∈ S ∧ 0 < p.1 ∧ 0 < p.2 ∧
      ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2 :=
  NashBargainingProblem.Axiomatic.nash_product_maximizer_exists_unique S hS_compact hS_convex hS_zero hS_gain

theorem nash_axioms_force_nash_product_max
    (B : Set (Set (ℝ × ℝ) × (ℝ × ℝ)))
    (hB : B = {P | IsCompact P.1 ∧ Convex ℝ P.1 ∧ P.2 ∈ P.1 ∧
      ∃ s ∈ P.1, P.2.1 < s.1 ∧ P.2.2 < s.2})
    (g : B → ℝ × ℝ)
    -- g is a bargaining solution: it selects a point of S
    (h_sel : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), g ⟨(S, d), h⟩ ∈ S)
    -- INV: invariance under positive affine rescalings of the two utilities
    (h_inv : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B)
            (α₁ α₂ β₁ β₂ : ℝ) (L : ℝ × ℝ → ℝ × ℝ), 0 < α₁ → 0 < α₂ →
            (∀ s : ℝ × ℝ, L s = (α₁ * s.1 + β₁, α₂ * s.2 + β₂)) →
            ∀ h' : (L '' S, L d) ∈ B, g ⟨(L '' S, L d), h'⟩ = L (g ⟨(S, d), h⟩))
    -- SYM: symmetric problems get symmetric outcomes
    (h_sym : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), d.1 = d.2 →
            (∀ s₁ s₂ : ℝ, (s₁, s₂) ∈ S ↔ (s₂, s₁) ∈ S) →
            (g ⟨(S, d), h⟩).1 = (g ⟨(S, d), h⟩).2)
    -- IIA: independence of irrelevant alternatives
    (h_iia : ∀ (S T : Set (ℝ × ℝ)) (d : ℝ × ℝ) (hS : (S, d) ∈ B) (hT : (T, d) ∈ B),
            S ⊆ T → g ⟨(T, d), hT⟩ ∈ S → g ⟨(S, d), hS⟩ = g ⟨(T, d), hT⟩)
    -- PAR: Pareto efficiency (a point of S strictly improved upon by some t ∈ S is never chosen)
    (h_par : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), ∀ s ∈ S, ∀ t ∈ S,
            s.1 < t.1 → s.2 < t.2 → g ⟨(S, d), h⟩ ≠ s) :
    ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B),
      d.1 ≤ (g ⟨(S, d), h⟩).1 ∧ d.2 ≤ (g ⟨(S, d), h⟩).2 ∧
      ∀ s ∈ S, d.1 ≤ s.1 → d.2 ≤ s.2 → s ≠ g ⟨(S, d), h⟩ →
        (s.1 - d.1) * (s.2 - d.2) <
          ((g ⟨(S, d), h⟩).1 - d.1) * ((g ⟨(S, d), h⟩).2 - d.2) :=
  NashBargainingProblem.Axiomatic.nash_axioms_force_nash_product_max B hB g h_sel h_inv h_sym h_iia h_par

def BSet : Set (Set (ℝ × ℝ) × (ℝ × ℝ)) :=
  {P | IsCompact P.1 ∧ Convex ℝ P.1 ∧ P.2 ∈ P.1 ∧ ∃ s ∈ P.1, P.2.1 < s.1 ∧ P.2.2 < s.2}

theorem affine_mem_BSet {S : Set (ℝ × ℝ)} {d : ℝ × ℝ} (h : (S, d) ∈ BSet)
    (α₁ α₂ β₁ β₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (L : ℝ × ℝ → ℝ × ℝ)
    (hL : ∀ s : ℝ × ℝ, L s = (α₁ * s.1 + β₁, α₂ * s.2 + β₂)) : (L '' S, L d) ∈ BSet := by
  obtain ⟨hc, hv, hd, s0, hs0, hs0a, hs0b⟩ := h
  have hLc : Continuous L := by
    have : L = fun s => (α₁ * s.1 + β₁, α₂ * s.2 + β₂) := funext hL
    rw [this]; fun_prop
  refine ⟨hc.image hLc, ?_, ⟨d, hd, rfl⟩, ⟨L s0, ⟨s0, hs0, rfl⟩, ?_, ?_⟩⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv', rfl⟩ a b ha hb hab
    refine ⟨a • u + b • v, hv hu hv' ha hb hab, ?_⟩
    rw [hL, hL, hL]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linear_combination (-β₁) * hab
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; linear_combination (-β₂) * hab
  · rw [hL, hL]; simp only; nlinarith
  · rw [hL, hL]; simp only; nlinarith

def NashProp (S : Set (ℝ × ℝ)) (d p : ℝ × ℝ) : Prop :=
  p ∈ S ∧ d.1 ≤ p.1 ∧ d.2 ≤ p.2 ∧
    ∀ s ∈ S, d.1 ≤ s.1 → d.2 ≤ s.2 → s ≠ p →
      (s.1 - d.1) * (s.2 - d.2) < (p.1 - d.1) * (p.2 - d.2)

theorem nashProp_unique {S : Set (ℝ × ℝ)} {d p q : ℝ × ℝ} (hp : NashProp S d p)
    (hq : NashProp S d q) : p = q := by
  by_contra hne
  have h1 := hq.2.2.2 p hp.1 hp.2.1 hp.2.2.1 hne
  have h2 := hp.2.2.2 q hq.1 hq.2.1 hq.2.2.1 (Ne.symm hne)
  linarith

theorem exists_nashProp {S : Set (ℝ × ℝ)} {d : ℝ × ℝ} (h : (S, d) ∈ BSet) :
    ∃ p, NashProp S d p := by
  obtain ⟨L1, hL1⟩ : ∃ L : ℝ × ℝ → ℝ × ℝ, ∀ s, L s = (1 * s.1 + (-d.1), 1 * s.2 + (-d.2)) :=
    ⟨_, fun _ => rfl⟩
  have h1 : (L1 '' S, L1 d) ∈ BSet := affine_mem_BSet h 1 1 (-d.1) (-d.2) one_pos one_pos L1 hL1
  have hd0 : L1 d = ((0 : ℝ), (0 : ℝ)) := by rw [hL1]; ext <;> simp
  obtain ⟨hc1, hv1, hd1, s1, hs1, hs1a, hs1b⟩ := h1
  rw [hd0] at hd1 hs1a hs1b
  obtain ⟨p0, ⟨hp0S, hp01, hp02, hp0max⟩, -⟩ :=
    nash_product_maximizer_exists_unique (L1 '' S) hc1 hv1 hd1 ⟨s1, hs1, hs1a, hs1b⟩
  obtain ⟨P, hPS, rfl⟩ := hp0S
  have hP1 : 0 < (L1 P).1 := hp01
  have hP2 : 0 < (L1 P).2 := hp02
  rw [hL1] at hP1 hP2
  simp only at hP1 hP2
  refine ⟨P, hPS, by linarith, by linarith, ?_⟩
  intro s hs hs1' hs2' hne
  have := hp0max (L1 s) ⟨s, hs, rfl⟩ (by rw [hL1]; simp only; linarith)
    (by rw [hL1]; simp only; linarith) (fun h' => hne (by
      have := congrArg (fun x => x) h'
      rw [hL1, hL1] at this
      simp only [Prod.mk.injEq] at this
      exact Prod.ext (by linarith [this.1]) (by linarith [this.2])))
  rw [hL1, hL1] at this
  simp only at this
  nlinarith

theorem nash_bargaining_solution_unique (B : Set (Set (ℝ × ℝ) × (ℝ × ℝ)))
    (hB : B = {P | IsCompact P.1 ∧ Convex ℝ P.1 ∧ P.2 ∈ P.1 ∧
      ∃ s ∈ P.1, P.2.1 < s.1 ∧ P.2.2 < s.2}) :
    ∃ f : B → ℝ × ℝ,
      (∀ g : B → ℝ × ℝ,
        (-- g is a bargaining solution: it selects a point of S
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), g ⟨(S, d), h⟩ ∈ S) ∧
         -- INV: invariance under positive affine rescalings of the two utilities
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B)
            (α₁ α₂ β₁ β₂ : ℝ) (L : ℝ × ℝ → ℝ × ℝ), 0 < α₁ → 0 < α₂ →
            (∀ s : ℝ × ℝ, L s = (α₁ * s.1 + β₁, α₂ * s.2 + β₂)) →
            ∀ h' : (L '' S, L d) ∈ B, g ⟨(L '' S, L d), h'⟩ = L (g ⟨(S, d), h⟩)) ∧
         -- SYM: symmetric problems get symmetric outcomes
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), d.1 = d.2 →
            (∀ s₁ s₂ : ℝ, (s₁, s₂) ∈ S ↔ (s₂, s₁) ∈ S) →
            (g ⟨(S, d), h⟩).1 = (g ⟨(S, d), h⟩).2) ∧
         -- IIA: independence of irrelevant alternatives
         (∀ (S T : Set (ℝ × ℝ)) (d : ℝ × ℝ) (hS : (S, d) ∈ B) (hT : (T, d) ∈ B),
            S ⊆ T → g ⟨(T, d), hT⟩ ∈ S → g ⟨(S, d), hS⟩ = g ⟨(T, d), hT⟩) ∧
         -- PAR: Pareto efficiency (a point of S strictly improved upon by some t ∈ S is never chosen)
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), ∀ s ∈ S, ∀ t ∈ S,
            s.1 < t.1 → s.2 < t.2 → g ⟨(S, d), h⟩ ≠ s))
        ↔ g = f) ∧
      -- the unique such solution is the maximizer of the Nash product
      ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B),
        d.1 ≤ (f ⟨(S, d), h⟩).1 ∧ d.2 ≤ (f ⟨(S, d), h⟩).2 ∧
        ∀ s ∈ S, d.1 ≤ s.1 → d.2 ≤ s.2 → s ≠ f ⟨(S, d), h⟩ →
          (s.1 - d.1) * (s.2 - d.2) <
            ((f ⟨(S, d), h⟩).1 - d.1) * ((f ⟨(S, d), h⟩).2 - d.2) := by
  have hB' : B = BSet := hB
  subst hB'
  have hex : ∀ x : BSet, ∃ p, NashProp x.1.1 x.1.2 p := fun x => exists_nashProp x.2
  choose f hf using hex
  have hfuniq : ∀ (x : BSet) p, NashProp x.1.1 x.1.2 p → f x = p :=
    fun x p hp => nashProp_unique (hf x) hp
  have hf' : ∀ S d (h : (S, d) ∈ BSet), NashProp S d (f ⟨(S, d), h⟩) := fun S d h => hf ⟨(S, d), h⟩
  have hfuniq' : ∀ S d (h : (S, d) ∈ BSet) p, NashProp S d p → f ⟨(S, d), h⟩ = p :=
    fun S d h p hp => hfuniq ⟨(S, d), h⟩ p hp
  refine ⟨f, fun g => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨h_sel, h_inv, h_sym, h_iia, h_par⟩
    funext x
    obtain ⟨⟨S, d⟩, h⟩ := x
    have hF := nash_axioms_force_nash_product_max BSet rfl g h_sel h_inv h_sym h_iia h_par S d h
    exact (hfuniq ⟨(S, d), h⟩ _ ⟨h_sel S d h, hF.1, hF.2.1, hF.2.2⟩).symm
  · rintro rfl
    refine ⟨fun S d h => (hf' S d h).1, ?_, ?_, ?_, ?_⟩
    · -- INV
      intro S d h α₁ α₂ β₁ β₂ L hα₁ hα₂ hL h'
      obtain ⟨hPS, hdP1, hdP2, hstrict⟩ := hf' S d h
      refine hfuniq' (L '' S) (L d) h' _ ⟨⟨_, hPS, rfl⟩, ?_, ?_, ?_⟩
      · rw [hL, hL]; simp only; nlinarith [mul_le_mul_of_nonneg_left hdP1 hα₁.le]
      · rw [hL, hL]; simp only; nlinarith [mul_le_mul_of_nonneg_left hdP2 hα₂.le]
      · rintro _ ⟨s, hs, rfl⟩ h1 h2 hne
        rw [hL, hL] at h1 h2
        simp only at h1 h2
        have hs1 : d.1 ≤ s.1 := by nlinarith
        have hs2 : d.2 ≤ s.2 := by nlinarith
        have hsP : s ≠ g ⟨(S, d), h⟩ := fun h'' => hne (by rw [h''])
        have := hstrict s hs hs1 hs2 hsP
        rw [hL, hL, hL]
        simp only
        have hpos : 0 < α₁ * α₂ := mul_pos hα₁ hα₂
        nlinarith
    · -- SYM
      intro S d h hd hS
      have hnp := hf' S d h
      generalize hPdef : g ⟨(S, d), h⟩ = P at hnp ⊢
      obtain ⟨a, b⟩ := P
      obtain ⟨hPS, hdP1, hdP2, hstrict⟩ := hnp
      have hsw : NashProp S d (b, a) := by
        refine ⟨(hS a b).1 hPS, ?_, ?_, ?_⟩
        · simp only at hdP2 ⊢; linarith
        · simp only at hdP1 ⊢; linarith
        · intro s hs h1 h2 hne
          obtain ⟨s1, s2⟩ := s
          simp only at h1 h2 ⊢
          have := hstrict (s2, s1) ((hS s1 s2).1 hs) (by simp only; linarith)
            (by simp only; linarith) (fun h' => hne (by
              simp only [Prod.mk.injEq] at h'; rw [h'.1, h'.2]))
          simp only at this
          have hd' : d.1 = d.2 := hd
          rw [← hd'] at this ⊢
          nlinarith
      have := nashProp_unique ⟨hPS, hdP1, hdP2, hstrict⟩ hsw
      simp only [Prod.mk.injEq] at this
      exact this.1
    · -- IIA
      intro S T d hS hT hST hmem
      obtain ⟨hTS, hd1, hd2, hstr⟩ := hf' T d hT
      exact hfuniq' S d hS _ ⟨hmem, hd1, hd2, fun s hs h1 h2 hne => hstr s (hST hs) h1 h2 hne⟩
    · -- PAR
      intro S d h s hs t ht h1 h2 heq
      have hnp := hf' S d h
      rw [heq] at hnp
      obtain ⟨_, hd1, hd2, hstr⟩ := hnp
      have hne : t ≠ s := fun h' => by rw [h'] at h1; exact lt_irrefl _ h1
      have := hstr t ht (by linarith) (by linarith) hne
      nlinarith [mul_nonneg (sub_nonneg.2 hd1) (sub_nonneg.2 hd2),
        mul_pos (sub_pos.2 h1) (sub_pos.2 h2),
        mul_nonneg (sub_nonneg.2 hd1) (sub_nonneg.2 h2.le),
        mul_nonneg (sub_nonneg.2 hd2) (sub_nonneg.2 h1.le)]
  · intro S d h
    obtain ⟨_, hd1, hd2, hstr⟩ := hf' S d h
    exact ⟨hd1, hd2, hstr⟩

end NashWork

theorem solution
    (B : Set (Set (ℝ × ℝ) × (ℝ × ℝ)))
    (hB : B = {P | IsCompact P.1 ∧ Convex ℝ P.1 ∧ P.2 ∈ P.1 ∧
      ∃ s ∈ P.1, P.2.1 < s.1 ∧ P.2.2 < s.2}) :
    ∃ f : B → ℝ × ℝ,
      (∀ g : B → ℝ × ℝ,
        (-- g is a bargaining solution: it selects a point of S
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), g ⟨(S, d), h⟩ ∈ S) ∧
         -- INV: invariance under positive affine rescalings of the two utilities
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B)
            (α₁ α₂ β₁ β₂ : ℝ) (L : ℝ × ℝ → ℝ × ℝ), 0 < α₁ → 0 < α₂ →
            (∀ s : ℝ × ℝ, L s = (α₁ * s.1 + β₁, α₂ * s.2 + β₂)) →
            ∀ h' : (L '' S, L d) ∈ B, g ⟨(L '' S, L d), h'⟩ = L (g ⟨(S, d), h⟩)) ∧
         -- SYM: symmetric problems get symmetric outcomes
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), d.1 = d.2 →
            (∀ s₁ s₂ : ℝ, (s₁, s₂) ∈ S ↔ (s₂, s₁) ∈ S) →
            (g ⟨(S, d), h⟩).1 = (g ⟨(S, d), h⟩).2) ∧
         -- IIA: independence of irrelevant alternatives
         (∀ (S T : Set (ℝ × ℝ)) (d : ℝ × ℝ) (hS : (S, d) ∈ B) (hT : (T, d) ∈ B),
            S ⊆ T → g ⟨(T, d), hT⟩ ∈ S → g ⟨(S, d), hS⟩ = g ⟨(T, d), hT⟩) ∧
         -- PAR: Pareto efficiency (a point of S strictly improved upon by some t ∈ S is never chosen)
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), ∀ s ∈ S, ∀ t ∈ S,
            s.1 < t.1 → s.2 < t.2 → g ⟨(S, d), h⟩ ≠ s))
        ↔ g = f) ∧
      -- the unique such solution is the maximizer of the Nash product
      ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B),
        d.1 ≤ (f ⟨(S, d), h⟩).1 ∧ d.2 ≤ (f ⟨(S, d), h⟩).2 ∧
        ∀ s ∈ S, d.1 ≤ s.1 → d.2 ≤ s.2 → s ≠ f ⟨(S, d), h⟩ →
          (s.1 - d.1) * (s.2 - d.2) <
            ((f ⟨(S, d), h⟩).1 - d.1) * ((f ⟨(S, d), h⟩).2 - d.2) :=
  NashWork.nash_bargaining_solution_unique B hB

#print axioms solution
