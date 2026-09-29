-- Prove2me | solution 1 for MaxLatticeFree.Inequalities.minimal_valid_inequalities_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T20:14:11.093952+00:00
-- url     : https://prove2.me/submissions/cf53aff1-8d88-487d-a03e-f7bc169a4ee1

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
import Definitions.Def_MaxLatticeFree_Inequalities_Polar

open MaxLatticeFree.Inequalities in
lemma p4e_combo_eq {q : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (s : W →₀ ℝ) :
    combo W s = Finsupp.linearCombination ℝ (fun r : W => (r : EuclideanSpace ℝ (Fin q))) s := by
  simp [combo, Finsupp.linearCombination_apply]

open MaxLatticeFree.Inequalities in
lemma p4e_linVal_eq {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ : W → ℝ) (s : W →₀ ℝ) :
    linVal ψ s = Finsupp.linearCombination ℝ ψ s := by
  simp only [linVal, Finsupp.linearCombination_apply, smul_eq_mul]
  exact Finsupp.sum_congr (fun x _ => mul_comm _ _)

open MaxLatticeFree.Inequalities in
lemma p4e_combo_mem {q : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (s : W →₀ ℝ) :
    combo W s ∈ W := by
  unfold combo
  exact Submodule.sum_mem _ (fun r _ => W.smul_mem _ r.2)

open MaxLatticeFree.Inequalities in
lemma p4e_combo_single {q : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (r : W) (c : ℝ) :
    combo W (Finsupp.single r c) = c • (r : EuclideanSpace ℝ (Fin q)) := by
  simp [combo]

open MaxLatticeFree.Inequalities in
lemma p4e_linVal_single {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ : W → ℝ) (r : W) (c : ℝ) :
    linVal ψ (Finsupp.single r c) = ψ r * c := by
  simp [linVal]

open MaxLatticeFree.Inequalities in
lemma p4e_combo_add {q : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (s t : W →₀ ℝ) :
    combo W (s + t) = combo W s + combo W t := by
  rw [p4e_combo_eq, p4e_combo_eq, p4e_combo_eq, map_add]

open MaxLatticeFree.Inequalities in
lemma p4e_combo_smul {q : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (c : ℝ) (s : W →₀ ℝ) :
    combo W (c • s) = c • combo W s := by
  rw [p4e_combo_eq, p4e_combo_eq, map_smul]

open MaxLatticeFree.Inequalities in
lemma p4e_linVal_add {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ : W → ℝ) (s t : W →₀ ℝ) :
    linVal ψ (s + t) = linVal ψ s + linVal ψ t := by
  rw [p4e_linVal_eq, p4e_linVal_eq, p4e_linVal_eq, map_add]

open MaxLatticeFree.Inequalities in
lemma p4e_linVal_smul {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ : W → ℝ) (c : ℝ) (s : W →₀ ℝ) :
    linVal ψ (c • s) = c * linVal ψ s := by
  rw [p4e_linVal_eq, p4e_linVal_eq, map_smul, smul_eq_mul]

open MaxLatticeFree.Inequalities in
lemma p4e_linVal_mono {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ ψ' : W → ℝ)
    (h : ∀ r, ψ r ≤ ψ' r) (s : W →₀ ℝ) (hs : ∀ r, 0 ≤ s r) : linVal ψ s ≤ linVal ψ' s := by
  unfold linVal
  exact Finsupp.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_right (h r) (hs r))

open MaxLatticeFree.Inequalities in
lemma p4e_valid_two {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {ψ : W → ℝ} {α : ℝ} (hv : IsValid f W ψ α) (a b : W) (c1 c2 : ℝ) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (hint : f + (c1 • (a : EuclideanSpace ℝ (Fin q)) + c2 • (b : EuclideanSpace ℝ (Fin q))) ∈ integralPoints q) :
    α ≤ c1 * ψ a + c2 * ψ b := by
  have := hv (Finsupp.single a c1 + Finsupp.single b c2) ⟨by
    rw [p4e_combo_add, p4e_combo_single, p4e_combo_single]; exact hint, by
    intro r
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> linarith⟩
  rw [p4e_linVal_add, p4e_linVal_single, p4e_linVal_single] at this
  linarith [mul_comm (ψ a) c1, mul_comm (ψ b) c2]

open MaxLatticeFree.Inequalities in
lemma p4e_valid_single {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {ψ : W → ℝ} {α : ℝ} (hv : IsValid f W ψ α) (x : EuclideanSpace ℝ (Fin q)) (hx : x - f ∈ W)
    (hxi : x ∈ integralPoints q) : α ≤ ψ ⟨x - f, hx⟩ := by
  have := hv (Finsupp.single ⟨x - f, hx⟩ 1) ⟨by
    rw [p4e_combo_single]; simpa using hxi, by
    intro r
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num⟩
  rw [p4e_linVal_single] at this
  linarith
lemma p4e_chain_min {ι : Type*} (c : Set (ι → ℝ)) (hc : ∀ a ∈ c, ∀ b ∈ c, a ≤ b ∨ b ≤ a)
    (hne : c.Nonempty) (T : Finset (ι → ℝ)) (hT : ∀ a ∈ T, a ∈ c) :
    ∃ b ∈ c, ∀ a ∈ T, b ≤ a := by
  classical
  induction T using Finset.induction_on with
  | empty => obtain ⟨b, hb⟩ := hne; exact ⟨b, hb, by simp⟩
  | insert a T haT ih =>
    obtain ⟨b, hbc, hb⟩ := ih (fun x hx => hT x (Finset.mem_insert_of_mem hx))
    have haC : a ∈ c := hT a (Finset.mem_insert_self _ _)
    rcases hc a haC b hbc with h | h
    · refine ⟨a, haC, ?_⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · exact h.trans (hb x hx)
    · refine ⟨b, hbc, ?_⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h
      · exact hb x hx

open MaxLatticeFree.Inequalities in
lemma p4e_lower_bound {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {ψ ψ' : W → ℝ} {α : ℝ} (z : EuclideanSpace ℝ (Fin q)) (hzW : z - f ∈ W) (hzi : z ∈ integralPoints q)
    (hv' : IsValid f W ψ' α) (hd : ∀ r, ψ' r ≤ ψ r) (r : W) :
    α - ψ ⟨z - f - (r : EuclideanSpace ℝ (Fin q)), W.sub_mem hzW r.2⟩ ≤ ψ' r := by
  have h := p4e_valid_two hv' r ⟨z - f - (r : EuclideanSpace ℝ (Fin q)), W.sub_mem hzW r.2⟩ 1 1
    zero_le_one zero_le_one (by
      have : f + ((1:ℝ) • (r : EuclideanSpace ℝ (Fin q)) + (1:ℝ) • (z - f - (r : EuclideanSpace ℝ (Fin q)))) = z := by
        simp only [one_smul]; abel
      rw [this]; exact hzi)
  have := hd ⟨z - f - (r : EuclideanSpace ℝ (Fin q)), W.sub_mem hzW r.2⟩
  linarith

open MaxLatticeFree.Inequalities in
lemma p4e_part1 {q : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (hf : (affSpace f W ∩ integralPoints q).Nonempty)
    (ψ : W → ℝ) (α : ℝ) (hv : IsValid f W ψ α) (hnt : ¬ IsTrivial f W ψ α) :
    ∃ ψ' : W → ℝ, IsMinimal f W ψ' α ∧ ¬ IsTrivial f W ψ' α ∧ Dominates ψ' ψ := by
  classical
  obtain ⟨z, hzA, hzi⟩ := hf
  have hzW : z - f ∈ W := hzA
  let S := {ψ' : W → ℝ // IsValid f W ψ' α ∧ Dominates ψ' ψ}
  have : Nonempty S := ⟨⟨ψ, hv, fun r => le_rfl⟩⟩
  have hbound : ∀ c : Set S, IsChain (fun a b : S => b.1 ≤ a.1) c → c.Nonempty →
      ∃ ub : S, ∀ a ∈ c, ub.1 ≤ a.1 := by
    intro c hc hne
    obtain ⟨a0, ha0⟩ := hne
    have : Nonempty c := ⟨⟨a0, ha0⟩⟩
    let g : W → ℝ := fun r => ⨅ a : c, (a.1.1 : W → ℝ) r
    have hbdd : ∀ r, BddBelow (Set.range fun a : c => (a.1.1 : W → ℝ) r) := by
      intro r
      refine ⟨α - ψ ⟨z - f - (r : EuclideanSpace ℝ (Fin q)), W.sub_mem hzW r.2⟩, ?_⟩
      rintro _ ⟨a, rfl⟩
      exact p4e_lower_bound z hzW hzi a.1.2.1 a.1.2.2 r
    have hgle : ∀ a ∈ c, ∀ r, g r ≤ a.1 r := fun a ha r => ciInf_le (hbdd r) ⟨a, ha⟩
    have hgψ : Dominates g ψ := fun r => (hgle a0 ha0 r).trans (a0.2.2 r)
    refine ⟨⟨g, ?_, hgψ⟩, fun a ha r => hgle a ha r⟩
    intro s hs
    apply le_of_forall_pos_le_add
    intro ε hε
    set M : ℝ := ∑ r ∈ s.support, s r with hM
    have hM0 : 0 ≤ M := Finset.sum_nonneg (fun r _ => hs.2 r)
    set δ : ℝ := ε / (M + 1) with hδ
    have hδ0 : 0 < δ := div_pos hε (by linarith)
    have hex : ∀ r, ∃ a : c, (a.1.1 : W → ℝ) r < g r + δ := by
      intro r
      exact exists_lt_of_ciInf_lt (by show g r < g r + δ; linarith)
    choose A hA using hex
    have hchain : ∀ a ∈ (fun a : S => a.1) '' c, ∀ b ∈ (fun a : S => a.1) '' c, a ≤ b ∨ b ≤ a := by
      rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩
      by_cases h : a₁ = a₂
      · subst h; exact Or.inl le_rfl
      · rcases hc ha₁ ha₂ h with h | h
        · exact Or.inr h
        · exact Or.inl h
    obtain ⟨b, ⟨a', ha'c, rfl⟩, hb⟩ := p4e_chain_min ((fun a : S => a.1) '' c) hchain
      ⟨a0.1, a0, ha0, rfl⟩ (s.support.image (fun r => (A r).1.1)) (by
        intro x hx
        obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hx
        exact ⟨(A r).1, (A r).2, rfl⟩)
    have hlt : ∀ r ∈ s.support, a'.1 r < g r + δ := by
      intro r hr
      have := hb ((A r).1.1) (Finset.mem_image.2 ⟨r, hr, rfl⟩) r
      exact lt_of_le_of_lt this (hA r)
    have h1 : linVal a'.1 s ≤ linVal g s + δ * M := by
      unfold linVal Finsupp.sum
      calc ∑ r ∈ s.support, a'.1 r * s r ≤ ∑ r ∈ s.support, (g r + δ) * s r :=
            Finset.sum_le_sum (fun r hr =>
              mul_le_mul_of_nonneg_right (le_of_lt (hlt r hr)) (hs.2 r))
        _ = ∑ r ∈ s.support, g r * s r + δ * M := by
            rw [hM]; simp only [add_mul]; rw [Finset.sum_add_distrib, Finset.mul_sum]
    have h2 : δ * M ≤ ε := by
      rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    have h3 := a'.2.1 s hs
    linarith
  obtain ⟨m, hm⟩ := exists_maximal_of_nonempty_chains_bounded (α := S)
    (r := fun a b => b.1 ≤ a.1) hbound (fun {a b c} hab hbc => hbc.trans hab)
  refine ⟨m.1, ⟨m.2.1, ?_⟩, ?_, m.2.2⟩
  · intro ψ'' hv'' hd''
    have h1 : m.1 ≤ ψ'' := hm ⟨ψ'', hv'', fun r => (hd'' r).trans (m.2.2 r)⟩ hd''
    exact funext fun r => le_antisymm (hd'' r) (h1 r)
  · intro hT
    apply hnt
    intro s hs hs0
    exact (hT s hs hs0).trans (p4e_linVal_mono m.1 ψ m.2.2 s hs0)

open MaxLatticeFree.Inequalities in
lemma p4e_single_nonneg {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (r : W) (c : ℝ)
    (hc : 0 ≤ c) (x : W) : 0 ≤ Finsupp.single r c x := by
  rw [Finsupp.single_apply]; split_ifs
  · exact hc
  · exact le_rfl

open MaxLatticeFree.Inequalities in
lemma p4e_rep_bdd {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {ψ : W → ℝ} {α : ℝ} (z : EuclideanSpace ℝ (Fin q)) (hzW : z - f ∈ W) (hzi : z ∈ integralPoints q)
    (hv : IsValid f W ψ α) (r : W) (t : W →₀ ℝ) (ht : ∀ x, 0 ≤ t x)
    (hc : combo W t = (r : EuclideanSpace ℝ (Fin q))) :
    α - ψ ⟨z - f - (r : EuclideanSpace ℝ (Fin q)), W.sub_mem hzW r.2⟩ ≤ linVal ψ t := by
  have h := hv (t + Finsupp.single ⟨z - f - (r : EuclideanSpace ℝ (Fin q)), W.sub_mem hzW r.2⟩ 1) ⟨by
    rw [p4e_combo_add, p4e_combo_single, hc]
    have : f + ((r : EuclideanSpace ℝ (Fin q)) + (1:ℝ) • (z - f - (r : EuclideanSpace ℝ (Fin q)))) = z := by
      simp only [one_smul]; abel
    rw [this]; exact hzi, by
    intro x
    rw [Finsupp.add_apply]
    exact add_nonneg (ht x) (p4e_single_nonneg _ _ zero_le_one x)⟩
  rw [p4e_linVal_add, p4e_linVal_single] at h
  linarith

open MaxLatticeFree.Inequalities in
lemma p4e_rep {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) {ψ : W → ℝ} {α : ℝ} (hm : IsMinimal f W ψ α)
    (r : W) (t : W →₀ ℝ) (ht : ∀ x, 0 ≤ t x) (hc : combo W t = (r : EuclideanSpace ℝ (Fin q))) :
    ψ r ≤ linVal ψ t := by
  classical
  obtain ⟨z, hzA, hzi⟩ := hf
  have hzW : z - f ∈ W := hzA
  let R : W → Set ℝ := fun r => {x | ∃ t : W →₀ ℝ, (∀ y, 0 ≤ t y) ∧
    combo W t = (r : EuclideanSpace ℝ (Fin q)) ∧ x = linVal ψ t}
  have hRne : ∀ r, (R r).Nonempty := fun r =>
    ⟨_, Finsupp.single r 1, fun y => p4e_single_nonneg r 1 zero_le_one y, by
      rw [p4e_combo_single]; simp, rfl⟩
  have hRbdd : ∀ r, BddBelow (R r) := by
    intro r
    refine ⟨α - ψ ⟨z - f - (r : EuclideanSpace ℝ (Fin q)), W.sub_mem hzW r.2⟩, ?_⟩
    rintro _ ⟨t, ht0, htc, rfl⟩
    exact p4e_rep_bdd z hzW hzi hm.1 r t ht0 htc
  let ψ' : W → ℝ := fun r => sInf (R r)
  have hdom : ∀ r, ψ' r ≤ ψ r := by
    intro r
    have := csInf_le (hRbdd r) (show linVal ψ (Finsupp.single r 1) ∈ R r from
      ⟨Finsupp.single r 1, fun y => p4e_single_nonneg r 1 zero_le_one y, by
        rw [p4e_combo_single]; simp, rfl⟩)
    rw [p4e_linVal_single] at this
    simpa using this
  have hval : IsValid f W ψ' α := by
    intro s hs
    apply le_of_forall_pos_le_add
    intro ε hε
    set M : ℝ := ∑ r ∈ s.support, s r with hM
    have hM0 : 0 ≤ M := Finset.sum_nonneg (fun r _ => hs.2 r)
    set δ : ℝ := ε / (M + 1) with hδ
    have hδ0 : 0 < δ := div_pos hε (by linarith)
    have hex : ∀ r : W, ∃ t : W →₀ ℝ, (∀ y, 0 ≤ t y) ∧ combo W t = (r : EuclideanSpace ℝ (Fin q)) ∧
        linVal ψ t < ψ' r + δ := by
      intro r
      obtain ⟨x, ⟨t, ht0, htc, rfl⟩, hx⟩ := exists_lt_of_csInf_lt (hRne r)
        (show sInf (R r) < sInf (R r) + δ by linarith)
      exact ⟨t, ht0, htc, hx⟩
    choose t ht0 htc htl using hex
    let T : W →₀ ℝ := s.sum (fun r c => c • t r)
    have hT0 : ∀ y, 0 ≤ T y := by
      intro y
      simp only [T, Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg (fun r _ => mul_nonneg (hs.2 r) (ht0 r y))
    have hTc : combo W T = combo W s := by
      rw [p4e_combo_eq]
      simp only [T]
      rw [map_finsuppSum]
      simp only [map_smul, ← p4e_combo_eq, htc]
      rfl
    have hTl : linVal ψ T = ∑ r ∈ s.support, s r * linVal ψ (t r) := by
      rw [p4e_linVal_eq]
      simp only [T]
      rw [map_finsuppSum]
      simp only [map_smul, ← p4e_linVal_eq, smul_eq_mul]
      rfl
    have h1 := hm.1 T ⟨by rw [hTc]; exact hs.1, hT0⟩
    have h2 : linVal ψ T ≤ linVal ψ' s + δ * M := by
      rw [hTl]
      unfold linVal Finsupp.sum
      calc ∑ r ∈ s.support, s r * linVal ψ (t r) ≤ ∑ r ∈ s.support, (ψ' r + δ) * s r :=
            Finset.sum_le_sum (fun r hr => by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right (le_of_lt (htl r)) (hs.2 r))
        _ = ∑ r ∈ s.support, ψ' r * s r + δ * M := by
            rw [hM]; simp only [add_mul]; rw [Finset.sum_add_distrib, Finset.mul_sum]
    have h3 : δ * M ≤ ε := by
      rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have heq : ψ' = ψ := hm.2 ψ' hval hdom
  have := csInf_le (hRbdd r) (show linVal ψ t ∈ R r from ⟨t, ht, hc, rfl⟩)
  have h5 : ψ' r = ψ r := by rw [heq]
  calc ψ r = ψ' r := h5.symm
    _ ≤ linVal ψ t := this

open MaxLatticeFree.Inequalities in
lemma p4e_zero_nonneg {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) {ψ : W → ℝ} {α : ℝ} (hv : IsValid f W ψ α) :
    0 ≤ ψ 0 := by
  obtain ⟨z, hzA, hzi⟩ := hf
  have hzW : z - f ∈ W := hzA
  by_contra hneg'
  have hneg : ψ 0 < 0 := not_le.mp hneg'
  set X := ψ ⟨z - f, hzW⟩ - α + 1
  have h := p4e_valid_two hv 0 ⟨z - f, hzW⟩ (|X| / (-ψ 0)) 1 (div_nonneg (abs_nonneg _) (by linarith))
    zero_le_one (by
      have : f + ((|X| / (-ψ 0)) • ((0 : W) : EuclideanSpace ℝ (Fin q)) + (1:ℝ) • (z - f)) = z := by
        simp
      simpa using hzi)
  have h2 : |X| / (-ψ 0) * ψ 0 = -|X| := by
    rw [div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.2 hneg.ne)]; ring
  rw [h2] at h
  have := neg_abs_le X
  linarith [le_abs_self X]

open MaxLatticeFree.Inequalities in
lemma p4e_sublinear {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) {ψ : W → ℝ} {α : ℝ} (hm : IsMinimal f W ψ α) :
    IsSublinear ψ := by
  have hsmul : ∀ (r : W) (c : ℝ), 0 < c → ψ (c • r) ≤ c * ψ r := by
    intro r c hc
    have := p4e_rep hf hm (c • r) (Finsupp.single r c) (fun x => p4e_single_nonneg r c hc.le x) (by
      rw [p4e_combo_single]; rfl)
    rw [p4e_linVal_single] at this
    linarith [mul_comm (ψ r) c]
  refine ⟨?_, ?_⟩
  · intro r c hc
    rcases hc.eq_or_lt with h | h
    · subst h
      have h0 : ψ 0 = 0 := by
        have h1 := p4e_rep hf hm 0 0 (fun x => le_rfl) (by simp [combo])
        have h2 := p4e_zero_nonneg hf hm.1
        have : linVal ψ (0 : W →₀ ℝ) = 0 := by simp [linVal]
        linarith
      simp [h0]
    · refine le_antisymm (hsmul r c h) ?_
      have := hsmul (c • r) c⁻¹ (inv_pos.2 h)
      rw [smul_smul, inv_mul_cancel₀ h.ne', one_smul] at this
      have h3 : c * ψ r ≤ c * (c⁻¹ * ψ (c • r)) := mul_le_mul_of_nonneg_left this h.le
      rw [← mul_assoc, mul_inv_cancel₀ h.ne', one_mul] at h3
      exact h3
  · intro r₁ r₂
    have := p4e_rep hf hm (r₁ + r₂) (Finsupp.single r₁ 1 + Finsupp.single r₂ 1)
      (fun x => by
        rw [Finsupp.add_apply]
        exact add_nonneg (p4e_single_nonneg _ _ zero_le_one x) (p4e_single_nonneg _ _ zero_le_one x))
      (by rw [p4e_combo_add, p4e_combo_single, p4e_combo_single]; simp)
    rw [p4e_linVal_add, p4e_linVal_single, p4e_linVal_single] at this
    linarith

open MaxLatticeFree.Inequalities in
lemma p4e_mem_int {q : ℕ} (x : EuclideanSpace ℝ (Fin q)) :
    x ∈ integralPoints q ↔ ∀ i, ∃ z : ℤ, x.ofLp i = (z : ℝ) := Iff.rfl

open MaxLatticeFree.Inequalities in
lemma p4e_int_zero {q : ℕ} : (0 : EuclideanSpace ℝ (Fin q)) ∈ integralPoints q := by
  rw [p4e_mem_int]; intro i; exact ⟨0, by simp⟩

open MaxLatticeFree.Inequalities in
lemma p4e_int_add {q : ℕ} {x y : EuclideanSpace ℝ (Fin q)} (hx : x ∈ integralPoints q)
    (hy : y ∈ integralPoints q) : x + y ∈ integralPoints q := by
  rw [p4e_mem_int] at *
  intro i
  obtain ⟨a, ha⟩ := hx i
  obtain ⟨b, hb⟩ := hy i
  exact ⟨a + b, by simp [ha, hb]⟩

open MaxLatticeFree.Inequalities in
lemma p4e_int_smul {q : ℕ} {x : EuclideanSpace ℝ (Fin q)} (hx : x ∈ integralPoints q) (k : ℤ) :
    (k : ℝ) • x ∈ integralPoints q := by
  rw [p4e_mem_int] at *
  intro i
  obtain ⟨a, ha⟩ := hx i
  exact ⟨k * a, by simp [ha]⟩

open MaxLatticeFree.Inequalities in
lemma p4e_int_sub {q : ℕ} {x y : EuclideanSpace ℝ (Fin q)} (hx : x ∈ integralPoints q)
    (hy : y ∈ integralPoints q) : x - y ∈ integralPoints q := by
  have := p4e_int_add hx (p4e_int_smul hy (-1))
  simpa [sub_eq_add_neg] using this

open MaxLatticeFree.Inequalities in
lemma p4e_int_sum {q : ℕ} {ι : Type*} (T : Finset ι) (v : ι → EuclideanSpace ℝ (Fin q))
    (hv : ∀ i ∈ T, v i ∈ integralPoints q) : ∑ i ∈ T, v i ∈ integralPoints q :=
  Finset.sum_induction v (fun x => x ∈ integralPoints q) (fun _ _ ha hb => p4e_int_add ha hb)
    p4e_int_zero hv

open MaxLatticeFree.Inequalities in
lemma p4e_sub_sum {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} {ψ : W → ℝ}
    (hsub : IsSublinear ψ) {ι : Type*} (T : Finset ι) (c : ι → ℝ) (v : ι → W)
    (hc : ∀ i ∈ T, 0 ≤ c i) : ψ (∑ i ∈ T, c i • v i) ≤ ∑ i ∈ T, c i * ψ (v i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have := hsub.1 0 0 le_rfl
    simp at this ⊢
    linarith
  | insert a T haT ih =>
    rw [Finset.sum_insert haT, Finset.sum_insert haT]
    have h1 := hsub.2 (c a • v a) (∑ i ∈ T, c i • v i)
    have h2 := hsub.1 (v a) (c a) (hc a (Finset.mem_insert_self _ _))
    have h3 := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
    linarith

open MaxLatticeFree.Inequalities in
lemma p4e_lattice_nonneg {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) {ψ : W → ℝ} {α : ℝ} (hv : IsValid f W ψ α)
    (w : W) (hw : (w : EuclideanSpace ℝ (Fin q)) ∈ integralPoints q) : 0 ≤ ψ w := by
  obtain ⟨z, hzA, hzi⟩ := hf
  have hzW : z - f ∈ W := hzA
  by_contra hneg'
  have hneg : ψ w < 0 := not_le.mp hneg'
  set X := ψ ⟨z - f, hzW⟩ - α + 1
  obtain ⟨n, hn⟩ := exists_nat_ge (|X| / (-ψ w))
  have h := p4e_valid_two hv w ⟨z - f, hzW⟩ (n : ℝ) 1 (Nat.cast_nonneg n) zero_le_one (by
    have : f + ((n : ℝ) • (w : EuclideanSpace ℝ (Fin q)) + (1:ℝ) • (z - f)) = z + (n : ℝ) • (w : EuclideanSpace ℝ (Fin q)) := by
      simp only [one_smul]; abel
    rw [this]
    have h2 := p4e_int_smul hw (n : ℤ)
    simp only [Int.cast_natCast] at h2
    exact p4e_int_add hzi h2)
  have h4 : |X| ≤ n * (-ψ w) := by
    have := (div_le_iff₀ (by linarith : 0 < -ψ w)).1 hn
    exact this
  linarith [le_abs_self X]

open MaxLatticeFree.Inequalities in
lemma p4e_span_nonneg {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} {ψ : W → ℝ}
    (hsub : IsSublinear ψ)
    (hΛ : ∀ w : W, (w : EuclideanSpace ℝ (Fin q)) ∈ integralPoints q → 0 ≤ ψ w)
    (G : Set W) (hG : ∀ g ∈ G, (g : EuclideanSpace ℝ (Fin q)) ∈ integralPoints q)
    (w : W) (hw : w ∈ Submodule.span ℝ G) : 0 ≤ ψ w := by
  classical
  obtain ⟨c, hcG, hcw⟩ := Submodule.mem_span_set.1 hw
  set K : ℝ := ∑ g ∈ c.support, |ψ (-g)| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun g _ => abs_nonneg _)
  have key : ∀ n : ℕ, 0 ≤ (n : ℝ) * ψ w + K := by
    intro n
    set k : W → ℤ := fun g => ⌊(n : ℝ) * c g⌋ with hk
    set fr : W → ℝ := fun g => (n : ℝ) * c g - k g with hfr
    have hfr0 : ∀ g, 0 ≤ fr g := fun g => by
      simp only [hfr, hk]; linarith [Int.floor_le ((n : ℝ) * c g)]
    have hfr1 : ∀ g, fr g ≤ 1 := fun g => by
      simp only [hfr, hk]; linarith [Int.lt_floor_add_one ((n : ℝ) * c g)]
    set wn : W := ∑ g ∈ c.support, (k g : ℝ) • g with hwn
    set u : W := ∑ g ∈ c.support, fr g • (-g) with hu
    have hwn_eq : wn = (n : ℝ) • w + u := by
      rw [← hcw, hwn, hu]
      simp only [Finsupp.sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      simp only [hfr]
      module
    have hwn_int : (wn : EuclideanSpace ℝ (Fin q)) ∈ integralPoints q := by
      rw [hwn, Submodule.coe_sum]
      refine p4e_int_sum _ _ (fun g hg => ?_)
      rw [Submodule.coe_smul]
      exact p4e_int_smul (hG g (hcG hg)) (k g)
    have h1 := hΛ wn hwn_int
    have h2 : ψ wn ≤ ψ ((n : ℝ) • w) + ψ u := by
      rw [hwn_eq]; exact hsub.2 _ _
    have h3 : ψ ((n : ℝ) • w) = n * ψ w := hsub.1 w n (Nat.cast_nonneg n)
    have h4 : ψ u ≤ ∑ g ∈ c.support, fr g * ψ (-g) := p4e_sub_sum hsub _ _ _ (fun g _ => hfr0 g)
    have h5 : ∑ g ∈ c.support, fr g * ψ (-g) ≤ K := by
      refine Finset.sum_le_sum (fun g _ => ?_)
      have := hfr0 g; have := hfr1 g
      calc fr g * ψ (-g) ≤ fr g * |ψ (-g)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (hfr0 g)
        _ ≤ 1 * |ψ (-g)| := mul_le_mul_of_nonneg_right (hfr1 g) (abs_nonneg _)
        _ = |ψ (-g)| := one_mul _
    linarith
  by_contra hneg'
  have hneg : ψ w < 0 := not_le.mp hneg'
  obtain ⟨n, hn⟩ := exists_nat_ge (K / (-ψ w))
  have h4 : K ≤ n * (-ψ w) := (div_le_iff₀ (by linarith : 0 < -ψ w)).1 hn
  have := key (n + 1)
  push_cast at this
  linarith

open MaxLatticeFree.Inequalities Matrix in
lemma p4e_D_nonneg {q ℓ : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) {C : Matrix (Fin ℓ) (Fin q) ℝ} {d : Fin ℓ → ℝ}
    (hCd : IsAffineHullDescription f W C d) {ψ : W → ℝ} {α : ℝ} (hv : IsValid f W ψ α)
    (hsub : IsSublinear ψ) (r : W) (hr : C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp = 0) : 0 ≤ ψ r := by
  classical
  obtain ⟨z, hzA, hzi⟩ := hf
  have hzW : z - f ∈ W := hzA
  set P : Set (EuclideanSpace ℝ (Fin q)) := affSpace f W ∩ integralPoints q with hP
  have hzV : z ∈ (affHullInt f W : Set (EuclideanSpace ℝ (Fin q))) :=
    subset_affineSpan ℝ P ⟨hzA, hzi⟩
  have hzV' := hzV
  rw [hCd] at hzV'
  have hCz : C *ᵥ z.ofLp = d := hzV'.2
  have hzr : z + (r : EuclideanSpace ℝ (Fin q)) ∈ (affHullInt f W : Set (EuclideanSpace ℝ (Fin q))) := by
    rw [hCd]
    refine ⟨?_, ?_⟩
    · show z + (r : EuclideanSpace ℝ (Fin q)) - f ∈ W
      have : z + (r : EuclideanSpace ℝ (Fin q)) - f = (z - f) + (r : EuclideanSpace ℝ (Fin q)) := by abel
      rw [this]; exact W.add_mem hzW r.2
    · have : (z + (r : EuclideanSpace ℝ (Fin q))).ofLp = z.ofLp + (r : EuclideanSpace ℝ (Fin q)).ofLp := rfl
      rw [this, Matrix.mulVec_add, hCz, hr, add_zero]
  have hdir : (r : EuclideanSpace ℝ (Fin q)) ∈ (affHullInt f W).direction := by
    have := AffineSubspace.vsub_mem_direction hzr hzV
    simpa using this
  have hspan : (r : EuclideanSpace ℝ (Fin q)) ∈ Submodule.span ℝ (P -ᵥ P) := by
    have : (affHullInt f W).direction = vectorSpan ℝ P := direction_affineSpan ℝ P
    rw [this, vectorSpan_def] at hdir
    exact hdir
  set G : Set W := {g : W | ∃ p ∈ P, ∃ p' ∈ P, (g : EuclideanSpace ℝ (Fin q)) = p - p'} with hG
  have hsub' : P -ᵥ P ⊆ W.subtype '' G := by
    intro x hx
    obtain ⟨p, hp, p', hp', rfl⟩ := Set.mem_vsub.1 hx
    have hpW : p - p' ∈ W := by
      have h1 : p - f ∈ W := hp.1
      have h2 : p' - f ∈ W := hp'.1
      have := W.sub_mem h1 h2
      simpa using this
    exact ⟨⟨p - p', hpW⟩, ⟨p, hp, p', hp', rfl⟩, rfl⟩
  have hmem : (r : EuclideanSpace ℝ (Fin q)) ∈ Submodule.map W.subtype (Submodule.span ℝ G) := by
    rw [Submodule.map_span]
    exact Submodule.span_mono hsub' hspan
  obtain ⟨w, hw, hwr⟩ := hmem
  have hwr' : w = r := Subtype.ext hwr
  rw [← hwr']
  refine p4e_span_nonneg hsub (fun w hw => p4e_lattice_nonneg ⟨z, hzA, hzi⟩ hv w hw) G ?_ w hw
  rintro g ⟨p, hp, p', hp', hgp⟩
  rw [hgp]
  exact p4e_int_sub hp.2 hp'.2

open MaxLatticeFree.Inequalities Matrix in
lemma p4e_tilt {q ℓ : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (C : Matrix (Fin ℓ) (Fin q) ℝ)
    (ψ : W → ℝ) (hsub : IsSublinear ψ)
    (hD : ∀ r : W, C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp = 0 → 0 ≤ ψ r) :
    ∃ lam : Fin ℓ → ℝ, ∀ r : W, lam ⬝ᵥ (C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp) ≤ ψ r := by
  classical
  let CW : W →ₗ[ℝ] (Fin ℓ → ℝ) :=
    { toFun := fun r => C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp
      map_add' := by intro a b; simp [Matrix.mulVec_add]
      map_smul' := by intro c a; simp [Matrix.mulVec_smul] }
  have hCW : ∀ r, CW r = C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp := fun r => rfl
  let ℓ0 : W →ₗ.[ℝ] ℝ := ⟨LinearMap.ker CW, 0⟩
  obtain ⟨g, hg0, hgle⟩ := exists_extension_of_le_sublinear ℓ0 ψ
    (fun c hc x => hsub.1 x c hc.le) hsub.2 (by
      intro x
      have h0 : ℓ0 x = 0 := rfl
      rw [h0]
      exact hD x.1 x.2)
  have hker : ∀ x, CW x = 0 → g x = 0 := by
    intro x hx
    have := hg0 ⟨x, hx⟩
    rw [show ℓ0 ⟨x, hx⟩ = 0 from rfl] at this
    exact this
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective CW.rangeRestrict
    (LinearMap.range_rangeRestrict CW)
  obtain ⟨θ, hθ⟩ := LinearMap.exists_extend (g ∘ₗ σ)
  have hσ' : ∀ y : LinearMap.range CW, CW (σ y) = (y : Fin ℓ → ℝ) := by
    intro y
    have := congrArg (fun L => ((L y : LinearMap.range CW) : Fin ℓ → ℝ)) hσ
    simpa using this
  have hfac : ∀ r, θ (CW r) = g r := by
    intro r
    have hr : CW r ∈ LinearMap.range CW := ⟨r, rfl⟩
    have h1 : θ (CW r) = g (σ ⟨CW r, hr⟩) := by
      have := congrArg (fun L => L ⟨CW r, hr⟩) hθ
      simpa using this
    have h2 : CW (r - σ ⟨CW r, hr⟩) = 0 := by
      rw [map_sub, hσ' ⟨CW r, hr⟩]; simp
    have h3 := hker _ h2
    rw [map_sub] at h3
    rw [h1]; linarith
  refine ⟨fun i => θ (fun j => if i = j then 1 else 0), fun r => ?_⟩
  have h4 : θ (CW r) = (fun i => θ (fun j => if i = j then 1 else 0)) ⬝ᵥ (C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp) := by
    rw [LinearMap.pi_apply_eq_sum_univ θ (CW r)]
    unfold dotProduct
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_eq_mul, mul_comm]
    rfl
  rw [← h4, hfac]
  exact hgle r

open MaxLatticeFree.Inequalities in
lemma p4e_linVal_aff {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (a : ℝ) (φ β : W → ℝ)
    (s : W →₀ ℝ) : linVal (fun r => a * φ r + β r) s = a * linVal φ s + linVal β s := by
  unfold linVal Finsupp.sum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => by ring)

open MaxLatticeFree.Inequalities in
lemma p4e_linVal_sub {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (φ β : W → ℝ)
    (s : W →₀ ℝ) : linVal (fun r => φ r - β r) s = linVal φ s - linVal β s := by
  unfold linVal Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun r _ => by ring)

open MaxLatticeFree.Inequalities in
lemma p4e_linVal_div {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (φ : W → ℝ) (ρ : ℝ)
    (s : W →₀ ℝ) : linVal (fun r => φ r / ρ) s = linVal φ s / ρ := by
  unfold linVal Finsupp.sum
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun r _ => by ring)

open MaxLatticeFree.Inequalities in
lemma p4e_linVal_nonneg {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (φ : W → ℝ)
    (h : ∀ r, 0 ≤ φ r) (s : W →₀ ℝ) (hs : ∀ r, 0 ≤ s r) : 0 ≤ linVal φ s := by
  unfold linVal Finsupp.sum
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (h r) (hs r))

open MaxLatticeFree.Inequalities Matrix in
lemma p4e_linVal_dot {q ℓ : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    (C : Matrix (Fin ℓ) (Fin q) ℝ) (lam : Fin ℓ → ℝ) (s : W →₀ ℝ) :
    linVal (fun r : W => lam ⬝ᵥ (C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp)) s =
      lam ⬝ᵥ (C *ᵥ (combo W s).ofLp) := by
  let A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] ℝ :=
    { toFun := fun x => lam ⬝ᵥ (C *ᵥ x.ofLp)
      map_add' := by intro a b; simp [Matrix.mulVec_add, dotProduct_add]
      map_smul' := by intro c a; simp [Matrix.mulVec_smul, dotProduct_smul] }
  show linVal (fun r : W => A r) s = A (combo W s)
  unfold combo linVal Finsupp.sum
  rw [map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_smul, smul_eq_mul, mul_comm]

open MaxLatticeFree.Inequalities Matrix in
lemma p4e_calV_C {q ℓ : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {C : Matrix (Fin ℓ) (Fin q) ℝ} {d : Fin ℓ → ℝ} (hCd : IsAffineHullDescription f W C d)
    (s : W →₀ ℝ) (hs : s ∈ calV f W) : C *ᵥ (combo W s).ofLp = d - C *ᵥ f.ofLp := by
  have h1 : f + combo W s ∈ (affHullInt f W : Set (EuclideanSpace ℝ (Fin q))) := hs
  rw [hCd] at h1
  have h2 : C *ᵥ (f + combo W s).ofLp = d := h1.2
  have h3 : (f + combo W s).ofLp = f.ofLp + (combo W s).ofLp := rfl
  rw [h3, Matrix.mulVec_add] at h2
  rw [← h2]; abel

open MaxLatticeFree.Inequalities in
lemma p4e_Rf_calV {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {s : W →₀ ℝ} (hs : s ∈ Rf f W) : s ∈ calV f W := by
  have hmem : f + combo W s ∈ affSpace f W ∩ integralPoints q := ⟨by
    show f + combo W s - f ∈ W
    rw [add_sub_cancel_left]; exact p4e_combo_mem W s, hs.1⟩
  exact subset_affineSpan ℝ _ hmem

open MaxLatticeFree.Inequalities Matrix in
lemma p4e_normalize {q ℓ : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) {C : Matrix (Fin ℓ) (Fin q) ℝ} {d : Fin ℓ → ℝ}
    (hCd : IsAffineHullDescription f W C d) {ψ : W → ℝ} {α : ℝ} (hm : IsMinimal f W ψ α)
    (hnt : ¬ IsTrivial f W ψ α) :
    ∃ (φ : W → ℝ) (ρ : ℝ) (lam : Fin ℓ → ℝ), 0 < ρ ∧ IsMinimal f W φ 1 ∧ IsSublinear φ ∧
      (∀ r, 0 ≤ φ r) ∧
      (∀ r : W, ψ r = ρ * φ r + lam ⬝ᵥ (C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp)) ∧
      α = ρ * 1 + lam ⬝ᵥ (d - C *ᵥ f.ofLp) := by
  have hsub := p4e_sublinear hf hm
  obtain ⟨lam, hlam⟩ := p4e_tilt W C ψ hsub (fun r hr => p4e_D_nonneg hf hCd hm.1 hsub r hr)
  set A : W → ℝ := fun r => lam ⬝ᵥ (C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp) with hA
  set β : ℝ := lam ⬝ᵥ (d - C *ᵥ f.ofLp) with hβ
  have hAsmul : ∀ (c : ℝ) (r : W), A (c • r) = c * A r := by
    intro c r; simp [hA, Matrix.mulVec_smul, dotProduct_smul]
  have hAadd : ∀ r₁ r₂ : W, A (r₁ + r₂) = A r₁ + A r₂ := by
    intro r₁ r₂; simp [hA, Matrix.mulVec_add, dotProduct_add]
  have hAcalV : ∀ s ∈ calV f W, linVal A s = β := by
    intro s hs
    rw [hA, p4e_linVal_dot, p4e_calV_C hCd s hs]
  have hARf : ∀ s ∈ Rf f W, linVal A s = β := fun s hs => hAcalV s (p4e_Rf_calV hs)
  set ψ' : W → ℝ := fun r => ψ r - A r with hψ'
  have hψ'0 : ∀ r, 0 ≤ ψ' r := fun r => sub_nonneg.2 (hlam r)
  have hlv' : ∀ s, linVal ψ' s = linVal ψ s - linVal A s := fun s => p4e_linVal_sub ψ A s
  obtain ⟨s0, hs0, hs00, hs0lt⟩ : ∃ s ∈ calV f W, (∀ r, 0 ≤ s r) ∧ ¬ α ≤ linVal ψ s := by
    by_contra h
    apply hnt
    intro s hs hs0
    by_contra h'
    exact h ⟨s, hs, hs0, h'⟩
  have hρ : 0 < α - β := by
    have h1 := p4e_linVal_nonneg ψ' hψ'0 s0 hs00
    rw [hlv', hAcalV s0 hs0] at h1
    have h2 := not_le.mp hs0lt
    linarith
  set ρ : ℝ := α - β with hρdef
  set φ : W → ℝ := fun r => ψ' r / ρ with hφ
  have hφ0 : ∀ r, 0 ≤ φ r := fun r => div_nonneg (hψ'0 r) hρ.le
  have hψφ : ∀ r, ψ r = ρ * φ r + A r := by
    intro r
    simp only [hφ, hψ']
    rw [mul_div_cancel₀ _ hρ.ne']; ring
  have hlvφ : ∀ s, linVal φ s = linVal ψ' s / ρ := fun s => p4e_linVal_div ψ' ρ s
  have hvalφ : IsValid f W φ 1 := by
    intro s hs
    rw [hlvφ, hlv', hARf s hs]
    have := hm.1 s hs
    rw [le_div_iff₀ hρ]
    linarith
  refine ⟨φ, ρ, lam, hρ, ⟨hvalφ, ?_⟩, ⟨?_, ?_⟩, hφ0, hψφ, by rw [hρdef]; ring⟩
  · intro φ'' hv'' hd''
    set ψ'' : W → ℝ := fun r => ρ * φ'' r + A r with hψ''
    have hval'' : IsValid f W ψ'' α := by
      intro s hs
      rw [p4e_linVal_aff, hARf s hs]
      have := hv'' s hs
      have h2 : ρ * 1 ≤ ρ * linVal φ'' s := mul_le_mul_of_nonneg_left this hρ.le
      rw [hρdef] at h2 ⊢
      linarith
    have hdom'' : Dominates ψ'' ψ := by
      intro r
      rw [hψφ r]
      have := mul_le_mul_of_nonneg_left (hd'' r) hρ.le
      simp only [hψ'']
      linarith
    have := hm.2 ψ'' hval'' hdom''
    funext r
    have h3 := congrFun this r
    have h4 : ρ * φ'' r = ρ * φ r := by
      have := hψφ r
      simp only [hψ''] at h3
      linarith
    exact mul_left_cancel₀ hρ.ne' h4
  · intro r c hc
    show ψ' (c • r) / ρ = c * (ψ' r / ρ)
    have h1 := hsub.1 r c hc
    simp only [hψ', hAsmul, h1]
    field_simp
  · intro r₁ r₂
    show ψ' (r₁ + r₂) / ρ ≤ ψ' r₁ / ρ + ψ' r₂ / ρ
    have h1 := hsub.2 r₁ r₂
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hρ.le
    simp only [hψ', hAadd]
    linarith

open MaxLatticeFree.Inequalities in
lemma p4e_sl_zero {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} {σ : W → ℝ}
    (h : IsSublinear σ) : σ 0 = 0 := by
  have := h.1 0 0 le_rfl
  simpa using this

open MaxLatticeFree.Inequalities in
lemma p4e_sl_neg {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} {σ : W → ℝ}
    (h : IsSublinear σ) (v : W) (t : ℝ) : t * σ v ≤ σ (t • v) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [h.1 v t ht]
  · have h1 := h.2 (t • v) ((-t) • v)
    have e : t • v + (-t) • v = 0 := by rw [← add_smul]; simp
    rw [e, p4e_sl_zero h, h.1 v (-t) (by linarith)] at h1
    linarith

open MaxLatticeFree.Inequalities in
lemma p4e_sl_convex {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} {σ : W → ℝ}
    (h : IsSublinear σ) : ConvexOn ℝ Set.univ σ := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have h1 := h.2 (a • x) (b • y)
  rw [h.1 x a ha, h.1 y b hb] at h1
  simp only [smul_eq_mul]
  exact h1

open MaxLatticeFree.Inequalities in
lemma p4e_sl_cont {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} {σ : W → ℝ}
    (h : IsSublinear σ) : Continuous σ :=
  continuousOn_univ.1 ((p4e_sl_convex h).continuousOn isOpen_univ)

open MaxLatticeFree.Inequalities in
lemma p4e_hb {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} {σ : W → ℝ}
    (h : IsSublinear σ) (v : W) :
    ∃ l : W →ₗ[ℝ] ℝ, (∀ u, l u ≤ σ u) ∧ l v = σ v := by
  have H : ∀ c : ℝ, c • v = 0 → c • σ v = 0 := by
    intro c hc
    rcases smul_eq_zero.1 hc with h0 | h0
    · rw [h0, zero_smul]
    · rw [h0, p4e_sl_zero h, smul_zero]
  let p : W →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' v (σ v) H
  have hp : ∀ (c : ℝ) (hc : c • v ∈ p.domain), p ⟨c • v, hc⟩ = c * σ v := by
    intro c hc
    have := LinearPMap.mkSpanSingleton'_apply v (σ v) H c hc
    rw [smul_eq_mul] at this
    exact this
  have hv : v ∈ p.domain := by
    show v ∈ Submodule.span ℝ {v}
    exact Submodule.mem_span_singleton_self v
  obtain ⟨g, hg0, hgle⟩ := exists_extension_of_le_sublinear p σ
    (fun c hc x => h.1 x c hc.le) h.2 (by
      intro x
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (x.2 : (x : W) ∈ Submodule.span ℝ {v})
      have hx : x = ⟨c • v, by rw [hc]; exact x.2⟩ := Subtype.ext hc.symm
      have h1 : p x = c * σ v := by rw [hx]; exact hp c _
      have h2 : (x : W) = c • v := hc.symm
      rw [h1, h2]
      exact p4e_sl_neg h v c)
  refine ⟨g, hgle, ?_⟩
  have h3 : p ⟨v, hv⟩ = σ v := LinearPMap.mkSpanSingleton'_apply_self v (σ v) H hv
  exact (hg0 ⟨v, hv⟩).trans h3

lemma p4e_riesz {q : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (l : W →ₗ[ℝ] ℝ) :
    ∃ y ∈ W, ∀ u : W, inner ℝ (u : EuclideanSpace ℝ (Fin q)) y = l u := by
  let L : W →L[ℝ] ℝ := LinearMap.toContinuousLinearMap l
  let y' : W := (InnerProductSpace.toDual ℝ W).symm L
  refine ⟨(y' : EuclideanSpace ℝ (Fin q)), y'.2, fun u => ?_⟩
  have h1 : inner ℝ y' u = L u := InnerProductSpace.toDual_symm_apply
  have h2 : inner ℝ (u : EuclideanSpace ℝ (Fin q)) (y' : EuclideanSpace ℝ (Fin q)) = inner ℝ u y' := rfl
  rw [h2, real_inner_comm]
  exact h1

open MaxLatticeFree.Inequalities in
lemma p4e_memK {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} (v : W) (hv : φ v ≤ 1) :
    (v : EuclideanSpace ℝ (Fin q)) ∈ (fun x => x - f) '' Bpsi f W φ 1 := by
  have hx : f + (v : EuclideanSpace ℝ (Fin q)) - f ∈ W := by
    rw [add_sub_cancel_left]; exact v.2
  refine ⟨f + (v : EuclideanSpace ℝ (Fin q)), ⟨hx, ?_⟩, by simp⟩
  have e : (⟨f + (v : EuclideanSpace ℝ (Fin q)) - f, hx⟩ : W) = v := Subtype.ext (by simp)
  rw [e]; exact hv

open MaxLatticeFree.Inequalities in
lemma p4e_polar_le {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} (hs : IsSublinear φ) (h0 : ∀ r, 0 ≤ φ r)
    {y : EuclideanSpace ℝ (Fin q)} (hy : y ∈ Khat W ((fun x => x - f) '' Bpsi f W φ 1)) (r : W) :
    inner ℝ (r : EuclideanSpace ℝ (Fin q)) y ≤ φ r := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have htpos : 0 < φ r + ε := by have := h0 r; linarith
  have h1 : φ ((φ r + ε)⁻¹ • r) ≤ 1 := by
    rw [hs.1 r _ (inv_nonneg.2 htpos.le), inv_mul_le_iff₀ htpos, mul_one]; linarith
  have h2 := hy.1.2 _ (p4e_memK (f := f) ((φ r + ε)⁻¹ • r) h1)
  have h3 : inner ℝ (((φ r + ε)⁻¹ • r : W) : EuclideanSpace ℝ (Fin q)) y =
      (φ r + ε)⁻¹ * inner ℝ (r : EuclideanSpace ℝ (Fin q)) y := by
    rw [Submodule.coe_smul, real_inner_smul_left]
  rw [h3, inv_mul_le_iff₀ htpos, mul_one] at h2
  exact h2

open MaxLatticeFree.Inequalities in
lemma p4e_inner_le_psiB {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} (hs : IsSublinear φ) (h0 : ∀ r, 0 ≤ φ r)
    {y : EuclideanSpace ℝ (Fin q)} (hy : y ∈ Khat W ((fun x => x - f) '' Bpsi f W φ 1)) (r : W) :
    inner ℝ (r : EuclideanSpace ℝ (Fin q)) y ≤ psiB f W (Bpsi f W φ 1) r := by
  show inner ℝ (r : EuclideanSpace ℝ (Fin q)) y ≤
    sSup ((fun y => inner ℝ (r : EuclideanSpace ℝ (Fin q)) y) '' Khat W ((fun x => x - f) '' Bpsi f W φ 1))
  refine le_csSup ⟨φ r, ?_⟩ ⟨y, hy, rfl⟩
  rintro _ ⟨y', hy', rfl⟩
  exact p4e_polar_le hs h0 hy' r

open MaxLatticeFree.Inequalities in
lemma p4e_psiB_le {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} (hs : IsSublinear φ) (h0 : ∀ r, 0 ≤ φ r) (r : W) :
    psiB f W (Bpsi f W φ 1) r ≤ φ r := by
  show sSup ((fun y => inner ℝ (r : EuclideanSpace ℝ (Fin q)) y) '' Khat W ((fun x => x - f) '' Bpsi f W φ 1)) ≤ φ r
  refine Real.sSup_le ?_ (h0 r)
  rintro _ ⟨y, hy, rfl⟩
  exact p4e_polar_le hs h0 hy r

open MaxLatticeFree.Inequalities in
lemma p4e_psiB_valid {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} (hs : IsSublinear φ) (h0 : ∀ r, 0 ≤ φ r) (hv : IsValid f W φ 1) :
    IsValid f W (psiB f W (Bpsi f W φ 1)) 1 := by
  intro s hs'
  have hcm : combo W s ∈ W := p4e_combo_mem W s
  obtain ⟨v, hvdef⟩ : ∃ v : W, (v : EuclideanSpace ℝ (Fin q)) = combo W s := ⟨⟨_, hcm⟩, rfl⟩
  have hφv : 1 ≤ φ v := by
    have hx : f + combo W s - f ∈ W := by rw [add_sub_cancel_left]; exact hcm
    have h1 := p4e_valid_single hv (f + combo W s) hx hs'.1
    have e : (⟨f + combo W s - f, hx⟩ : W) = v := Subtype.ext (by
      show f + combo W s - f = (v : EuclideanSpace ℝ (Fin q))
      rw [hvdef]; simp)
    rw [e] at h1; exact h1
  obtain ⟨l, hl, hlv⟩ := p4e_hb hs v
  obtain ⟨y, hyW, hy⟩ := p4e_riesz W l
  have hyK : y ∈ Khat W ((fun x => x - f) '' Bpsi f W φ 1) := by
    refine ⟨⟨hyW, ?_⟩, ?_⟩
    · rintro _ ⟨x, ⟨hx, hφx⟩, rfl⟩
      show inner ℝ (x - f) y ≤ 1
      have h1 := hy ⟨x - f, hx⟩
      calc inner ℝ (x - f) y = l ⟨x - f, hx⟩ := h1
        _ ≤ φ ⟨x - f, hx⟩ := hl _
        _ ≤ 1 := hφx
    · have hpos : 0 < φ v := by linarith
      have hφw : φ ((φ v)⁻¹ • v) = 1 := by
        rw [hs.1 v _ (inv_nonneg.2 hpos.le), inv_mul_cancel₀ hpos.ne']
      refine ⟨(((φ v)⁻¹ • v : W) : EuclideanSpace ℝ (Fin q)), p4e_memK _ hφw.le, ?_⟩
      have h3 : inner ℝ (((φ v)⁻¹ • v : W) : EuclideanSpace ℝ (Fin q)) y =
          (φ v)⁻¹ * inner ℝ (v : EuclideanSpace ℝ (Fin q)) y := by
        rw [Submodule.coe_smul, real_inner_smul_left]
      rw [h3, hy v, hlv, inv_mul_cancel₀ hpos.ne']
  have h1 : inner ℝ (combo W s) y = linVal (fun r : W => inner ℝ (r : EuclideanSpace ℝ (Fin q)) y) s := by
    unfold combo linVal Finsupp.sum
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [real_inner_smul_left, mul_comm]
  have h2 : linVal (fun r : W => inner ℝ (r : EuclideanSpace ℝ (Fin q)) y) s ≤
      linVal (psiB f W (Bpsi f W φ 1)) s :=
    p4e_linVal_mono _ _ (fun r => p4e_inner_le_psiB hs h0 hyK r) s hs'.2
  have h3 : inner ℝ (combo W s) y = l v := by rw [← hvdef]; exact hy v
  linarith [hlv]

open MaxLatticeFree.Inequalities in
lemma p4e_psiB_eq {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} (hs : IsSublinear φ) (h0 : ∀ r, 0 ≤ φ r) (hm : IsMinimal f W φ 1) :
    psiB f W (Bpsi f W φ 1) = φ :=
  hm.2 _ (p4e_psiB_valid hs h0 hm.1) (fun r => p4e_psiB_le hs h0 r)

open MaxLatticeFree.Inequalities in
lemma p4e_B_sub {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} : Bpsi f W φ 1 ⊆ affSpace f W := by
  intro x hx
  obtain ⟨h, _⟩ := hx
  exact h

open MaxLatticeFree.Inequalities in
lemma p4e_B_convex {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} (hs : IsSublinear φ) : Convex ℝ (Bpsi f W φ 1) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hb' : b = 1 - a := by linarith
  subst hb'
  have e : a • x + (1 - a) • y - f = a • (x - f) + (1 - a) • (y - f) := by module
  have hW : a • x + (1 - a) • y - f ∈ W := by
    rw [e]; exact W.add_mem (W.smul_mem _ hx1) (W.smul_mem _ hy1)
  refine ⟨hW, ?_⟩
  have e2 : (⟨a • x + (1 - a) • y - f, hW⟩ : W) =
      a • (⟨x - f, hx1⟩ : W) + (1 - a) • (⟨y - f, hy1⟩ : W) := Subtype.ext e
  rw [e2]
  calc φ (a • (⟨x - f, hx1⟩ : W) + (1 - a) • (⟨y - f, hy1⟩ : W))
      ≤ φ (a • (⟨x - f, hx1⟩ : W)) + φ ((1 - a) • (⟨y - f, hy1⟩ : W)) := hs.2 _ _
    _ = a * φ ⟨x - f, hx1⟩ + (1 - a) * φ ⟨y - f, hy1⟩ := by rw [hs.1 _ _ ha, hs.1 _ _ hb]
    _ ≤ a * 1 + (1 - a) * 1 := by gcongr
    _ = 1 := by ring

open MaxLatticeFree.Inequalities in
lemma p4e_B_int {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} (hs : IsSublinear φ) : f ∈ intRel (affSpace f W) (Bpsi f W φ 1) := by
  have hc := p4e_sl_cont hs
  have hU : IsOpen {r : W | φ r < 1} := isOpen_lt hc continuous_const
  have h0U : (0 : W) ∈ {r : W | φ r < 1} := by
    show φ 0 < 1
    rw [p4e_sl_zero hs]; exact one_pos
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have hf0 : f ∈ Bpsi f W φ 1 := by
    have h : f - f ∈ W := by simp
    refine ⟨h, ?_⟩
    have e : (⟨f - f, h⟩ : W) = 0 := Subtype.ext (by simp)
    rw [e, p4e_sl_zero hs]; norm_num
  refine ⟨hf0, δ, hδ, ?_⟩
  rintro x ⟨hxb, hxa⟩
  have hxW : x - f ∈ W := hxa
  have hmemb : (⟨x - f, hxW⟩ : W) ∈ Metric.ball (0 : W) δ := by
    rw [Metric.mem_ball, dist_zero_right]
    show ‖x - f‖ < δ
    rw [← dist_eq_norm]; exact hxb
  exact ⟨hxW, le_of_lt (hball hmemb)⟩

open MaxLatticeFree.Inequalities in
lemma p4e_B_free {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} (hs : IsSublinear φ) (hv : IsValid f W φ 1) :
    ∀ x ∈ intRel (affSpace f W) (Bpsi f W φ 1), x ∉ integralPoints q := by
  rintro x ⟨⟨hx1, hx2⟩, ε, hε, hball⟩ hxi
  have h1 := p4e_valid_single hv x hx1 hxi
  obtain ⟨t, ht, htN⟩ := exists_pos_mul_lt hε ‖x - f‖
  have hmem : x + t • (x - f) ∈ Metric.ball x ε ∩ affSpace f W := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
      linarith
    · show x + t • (x - f) - f ∈ W
      have : x + t • (x - f) - f = (1 + t) • (x - f) := by module
      rw [this]; exact W.smul_mem _ hx1
  obtain ⟨h', hle⟩ := hball hmem
  have e : (⟨x + t • (x - f) - f, h'⟩ : W) = (1 + t) • (⟨x - f, hx1⟩ : W) := Subtype.ext (by
    show x + t • (x - f) - f = (1 + t) • (x - f)
    module)
  rw [e, hs.1 _ _ (by linarith)] at hle
  have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 1 + t by linarith)
  linarith

open MaxLatticeFree.Inequalities in
lemma p4e_B_max {q : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    {φ : W → ℝ} (hs : IsSublinear φ) (h0 : ∀ r, 0 ≤ φ r) (hm : IsMinimal f W φ 1)
    (B' : Set (EuclideanSpace ℝ (Fin q))) (hB' : IsLatticeFree f W B') (hsub : Bpsi f W φ 1 ⊆ B') :
    B' = Bpsi f W φ 1 := by
  obtain ⟨hB'aff, hB'cvx, hB'free⟩ := hB'
  obtain ⟨S, hSmem⟩ : ∃ S : Set W, ∀ r : W, r ∈ S ↔ f + (r : EuclideanSpace ℝ (Fin q)) ∈ B' :=
    ⟨{r | f + (r : EuclideanSpace ℝ (Fin q)) ∈ B'}, fun r => Iff.rfl⟩
  have hSconv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    rw [hSmem] at hx hy ⊢
    have e : f + ((a • x + b • y : W) : EuclideanSpace ℝ (Fin q)) =
        a • (f + (x : EuclideanSpace ℝ (Fin q))) + b • (f + (y : EuclideanSpace ℝ (Fin q))) := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      simp only [Submodule.coe_add, Submodule.coe_smul]; module
    rw [e]
    exact hB'cvx hx hy ha hb hab
  have hc := p4e_sl_cont hs
  have hU : IsOpen {r : W | φ r < 1} := isOpen_lt hc continuous_const
  have hUS : {r : W | φ r < 1} ⊆ S := by
    intro r hr
    rw [hSmem]
    apply hsub
    have hx : f + (r : EuclideanSpace ℝ (Fin q)) - f ∈ W := by
      rw [add_sub_cancel_left]; exact r.2
    refine ⟨hx, ?_⟩
    have e : (⟨f + (r : EuclideanSpace ℝ (Fin q)) - f, hx⟩ : W) = r := Subtype.ext (by simp)
    rw [e]; exact le_of_lt hr
  have h0U : (0 : W) ∈ {r : W | φ r < 1} := by
    show φ 0 < 1
    rw [p4e_sl_zero hs]; exact one_pos
  have hSn : S ∈ nhds (0 : W) := Filter.mem_of_superset (hU.mem_nhds h0U) hUS
  have habs : Absorbent ℝ S := absorbent_nhds_zero hSn
  have h0S : (0 : W) ∈ S := mem_of_mem_nhds hSn
  have hgsub : IsSublinear (gauge S) :=
    ⟨fun r c hc => by rw [gauge_smul_of_nonneg hc, smul_eq_mul],
     fun r₁ r₂ => gauge_add_le hSconv habs r₁ r₂⟩
  have hgcont := p4e_sl_cont hgsub
  have hgle : ∀ r, gauge S r ≤ φ r := by
    intro r
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have htpos : 0 < φ r + ε := by have := h0 r; linarith
    apply gauge_le_of_mem htpos.le
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ htpos.ne', hSmem]
    apply hsub
    have hx : f + (((φ r + ε)⁻¹ • r : W) : EuclideanSpace ℝ (Fin q)) - f ∈ W := by
      rw [add_sub_cancel_left]; exact ((φ r + ε)⁻¹ • r : W).2
    refine ⟨hx, ?_⟩
    have e : (⟨f + (((φ r + ε)⁻¹ • r : W) : EuclideanSpace ℝ (Fin q)) - f, hx⟩ : W) =
        (φ r + ε)⁻¹ • r := Subtype.ext (by simp)
    rw [e, hs.1 r _ (inv_nonneg.2 htpos.le), inv_mul_le_iff₀ htpos, mul_one]
    linarith
  have hgv : IsValid f W (gauge S) 1 := by
    intro s hs'
    obtain ⟨v, hvdef⟩ : ∃ v : W, (v : EuclideanSpace ℝ (Fin q)) = combo W s :=
      ⟨⟨_, p4e_combo_mem W s⟩, rfl⟩
    have h1 : 1 ≤ gauge S v := by
      by_contra hlt
      have hlt' : gauge S v < 1 := not_le.mp hlt
      have hxi := hs'.1
      have hxmem : (f + combo W s) ∈ intRel (affSpace f W) B' := by
        refine ⟨?_, ?_⟩
        · have := setOfPred_gauge_lt_one_subset_self hSconv h0S habs hlt'
          rw [hSmem, hvdef] at this
          exact this
        · have hUg : IsOpen {r : W | gauge S r < 1} := isOpen_lt hgcont continuous_const
          obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hUg v hlt'
          refine ⟨δ, hδ, ?_⟩
          rintro y ⟨hyb, hya⟩
          have hyW : y - f ∈ W := hya
          have hmemb : (⟨y - f, hyW⟩ : W) ∈ Metric.ball v δ := by
            rw [Metric.mem_ball, dist_eq_norm]
            show ‖(y - f) - (v : EuclideanSpace ℝ (Fin q))‖ < δ
            rw [hvdef]
            have : y - f - combo W s = y - (f + combo W s) := by abel
            rw [this, ← dist_eq_norm]; exact hyb
          have := setOfPred_gauge_lt_one_subset_self hSconv h0S habs (hball hmemb)
          rw [hSmem] at this
          simpa using this
      exact hB'free _ hxmem hxi
    have hvsum : v = ∑ r ∈ s.support, s r • r := by
      apply Subtype.ext
      rw [hvdef, Submodule.coe_sum]
      rfl
    have h2 : gauge S (∑ r ∈ s.support, s r • r) ≤ ∑ r ∈ s.support, s r * gauge S r :=
      p4e_sub_sum hgsub s.support (fun r => s r) (fun r => r) (fun r _ => hs'.2 r)
    rw [← hvsum] at h2
    have h3 : linVal (gauge S) s = ∑ r ∈ s.support, s r * gauge S r := by
      unfold linVal Finsupp.sum
      exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)
    linarith
  have hgeq : gauge S = φ := hm.2 _ hgv hgle
  refine Set.Subset.antisymm ?_ hsub
  intro x hx
  have hxW : x - f ∈ W := hB'aff hx
  have hxS : (⟨x - f, hxW⟩ : W) ∈ S := by
    rw [hSmem]; simpa using hx
  have := gauge_le_one_of_mem hxS
  rw [hgeq] at this
  exact ⟨hxW, this⟩

open MaxLatticeFree.Inequalities Matrix in
lemma p4e_part2 {q ℓ : ℕ} {f : EuclideanSpace ℝ (Fin q)} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) {C : Matrix (Fin ℓ) (Fin q) ℝ} {d : Fin ℓ → ℝ}
    (hCd : IsAffineHullDescription f W C d) {ψ : W → ℝ} {α : ℝ} (hm : IsMinimal f W ψ α)
    (hnt : ¬ IsTrivial f W ψ α) :
    ∃ B : Set (EuclideanSpace ℝ (Fin q)), IsMaximalLatticeFree f W B ∧ f ∈ intRel (affSpace f W) B ∧
      (∀ r : W, 0 ≤ psiB f W B r) ∧ Equivalent f W C d ψ α (psiB f W B) 1 := by
  obtain ⟨φ, ρ, lam, hρ, hφm, hφs, hφ0, hψ, hα⟩ := p4e_normalize hf hCd hm hnt
  have heq := p4e_psiB_eq (f := f) hφs hφ0 hφm
  refine ⟨Bpsi f W φ 1, ⟨⟨p4e_B_sub, p4e_B_convex hφs, p4e_B_free hφs hφm.1⟩,
    fun B' hB' hsub => p4e_B_max hφs hφ0 hφm B' hB' hsub⟩, p4e_B_int hφs, ?_, ?_⟩
  · rw [heq]; exact hφ0
  · rw [heq]
    exact ⟨hCd, hm.1, hφm.1, ρ, hρ, lam, hψ, hα⟩

open MaxLatticeFree.Inequalities Matrix in
theorem solution {q ℓ : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (hf : (affSpace f W ∩ integralPoints q).Nonempty)
    (C : Matrix (Fin ℓ) (Fin q) ℝ) (d : Fin ℓ → ℝ) (hCd : IsAffineHullDescription f W C d) :
    (∀ (ψ : W → ℝ) (α : ℝ), IsValid f W ψ α → ¬ IsTrivial f W ψ α →
        ∃ ψ' : W → ℝ, IsMinimal f W ψ' α ∧ ¬ IsTrivial f W ψ' α ∧ Dominates ψ' ψ) ∧
    (∀ (ψ : W → ℝ) (α : ℝ), IsMinimal f W ψ α → ¬ IsTrivial f W ψ α →
        ∃ B : Set (EuclideanSpace ℝ (Fin q)), IsMaximalLatticeFree f W B ∧ f ∈ intRel (affSpace f W) B ∧
          (∀ r : W, 0 ≤ psiB f W B r) ∧ Equivalent f W C d ψ α (psiB f W B) 1) := by
  exact ⟨fun ψ α hv hnt => p4e_part1 f W hf ψ α hv hnt, fun ψ α hm hnt => p4e_part2 hf hCd hm hnt⟩
