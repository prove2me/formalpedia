-- Prove2me | solution 1 for NQueensComp.NPC.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:56:21.690458+00:00
-- url     : https://prove2.me/submissions/0422c4a4-8989-459f-93e8-fbd75f378a44

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

open NQueensComp.NPC

theorem le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem band_nat (n x y a b : ℕ) (hx : x < n) (hy : y < n) (hab : a ≠ b) :
    x + 2 * n * a ≠ y + 2 * n * b := by
  intro h
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · have : 2 * n * (a + 1) ≤ 2 * n * b := Nat.mul_le_mul_left _ hlt
    nlinarith
  · have : 2 * n * (b + 1) ≤ 2 * n * a := Nat.mul_le_mul_left _ hlt
    nlinarith

theorem band_int (n : ℕ) (x y : ℤ) (a b : ℕ) (hx : |x| < n) (hy : |y| < n) (hab : a ≠ b) :
    x + 4 * n * a ≠ y + 4 * n * b := by
  intro h
  rw [abs_lt] at hx hy
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · have h1 : (a : ℤ) + 1 ≤ b := by exact_mod_cast hlt
    have := mul_nonneg (by positivity : (0 : ℤ) ≤ n) (by linarith : (0 : ℤ) ≤ b - a - 1)
    nlinarith
  · have h1 : (b : ℤ) + 1 ≤ a := by exact_mod_cast hlt
    have := mul_nonneg (by positivity : (0 : ℤ) ≤ n) (by linarith : (0 : ℤ) ≤ a - b - 1)
    nlinarith

/-- Attacks from integer data. -/
theorem attacks_of_int (q₁ q₂ : Queen)
    (hne : ¬ ((q₁.1 : ℤ) = q₂.1 ∧ (q₁.2 : ℤ) = q₂.2))
    (hl : (q₁.1 : ℤ) = q₂.1 ∨ (q₁.2 : ℤ) = q₂.2 ∨ (q₁.1 : ℤ) + q₁.2 = q₂.1 + q₂.2 ∨
      (q₁.1 : ℤ) - q₁.2 = q₂.1 - q₂.2) : Attacks q₁ q₂ := by
  refine ⟨fun h => hne ⟨by rw [h], by rw [h]⟩, ?_⟩
  simp only [col, row, sumDiag, diffDiag]
  rcases hl with h | h | h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (Or.inl (by exact_mod_cast h))
  · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h)))
  · exact Or.inr (Or.inr (Or.inr h))

theorem gadget_facts (M : Inst4) (S : Finset Queen) (hM : M.Valid) (hS : M.IsSol S) :
    1 ≤ M.n ∧ (∀ c ∈ M.C, c < M.n) ∧ (∀ r ∈ M.R, r < M.n) ∧
    (∀ d ∈ M.Dm, -((M.n : ℤ) - 1) ≤ d ∧ d ≤ (M.n : ℤ) - 1) ∧
    S.card = M.C.card ∧ NonAttacking S ∧ (∀ q ∈ S, q.1 ∈ M.C ∧ q.2 ∈ M.R) ∧
    (∀ q ∈ S, diffDiag q ∉ M.Dm) := by
  obtain ⟨⟨⟨h1, _, _⟩, _, _, h3, h4⟩, h5, _⟩ := hM
  obtain ⟨⟨s1, _, s3, s4⟩, s5⟩ := hS
  simp only [Inst4.toInst3, Finset.card_empty, add_zero, Finset.sdiff_empty] at s1 s4
  exact ⟨h1, h3, h4, h5, s1, s3, fun q hq => s4 q hq, fun q hq => (s5 q hq).1⟩

theorem solution (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms ≠ []) (Ss : List (Finset Queen))
    (hS : Inst5IsSol Ms Ss) : (def20 Ms).IsSol (lemma21_map Ms Ss) := by
  obtain ⟨hF, hcross⟩ := hS
  have hk0 : Ms.length ≠ 0 := by
    intro h; exact hk (List.length_eq_zero_iff.mp h)
  have hlen : Ss.length = Ms.length := hF.length_eq.symm
  have hnle : ∀ M ∈ Ms, M.n ≤ def20_nmax Ms := by
    intro M hM
    exact le_foldr_max _ _ (List.mem_map_of_mem hM)
  -- per-gadget facts
  have hsol : ∀ a (ha : a < Ms.length), (Ms.get ⟨a, ha⟩).IsSol (Ss.getD a ∅) := by
    intro a ha
    have h := (List.forall₂_iff_get.mp hF).2 a ha (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact h
  have hval : ∀ a (ha : a < Ms.length), (Ms.get ⟨a, ha⟩).Valid ∧ (Ms.get ⟨a, ha⟩).Dp = ∅ :=
    fun a ha => hMs _ (List.get_mem _ _)
  -- the facts we use about a queen of block `a`
  have hq : ∀ a (ha : a < Ms.length), ∀ p ∈ Ss.getD a ∅,
      p.1 < def20_nmax Ms ∧ p.2 < def20_nmax Ms ∧ p.1 ∈ (Ms.get ⟨a, ha⟩).C ∧
        p.2 ∈ (Ms.get ⟨a, ha⟩).R ∧ diffDiag p ∉ (Ms.get ⟨a, ha⟩).Dm := by
    intro a ha p hp
    obtain ⟨_, hC, hR, _, _, _, hcr, hd⟩ := gadget_facts _ _ (hval a ha).1 (hsol a ha)
    have hn := hnle _ (List.get_mem Ms ⟨a, ha⟩)
    obtain ⟨hc, hr⟩ := hcr p hp
    exact ⟨by have := hC _ hc; omega, by have := hR _ hr; omega, hc, hr, hd p hp⟩
  have hmem : ∀ q, q ∈ lemma21_map Ms Ss ↔
      ∃ a < Ms.length, ∃ p ∈ Ss.getD a ∅,
        p + (2 * def20_nmax Ms * a, 2 * def20_nmax Ms * (Ms.length - 1 - a)) = q := by
    intro q
    simp only [lemma21_map, shiftSet, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      def20_alpha, def20_beta]
  -- arithmetic of the offsets
  have hT : ∀ a, a < Ms.length →
      2 * def20_nmax Ms * a + 2 * def20_nmax Ms * (Ms.length - 1 - a) =
        2 * def20_nmax Ms * (Ms.length - 1) := by
    intro a ha; rw [← Nat.mul_add]; congr 1; omega
  have hTz : ∀ a, a < Ms.length →
      2 * (def20_nmax Ms : ℤ) * ((Ms.length - 1 - a : ℕ) : ℤ) =
        2 * (def20_nmax Ms : ℤ) * ((Ms.length - 1 : ℕ) : ℤ) - 2 * (def20_nmax Ms : ℤ) * a := by
    intro a ha
    rw [Nat.cast_sub (by omega)]
    ring
  have hkk : 2 * def20_nmax Ms * Ms.length =
      2 * def20_nmax Ms * (Ms.length - 1) + 2 * def20_nmax Ms := by
    rcases hL : Ms.length with _ | k
    · exact absurd hL hk0
    · rw [Nat.add_sub_cancel]; ring
  have hkk2 : def20_nmax Ms * (2 * Ms.length - 1) =
      2 * def20_nmax Ms * (Ms.length - 1) + def20_nmax Ms := by
    rcases hL : Ms.length with _ | k
    · exact absurd hL hk0
    · have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [this, Nat.add_sub_cancel]; ring
  have hcross' : ∀ a < Ms.length, ∀ b < Ms.length, a ≠ b →
      ∀ qa ∈ Ss.getD a ∅, ∀ qb ∈ Ss.getD b ∅, sumDiag qa ≠ sumDiag qb := by
    intro a ha b hb hab
    exact hcross a (by omega) b (by omega) hab
  rw [def20, if_neg hk0]
  simp only [Inst4.IsSol, Inst4.toInst3, Inst3.IsSol, Finset.card_empty, add_zero,
    Finset.empty_subset, true_and, Finset.sdiff_empty]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- cardinality
    have hdisjS : ((Finset.range Ms.length : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun a => shiftSet (Ss.getD a ∅) (def20_alpha Ms a, def20_beta Ms a)) := by
      intro a ha b hb hab
      rw [Function.onFun, Finset.disjoint_left]
      intro q hqa hqb
      simp only [shiftSet, Finset.mem_image, def20_alpha, def20_beta] at hqa hqb
      obtain ⟨p, hp, rfl⟩ := hqa
      obtain ⟨p', hp', hpp⟩ := hqb
      have h1 := (hq a (by simpa using ha) p hp).1
      have h2 := (hq b (by simpa using hb) p' hp').1
      have := congrArg Prod.fst hpp
      simp only [Prod.fst_add] at this
      exact band_nat (def20_nmax Ms) p'.1 p.1 b a h2 h1 (Ne.symm hab) this
    have hdisjC : ((Finset.univ : Finset (Fin Ms.length)) : Set (Fin Ms.length)).PairwiseDisjoint
        (fun a => (Ms.get a).C.image (fun c => c + def20_alpha Ms a)) := by
      intro a _ b _ hab
      rw [Function.onFun, Finset.disjoint_left]
      intro c hca hcb
      simp only [Finset.mem_image, def20_alpha] at hca hcb
      obtain ⟨x, hx, rfl⟩ := hca
      obtain ⟨y, hy, hxy⟩ := hcb
      obtain ⟨_, hC, _⟩ := gadget_facts _ _ (hval a a.2).1 (hsol a a.2)
      obtain ⟨_, hC', _⟩ := gadget_facts _ _ (hval b b.2).1 (hsol b b.2)
      have hna := hnle _ (List.get_mem Ms ⟨a.1, a.2⟩)
      have hnb := hnle _ (List.get_mem Ms ⟨b.1, b.2⟩)
      have h1 : x < def20_nmax Ms := by have := hC _ hx; omega
      have h2 : y < def20_nmax Ms := by have := hC' _ hy; omega
      exact band_nat (def20_nmax Ms) y x b a h2 h1 (fun h => hab (Fin.ext h).symm) hxy
    unfold lemma21_map
    rw [Finset.card_biUnion hdisjS, Finset.card_biUnion hdisjC, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.card_image_of_injective _ (add_left_injective _), shiftSet,
      Finset.card_image_of_injective _ (add_left_injective _)]
    obtain ⟨_, _, _, _, hcard, _⟩ := gadget_facts _ _ (hval a a.2).1 (hsol a a.2)
    exact hcard
  · -- non-attacking
    intro q₁ h₁ q₂ h₂ hatt
    obtain ⟨a, ha, p₁, hp₁, rfl⟩ := (hmem q₁).mp h₁
    obtain ⟨b, hb, p₂, hp₂, rfl⟩ := (hmem q₂).mp h₂
    obtain ⟨hne, hl⟩ := hatt
    simp only [col, row, sumDiag, diffDiag, Prod.fst_add, Prod.snd_add, ne_eq] at hne hl
    obtain ⟨f₁, g₁, _, _, _⟩ := hq a ha p₁ hp₁
    obtain ⟨f₂, g₂, _, _, _⟩ := hq b hb p₂ hp₂
    by_cases hab : a = b
    · subst hab
      obtain ⟨_, _, _, _, _, hNA, _⟩ := gadget_facts _ _ (hval a ha).1 (hsol a ha)
      apply hNA p₁ hp₁ p₂ hp₂
      refine ⟨fun h => hne (by rw [h]), ?_⟩
      simp only [col, row, sumDiag, diffDiag]
      rcases hl with h | h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inr (by push_cast at h; linarith)))
    · rcases hl with h | h | h | h
      · exact band_nat (def20_nmax Ms) p₁.1 p₂.1 a b f₁ f₂ hab h
      · exact band_nat (def20_nmax Ms) p₁.2 p₂.2 (Ms.length - 1 - a) (Ms.length - 1 - b) g₁ g₂
          (by omega) h
      · apply hcross' a ha b hb hab p₁ hp₁ p₂ hp₂
        have ta := hT a ha
        have tb := hT b hb
        simp only [sumDiag]
        omega
      · have ta := hTz a ha
        have tb := hTz b hb
        push_cast at h
        apply band_int (def20_nmax Ms) ((p₁.1 : ℤ) - p₁.2) ((p₂.1 : ℤ) - p₂.2) a b
          (by rw [abs_lt]; constructor <;> omega) (by rw [abs_lt]; constructor <;> omega) hab
        linarith
  · -- columns and rows
    intro q hq'
    obtain ⟨a, ha, p, hp, rfl⟩ := (hmem q).mp hq'
    obtain ⟨_, _, hc, hr, _⟩ := hq a ha p hp
    simp only [col, row, Prod.fst_add, Prod.snd_add, Finset.mem_biUnion, Finset.mem_univ,
      true_and, Finset.mem_image, def20_alpha, def20_beta]
    exact ⟨⟨⟨a, ha⟩, p.1, hc, rfl⟩, ⟨⟨a, ha⟩, p.2, hr, rfl⟩⟩
  · -- excluded diagonals
    intro q hq'
    obtain ⟨a, ha, p, hp, rfl⟩ := (hmem q).mp hq'
    obtain ⟨f, g, _, _, hd⟩ := hq a ha p hp
    constructor
    · intro hmemD
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, def20_alpha,
        def20_beta] at hmemD
      obtain ⟨b, d, hdb, hdq⟩ := hmemD
      obtain ⟨_, _, _, hDm, _⟩ := gadget_facts _ _ (hval b b.2).1 (hsol b b.2)
      have hnb := hnle _ (List.get_mem Ms ⟨b.1, b.2⟩)
      obtain ⟨hd1, hd2⟩ := hDm d hdb
      simp only [diffDiag, Prod.fst_add, Prod.snd_add] at hdq hd
      push_cast at hdq
      have ta := hTz a ha
      have tb := hTz b b.2
      by_cases hab : a = b
      · subst hab
        apply hd
        have : d = (p.1 : ℤ) - p.2 := by linarith
        rw [this] at hdb
        exact hdb
      · apply band_int (def20_nmax Ms) d ((p.1 : ℤ) - p.2) b a
          (by rw [abs_lt]; constructor <;> omega) (by rw [abs_lt]; constructor <;> omega)
          (fun h => hab h.symm)
        linarith
    · intro hmemD
      simp only [sumDiag, Prod.fst_add, Prod.snd_add, Finset.mem_union, Finset.mem_range,
        Finset.mem_Icc] at hmemD
      have ta := hT a ha
      rcases hmemD with h | ⟨h1, h2⟩
      · omega
      · omega
