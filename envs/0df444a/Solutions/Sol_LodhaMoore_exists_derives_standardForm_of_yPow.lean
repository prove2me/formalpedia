-- Prove2me | solution 1 for LodhaMoore.exists_derives_standardForm_of_yPow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.58234+00:00
-- url     : https://prove2.me/submissions/85b3b680-da1d-4974-841f-bbde2d9f5fa6

import Mathlib
import Definitions.Def_LodhaMooreWords

section
namespace LodhaMoore

theorem Step.context {W W' : Word} (h : Step W W') (p q : Word) :
    Step (p ++ W ++ q) (p ++ W' ++ q) := by
  cases h with
  | moveX pre post s t t' i h =>
    simpa [List.append_assoc] using Step.moveX (p ++ pre) (post ++ q) s t t' i h
  | moveXInv pre post s t t' i h =>
    simpa [List.append_assoc] using Step.moveXInv (p ++ pre) (post ++ q) s t t' i h
  | expand pre post s => simpa [List.append_assoc] using Step.expand (p ++ pre) (post ++ q) s
  | expandInv pre post s => simpa [List.append_assoc] using Step.expandInv (p ++ pre) (post ++ q) s
  | commute pre post u v i j h =>
    simpa [List.append_assoc] using Step.commute (p ++ pre) (post ++ q) u v i j h
  | split pre post g i j hi hj hij =>
    simpa [List.append_assoc] using Step.split (p ++ pre) (post ++ q) g i j hi hj hij
  | merge pre post g i j hi hj hij =>
    simpa [List.append_assoc] using Step.merge (p ++ pre) (post ++ q) g i j hi hj hij
  | cancel pre post s i hi => simpa [List.append_assoc] using Step.cancel (p ++ pre) (post ++ q) s i hi

theorem Derives.context {W W' : Word} (h : Derives W W') (p q : Word) :
    Derives (p ++ W ++ q) (p ++ W' ++ q) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (hs.context p q)

theorem Derives.append {A A' B B' : Word} (hA : Derives A A') (hB : Derives B B') :
    Derives (A ++ B) (A' ++ B') := by
  have h1 := hA.context [] B
  have h2 := hB.context A' []
  simp only [List.nil_append, List.append_nil] at h1 h2
  exact h1.trans h2

theorem xFin_of_incompatible {s t : Seq} (h : Incompatible s t) : xFin s t = some t := by
  unfold xFin; rw [if_neg h.1, if_neg h.2]

theorem xFinInv_of_incompatible {s t : Seq} (h : Incompatible s t) : xFinInv s t = some t := by
  unfold xFinInv; rw [if_neg h.1, if_neg h.2]

theorem Incompatible.symm' {s t : Seq} (h : Incompatible s t) : Incompatible t s := ⟨h.2, h.1⟩

theorem Incompatible.mono {a b a' b' : Seq} (h : Incompatible a b) (ha : a <+: a') (hb : b <+: b') :
    Incompatible a' b' := by
  constructor
  · intro hab
    rcases List.prefix_or_prefix_of_prefix (ha.trans hab) hb with h1 | h1
    · exact h.1 h1
    · exact h.2 h1
  · intro hba
    rcases List.prefix_or_prefix_of_prefix ha (hb.trans hba) with h1 | h1
    · exact h.1 h1
    · exact h.2 h1

theorem derives_swap {u t : Seq} {e i : ℤ} (he : e = 1 ∨ e = -1) (h : Incompatible u t) :
    Derives [(.y t, i), (.x u, e)] [(.x u, e), (.y t, i)] := by
  rcases he with rfl | rfl
  · simpa [Derives] using Relation.ReflTransGen.single (Step.moveX [] [] u t t i (xFin_of_incompatible h))
  · simpa [Derives] using Relation.ReflTransGen.single (Step.moveXInv [] [] u t t i (xFinInv_of_incompatible h))

theorem derives_moveX1 {u : Seq} {e : ℤ} (he : e = 1 ∨ e = -1) :
    ∀ Υ : Word, (∀ p ∈ Υ, ∃ t, p.1 = .y t ∧ Incompatible u t) →
      Derives (Υ ++ [(.x u, e)]) ((.x u, e) :: Υ)
  | [], _ => Relation.ReflTransGen.refl
  | (g, i) :: Υ, h => by
    obtain ⟨t, hp, hut⟩ := h (g, i) (by simp)
    simp only at hp
    subst hp
    have ih := derives_moveX1 he Υ (fun q hq => h q (by simp [hq]))
    have h1 := ih.context [(.y t, i)] []
    have h2 := (derives_swap (i := i) he hut).context [] Υ
    simp only [List.append_nil, List.nil_append] at h1 h2
    have := h1.trans (by simpa [Derives] using h2)
    simpa [Derives] using this

theorem derives_moveXs :
    ∀ (Ξ Υ : Word), (∀ p ∈ Ξ, ∃ u, p.1 = .x u ∧ (p.2 = 1 ∨ p.2 = -1) ∧
        ∀ q ∈ Υ, ∃ t, q.1 = .y t ∧ Incompatible u t) →
      Derives (Υ ++ Ξ) (Ξ ++ Υ)
  | [], Υ, _ => by simpa [Derives] using Relation.ReflTransGen.refl
  | (g, e) :: Ξ, Υ, h => by
    obtain ⟨u, hg, he, hΥ⟩ := h (g, e) (by simp)
    simp only at hg he
    subst hg
    have h1 := (derives_moveX1 he Υ hΥ).context [] Ξ
    have ih := derives_moveXs Ξ Υ (fun p hp => h p (by simp [hp]))
    have h2 := ih.context [(.x u, e)] []
    simp only [List.append_nil, List.nil_append] at h1 h2
    have := h1.trans (by simpa [Derives] using h2)
    simpa [Derives] using this

/-- The invariant of Lemma 5.2's induction: an `X`-part with exponents `±1` and indices extending
`s`, then a `Y`-part with exponents `±1`, indices extending `s` of length at least `l`, pairwise
incompatible. -/
def Good (s : Seq) (l : ℕ) (Ξ Υ : Word) : Prop :=
  (∀ p ∈ Ξ, ∃ u, p.1 = .x u ∧ s <+: u ∧ (p.2 = 1 ∨ p.2 = -1)) ∧
  (∀ p ∈ Υ, ∃ u, p.1 = .y u ∧ s <+: u ∧ l ≤ u.length ∧ (p.2 = 1 ∨ p.2 = -1)) ∧
  Υ.Pairwise (fun p q => ∃ u v, p.1 = .y u ∧ q.1 = .y v ∧ Incompatible u v)

theorem good_combine {s c₁ c₂ c₃ : Seq} {l : ℕ} {e : ℤ} (he : e = 1 ∨ e = -1)
    (h₁ : s <+: c₁) (h₂ : s <+: c₂) (h₃ : s <+: c₃)
    (i₁₂ : Incompatible c₁ c₂) (i₁₃ : Incompatible c₁ c₃) (i₂₃ : Incompatible c₂ c₃)
    {Ξ₁ Υ₁ Ξ₂ Υ₂ Ξ₃ Υ₃ : Word} (g₁ : Good c₁ l Ξ₁ Υ₁) (g₂ : Good c₂ l Ξ₂ Υ₂) (g₃ : Good c₃ l Ξ₃ Υ₃) :
    Derives ((.x s, e) :: (Ξ₁ ++ Υ₁ ++ (Ξ₂ ++ Υ₂) ++ (Ξ₃ ++ Υ₃)))
      ((.x s, e) :: (Ξ₁ ++ Ξ₂ ++ Ξ₃) ++ (Υ₁ ++ Υ₂ ++ Υ₃)) ∧
    Good s l ((.x s, e) :: (Ξ₁ ++ Ξ₂ ++ Ξ₃)) (Υ₁ ++ Υ₂ ++ Υ₃) := by
  -- Ξ₂ moves left past Υ₁
  have m₂ : Derives (Υ₁ ++ Ξ₂) (Ξ₂ ++ Υ₁) := by
    apply derives_moveXs
    intro p hp
    obtain ⟨u, hu, hsu, hpe⟩ := g₂.1 p hp
    refine ⟨u, hu, hpe, fun q hq => ?_⟩
    obtain ⟨t, ht, hst, -, -⟩ := g₁.2.1 q hq
    exact ⟨t, ht, (i₁₂.mono hst hsu).symm'⟩
  -- Ξ₃ moves left past Υ₁ ++ Υ₂
  have m₃ : Derives ((Υ₁ ++ Υ₂) ++ Ξ₃) (Ξ₃ ++ (Υ₁ ++ Υ₂)) := by
    apply derives_moveXs
    intro p hp
    obtain ⟨u, hu, hsu, hpe⟩ := g₃.1 p hp
    refine ⟨u, hu, hpe, fun q hq => ?_⟩
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨t, ht, hst, -, -⟩ := g₁.2.1 q hq
      exact ⟨t, ht, (i₁₃.mono hst hsu).symm'⟩
    · obtain ⟨t, ht, hst, -, -⟩ := g₂.2.1 q hq
      exact ⟨t, ht, (i₂₃.mono hst hsu).symm'⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have d1 := m₂.context ((.x s, e) :: Ξ₁) (Υ₂ ++ (Ξ₃ ++ Υ₃))
    have d2 := m₃.context ((.x s, e) :: (Ξ₁ ++ Ξ₂)) Υ₃
    have := d1.trans (by simpa [Derives] using d2)
    simpa [Derives] using this
  · intro p hp
    simp only [List.mem_cons, List.mem_append] at hp
    rcases hp with rfl | (hp | hp) | hp
    · exact ⟨s, rfl, List.prefix_refl s, he⟩
    · obtain ⟨u, hu, hcu, hpe⟩ := g₁.1 p hp; exact ⟨u, hu, h₁.trans hcu, hpe⟩
    · obtain ⟨u, hu, hcu, hpe⟩ := g₂.1 p hp; exact ⟨u, hu, h₂.trans hcu, hpe⟩
    · obtain ⟨u, hu, hcu, hpe⟩ := g₃.1 p hp; exact ⟨u, hu, h₃.trans hcu, hpe⟩
  · intro p hp
    simp only [List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · obtain ⟨u, hu, hcu, hl, hpe⟩ := g₁.2.1 p hp; exact ⟨u, hu, h₁.trans hcu, hl, hpe⟩
    · obtain ⟨u, hu, hcu, hl, hpe⟩ := g₂.2.1 p hp; exact ⟨u, hu, h₂.trans hcu, hl, hpe⟩
    · obtain ⟨u, hu, hcu, hl, hpe⟩ := g₃.2.1 p hp; exact ⟨u, hu, h₃.trans hcu, hl, hpe⟩
  · have cross : ∀ {c c' : Seq} {Ξ Υ Ξ' Υ' : Word}, Incompatible c c' → Good c l Ξ Υ →
        Good c' l Ξ' Υ' → ∀ p ∈ Υ, ∀ q ∈ Υ', ∃ u v, p.1 = .y u ∧ q.1 = .y v ∧ Incompatible u v := by
      intro c c' Ξ Υ Ξ' Υ' hcc g g' p hp q hq
      obtain ⟨u, hu, hcu, -, -⟩ := g.2.1 p hp
      obtain ⟨v, hv, hcv, -, -⟩ := g'.2.1 q hq
      exact ⟨u, v, hu, hv, hcc.mono hcu hcv⟩
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨g₁.2.2, g₂.2.2, cross i₁₂ g₁ g₂⟩, g₃.2.2, ?_⟩
    intro p hp q hq
    rcases List.mem_append.1 hp with hp | hp
    · exact cross i₁₃ g₁ g₃ p hp q hq
    · exact cross i₂₃ g₂ g₃ p hp q hq

theorem incompat_app {s a b : Seq} {x y : Bool} (hxy : x ≠ y) :
    Incompatible (s ++ x :: a) (s ++ y :: b) := by
  constructor
  · intro h
    rw [List.prefix_append_right_inj] at h
    exact hxy (List.cons_prefix_cons.1 h).1
  · intro h
    rw [List.prefix_append_right_inj] at h
    exact hxy (List.cons_prefix_cons.1 h).1.symm

theorem exists_good (l : ℕ) :
    ∀ k : ℕ, ∀ (s : Seq) (ε : ℤ), l - s.length ≤ k → (ε = 1 ∨ ε = -1) →
      ∃ Ξ Υ, Derives [(.y s, ε)] (Ξ ++ Υ) ∧ Good s l Ξ Υ := by
  intro k
  induction k with
  | zero =>
    intro s ε hk hε
    refine ⟨[], [(.y s, ε)], Relation.ReflTransGen.refl, by simp, ?_, by simp⟩
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨s, rfl, List.prefix_refl s, by omega, hε⟩
  | succ k ih =>
    intro s ε hk hε
    by_cases hl : l ≤ s.length
    · refine ⟨[], [(.y s, ε)], Relation.ReflTransGen.refl, by simp, ?_, by simp⟩
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨s, rfl, List.prefix_refl s, hl, hε⟩
    rcases hε with rfl | rfl
    · obtain ⟨Ξ₁, Υ₁, d₁, g₁⟩ := ih (s ++ [false]) 1 (by simp; omega) (Or.inl rfl)
      obtain ⟨Ξ₂, Υ₂, d₂, g₂⟩ := ih (s ++ [true, false]) (-1) (by simp; omega) (Or.inr rfl)
      obtain ⟨Ξ₃, Υ₃, d₃, g₃⟩ := ih (s ++ [true, true]) 1 (by simp; omega) (Or.inl rfl)
      obtain ⟨dc, gc⟩ := good_combine (s := s) (e := 1) (Or.inl rfl) (List.prefix_append _ _)
        (List.prefix_append _ _) (List.prefix_append _ _) (incompat_app (by decide))
        (incompat_app (by decide)) (incompat_app (s := s ++ [true]) (a := []) (b := []) (by decide) |>
          fun h => by simpa [Derives] using h) g₁ g₂ g₃
      refine ⟨_, _, ?_, gc⟩
      have e1 : Derives [(.y s, 1)] [(.x s, 1), (.y (s ++ [false]), 1), (.y (s ++ [true, false]), -1),
          (.y (s ++ [true, true]), 1)] := by
        simpa [Derives] using Relation.ReflTransGen.single (Step.expand [] [] s)
      have e2 : Derives [(.x s, 1), (.y (s ++ [false]), 1), (.y (s ++ [true, false]), -1),
          (.y (s ++ [true, true]), 1)] ((.x s, 1) :: (Ξ₁ ++ Υ₁ ++ (Ξ₂ ++ Υ₂) ++ (Ξ₃ ++ Υ₃))) := by
        have := (((d₁.append d₂).append d₃).context [(.x s, 1)] [])
        simpa [Derives] using this
      exact (e1.trans e2).trans dc
    · obtain ⟨Ξ₁, Υ₁, d₁, g₁⟩ := ih (s ++ [false, false]) (-1) (by simp; omega) (Or.inr rfl)
      obtain ⟨Ξ₂, Υ₂, d₂, g₂⟩ := ih (s ++ [false, true]) 1 (by simp; omega) (Or.inl rfl)
      obtain ⟨Ξ₃, Υ₃, d₃, g₃⟩ := ih (s ++ [true]) (-1) (by simp; omega) (Or.inr rfl)
      obtain ⟨dc, gc⟩ := good_combine (s := s) (e := -1) (Or.inr rfl) (List.prefix_append _ _)
        (List.prefix_append _ _) (List.prefix_append _ _)
        (incompat_app (s := s ++ [false]) (a := []) (b := []) (by decide) |> fun h => by simpa [Derives] using h)
        (incompat_app (by decide)) (incompat_app (by decide)) g₁ g₂ g₃
      refine ⟨_, _, ?_, gc⟩
      have e1 : Derives [(.y s, -1)] [(.x s, -1), (.y (s ++ [false, false]), -1),
          (.y (s ++ [false, true]), 1), (.y (s ++ [true]), -1)] := by
        simpa [Derives] using Relation.ReflTransGen.single (Step.expandInv [] [] s)
      have e2 : Derives [(.x s, -1), (.y (s ++ [false, false]), -1), (.y (s ++ [false, true]), 1),
          (.y (s ++ [true]), -1)] ((.x s, -1) :: (Ξ₁ ++ Υ₁ ++ (Ξ₂ ++ Υ₂) ++ (Ξ₃ ++ Υ₃))) := by
        have := (((d₁.append d₂).append d₃).context [(.x s, -1)] [])
        simpa [Derives] using this
      exact (e1.trans e2).trans dc

end LodhaMoore
end

section
open LodhaMoore
theorem solution (s : Seq) (l : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ W, Derives [(.y s, ε)] W ∧ IsStandardForm W ∧
      (∀ u n, (Gen.x u, n) ∈ W → s <+: u) ∧
      (∀ u n, (Gen.y u, n) ∈ W → s <+: u ∧ l ≤ u.length ∧ (n = 1 ∨ n = -1)) ∧
      (∀ u v, YOccurs W u → YOccurs W v → u ≠ v → Incompatible u v) := by
  obtain ⟨Ξ, Υ, d, gΞ, gΥ, gP⟩ := exists_good l (l - s.length) s ε le_rfl hε
  have notY : ∀ u n, (Gen.y u, n) ∉ Ξ := fun u n h => by
    obtain ⟨v, hv, -, -⟩ := gΞ _ h; cases hv
  have notX : ∀ u n, (Gen.x u, n) ∉ Υ := fun u n h => by
    obtain ⟨v, hv, -, -, -⟩ := gΥ _ h; cases hv
  have memY : ∀ u n, (Gen.y u, n) ∈ Ξ ++ Υ → (Gen.y u, n) ∈ Υ := fun u n h => by
    rcases List.mem_append.1 h with h | h
    · exact absurd h (notY u n)
    · exact h
  have nz : ∀ p ∈ Ξ ++ Υ, p.2 ≠ 0 := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨-, -, -, h⟩ := gΞ p hp; rcases h with h | h <;> rw [h] <;> decide
    · obtain ⟨-, -, -, -, h⟩ := gΥ p hp; rcases h with h | h <;> rw [h] <;> decide
  refine ⟨Ξ ++ Υ, d, ⟨nz, ⟨Ξ, Υ, rfl, ⟨fun p hp => nz p (List.mem_append_left _ hp), fun p hp => ?_⟩,
    ⟨fun p hp => nz p (List.mem_append_right _ hp), fun p hp => ?_⟩⟩, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨u, hu, -, -⟩ := gΞ p hp; exact ⟨u, hu⟩
  · obtain ⟨u, hu, -, -, -⟩ := gΥ p hp; exact ⟨u, hu⟩
  · intro i j hi hj s' t m n hiW hjW hst
    by_contra hlt
    push_neg at hlt
    have big : ∀ k (hk : k < (Ξ ++ Υ).length) (u : Seq) (r : ℤ), (Ξ ++ Υ)[k] = (Gen.y u, r) →
        Ξ.length ≤ k := by
      intro k hk u r hk'
      by_contra hc
      push_neg at hc
      rw [List.getElem_append_left hc] at hk'
      exact notY u r (hk' ▸ List.getElem_mem hc)
    have hi' := big i hi s' m hiW
    have hj' := big j hj t n hjW
    rw [List.getElem_append_right hi'] at hiW
    rw [List.getElem_append_right hj'] at hjW
    have hlen : ∀ k, k < (Ξ ++ Υ).length → Ξ.length ≤ k → k - Ξ.length < Υ.length := by
      intro k hk hk'; simp at hk; omega
    obtain ⟨u, v, hu, hv, hinc⟩ := List.pairwise_iff_getElem.1 gP (i - Ξ.length) (j - Ξ.length)
      (hlen i hi hi') (hlen j hj hj') (by omega)
    rw [hiW] at hu; rw [hjW] at hv
    simp only [Gen.y.injEq] at hu hv
    subst hu; subst hv
    exact hinc.1 hst
  · intro u n h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨v, hv, hsv, -⟩ := gΞ _ h
      simp only [Gen.x.injEq] at hv; subst hv; exact hsv
    · exact absurd h (notX u n)
  · intro u n h
    obtain ⟨v, hv, hsv, hl, hn⟩ := gΥ _ (memY u n h)
    simp only [Gen.y.injEq] at hv; subst hv
    exact ⟨hsv, hl, hn⟩
  · rintro u v ⟨m, hm⟩ ⟨n, hn⟩ huv
    have hm' := memY u m hm
    have hn' := memY v n hn
    obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.1 hm'
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.1 hn'
    have hij : i ≠ j := by
      rintro rfl; apply huv; rw [hiu] at hjv; simpa using congrArg Prod.fst hjv
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · obtain ⟨a, b, ha, hb, hab⟩ := List.pairwise_iff_getElem.1 gP i j hi hj h
      rw [hiu] at ha; rw [hjv] at hb
      simp only [Gen.y.injEq] at ha hb
      subst ha; subst hb
      exact hab
    · obtain ⟨a, b, ha, hb, hab⟩ := List.pairwise_iff_getElem.1 gP j i hj hi h
      rw [hjv] at ha; rw [hiu] at hb
      simp only [Gen.y.injEq] at ha hb
      subst ha; subst hb
      exact hab.symm'
end
