-- Prove2me | solution 1 for LodhaMoore.exists_derives_standardForm_le_depth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.878827+00:00
-- url     : https://prove2.me/submissions/3faff9d5-cfbc-42bc-9ca6-31eea2dae7e2

import Mathlib
import Definitions.Def_LodhaMooreWords
import Theorems.Thm_LodhaMoore_exists_derives_standardForm_of_yPow
import Theorems.Thm_LodhaMoore_exists_derives_append_xWord

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

end LodhaMoore
end

section
namespace LodhaMoore

/-- The order condition of Definition 5.1. -/
def OC (W : Word) : Prop :=
  ∀ (i j : ℕ) (hi : i < W.length) (hj : j < W.length) (s t : Seq) (m n : ℤ),
    W[i] = (.y s, m) → W[j] = (.y t, n) → s <+: t → j ≤ i

theorem oc_append {Ξ Υ : Word} (hΞ : ∀ p ∈ Ξ, ∀ t, p.1 ≠ .y t) : OC (Ξ ++ Υ) ↔ OC Υ := by
  constructor
  · intro h i j hi hj s t m n hiv hjv hst
    have := h (Ξ.length + i) (Ξ.length + j) (by simp; omega) (by simp; omega) s t m n
      (by rw [List.getElem_append_right (by omega)]; simpa using hiv)
      (by rw [List.getElem_append_right (by omega)]; simpa using hjv) hst
    omega
  · intro h i j hi hj s t m n hiv hjv hst
    have big : ∀ k (hk : k < (Ξ ++ Υ).length) (u : Seq) (r : ℤ), (Ξ ++ Υ)[k] = (Gen.y u, r) →
        Ξ.length ≤ k := by
      intro k hk u r hk'
      by_contra hc
      push Not at hc
      rw [List.getElem_append_left hc] at hk'
      exact hΞ _ (List.getElem_mem hc) u (by rw [hk'])
    have hi' := big i hi s m hiv
    have hj' := big j hj t n hjv
    rw [List.getElem_append_right hi'] at hiv
    rw [List.getElem_append_right hj'] at hjv
    have := h (i - Ξ.length) (j - Ξ.length) (by simp at hi; omega) (by simp at hj; omega) s t m n hiv hjv hst
    omega

theorem depth_le_of_mem {W : Word} {t : Seq} {n : ℤ} (h : (Gen.y t, n) ∈ W) :
    depth W ≤ (t.length : ℕ∞) := by
  unfold depth
  exact iInf₂_le t ⟨n, h⟩

end LodhaMoore
end

section
namespace LodhaMoore

theorem le_depth_iff {W : Word} {l : ℕ∞} : l ≤ depth W ↔ ∀ t, YOccurs W t → l ≤ t.length := by
  unfold depth; simp [le_iInf_iff]

theorem isStandardForm_of_isXWord {W : Word} (h : IsXWord W) : IsStandardForm W := by
  refine ⟨h.1, ⟨W, [], by simp, h, ⟨by simp [IsWord], by simp⟩⟩, ?_⟩
  intro i j hi hj s t m n hiv
  exfalso
  obtain ⟨u, hu⟩ := h.2 _ (List.getElem_mem hi)
  rw [hiv] at hu; cases hu

theorem depth_eq_top_of_isXWord {W : Word} (h : IsXWord W) : depth W = ⊤ := by
  unfold depth
  simp only [iInf_eq_top]
  rintro t ⟨n, hn⟩
  obtain ⟨u, hu⟩ := h.2 _ hn
  cases hu

theorem isStandardForm_append_yWord {A Υ : Word} {m : ℕ} (hA : IsStandardForm A)
    (hdA : (m : ℕ∞) ≤ depth A) (hΥ : IsYWord Υ) (hshort : ∀ t n, (Gen.y t, n) ∈ Υ → t.length < m)
    (hoc : OC Υ) : IsStandardForm (A ++ Υ) := by
  obtain ⟨hw, ⟨Ξa, Υa, rfl, hΞa, hΥa⟩, hord⟩ := hA
  have hΞy : ∀ p ∈ Ξa, ∀ t, p.1 ≠ .y t := by
    intro p hp t h
    obtain ⟨u, hu⟩ := hΞa.2 p hp
    rw [hu] at h; cases h
  have hlong : ∀ t n, (Gen.y t, n) ∈ Υa → m ≤ t.length := by
    intro t n h
    have := hdA.trans (depth_le_of_mem (List.mem_append_right Ξa h))
    exact_mod_cast this
  have hocA : OC Υa := (oc_append hΞy).1 hord
  refine ⟨?_, ⟨Ξa, Υa ++ Υ, by simp, hΞa, ⟨?_, ?_⟩⟩, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hw p hp
    · exact hΥ.1 p hp
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hw p (List.mem_append_right _ hp)
    · exact hΥ.1 p hp
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hΥa.2 p hp
    · exact hΥ.2 p hp
  · show OC _
    rw [List.append_assoc, oc_append hΞy]
    intro i j hi hj s t a b hiv hjv hst
    simp only [List.length_append] at hi hj
    by_cases hiA : i < Υa.length <;> by_cases hjA : j < Υa.length
    · rw [List.getElem_append_left hiA] at hiv
      rw [List.getElem_append_left hjA] at hjv
      exact hocA i j hiA hjA s t a b hiv hjv hst
    · exfalso
      rw [List.getElem_append_left hiA] at hiv
      rw [List.getElem_append_right (by omega)] at hjv
      have h1 := hlong s a (hiv ▸ List.getElem_mem hiA)
      have h2 := hshort t b (hjv ▸ List.getElem_mem (by omega))
      have := hst.length_le
      omega
    · omega
    · rw [List.getElem_append_right (by omega)] at hiv hjv
      have := hoc (i - Υa.length) (j - Υa.length) (by omega) (by omega) s t a b hiv hjv hst
      omega

/-- A bound for the lengths of the `y`-indices of a word. -/
def ylen (Υ : Word) : ℕ := (Υ.map fun p => match p.1 with | .x u => u.length | .y u => u.length).sum

theorem lt_ylen {Υ : Word} {t : Seq} {n : ℤ} (h : (Gen.y t, n) ∈ Υ) : t.length < ylen Υ + 1 := by
  have := List.single_le_sum (l := Υ.map fun p => match p.1 with | .x u => u.length | .y u => u.length)
    (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨_, h, rfl⟩)
  simp only at this
  unfold ylen; omega

theorem combine {Ω₀ Ω₁ : Word} (l : ℕ)
    (ih₀ : ∀ l : ℕ, ∃ W', Derives Ω₀ W' ∧ IsStandardForm W' ∧ (l : ℕ∞) ≤ depth W')
    (ih₁ : ∀ l : ℕ, ∃ W', Derives Ω₁ W' ∧ IsStandardForm W' ∧ (l : ℕ∞) ≤ depth W') :
    ∃ W', Derives (Ω₀ ++ Ω₁) W' ∧ IsStandardForm W' ∧ (l : ℕ∞) ≤ depth W' := by
  obtain ⟨W₁, d₁, sf₁, dep₁⟩ := ih₁ l
  have sf₁' := sf₁
  obtain ⟨hw₁, ⟨Ξ, Υ, rfl, hΞ, hΥ⟩, hord₁⟩ := sf₁'
  have hΞy : ∀ p ∈ Ξ, ∀ t, p.1 ≠ .y t := by
    intro p hp t h
    obtain ⟨u, hu⟩ := hΞ.2 p hp
    rw [hu] at h; cases h
  obtain ⟨l₀, h53⟩ := exists_derives_append_xWord Ξ hΞ
  set m := l + ylen Υ + 1 with hm
  obtain ⟨W₀, d₀, sf₀, dep₀⟩ := ih₀ (m + Word.wordLength Ξ + l₀)
  obtain ⟨W₀', d₀', sf₀', dep₀'⟩ := h53 W₀ sf₀ (le_trans (by exact_mod_cast (by omega)) dep₀)
  have hdm : (m : ℕ∞) ≤ depth W₀' := by
    refine le_trans ?_ dep₀'
    induction h : depth W₀ using ENat.recTopCoe with
    | top => simp
    | coe d =>
      rw [h] at dep₀
      have h' : m + Word.wordLength Ξ + l₀ ≤ d := by exact_mod_cast dep₀
      have : ((d : ℕ∞) - (Word.wordLength Ξ : ℕ∞)) = ((d - Word.wordLength Ξ : ℕ) : ℕ∞) := by simp
      rw [this]
      exact_mod_cast (by omega : m ≤ d - Word.wordLength Ξ)
  refine ⟨W₀' ++ Υ, ?_, ?_, ?_⟩
  · have e1 := d₁.context Ω₀ []
    have e2 := d₀.context [] (Ξ ++ Υ)
    have e3 := d₀'.context [] Υ
    simp only [List.append_nil, List.nil_append] at e1 e2 e3
    refine (e1.trans (by simpa [Derives] using e2)).trans ?_
    simpa [Derives] using e3
  · exact isStandardForm_append_yWord sf₀' hdm hΥ (fun t n h => by have := lt_ylen h; omega)
      ((oc_append hΞy).1 hord₁)
  · rw [le_depth_iff]
    rintro t ⟨n, hn⟩
    rcases List.mem_append.1 hn with hn | hn
    · have := hdm.trans (depth_le_of_mem hn)
      exact le_trans (by exact_mod_cast (by omega : l ≤ m)) this
    · exact dep₁.trans (depth_le_of_mem (List.mem_append_right Ξ hn))

theorem exists_derives_standardForm_le_depth_aux : ∀ N : ℕ, ∀ W : Word, IsWord W →
    Word.wordLength W = N → ∀ l : ℕ, ∃ W', Derives W W' ∧ IsStandardForm W' ∧ (l : ℕ∞) ≤ depth W' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro W hW hN l
  match W, hW, hN with
  | [], _, _ =>
    exact ⟨[], Relation.ReflTransGen.refl, isStandardForm_of_isXWord ⟨by simp [IsWord], by simp⟩,
      by rw [depth_eq_top_of_isXWord ⟨by simp [IsWord], by simp⟩]; exact le_top⟩
  | [(g, n)], hW, hN =>
    have hn : n ≠ 0 := hW (g, n) (by simp)
    by_cases h1 : n.natAbs = 1
    · have he : n = 1 ∨ n = -1 := by omega
      cases g with
      | x s =>
        have hx : IsXWord [(Gen.x s, n)] := ⟨hW, by simp⟩
        exact ⟨_, Relation.ReflTransGen.refl, isStandardForm_of_isXWord hx,
          by rw [depth_eq_top_of_isXWord hx]; exact le_top⟩
      | y s =>
        obtain ⟨W', d, sf, -, hy, -⟩ := exists_derives_standardForm_of_yPow s l n he
        refine ⟨W', d, sf, ?_⟩
        rw [le_depth_iff]
        rintro t ⟨m, hm⟩
        exact_mod_cast (hy t m hm).2.1
    · -- split the exponent
      set e : ℤ := if 0 < n then 1 else -1 with he_def
      have he0 : e ≠ 0 := by by_cases h : 0 < n <;> simp [he_def, h]
      have hne : n - e ≠ 0 := by by_cases h : 0 < n <;> simp [he_def, h] <;> omega
      have hsign : 0 < e * (n - e) := by by_cases h : 0 < n <;> simp [he_def, h] <;> omega
      have hsplit := Relation.ReflTransGen.single (Step.split [] [] g e (n - e) he0 hne hsign)
      rw [show e + (n - e) = n by ring] at hsplit
      simp only [List.append_nil, List.nil_append] at hsplit
      have hwl : ∀ k : ℤ, Word.wordLength [(g, k)] = k.natAbs := by intro k; simp [Word.wordLength]
      have hN1 : Word.wordLength [(g, n)] = n.natAbs := hwl n
      have h0 := ih e.natAbs (by rw [← hN, hN1]; by_cases h : 0 < n <;> simp [he_def, h] <;> omega)
        [(g, e)] (by intro p hp; simp at hp; subst hp; exact he0) (hwl e)
      have h1' := ih (n - e).natAbs (by rw [← hN, hN1]; by_cases h : 0 < n <;> simp [he_def, h] <;> omega)
        [(g, n - e)] (by intro p hp; simp at hp; subst hp; exact hne) (hwl _)
      obtain ⟨W', d, sf, dep⟩ := combine (Ω₀ := [(g, e)]) (Ω₁ := [(g, n - e)]) l h0 h1'
      exact ⟨W', (by simpa [Derives] using hsplit : Derives [(g, n)] [(g, e), (g, n - e)]).trans d, sf, dep⟩
  | p :: q :: rest, hW, hN =>
    have hwl : ∀ A B : Word, Word.wordLength (A ++ B) = Word.wordLength A + Word.wordLength B := by
      intro A B; simp [Word.wordLength]
    have hpos : ∀ r ∈ (p :: q :: rest), 0 < r.2.natAbs := fun r hr => Int.natAbs_pos.2 (hW r hr)
    have hA : 0 < Word.wordLength [p] := by simp [Word.wordLength]; exact hW p (by simp)
    have hB : 0 < Word.wordLength (q :: rest) := by
      simp only [Word.wordLength, List.map_cons, List.sum_cons]
      have := hpos q (by simp); omega
    have hsplitN : Word.wordLength (p :: q :: rest) = Word.wordLength [p] + Word.wordLength (q :: rest) := by
      rw [← hwl]; rfl
    have h0 := ih _ (by omega) [p] (fun r hr => hW r (by simp at hr; simp [hr])) rfl
    have h1 := ih _ (by omega) (q :: rest) (fun r hr => hW r (List.mem_cons_of_mem _ hr)) rfl
    simpa using combine (Ω₀ := [p]) (Ω₁ := q :: rest) l h0 h1

end LodhaMoore

end

section
open LodhaMoore
theorem solution (W : Word) (hW : IsWord W) (l : ℕ) :
    ∃ W', Derives W W' ∧ IsStandardForm W' ∧ (l : ℕ∞) ≤ depth W' :=
  exists_derives_standardForm_le_depth_aux _ W hW rfl l
end
