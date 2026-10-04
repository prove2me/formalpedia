-- Prove2me | solution 1 for LodhaMoore.exists_derives_append_xWord
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.982251+00:00
-- url     : https://prove2.me/submissions/b3751582-9d31-40d5-a052-5a993750a9d5

import Mathlib
import Definitions.Def_LodhaMooreWords
import Definitions.Def_LodhaMoore

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

/-- The tail action of `x` on finite sequences: `00r ↦ 0r`, `01r ↦ 10r`, `1r ↦ 11r`. -/
def xr : List Bool → Option (List Bool)
  | false :: false :: r => some (false :: r)
  | false :: true :: r => some (true :: false :: r)
  | true :: r => some (true :: true :: r)
  | _ => none

/-- The tail action of `x⁻¹`: `0r ↦ 00r`, `10r ↦ 01r`, `11r ↦ 1r`. -/
def xrInv : List Bool → Option (List Bool)
  | false :: r => some (false :: false :: r)
  | true :: false :: r => some (false :: true :: r)
  | true :: true :: r => some (true :: r)
  | _ => none

theorem xFin_append (s r : Seq) : xFin s (s ++ r) = (xr r).map (s ++ ·) := by
  unfold xFin
  rw [if_pos (List.prefix_append _ _)]
  simp only [List.drop_left]
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> rfl

theorem xFinInv_append (s r : Seq) : xFinInv s (s ++ r) = (xrInv r).map (s ++ ·) := by
  unfold xFinInv
  rw [if_pos (List.prefix_append _ _)]
  simp only [List.drop_left]
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> rfl

theorem xr_defined {r : List Bool} (h : 2 ≤ r.length) :
    ∃ r', xr r = some r' ∧ r.length ≤ r'.length + 1 := by
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> simp_all [xr] <;> omega

theorem xrInv_defined {r : List Bool} (h : 2 ≤ r.length) :
    ∃ r', xrInv r = some r' ∧ r.length ≤ r'.length + 1 := by
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> simp_all [xrInv] <;> omega

theorem xr_prefix {r q r' q' : List Bool} (hr : xr r = some r') (hq : xr q = some q')
    (h : r' <+: q') : r <+: q := by
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> rcases q with _ | ⟨_ | _, _ | ⟨_ | _, q⟩⟩ <;>
    simp only [xr, reduceCtorEq, Option.some.injEq] at hr hq <;> (try subst hr) <;> (try subst hq) <;>
    simp_all [List.cons_prefix_cons]

theorem xrInv_prefix {r q r' q' : List Bool} (hr : xrInv r = some r') (hq : xrInv q = some q')
    (h : r' <+: q') : r <+: q := by
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> rcases q with _ | ⟨_ | _, _ | ⟨_ | _, q⟩⟩ <;>
    simp only [xrInv, reduceCtorEq, Option.some.injEq] at hr hq <;> (try subst hr) <;> (try subst hq) <;>
    simp_all [List.cons_prefix_cons]

/-- `t.x_s^e` for `e = ±1`. -/
def xAct (e : ℤ) (s t : Seq) : Option Seq := if e = 1 then xFin s t else xFinInv s t

theorem xFin_of_not_prefix {s t : Seq} (h : ¬ s <+: t) (hl : s.length < t.length) : xFin s t = some t := by
  unfold xFin; rw [if_neg h, if_neg (fun h' => by have := h'.length_le; omega)]

theorem xFinInv_of_not_prefix {s t : Seq} (h : ¬ s <+: t) (hl : s.length < t.length) :
    xFinInv s t = some t := by
  unfold xFinInv; rw [if_neg h, if_neg (fun h' => by have := h'.length_le; omega)]

theorem xAct_defined {e : ℤ} (he : e = 1 ∨ e = -1) {s t : Seq} (ht : s.length + 2 ≤ t.length) :
    ∃ t', xAct e s t = some t' ∧ t.length ≤ t'.length + 1 := by
  by_cases hst : s <+: t
  · obtain ⟨r, rfl⟩ := hst
    have hr : 2 ≤ r.length := by simp at ht; omega
    rcases he with rfl | rfl
    · obtain ⟨r', h1, h2⟩ := xr_defined hr
      exact ⟨s ++ r', by simp [xAct, xFin_append, h1], by simp; omega⟩
    · obtain ⟨r', h1, h2⟩ := xrInv_defined hr
      exact ⟨s ++ r', by simp [xAct, xFinInv_append, h1], by simp; omega⟩
  · rcases he with rfl | rfl
    · exact ⟨t, by simp [xAct, xFin_of_not_prefix hst (by omega)], by omega⟩
    · exact ⟨t, by simp [xAct, xFinInv_of_not_prefix hst (by omega)], by omega⟩

theorem xAct_prefix {e : ℤ} (he : e = 1 ∨ e = -1) {s a b a' b' : Seq} (ha : s.length + 2 ≤ a.length)
    (hb : s.length + 2 ≤ b.length) (ha' : xAct e s a = some a') (hb' : xAct e s b = some b')
    (h : a' <+: b') : a <+: b := by
  have key : ∀ {f : List Bool → Option (List Bool)},
      (∀ {r q r' q' : List Bool}, f r = some r' → f q = some q' → r' <+: q' → r <+: q) →
      (∀ r, xAct e s (s ++ r) = (f r).map (s ++ ·)) →
      (∀ t, ¬ s <+: t → s.length < t.length → xAct e s t = some t) → a <+: b := by
    intro f hf happ hnp
    by_cases hsa : s <+: a <;> by_cases hsb : s <+: b
    · obtain ⟨r, rfl⟩ := hsa
      obtain ⟨q, rfl⟩ := hsb
      rw [happ] at ha' hb'
      obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 ha'
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.1 hb'
      rw [List.prefix_append_right_inj] at h ⊢
      exact hf hr' hq' h
    · obtain ⟨r, rfl⟩ := hsa
      rw [happ] at ha'
      obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.1 ha'
      rw [hnp b hsb (by omega)] at hb'
      cases hb'
      exact absurd ((List.prefix_append s r').trans h) hsb
    · obtain ⟨q, rfl⟩ := hsb
      rw [happ] at hb'
      obtain ⟨q', -, rfl⟩ := Option.map_eq_some_iff.1 hb'
      rw [hnp a hsa (by omega)] at ha'
      cases ha'
      rcases List.prefix_or_prefix_of_prefix h (List.prefix_append s q') with h1 | h1
      · have := h1.length_le; omega
      · exact absurd h1 hsa
    · rw [hnp a hsa (by omega)] at ha'
      rw [hnp b hsb (by omega)] at hb'
      cases ha'; cases hb'
      exact h
  rcases he with rfl | rfl
  · exact key xr_prefix (fun r => by simp [xAct, xFin_append])
      (fun t h hl => by simp [xAct, xFin_of_not_prefix h hl])
  · exact key xrInv_prefix (fun r => by simp [xAct, xFinInv_append])
      (fun t h hl => by simp [xAct, xFinInv_of_not_prefix h hl])

theorem step_moveX_e {e : ℤ} (he : e = 1 ∨ e = -1) (pre post : Word) (s t t' : Seq) (i : ℤ)
    (h : xAct e s t = some t') :
    Step (pre ++ [(.y t, i), (.x s, e)] ++ post) (pre ++ [(.x s, e), (.y t', i)] ++ post) := by
  rcases he with rfl | rfl
  · exact Step.moveX pre post s t t' i (by simpa [xAct] using h)
  · exact Step.moveXInv pre post s t t' i (by simpa [xAct] using h)

/-- How a `Y`-letter is changed by moving `x_s^e` left past it. -/
def Moved (e : ℤ) (s : Seq) (p q : Gen × ℤ) : Prop :=
  ∃ t t', p.1 = .y t ∧ q.1 = .y t' ∧ q.2 = p.2 ∧ xAct e s t = some t' ∧ t.length ≤ t'.length + 1 ∧
    s.length + 2 ≤ t.length

theorem derives_moveX_map {s : Seq} {e : ℤ} (he : e = 1 ∨ e = -1) :
    ∀ Υ : Word, (∀ p ∈ Υ, ∃ t, p.1 = .y t ∧ s.length + 2 ≤ t.length) →
      ∃ Υ', Derives (Υ ++ [(.x s, e)]) ((.x s, e) :: Υ') ∧ List.Forall₂ (Moved e s) Υ Υ'
  | [], _ => ⟨[], Relation.ReflTransGen.refl, List.Forall₂.nil⟩
  | (g, i) :: Υ, h => by
    obtain ⟨t, hg, hlt⟩ := h (g, i) (by simp)
    simp only at hg
    subst hg
    obtain ⟨Υ', d, hf⟩ := derives_moveX_map he Υ (fun q hq => h q (by simp [hq]))
    obtain ⟨t', ht', hlen⟩ := xAct_defined he hlt
    refine ⟨(.y t', i) :: Υ', ?_, List.Forall₂.cons ⟨t, t', rfl, rfl, rfl, ht', hlen, hlt⟩ hf⟩
    have h1 := d.context [(.y t, i)] []
    have h2 := Relation.ReflTransGen.single (step_moveX_e he [] Υ' s t t' i ht')
    simp only [List.append_nil, List.nil_append] at h1 h2
    have := h1.trans (by simpa [Derives] using h2)
    simpa [Derives] using this

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

theorem oc_moved {e : ℤ} (he : e = 1 ∨ e = -1) {s : Seq} {Υ Υ' : Word}
    (hf : List.Forall₂ (Moved e s) Υ Υ') (h : OC Υ) : OC Υ' := by
  intro i j hi hj a' b' m n hiv hjv hab
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 hf
  obtain ⟨a, a'', ha, ha', hm, hxa, -, hla⟩ := hget i (by omega) hi
  obtain ⟨b, b'', hb, hb', hn, hxb, -, hlb⟩ := hget j (by omega) hj
  simp only [List.get_eq_getElem] at ha ha' hm hb hb' hn
  rw [hiv] at ha' hm; rw [hjv] at hb' hn
  simp only [Gen.y.injEq] at ha' hb'
  subst ha'; subst hb'
  apply h i j (by omega) (by omega) a b m n
  · ext <;> simp_all
  · ext <;> simp_all
  · exact xAct_prefix he hla hlb hxa hxb hab

theorem forall₂_mem_right {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem depth_le_of_mem {W : Word} {t : Seq} {n : ℤ} (h : (Gen.y t, n) ∈ W) :
    depth W ≤ (t.length : ℕ∞) := by
  unfold depth
  exact iInf₂_le t ⟨n, h⟩

theorem single_move {W : Word} (hW : IsStandardForm W) {s : Seq} {e : ℤ} (he : e = 1 ∨ e = -1)
    (hd : ((s.length + 2 : ℕ) : ℕ∞) ≤ depth W) :
    ∃ W', Derives (W ++ [(.x s, e)]) W' ∧ IsStandardForm W' ∧ depth W - 1 ≤ depth W' := by
  obtain ⟨hw, ⟨Ξw, Υ, rfl, hΞ, hΥ⟩, hord⟩ := hW
  have hΞy : ∀ p ∈ Ξw, ∀ t, p.1 ≠ .y t := by
    intro p hp t h
    obtain ⟨u, hu⟩ := hΞ.2 p hp
    rw [hu] at h; cases h
  have hlong : ∀ p ∈ Υ, ∃ t, p.1 = .y t ∧ s.length + 2 ≤ t.length := by
    intro p hp
    obtain ⟨t, ht⟩ := hΥ.2 p hp
    refine ⟨t, ht, ?_⟩
    have hm : (Gen.y t, p.2) ∈ Ξw ++ Υ := by
      rw [← ht]; exact List.mem_append_right _ hp
    have := hd.trans (depth_le_of_mem hm)
    exact_mod_cast this
  obtain ⟨Υ', d, hf⟩ := derives_moveX_map he Υ hlong
  have hΥ'y : ∀ q ∈ Υ', ∃ t' : Seq, q.1 = .y t' ∧ ∃ p ∈ Υ, q.2 = p.2 ∧ ∃ t,
      (Gen.y t, p.2) ∈ Υ ∧ t.length ≤ t'.length + 1 := by
    intro q hq
    obtain ⟨p, hp, t, t', hpt, hqt, hqp, -, hl, -⟩ := forall₂_mem_right hf hq
    refine ⟨t', hqt, p, hp, hqp, t, by rw [← hpt]; exact hp, hl⟩
  have heq : Ξw ++ (Gen.x s, e) :: Υ' = (Ξw ++ [(Gen.x s, e)]) ++ Υ' := by simp
  have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> decide
  refine ⟨Ξw ++ (.x s, e) :: Υ', ?_, ⟨?_, ⟨Ξw ++ [(.x s, e)], Υ', heq, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
  · have := d.context Ξw []
    simpa [Derives] using this
  · intro q hq
    simp only [List.mem_append, List.mem_cons] at hq
    rcases hq with hq | rfl | hq
    · exact hw q (List.mem_append_left _ hq)
    · exact he0
    · obtain ⟨-, -, p, hp, hqp, -⟩ := hΥ'y q hq
      rw [hqp]; exact hw p (List.mem_append_right _ hp)
  · intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hw q (List.mem_append_left _ hq)
    · exact he0
  · intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hΞ.2 q hq
    · exact ⟨s, rfl⟩
  · intro q hq
    obtain ⟨-, -, p, hp, hqp, -⟩ := hΥ'y q hq
    rw [hqp]; exact hw p (List.mem_append_right _ hp)
  · intro q hq
    obtain ⟨t', ht', -⟩ := hΥ'y q hq
    exact ⟨t', ht'⟩
  · show OC _
    rw [heq, oc_append]
    · exact oc_moved he hf ((oc_append hΞy).1 hord)
    · intro q hq t h
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact hΞy q hq t h
      · cases h
  · unfold depth
    apply le_iInf₂
    rintro t' ⟨n, hn⟩
    have hn' : (Gen.y t', n) ∈ Υ' := by
      simp only [List.mem_append, List.mem_cons] at hn
      rcases hn with hn | hn | hn
      · exact absurd rfl (hΞy _ hn t')
      · cases hn
      · exact hn
    obtain ⟨t'', ht'', p, hp, -, t, htm, hl⟩ := hΥ'y _ hn'
    simp only [Gen.y.injEq] at ht''
    subst ht''
    have h1 : depth (Ξw ++ Υ) ≤ (t.length : ℕ∞) := depth_le_of_mem (List.mem_append_right _ htm)
    rw [tsub_le_iff_right]
    calc depth (Ξw ++ Υ) ≤ (t.length : ℕ∞) := h1
      _ ≤ (t'.length : ℕ∞) + 1 := by exact_mod_cast hl

theorem enat_le_sub_one {D : ℕ∞} {a : ℕ} (h : ((a + 1 : ℕ) : ℕ∞) ≤ D) : (a : ℕ∞) ≤ D - 1 := by
  induction D using ENat.recTopCoe with
  | top => simp
  | coe d =>
    have h' : a + 1 ≤ d := by exact_mod_cast h
    have : ((d : ℕ∞) - 1) = ((d - 1 : ℕ) : ℕ∞) := by simp
    rw [this]
    exact_mod_cast (by omega : a ≤ d - 1)

theorem multi_move {s : Seq} : ∀ (k : ℕ) (W : Word) (n : ℤ), IsStandardForm W → n ≠ 0 →
    n.natAbs = k → ((s.length + 1 + k : ℕ) : ℕ∞) ≤ depth W →
    ∃ W', Derives (W ++ [(.x s, n)]) W' ∧ IsStandardForm W' ∧ depth W - k ≤ depth W'
  | 0, _, n, _, hn, hk, _ => absurd (Int.natAbs_eq_zero.1 hk) hn
  | 1, W, n, hW, _, hk, hd => by
    have he : n = 1 ∨ n = -1 := by omega
    obtain ⟨W', d, hW', hdep⟩ := single_move hW he
      (by rw [show s.length + 2 = s.length + 1 + 1 by omega]; exact hd)
    exact ⟨W', d, hW', by simpa using hdep⟩
  | k + 2, W, n, hW, hn, hk, hd => by
    set e : ℤ := if 0 < n then 1 else -1 with he_def
    have he : e = 1 ∨ e = -1 := by by_cases h : 0 < n <;> simp [he_def, h]
    have he0 : e ≠ 0 := by rcases he with h | h <;> rw [h] <;> decide
    have hne : n - e ≠ 0 := by by_cases h : 0 < n <;> simp [he_def, h] <;> omega
    have hsign : 0 < e * (n - e) := by
      by_cases h : 0 < n <;> simp [he_def, h] <;> omega
    have hk' : (n - e).natAbs = k + 1 := by by_cases h : 0 < n <;> simp [he_def, h] <;> omega
    have hsplit := Relation.ReflTransGen.single (Step.split W [] (.x s) e (n - e) he0 hne hsign)
    rw [show e + (n - e) = n by ring] at hsplit
    simp only [List.append_nil] at hsplit
    have hd1 : ((s.length + 2 : ℕ) : ℕ∞) ≤ depth W :=
      le_trans (by exact_mod_cast (show s.length + 2 ≤ s.length + 1 + (k + 2) by omega)) hd
    obtain ⟨W₁, d₁, hW₁, hdep₁⟩ := single_move hW he hd1
    have hd₁ : ((s.length + 1 + (k + 1) : ℕ) : ℕ∞) ≤ depth W₁ :=
      (enat_le_sub_one (by rw [show s.length + 1 + (k + 1) + 1 = s.length + 1 + (k + 2) by omega]; exact hd)).trans hdep₁
    obtain ⟨W', d', hW', hdep'⟩ := multi_move (k + 1) W₁ (n - e) hW₁ hne hk' hd₁
    refine ⟨W', ?_, hW', ?_⟩
    · have d₁' := d₁.context [] [(.x s, n - e)]
      simp only [List.nil_append] at d₁'
      have := (by simpa [Derives] using hsplit : Derives (W ++ [(.x s, n)]) (W ++ [(.x s, e), (.x s, n - e)]))
      refine (this.trans ?_).trans d'
      simpa [Derives] using d₁'
    · calc depth W - ((k + 2 : ℕ) : ℕ∞) = depth W - 1 - ((k + 1 : ℕ) : ℕ∞) := by
            rw [tsub_tsub]; congr 1; push_cast; ring
        _ ≤ depth W₁ - ((k + 1 : ℕ) : ℕ∞) := tsub_le_tsub_right hdep₁ _
        _ ≤ depth W' := hdep'

/-- The `l₀` of Lemma 5.3: enough depth for every letter of `Ξ` in turn. -/
def cost (Ξ : Word) : ℕ :=
  (Ξ.map fun p => (match p.1 with | .x s => s.length | .y s => s.length) + 1 + p.2.natAbs).sum

theorem exists_derives_append_xWord_aux : ∀ (Ξ : Word), IsXWord Ξ → ∀ W, IsStandardForm W →
    ((cost Ξ : ℕ) : ℕ∞) ≤ depth W →
    ∃ W', Derives (W ++ Ξ) W' ∧ IsStandardForm W' ∧ depth W - Word.wordLength Ξ ≤ depth W'
  | [], _, W, hW, _ => ⟨W, by simpa [Derives] using Relation.ReflTransGen.refl, hW, by simp [Word.wordLength]⟩
  | (g, n) :: Ξ, hΞ, W, hW, hd => by
    obtain ⟨s, hs⟩ := hΞ.2 (g, n) (by simp)
    simp only at hs
    subst hs
    have hn : n ≠ 0 := hΞ.1 (.x s, n) (by simp)
    have hΞ' : IsXWord Ξ := ⟨fun p hp => hΞ.1 p (by simp [hp]), fun p hp => hΞ.2 p (by simp [hp])⟩
    have hcost : cost ((.x s, n) :: Ξ) = s.length + 1 + n.natAbs + cost Ξ := by
      simp [cost]
    rw [hcost] at hd
    obtain ⟨W₁, d₁, hW₁, hdep₁⟩ := multi_move (s := s) n.natAbs W n hW hn rfl
      (le_trans (by exact_mod_cast (by omega)) hd)
    have hd₁ : ((cost Ξ : ℕ) : ℕ∞) ≤ depth W₁ := by
      refine le_trans ?_ hdep₁
      induction h : depth W using ENat.recTopCoe with
      | top => simp
      | coe d =>
        rw [h] at hd
        have h' : s.length + 1 + n.natAbs + cost Ξ ≤ d := by exact_mod_cast hd
        have : ((d : ℕ∞) - (n.natAbs : ℕ∞)) = ((d - n.natAbs : ℕ) : ℕ∞) := by simp
        rw [this]
        exact_mod_cast (by omega : cost Ξ ≤ d - n.natAbs)
    obtain ⟨W', d', hW', hdep'⟩ := exists_derives_append_xWord_aux Ξ hΞ' W₁ hW₁ hd₁
    refine ⟨W', ?_, hW', ?_⟩
    · have := d₁.context [] Ξ
      simp only [List.nil_append] at this
      exact (by simpa [Derives] using this : Derives (W ++ (Gen.x s, n) :: Ξ) (W₁ ++ Ξ)).trans d'
    · have hwl : Word.wordLength ((Gen.x s, n) :: Ξ) = n.natAbs + Word.wordLength Ξ := by
        simp [Word.wordLength]
      rw [hwl]
      calc depth W - ((n.natAbs + Word.wordLength Ξ : ℕ) : ℕ∞)
          = depth W - (n.natAbs : ℕ∞) - (Word.wordLength Ξ : ℕ∞) := by rw [tsub_tsub]; push_cast; rfl
        _ ≤ depth W₁ - (Word.wordLength Ξ : ℕ∞) := tsub_le_tsub_right hdep₁ _
        _ ≤ depth W' := hdep'

end LodhaMoore
end

section
open LodhaMoore
theorem solution (Ξ : Word) (hΞ : IsXWord Ξ) :
    ∃ l₀ : ℕ, ∀ W, IsStandardForm W → (l₀ : ℕ∞) ≤ depth W →
      ∃ W', Derives (W ++ Ξ) W' ∧ IsStandardForm W' ∧ depth W - Ξ.wordLength ≤ depth W' :=
  ⟨cost Ξ, exists_derives_append_xWord_aux Ξ hΞ⟩
end
