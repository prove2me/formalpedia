-- Prove2me | solution 1 for OAI.GeneralizedStarHeight.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T17:53:46.245976+00:00
-- url     : https://prove2.me/submissions/b3ca4d4c-5334-4634-b7e5-7371a5ce3f20

import Mathlib
import Definitions.Def_GeneralizedStarHeight

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
alias Finset.prod_le_one₀ := Finset.prod_le_one
alias Finset.one_le_prod₀ := Finset.one_le_prod
alias List.Nodup.getElem?_inj := List.getElem?_inj
end OAICompat434

universe u uι uι2 uS uM uK uS2 uΩ uC uι3 uι4 uA uI uS3 uS4 uS5 uI2 uA2 uA3 uS6 uT uP uC2 uC3 uC4 uC5 uP2 uP3 uP4 uC6 uC7 uC8 uC9 uB uC10 uT2 uA4 uB2 uC11 uA5 uB3 uC12 uT3 uA6 uB4 uC13 uT4 uA7 uB5 uC14 uT5 uA8 uB6 uC15 uT6 uA9 uB7 uC16 uT7 uA10 uB8 uC17 uA11 uB9 uA12 uB10 uC18 uA13 uB11 uP5 uC19 uT8 uP6 uC20 uT9 uP7 uT10 uP8 uT11 uP9 uC21 uAlphabet uAlphabet2 uQ uQ2 uJ uKind uM2 uAlphabet3 uAlphabet4 uM3 uM4 uM5 uM6 uK2 uM7 uK3 uJ2 uJ3 uPBad uG uG2 uP10 uU uV uV2 uAlphabet5 uV3 uAlphabet6 uAlphabet7 uJ4 uJ5 uAlphabet8 uAlphabet9 uJ6 uV4 uV5 uK4

section
section
namespace OAI

namespace GeneralizedStarHeight

namespace Expression

open scoped Computability

end Expression

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace HasHeightAtMost

open scoped Computability

variable {Alphabet : Type u} {L M : Language Alphabet} {n k : ℕ}

lemma mono (h : HasHeightAtMost L n) (hn : n ≤ k) : HasHeightAtMost L k := by
  obtain ⟨P, rfl, hP⟩ := h
  exact ⟨P, rfl, hP.trans hn⟩

lemma zero (n : ℕ) : HasHeightAtMost (0 : Language Alphabet) n :=
  ⟨Expression.zero, rfl, Nat.zero_le _⟩

lemma one (n : ℕ) : HasHeightAtMost (1 : Language Alphabet) n :=
  ⟨Expression.one, rfl, Nat.zero_le _⟩

lemma letter (a : Alphabet) (n : ℕ) : HasHeightAtMost ({[a]} : Language Alphabet) n :=
  ⟨Expression.letter a, rfl, Nat.zero_le _⟩

lemma union (hL : HasHeightAtMost L n) (hM : HasHeightAtMost M n) :
    HasHeightAtMost (L + M) n := by
  obtain ⟨P, rfl, hP⟩ := hL
  obtain ⟨Q, rfl, hQ⟩ := hM
  exact ⟨P.union Q, rfl, max_le hP hQ⟩

lemma concat (hL : HasHeightAtMost L n) (hM : HasHeightAtMost M n) :
    HasHeightAtMost (L * M) n := by
  obtain ⟨P, rfl, hP⟩ := hL
  obtain ⟨Q, rfl, hQ⟩ := hM
  exact ⟨P.concat Q, rfl, max_le hP hQ⟩

lemma compl (hL : HasHeightAtMost L n) : HasHeightAtMost Lᶜ n := by
  obtain ⟨P, rfl, hP⟩ := hL
  exact ⟨P.compl, rfl, hP⟩

lemma inter (hL : HasHeightAtMost L n) (hM : HasHeightAtMost M n) :
    HasHeightAtMost (L ⊓ M) n := by
  have h := (hL.compl.union hM.compl).compl
  have heq : ((Lᶜ + Mᶜ)ᶜ : Language Alphabet) = L ⊓ M := by
    ext x
    change (¬(x ∉ L ∨ x ∉ M)) ↔ x ∈ L ∧ x ∈ M
    tauto
  exact heq ▸ h

lemma star (hL : HasHeightAtMost L n) : HasHeightAtMost L∗ (1 + n) := by
  obtain ⟨P, rfl, hP⟩ := hL
  exact ⟨P.star, rfl, Nat.add_le_add_left hP 1⟩

lemma finset_iSup {ι : Type uι} (s : Finset ι) (L : ι → Language Alphabet)
    (h : ∀ i ∈ s, HasHeightAtMost (L i) n) :
    HasHeightAtMost (⨆ i ∈ s, L i) n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.notMem_empty, iSup_false, iSup_bot]
      exact zero n
  | @insert i s hi ih =>
      rw [Finset.iSup_insert]
      exact (h i (Finset.mem_insert_self _ _)).union
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma iSup {ι : Type uι2} [Finite ι] (L : ι → Language Alphabet)
    (h : ∀ i, HasHeightAtMost (L i) n) : HasHeightAtMost (⨆ i, L i) n := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  simpa using finset_iSup Finset.univ L (fun i _ => h i)

lemma singleton (w : List Alphabet) (n : ℕ) :
    HasHeightAtMost ({w} : Language Alphabet) n := by
  induction w with
  | nil => exact one n
  | cons a w ih =>
      have h := (letter a n).concat ih
      convert h using 1
      apply Language.ext
      intro x
      change (x = a :: w) ↔ _
      rw [Language.mem_mul]
      change (x = a :: w) ↔ ∃ s, s = [a] ∧ ∃ t, t = w ∧ s ++ t = x
      simp [eq_comm]

lemma finite (L : Language Alphabet) (hL : (L : Set (List Alphabet)).Finite) (n : ℕ) :
    HasHeightAtMost L n := by
  have heq : L = ⨆ w : {w : List Alphabet // w ∈ L}, ({w.1} : Language Alphabet) := by
    ext x
    rw [Language.mem_iSup]
    change (x ∈ L) ↔ ∃ w : {w : List Alphabet // w ∈ L}, x = w.1
    simp
  let : Finite {w : List Alphabet // w ∈ L} := hL.to_subtype
  rw [heq]
  exact iSup _ (fun w => singleton w.1 n)

end HasHeightAtMost

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace EpisodeAlgebra

open scoped Computability

variable {Alphabet : Type u} {S : Type uS}

def PrefixCode (E : Language Alphabet) : Prop :=
  [] ∉ E ∧ ∀ e ∈ E, ∀ f ∈ E, e <+: f → e = f

def AllIn (D : Language Alphabet) (es : List (List Alphabet)) : Prop :=
  ∀ e ∈ es, e ∈ D

def updateWord (G : List Alphabet → S → S) (x : S) (es : List (List Alphabet)) : S :=
  es.foldl (fun z e => G e z) x

def graph (D : Language Alphabet) (G : List Alphabet → S → S) (x y : S) : Language Alphabet :=
  {w | ∃ es, AllIn D es ∧ es.flatten = w ∧ updateWord G x es = y}

lemma AllIn.mono {D E : Language Alphabet} {es : List (List Alphabet)}
    (h : AllIn D es) (hDE : D ≤ E) : AllIn E es := fun e he => hDE (h e he)

lemma AllIn.append {D : Language Alphabet} {es fs : List (List Alphabet)}
    (he : AllIn D es) (hf : AllIn D fs) : AllIn D (es ++ fs) := by
  intro e hm
  rcases List.mem_append.mp hm with hm | hm
  · exact he e hm
  · exact hf e hm

lemma AllIn.of_append_right {D : Language Alphabet} {es fs : List (List Alphabet)}
    (h : AllIn D (es ++ fs)) : AllIn D fs := fun e he => h e (List.mem_append_right _ he)

@[simp] lemma updateWord_nil (G : List Alphabet → S → S) (x : S) :
    updateWord G x [] = x := rfl

@[simp] lemma updateWord_cons (G : List Alphabet → S → S) (x : S)
    (e : List Alphabet) (es : List (List Alphabet)) :
    updateWord G x (e :: es) = updateWord G (G e x) es := rfl

lemma updateWord_append (G : List Alphabet → S → S) (x : S)
    (es fs : List (List Alphabet)) :
    updateWord G x (es ++ fs) = updateWord G (updateWord G x es) fs :=
  List.foldl_append

lemma graph_nil (D : Language Alphabet) (G : List Alphabet → S → S) (x : S) :
    [] ∈ graph D G x x := ⟨[], by simp [AllIn], rfl, rfl⟩

lemma graph_singleton {D : Language Alphabet} (G : List Alphabet → S → S)
    (x : S) {e : List Alphabet} (he : e ∈ D) : e ∈ graph D G x (G e x) :=
  ⟨[e], by simpa [AllIn], by simp, rfl⟩

lemma graph_mono {D E : Language Alphabet} (hDE : D ≤ E)
    (G : List Alphabet → S → S) (x y : S) : graph D G x y ≤ graph E G x y := by
  rintro w ⟨es, he, hw, hx⟩
  exact ⟨es, he.mono hDE, hw, hx⟩

lemma graph_concat {D : Language Alphabet} {G : List Alphabet → S → S}
    {x y z : S} {u v : List Alphabet} (hu : u ∈ graph D G x y)
    (hv : v ∈ graph D G y z) : u ++ v ∈ graph D G x z := by
  obtain ⟨es, he, rfl, hx⟩ := hu
  obtain ⟨fs, hf, rfl, hy⟩ := hv
  exact ⟨es ++ fs, he.append hf, List.flatten_append,
    by rw [updateWord_append, hx, hy]⟩

lemma flatten_prefix {E : Language Alphabet} (hE : PrefixCode E)
    {es fs : List (List Alphabet)} (he : AllIn E es) (hf : AllIn E fs)
    (hp : es.flatten <+: fs.flatten) : es <+: fs := by
  induction es generalizing fs with
  | nil => exact List.nil_prefix
  | cons e es ih =>
      have heE : e ∈ E := he e (by simp)
      cases fs with
      | nil =>
          obtain ⟨r, hr⟩ := hp
          have he0 : e = [] := by
            have hh : e ++ (es.flatten ++ r) = [] := by simpa [List.append_assoc] using hr
            exact (List.append_eq_nil_iff.mp hh).1
          exact False.elim (hE.1 (he0 ▸ heE))
      | cons f fs =>
          have hfE : f ∈ E := hf f (by simp)
          have hePre : e <+: (f :: fs).flatten :=
            (List.prefix_append e es.flatten).trans hp
          have hfPre : f <+: (f :: fs).flatten := List.prefix_append _ _
          have hef : e = f := by
            rcases List.prefix_or_prefix_of_prefix hePre hfPre with h | h
            · exact hE.2 e heE f hfE h
            · exact (hE.2 f hfE e heE h).symm
          subst f
          obtain ⟨r, hr⟩ := hp
          have htail : es.flatten ++ r = fs.flatten := by
            apply List.append_cancel_left (as := e)
            simpa only [List.flatten_cons, List.append_assoc] using hr
          have hrec := ih (fun a ha => he a (by simp [ha]))
            (fun a ha => hf a (by simp [ha])) ⟨r, htail⟩
          obtain ⟨gs, hgs⟩ := hrec
          exact ⟨gs, by simp [hgs]⟩

lemma consume_graph_prefix {E D D' : Language Alphabet} (hE : PrefixCode E)
    (hDE : D ≤ E) (hD'D : D' ≤ D) {G : List Alphabet → S → S}
    {x z : S} {u v : List Alphabet} {es : List (List Alphabet)}
    (hu : u ∈ graph D' G x z) (hes : AllIn D es) (hword : u ++ v = es.flatten) :
    ∃ fs, AllIn D fs ∧ fs.flatten = v ∧ updateWord G x es = updateWord G z fs := by
  obtain ⟨pre, hp, hu, hx⟩ := hu
  have hpre := flatten_prefix hE (hp.mono (hD'D.trans hDE)) (hes.mono hDE)
    (show pre.flatten <+: es.flatten from ⟨v, by rw [hu, hword]⟩)
  obtain ⟨fs, rfl⟩ := hpre
  refine ⟨fs, hes.of_append_right, ?_, ?_⟩
  · apply List.append_cancel_left (as := u)
    simpa only [List.flatten_append, hu] using hword.symm
  · rw [updateWord_append, hx]

lemma flatten_injective {E : Language Alphabet} (hE : PrefixCode E)
    {es fs : List (List Alphabet)} (he : AllIn E es) (hf : AllIn E fs)
    (h : es.flatten = fs.flatten) : es = fs := by
  have hp := flatten_prefix hE he hf (h ▸ List.prefix_rfl)
  have hq := flatten_prefix hE hf he (h.symm ▸ List.prefix_rfl)
  exact hp.sublist.antisymm hq.sublist

lemma graph_iff_update {E D : Language Alphabet} (hE : PrefixCode E) (hDE : D ≤ E)
    (G : List Alphabet → S → S) (x y : S) {es : List (List Alphabet)}
    (he : AllIn D es) : es.flatten ∈ graph D G x y ↔ updateWord G x es = y := by
  constructor
  · rintro ⟨fs, hf, hw, hx⟩
    have hfs := flatten_injective hE (hf.mono hDE) (he.mono hDE) hw
    simpa only [hfs] using hx
  · exact fun hx => ⟨es, he, rfl, hx⟩

def SplitSound (D : Language Alphabet) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet) : Prop :=
  ∀ (x y : S) (es : List (List Alphabet)) (u v : List Alphabet),
    AllIn D es → u ∈ P x → v ∈ Q y → u ++ v <+: es.flatten →
      ∃ e fs, es = e :: fs ∧ u ++ v = e ∧ G e x = y

def SplitAvailable (D D' : Language Alphabet) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet) : Prop :=
  ∀ e ∈ D, e ∉ D' → ∀ x, e ∈ P x * Q (G e x)

lemma consume_pair_prefix {D : Language Alphabet} {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} (hs : SplitSound D G P Q)
    {x y : S} {u v r : List Alphabet} {es : List (List Alphabet)}
    (he : AllIn D es) (hu : u ∈ P x) (hv : v ∈ Q y)
    (hw : (u ++ v) ++ r = es.flatten) :
    ∃ fs, AllIn D fs ∧ fs.flatten = r ∧ updateWord G x es = updateWord G y fs := by
  obtain ⟨e, fs, rfl, huv, hxy⟩ := hs x y es u v he hu hv ⟨r, hw⟩
  refine ⟨fs, fun a ha => he a (by simp [ha]), ?_, ?_⟩
  · apply List.append_cancel_left (as := e)
    simpa only [List.flatten_cons, huv] using hw.symm
  · simp only [updateWord_cons, hxy]

def start (W : S → S → Language Alphabet) (P : S → Language Alphabet) (x : S) :=
  ⨆ i, W x i * P i

def middle (W : S → S → Language Alphabet) (P Q : S → Language Alphabet) :=
  ⨆ j, ⨆ i, Q j * W j i * P i

def finish (W : S → S → Language Alphabet) (Q : S → Language Alphabet) (y : S) :=
  ⨆ l, Q l * W l y

def body (W : S → S → Language Alphabet) (P Q : S → Language Alphabet) (x y : S) :=
  W x y + start W P x * (middle W P Q)∗ * finish W Q y

lemma mem_start_iff {W : S → S → Language Alphabet} {P : S → Language Alphabet}
    {x : S} {w : List Alphabet} : w ∈ start W P x ↔
    ∃ i u v, u ∈ W x i ∧ v ∈ P i ∧ u ++ v = w := by
  simp only [start, Language.mem_iSup, Language.mem_mul]
  aesop

lemma mem_middle_iff {W : S → S → Language Alphabet} {P Q : S → Language Alphabet}
    {w : List Alphabet} : w ∈ middle W P Q ↔
    ∃ j i u v p, u ∈ Q j ∧ v ∈ W j i ∧ p ∈ P i ∧ (u ++ v) ++ p = w := by
  simp only [middle, Language.mem_iSup, Language.mem_mul]
  constructor
  · rintro ⟨j, i, a, ⟨u, hu, v, hv, rfl⟩, p, hp, rfl⟩
    exact ⟨j, i, u, v, p, hu, hv, hp, rfl⟩
  · rintro ⟨j, i, u, v, p, hu, hv, hp, rfl⟩
    exact ⟨j, i, u ++ v, ⟨u, hu, v, hv, rfl⟩, p, hp, rfl⟩

lemma mem_finish_iff {W : S → S → Language Alphabet} {Q : S → Language Alphabet}
    {y : S} {w : List Alphabet} : w ∈ finish W Q y ↔
    ∃ j u v, u ∈ Q j ∧ v ∈ W j y ∧ u ++ v = w := by
  simp only [finish, Language.mem_iSup, Language.mem_mul]
  aesop

lemma mem_body_iff {W : S → S → Language Alphabet} {P Q : S → Language Alphabet}
    {x y : S} {w : List Alphabet} : w ∈ body W P Q x y ↔
    w ∈ W x y ∨ ∃ a ms b, a ∈ start W P x ∧ AllIn (middle W P Q) ms ∧
      b ∈ finish W Q y ∧ (a ++ ms.flatten) ++ b = w := by
  simp only [body, Language.mem_add, Language.mem_mul, Language.mem_kstar]
  constructor
  · rintro (h | ⟨c, ⟨a, ha, m, ⟨ms, rfl, hm⟩, rfl⟩, b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ms, b, ha, hm, hb, rfl⟩
  · rintro (h | ⟨a, ms, b, ha, hm, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a ++ ms.flatten, ⟨a, ha, ms.flatten, ⟨ms, rfl, hm⟩, rfl⟩,
        b, hb, rfl⟩

lemma suffix_sound {E D D' : Language Alphabet} (hE : PrefixCode E)
    (hDE : D ≤ E) (hD'D : D' ≤ D) {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} (hs : SplitSound D G P Q)
    (ms : List (List Alphabet)) (hm : AllIn (middle (graph D' G) P Q) ms)
    {x y : S} {p b : List Alphabet} {es : List (List Alphabet)}
    (hp : p ∈ P x) (hb : b ∈ finish (graph D' G) Q y) (he : AllIn D es)
    (hw : (p ++ ms.flatten) ++ b = es.flatten) : updateWord G x es = y := by
  induction ms generalizing x p es with
  | nil =>
      obtain ⟨j, q, w, hq, hwg, rfl⟩ := mem_finish_iff.mp hb
      have hw' : (p ++ q) ++ w = es.flatten := by simpa [List.append_assoc] using hw
      obtain ⟨fs, hf, hfw, hxy⟩ := consume_pair_prefix hs he hp hq hw'
      rw [hxy]
      apply (graph_iff_update hE hDE G j y hf).mp
      rw [hfw]
      exact graph_mono hD'D G j y hwg
  | cons m ms ih =>
      obtain ⟨j, i, q, w, p', hq, hwg, hp', rfl⟩ :=
        mem_middle_iff.mp (hm m (by simp))
      have hw' : (p ++ q) ++ (w ++ ((p' ++ ms.flatten) ++ b)) = es.flatten := by
        simpa only [List.flatten_cons, List.append_assoc] using hw
      obtain ⟨fs, hf, hfw, hxy⟩ := consume_pair_prefix hs he hp hq hw'
      obtain ⟨gs, hg, hgw, hj⟩ := consume_graph_prefix hE hDE hD'D hwg hf hfw.symm
      rw [hxy, hj]
      exact ih (fun a ha => hm a (by simp [ha])) hp' hg hgw.symm

lemma body_sound {E D D' : Language Alphabet} (hE : PrefixCode E)
    (hDE : D ≤ E) (hD'D : D' ≤ D) {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} (hs : SplitSound D G P Q)
    {x y : S} {es : List (List Alphabet)} (he : AllIn D es)
    (hb : es.flatten ∈ body (graph D' G) P Q x y) : updateWord G x es = y := by
  rcases mem_body_iff.mp hb with hw | ⟨a, ms, b, ha, hm, hb, hword⟩
  · exact (graph_iff_update hE hDE G x y he).mp (graph_mono hD'D G x y hw)
  · obtain ⟨i, w, p, hw, hp, rfl⟩ := mem_start_iff.mp ha
    have hword' : w ++ ((p ++ ms.flatten) ++ b) = es.flatten := by
      simpa only [List.append_assoc] using hword
    obtain ⟨fs, hf, hfw, hxy⟩ := consume_graph_prefix hE hDE hD'D hw he hword'
    rw [hxy]
    exact suffix_sound hE hDE hD'D hs ms hm hp hb hf hfw.symm

lemma body_prepend_skip {D' : Language Alphabet} {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} {x z y : S} {u v : List Alphabet}
    (hu : u ∈ graph D' G x z) (hv : v ∈ body (graph D' G) P Q z y) :
    u ++ v ∈ body (graph D' G) P Q x y := by
  apply mem_body_iff.mpr
  rcases mem_body_iff.mp hv with hv | ⟨a, ms, b, ha, hm, hb, rfl⟩
  · exact Or.inl (graph_concat hu hv)
  · obtain ⟨i, w, p, hw, hp, rfl⟩ := mem_start_iff.mp ha
    apply Or.inr
    refine ⟨(u ++ w) ++ p, ms, b, ?_, hm, hb, ?_⟩
    · exact mem_start_iff.mpr ⟨i, u ++ w, p, graph_concat hu hw, hp, rfl⟩
    · simp only [List.append_assoc]

lemma body_prepend_pair {D' : Language Alphabet} {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} {x z y : S} {p q v : List Alphabet}
    (hp : p ∈ P x) (hq : q ∈ Q z) (hv : v ∈ body (graph D' G) P Q z y) :
    (p ++ q) ++ v ∈ body (graph D' G) P Q x y := by
  have hstart : p ∈ start (graph D' G) P x :=
    mem_start_iff.mpr ⟨x, [], p, graph_nil D' G x, hp, by simp⟩
  apply mem_body_iff.mpr
  rcases mem_body_iff.mp hv with hv | ⟨a, ms, b, ha, hm, hb, rfl⟩
  · refine Or.inr ⟨p, [], q ++ v, hstart, by simp [AllIn], ?_, ?_⟩
    · exact mem_finish_iff.mpr ⟨z, q, v, hq, hv, rfl⟩
    · simp [List.append_assoc]
  · obtain ⟨i, w, r, hw, hr, rfl⟩ := mem_start_iff.mp ha
    have hmid : (q ++ w) ++ r ∈ middle (graph D' G) P Q :=
      mem_middle_iff.mpr ⟨z, i, q, w, r, hq, hw, hr, rfl⟩
    refine Or.inr ⟨p, ((q ++ w) ++ r) :: ms, b, hstart, ?_, hb, ?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hmid
      · exact hm a ha
    · simp only [List.flatten_cons, List.append_assoc]

lemma body_available {D D' : Language Alphabet} {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} (ha : SplitAvailable D D' G P Q)
    (es : List (List Alphabet)) (he : AllIn D es) (x : S) :
    es.flatten ∈ body (graph D' G) P Q x (updateWord G x es) := by
  classical
  induction es generalizing x with
  | nil => exact mem_body_iff.mpr (Or.inl (graph_nil D' G x))
  | cons e es ih =>
      have heD := he e (by simp)
      have hes : AllIn D es := fun a ha => he a (by simp [ha])
      have hind := ih hes (G e x)
      by_cases he' : e ∈ D'
      · exact body_prepend_skip (graph_singleton G x he') hind
      · obtain ⟨p, hp, q, hq, heq⟩ := Language.mem_mul.mp (ha e heD he' x)
        simpa only [heq, List.flatten_cons, updateWord_cons] using body_prepend_pair hp hq hind

theorem split_identity {E D D' : Language Alphabet} (hE : PrefixCode E)
    (hDE : D ≤ E) (hD'D : D' ≤ D) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet) (hs : SplitSound D G P Q)
    (ha : SplitAvailable D D' G P Q) (x y : S) :
    graph D G x y = D∗ ⊓ body (graph D' G) P Q x y := by
  ext w
  constructor
  · rintro ⟨es, he, rfl, rfl⟩
    exact ⟨Language.join_mem_kstar he, body_available ha es he x⟩
  · rintro ⟨⟨es, rfl, he⟩, hb⟩
    exact ⟨es, he, rfl, body_sound hE hDE hD'D hs he hb⟩

theorem split_height [Finite S] {E D D' : Language Alphabet} (hE : PrefixCode E)
    (hDE : D ≤ E) (hD'D : D' ≤ D) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet) (hs : SplitSound D G P Q)
    (ha : SplitAvailable D D' G P Q) (H : ℕ)
    (hD : HasHeightAtMost D 1) (hP : ∀ x, HasHeightAtMost (P x) 1)
    (hQ : ∀ y, HasHeightAtMost (Q y) 1)
    (hW : ∀ x y, HasHeightAtMost (graph D' G x y) H) (x y : S) :
    HasHeightAtMost (graph D G x y) (max 2 (1 + H)) := by
  rw [split_identity hE hDE hD'D G P Q hs ha]
  have hH : H ≤ max 2 (1 + H) := by omega
  have h1 : 1 ≤ max 1 H := le_max_left _ _
  have hh : H ≤ max 1 H := le_max_right _ _
  have hm : max 1 H ≤ max 2 (1 + H) := by omega
  have hstar : 1 + max 1 H ≤ max 2 (1 + H) := by omega
  apply (hD.star.mono (le_max_left _ _)).inter
  apply (hW x y |>.mono hH).union
  apply HasHeightAtMost.concat
  · apply HasHeightAtMost.concat
    · exact (HasHeightAtMost.iSup _ (fun i => (hW x i |>.mono hh).concat
        (hP i |>.mono h1))).mono hm
    · exact (HasHeightAtMost.iSup _ (fun j => HasHeightAtMost.iSup _ (fun i =>
        ((hQ j |>.mono h1).concat (hW j i |>.mono hh)).concat (hP i |>.mono h1)))).star.mono hstar
  · exact (HasHeightAtMost.iSup _ (fun l => (hQ l |>.mono h1).concat
      (hW l y |>.mono hh))).mono hm

lemma graph_empty [DecidableEq S] (G : List Alphabet → S → S) (x y : S) :
    graph (0 : Language Alphabet) G x y = if x = y then 1 else 0 := by
  classical
  ext w
  by_cases h : x = y
  · subst y
    simp only [ite_true, Language.mem_one]
    constructor
    · rintro ⟨es, he, rfl, _⟩
      have hes : es = [] := by
        cases es with
        | nil => rfl
        | cons e es => exact False.elim (he e (by simp))
      simp [hes]
    · rintro rfl
      exact graph_nil 0 G x
  · simp only [h, ite_false, Language.notMem_zero, iff_false]
    rintro ⟨es, he, _, hu⟩
    have hes : es = [] := by
      cases es with
      | nil => rfl
      | cons e es => exact False.elim (he e (by simp))
    exact h (by simpa [hes] using hu)

lemma empty_skip_height (G : List Alphabet → S → S) (x y : S) :
    HasHeightAtMost (graph (0 : Language Alphabet) G x y) 0 := by
  classical
  rw [graph_empty]
  split
  · exact HasHeightAtMost.one 0
  · exact HasHeightAtMost.zero 0

end EpisodeAlgebra

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace AffineRecovery

open scoped Computability
open EpisodeAlgebra

variable {Alphabet : Type u} {S : Type uS} [AddCommGroup S]

def affine (L : List Alphabet → S →+ S) (b : List Alphabet → S)
    (e : List Alphabet) (x : S) : S := L e x + b e

lemma update_add (L : List Alphabet → S →+ S) (b : List Alphabet → S)
    (es : List (List Alphabet)) (x z : S) :
    updateWord (affine L b) (x + z) es =
      updateWord (fun e => L e) x es + updateWord (affine L b) z es := by
  induction es generalizing x z with
  | nil => rfl
  | cons e es ih =>
      simp only [updateWord_cons]
      have hh : affine L b e (x + z) = L e x + affine L b e z := by
        simp only [affine, map_add, add_assoc]
      rw [hh, ih]

lemma update_eq_linear_add (L : List Alphabet → S →+ S) (b : List Alphabet → S)
    (es : List (List Alphabet)) (x : S) :
    updateWord (affine L b) x es =
      updateWord (fun e => L e) x es + updateWord (affine L b) 0 es := by
  simpa only [add_zero] using update_add L b es x 0

theorem recovery {E D : Language Alphabet} (hE : PrefixCode E) (hDE : D ≤ E)
    (L : List Alphabet → S →+ S) (b : List Alphabet → S) (x y : S) :
    graph D (fun e => L e) x y =
      ⨆ c : S, graph D (affine L b) x (y + c) ⊓ graph D (affine L b) 0 c := by
  ext w
  rw [Language.mem_iSup]
  constructor
  · rintro ⟨es, he, rfl, hxy⟩
    refine ⟨updateWord (affine L b) 0 es, ⟨es, he, rfl, ?_⟩, es, he, rfl, rfl⟩
    rw [update_eq_linear_add, hxy]
  · rintro ⟨c, ⟨es, he, hw, hx⟩, fs, hf, hfw, hzero⟩
    have hef := flatten_injective hE (he.mono hDE) (hf.mono hDE) (hw.trans hfw.symm)
    subst fs
    refine ⟨es, he, hw, ?_⟩
    rw [update_eq_linear_add, hzero] at hx
    exact add_right_cancel hx

theorem recovery_height [Finite S] {E D : Language Alphabet}
    (hE : PrefixCode E) (hDE : D ≤ E)
    (L : List Alphabet → S →+ S) (b : List Alphabet → S) (H : ℕ)
    (hG : ∀ x y, HasHeightAtMost (graph D (affine L b) x y) H) (x y : S) :
    HasHeightAtMost (graph D (fun e => L e) x y) H := by
  rw [recovery hE hDE L b]
  exact HasHeightAtMost.iSup _ (fun c => (hG x (y + c)).inter (hG 0 c))

end AffineRecovery

namespace RightRegular

variable (M : Type uM) [Monoid M] [Finite M]

abbrev V := M → ZMod 2

noncomputable def basis : Module.Basis M (ZMod 2) (V M) := Pi.basisFun (ZMod 2) M

noncomputable def action (d : M) : V M →ₗ[ZMod 2] V M :=
  (basis M).constr (ZMod 2) (fun m => basis M (m * d))

@[simp] lemma action_basis (d m : M) : action M d (basis M m) = basis M (m * d) := by
  simp only [action, Module.Basis.constr_basis]

@[simp] lemma action_one : action M 1 = LinearMap.id := by
  apply (basis M).ext
  intro m
  simp

lemma action_mul (d e : M) : action M (d * e) = (action M e).comp (action M d) := by
  apply (basis M).ext
  intro m
  simp [mul_assoc]

omit [Monoid M] in
lemma basis_injective : Function.Injective (basis M) := (basis M).injective

lemma action_faithful : Function.Injective (action M) := by
  intro d e h
  have hh := LinearMap.congr_fun h (basis M 1)
  simp only [action_basis, one_mul] at hh
  exact basis_injective M hh

lemma value_recovery (d e : M) : action M d (basis M 1) = basis M e ↔ d = e := by
  simp only [action_basis, one_mul, (basis_injective M).eq_iff]

end RightRegular

namespace Homogenization

variable {K : Type uK} {S : Type uS2} [CommSemiring K] [AddCommMonoid S] [Module K S]

def lift (L : S →ₗ[K] S) (b : S) : (S × K) →ₗ[K] (S × K) where
  toFun u := (L u.1 + u.2 • b, u.2)
  map_add' u v := by
    ext <;> simp [add_smul, add_assoc, add_comm, add_left_comm]
  map_smul' a u := by
    ext <;> simp [smul_add, smul_smul]

@[simp] lemma lift_apply_one (L : S →ₗ[K] S) (b : S) (x : S) :
    lift L b (x, 1) = (L x + b, 1) := by simp [lift]

@[simp] lemma lift_apply_zero (L : S →ₗ[K] S) (b : S) (x : S) :
    lift L b (x, 0) = (L x, 0) := by simp [lift]

lemma lift_comp (L A : S →ₗ[K] S) (b c : S) :
    (lift A c).comp (lift L b) = lift (A.comp L) (A b + c) := by
  ext u <;> simp [lift, smul_add]

end Homogenization

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace FiniteAvoidance

variable {Ω : Type uΩ} {ι : Type uι} [Fintype Ω]

noncomputable def mass (w : Ω → ℝ) (A : Set Ω) : ℝ := by
  classical
  exact ∑ x : Ω, if x ∈ A then w x else 0

lemma mass_nonneg {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x) (A : Set Ω) :
    0 ≤ mass w A := by
  classical
  exact Finset.sum_nonneg fun x _ => by
    by_cases hx : x ∈ A <;> simp [hx, hw x]

lemma mass_mono {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x) {A C : Set Ω}
    (hAC : A ⊆ C) : mass w A ≤ mass w C := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ A
  · simp [hx, hAC hx]
  · by_cases hc : x ∈ C <;> simp [hx, hc, hw x]

@[simp] lemma mass_empty (w : Ω → ℝ) : mass w ∅ = 0 := by
  classical
  simp [mass]

lemma mass_diff (w : Ω → ℝ) (A C : Set Ω) :
    mass w (A \ C) = mass w A - mass w (C ∩ A) := by
  classical
  simp only [mass, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ A <;> by_cases hc : x ∈ C <;> simp [hx, hc]

def avoids (B : ι → Set Ω) (J : Finset ι) : Set Ω :=
  {x | ∀ i ∈ J, x ∉ B i}

omit [Fintype Ω] in
@[simp] lemma avoids_empty (B : ι → Set Ω) : avoids B ∅ = Set.univ := by
  ext x
  simp [avoids]

omit [Fintype Ω] in
lemma avoids_antitone (B : ι → Set Ω) {J K : Finset ι} (hJK : J ⊆ K) :
    avoids B K ⊆ avoids B J := by
  intro x hx i hi
  exact hx i (hJK hi)

omit [Fintype Ω] in
lemma avoids_insert [DecidableEq ι] (B : ι → Set Ω) (J : Finset ι) (i : ι) :
    avoids B (insert i J) = avoids B J \ B i := by
  ext x
  simp only [avoids, Set.mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp,
    Set.mem_sdiff]
  exact and_comm

lemma mass_avoids_insert [DecidableEq ι] (w : Ω → ℝ) (B : ι → Set Ω)
    (J : Finset ι) (i : ι) :
    mass w (avoids B (insert i J)) =
      mass w (avoids B J) - mass w (B i ∩ avoids B J) := by
  rw [avoids_insert, mass_diff]

lemma avoid_union_lower [DecidableEq ι] (w : Ω → ℝ) (B : ι → Set Ω)
    (s : ℝ) (hs : s ≤ 1) (J K : Finset ι) (hd : Disjoint J K)
    (hb : ∀ U : Finset ι, U ⊆ K → U.card < K.card →
      ∀ i, i ∉ J ∪ U → mass w (B i ∩ avoids B (J ∪ U)) ≤
        s * mass w (avoids B (J ∪ U))) :
    (1 - s) ^ K.card * mass w (avoids B J) ≤ mass w (avoids B (J ∪ K)) := by
  induction K using Finset.induction_on with
  | empty => simp
  | @insert i K hi ih =>
      have hdK : Disjoint J K := hd.mono_right (Finset.subset_insert _ _)
      have hiJ : i ∉ J := by
        intro hm
        exact Finset.disjoint_left.mp hd hm (Finset.mem_insert_self _ _)
      have hbK : ∀ U : Finset ι, U ⊆ K → U.card < K.card →
          ∀ j, j ∉ J ∪ U → mass w (B j ∩ avoids B (J ∪ U)) ≤
            s * mass w (avoids B (J ∪ U)) := by
        intro U hU hcard j hj
        apply hb U (hU.trans (Finset.subset_insert _ _))
        · simpa [Finset.card_insert_of_notMem hi] using hcard.trans_le (Nat.le_succ _)
        · exact hj
      have hstep := hb K (Finset.subset_insert _ _) (by simp [hi]) i
        (by simp [hiJ, hi])
      have hrec := ih hdK hbK
      rw [Finset.card_insert_of_notMem hi, pow_succ,
        mul_comm ((1 - s) ^ K.card) (1 - s), mul_assoc]
      calc
        (1 - s) * ((1 - s) ^ K.card * mass w (avoids B J))
            ≤ (1 - s) * mass w (avoids B (J ∪ K)) :=
              mul_le_mul_of_nonneg_left hrec (sub_nonneg.mpr hs)
        _ ≤ mass w (avoids B (J ∪ insert i K)) := by
          rw [Finset.union_insert, mass_avoids_insert]
          linarith

theorem local_lemma [DecidableEq ι] (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (htotal : 0 < mass w Set.univ) (B : ι → Set Ω)
    (neighbors : ι → Finset ι) (D : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hdegree : ∀ i, (neighbors i).card ≤ D)
    (hbad : ∀ i, mass w (B i) ≤ s * (1 - s) ^ D * mass w Set.univ)
    (hind : ∀ i (J : Finset ι), i ∉ J → Disjoint J (neighbors i) →
      mass w (B i ∩ avoids B J) * mass w Set.univ =
        mass w (B i) * mass w (avoids B J))
    (J : Finset ι) : 0 < mass w (avoids B J) := by
  have hconditional : ∀ n : ℕ, ∀ K : Finset ι, K.card = n →
      0 < mass w (avoids B K) ∧ ∀ i, i ∉ K →
        mass w (B i ∩ avoids B K) ≤ s * mass w (avoids B K) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hK
      have hpos : 0 < mass w (avoids B K) := by
        by_cases he : K = ∅
        · simpa [he] using htotal
        · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr he
          have hsmall : (K.erase i).card < n := by
            rw [← hK]
            exact Finset.card_erase_lt_of_mem hi
          have hprev := ih (K.erase i).card hsmall (K.erase i) rfl
          have hb := hprev.2 i (Finset.notMem_erase i K)
          have hins : insert i (K.erase i) = K := Finset.insert_erase hi
          rw [← hins, mass_avoids_insert]
          have hp : 0 < (1 - s) * mass w (avoids B (K.erase i)) :=
            mul_pos (sub_pos.mpr hs1) hprev.1
          linarith
      refine ⟨hpos, ?_⟩
      intro i hi
      let N := K ∩ neighbors i
      let F := K \ neighbors i
      have hFN : Disjoint F N := by
        exact Finset.disjoint_sdiff_inter _ _
      have hUF : F ∪ N = K := by
        exact Finset.sdiff_union_inter _ _
      have hFsub : F ⊆ K := Finset.sdiff_subset
      have hFdisj : Disjoint F (neighbors i) := by
        apply Finset.disjoint_left.mpr
        intro x hx hnx
        exact (Finset.mem_sdiff.mp hx).2 hnx
      have hiF : i ∉ F := fun h => hi (hFsub h)
      have hInd := hind i F hiF hFdisj
      have hBF : mass w (B i ∩ avoids B F) ≤
          s * (1 - s) ^ D * mass w (avoids B F) := by
        apply (mul_le_mul_iff_left₀ htotal).mp
        rw [hInd]
        calc
          mass w (B i) * mass w (avoids B F)
              ≤ (s * (1 - s) ^ D * mass w Set.univ) * mass w (avoids B F) :=
                mul_le_mul_of_nonneg_right (hbad i) (mass_nonneg hw _)
          _ = (s * (1 - s) ^ D * mass w (avoids B F)) * mass w Set.univ := by ring
      have hchain : (1 - s) ^ N.card * mass w (avoids B F) ≤
          mass w (avoids B K) := by
        rw [← hUF]
        apply avoid_union_lower w B s hs1.le F N hFN
        intro U hU hcard j hj
        have hdu : Disjoint F U := hFN.mono_right hU
        have hsmall : (F ∪ U).card < n := by
          rw [Finset.card_union_of_disjoint hdu, ← hK, ← hUF,
            Finset.card_union_of_disjoint hFN]
          exact Nat.add_lt_add_left hcard _
        exact (ih (F ∪ U).card hsmall (F ∪ U) rfl).2 j hj
      have hNcard : N.card ≤ D :=
        (Finset.card_le_card (Finset.inter_subset_right)).trans (hdegree i)
      have hpow : (1 - s) ^ D ≤ (1 - s) ^ N.card :=
        pow_le_pow_of_le_one (sub_nonneg.mpr hs1.le)
          (by linarith) hNcard
      calc
        mass w (B i ∩ avoids B K) ≤ mass w (B i ∩ avoids B F) :=
          mass_mono hw (Set.inter_subset_inter_right _ (avoids_antitone B hFsub))
        _ ≤ s * (1 - s) ^ D * mass w (avoids B F) := hBF
        _ ≤ s * ((1 - s) ^ N.card * mass w (avoids B F)) := by
          have hh := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hs0.le) (mass_nonneg hw (avoids B F))
          simpa only [mul_assoc] using hh
        _ ≤ s * mass w (avoids B K) := mul_le_mul_of_nonneg_left hchain hs0.le
  exact (hconditional J.card J rfl).1

lemma mass_one_eq_card (A : Set Ω) :
    mass (fun _ : Ω => (1 : ℝ)) A = Nat.card A := by
  classical
  simp [mass, Nat.card_eq_fintype_card, Fintype.card_subtype]

@[simp] lemma mass_one_univ :
    mass (fun _ : Ω => (1 : ℝ)) Set.univ = Fintype.card Ω := by
  classical
  simp [mass]

noncomputable def probability (E : Set Ω) : ℝ :=
  mass (fun _ => (1 : ℝ)) E / Fintype.card Ω

@[simp] lemma probability_univ [Nonempty Ω] :
    probability (Set.univ : Set Ω) = 1 := by
  simp [probability, ne_of_gt Fintype.card_pos]

lemma probability_compl [Nonempty Ω] (E : Set Ω) :
    probability Eᶜ = 1 - probability E := by
  have hd := mass_diff (fun _ : Ω => (1 : ℝ)) Set.univ E
  simp only [← Set.compl_eq_univ_sdiff, Set.inter_univ, mass_one_univ] at hd
  unfold probability
  rw [hd, sub_div, div_self (by exact_mod_cast ne_of_gt Fintype.card_pos)]

lemma probability_eq_of_equiv (E F : Set Ω) (e : E ≃ F) :
    probability E = probability F := by
  unfold probability
  rw [mass_one_eq_card, mass_one_eq_card, Nat.card_congr e]

lemma probability_inter_of_independent [Nonempty Ω] (E F : Set Ω)
    (hind : mass (fun _ : Ω => (1 : ℝ)) (E ∩ F) *
        mass (fun _ : Ω => (1 : ℝ)) Set.univ =
      mass (fun _ : Ω => (1 : ℝ)) E * mass (fun _ : Ω => (1 : ℝ)) F) :
    probability (E ∩ F) = probability E * probability F := by
  have hp : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt Fintype.card_pos
  simp only [mass_one_univ] at hind
  unfold probability
  field_simp
  exact hind

lemma nonempty_of_mass_pos {w : Ω → ℝ} {E : Set Ω} (h : 0 < mass w E) :
    E.Nonempty := by
  by_contra hn
  have he := Set.not_nonempty_iff_eq_empty.mp hn
  simp [he] at h

lemma local_parameter (D : ℕ) (p : ℝ)
    (hp : 4 * ((D : ℝ) + 1) * p ≤ 1) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ p ≤ s * (1 - s) ^ D := by
  let s : ℝ := (2 * ((D : ℝ) + 1))⁻¹
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hden : 0 < 2 * ((D : ℝ) + 1) := by positivity
  have hs0 : 0 < s := inv_pos.mpr hden
  have heq : s * (2 * ((D : ℝ) + 1)) = 1 := inv_mul_cancel₀ hden.ne'
  have hsD : 0 ≤ s * D := mul_nonneg hs0.le hD
  have hshalf : s ≤ 1 / 2 := by nlinarith
  have hs1 : s < 1 := by linarith
  have hbern : 1 - (D : ℝ) * s ≤ (1 - s) ^ D := by
    simpa only [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (a := -s) (by linarith) D)
  have hhalf : (1 : ℝ) / 2 ≤ (1 - s) ^ D := by nlinarith
  have hp' : p ≤ s / 2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * ((D : ℝ) + 1) by positivity)).mp
    nlinarith [heq]
  refine ⟨s, hs0, hs1, hp'.trans ?_⟩
  nlinarith

end FiniteAvoidance

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace FiniteProduct

variable {C : Type uC} {S : Type uS}

def DependsOn (E : Set (C → S)) (s : Set C) : Prop :=
  ∀ β γ, Set.EqOn β γ s → (β ∈ E ↔ γ ∈ E)

lemma DependsOn.mono {E : Set (C → S)} {s t : Set C}
    (h : DependsOn E s) (hst : s ⊆ t) : DependsOn E t := by
  intro β γ he
  exact h β γ (he.mono hst)

noncomputable def splice (s : Set C) (β γ : C → S) : C → S := by
  classical
  exact fun c => if c ∈ s then β c else γ c

lemma splice_eqOn_left (s : Set C) (β γ : C → S) :
    Set.EqOn (splice s β γ) β s := by
  classical
  intro c hc
  simp [splice, hc]

lemma splice_eqOn_right (s : Set C) (β γ : C → S) :
    Set.EqOn (splice s β γ) γ sᶜ := by
  classical
  intro c hc
  simp only [Set.mem_compl_iff] at hc
  simp [splice, hc]

lemma splice_splice (s : Set C) (β γ : C → S) :
    splice s (splice s β γ) (splice s γ β) = β := by
  classical
  funext c
  by_cases hc : c ∈ s <;> simp [splice, hc]

noncomputable def cylinderEquiv (E F : Set (C → S)) (s : Set C)
    (hE : DependsOn E s) (hF : DependsOn F sᶜ) :
    ↥(E ∩ F) × (C → S) ≃ E × F where
  toFun p :=
    (⟨splice s p.1.1 p.2,
      (hE _ _ (splice_eqOn_left _ _ _)).mpr p.1.2.1⟩,
     ⟨splice s p.2 p.1.1,
      (hF _ _ (splice_eqOn_right _ _ _)).mpr p.1.2.2⟩)
  invFun p :=
    (⟨splice s p.1.1 p.2.1,
      ⟨(hE _ _ (splice_eqOn_left _ _ _)).mpr p.1.2,
       (hF _ _ (splice_eqOn_right _ _ _)).mpr p.2.2⟩⟩,
     splice s p.2.1 p.1.1)
  left_inv p := by
    apply Prod.ext
    · exact Subtype.ext (splice_splice _ _ _)
    · exact splice_splice _ _ _
  right_inv p := by
    apply Prod.ext <;> exact Subtype.ext (splice_splice _ _ _)

lemma independent_of_disjoint_support [Fintype C] [Fintype S] [DecidableEq C]
    (E F : Set (C → S)) (s t : Set C)
    (hE : DependsOn E s) (hF : DependsOn F t) (hst : Disjoint s t) :
    FiniteAvoidance.mass (fun _ => (1 : ℝ)) (E ∩ F) *
        FiniteAvoidance.mass (fun _ : C → S => (1 : ℝ)) Set.univ =
      FiniteAvoidance.mass (fun _ => (1 : ℝ)) E *
        FiniteAvoidance.mass (fun _ => (1 : ℝ)) F := by
  classical
  have htc : t ⊆ sᶜ := by
    intro c hc hs
    exact Set.disjoint_left.mp hst hs hc
  have hcard := Fintype.card_congr (cylinderEquiv E F s hE (hF.mono htc))
  simp only [Fintype.card_prod] at hcard
  simpa only [FiniteAvoidance.mass_one_eq_card, Nat.card_eq_fintype_card,
    Fintype.card_setUniv, Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ)) hcard

lemma DependsOn.compl {E : Set (C → S)} {s : Set C}
    (h : DependsOn E s) : DependsOn Eᶜ s := by
  intro β γ he
  exact not_congr (h β γ he)

lemma DependsOn.inter {E F : Set (C → S)} {s t : Set C}
    (hE : DependsOn E s) (hF : DependsOn F t) : DependsOn (E ∩ F) (s ∪ t) := by
  intro β γ he
  exact and_congr (hE β γ (he.mono Set.subset_union_left))
    (hF β γ (he.mono Set.subset_union_right))

lemma probability_inter [Fintype C] [Fintype S] [DecidableEq C] [Nonempty S]
    (E F : Set (C → S)) (s t : Set C)
    (hE : DependsOn E s) (hF : DependsOn F t) (hst : Disjoint s t) :
    FiniteAvoidance.probability (E ∩ F) =
      FiniteAvoidance.probability E * FiniteAvoidance.probability F :=
  FiniteAvoidance.probability_inter_of_independent _ _
    (independent_of_disjoint_support E F s t hE hF hst)

noncomputable def agreementEquiv (s : Set C) (d : C → S) :
    {β : C → S // Set.EqOn β d s} ≃ (↥(sᶜ) → S) := by
  classical
  exact {
  toFun β c := β.1 c
  invFun γ := ⟨fun c => if h : c ∈ s then d c else γ ⟨c, h⟩, by
    intro c hc
    simp [hc]⟩
  left_inv β := by
    apply Subtype.ext
    funext c
    dsimp
    split_ifs with hc
    · exact (β.2 hc).symm
    · rfl
  right_inv γ := by
    funext c
    have hc : (c : C) ∉ s := c.2
    simp [hc]
  }

lemma probability_agreement [Fintype C] [Fintype S] [DecidableEq C] [Nonempty S]
    (s : Set C) (d : C → S) :
    FiniteAvoidance.probability {β : C → S | Set.EqOn β d s} =
      ((Fintype.card S : ℝ) ^ Nat.card s)⁻¹ := by
  classical
  have hsplit := Fintype.card_congr (Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => S))
  simp only [Fintype.card_prod, Fintype.card_fun] at hsplit
  have hc := Nat.card_congr (agreementEquiv s d)
  unfold FiniteAvoidance.probability
  rw [FiniteAvoidance.mass_one_eq_card]
  change (Nat.card {β : C → S // Set.EqOn β d s} : ℝ) /
    Fintype.card (C → S) = _
  rw [hc]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow]
  have hsplit' := congrArg (fun n : ℕ => (n : ℝ)) hsplit
  simp only [Nat.cast_mul, Nat.cast_pow] at hsplit'
  rw [hsplit']
  have hq : (Fintype.card S : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt Fintype.card_pos
  field_simp
  congr 1

lemma agreement_dependsOn (s : Set C) (d : C → S) :
    DependsOn {β : C → S | Set.EqOn β d s} s := by
  intro β γ he
  exact ⟨fun hb c hc => (he hc).symm.trans (hb hc),
    fun hg c hc => (he hc).trans (hg hc)⟩

def allEvents {ι : Type uι} (E : ι → Set (C → S)) (J : Finset ι) : Set (C → S) :=
  {β | ∀ i ∈ J, β ∈ E i}

def supportUnion {ι : Type uι2} (s : ι → Set C) (J : Finset ι) : Set C :=
  {c | ∃ i ∈ J, c ∈ s i}

lemma allEvents_dependsOn {ι : Type uι3} (E : ι → Set (C → S))
    (s : ι → Set C) (hE : ∀ i, DependsOn (E i) (s i)) (J : Finset ι) :
    DependsOn (allEvents E J) (supportUnion s J) := by
  intro β γ he
  have hi (i) (hi : i ∈ J) : β ∈ E i ↔ γ ∈ E i := by
    have hs : s i ⊆ supportUnion s J := fun _ hc => ⟨i, hi, hc⟩
    exact hE i β γ (he.mono hs)
  exact ⟨fun hb i hm => (hi i hm).mp (hb i hm),
    fun hg i hm => (hi i hm).mpr (hg i hm)⟩

lemma probability_allEvents {ι : Type uι4} [Fintype C] [Fintype S]
    [DecidableEq C] [Nonempty S]
    (E : ι → Set (C → S)) (s : ι → Set C)
    (hE : ∀ i, DependsOn (E i) (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (J : Finset ι) :
    FiniteAvoidance.probability (allEvents E J) =
      ∏ i ∈ J, FiniteAvoidance.probability (E i) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [allEvents]
  | @insert i J hi ih =>
      have heq : allEvents E (insert i J) = E i ∩ allEvents E J := by
        ext β
        simp [allEvents]
      have hdisj : Disjoint (s i) (supportUnion s J) := by
        apply Set.disjoint_left.mpr
        rintro c hc ⟨j, hj, hcj⟩
        have hij : i ≠ j := fun he => hi (he ▸ hj)
        exact Set.disjoint_left.mp (hd hij) hc hcj
      rw [heq, probability_inter _ _ _ _ (hE i)
        (allEvents_dependsOn E s hE J) hdisj, ih, Finset.prod_insert hi]

section Centering

variable [AddCommGroup S] [DecidableEq C]

def centeredEquiv (a : C) : (C → S) ≃ (C → S) where
  toFun β c := if c = a then β c else β c - β a
  invFun γ c := if c = a then γ c else γ c + γ a
  left_inv β := by
    funext c
    by_cases hc : c = a <;> simp [hc]
  right_inv γ := by
    funext c
    by_cases hc : c = a <;> simp [hc]

def translationEquiv (g : C → S) : (C → S) ≃ (C → S) where
  toFun β c := g c + β c
  invFun γ c := γ c - g c
  left_inv β := by
    funext c
    simp
  right_inv γ := by
    funext c
    simp

end Centering

end FiniteProduct

namespace ShiftCombinatorics

variable {A : Type uA} {I : Type uI} [DecidableEq I]

def offLine (a : I → A) (i : I) : Set (I → A) :=
  Set.range (fun b : {b : A // b ≠ a i} => Function.update a i b.1)

lemma update_ne_center (a : I → A) (i : I) {b : A} (hb : b ≠ a i) :
    Function.update a i b ≠ a := by
  intro he
  exact hb (by simpa using congrFun he i)

lemma offLine_pairwise (a : I → A) :
    Pairwise (fun i j : I => Disjoint (offLine a i) (offLine a j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro c ⟨b, rfl⟩ ⟨d, hd⟩
  have he := congrFun hd i
  simp only [Function.update_self, Function.update_of_ne hij] at he
  exact b.2 he.symm

lemma card_offLine [Fintype A] (a : I → A) (i : I) :
    Nat.card (offLine a i) = Fintype.card A - 1 := by
  classical
  have hinj : Function.Injective
      (fun b : {b : A // b ≠ a i} => Function.update a i b.1) := by
    intro b d he
    apply Subtype.ext
    simpa using congrFun he i
  unfold offLine
  rw [Nat.card_congr (Equiv.ofInjective _ hinj).symm,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

lemma centered_line_iff {S : Type uS2} [AddCommGroup S] [DecidableEq (I → A)]
    (a : I → A) (γ : (I → A) → S) (i : I) :
    Set.EqOn (FiniteProduct.centeredEquiv a γ) (fun _ => 0) (offLine a i) ↔
      ∀ b : A, γ (Function.update a i b) = γ a := by
  classical
  constructor
  · intro h b
    by_cases hb : b = a i
    · simp [hb]
    · have hc := h (show Function.update a i b ∈ offLine a i from
        ⟨⟨b, hb⟩, rfl⟩)
      simpa [FiniteProduct.centeredEquiv, update_ne_center a i hb, sub_eq_zero] using hc
  · intro h c hc
    obtain ⟨b, rfl⟩ := hc
    simpa [FiniteProduct.centeredEquiv, update_ne_center a i b.2, sub_eq_zero] using h b

def starSupport (a : I → A) : Set (I → A) :=
  {c | c = a ∨ ∃ i b, c = Function.update a i b}

def badEvent {S : Type uS3} [AddCommGroup S] (g : (I → A) → S) (a : I → A) :
    Set ((I → A) → S) :=
  {β | ¬∃ i : I, ∀ b : A,
    g (Function.update a i b) + β (Function.update a i b) = g a + β a}

lemma badEvent_dependsOn {S : Type uS4} [AddCommGroup S]
    (g : (I → A) → S) (a : I → A) :
    FiniteProduct.DependsOn (badEvent g a) (starSupport a) := by
  intro β γ he
  apply not_congr
  apply exists_congr
  intro i
  apply forall_congr'
  intro b
  rw [he (show Function.update a i b ∈ starSupport a from Or.inr ⟨i, b, rfl⟩),
    he (show a ∈ starSupport a from Or.inl rfl)]

lemma probability_badEvent {S : Type uS5} [AddCommGroup S]
    [Fintype I] [Fintype A] [DecidableEq A] [Fintype S]
    (g : (I → A) → S) (a : I → A) :
    FiniteAvoidance.probability (badEvent g a) =
      (1 - ((Fintype.card S : ℝ) ^ (Fintype.card A - 1))⁻¹) ^ Fintype.card I := by
  classical
  let E (i : I) : Set ((I → A) → S) :=
    {γ | Set.EqOn γ (fun _ => 0) (offLine a i)}ᶜ
  let e := (FiniteProduct.translationEquiv g).trans (FiniteProduct.centeredEquiv a)
  have he (β : (I → A) → S) :
      β ∈ badEvent g a ↔ e β ∈ FiniteProduct.allEvents E Finset.univ := by
    change (¬∃ i, ∀ b, g (Function.update a i b) + β (Function.update a i b) =
      g a + β a) ↔ ∀ i ∈ Finset.univ, ¬Set.EqOn (e β) (fun _ => 0) (offLine a i)
    simp only [not_exists, Finset.mem_univ, forall_const]
    apply forall_congr'
    intro i
    exact not_congr (centered_line_iff a (FiniteProduct.translationEquiv g β) i).symm
  rw [FiniteAvoidance.probability_eq_of_equiv _ _ (e.subtypeEquiv he)]
  rw [FiniteProduct.probability_allEvents E (offLine a)
    (fun i => (FiniteProduct.agreement_dependsOn _ _).compl) (offLine_pairwise a)]
  have hE (i : I) : FiniteAvoidance.probability (E i) =
      1 - ((Fintype.card S : ℝ) ^ (Fintype.card A - 1))⁻¹ := by
    rw [FiniteAvoidance.probability_compl, FiniteProduct.probability_agreement,
      card_offLine]
  simp only [hE, Finset.prod_const, Finset.card_univ]

abbrev CenterCode (I : Type uI2) (A : Type uA2) := Unit ⊕ ((I × A) ⊕ ((I × A) × (I × A)))

def centerOfCode (a : I → A) : CenterCode I A → (I → A)
  | .inl _ => a
  | .inr (.inl (i, b)) => Function.update a i b
  | .inr (.inr ((i, b), (j, d))) => Function.update (Function.update a i b) j d

noncomputable def nearCenters [Fintype I] [Fintype A] (a : I → A) : Finset (I → A) := by
  classical
  exact Finset.univ.image (centerOfCode a)

lemma mem_nearCenters [Fintype I] [Fintype A] (a : I → A) (k : CenterCode I A) :
    centerOfCode a k ∈ nearCenters a := by
  classical
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

lemma card_nearCenters [Fintype I] [Fintype A] (a : I → A) :
    (nearCenters a).card ≤ 1 + Fintype.card I * Fintype.card A +
      (Fintype.card I) ^ 2 * (Fintype.card A) ^ 2 := by
  classical
  calc
    (nearCenters a).card ≤ Fintype.card (CenterCode I A) :=
      (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = _ := by
      simp only [CenterCode, Fintype.card_sum, Fintype.card_prod, Fintype.card_unit]
      ring

lemma restore_center (d c : I → A) (j : I) (b : A)
    (h : c = Function.update d j b) : d = Function.update c j (d j) := by
  rw [h]
  simp

lemma mem_nearCenters_of_shared [Fintype I] [Fintype A]
    {a d c : I → A} (ha : c ∈ starSupport a) (hd : c ∈ starSupport d) :
    d ∈ nearCenters a := by
  rcases ha with ha | ⟨i, b, ha⟩
  · rcases hd with hd | ⟨j, b, hj⟩
    · have he : d = a := hd.symm.trans ha
      rw [he]
      exact mem_nearCenters a (.inl ())
    · have he := restore_center d a j b (ha.symm.trans hj)
      rw [he]
      exact mem_nearCenters a (.inr (.inl (j, d j)))
  · rcases hd with hd | ⟨j, e, hj⟩
    · have he : d = Function.update a i b := hd.symm.trans ha
      rw [he]
      exact mem_nearCenters a (.inr (.inl (i, b)))
    · have he := restore_center d (Function.update a i b) j e (ha.symm.trans hj)
      rw [he]
      exact mem_nearCenters a (.inr (.inr ((i, b), (j, d j))))

end ShiftCombinatorics

section ShiftTable

variable {A : Type uA3} {K : Type uK} {S : Type uS6} [Field K] [AddCommGroup S] [Module K S]

def ShiftTableProperty (l : ℕ) (f : (Fin l → A) → (S →ₗ[K] S))
    (β : (Fin l → A) → S) : Prop :=
  ∀ (a : Fin l → A) (x : S), ∃ i : Fin l, ∀ b : A,
    f (Function.update a i b) x + β (Function.update a i b) = f a x + β a

theorem exists_shift_table_length (a q r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) :
    ∃ l : ℕ, 1 ≤ l ∧
      4 * (q * (1 + l * a + (l : ℝ) ^ 2 * a ^ 2) + 1) * r ^ l ≤ 1 := by
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr'
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr hr'
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr hr'
  have ht : Filter.Tendsto
      (fun l : ℕ => 4 * (q * (1 + l * a + (l : ℝ) ^ 2 * a ^ 2) + 1) * r ^ l)
      Filter.atTop (nhds 0) := by
    have ht' := ((h0.const_mul (4 * q + 4)).add
      (h1.const_mul (4 * q * a))).add (h2.const_mul (4 * q * a ^ 2))
    convert ht' using 1
    · ext l
      simp only [pow_one]
      ring
    · simp only [mul_zero, add_zero]
  have he : ∀ᶠ l : ℕ in Filter.atTop,
      1 ≤ l ∧ 4 * (q * (1 + l * a + (l : ℝ) ^ 2 * a ^ 2) + 1) * r ^ l < 1 :=
    (Filter.eventually_ge_atTop 1).and (ht.eventually (gt_mem_nhds zero_lt_one))
  obtain ⟨l, hl, hb⟩ := he.exists
  exact ⟨l, hl, hb.le⟩

theorem shift_table_at_length [Fintype A] [Fintype S] [DecidableEq A]
    (l : ℕ)
    (hnum : 4 * ((Fintype.card S : ℝ) *
      (1 + l * (Fintype.card A : ℝ) + (l : ℝ) ^ 2 * (Fintype.card A : ℝ) ^ 2) + 1) *
      (1 - ((Fintype.card S : ℝ) ^ (Fintype.card A - 1))⁻¹) ^ l ≤ 1)
    (f : (Fin l → A) → (S →ₗ[K] S)) :
    ∃ β : (Fin l → A) → S, ShiftTableProperty l f β := by
  classical
  let C := Fin l → A
  let Ω := C → S
  let B (j : S × C) : Set Ω := ShiftCombinatorics.badEvent (fun c => f c j.1) j.2
  let N (j : S × C) : Finset (S × C) :=
    Finset.univ ×ˢ ShiftCombinatorics.nearCenters j.2
  let D := Fintype.card S * (1 + l * Fintype.card A + l ^ 2 * (Fintype.card A) ^ 2)
  let p : ℝ := (1 - ((Fintype.card S : ℝ) ^ (Fintype.card A - 1))⁻¹) ^ l
  have hp : 4 * ((D : ℝ) + 1) * p ≤ 1 := by
    simpa only [D, p, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow] using hnum
  obtain ⟨s, hs0, hs1, hps⟩ := FiniteAvoidance.local_parameter D p hp
  have htotal : 0 < FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) Set.univ := by
    rw [FiniteAvoidance.mass_one_univ]
    exact_mod_cast Fintype.card_pos
  have hdegree (j : S × C) : (N j).card ≤ D := by
    rw [Finset.card_product, Finset.card_univ]
    exact Nat.mul_le_mul_left _ (by
      simpa only [Fintype.card_fin] using ShiftCombinatorics.card_nearCenters j.2)
  have hbad (j : S × C) : FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) (B j) ≤
      s * (1 - s) ^ D * FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) Set.univ := by
    have he : FiniteAvoidance.probability (B j) = p := by
      simpa only [Fintype.card_fin] using
        ShiftCombinatorics.probability_badEvent (fun c => f c j.1) j.2
    have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt Fintype.card_pos
    have he' := (div_eq_iff hc).mp he
    rw [FiniteAvoidance.mass_one_univ, he']
    exact mul_le_mul_of_nonneg_right hps (by positivity)
  have hind (j : S × C) (J : Finset (S × C)) (_hj : j ∉ J) (hJ : Disjoint J (N j)) :
      FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) (B j ∩ FiniteAvoidance.avoids B J) *
          FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) Set.univ =
        FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) (B j) *
          FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) (FiniteAvoidance.avoids B J) := by
    apply FiniteProduct.independent_of_disjoint_support _ _
      (ShiftCombinatorics.starSupport j.2)
      (FiniteProduct.supportUnion (fun k : S × C => ShiftCombinatorics.starSupport k.2) J)
    · exact ShiftCombinatorics.badEvent_dependsOn _ _
    · exact FiniteProduct.allEvents_dependsOn (fun k => (B k)ᶜ) _
        (fun k => (ShiftCombinatorics.badEvent_dependsOn _ _).compl) J
    · apply Set.disjoint_left.mpr
      rintro c hc ⟨k, hk, hck⟩
      apply Finset.disjoint_left.mp hJ hk
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
        ShiftCombinatorics.mem_nearCenters_of_shared hc hck⟩
  have hav := FiniteAvoidance.local_lemma (fun _ : Ω => (1 : ℝ))
    (fun _ => zero_le_one) htotal B N D s hs0 hs1 hdegree hbad hind Finset.univ
  obtain ⟨β, hβ⟩ := FiniteAvoidance.nonempty_of_mass_pos hav
  refine ⟨β, ?_⟩
  intro a x
  exact not_not.mp (hβ (x, a) (Finset.mem_univ _))

theorem exists_shift_table [Fintype A] [Nonempty A] [Fintype S] :
    ∃ l : ℕ, 1 ≤ l ∧ ∀ f : (Fin l → A) → (S →ₗ[K] S),
      ∃ β : (Fin l → A) → S, ShiftTableProperty l f β := by
  classical
  let r : ℝ := 1 - ((Fintype.card S : ℝ) ^ (Fintype.card A - 1))⁻¹
  have hq : (1 : ℝ) ≤ Fintype.card S := by
    exact_mod_cast Fintype.card_pos
  have hpow : (1 : ℝ) ≤ (Fintype.card S : ℝ) ^ (Fintype.card A - 1) := one_le_pow₀ hq
  have hr0 : 0 ≤ r := sub_nonneg.mpr (inv_le_one_of_one_le₀ hpow)
  have hr1 : r < 1 := by
    have hi := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hpow)
    dsimp [r]
    linarith
  obtain ⟨l, hl, hnum⟩ := exists_shift_table_length (Fintype.card A) (Fintype.card S) r hr0 hr1
  exact ⟨l, hl, fun f => shift_table_at_length l hnum f⟩

end ShiftTable

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace FiniteAvoidance

variable {Ω : Type uΩ} {ι : Type uι} [Fintype Ω]

lemma probability_nonneg (E : Set Ω) : 0 ≤ probability E :=
  div_nonneg (mass_nonneg (by intro; norm_num) _) (Nat.cast_nonneg _)

lemma probability_mono {E F : Set Ω} (hEF : E ⊆ F) :
    probability E ≤ probability F :=
  div_le_div_of_nonneg_right (mass_mono (by intro; norm_num) hEF) (Nat.cast_nonneg _)

lemma probability_union_le (E F : Set Ω) :
    probability (E ∪ F) ≤ probability E + probability F := by
  classical
  unfold probability mass
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> simp [he, hf]

lemma probability_iUnion_finset_le (E : ι → Set Ω) (J : Finset ι) :
    probability (⋃ i ∈ J, E i) ≤ ∑ i ∈ J, probability (E i) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [probability, mass]
  | @insert i J hi ih =>
      simp only [Finset.set_biUnion_insert, Finset.sum_insert hi]
      exact (probability_union_le _ _).trans (add_le_add (le_refl _) ih)

lemma exists_avoiding [Nonempty Ω] [Fintype ι] (E : ι → Set Ω)
    (h : ∑ i, probability (E i) < 1) : ∃ x, ∀ i, x ∉ E i := by
  classical
  by_contra hn
  have hcover : (⋃ i ∈ (Finset.univ : Finset ι), E i) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_const, Set.mem_univ, iff_true]
    by_contra hx
    exact hn ⟨x, by simpa only [not_exists] using hx⟩
  have hh := probability_iUnion_finset_le E Finset.univ
  rw [hcover, probability_univ] at hh
  linarith

end FiniteAvoidance

namespace TagPartitions

variable {T : Type uT} [DecidableEq T]

def Feasible (a l g n : T) : Prop := a ≠ l ∧ ({a, l} : Finset T) ≠ {g, n}

def Satisfies (a l g n : T) (p : T → Bool) : Prop :=
  p a = false ∧ p l = true ∧ p g = p n

lemma feasible_partition {a l g n : T} (h : Feasible a l g n) :
    ∃ p : T → Bool, Satisfies a l g n p := by
  classical
  obtain ⟨hal, hset⟩ := h
  let p : T → Bool := fun x => decide (x = l ∨ ((g = l ∨ n = l) ∧ (x = g ∨ x = n)))
  refine ⟨p, ?_⟩
  dsimp [Satisfies, p]
  by_cases hgl : g = l <;> by_cases hnl : n = l <;>
    by_cases hag : a = g <;> by_cases han : a = n <;>
    simp_all [Finset.pair_comm]

noncomputable def repetitions (m : ℕ) : ℕ := ⌈64 * Real.log (2 * m)⌉₊

lemma repetitions_estimate {m : ℕ} (hm : 0 < m) :
    (m : ℝ) ^ 4 * ((15 : ℝ) / 16) ^ repetitions m ≤ 1 / 16 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by nlinarith)
  have hn := Nat.le_ceil (64 * Real.log (2 * m))
  change 64 * Real.log (2 * m) ≤ (repetitions m : ℝ) at hn
  have hpow : ((15 : ℝ) / 16) ^ repetitions m ≤
      Real.exp (-4 * Real.log (2 * m)) := by
    calc
      _ ≤ Real.exp (-(1 / 16 : ℝ)) ^ repetitions m :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.one_sub_le_exp_neg (1 / 16 : ℝ)]) _
      _ = Real.exp ((repetitions m : ℝ) * (-(1 / 16))) :=
        (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (-4 * Real.log (2 * m)) = ((2 * m : ℝ) ^ 4)⁻¹ := by
    rw [show -4 * Real.log (2 * m) = -(4 * Real.log (2 * m)) by ring,
      Real.exp_neg, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (by positivity)]
  calc
    (m : ℝ) ^ 4 * ((15 : ℝ) / 16) ^ repetitions m ≤
        (m : ℝ) ^ 4 * ((2 * m : ℝ) ^ 4)⁻¹ := by
          rw [← he]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 1 / 16 := by field_simp; ring

lemma repetitions_bound {m : ℕ} (hm : 0 < m) :
    (repetitions m : ℝ) ≤ 66 * Real.log (2 * m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : (1 / 2 : ℝ) < Real.log (2 * m) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ 2 * m by linarith)
    linarith [Real.log_two_gt_d9]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 64 * Real.log (2 * m) by positivity)
  change (repetitions m : ℝ) < _ at hceil
  linarith

lemma repetitions_pos {m : ℕ} (hm : 0 < m) : 0 < repetitions m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 < Real.log (2 * m) := Real.log_pos (by linarith)
  have hn := Nat.le_ceil (64 * Real.log (2 * m))
  change 64 * Real.log (2 * m) ≤ (repetitions m : ℝ) at hn
  by_contra hn0
  have hz : repetitions m = 0 := by omega
  simp [hz] at hn
  linarith

lemma probability_satisfies [Fintype T] (N : ℕ) (i : Fin N)
    {a l g n : T} (h : Feasible a l g n) :
    1 / 16 ≤ FiniteAvoidance.probability
      {β : (Fin N × T) → Bool | Satisfies a l g n (fun t => β (i, t))} := by
  classical
  obtain ⟨p, hp⟩ := feasible_partition h
  let s : Finset (Fin N × T) := {(i, a), (i, l), (i, g), (i, n)}
  let d : (Fin N × T) → Bool := fun c => p c.2
  have hsub : {β : (Fin N × T) → Bool | Set.EqOn β d s} ⊆
      {β | Satisfies a l g n (fun t => β (i, t))} := by
    intro β hβ
    obtain ⟨ha, hl, hgn⟩ := hp
    dsimp [Satisfies]
    have he (t) (ht : (i, t) ∈ s) : β (i, t) = p t := hβ ht
    rw [he a (by simp [s]), he l (by simp [s]), he g (by simp [s]), he n (by simp [s])]
    exact ⟨ha, hl, hgn⟩
  have hprob := FiniteAvoidance.probability_mono hsub
  rw [FiniteProduct.probability_agreement] at hprob
  simp only [Fintype.card_bool, Nat.cast_ofNat, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hprob
  have hcard : s.card ≤ 4 := by
    dsimp [s]
    exact (Finset.card_insert_le _ _).trans (by
      have h1 := Finset.card_insert_le (i, l) ({(i, g), (i, n)} : Finset (Fin N × T))
      have h2 := Finset.card_insert_le (i, g) ({(i, n)} : Finset (Fin N × T))
      simp only [Finset.card_singleton] at h2
      omega)
  have hpow : (2 : ℝ) ^ s.card ≤ 16 := by
    calc
      _ ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hcard
      _ = _ := by norm_num
  have hinv : (1 / 16 : ℝ) ≤ ((2 : ℝ) ^ s.card)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ s.card) hpow
  exact hinv.trans hprob

omit [DecidableEq T] in
lemma satisfies_depends (N : ℕ) (i : Fin N) (a l g n : T) :
    FiniteProduct.DependsOn
      {β : (Fin N × T) → Bool | Satisfies a l g n (fun t => β (i, t))}
      {c | c.1 = i} := by
  intro β γ he
  have hrow : (fun t => β (i, t)) = (fun t => γ (i, t)) :=
    funext (fun t => he (by rfl))
  simp only [Set.mem_ofPred_eq, hrow]

lemma probability_failure [Fintype T] (N : ℕ) {a l g n : T}
    (h : Feasible a l g n) :
    FiniteAvoidance.probability
      {β : (Fin N × T) → Bool | ∀ i, ¬ Satisfies a l g n (fun t => β (i, t))} ≤
      ((15 : ℝ) / 16) ^ N := by
  classical
  let E (i : Fin N) : Set ((Fin N × T) → Bool) :=
    {β | ¬ Satisfies a l g n (fun t => β (i, t))}
  have hdep (i) : FiniteProduct.DependsOn (E i) {c | c.1 = i} :=
    (satisfies_depends N i a l g n).compl
  have hd : Pairwise (fun i j : Fin N => Disjoint {c : Fin N × T | c.1 = i} {c | c.1 = j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (by intro c hi hj; exact hij (hi.symm.trans hj))
  have heq : {β : (Fin N × T) → Bool | ∀ i, ¬ Satisfies a l g n (fun t => β (i, t))} =
      FiniteProduct.allEvents E Finset.univ := by ext β; simp [FiniteProduct.allEvents, E]
  rw [heq, FiniteProduct.probability_allEvents E _ hdep hd]
  calc
    _ ≤ ∏ _i : Fin N, ((15 : ℝ) / 16) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact FiniteAvoidance.probability_nonneg _
      · intro i _
        change FiniteAvoidance.probability
          ({β : (Fin N × T) → Bool | Satisfies a l g n (fun t => β (i, t))}ᶜ) ≤ _
        rw [FiniteAvoidance.probability_compl]
        linarith [probability_satisfies N i h]
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem exists_partitions [Fintype T] [Nonempty T] :
    ∃ p : Fin (repetitions (Fintype.card T)) → T → Bool,
      ∀ a l g n, Feasible a l g n → ∃ i,
        Satisfies a l g n (p i) := by
  classical
  let N := repetitions (Fintype.card T)
  let E : (T × T × T × T) → Set ((Fin N × T) → Bool) := fun q =>
    {β | Feasible q.1 q.2.1 q.2.2.1 q.2.2.2 ∧
      ∀ i, ¬ Satisfies q.1 q.2.1 q.2.2.1 q.2.2.2 (fun t => β (i, t))}
  have hbound (q) : FiniteAvoidance.probability (E q) ≤ ((15 : ℝ) / 16) ^ N := by
    by_cases hq : Feasible q.1 q.2.1 q.2.2.1 q.2.2.2
    · exact (FiniteAvoidance.probability_mono (by intro β hβ; exact hβ.2)).trans
        (probability_failure N hq)
    · simp [E, hq, FiniteAvoidance.probability, FiniteAvoidance.mass]
      positivity
  have hsum : ∑ q, FiniteAvoidance.probability (E q) < 1 := by
    calc
      _ ≤ ∑ _q : T × T × T × T, ((15 : ℝ) / 16) ^ N :=
        Finset.sum_le_sum (fun q _ => hbound q)
      _ = (Fintype.card T : ℝ) ^ 4 * ((15 : ℝ) / 16) ^ N := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
          Nat.cast_mul]
        ring
      _ ≤ 1 / 16 := repetitions_estimate Fintype.card_pos
      _ < 1 := by norm_num
  obtain ⟨β, hβ⟩ := FiniteAvoidance.exists_avoiding E hsum
  refine ⟨fun i t => β (i, t), ?_⟩
  intro a l g n h
  have hh := hβ (a, l, g, n)
  by_contra hn
  push Not at hn
  exact hh ⟨h, hn⟩

noncomputable def typeCount (m : ℕ) : ℕ := ⌈Real.log m / Real.log 2⌉₊

lemma card_le_binary {m : ℕ} (hm : 0 < m) : m ≤ 2 ^ typeCount m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := Nat.le_ceil (Real.log m / Real.log 2)
  change Real.log m / Real.log 2 ≤ (typeCount m : ℝ) at hn
  have hh : Real.log m ≤ (typeCount m : ℝ) * Real.log 2 := (div_le_iff₀ h2).mp hn
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log hmR, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  exact_mod_cast he

lemma typeCount_bound {m : ℕ} (hm : 0 < m) :
    (typeCount m : ℝ) ≤ 2 * Real.log (2 * m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogm := Real.log_nonneg hm1
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.log m / Real.log 2 by positivity)
  change (typeCount m : ℝ) < Real.log m / Real.log 2 + 1 at hceil
  have hh : (typeCount m : ℝ) * Real.log 2 < Real.log m + Real.log 2 := by
    have h := (mul_lt_mul_iff_left₀ (show 0 < Real.log 2 by linarith)).mpr hceil
    rwa [add_mul, div_mul_cancel₀ _ (ne_of_gt (show 0 < Real.log 2 by linarith)), one_mul] at h
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmR.ne']
  have hcount : (0 : ℝ) ≤ typeCount m := Nat.cast_nonneg _
  nlinarith

omit [DecidableEq T] in
lemma exists_types [Fintype T] [Nonempty T] :
    ∃ p : Fin (typeCount (Fintype.card T)) → T → Bool,
      ∀ a l, a ≠ l → ∃ i, p i a ≠ p i l := by
  classical
  have hcard : Fintype.card T ≤ Fintype.card (Fin (typeCount (Fintype.card T)) → Bool) := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using
      card_le_binary (m := Fintype.card T) Fintype.card_pos
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun i a => f a i, ?_⟩
  intro a l hal
  by_contra hn
  push Not at hn
  exact hal (f.injective (funext hn))

lemma total_count_bound {m : ℕ} (hm : 0 < m) :
    ((repetitions m + 4 * 400 ^ 2 * typeCount m : ℕ) : ℝ) ≤
      10000000 * Real.log (2 * m) := by
  have ha := repetitions_bound hm
  have hb := typeCount_bound hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
  push_cast
  nlinarith

end TagPartitions

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace RobustClock

variable {P : Type uP} [DecidableEq P]

def vertices : List (P × P) → Finset P
  | [] => ∅
  | e :: es => insert e.1 (insert e.2 (vertices es))

def FreshPairs : List (P × P) → Prop
  | [] => True
  | e :: es => e.1 ≠ e.2 ∧ (e.1 ∉ vertices es ∨ e.2 ∉ vertices es) ∧ FreshPairs es

lemma mem_vertices {es : List (P × P)} {e : P × P} (he : e ∈ es) :
    e.1 ∈ vertices es ∧ e.2 ∈ vertices es := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
      rcases List.mem_cons.mp he with rfl | he
      · simp [vertices]
      · obtain ⟨h1, h2⟩ := ih he
        simp [vertices, h1, h2]

lemma card_vertices (es : List (P × P)) : (vertices es).card ≤ 2 * es.length := by
  induction es with
  | nil => simp [vertices]
  | cons e es ih =>
      have h1 := Finset.card_insert_le e.1 (insert e.2 (vertices es))
      have h2 := Finset.card_insert_le e.2 (vertices es)
      simp only [vertices, List.length_cons]
      omega

lemma FreshPairs.nodup {es : List (P × P)} (h : FreshPairs es) : es.Nodup := by
  induction es with
  | nil => exact List.nodup_nil
  | cons e es ih =>
      refine List.nodup_cons.mpr ⟨?_, ih h.2.2⟩
      intro he
      obtain ⟨h1, h2⟩ := mem_vertices he
      exact h.2.1.elim (fun hn => hn h1) (fun hn => hn h2)

lemma FreshPairs.realize {A : Type uA} [AddCommGroup A]
    {es : List (P × P)} (h : FreshPairs es) (d : P × P → A) :
    ∃ v : P → A, ∀ e ∈ es, v e.2 - v e.1 = d e := by
  classical
  induction es with
  | nil => exact ⟨fun _ => 0, by simp⟩
  | cons e es ih =>
      obtain ⟨v, hv⟩ := ih h.2.2
      rcases h.2.1 with hnew | hnew
      · refine ⟨Function.update v e.1 (v e.2 - d e), ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simp only [Function.update_self, Function.update_of_ne h.1.symm]
          abel
        · obtain ⟨ha1, ha2⟩ := mem_vertices ha
          have hn1 : a.1 ≠ e.1 := fun hh => hnew (hh ▸ ha1)
          have hn2 : a.2 ≠ e.1 := fun hh => hnew (hh ▸ ha2)
          simp only [Function.update_of_ne hn1, Function.update_of_ne hn2]
          exact hv a ha
      · refine ⟨Function.update v e.2 (v e.1 + d e), ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simp only [Function.update_self, Function.update_of_ne h.1]
          abel
        · obtain ⟨ha1, ha2⟩ := mem_vertices ha
          have hn1 : a.1 ≠ e.2 := fun hh => hnew (hh ▸ ha1)
          have hn2 : a.2 ≠ e.2 := fun hh => hnew (hh ▸ ha2)
          simp only [Function.update_of_ne hn1, Function.update_of_ne hn2]
          exact hv a ha

lemma realize_sequence {A : Type uA2} [AddCommGroup A] {F : ℕ} (f : Fin F → P × P)
    (hf : FreshPairs (List.ofFn f)) (d : Fin F → A) :
    ∃ v : P → A, ∀ j, v (f j).2 - v (f j).1 = d j := by
  classical
  have hinj : Function.Injective f := List.nodup_ofFn.mp hf.nodup
  obtain ⟨v, hv⟩ := hf.realize (Function.extend f d (fun _ => 0))
  refine ⟨v, fun j => ?_⟩
  simpa only [hinj.extend_apply] using hv (f j) (List.mem_ofFn.mpr ⟨j, rfl⟩)

lemma extract_forest (B : Finset (P × P)) (hB : ∀ e ∈ B, e.1 ≠ e.2)
    (F : ℕ) (hcard : 4 * F ^ 2 < B.card) :
    ∃ f : Fin F → P × P, FreshPairs (List.ofFn f) ∧ ∀ j, f j ∈ B := by
  have build : ∀ n ≤ F, ∃ es : List (P × P), es.length = n ∧ FreshPairs es ∧
      ∀ e ∈ es, e ∈ B := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨[], rfl, trivial, by simp⟩
    | succ n ih =>
        intro hn
        obtain ⟨es, hlen, hf, he⟩ := ih (by omega)
        have hverts : (vertices es).card ≤ 2 * F := by
          have hc := card_vertices es
          rw [hlen] at hc
          omega
        have hnot : ¬B ⊆ (vertices es) ×ˢ (vertices es) := by
          intro hsub
          have hc := Finset.card_le_card hsub
          rw [Finset.card_product] at hc
          have hm := Nat.mul_le_mul hverts hverts
          nlinarith
        obtain ⟨e, heB, heout⟩ := Finset.not_subset.mp hnot
        have heFresh : e.1 ∉ vertices es ∨ e.2 ∉ vertices es := by
          simpa only [Finset.mem_product, not_and_or] using heout
        refine ⟨e :: es, by simp [hlen], ⟨hB e heB, heFresh, hf⟩, ?_⟩
        intro a ha
        exact (List.mem_cons.mp ha).elim (fun h => h ▸ heB) (he a)
  obtain ⟨es, hlen, hf, he⟩ := build F le_rfl
  subst F
  exact ⟨es.get, by simpa only [List.ofFn_get] using hf,
    fun j => he (es.get j) (List.get_mem es j)⟩

lemma count_of_no_forest (B : Finset (P × P)) (hB : ∀ e ∈ B, e.1 ≠ e.2)
    (F : ℕ) (hn : ∀ f : Fin F → P × P, FreshPairs (List.ofFn f) →
      ∃ j, f j ∉ B) : B.card ≤ 4 * F ^ 2 := by
  by_contra h
  obtain ⟨f, hf, hm⟩ := extract_forest B hB F (Nat.lt_of_not_ge h)
  obtain ⟨j, hj⟩ := hn f hf
  exact hj (hm j)

abbrev Circle := UnitAddCircle

@[simp] lemma coe_integer (k : ℤ) : (((k : ℝ) : Circle)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨k, by simp⟩

lemma representative (a : Circle) : ∃ r : ℝ, (r : Circle) = a ∧ |r| = ‖a‖ := by
  obtain ⟨x⟩ := a
  change ∃ r : ℝ, (r : Circle) = (x : Circle) ∧ |r| = ‖(x : Circle)‖
  refine ⟨x - round x, ?_, ?_⟩
  · rw [AddCircle.coe_sub, coe_integer, sub_zero]
  · simpa using (AddCircle.norm_eq (1 : ℝ) (x := x)).symm

lemma norm_coe_le_abs (r : ℝ) : ‖(r : Circle)‖ ≤ |r| :=
  QuotientAddGroup.norm_mk_le_norm

lemma coe_mod_fraction (n : ℕ) (hn : 0 < n) (k : ℤ) :
    ((((k % (n : ℤ) : ℤ) : ℝ) / n : ℝ) : Circle) = (((k : ℝ) / n : ℝ) : Circle) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hc : ((k % (n : ℤ) : ℤ) : ℝ) + (n : ℝ) * ((k / (n : ℤ) : ℤ) : ℝ) = k := by
    exact_mod_cast Int.emod_add_mul_ediv k (n : ℤ)
  have hh : ((k % (n : ℤ) : ℤ) : ℝ) / n = (k : ℝ) / n - ((k / (n : ℤ) : ℤ) : ℝ) := by
    apply (div_eq_iff hnR).mpr
    rw [sub_mul, div_mul_cancel₀ _ hnR]
    linarith
  rw [hh, AddCircle.coe_sub, coe_integer, sub_zero]

lemma grid_near (n : ℕ) (hn : 0 < n) (a : Circle) :
    ∃ j : Fin n, ‖a + (((j : ℝ) / n : ℝ) : Circle)‖ ≤ 1 / (2 * n) := by
  obtain ⟨r, rfl, _⟩ := representative a
  let k : ℤ := -round ((n : ℝ) * r)
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 := Int.emod_nonneg k hnZ.ne'
  let j : Fin n := ⟨(k % (n : ℤ)).toNat,
    (Int.toNat_lt hk0).mpr (Int.emod_lt_of_pos k hnZ)⟩
  have hj : (j : ℝ) = ((k % (n : ℤ) : ℤ) : ℝ) := by
    change (((k % (n : ℤ)).toNat : ℕ) : ℝ) = _
    exact_mod_cast Int.toNat_of_nonneg hk0
  refine ⟨j, ?_⟩
  rw [hj, coe_mod_fraction n hn, ← AddCircle.coe_add]
  apply (norm_coe_le_abs _).trans
  have hh : r + (k : ℝ) / n = ((n : ℝ) * r - round ((n : ℝ) * r)) / n := by
    dsimp [k]
    push_cast
    field_simp
    ring
  rw [hh, abs_div, abs_of_pos hnR]
  calc
    |(n : ℝ) * r - round ((n : ℝ) * r)| / n ≤ (1 / 2 : ℝ) / n :=
      div_le_div_of_nonneg_right (abs_sub_round _) hnR.le
    _ = 1 / (2 * n) := by ring

def Near (C : Set Circle) (r : ℝ) : Set Circle :=
  {x | ∃ c ∈ C, dist x c ≤ r}

def centersI : Set Circle := {((0 : ℝ) : Circle), ((1 / 6 : ℝ) : Circle),
  ((3 / 6 : ℝ) : Circle)}

def centersJ : Set Circle := {((2 / 6 : ℝ) : Circle), ((4 / 6 : ℝ) : Circle),
  ((5 / 6 : ℝ) : Circle)}

lemma center_separation {c d : Circle} (hc : c ∈ centersI) (hd : d ∈ centersJ) :
    1 / 6 ≤ dist c d := by
  simp only [centersI, centersJ, Set.mem_insert_iff, Set.mem_singleton_iff] at hc hd
  rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
    norm_num [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]

lemma center_sums (j : Fin 6) : ∃ c ∈ centersI, ∃ d ∈ centersJ,
    c + d = (((j : ℝ) / 6 : ℝ) : Circle) := by
  fin_cases j
  · refine ⟨((1 / 6 : ℝ) : Circle), by simp [centersI],
      ((5 / 6 : ℝ) : Circle), by simp [centersJ], ?_⟩
    norm_num [← AddCircle.coe_add]
  · refine ⟨((3 / 6 : ℝ) : Circle), by simp [centersI],
      ((4 / 6 : ℝ) : Circle), by simp [centersJ], ?_⟩
    rw [← AddCircle.coe_add]
    have he : (3 / 6 + 4 / 6 : ℝ) = 1 / 6 + 1 := by ring
    rw [he, AddCircle.coe_add_period]
    norm_num
  · exact ⟨((0 : ℝ) : Circle), by simp [centersI],
      ((2 / 6 : ℝ) : Circle), by simp [centersJ], by simp⟩
  · refine ⟨((1 / 6 : ℝ) : Circle), by simp [centersI],
      ((2 / 6 : ℝ) : Circle), by simp [centersJ], ?_⟩
    norm_num [← AddCircle.coe_add]
  · exact ⟨((0 : ℝ) : Circle), by simp [centersI],
      ((4 / 6 : ℝ) : Circle), by simp [centersJ], by simp⟩
  · exact ⟨((0 : ℝ) : Circle), by simp [centersI],
      ((5 / 6 : ℝ) : Circle), by simp [centersJ], by simp⟩

lemma type_one_difference {i j : Circle}
    (hi : i ∈ Near centersI (1 / 16)) (hj : j ∈ Near centersJ (1 / 16)) :
    1 / 24 ≤ ‖i - j‖ := by
  obtain ⟨c, hc, hic⟩ := hi
  obtain ⟨d, hd, hjd⟩ := hj
  have hsep := center_separation hc hd
  have ht := dist_triangle4 c i j d
  rw [dist_comm c i, dist_eq_norm i j] at ht
  linarith

lemma type_one_interior (z : Circle) :
    ∃ i j : Circle, i + j = z ∧ ∀ h : Circle, ‖h‖ ≤ 1 / 96 →
      i + h ∈ Near centersI (1 / 16) ∧ j - h ∈ Near centersJ (1 / 16) := by
  obtain ⟨k, hk⟩ := grid_near 6 (by omega) (-z)
  obtain ⟨c, hc, d, hd, hsum⟩ := center_sums k
  have herr : ‖z - (c + d)‖ ≤ 1 / 12 := by
    rw [hsum, ← norm_neg, neg_sub, sub_eq_add_neg]
    simpa only [Nat.cast_ofNat, show (1 : ℝ) / (2 * 6) = 1 / 12 by norm_num, add_comm] using hk
  obtain ⟨δ, hδ, hnorm⟩ := representative (z - (c + d))
  let t : Circle := ((δ / 2 : ℝ) : Circle)
  have ht : ‖t‖ ≤ 1 / 24 := by
    apply (norm_coe_le_abs _).trans
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), hnorm]
    linarith
  refine ⟨c + t, d + t, ?_, ?_⟩
  · have htt : t + t = z - (c + d) := by
      dsimp [t]
      rw [← AddCircle.coe_add, show δ / 2 + δ / 2 = δ by ring, hδ]
    calc
      c + t + (d + t) = c + d + (t + t) := by abel
      _ = z := by rw [htt]; abel
  · intro h hh
    constructor
    · refine ⟨c, hc, ?_⟩
      have hnorm := norm_add_le t h
      have he : c + t + h - c = t + h := by abel
      rw [dist_eq_norm, he]
      linarith
    · refine ⟨d, hd, ?_⟩
      have hnorm := norm_sub_le t h
      have he : d + t - h - d = t - h := by abel
      rw [dist_eq_norm, he]
      linarith

noncomputable def smallCoords {C : Type uC} [Fintype C] (x : C → Circle) (r : ℝ) : Finset C := by
  classical
  exact Finset.univ.filter (fun c => ‖x c‖ ≤ r)

lemma mem_smallCoords {C : Type uC2} [Fintype C] (x : C → Circle) (r : ℝ) (c : C) :
    c ∈ smallCoords x r ↔ ‖x c‖ ≤ r := by
  classical
  simp [smallCoords]

def TypeTwo {C : Type uC3} [Fintype C] (s : ℕ) : Set (C → Circle) :=
  {x | s + 1 ≤ (smallCoords x (1 / 100)).card}

lemma type_two_difference {C : Type uC4} [Fintype C] (s : ℕ)
    (hC : Fintype.card C = 2 * s + 1) {i j : C → Circle}
    (hi : i ∈ TypeTwo s) (hj : j ∈ TypeTwo s) :
    ∃ c, ‖i c - j c‖ ≤ 2 / 100 := by
  classical
  have hc : (Finset.univ : Finset C).card <
      (smallCoords i (1 / 100)).card + (smallCoords j (1 / 100)).card := by
    change s + 1 ≤ _ at hi hj
    simp only [Finset.card_univ, hC]
    omega
  obtain ⟨c, hc'⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ _) (Finset.subset_univ _) hc
  obtain ⟨hci, hcj⟩ := Finset.mem_inter.mp hc'
  have hic := (mem_smallCoords _ _ _).mp hci
  have hjc := (mem_smallCoords _ _ _).mp hcj
  refine ⟨c, ?_⟩
  have hh := norm_sub_le (i c) (j c)
  linarith

lemma type_two_interior {C : Type uC5} [Fintype C] (s : ℕ)
    (hC : Fintype.card C = 2 * s + 1) (z : C → Circle)
    (hz : ∃ c, ‖z c‖ ≤ 1 / 200) :
    ∃ i j : C → Circle, i + j = z ∧ ∀ h : C → Circle,
      (∀ c, ‖h c‖ ≤ 1 / 400) → i + h ∈ TypeTwo s ∧ j - h ∈ TypeTwo s := by
  classical
  obtain ⟨c₀, hc₀⟩ := hz
  have hcard : s ≤ ((Finset.univ : Finset C).erase c₀).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hC]
    omega
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hcard
  have hcA : c₀ ∉ A := fun hm => (Finset.mem_erase.mp (hA hm)).1 rfl
  let i : C → Circle := fun c => if c ∈ A then 0 else z c
  let j : C → Circle := z - i
  refine ⟨i, j, ?_, ?_⟩
  · dsimp [j]
    abel
  · intro h hh
    constructor
    · change s + 1 ≤ (smallCoords (i + h) (1 / 100)).card
      have hsub : insert c₀ A ⊆ smallCoords (i + h) (1 / 100) := by
        intro c hc
        apply (mem_smallCoords _ _ _).mpr
        rcases Finset.mem_insert.mp hc with hcc | hc
        · subst c
          have hnorm := norm_add_le (z c₀) (h c₀)
          change ‖i c₀ + h c₀‖ ≤ _
          simp only [i, hcA, ite_false]
          linarith [hh c₀]
        · change ‖i c + h c‖ ≤ _
          simp only [i, hc, ite_true, zero_add]
          linarith [hh c]
      have hle := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hcA, hAc] at hle
      exact hle
    · change s + 1 ≤ (smallCoords (j - h) (1 / 100)).card
      have hsub : Aᶜ ⊆ smallCoords (j - h) (1 / 100) := by
        intro c hc
        have hc' := Finset.mem_compl.mp hc
        apply (mem_smallCoords _ _ _).mpr
        change ‖z c - i c - h c‖ ≤ _
        simp only [i, hc', ite_false, sub_self, zero_sub, norm_neg]
        linarith [hh c]
      have hle := Finset.card_le_card hsub
      rw [Finset.card_compl, hC, hAc] at hle
      omega

def FirstI (ε : ℝ) (side : Bool) : Set Circle :=
  if side then {i | 4 * ε ≤ ‖i‖} else {i | ‖i‖ ≤ ε}

def FirstJ (ε : ℝ) (side : Bool) : Set Circle :=
  if side then {j | ‖j‖ ≤ ε} else {j | 4 * ε ≤ ‖j‖}

lemma first_left_right {ε : ℝ} {i j : Circle}
    (hi : i ∈ FirstI ε false) (hj : j ∈ FirstJ ε true) : ‖i + j‖ ≤ 2 * ε := by
  change ‖i‖ ≤ ε at hi
  change ‖j‖ ≤ ε at hj
  linarith [norm_add_le i j]

lemma first_same_side {ε : ℝ} (side : Bool) {i j : Circle}
    (hi : i ∈ FirstI ε side) (hj : j ∈ FirstJ ε side) : 3 * ε ≤ ‖i + j‖ := by
  cases side
  · change ‖i‖ ≤ ε at hi
    change 4 * ε ≤ ‖j‖ at hj
    have h := norm_sub_le_norm_add j i
    rw [add_comm j i] at h
    linarith
  · change 4 * ε ≤ ‖i‖ at hi
    change ‖j‖ ≤ ε at hj
    linarith [norm_sub_le_norm_add i j]

lemma first_interior {ε : ℝ} (hε : 0 < ε) (side : Bool) (z : Circle)
    (hz : 6 * ε < ‖z‖) : ∃ i j : Circle, i + j = z ∧
      ∀ h : Circle, ‖h‖ ≤ ε / 2 → i + h ∈ FirstI ε side ∧ j - h ∈ FirstJ ε side := by
  cases side
  · refine ⟨0, z, zero_add _, ?_⟩
    intro h hh
    change ‖0 + h‖ ≤ ε ∧ 4 * ε ≤ ‖z - h‖
    simp only [zero_add]
    constructor
    · linarith
    · linarith [norm_sub_norm_le z h]
  · refine ⟨z, 0, add_zero _, ?_⟩
    intro h hh
    change 4 * ε ≤ ‖z + h‖ ∧ ‖0 - h‖ ≤ ε
    simp only [zero_sub, norm_neg]
    constructor
    · linarith [norm_sub_le_norm_add z h]
    · linarith

lemma pow_two_half {a b : ℕ} (h : a < b) :
    2 * (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b := by
  rw [mul_comm, ← pow_succ]
  exact pow_le_pow_right₀ (by norm_num) h

lemma pow_two_pos_diff_inj {a b c d : ℕ} (hab : a < b) (hcd : c < d)
    (h : (2 : ℝ) ^ b - 2 ^ a = 2 ^ d - 2 ^ c) : a = c ∧ b = d := by
  have hbd : b = d := by
    rcases lt_trichotomy b d with hbd | hbd | hbd
    · have h1 := pow_two_half hbd
      have h2 := pow_two_half hcd
      have h3 := pow_pos (by norm_num : (0 : ℝ) < 2) a
      linarith
    · exact hbd
    · have h1 := pow_two_half hbd
      have h2 := pow_two_half hab
      have h3 := pow_pos (by norm_num : (0 : ℝ) < 2) c
      linarith
  have hac : (2 : ℝ) ^ a = 2 ^ c := by rw [hbd] at h; linarith
  refine ⟨?_, hbd⟩
  exact (pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)) hac

lemma pow_two_diff_ne_zero {a b : ℕ} (hab : a ≠ b) :
    (2 : ℝ) ^ b - 2 ^ a ≠ 0 := by
  intro h
  exact hab ((pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)) (sub_eq_zero.mp h)).symm

lemma pow_two_diff_inj {a b c d : ℕ} (hab : a ≠ b) (_hcd : c ≠ d)
    (h : (2 : ℝ) ^ b - 2 ^ a = 2 ^ d - 2 ^ c) : a = c ∧ b = d := by
  rcases lt_or_gt_of_ne hab with hab | hab
  · have hp : (2 : ℝ) ^ a < 2 ^ b := pow_lt_pow_right₀ (by norm_num) hab
    have hcd' : c < d := by
      by_contra hn
      have hle := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_of_not_gt hn)
      linarith
    exact pow_two_pos_diff_inj hab hcd' h
  · have hp : (2 : ℝ) ^ b < 2 ^ a := pow_lt_pow_right₀ (by norm_num) hab
    have hcd' : d < c := by
      by_contra hn
      have hle := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_of_not_gt hn)
      linarith
    have he : (2 : ℝ) ^ a - 2 ^ b = 2 ^ c - 2 ^ d := by linarith
    obtain ⟨hbd, hac⟩ := pow_two_pos_diff_inj hab hcd' he
    exact ⟨hac, hbd⟩

noncomputable def realRoster [Fintype P] (p : P) : ℝ :=
  (2 : ℝ) ^ (Fintype.equivFin P p).val / (16 * 2 ^ Fintype.card P)

omit [DecidableEq P] in
lemma realRoster_range [Fintype P] (p : P) : 0 < realRoster p ∧ realRoster p < 1 / 16 := by
  have hd : (0 : ℝ) < 16 * 2 ^ Fintype.card P := by positivity
  constructor
  · exact div_pos (by positivity) hd
  · rw [realRoster, div_lt_iff₀ hd]
    have hh := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (Fintype.equivFin P p).isLt
    nlinarith

omit [DecidableEq P] in
lemma realRoster_diff_ne_zero [Fintype P] {p q : P} (hpq : p ≠ q) :
    realRoster q - realRoster p ≠ 0 := by
  have hindex : (Fintype.equivFin P p).val ≠ (Fintype.equivFin P q).val := by
    intro h
    exact hpq ((Fintype.equivFin P).injective (Fin.ext h))
  have hraw := pow_two_diff_ne_zero hindex
  dsimp [realRoster]
  rw [← sub_div]
  exact div_ne_zero hraw (by positivity)

omit [DecidableEq P] in
lemma realRoster_diff_inj [Fintype P] {p q r s : P} (hpq : p ≠ q) (hrs : r ≠ s)
    (h : realRoster q - realRoster p = realRoster s - realRoster r) : p = r ∧ q = s := by
  have hindex {p q : P} (hpq : p ≠ q) :
      (Fintype.equivFin P p).val ≠ (Fintype.equivFin P q).val := by
    intro h
    exact hpq ((Fintype.equivFin P).injective (Fin.ext h))
  dsimp [realRoster] at h
  rw [← sub_div, ← sub_div, div_left_inj' (by positivity : (16 * (2 : ℝ) ^ Fintype.card P) ≠ 0)] at h
  obtain ⟨ha, hb⟩ := pow_two_diff_inj (hindex hpq) (hindex hrs) h
  exact ⟨(Fintype.equivFin P).injective (Fin.ext ha), (Fintype.equivFin P).injective (Fin.ext hb)⟩

noncomputable def firstRoster [Fintype P] (p : P) : Circle := (realRoster p : Circle)

omit [DecidableEq P] in
lemma realRoster_diff_range [Fintype P] (p q : P) :
    realRoster q - realRoster p ∈ Set.Ico (-(1 / 8 : ℝ)) (-(1 / 8 : ℝ) + 1) := by
  have hp := realRoster_range p
  have hq := realRoster_range q
  constructor <;> linarith

omit [DecidableEq P] in
lemma firstRoster_diff_ne_zero [Fintype P] {p q : P} (hpq : p ≠ q) :
    firstRoster q - firstRoster p ≠ 0 := by
  intro h
  have he : ((realRoster q - realRoster p : ℝ) : Circle) = ((0 : ℝ) : Circle) := by
    simpa only [AddCircle.coe_sub, AddCircle.coe_zero, firstRoster] using h
  have hz : (0 : ℝ) ∈ Set.Ico (-(1 / 8 : ℝ)) (-(1 / 8 : ℝ) + 1) := by constructor <;> norm_num
  have hr := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ))
    (realRoster_diff_range p q) hz).mp he
  exact realRoster_diff_ne_zero hpq hr

omit [DecidableEq P] in
lemma firstRoster_diff_inj [Fintype P] {p q r s : P} (hpq : p ≠ q) (hrs : r ≠ s)
    (h : firstRoster q - firstRoster p = firstRoster s - firstRoster r) : p = r ∧ q = s := by
  have he : ((realRoster q - realRoster p : ℝ) : Circle) =
      ((realRoster s - realRoster r : ℝ) : Circle) := by
    simpa only [AddCircle.coe_sub, firstRoster] using h
  exact realRoster_diff_inj hpq hrs ((AddCircle.coe_eq_coe_iff_of_mem_Ico
    (p := (1 : ℝ)) (realRoster_diff_range p q) (realRoster_diff_range r s)).mp he)

lemma finite_positive_lower {ι : Type uι} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, r < f i := by
  classical
  have aux (J : Finset ι) : ∃ r : ℝ, 0 < r ∧ ∀ i ∈ J, r < f i := by
    induction J using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i J hi ih =>
        obtain ⟨r, hr, hri⟩ := ih
        refine ⟨min r (f i / 2), lt_min hr (by linarith [hf i]), ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          exact (min_le_right _ _).trans_lt (by linarith [hf i])
        · exact (min_le_left _ _).trans_lt (hri j hj)
  obtain ⟨r, hr, hri⟩ := aux Finset.univ
  exact ⟨r, hr, fun i => hri i (Finset.mem_univ _)⟩

def OffPair (P : Type uP2) := {e : P × P // e.1 ≠ e.2}

noncomputable instance [Fintype P] : Fintype (OffPair P) := by
  classical
  unfold OffPair
  infer_instance

omit [DecidableEq P] in
lemma firstRoster_parameters [Fintype P] :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 100 ∧
      (∀ p q : P, p ≠ q → 16 * ε < ‖firstRoster q - firstRoster p‖) ∧
      (∀ p q r s : P, p ≠ q → r ≠ s → (p, q) ≠ (r, s) →
        16 * ε < ‖(firstRoster q - firstRoster p) - (firstRoster s - firstRoster r)‖) := by
  classical
  let d (e : OffPair P) : Circle := firstRoster e.1.2 - firstRoster e.1.1
  have hd (e : OffPair P) : 0 < ‖d e‖ := norm_pos_iff.mpr (firstRoster_diff_ne_zero e.2)
  obtain ⟨δ, hδ, hδd⟩ := finite_positive_lower (fun e => ‖d e‖) hd
  have hdd (es : {es : OffPair P × OffPair P // es.1 ≠ es.2}) :
      0 < ‖d es.1.1 - d es.1.2‖ := by
    apply norm_pos_iff.mpr
    intro h
    obtain ⟨ha, hb⟩ := firstRoster_diff_inj es.1.1.2 es.1.2.2 (sub_eq_zero.mp h)
    exact es.2 (Subtype.ext (Prod.ext ha hb))
  obtain ⟨δ', hδ', hδd'⟩ := finite_positive_lower
    (fun es : {es : OffPair P × OffPair P // es.1 ≠ es.2} => ‖d es.1.1 - d es.1.2‖) hdd
  let ε := min (1 / 200 : ℝ) (min δ δ') / 32
  have hε : 0 < ε := div_pos (lt_min (by norm_num) (lt_min hδ hδ')) (by norm_num)
  have hε0 : ε ≤ 1 / 200 / 32 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hεδ : 32 * ε ≤ δ := by
    have hh := (min_le_right (1 / 200 : ℝ) (min δ δ')).trans (min_le_left δ δ')
    dsimp [ε]
    linarith
  have hεδ' : 32 * ε ≤ δ' := by
    have hh := (min_le_right (1 / 200 : ℝ) (min δ δ')).trans (min_le_right δ δ')
    dsimp [ε]
    linarith
  refine ⟨ε, hε, by linarith, ?_, ?_⟩
  · intro p q hpq
    have hh := hδd ⟨(p, q), hpq⟩
    change δ < ‖firstRoster q - firstRoster p‖ at hh
    linarith
  · intro p q r s hpq hrs hne
    have he : (⟨(p, q), hpq⟩ : OffPair P) ≠ ⟨(r, s), hrs⟩ :=
      fun h => hne (congrArg Subtype.val h)
    have hh := hδd' ⟨(⟨(p, q), hpq⟩, ⟨(r, s), hrs⟩), he⟩
    change δ' < ‖(firstRoster q - firstRoster p) - (firstRoster s - firstRoster r)‖ at hh
    linarith

lemma norm_difference_perturb (p q p' q' : Circle) :
    ‖(q' - p') - (q - p)‖ ≤ ‖q' - q‖ + ‖p' - p‖ := by
  convert norm_sub_le (q' - q) (p' - p) using 1
  congr 1
  abel

omit [DecidableEq P] in
lemma first_roster_separation {ε η : ℝ} (hε : 0 < ε) (hη : η ≤ ε / 2)
    (v v' : P → Circle) (hv' : ∀ p, ‖v' p - v p‖ < η)
    {p q r s : P} (hsep : 16 * ε < ‖(v q - v p) - (v s - v r)‖) :
    12 * ε < ‖(v' q - v' p) - (v' s - v' r)‖ := by
  have hpq := norm_difference_perturb (v p) (v q) (v' p) (v' q)
  have hrs := norm_difference_perturb (v r) (v s) (v' r) (v' s)
  have hall := norm_difference_perturb (v s - v r) (v q - v p)
    (v' s - v' r) (v' q - v' p)
  have hn := norm_sub_norm_le ((v q - v p) - (v s - v r))
    ((v' q - v' p) - (v' s - v' r))
  rw [norm_sub_rev ((v q - v p) - (v s - v r))] at hn
  linarith [hv' p, hv' q, hv' r, hv' s]

lemma first_obstruction_count [Fintype P] {ε η : ℝ} (hε : 0 < ε) (hη : η ≤ ε / 2)
    (v' : P → Circle) (hv' : ∀ p, ‖v' p - firstRoster p‖ < η)
    (hsep : ∀ p q r s : P, p ≠ q → r ≠ s → (p, q) ≠ (r, s) →
      16 * ε < ‖(firstRoster q - firstRoster p) - (firstRoster s - firstRoster r)‖)
    (a : Circle) :
    (Finset.univ.filter (fun e : P × P => e.1 ≠ e.2 ∧ ‖a + v' e.2 - v' e.1‖ ≤ 6 * ε)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he hf
  by_contra hne
  have hs := first_roster_separation hε hη firstRoster v' hv' (hsep e.1 e.2 f.1 f.2 he.1 hf.1 hne)
  have hn := norm_sub_le (a + v' e.2 - v' e.1) (a + v' f.2 - v' f.1)
  have heq : (a + v' e.2 - v' e.1) - (a + v' f.2 - v' f.1) =
      (v' e.2 - v' e.1) - (v' f.2 - v' f.1) := by abel
  rw [heq] at hn
  linarith [he.2, hf.2]

def Forest (P : Type uP3) [DecidableEq P] :=
  {f : Fin 400 → P × P // FreshPairs (List.ofFn f)}

noncomputable instance [Fintype P] : Fintype (Forest P) := by
  classical
  unfold Forest
  infer_instance

def Batch (P : Type uP4) [DecidableEq P] := Option (Forest P × Bool)

noncomputable instance [Fintype P] : Fintype (Batch P) := by
  unfold Batch
  infer_instance

lemma batch_card [Fintype P] : Fintype.card (Batch P) = 2 * Fintype.card (Forest P) + 1 := by
  simp only [Batch, Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
  omega

noncomputable def forestRoster (f : Forest P) : P → Circle :=
  Classical.choose (realize_sequence f.1 f.2 (fun j => (((j : ℝ) / 400 : ℝ) : Circle)))

lemma forestRoster_spec (f : Forest P) (j : Fin 400) :
    forestRoster f (f.1 j).2 - forestRoster f (f.1 j).1 = (((j : ℝ) / 400 : ℝ) : Circle) :=
  Classical.choose_spec (realize_sequence f.1 f.2 (fun j => (((j : ℝ) / 400 : ℝ) : Circle))) j

noncomputable def batchRoster (p : P) : Batch P → Circle
  | none => 0
  | some (f, _) => forestRoster f p

lemma batch_forest_hit {η : ℝ} (hη : η ≤ 1 / 1600)
    (v' : P → Batch P → Circle) (hv' : ∀ p c, ‖v' p c - batchRoster p c‖ < η)
    (a : Batch P → Circle) (f : Forest P) :
    ∃ j : Fin 400, ∃ c : Batch P,
      ‖a c + v' (f.1 j).2 c - v' (f.1 j).1 c‖ ≤ 1 / 200 := by
  let c : Batch P := some (f, false)
  obtain ⟨j, hj⟩ := grid_near 400 (by norm_num) (a c)
  have heq : batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c =
      (((j : ℝ) / 400 : ℝ) : Circle) := forestRoster_spec f j
  have hold : ‖a c + batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c‖ ≤ 1 / 800 := by
    rw [add_sub_assoc, heq]
    norm_num at hj ⊢
    exact hj
  have hh := norm_difference_perturb
    (batchRoster (f.1 j).1 c) (batchRoster (f.1 j).2 c)
    (v' (f.1 j).1 c) (v' (f.1 j).2 c)
  have hn := norm_add_le (a c + batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c)
    ((v' (f.1 j).2 c - v' (f.1 j).1 c) -
      (batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c))
  have halg : (a c + batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c) +
      ((v' (f.1 j).2 c - v' (f.1 j).1 c) -
        (batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c)) =
      a c + v' (f.1 j).2 c - v' (f.1 j).1 c := by abel
  rw [halg] at hn
  refine ⟨j, c, ?_⟩
  linarith [hv' (f.1 j).1 c, hv' (f.1 j).2 c]

lemma batch_obstruction_count [Fintype P] {η : ℝ} (hη : η ≤ 1 / 1600)
    (v' : P → Batch P → Circle) (hv' : ∀ p c, ‖v' p c - batchRoster p c‖ < η)
    (a : Batch P → Circle) :
    (Finset.univ.filter (fun e : P × P => e.1 ≠ e.2 ∧
      ∀ c : Batch P, 1 / 200 < ‖a c + v' e.2 c - v' e.1 c‖)).card ≤ 4 * 400 ^ 2 := by
  classical
  let B := Finset.univ.filter (fun e : P × P => e.1 ≠ e.2 ∧
    ∀ c : Batch P, 1 / 200 < ‖a c + v' e.2 c - v' e.1 c‖)
  apply count_of_no_forest B
  · intro e he
    exact (Finset.mem_filter.mp he).2.1
  · intro f hf
    obtain ⟨j, c, hj⟩ := batch_forest_hit hη v' hv' a ⟨f, hf⟩
    refine ⟨j, fun hm => ?_⟩
    have hbad := (Finset.mem_filter.mp hm).2.2 c
    linarith

def BlockI {C : Type uC6} [Fintype C] (s : ℕ) (t : Bool) (x : C → Circle) : Prop :=
  if t then x ∈ TypeTwo s else ∀ c, x c ∈ Near centersI (1 / 16)

def BlockJ {C : Type uC7} [Fintype C] (s : ℕ) (t : Bool) (x : C → Circle) : Prop :=
  if t then x ∈ TypeTwo s else ∀ c, x c ∈ Near centersJ (1 / 16)

lemma block_reversal_false {C : Type uC8} [Fintype C] (s : ℕ)
    (hC : Fintype.card C = 2 * s + 1) {t u : Bool} (htu : t ≠ u)
    {i j i' j' : C → Circle} (hi : BlockI s t i) (hj : BlockJ s t j)
    (hi' : BlockI s u i') (hj' : BlockJ s u j') (he : i + j' = i' + j) : False := by
  have hd (c : C) : i c - j c = i' c - j' c := by
    have hc := congrFun he c
    change i c + j' c = i' c + j c at hc
    calc
      i c - j c = (i c + j' c) - j c - j' c := by abel
      _ = (i' c + j c) - j c - j' c := by rw [hc]
      _ = i' c - j' c := by abel
  cases t <;> cases u
  · exact htu rfl
  · obtain ⟨c, hc⟩ := type_two_difference s hC hi' hj'
    have hs := type_one_difference (hi c) (hj c)
    rw [hd c] at hs
    linarith
  · obtain ⟨c, hc⟩ := type_two_difference s hC hi hj
    have hs := type_one_difference (hi' c) (hj' c)
    rw [← hd c] at hs
    linarith
  · exact htu rfl

lemma block_interior {C : Type uC9} [Fintype C] (s : ℕ)
    (hC : Fintype.card C = 2 * s + 1) (t : Bool) (z : C → Circle)
    (hz : ∃ c, ‖z c‖ ≤ 1 / 200) {ρ : ℝ} (hρ1 : ρ ≤ 1 / 96) (hρ2 : ρ ≤ 1 / 400) :
    ∃ i j : C → Circle, i + j = z ∧ ∀ h : C → Circle,
      (∀ c, ‖h c‖ ≤ ρ) → BlockI s t (i + h) ∧ BlockJ s t (j - h) := by
  classical
  cases t
  · choose i j hij hp using (fun c => type_one_interior (z c))
    refine ⟨i, j, funext hij, ?_⟩
    intro h hh
    exact ⟨fun c => (hp c (h c) ((hh c).trans hρ1)).1,
      fun c => (hp c (h c) ((hh c).trans hρ1)).2⟩
  · obtain ⟨i, j, hij, hp⟩ := type_two_interior s hC z hz
    exact ⟨i, j, hij, fun h hh => hp h (fun c => (hh c).trans hρ2)⟩

def ClockI {T : Type uT} {A : Type uA3} {B : Type uB} {C : Type uC10} [Fintype C] (ε : ℝ) (s : ℕ)
    (p : A → T → Bool) (t : B → T → Bool) (α : T) : Set ((A ⊕ (B × C)) → Circle) :=
  {x | (∀ a, x (Sum.inl a) ∈ FirstI ε (p a α)) ∧
    ∀ b, BlockI s (t b α) (fun c => x (Sum.inr (b, c)))}

def ClockJ {T : Type uT2} {A : Type uA4} {B : Type uB2} {C : Type uC11} [Fintype C] (ε : ℝ) (s : ℕ)
    (p : A → T → Bool) (t : B → T → Bool) (α : T) : Set ((A ⊕ (B × C)) → Circle) :=
  {x | (∀ a, x (Sum.inl a) ∈ FirstJ ε (p a α)) ∧
    ∀ b, BlockJ s (t b α) (fun c => x (Sum.inr (b, c)))}

def Obstruction {A : Type uA5} {B : Type uB3} {C : Type uC12} (ε : ℝ) : Set ((A ⊕ (B × C)) → Circle) :=
  {z | (∃ a, ‖z (Sum.inl a)‖ ≤ 6 * ε) ∨
    (∃ b, ∀ c, 1 / 200 < ‖z (Sum.inr (b, c))‖)}

def Edge {T : Type uT3} {A : Type uA6} {B : Type uB4} {C : Type uC13} [Fintype C] (ε : ℝ) (s : ℕ)
    (p : A → T → Bool) (t : B → T → Bool) (z : (A ⊕ (B × C)) → Circle) (α lam : T) : Prop :=
  ∃ i ∈ ClockI ε s p t α, ∃ j ∈ ClockJ ε s p t lam, i + j = z

lemma unequal_edge_unique {T : Type uT4} {A : Type uA7} {B : Type uB5} {C : Type uC14} [DecidableEq T] [Fintype C]
    {ε : ℝ} (hε : 0 < ε) (s : ℕ) (hC : Fintype.card C = 2 * s + 1)
    (p : A → T → Bool) (t : B → T → Bool)
    (hp : ∀ α lam γ ν, TagPartitions.Feasible α lam γ ν →
      ∃ a, TagPartitions.Satisfies α lam γ ν (p a))
    (ht : ∀ α lam, α ≠ lam → ∃ b, t b α ≠ t b lam)
    {z : (A ⊕ (B × C)) → Circle} {α lam γ ν : T} (hαlam : α ≠ lam)
    (hα : Edge ε s p t z α lam) (hγ : Edge ε s p t z γ ν) : γ = α ∧ ν = lam := by
  obtain ⟨i, hi, j, hj, hij⟩ := hα
  obtain ⟨i', hi', j', hj', hij'⟩ := hγ
  have hpair : ({α, lam} : Finset T) = {γ, ν} := by
    by_contra hn
    obtain ⟨a, ha, hl, hsame⟩ := hp α lam γ ν ⟨hαlam, hn⟩
    have hia := hi.1 a
    have hja := hj.1 a
    rw [ha] at hia
    rw [hl] at hja
    have hlo := first_left_right hia hja
    have hia' := hi'.1 a
    have hja' := hj'.1 a
    rw [← hsame] at hja'
    have hhi := first_same_side (p a γ) hia' hja'
    have he := congrFun (hij.trans hij'.symm) (Sum.inl a)
    change i (Sum.inl a) + j (Sum.inl a) = i' (Sum.inl a) + j' (Sum.inl a) at he
    rw [he] at hlo
    linarith
  have ha : α = γ ∨ α = ν := by
    have hm : α ∈ ({γ, ν} : Finset T) := hpair ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hl : lam = γ ∨ lam = ν := by
    have hm : lam ∈ ({γ, ν} : Finset T) := hpair ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hor : (γ = α ∧ ν = lam) ∨ (γ = lam ∧ ν = α) := by aesop
  rcases hor with h | ⟨hγ, hν⟩
  · exact h
  · subst γ
    subst ν
    obtain ⟨b, hb⟩ := ht α lam hαlam
    exfalso
    apply block_reversal_false s hC hb (hi.2 b) (hj'.2 b) (hi'.2 b) (hj.2 b)
    funext c
    exact congrFun (hij.trans hij'.symm) (Sum.inr (b, c))

lemma graph_alternative {T : Type uT5} {A : Type uA8} {B : Type uB6} {C : Type uC15} [DecidableEq T] [Fintype C]
    {ε : ℝ} (hε : 0 < ε) (s : ℕ) (hC : Fintype.card C = 2 * s + 1)
    (p : A → T → Bool) (t : B → T → Bool)
    (hp : ∀ α lam γ ν, TagPartitions.Feasible α lam γ ν →
      ∃ a, TagPartitions.Satisfies α lam γ ν (p a))
    (ht : ∀ α lam, α ≠ lam → ∃ b, t b α ≠ t b lam)
    (z : (A ⊕ (B × C)) → Circle) :
    (∀ α lam, Edge ε s p t z α lam → α = lam) ∨
      ∃ α lam, α ≠ lam ∧ Edge ε s p t z α lam ∧
        ∀ γ ν, Edge ε s p t z γ ν → γ = α ∧ ν = lam := by
  classical
  by_cases h : ∃ α lam, α ≠ lam ∧ Edge ε s p t z α lam
  · obtain ⟨α, lam, hne, he⟩ := h
    exact Or.inr ⟨α, lam, hne, he, fun γ ν h' => unequal_edge_unique hε s hC p t hp ht hne he h'⟩
  · left
    intro α lam he
    by_contra hn
    exact h ⟨α, lam, hn, he⟩

lemma clock_interior {T : Type uT6} {A : Type uA9} {B : Type uB7} {C : Type uC16} [Fintype C]
    {ε ρ : ℝ} (hε : 0 < ε) (hρ0 : ρ ≤ ε / 2) (hρ1 : ρ ≤ 1 / 96) (hρ2 : ρ ≤ 1 / 400)
    (s : ℕ) (hC : Fintype.card C = 2 * s + 1)
    (p : A → T → Bool) (t : B → T → Bool) (α : T)
    (z : (A ⊕ (B × C)) → Circle) (hz : z ∉ Obstruction ε) :
    ∃ i j : (A ⊕ (B × C)) → Circle, i + j = z ∧
      ∀ h : (A ⊕ (B × C)) → Circle, (∀ c, ‖h c‖ ≤ ρ) →
        i + h ∈ ClockI ε s p t α ∧ j - h ∈ ClockJ ε s p t α := by
  classical
  have hfirst (a : A) : 6 * ε < ‖z (Sum.inl a)‖ := by
    by_contra hn
    exact hz (Or.inl ⟨a, le_of_not_gt hn⟩)
  have hbatch (b : B) : ∃ c, ‖z (Sum.inr (b, c))‖ ≤ 1 / 200 := by
    by_contra hn
    push Not at hn
    exact hz (Or.inr ⟨b, hn⟩)
  choose iA jA hsA hpA using (fun a => first_interior hε (p a α) (z (Sum.inl a)) (hfirst a))
  choose iB jB hsB hpB using (fun b => block_interior s hC (t b α)
    (fun c => z (Sum.inr (b, c))) (hbatch b) hρ1 hρ2)
  let i : (A ⊕ (B × C)) → Circle := Sum.elim iA (fun bc => iB bc.1 bc.2)
  let j : (A ⊕ (B × C)) → Circle := Sum.elim jA (fun bc => jB bc.1 bc.2)
  refine ⟨i, j, ?_, ?_⟩
  · funext c
    cases c with
    | inl a => exact hsA a
    | inr bc => exact congrFun (hsB bc.1) bc.2
  · intro h hh
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro a
      exact (hpA a (h (Sum.inl a)) ((hh _).trans hρ0)).1
    · intro b
      exact (hpB b (fun c => h (Sum.inr (b, c))) (fun c => hh _)).1
    · intro a
      exact (hpA a (h (Sum.inl a)) ((hh _).trans hρ0)).2
    · intro b
      exact (hpB b (fun c => h (Sum.inr (b, c))) (fun c => hh _)).2

lemma clock_ball {T : Type uT7} {A : Type uA10} {B : Type uB8} {C : Type uC17} [Fintype A] [Fintype B] [Fintype C]
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (hρ0 : ρ ≤ ε / 2) (hρ1 : ρ ≤ 1 / 96) (hρ2 : ρ ≤ 1 / 400)
    (s : ℕ) (hC : Fintype.card C = 2 * s + 1)
    (p : A → T → Bool) (t : B → T → Bool) (α : T)
    (z : (A ⊕ (B × C)) → Circle) (hz : z ∉ Obstruction ε) :
    ∃ i : (A ⊕ (B × C)) → Circle, ∀ x, dist x i < ρ →
      x ∈ ClockI ε s p t α ∧ z - x ∈ ClockJ ε s p t α := by
  obtain ⟨i, j, hij, hp⟩ := clock_interior hε hρ0 hρ1 hρ2 s hC p t α z hz
  refine ⟨i, ?_⟩
  intro x hx
  have hnorm (c) : ‖(x - i) c‖ ≤ ρ := by
    exact le_of_lt (by simpa only [Pi.sub_apply, dist_eq_norm] using (dist_pi_lt_iff hρ).mp hx c)
  obtain ⟨hi, hj⟩ := hp (x - i) hnorm
  have hi' : i + (x - i) = x := by abel
  have hj' : j - (x - i) = z - x := by rw [← hij]; abel
  exact ⟨hi' ▸ hi, hj' ▸ hj⟩

noncomputable def roster [Fintype P] {A : Type uA11} {B : Type uB9} (p : P) : (A ⊕ (B × Batch P)) → Circle :=
  Sum.elim (fun _ => firstRoster p) (fun bc => batchRoster p bc.2)

noncomputable def obstructionPairs [Fintype P] {A : Type uA12} {B : Type uB10} {C : Type uC18} (ε : ℝ)
    (a : (A ⊕ (B × C)) → Circle) (v : P → (A ⊕ (B × C)) → Circle) : Finset (P × P) := by
  classical
  exact Finset.univ.filter (fun e => e.1 ≠ e.2 ∧ a + v e.2 - v e.1 ∈ Obstruction ε)

lemma roster_estimate [Fintype P] {A : Type uA13} {B : Type uB11} [Fintype A] [Fintype B]
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hηε : η ≤ ε / 2) (hη0 : η ≤ 1 / 1600)
    (hsep : ∀ p q r s : P, p ≠ q → r ≠ s → (p, q) ≠ (r, s) →
      16 * ε < ‖(firstRoster q - firstRoster p) - (firstRoster s - firstRoster r)‖)
    (v' : P → (A ⊕ (B × Batch P)) → Circle)
    (hv' : ∀ p, dist (v' p) (roster p) < η)
    (a : (A ⊕ (B × Batch P)) → Circle) :
    (obstructionPairs ε a v').card ≤
        Fintype.card A + 4 * 400 ^ 2 * Fintype.card B := by
  classical
  unfold obstructionPairs
  have hnorm (p : P) (c : A ⊕ (B × Batch P)) :
      ‖v' p c - roster p c‖ < η := by
    simpa only [dist_eq_norm] using (dist_pi_lt_iff hη).mp (hv' p) c
  let EA (c : A) : Finset (P × P) := Finset.univ.filter (fun e => e.1 ≠ e.2 ∧
    ‖a (Sum.inl c) + v' e.2 (Sum.inl c) - v' e.1 (Sum.inl c)‖ ≤ 6 * ε)
  let EB (b : B) : Finset (P × P) := Finset.univ.filter (fun e => e.1 ≠ e.2 ∧
    ∀ c : Batch P, 1 / 200 < ‖a (Sum.inr (b, c)) + v' e.2 (Sum.inr (b, c)) - v' e.1 (Sum.inr (b, c))‖)
  have hEA (c : A) : (EA c).card ≤ 1 := first_obstruction_count hε hηε
    (fun p => v' p (Sum.inl c)) (fun p => hnorm p (Sum.inl c)) hsep (a (Sum.inl c))
  have hEB (b : B) : (EB b).card ≤ 4 * 400 ^ 2 := batch_obstruction_count hη0
    (fun p c => v' p (Sum.inr (b, c))) (fun p c => hnorm p (Sum.inr (b, c)))
    (fun c => a (Sum.inr (b, c)))
  have hcover : Finset.univ.filter (fun e : P × P => e.1 ≠ e.2 ∧
      a + v' e.2 - v' e.1 ∈ Obstruction ε) ⊆
      Finset.univ.biUnion EA ∪ Finset.univ.biUnion EB := by
    intro e he
    obtain ⟨hne, hob⟩ := (Finset.mem_filter.mp he).2
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    rcases hob with ⟨c, hc⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hc⟩⟩
    · exact Or.inr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hb⟩⟩
  have ha := Finset.card_biUnion_le_card_mul Finset.univ EA 1 (fun c _ => hEA c)
  have hb := Finset.card_biUnion_le_card_mul Finset.univ EB (4 * 400 ^ 2) (fun b _ => hEB b)
  have hu := Finset.card_union_le (Finset.univ.biUnion EA) (Finset.univ.biUnion EB)
  have hd := Finset.card_le_card hcover
  simp only [Finset.card_univ, mul_one] at ha hb
  omega

noncomputable def badPairs {P : Type uP5} {C : Type uC19} [Fintype P]
    (W : Set (C → Circle)) (a : C → Circle) (v : P → C → Circle) : Finset (P × P) := by
  classical
  exact Finset.univ.filter (fun e => e.1 ≠ e.2 ∧ a + v e.2 - v e.1 ∈ W)

structure Specification (T : Type uT8) (P : Type uP6) (C : Type uC20) [Fintype T] [Fintype P] [Fintype C] where
  I : T → Set (C → Circle)
  J : T → Set (C → Circle)
  W : Set (C → Circle)
  v : P → C → Circle
  ρ : ℝ
  η : ℝ
  radius_pos : 0 < ρ
  tolerance_pos : 0 < η
  graph : ∀ z : C → Circle,
    (∀ α lam, (∃ i ∈ I α, ∃ j ∈ J lam, i + j = z) → α = lam) ∨
    ∃ α lam, α ≠ lam ∧ (∃ i ∈ I α, ∃ j ∈ J lam, i + j = z) ∧
      ∀ γ ν, (∃ i ∈ I γ, ∃ j ∈ J ν, i + j = z) → γ = α ∧ ν = lam
  interior : ∀ z : C → Circle, z ∉ W → ∀ α,
    ∃ i : C → Circle, ∀ x, dist x i < ρ → x ∈ I α ∧ z - x ∈ J α
  count : ∀ v' : P → C → Circle, (∀ p, dist (v' p) (v p) < η) →
    ∀ a : C → Circle, ((badPairs W a v').card : ℝ) ≤
      10000000 * Real.log (2 * Fintype.card T)

abbrev Coordinates (T : Type uT9) (P : Type uP7) [Fintype T] [DecidableEq P] :=
  Fin (TagPartitions.repetitions (Fintype.card T)) ⊕
    (Fin (TagPartitions.typeCount (Fintype.card T)) × Batch P)

theorem exists_clock (T : Type uT10) (P : Type uP8) [Fintype T] [Nonempty T] [Fintype P] [DecidableEq P] :
    Nonempty (Specification T P (Coordinates T P)) := by
  classical
  obtain ⟨p, hp⟩ := TagPartitions.exists_partitions (T := T)
  obtain ⟨t, ht⟩ := TagPartitions.exists_types (T := T)
  obtain ⟨ε, hε, _, _, hsep⟩ := firstRoster_parameters (P := P)
  let η := min (ε / 2) (1 / 1600 : ℝ)
  let ρ := min (ε / 2) (min (1 / 96 : ℝ) (1 / 400))
  have hη : 0 < η := lt_min (half_pos hε) (by norm_num)
  have hρ : 0 < ρ := lt_min (half_pos hε) (lt_min (by norm_num) (by norm_num))
  refine ⟨{
    I := ClockI ε (Fintype.card (Forest P)) p t
    J := ClockJ ε (Fintype.card (Forest P)) p t
    W := Obstruction ε
    v := roster
    ρ := ρ
    η := η
    radius_pos := hρ
    tolerance_pos := hη
    graph := ?_
    interior := ?_
    count := ?_ }⟩
  · exact graph_alternative hε _ (batch_card (P := P)) p t hp ht
  · intro z hz α
    exact clock_ball hε hρ (min_le_left _ _)
      ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _))
      _ (batch_card (P := P)) p t α z hz
  · intro v' hv' a
    have hb := roster_estimate hε hη (min_le_left _ _) (min_le_right _ _) hsep v' hv' a
    have hbR : ((badPairs (Obstruction ε) a v').card : ℝ) ≤
        ((TagPartitions.repetitions (Fintype.card T) +
          4 * 400 ^ 2 * TagPartitions.typeCount (Fintype.card T) : ℕ) : ℝ) := by
      have hb' : (badPairs (Obstruction ε) a v').card ≤
          TagPartitions.repetitions (Fintype.card T) +
            4 * 400 ^ 2 * TagPartitions.typeCount (Fintype.card T) := by
        have he : badPairs (Obstruction ε) a v' = obstructionPairs ε a v' := by
          ext e
          simp [badPairs, obstructionPairs]
        rw [he]
        simpa only [Fintype.card_fin] using hb
      exact_mod_cast hb'
    exact hbR.trans (TagPartitions.total_count_bound Fintype.card_pos)

lemma Specification.diagonal {T : Type uT11} {P : Type uP9} {C : Type uC21} [Fintype T] [Fintype P] [Fintype C]
    (S : Specification T P C) (z : C → Circle) (hz : z ∉ S.W) :
    ∀ α lam, (∃ i ∈ S.I α, ∃ j ∈ S.J lam, i + j = z) ↔ α = lam := by
  intro α lam
  have hdiag (a : T) : ∃ i ∈ S.I a, ∃ j ∈ S.J a, i + j = z := by
    obtain ⟨i, hi⟩ := S.interior z hz a
    obtain ⟨hI, hJ⟩ := hi i (by simpa using S.radius_pos)
    exact ⟨i, hI, z - i, hJ, by abel⟩
  constructor
  · intro he
    rcases S.graph z with h | ⟨a, l, hne, _, hu⟩
    · exact h α lam he
    · obtain ⟨ha, hl⟩ := hu a a (hdiag a)
      exact False.elim (hne hl)
  · rintro rfl
    exact hdiag α

end RobustClock

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace LocalMarkers

variable {Alphabet : Type uAlphabet} {K d : ℕ}

def Period (v : Fin K → Alphabet) (a : ℕ) : Prop :=
  ∀ i j : Fin K, i.val + a = j.val → v i = v j

def Aperiodic (d : ℕ) (v : Fin K → Alphabet) : Prop :=
  ∀ a, 0 < a → a < d → ¬ Period v a

def Occurs (w : ℤ → Alphabet) (v : Fin K → Alphabet) (x : ℤ) : Prop :=
  ∀ i : Fin K, w (x + i.val) = v i

def markers (d : ℕ) (w : ℤ → Alphabet) : List (Fin K → Alphabet) → Set ℤ
  | [] => ∅
  | v :: vs => markers d w vs ∪
      {x | Occurs w v x ∧ ∀ y ∈ markers d w vs, (d : ℤ) ≤ |x - y|}

lemma overlap_period {w : ℤ → Alphabet} {v : Fin K → Alphabet} {x y : ℤ}
    (hx : Occurs w v x) (hy : Occurs w v y) (hxy : x < y) :
    Period v (y - x).toNat := by
  intro i j hij
  have hn : ((y - x).toNat : ℤ) = y - x := Int.toNat_of_nonneg (by omega)
  have he : x + j.val = y + i.val := by omega
  rw [← hx j, he, hy i]

lemma occurrence_separated {w : ℤ → Alphabet} {v : Fin K → Alphabet} (hv : Aperiodic d v)
    {x y : ℤ} (hx : Occurs w v x) (hy : Occurs w v y) (hne : x ≠ y) :
    (d : ℤ) ≤ |x - y| := by
  by_contra hn
  have hsmall : |x - y| < (d : ℤ) := lt_of_not_ge hn
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have hp := overlap_period hx hy hxy
    have hcast : ((y - x).toNat : ℤ) = y - x := Int.toNat_of_nonneg (by omega)
    have habs : |x - y| = y - x := abs_of_neg (by omega) |>.trans (by omega)
    exact hv _ (by omega) (by omega) hp
  · have hp := overlap_period hy hx hyx
    have hcast : ((x - y).toNat : ℤ) = x - y := Int.toNat_of_nonneg (by omega)
    have habs : |x - y| = x - y := abs_of_pos (by omega)
    exact hv _ (by omega) (by omega) hp

lemma separated (vs : List (Fin K → Alphabet)) (hv : ∀ v ∈ vs, Aperiodic d v)
    (w : ℤ → Alphabet) : ∀ x ∈ markers d w vs, ∀ y ∈ markers d w vs,
      x ≠ y → (d : ℤ) ≤ |x - y| := by
  induction vs with
  | nil => simp [markers]
  | cons v vs ih =>
    have hi := ih (fun u hu => hv u (List.mem_cons_of_mem _ hu))
    intro x hx y hy hne
    rcases hx with hx | ⟨hx, hxold⟩ <;> rcases hy with hy | ⟨hy, hyold⟩
    · exact hi x hx y hy hne
    · simpa only [abs_sub_comm] using hyold x hx
    · exact hxold y hy
    · exact occurrence_separated (hv v (List.mem_cons_self)) hx hy hne

lemma occurrence_near (hd : 0 < d) (vs : List (Fin K → Alphabet)) (w : ℤ → Alphabet)
    {v : Fin K → Alphabet} (hv : v ∈ vs) {x : ℤ} (hx : Occurs w v x) :
    ∃ y ∈ markers d w vs, |x - y| < (d : ℤ) := by
  induction vs with
  | nil => simp at hv
  | cons u vs ih =>
    classical
    rcases List.mem_cons.mp hv with rfl | hv
    · by_cases h : ∃ y ∈ markers d w vs, |x - y| < (d : ℤ)
      · obtain ⟨y, hy, hdist⟩ := h
        exact ⟨y, Or.inl hy, hdist⟩
      · refine ⟨x, Or.inr ⟨hx, ?_⟩, ?_⟩
        · intro y hy
          exact le_of_not_gt (fun hlt => h ⟨y, hy, hlt⟩)
        · simpa using hd
    · obtain ⟨y, hy, hdist⟩ := ih hv
      exact ⟨y, Or.inl hy, hdist⟩

def radius (d K : ℕ) (n : ℕ) : ℤ := (K : ℤ) + n * ((d : ℤ) - 1)

lemma radius_ge (hd : 0 < d) (n : ℕ) : (K : ℤ) ≤ radius d K n := by
  have hm : 0 ≤ (n : ℤ) * ((d : ℤ) - 1) := mul_nonneg (by omega) (by omega)
  unfold radius
  omega

lemma locality (hd : 0 < d) (hK : 0 < K) (vs : List (Fin K → Alphabet)) (w w' : ℤ → Alphabet)
    (x : ℤ) (hw : ∀ i, x - radius d K vs.length ≤ i →
      i < x + radius d K vs.length → w i = w' i) :
    x ∈ markers d w vs ↔ x ∈ markers d w' vs := by
  induction vs generalizing x with
  | nil => simp [markers]
  | cons v vs ih =>
    have hr : radius d K (v :: vs).length = radius d K vs.length + (d : ℤ) - 1 := by
      simp only [radius, List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    have hk := radius_ge (K := K) hd vs.length
    have hold (y : ℤ) (hy : |x - y| < (d : ℤ)) :
        y ∈ markers d w vs ↔ y ∈ markers d w' vs := by
      apply ih
      intro i hi hi'
      have hxy := abs_lt.mp hy
      apply hw i <;> rw [hr] <;> omega
    have hxold : x ∈ markers d w vs ↔ x ∈ markers d w' vs :=
      hold x (by simpa using hd)
    have hoc : Occurs w v x ↔ Occurs w' v x := by
      apply forall_congr'
      intro i
      have he := hw (x + i.val) (by rw [hr]; omega) (by rw [hr]; omega)
      rw [he]
    have hnear : (∀ y ∈ markers d w vs, (d : ℤ) ≤ |x - y|) ↔
        (∀ y ∈ markers d w' vs, (d : ℤ) ≤ |x - y|) := by
      constructor <;> intro h y hy <;> by_contra hn
      · exact hn (h y ((hold y (lt_of_not_ge hn)).mpr hy))
      · exact hn (h y ((hold y (lt_of_not_ge hn)).mp hy))
    exact or_congr hxold (and_congr hoc hnear)

lemma translate (vs : List (Fin K → Alphabet)) (w : ℤ → Alphabet) (a x : ℤ) :
    x ∈ markers d (fun i => w (i + a)) vs ↔ x + a ∈ markers d w vs := by
  induction vs generalizing x with
  | nil => simp [markers]
  | cons v vs ih =>
    have hoc : Occurs (fun i => w (i + a)) v x ↔ Occurs w v (x + a) := by
      unfold Occurs
      apply forall_congr'
      intro i
      have he : x + i.val + a = x + a + i.val := by omega
      dsimp only
      rw [he]
    have hn : (∀ y ∈ markers d (fun i => w (i + a)) vs, (d : ℤ) ≤ |x - y|) ↔
        (∀ y ∈ markers d w vs, (d : ℤ) ≤ |x + a - y|) := by
      constructor
      · intro h y hy
        have he : x - (y - a) = x + a - y := by omega
        exact he ▸ h (y - a) ((ih (y - a)).mpr (by simpa using hy))
      · intro h y hy
        have he : x + a - (y + a) = x - y := by omega
        exact he ▸ h (y + a) ((ih y).mp hy)
    exact or_congr (ih x) (and_congr hoc hn)

noncomputable def priorityList [Fintype Alphabet] (d K : ℕ) : List (Fin K → Alphabet) := by
  classical
  exact (Finset.univ.filter (Aperiodic d)).toList

lemma mem_priorityList [Fintype Alphabet] (v : Fin K → Alphabet) :
    v ∈ priorityList d K ↔ Aperiodic d v := by
  classical
  simp [priorityList]

theorem exists_markers [Fintype Alphabet] (hd : 2 ≤ d) (hK : 3 * d ^ 2 < K) :
    ∃ r : ℤ, (K : ℤ) ≤ r ∧ ∃ rule : (ℤ → Alphabet) → Set ℤ,
      (∀ w x, x ∈ rule w → ∀ y, y ∈ rule w → x ≠ y → (d : ℤ) ≤ |x - y|) ∧
      (∀ w w' x, (∀ i, x - r ≤ i → i < x + r → w i = w' i) →
        (x ∈ rule w ↔ x ∈ rule w')) ∧
      (∀ w a x, x ∈ rule (fun i => w (i + a)) ↔ x + a ∈ rule w) ∧
      (∀ w (z : ℤ), (∀ x : ℤ, z - d ≤ x → x ≤ z + d → x ∉ rule w) →
        ∃ a : ℕ, 0 < a ∧ a < d ∧ Period (fun i : Fin K => w (z + i.val)) a) := by
  classical
  let vs := priorityList (Alphabet := Alphabet) d K
  have hd0 : 0 < d := by omega
  have hK0 : 0 < K := by omega
  refine ⟨radius d K vs.length, radius_ge hd0 _, (fun w => markers d w vs), ?_, ?_, ?_, ?_⟩
  · exact fun w => separated vs (fun v hv => mem_priorityList v |>.mp hv) w
  · exact fun w w' x hw => locality hd0 hK0 vs w w' x hw
  · exact fun w a x => translate vs w a x
  · intro w z hz
    by_contra hn
    have hv : Aperiodic d (fun i : Fin K => w (z + i.val)) := by
      intro a ha had hp
      exact hn ⟨a, ha, had, hp⟩
    obtain ⟨x, hx, hdist⟩ := occurrence_near hd0 vs w
      ((mem_priorityList _).mpr hv) (fun _ => rfl)
    have hb := abs_lt.mp hdist
    exact hz x (by omega) (by omega) hx

end LocalMarkers

namespace LocalMarkers

variable {Alphabet : Type uAlphabet2} {K : ℕ}

lemma periodic_remainder {w : ℤ → Alphabet} {a : ℤ} (hw : Function.Periodic w a)
    (z x : ℤ) : w x = w (z + (x - z) % a) := by
  have he := Int.emod_add_mul_ediv (x - z) a
  have hx : x = z + (x - z) % a + ((x - z) / a) * a := by
    rw [mul_comm] at he
    omega
  calc
    w x = w (z + (x - z) % a + ((x - z) / a) * a) := congrArg w hx
    _ = w (z + (x - z) % a) := hw.int_mul ((x - z) / a) _

lemma periodic_agree {w w' : ℤ → Alphabet} {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hw : Function.Periodic w a)
    (hw' : Function.Periodic w' b) (z : ℤ)
    (he : ∀ i : ℤ, z ≤ i → i < z + a * b → w i = w' i) : w = w' := by
  have hp : Function.Periodic w (a * b) := by simpa [mul_comm] using hw.int_mul b
  have hp' : Function.Periodic w' (a * b) := by simpa using hw'.int_mul a
  funext x
  rw [periodic_remainder hp z x, periodic_remainder hp' z x]
  have h₀ := Int.emod_nonneg (x - z) (ne_of_gt (mul_pos ha hb))
  have h₁ := Int.emod_lt_of_pos (x - z) (mul_pos ha hb)
  exact he _ (by omega) (by omega)

lemma period_mod {v : Fin K → Alphabet} {a : ℕ} (ha : 0 < a) (haK : a ≤ K)
    (hp : Period v a) (i : Fin K) :
    v i = v ⟨i.val % a, (Nat.mod_lt _ ha).trans_le haK⟩ := by
  have aux (n : ℕ) : ∀ hn : n < K,
      v ⟨n, hn⟩ = v ⟨n % a, (Nat.mod_lt _ ha).trans_le haK⟩ := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hna : n < a
      · congr 1
        apply Fin.ext
        exact (Nat.mod_eq_of_lt hna).symm
      · have hle : a ≤ n := Nat.le_of_not_gt hna
        have hsub : n - a < n := Nat.sub_lt (by omega) ha
        have hsubK : n - a < K := hsub.trans hn
        have he := hp ⟨n - a, hsubK⟩ ⟨n, hn⟩ (by simpa using Nat.sub_add_cancel hle)
        have hm : (n - a) % a = n % a := by
          conv_rhs => rw [← Nat.sub_add_cancel hle]
          exact (Nat.add_mod_right (n - a) a).symm
        rw [← he, ih (n - a) hsub hsubK]
        congr 1
        exact Fin.ext hm
  exact aux i.val i.isLt

noncomputable def continuation (v : Fin K → Alphabet) (z : ℤ) (a : ℕ)
    (ha : 0 < a) (haK : a ≤ K) : ℤ → Alphabet := fun x =>
  v ⟨((x - z) % (a : ℤ)).toNat, by
    have h₀ := Int.emod_nonneg (x - z) (by omega : (a : ℤ) ≠ 0)
    have h₁ := Int.emod_lt_of_pos (x - z) (by omega : 0 < (a : ℤ))
    have hcast := Int.toNat_of_nonneg h₀
    omega⟩

lemma continuation_periodic (v : Fin K → Alphabet) (z : ℤ) (a : ℕ)
    (ha : 0 < a) (haK : a ≤ K) :
    Function.Periodic (continuation v z a ha haK) (a : ℤ) := by
  intro x
  unfold continuation
  congr 2
  have he : x + (a : ℤ) - z = (x - z) + a := by omega
  rw [he, Int.add_emod_right]

lemma continuation_agrees {v : Fin K → Alphabet} (z : ℤ) {a : ℕ}
    (ha : 0 < a) (haK : a ≤ K) (hp : Period v a) (i : Fin K) :
    continuation v z a ha haK (z + i.val) = v i := by
  rw [period_mod ha haK hp i]
  unfold continuation
  congr 2
  simp only [add_sub_cancel_left]
  rw [← Int.natCast_emod, Int.toNat_natCast]

lemma exists_continuation {v : Fin K → Alphabet} (z : ℤ) {a : ℕ}
    (ha : 0 < a) (haK : a ≤ K) (hp : Period v a) :
    ∃ w : ℤ → Alphabet, Function.Periodic w (a : ℤ) ∧ Occurs w v z :=
  ⟨continuation v z a ha haK, continuation_periodic v z a ha haK,
    continuation_agrees z ha haK hp⟩

lemma continuation_unique {d : ℕ} (hd : 2 ≤ d) (hK : d ^ 2 ≤ K)
    {v : Fin K → Alphabet} {z : ℤ} {w w' : ℤ → Alphabet}
    {a b : ℕ} (ha : 0 < a) (had : a < d) (hb : 0 < b) (hbd : b < d)
    (hw : Function.Periodic w (a : ℤ)) (hw' : Function.Periodic w' (b : ℤ))
    (he : Occurs w v z) (he' : Occurs w' v z) : w = w' := by
  have hab : a * b ≤ K := by nlinarith
  apply periodic_agree (by exact_mod_cast ha) (by exact_mod_cast hb) hw hw' z
  intro i hi hi'
  have habZ : (a : ℤ) * b ≤ K := by exact_mod_cast hab
  have hn : ((i - z).toNat : ℤ) = i - z := Int.toNat_of_nonneg (by omega)
  let j : Fin K := ⟨(i - z).toNat, by omega⟩
  have hj : z + (j.val : ℤ) = i := by dsimp [j]; omega
  rw [← hj, he j, he' j]

end LocalMarkers

namespace FiniteMonoidPeriod

variable {M : Type uM} [Monoid M]

lemma pow_add_of_repeat (c : M) {i v k : ℕ} (h : c ^ (i + v) = c ^ i) (hik : i ≤ k) :
    c ^ (k + v) = c ^ k := by
  have hk : k + v = (i + v) + (k - i) := by omega
  rw [hk, pow_add, h, ← pow_add, Nat.add_sub_of_le hik]

lemma pow_add_multiple (c : M) {i v k : ℕ} (h : c ^ (i + v) = c ^ i) (hik : i ≤ k)
    (q : ℕ) : c ^ (k + q * v) = c ^ k := by
  induction q with
  | zero => simp
  | succ q ih =>
    have he : k + (q + 1) * v = k + q * v + v := by ring
    rw [he, pow_add_of_repeat c h (by omega), ih]

lemma exists_repeat [Fintype M] (c : M) :
    ∃ i v : ℕ, i < Fintype.card M ∧ 0 < v ∧ v ≤ Fintype.card M ∧
      c ^ (i + v) = c ^ i := by
  obtain ⟨i, j, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (Fintype.card M + 1) => c ^ n.val) (by simp)
  have hvne : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hvne with hij | hji
  · refine ⟨i.val, j.val - i.val, by omega, by omega, by omega, ?_⟩
    rw [Nat.add_sub_of_le (le_of_lt hij)]
    exact he.symm
  · refine ⟨j.val, i.val - j.val, by omega, by omega, by omega, ?_⟩
    rw [Nat.add_sub_of_le (le_of_lt hji)]
    exact he

theorem pow_factorial [Fintype M] (c : M) {k : ℕ} (hk : Fintype.card M ≤ k) (q : ℕ) :
    c ^ (k + q * (Fintype.card M).factorial) = c ^ k := by
  obtain ⟨i, v, hi, hv, hvN, he⟩ := exists_repeat c
  obtain ⟨r, hr⟩ := Nat.dvd_factorial hv hvN
  rw [hr]
  have ha : q * (v * r) = (q * r) * v := by ring
  rw [ha]
  exact pow_add_multiple c he (by omega) _

end FiniteMonoidPeriod

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace LocalMarkers

variable {Alphabet : Type uAlphabet}

def AgreesOn (f g : ℤ → Alphabet) (l r : ℤ) : Prop :=
  ∀ x : ℤ, l ≤ x → x < r → f x = g x

def ShortContinuation (d K : ℕ) (w : ℤ → Alphabet) (z : ℤ) (v : ℤ → Alphabet) : Prop :=
  (∃ a : ℕ, 0 < a ∧ a < d ∧ Function.Periodic v (a : ℤ)) ∧
    AgreesOn w v z (z + K)

lemma short_continuation_exists {d K : ℕ} (hK : d ≤ K) (w : ℤ → Alphabet) (z : ℤ)
    (hp : ∃ a : ℕ, 0 < a ∧ a < d ∧ Period (fun i : Fin K => w (z + i.val)) a) :
    ∃ v : ℤ → Alphabet, ShortContinuation d K w z v := by
  obtain ⟨a, ha, had, hp⟩ := hp
  obtain ⟨v, hv, he⟩ := exists_continuation z ha (by omega) hp
  refine ⟨v, ⟨a, ha, had, hv⟩, ?_⟩
  intro x hx hx'
  have hn : ((x - z).toNat : ℤ) = x - z := Int.toNat_of_nonneg (by omega)
  let i : Fin K := ⟨(x - z).toNat, by omega⟩
  have hi : z + (i.val : ℤ) = x := by dsimp [i]; omega
  simpa only [hi] using (he i).symm

lemma short_continuations_equal {d K : ℕ} {w v v' : ℤ → Alphabet} {z z' : ℤ}
    (hv : ShortContinuation d K w z v) (hv' : ShortContinuation d K w z' v')
    (hover : (d : ℤ) ^ 2 ≤ (K : ℤ) - |z - z'|) : v = v' := by
  obtain ⟨⟨a, ha, had, hva⟩, he⟩ := hv
  obtain ⟨⟨b, hb, hbd, hvb⟩, he'⟩ := hv'
  have haZ : 0 < (a : ℤ) := by omega
  have hbZ : 0 < (b : ℤ) := by omega
  have hadZ : (a : ℤ) < d := by omega
  have hbdZ : (b : ℤ) < d := by omega
  have hab : (a : ℤ) * b ≤ (d : ℤ) ^ 2 := by nlinarith
  apply periodic_agree haZ hbZ hva hvb (max z z')
  intro x hx hx'
  have hz : z ≤ x := (le_max_left z z').trans hx
  have hz' : z' ≤ x := (le_max_right z z').trans hx
  have hu : x < z + K := by
    have hmax : max z z' = if z ≤ z' then z' else z := max_def _ _
    split_ifs at hmax with hzz
    · rw [abs_of_nonpos (by omega)] at hover
      omega
    · rw [abs_of_nonneg (by omega)] at hover
      omega
  have hu' : x < z' + K := by
    have hmax : max z z' = if z ≤ z' then z' else z := max_def _ _
    split_ifs at hmax with hzz
    · rw [abs_of_nonpos (by omega)] at hover
      omega
    · rw [abs_of_nonneg (by omega)] at hover
      omega
  exact (he x hz hu).symm.trans (he' x hz' hu')

lemma common_continuation {d K : ℕ} (w : ℤ → Alphabet) (S : Finset ℤ)
    (hne : S.Nonempty) (v : ℤ → ℤ → Alphabet)
    (hv : ∀ z ∈ S, ShortContinuation d K w z (v z))
    (hover : ∀ z ∈ S, ∀ z' ∈ S, (d : ℤ) ^ 2 ≤ (K : ℤ) - |z - z'|) :
    ∃ u : ℤ → Alphabet, (∃ a : ℕ, 0 < a ∧ a < d ∧ Function.Periodic u (a : ℤ)) ∧
      ∀ z ∈ S, v z = u ∧ AgreesOn w u z (z + K) := by
  obtain ⟨z, hz⟩ := hne
  refine ⟨v z, (hv z hz).1, ?_⟩
  intro z' hz'
  have he := short_continuations_equal (hv z' hz') (hv z hz) (hover z' hz' z hz)
  exact ⟨he, he ▸ (hv z' hz').2⟩

lemma periodic_run {d K : ℕ} (hd : 2 ≤ d) (hK : 3 * d ^ 2 < K)
    (w : ℤ → Alphabet) (l u : ℤ) (hlu : l ≤ u)
    (hp : ∀ x : ℤ, l ≤ x → x ≤ u →
      ∃ a : ℕ, 0 < a ∧ a < d ∧ Period (fun i : Fin K => w (x + i.val)) a) :
    ∃ v : ℤ → Alphabet, (∃ a : ℕ, 0 < a ∧ a < d ∧ Function.Periodic v (a : ℤ)) ∧
      AgreesOn w v l (u + K) := by
  classical
  have hdK : d ≤ K := by nlinarith
  have hex : ∀ x : {x : ℤ // l ≤ x ∧ x ≤ u},
      ∃ v : ℤ → Alphabet, ShortContinuation d K w x.val v := by
    intro x
    exact short_continuation_exists hdK w x.val (hp x.val x.2.1 x.2.2)
  choose v hv using hex
  let x₀ : {x : ℤ // l ≤ x ∧ x ≤ u} := ⟨l, le_refl _, hlu⟩
  have heq : ∀ (n : ℕ) (hn : l + n ≤ u),
      v ⟨l + n, by omega, hn⟩ = v x₀ := by
    intro n
    induction n with
    | zero => intro hn; congr 1; apply Subtype.ext; simp [x₀]
    | succ n ih =>
      intro hn
      have hn' : l + (n : ℤ) ≤ u := by omega
      have hover : (d : ℤ) ^ 2 ≤ (K : ℤ) - |(l + (n + 1 : ℕ)) - (l + n)| := by
        have hh : (n + 1 : ℕ) = n + 1 := rfl
        have hcast : (3 : ℤ) * (d : ℤ) ^ 2 < K := by exact_mod_cast hK
        have habs : |(l + (n + 1 : ℕ)) - (l + n)| = 1 := by
          rw [Nat.cast_add, Nat.cast_one]
          ring_nf
          norm_num
        rw [habs]
        nlinarith [sq_nonneg (d : ℤ)]
      exact (short_continuations_equal (hv ⟨l + ((n + 1 : ℕ) : ℤ), by omega, hn⟩)
        (hv ⟨l + n, by omega, hn'⟩) hover).trans (ih hn')
  refine ⟨v x₀, (hv x₀).1, ?_⟩
  intro i hi hi'
  let x : ℤ := min i u
  have hx : l ≤ x ∧ x ≤ u := ⟨le_min hi hlu, min_le_right _ _⟩
  have hn : ((x - l).toNat : ℤ) = x - l := Int.toNat_of_nonneg (by omega)
  have he : v ⟨x, hx⟩ = v x₀ := by
    have hh := heq (x - l).toNat (by omega)
    have hxval : l + (((x - l).toNat : ℕ) : ℤ) = x := by omega
    simpa only [hxval] using hh
  rw [← he]
  apply (hv ⟨x, hx⟩).2 i (min_le_left _ _)
  dsimp [x]
  rcases le_total i u with h | h
  · rw [min_eq_left h]
    have : (0 : ℤ) < K := by omega
    omega
  · rwa [min_eq_right h]

end LocalMarkers

namespace MarkerSearch

def Separated (S : Set ℤ) (d : ℤ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|

def FirstAfter (S : Set ℤ) (l m : ℤ) : Prop :=
  m ∈ S ∧ l ≤ m ∧ ∀ m' ∈ S, l ≤ m' → m ≤ m'

lemma firstAfter_unique {S : Set ℤ} {l m m' : ℤ}
    (h : FirstAfter S l m) (h' : FirstAfter S l m') : m = m' :=
  le_antisymm (h.2.2 m' h'.1 h'.2.1) (h'.2.2 m h.1 h.2.1)

noncomputable def search (S : Set ℤ) (l r : ℤ) : Option ℤ := by
  classical
  let F := (Finset.Icc l r).filter (· ∈ S)
  exact if h : F.Nonempty then some (F.min' h) else none

lemma search_none {S : Set ℤ} {l r : ℤ} :
    search S l r = none ↔ ∀ m ∈ S, l ≤ m → m ≤ r → False := by
  classical
  dsimp only [search]
  split_ifs with h
  · simp only [false_iff]
    obtain ⟨m, hm⟩ := h
    have hh := Finset.mem_filter.mp hm
    have hb := Finset.mem_Icc.mp hh.1
    exact fun hn => hn m hh.2 hb.1 hb.2
  · simp only [true_iff]
    intro m hm hl hr
    exact h ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl, hr⟩, hm⟩⟩

lemma search_some {S : Set ℤ} {l r m : ℤ} :
    search S l r = some m ↔ FirstAfter S l m ∧ m ≤ r := by
  classical
  let F := (Finset.Icc l r).filter (· ∈ S)
  constructor
  · dsimp only [search]
    split_ifs with h
    · intro he
      have hm : F.min' h = m := Option.some.inj he
      have hmem : m ∈ F := hm ▸ F.min'_mem h
      obtain ⟨hb, hS⟩ := Finset.mem_filter.mp hmem
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hb
      refine ⟨⟨hS, hl, ?_⟩, hr⟩
      intro m' hm' hl'
      by_cases hr' : m' ≤ r
      · rw [← hm]
        exact F.min'_le m' (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl', hr'⟩, hm'⟩)
      · omega
    · simp
  · rintro ⟨h, hr⟩
    have hf : F.Nonempty := ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h.2.1, hr⟩, h.1⟩⟩
    have hmem := F.min'_mem hf
    obtain ⟨hb, hS⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hl, _⟩ := Finset.mem_Icc.mp hb
    have he : F.min' hf = m := le_antisymm
      (F.min'_le m (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h.2.1, hr⟩, h.1⟩))
      (h.2.2 _ hS hl)
    dsimp only [search]
    rw [dite_eq_left hf]
    exact congrArg some he

lemma search_some_or_none (S : Set ℤ) (l r : ℤ) :
    (∀ m ∈ S, l ≤ m → m ≤ r → False) ∨
      ∃ m, FirstAfter S l m ∧ m ≤ r := by
  cases h : search S l r with
  | none => exact Or.inl (search_none.mp h)
  | some m => exact Or.inr ⟨m, search_some.mp h⟩

lemma search_ext {S : Set ℤ} {l r l' r' : ℤ}
    (he : ∀ m ∈ S, (l ≤ m ∧ m ≤ r) ↔ (l' ≤ m ∧ m ≤ r')) :
    search S l r = search S l' r' := by
  classical
  have hf : (Finset.Icc l r).filter (· ∈ S) = (Finset.Icc l' r').filter (· ∈ S) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h, hS⟩
      exact ⟨(he m hS).mp h, hS⟩
    · rintro ⟨h, hS⟩
      exact ⟨(he m hS).mpr h, hS⟩
  dsimp only [search]
  simp only [hf]

lemma firstAfter_shift {S : Set ℤ} {l v m w : ℤ} (_hw : 0 ≤ w) (hv : |v| ≤ w)
    (hleft : ∀ m ∈ S, w < |m - l|) :
    FirstAfter S (l + v) m ↔ FirstAfter S l m := by
  have hv' := abs_le.mp hv
  constructor
  · intro h
    have hml := h.2.1
    have hdist := hleft m h.1
    have hl : l ≤ m := by
      by_contra hn
      rw [abs_of_neg (by omega)] at hdist
      omega
    refine ⟨h.1, hl, ?_⟩
    intro m' hm' hl'
    have hdist' := hleft m' hm'
    rw [abs_of_nonneg (by omega)] at hdist'
    exact h.2.2 m' hm' (by omega)
  · intro h
    have hml := h.2.1
    have hdist := hleft m h.1
    rw [abs_of_nonneg (by omega)] at hdist
    refine ⟨h.1, by omega, ?_⟩
    intro m' hm' hl'
    have hdist' := hleft m' hm'
    have hl'' : l ≤ m' := by
      by_contra hn
      rw [abs_of_neg (by omega)] at hdist'
      omega
    exact h.2.2 m' hm' hl''

lemma instability_charge {S : Set ℤ} {l r v w : ℤ} (hw : 0 ≤ w) (hv : |v| ≤ w)
    (hne : search S l r ≠ search S (l + v) (r + v)) :
    (∃ m ∈ S, |m - l| ≤ w) ∨
      ∃ m, FirstAfter S l m ∧ |m - r| ≤ w := by
  classical
  by_cases hn : ∃ m ∈ S, |m - l| ≤ w
  · exact Or.inl hn
  · right
    have hleft : ∀ m ∈ S, w < |m - l| := by
      intro m hm
      exact lt_of_not_ge (fun he => hn ⟨m, hm, he⟩)
    have hv' := abs_le.mp hv
    cases h₀ : search S l r with
    | none =>
      cases h₁ : search S (l + v) (r + v) with
      | none => exact False.elim (hne (h₀.trans h₁.symm))
      | some m =>
        obtain ⟨hm, hmr⟩ := search_some.mp h₁
        have hm' := (firstAfter_shift hw hv hleft).mp hm
        have hlarge : r < m := by
          by_contra he
          exact search_none.mp h₀ m hm'.1 hm'.2.1 (le_of_not_gt he)
        refine ⟨m, hm', ?_⟩
        rw [abs_of_pos (by omega)]
        omega
    | some m =>
      obtain ⟨hm, hmr⟩ := search_some.mp h₀
      cases h₁ : search S (l + v) (r + v) with
      | none =>
        have hm' := (firstAfter_shift hw hv hleft).mpr hm
        have hlarge : r + v < m := by
          by_contra he
          exact search_none.mp h₁ m hm'.1 hm'.2.1 (le_of_not_gt he)
        refine ⟨m, hm, ?_⟩
        rw [abs_of_nonpos (by omega)]
        omega
      | some m' =>
        have hm' := (firstAfter_shift hw hv hleft).mp (search_some.mp h₁).1
        have he := firstAfter_unique hm hm'
        exact False.elim (hne (h₀.trans ((congrArg some he).trans h₁.symm)))

lemma extension_charge {S : Set ℤ} {l r H : ℤ}
    (hn : search S l r = none) (he : ∃ m ∈ S, l ≤ m ∧ m ≤ r + H) :
    ∃ m, FirstAfter S l m ∧ 0 < m - r ∧ m - r ≤ H := by
  have hsome : search S l (r + H) ≠ none := by
    intro h
    obtain ⟨m, hm, hl, hr⟩ := he
    exact search_none.mp h m hm hl hr
  cases h : search S l (r + H) with
  | none => exact False.elim (hsome h)
  | some m =>
    obtain ⟨hm, hr⟩ := search_some.mp h
    have hlo : r < m := by
      by_contra he
      exact search_none.mp hn m hm.1 hm.2.1 (le_of_not_gt he)
    exact ⟨m, hm, by omega, by omega⟩

end MarkerSearch

namespace MarkerSearch

open scoped Classical

lemma close_unique {a b c w : ℤ} (ha : |a - c| ≤ w) (hb : |b - c| ≤ w)
    (hgap : 2 * w < |a - b|) : False := by
  have h := abs_sub_le a c b
  rw [abs_sub_comm c b] at h
  omega

lemma separated_interval_unique {S : Set ℤ} {d l r x y : ℤ}
    (hS : Separated S d) (hlen : r - l < d)
    (hx : x ∈ S) (hy : y ∈ S) (hxl : l ≤ x) (hxr : x ≤ r)
    (hyl : l ≤ y) (hyr : y ≤ r) : x = y := by
  by_contra hn
  have h := hS x hx y hy hn
  have hxy : |x - y| ≤ r - l := abs_le.mpr ⟨by omega, by omega⟩
  omega

lemma firstAfter_same_side {S : Set ℤ} {d l r z z' m m' : ℤ}
    (hS : Separated S d) (hlen : r - l < d)
    (hz : l ≤ z ∧ z ≤ r) (hz' : l ≤ z' ∧ z' ≤ r)
    (hm : FirstAfter S z m) (hm' : FirstAfter S z' m')
    (hside : (m ≤ r) ↔ (m' ≤ r)) : m = m' := by
  by_cases h : m ≤ r
  · exact separated_interval_unique hS hlen hm.1 hm'.1
      (hz.1.trans hm.2.1) h (hz'.1.trans hm'.2.1) (hside.mp h)
  · have h' : r < m' := lt_of_not_ge (fun hh => h (hside.mpr hh))
    exact le_antisymm (hm.2.2 m' hm'.1 (by omega))
      (hm'.2.2 m hm.1 (by omega))

lemma left_charge_card {ι : Type uι} (s : Finset ι) {S : Set ℤ}
    {d z h w : ℤ} (δ : ι → ℤ)
    (hS : Separated S d) (hsep : 2 * h + 2 * w < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 * w < |δ i - δ j|) :
    (s.filter fun i => ∃ m ∈ S, |m - (z + δ i)| ≤ w).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, m, hm, hmclose⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, m', hm', hmclose'⟩ := Finset.mem_filter.mp hj
  have hiδ := abs_le.mp (hδ i hi)
  have hjδ := abs_le.mp (hδ j hj)
  have hmδ := abs_le.mp hmclose
  have hmδ' := abs_le.mp hmclose'
  have he : m = m' := separated_interval_unique hS (by omega) hm hm'
    (show z - h - w ≤ m by omega) (show m ≤ z + h + w by omega)
    (by omega) (by omega)
  subst m'
  by_contra hij
  have ha : |δ i - (m - z)| ≤ w := by
    rw [abs_sub_comm]
    convert hmclose using 1
    congr 1
    ring
  have hb : |δ j - (m - z)| ≤ w := by
    rw [abs_sub_comm]
    convert hmclose' using 1
    congr 1
    ring
  exact close_unique ha hb (hgap i hi j hj hij)

lemma right_charge_card {ι : Type uι2} (s : Finset ι) {S : Set ℤ}
    {d z h w : ℤ} (δ H : ι → ℤ)
    (hS : Separated S d) (hsep : 2 * h < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      2 * w < |(z + δ i + H i) - (z + δ j + H j)|) :
    (s.filter fun i => ∃ m, FirstAfter S (z + δ i) m ∧
      |m - (z + δ i + H i)| ≤ w).card ≤ 2 := by
  classical
  let F := s.filter fun i => ∃ m, FirstAfter S (z + δ i) m ∧
    |m - (z + δ i + H i)| ≤ w
  have hp : ∀ i : {i // i ∈ F}, ∃ m, FirstAfter S (z + δ i.val) m ∧
      |m - (z + δ i.val + H i.val)| ≤ w :=
    fun i => (Finset.mem_filter.mp i.2).2
  choose m hm using hp
  have hinj : Function.Injective (fun i => decide (m i ≤ z + h)) := by
    intro i j he
    have hi := (Finset.mem_filter.mp i.2).1
    have hj := (Finset.mem_filter.mp j.2).1
    have hiδ := abs_le.mp (hδ i.val hi)
    have hjδ := abs_le.mp (hδ j.val hj)
    have hside : (m i ≤ z + h) ↔ (m j ≤ z + h) := by simpa using he
    have hme := firstAfter_same_side hS (show z + h - (z - h) < d by omega)
      (show z - h ≤ z + δ i.val ∧ z + δ i.val ≤ z + h by omega)
      (show z - h ≤ z + δ j.val ∧ z + δ j.val ≤ z + h by omega)
      (hm i).1 (hm j).1 hside
    apply Subtype.ext
    by_contra hij
    have hc := (hm j).2
    rw [← hme] at hc
    exact close_unique (by simpa [abs_sub_comm] using (hm i).2)
      (by simpa [abs_sub_comm] using hc) (hgap i.val hi j.val hj hij)
  simpa [F] using Fintype.card_le_of_injective _ hinj

def InnerFailure (S : Set ℤ) (z H w E : ℤ) : Prop :=
  (∃ v, |v| ≤ w ∧ search S z (z + H) ≠ search S (z + v) (z + H + v)) ∨
  (search S z (z + H) = none ∧ ∃ m ∈ S, z ≤ m ∧ m ≤ z + H + E)

lemma innerFailure_charge {S : Set ℤ} {z H w E : ℤ} (hw : 0 ≤ w)
    (hf : InnerFailure S z H w E) :
    (∃ m ∈ S, |m - z| ≤ w) ∨
      ∃ m, FirstAfter S z m ∧ |m - (z + H)| ≤ max E w := by
  rcases hf with ⟨v, hv, hne⟩ | ⟨hn, he⟩
  · rcases instability_charge hw hv hne with h | ⟨m, hm, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨m, hm, hc.trans (le_max_right _ _)⟩
  · obtain ⟨m, hm, hlo, hhi⟩ := extension_charge hn he
    exact Or.inr ⟨m, hm, by rw [abs_of_pos hlo]; exact hhi.trans (le_max_left _ _)⟩

lemma innerFailure_card {ι : Type uι3} (s : Finset ι) {S : Set ℤ}
    {d z h w E : ℤ} (δ H : ι → ℤ)
    (hS : Separated S d) (hw : 0 ≤ w) (hsep : 2 * h + 2 * w < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 * w < |δ i - δ j|)
    (hrgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      2 * max E w < |(z + δ i + H i) - (z + δ j + H j)|) :
    (s.filter fun i => InnerFailure S (z + δ i) (H i) w E).card ≤ 3 := by
  classical
  let A := s.filter fun i => ∃ m ∈ S, |m - (z + δ i)| ≤ w
  let B := s.filter fun i => ∃ m, FirstAfter S (z + δ i) m ∧
    |m - (z + δ i + H i)| ≤ max E w
  have hs : (s.filter fun i => InnerFailure S (z + δ i) (H i) w E) ⊆ A ∪ B := by
    intro i hi
    obtain ⟨hi, hf⟩ := Finset.mem_filter.mp hi
    rcases innerFailure_charge hw hf with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hb⟩)
  have ha : A.card ≤ 1 := left_charge_card s δ hS hsep hδ hgap
  have hb : B.card ≤ 2 := right_charge_card s δ H hS (by omega) hδ hrgap
  exact (Finset.card_le_card hs).trans ((Finset.card_union_le A B).trans (show A.card + B.card ≤ 3 by omega))

end MarkerSearch

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace EndSearch

open scoped Classical

def width (B S a x : ℤ) : ℤ := a + x % B * S

def Eligible (markers : Set ℤ) (B S a z m : ℤ) : Prop :=
  m ∈ markers ∧ |m - z| ≤ width B S a (m - z)

lemma width_bounds {B S a x : ℤ} (hB : 0 < B) (hS : 0 ≤ S) :
    a ≤ width B S a x ∧ width B S a x ≤ a + (B - 1) * S := by
  have hlo := Int.emod_nonneg x (ne_of_gt hB)
  have hhi := Int.emod_lt_of_pos x hB
  dsimp [width]
  constructor
  · nlinarith
  · nlinarith

noncomputable def eligibleSet (markers : Set ℤ) (B S a z : ℤ) : Finset ℤ :=
  (Finset.Icc (z - (a + (B - 1) * S)) (z + (a + (B - 1) * S))).filter
    (Eligible markers B S a z)

lemma mem_eligibleSet {markers : Set ℤ} {B S a z m : ℤ}
    (hB : 0 < B) (hS : 0 ≤ S) :
    m ∈ eligibleSet markers B S a z ↔ Eligible markers B S a z m := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hm
    have hb := abs_le.mp (hm.2.trans (width_bounds hB hS).2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hm⟩

noncomputable def search (markers : Set ℤ) (B S a z : ℤ) : Option ℤ :=
  let F := eligibleSet markers B S a z
  if h : F.Nonempty then some (F.min' h) else none

lemma search_none {markers : Set ℤ} {B S a z : ℤ} (hB : 0 < B) (hS : 0 ≤ S) :
    search markers B S a z = none ↔ ∀ m, ¬Eligible markers B S a z m := by
  dsimp only [search]
  split_ifs with h
  · simp only [false_iff]
    obtain ⟨m, hm⟩ := h
    exact fun hn => hn m ((mem_eligibleSet hB hS).mp hm)
  · simp only [true_iff]
    exact fun m hm => h ⟨m, (mem_eligibleSet hB hS).mpr hm⟩

lemma search_some {markers : Set ℤ} {B S a z m : ℤ} (hB : 0 < B) (hS : 0 ≤ S) :
    search markers B S a z = some m ↔ Eligible markers B S a z m ∧
      ∀ m', Eligible markers B S a z m' → m ≤ m' := by
  dsimp only [search]
  split_ifs with h
  · constructor
    · intro he
      obtain rfl := Option.some.inj he
      exact ⟨(mem_eligibleSet hB hS).mp (Finset.min'_mem _ h),
        fun m' hm' => Finset.min'_le _ _ ((mem_eligibleSet hB hS).mpr hm')⟩
    · rintro ⟨hm, hmin⟩
      congr 1
      exact le_antisymm (Finset.min'_le _ _ ((mem_eligibleSet hB hS).mpr hm))
        (hmin _ ((mem_eligibleSet hB hS).mp (Finset.min'_mem _ h)))
  · constructor
    · intro he
      cases he
    · rintro ⟨hm, _⟩
      exact False.elim (h ⟨m, (mem_eligibleSet hB hS).mpr hm⟩)

lemma width_shift {B S a x v : ℤ} (hv : B ∣ v) :
    width B S a (x - v) = width B S a x := by
  dsimp [width]
  rw [Int.sub_emod, Int.emod_eq_zero_of_dvd hv, sub_zero, Int.emod_emod]

lemma changed_eligibility {markers : Set ℤ} {B S a z v : ℤ}
    (hB : 0 < B) (hS : 0 ≤ S)
    (hne : search markers B S a z ≠ search markers B S a (z + v)) :
    ∃ m, ¬(Eligible markers B S a z m ↔ Eligible markers B S a (z + v) m) := by
  by_contra! hn
  apply hne
  have he : eligibleSet markers B S a z = eligibleSet markers B S a (z + v) := by
    ext m
    exact (mem_eligibleSet hB hS).trans ((hn m).trans (mem_eligibleSet hB hS).symm)
  simp only [search, he]

lemma crossing {x D v w : ℤ} (hv : |v| ≤ w)
    (hne : ¬(|x| ≤ D ↔ |x - v| ≤ D)) :
    |x - D| ≤ w ∨ |x + D| ≤ w := by
  have hv' := abs_le.mp hv
  by_cases hx : |x| ≤ D
  · have hx' := abs_le.mp hx
    have hn : ¬ |x - v| ≤ D := fun h => hne ⟨fun _ => h, fun _ => hx⟩
    have hn' : ¬(-D ≤ x - v ∧ x - v ≤ D) := by simpa only [abs_le] using hn
    rw [abs_le, abs_le]
    omega
  · have hx' : |x - v| ≤ D := by
      by_contra hh
      exact hne ⟨fun h => False.elim (hx h), fun h => False.elim (hh h)⟩
    have hx'' := abs_le.mp hx'
    have hn' : ¬(-D ≤ x ∧ x ≤ D) := by simpa only [abs_le] using hx
    rw [abs_le, abs_le]
    omega

lemma instability_charge {markers : Set ℤ} {B S a z v w : ℤ}
    (hB : 0 < B) (hS : 0 ≤ S) (hvB : B ∣ v) (hv : |v| ≤ w)
    (hne : search markers B S a z ≠ search markers B S a (z + v)) :
    ∃ m ∈ markers,
      |m - (z + width B S a (m - z))| ≤ w ∨
      |m - (z - width B S a (m - z))| ≤ w := by
  obtain ⟨m, hm⟩ := changed_eligibility hB hS hne
  have hmS : m ∈ markers := by
    by_contra hn
    exact hm (by simp [Eligible, hn])
  have he : width B S a (m - (z + v)) = width B S a (m - z) := by
    rw [show m - (z + v) = (m - z) - v by ring]
    exact width_shift hvB
  have hc : ¬(|m - z| ≤ width B S a (m - z) ↔
      |(m - z) - v| ≤ width B S a (m - z)) := by
    simp only [Eligible, hmS, true_and] at hm
    rw [he] at hm
    simpa only [show m - (z + v) = (m - z) - v by ring] using hm
  refine ⟨m, hmS, ?_⟩
  rw [show m - (z + width B S a (m - z)) = (m - z) - width B S a (m - z) by ring,
    show m - (z - width B S a (m - z)) = (m - z) + width B S a (m - z) by ring]
  exact crossing hv hc

end EndSearch

namespace EndSearch

open scoped Classical

def Boundary (B S a z m : ℤ) (positive : Bool) : ℤ :=
  if positive then z + width B S a (m - z) else z - width B S a (m - z)

lemma boundary_charge_card {ι : Type uι} (s : Finset ι) {markers : Set ℤ}
    {B S a z h w d : ℤ} (δ : ι → ℤ) (positive : Bool)
    (hB : 0 < B) (hS : 2 * h + 2 * w < S) (hSn : 0 ≤ S)
    (hmarkers : MarkerSearch.Separated markers d)
    (hlen : 2 * h + (B - 1) * S + 2 * w < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hmod : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i % B ≠ δ j % B) :
    (s.filter fun i => ∃ m ∈ markers, |m - Boundary B S a (z + δ i) m positive| ≤ w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, m, hm, hc⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, m', hm', hc'⟩ := Finset.mem_filter.mp hj
  have hiδ := abs_le.mp (hδ i hi)
  have hjδ := abs_le.mp (hδ j hj)
  have hmi := width_bounds (x := m - (z + δ i)) (a := a) hB hSn
  have hmj := width_bounds (x := m' - (z + δ j)) (a := a) hB hSn
  have hcb := abs_le.mp hc
  have hcb' := abs_le.mp hc'
  have he : m = m' := by
    cases positive
    · dsimp [Boundary] at hcb hcb'
      exact MarkerSearch.separated_interval_unique hmarkers (by omega) hm hm'
        (show z - a - h - (B - 1) * S - w ≤ m by omega)
        (show m ≤ z - a + h + w by omega) (by omega) (by omega)
    · dsimp [Boundary] at hcb hcb'
      exact MarkerSearch.separated_interval_unique hmarkers (by omega) hm hm'
        (show z + a - h - w ≤ m by omega)
        (show m ≤ z + a + h + (B - 1) * S + w by omega) (by omega) (by omega)
  subst m'
  by_contra hij
  have hidx : (m - (z + δ i)) % B ≠ (m - (z + δ j)) % B := by
    intro he
    have hh := (show Int.ModEq B (m - (z + δ i)) (m - (z + δ j)) from he).sub_left (m - z)
    apply hmod i hi j hj hij
    change Int.ModEq B (δ i) (δ j)
    convert hh using 1 <;> ring
  have hidx' := lt_or_gt_of_ne hidx
  cases positive <;> dsimp [Boundary, width] at hcb hcb'
  all_goals rcases hidx' with hlt | hlt <;> nlinarith

 def Unstable (markers : Set ℤ) (B S a z w : ℤ) : Prop :=
  ∃ v, B ∣ v ∧ |v| ≤ w ∧ search markers B S a z ≠ search markers B S a (z + v)

lemma unstable_card {ι : Type uι2} (s : Finset ι) {markers : Set ℤ}
    {B S a z h w d : ℤ} (δ : ι → ℤ)
    (hB : 0 < B) (hS : 2 * h + 2 * w < S) (hSn : 0 ≤ S)
    (hmarkers : MarkerSearch.Separated markers d)
    (hlen : 2 * h + (B - 1) * S + 2 * w < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hmod : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i % B ≠ δ j % B) :
    (s.filter fun i => Unstable markers B S a (z + δ i) w).card ≤ 2 := by
  let F := fun b => s.filter fun i =>
    ∃ m ∈ markers, |m - Boundary B S a (z + δ i) m b| ≤ w
  have hsub : (s.filter fun i => Unstable markers B S a (z + δ i) w) ⊆
      F true ∪ F false := by
    intro i hi
    obtain ⟨hi, v, hvB, hv, hn⟩ := Finset.mem_filter.mp hi
    obtain ⟨m, hm, hc | hc⟩ := instability_charge hB hSn hvB hv hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, m, hm, hc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, m, hm, hc⟩)
  have ht : (F true).card ≤ 1 := boundary_charge_card s δ true hB hS hSn hmarkers hlen hδ hmod
  have hf : (F false).card ≤ 1 := boundary_charge_card s δ false hB hS hSn hmarkers hlen hδ hmod
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

lemma two_searches_card {ι : Type uι3} (s : Finset ι) {markers : Set ℤ}
    {B S a₀ a₁ z h w d : ℤ} (δ : ι → ℤ)
    (hB : 0 < B) (hS : 2 * h + 2 * w < S) (hSn : 0 ≤ S)
    (hmarkers : MarkerSearch.Separated markers d)
    (hlen : 2 * h + (B - 1) * S + 2 * w < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h)
    (hmod : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ i % B ≠ δ j % B) :
    (s.filter fun i => Unstable markers B S a₀ (z + δ i) w ∨
      Unstable markers B S a₁ (z + δ i) w).card ≤ 4 := by
  rw [Finset.filter_or]
  have h₀ := unstable_card (a := a₀) (z := z) s δ hB hS hSn hmarkers hlen hδ hmod
  have h₁ := unstable_card (a := a₁) (z := z) s δ hB hS hSn hmarkers hlen hδ hmod
  exact (Finset.card_union_le _ _).trans (by omega)

end EndSearch

namespace MarkerSearch

lemma interval_card {S : Set ℤ} {d l r : ℤ} (F : Finset ℤ) (N : ℕ)
    (hS : Separated S d) (hd : 0 < d) (hlen : r - l < N * d)
    (hF : ∀ m ∈ F, m ∈ S ∧ l ≤ m ∧ m ≤ r) : F.card ≤ N := by
  classical
  have hb : ∀ m : {m // m ∈ F}, 0 ≤ (m.val - l) / d ∧ (m.val - l) / d < N := by
    intro m
    obtain ⟨_, hl, hr⟩ := hF m.val m.2
    exact ⟨Int.ediv_nonneg (by omega) (le_of_lt hd),
      (Int.ediv_lt_iff_lt_mul hd).mpr (by omega)⟩
  let f : {m // m ∈ F} → Fin N := fun m =>
    ⟨((m.val - l) / d).toNat, (Int.toNat_lt (hb m).1).mpr (hb m).2⟩
  have hinj : Function.Injective f := by
    intro m m' he
    have hh := congrArg Fin.val he
    have hq : (m.val - l) / d = (m'.val - l) / d := by
      dsimp [f] at hh
      have h₀ := Int.toNat_of_nonneg (hb m).1
      have h₁ := Int.toNat_of_nonneg (hb m').1
      omega
    apply Subtype.ext
    by_contra hn
    have hsep := hS m.val (hF m.val m.2).1 m'.val (hF m'.val m'.2).1 hn
    have hmod₀ := Int.emod_nonneg (m.val - l) (ne_of_gt hd)
    have hmod₁ := Int.emod_nonneg (m'.val - l) (ne_of_gt hd)
    have hlt₀ := Int.emod_lt_of_pos (m.val - l) hd
    have hlt₁ := Int.emod_lt_of_pos (m'.val - l) hd
    have he₀ := Int.mul_ediv_add_emod (m.val - l) d
    have he₁ := Int.mul_ediv_add_emod (m'.val - l) d
    rw [hq] at he₀
    have habs : |m.val - m'.val| < d := abs_lt.mpr ⟨by omega, by omega⟩
    omega
  simpa using Fintype.card_le_of_injective f hinj

end MarkerSearch

namespace EndSearch

open scoped Classical

lemma nested {markers : Set ℤ} {B S a₀ a₁ z z' H : ℤ}
    (hB : 0 < B) (hS : 0 ≤ S) (hwidth : a₀ + (B - 1) * S + H ≤ a₁)
    (hzz : |z - z'| ≤ H) (hne : search markers B S a₀ z' ≠ none) :
    search markers B S a₁ z ≠ none := by
  intro hn
  cases he : search markers B S a₀ z' with
  | none => exact hne he
  | some m =>
    have hm := (search_some hB hS).mp he
    apply (search_none hB hS).mp hn m
    refine ⟨hm.1.1, ?_⟩
    have hdist : |m - z| ≤ |m - z'| + |z - z'| := by
      simpa only [abs_sub_comm z' z] using abs_sub_le m z' z
    exact (hdist.trans (add_le_add (hm.1.2.trans (width_bounds hB hS).2) hzz)).trans
      (hwidth.trans (width_bounds hB hS).1)

lemma anchor_card {ι : Type uι4} (s : Finset ι) {markers : Set ℤ}
    {B S d z h q₀ : ℤ} (δ : ι → ℤ)
    (hB : 0 < B) (hS : 0 ≤ S) (hd : 0 < d)
    (hmarkers : MarkerSearch.Separated markers d)
    (hlen : 2 * h + 2 * (B - 1) * S < d)
    (hδ : ∀ i ∈ s, |δ i| ≤ h) :
    (s.image fun i => (search markers B S (3 * d) (z + δ i)).getD q₀).card ≤ 8 := by
  classical
  let l := z - h - (3 * d + (B - 1) * S)
  let r := z + h + (3 * d + (B - 1) * S)
  let F := (Finset.Icc l r).filter (· ∈ markers)
  have hFc : F.card ≤ 7 := MarkerSearch.interval_card (l := l) (r := r) F 7 hmarkers hd (by dsimp [l, r]; nlinarith [hlen])
    (fun m hm => by
      obtain ⟨hb, hm⟩ := Finset.mem_filter.mp hm
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hb
      exact ⟨hm, hl, hr⟩)
  have hsub : (s.image fun i => (search markers B S (3 * d) (z + δ i)).getD q₀) ⊆
      insert q₀ F := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    cases he : search markers B S (3 * d) (z + δ i) with
    | none => simp
    | some m =>
      simp only [Option.getD_some, Finset.mem_insert]
      right
      have hm := (search_some hB hS).mp he
      have hb := abs_le.mp (hm.1.2.trans (width_bounds hB hS).2)
      have hiδ := abs_le.mp (hδ i hi)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp [l]; omega,
        by dsimp [r]; omega⟩, hm.1.1⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))

end EndSearch

namespace StencilSparsity

open scoped Classical

lemma biUnion_card_real {Q : Type uQ} {P : Type uP} (s : Finset Q) (F : Q → Finset P)
    (c : ℝ) (h : ∀ q ∈ s, ((F q).card : ℝ) ≤ c) :
    ((s.biUnion F).card : ℝ) ≤ s.card * c := by
  classical
  calc
    ((s.biUnion F).card : ℝ) ≤ ((∑ q ∈ s, (F q).card : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := s) (t := F))
    _ = ∑ q ∈ s, ((F q).card : ℝ) := by simp
    _ ≤ ∑ _q ∈ s, c := Finset.sum_le_sum h
    _ = s.card * c := by simp

lemma whole_stencil {P : Type uP2} {Q : Type uQ2} {J : Type uJ} (bad instability : Finset P)
    (anchors : Finset Q) (labels : Finset J) (clock : Q → Finset P)
    (inner : Q → J → Finset P) (c : ℝ) (μ : ℕ)
    (hc : 0 ≤ c) (hanchor : anchors.card ≤ 20)
    (hunstable : instability.card ≤ 4)
    (hclock : ∀ q ∈ anchors, ((clock q).card : ℝ) ≤ c)
    (hinner : ∀ q ∈ anchors, ∀ j ∈ labels, (inner q j).card ≤ 3)
    (hcover : bad ⊆ instability ∪ anchors.biUnion
      (fun q => clock q ∪ labels.biUnion (inner q)))
    (hμ : 20 * (c + 4 * labels.card) + 10 < μ) : bad.card < μ := by
  classical
  have hrow : ∀ q ∈ anchors,
      (((clock q ∪ labels.biUnion (inner q)).card : ℕ) : ℝ) ≤ c + 3 * labels.card := by
    intro q hq
    have ht := Finset.card_union_le (clock q) (labels.biUnion (inner q))
    have ht' : (((clock q ∪ labels.biUnion (inner q)).card : ℕ) : ℝ) ≤
        (clock q).card + (labels.biUnion (inner q)).card := by exact_mod_cast ht
    have hi := biUnion_card_real labels (inner q) 3 (fun j hj => by
      exact_mod_cast hinner q hq j hj)
    nlinarith [hclock q hq]
  have hall := biUnion_card_real anchors
    (fun q => clock q ∪ labels.biUnion (inner q)) (c + 3 * labels.card) hrow
  have hu := Finset.card_union_le instability
    (anchors.biUnion (fun q => clock q ∪ labels.biUnion (inner q)))
  have hb := (Finset.card_le_card hcover).trans hu
  have hb' : (bad.card : ℝ) ≤ instability.card +
      (anchors.biUnion (fun q => clock q ∪ labels.biUnion (inner q))).card := by
    exact_mod_cast hb
  have ha : (anchors.card : ℝ) ≤ 20 := by exact_mod_cast hanchor
  have hz : (instability.card : ℝ) ≤ 4 := by exact_mod_cast hunstable
  have hm : (bad.card : ℝ) < μ := by
    have hnon : 0 ≤ (labels.card : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right ha (show 0 ≤ c + 3 * labels.card by positivity)]
  exact_mod_cast hm

lemma good_copy {Kind : Type uKind} [Fintype Kind] (μ : ℕ)
    (bad : Finset ((Kind × Fin μ) × (Kind × Fin μ))) (hbad : bad.card < μ) :
    ∀ kind : Kind, ∃ copy : Fin μ, ∀ q, ((kind, copy), q) ∉ bad := by
  classical
  intro kind
  by_contra! hn
  choose q hq using hn
  let f : Fin μ → {p // p ∈ bad} := fun copy => ⟨((kind, copy), q copy), hq copy⟩
  have hf : Function.Injective f := by
    intro i j he
    exact congrArg (fun p : {p // p ∈ bad} => p.val.1.2) he
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  omega

noncomputable def decode {P : Type uP3} (witness : P → Prop) : Option P :=
  if h : ∃! p, witness p then some h.choose else none

lemma decode_eq_some {P : Type uP4} {witness : P → Prop} {p : P} :
    decode witness = some p ↔ witness p ∧ ∀ q, witness q → q = p := by
  classical
  dsimp only [decode]
  split_ifs with h
  · constructor
    · intro he
      have hp := Option.some.inj he
      exact hp ▸ h.choose_spec
    · rintro ⟨hp, huniq⟩
      exact congrArg some (huniq _ h.choose_spec.1)
  · constructor
    · intro he
      cases he
    · rintro ⟨hp, huniq⟩
      exact False.elim (h ⟨p, hp, huniq⟩)

lemma decode_sound {P : Type uP5} {witness : P → Prop} {actual decoded : P}
    (hactual : witness actual) (hdecode : decode witness = some decoded) : decoded = actual := by
  exact ((decode_eq_some.mp hdecode).2 actual hactual).symm

end StencilSparsity

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace PeriodicTemplates

open scoped Computability Classical

variable {Alphabet : Type u}

def wordPower (c : List Alphabet) (i : ℕ) : List Alphabet :=
  ((FreeMonoid.ofList c) ^ i).toList

@[simp] lemma wordPower_zero (c : List Alphabet) : wordPower c 0 = [] := rfl

lemma wordPower_add (c : List Alphabet) (i j : ℕ) :
    wordPower c (i + j) = wordPower c i ++ wordPower c j := by
  simp only [wordPower, pow_add, FreeMonoid.toList_mul]

@[simp] lemma wordPower_one (c : List Alphabet) : wordPower c 1 = c := by
  simp [wordPower]

lemma wordPower_mul (c : List Alphabet) (i j : ℕ) :
    wordPower (wordPower c i) j = wordPower c (i * j) := by
  simp only [wordPower, FreeMonoid.ofList_toList, pow_mul]

lemma wordPower_replicate (c : List Alphabet) (i : ℕ) :
    wordPower c i = (List.replicate i c).flatten := by
  induction i with
  | zero => rfl
  | succ i hi => simp [wordPower_add, List.replicate_add, hi]

lemma singleton_star (c : List Alphabet) (w : List Alphabet) :
    w ∈ ({c} : Language Alphabet)∗ ↔ ∃ i, w = wordPower c i := by
  rw [Language.mem_kstar]
  constructor
  · rintro ⟨pieces, rfl, hp⟩
    have he : pieces = List.replicate pieces.length c :=
      List.eq_replicate_iff.mpr ⟨rfl, fun v hv => hp v hv⟩
    exact ⟨pieces.length, by rw [wordPower_replicate, he]; simp⟩
  · rintro ⟨i, rfl⟩
    refine ⟨List.replicate i c, wordPower_replicate c i, ?_⟩
    intro v hv
    change v = c
    exact (List.mem_replicate.mp hv).2

 def progression (a c b : List Alphabet) (i p : ℕ) : Language Alphabet :=
  {a ++ wordPower c i} * ({wordPower c p} : Language Alphabet)∗ * {b}

lemma mem_progression (a c b : List Alphabet) (i p : ℕ) (w : List Alphabet) :
    w ∈ progression a c b i p ↔ ∃ q, w = a ++ wordPower c (i + q * p) ++ b := by
  simp only [progression, Language.mem_mul]
  constructor
  · rintro ⟨v, ⟨a', ha, mid, hm, rfl⟩, b', hb, rfl⟩
    subst a'
    subst b'
    obtain ⟨q, rfl⟩ := (singleton_star _ _).mp hm
    exact ⟨q, by rw [wordPower_mul, wordPower_add, Nat.mul_comm q p]; simp only [List.append_assoc]⟩
  · rintro ⟨q, rfl⟩
    refine ⟨(a ++ wordPower c i) ++ wordPower c (p * q), ?_, b, rfl, ?_⟩
    · refine ⟨a ++ wordPower c i, rfl, wordPower c (p * q), ?_, rfl⟩
      apply (singleton_star _ _).mpr
      exact ⟨q, (wordPower_mul c p q).symm⟩
    · rw [wordPower_add, Nat.mul_comm q p]
      simp only [List.append_assoc]

lemma progression_height (a c b : List Alphabet) (i p : ℕ) :
    HasHeightAtMost (progression a c b i p) 1 :=
  ((HasHeightAtMost.singleton _ 1).concat
    ((HasHeightAtMost.singleton _ 0).star)).concat (HasHeightAtMost.singleton _ 1)

 def accepted (a c b : List Alphabet) (P : ℕ → Prop) : Language Alphabet :=
  {w | ∃ i, P i ∧ w = a ++ wordPower c i ++ b}

lemma accepted_height (a c b : List Alphabet) (P : ℕ → Prop) (N p : ℕ)
    (hp : 0 < p) (hperiod : ∀ i, N ≤ i → ∀ q, P (i + q * p) ↔ P i) :
    HasHeightAtMost (accepted a c b P) 1 := by
  classical
  let small := (Finset.range N).filter P
  let residues := (Finset.range p).filter (fun r => P (N + r))
  let L₀ : Language Alphabet := ⨆ i ∈ small, {a ++ wordPower c i ++ b}
  let L₁ : Language Alphabet := ⨆ r ∈ residues, progression a c b (N + r) p
  have h₀ : HasHeightAtMost L₀ 1 := HasHeightAtMost.finset_iSup small _
    (fun i _ => HasHeightAtMost.singleton _ 1)
  have h₁ : HasHeightAtMost L₁ 1 := HasHeightAtMost.finset_iSup residues _
    (fun r _ => progression_height a c b (N + r) p)
  have he : accepted a c b P = L₀ + L₁ := by
    ext w
    change (∃ i, P i ∧ w = a ++ wordPower c i ++ b) ↔ w ∈ L₀ ∨ w ∈ L₁
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases hsmall : i < N
      · left
        exact Language.mem_iSup.mpr ⟨i, Language.mem_iSup.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsmall, hi⟩, rfl⟩⟩
      · right
        let r := (i - N) % p
        let q := (i - N) / p
        have hir : i = N + r + q * p := by
          have hd := Nat.mod_add_div (i - N) p
          rw [Nat.mul_comm p] at hd
          dsimp [r, q]
          omega
        have hr : r < p := Nat.mod_lt _ hp
        have hrP : P (N + r) := by
          apply (hperiod (N + r) (by omega) q).mp
          rwa [← hir]
        exact Language.mem_iSup.mpr ⟨r, Language.mem_iSup.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hrP⟩,
            (mem_progression _ _ _ _ _ _).mpr ⟨q, by rw [← hir]⟩⟩⟩
    · rintro (hw | hw)
      · obtain ⟨i, hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨hi, he⟩ := Language.mem_iSup.mp hw
        exact ⟨i, (Finset.mem_filter.mp hi).2, he⟩
      · obtain ⟨r, hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨hr, hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨q, he⟩ := (mem_progression _ _ _ _ _ _).mp hw
        exact ⟨N + r + q * p, (hperiod _ (by omega) q).mpr
          (Finset.mem_filter.mp hr).2, he⟩
  rw [he]
  exact h₀.union h₁

lemma recognized_template_height {M : Type uM} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) (F : Set M) (a c b : List Alphabet) :
    HasHeightAtMost (accepted a c b (fun i =>
      T (FreeMonoid.ofList a) * (T (FreeMonoid.ofList c)) ^ i * T (FreeMonoid.ofList b) ∈ F)) 1 := by
  apply accepted_height a c b _ (Fintype.card M) (Fintype.card M).factorial
    (Nat.factorial_pos _)
  intro i hi q
  rw [FiniteMonoidPeriod.pow_factorial _ hi]

end PeriodicTemplates

namespace FiniteRecognition

open scoped Computability

variable {Alphabet : Type u}

def transition {Q : Type uQ} (A : DFA Alphabet Q) :
    FreeMonoid Alphabet →* (Function.End Q)ᵐᵒᵖ where
  toFun w := MulOpposite.op (fun q => A.evalFrom q w.toList)
  map_one' := by apply MulOpposite.unop_injective; funext q; rfl
  map_mul' x y := by
    apply MulOpposite.unop_injective
    funext q
    exact A.evalFrom_of_append q x.toList y.toList

@[simp] lemma transition_apply {Q : Type uQ2} (A : DFA Alphabet Q) (w : List Alphabet) (q : Q) :
    (transition A (FreeMonoid.ofList w)).unop q = A.evalFrom q w := rfl

lemma of_regular {L : Language Alphabet} (hL : L.IsRegular) :
    ∃ (M : Type) (_ : Monoid M) (_ : Fintype M) (T : FreeMonoid Alphabet →* M) (F : Set M),
      ∀ w, w ∈ L ↔ T (FreeMonoid.ofList w) ∈ F := by
  classical
  obtain ⟨Q, hQ, A, rfl⟩ := hL
  let : Fintype Q := hQ
  let : Fintype (Function.End Q)ᵐᵒᵖ :=
    Fintype.ofEquiv (Q → Q) (Equiv.refl _ |>.trans MulOpposite.opEquiv)
  exact ⟨(Function.End Q)ᵐᵒᵖ, inferInstance, inferInstance, transition A,
    {f | f.unop A.start ∈ A.accept}, fun _ => Iff.rfl⟩

end FiniteRecognition

namespace PeriodicTemplates

open scoped Computability Classical

variable {Alphabet : Type u}

abbrev Template (Alphabet : Type u) := List Alphabet × List Alphabet × List Alphabet

def instanceWord (t : Template Alphabet) (i : ℕ) : List Alphabet :=
  t.1 ++ wordPower t.2.1 i ++ t.2.2

lemma recognized_cover_height {M : Type uM2} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) (F : Set M)
    (L : Language Alphabet) (hL : ∀ w, w ∈ L ↔ T (FreeMonoid.ofList w) ∈ F)
    (templates : Finset (Template Alphabet))
    (hcover : ∀ w ∈ L, ∃ t ∈ templates, ∃ i, w = instanceWord t i) :
    HasHeightAtMost L 1 := by
  let component := fun t : Template Alphabet => accepted t.1 t.2.1 t.2.2 (fun i =>
    T (FreeMonoid.ofList t.1) * (T (FreeMonoid.ofList t.2.1)) ^ i *
      T (FreeMonoid.ofList t.2.2) ∈ F)
  have hc : ∀ t ∈ templates, HasHeightAtMost (component t) 1 :=
    fun t _ => recognized_template_height T F t.1 t.2.1 t.2.2
  have beq : ∀ t i, T (FreeMonoid.ofList (instanceWord t i)) =
      T (FreeMonoid.ofList t.1) * (T (FreeMonoid.ofList t.2.1)) ^ i *
        T (FreeMonoid.ofList t.2.2) := by
    intro t i
    simp only [instanceWord, wordPower, FreeMonoid.ofList_append,
      FreeMonoid.ofList_toList, map_mul, map_pow]
  have he : L = ⨆ t ∈ templates, component t := by
    ext w
    constructor
    · intro hw
      obtain ⟨t, ht, i, rfl⟩ := hcover w hw
      refine Language.mem_iSup.mpr ⟨t, Language.mem_iSup.mpr ⟨ht, i, ?_, rfl⟩⟩
      change T (FreeMonoid.ofList t.1) * T (FreeMonoid.ofList t.2.1) ^ i *
        T (FreeMonoid.ofList t.2.2) ∈ F
      rw [← beq]
      exact (hL _).mp hw
    · intro hw
      obtain ⟨t, hw⟩ := Language.mem_iSup.mp hw
      obtain ⟨ht, i, hi, rfl⟩ := Language.mem_iSup.mp hw
      apply (hL _).mpr
      exact (beq t i).symm ▸ hi
  rw [he]
  exact HasHeightAtMost.finset_iSup templates component hc

lemma regular_cover_height (L : Language Alphabet) (hL : L.IsRegular)
    (templates : Finset (Template Alphabet))
    (hcover : ∀ w ∈ L, ∃ t ∈ templates, ∃ i, w = instanceWord t i) :
    HasHeightAtMost L 1 := by
  obtain ⟨M, hM, hF, T, F, hT⟩ := FiniteRecognition.of_regular hL
  exact recognized_cover_height T F L hT templates hcover

end PeriodicTemplates

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace SlotResidues

def modulus (N : ℤ) : ℤ := 20 * (N + 1) ^ 3

def representative (N i : ℤ) : ℤ := 4 * N ^ 2 * i + i ^ 2

lemma representative_strict {N i j : ℤ} (_hN : 0 < N) (hi : 0 ≤ i) (hij : i < j) :
    representative N i < representative N j := by
  have hp : 0 < (j - i) * (4 * N ^ 2 + i + j) := mul_pos (by omega) (by nlinarith)
  dsimp [representative]
  nlinarith

lemma positive_quotient {N i j : ℤ} (hN : 0 < N)
    (hj : 1 ≤ j) (hji : j < i) (hi : i ≤ N) :
    (representative N i - representative N j) / (4 * N ^ 2) = i - j := by
  rw [Int.ediv_eq_iff_of_pos (by positivity : 0 < 4 * N ^ 2)]
  have hsq : j ^ 2 < i ^ 2 := by nlinarith
  have hisq : i ^ 2 ≤ N ^ 2 := by nlinarith
  dsimp [representative]
  constructor <;> nlinarith [sq_nonneg j]

lemma positive_unique {N i j k l : ℤ} (hN : 0 < N)
    (hj : 1 ≤ j) (hji : j < i) (hi : i ≤ N)
    (hl : 1 ≤ l) (hlk : l < k) (hk : k ≤ N)
    (he : representative N i - representative N j =
      representative N k - representative N l) : i = k ∧ j = l := by
  have hd : i - j = k - l := by
    rw [← positive_quotient hN hj hji hi, he, positive_quotient hN hl hlk hk]
  have hp : (i - j) * (i + j) = (i - j) * (k + l) := by
    calc
      _ = i ^ 2 - j ^ 2 := by ring
      _ = k ^ 2 - l ^ 2 := by dsimp [representative] at he; nlinarith [hd]
      _ = (k - l) * (k + l) := by ring
      _ = _ := by rw [hd]
  have hs : i + j = k + l := mul_left_cancel₀ (by omega) hp
  omega

lemma signed_unique {N i j k l : ℤ} (hN : 0 < N)
    (hi : 1 ≤ i) (hiN : i ≤ N) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hk : 1 ≤ k) (hkN : k ≤ N) (hl : 1 ≤ l) (hlN : l ≤ N)
    (hij : i ≠ j) (hkl : k ≠ l)
    (he : representative N i - representative N j =
      representative N k - representative N l) : i = k ∧ j = l := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hlt := representative_strict hN (by omega) hij
    have hkl' : k < l := by
      by_contra hn
      have hgt := representative_strict hN (by omega) (by omega : l < k)
      omega
    have hh := positive_unique hN hi hij hjN hk hkl' hlN (by omega)
    exact ⟨hh.2, hh.1⟩
  · have hlt := representative_strict hN (by omega) hji
    have hlk : l < k := by
      by_contra hn
      have hgt := representative_strict hN (by omega) (by omega : k < l)
      omega
    exact positive_unique hN hj hji hiN hl hlk hkN he

lemma representative_bounds {N i : ℤ} (hN : 0 < N) (hi : 1 ≤ i) (hiN : i ≤ N) :
    0 < representative N i ∧ representative N i < modulus N / 2 := by
  have hsq : i ^ 2 ≤ N ^ 2 := by nlinarith
  have hmul : 4 * N ^ 2 * i ≤ 4 * N ^ 2 * N :=
    mul_le_mul_of_nonneg_left hiN (by positivity)
  have hm : modulus N / 2 = 10 * (N + 1) ^ 3 := by
    dsimp [modulus]
    omega
  rw [hm]
  dsimp [representative]
  constructor
  · positivity
  · nlinarith [sq_nonneg N, mul_nonneg (by omega : 0 ≤ N) (sq_nonneg N)]

lemma mod_difference_eq {N i j k l : ℤ} (hN : 0 < N)
    (hi : 1 ≤ i) (hiN : i ≤ N) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hk : 1 ≤ k) (hkN : k ≤ N) (hl : 1 ≤ l) (hlN : l ≤ N)
    (he : (representative N i - representative N j) % modulus N =
      (representative N k - representative N l) % modulus N) :
    representative N i - representative N j = representative N k - representative N l := by
  have hb₁ := representative_bounds hN hi hiN
  have hb₂ := representative_bounds hN hj hjN
  have hb₃ := representative_bounds hN hk hkN
  have hb₄ := representative_bounds hN hl hlN
  have hB : 0 < modulus N := by dsimp [modulus]; positivity
  have hh : |(representative N i - representative N j) -
      (representative N k - representative N l)| < modulus N := by
    apply abs_lt.mpr
    constructor <;> omega
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd (by
    simpa only [neg_sub] using dvd_neg.mpr (Int.modEq_iff_dvd.mp he)) hh)

lemma distinct_differences {N i j k l : ℤ} (hN : 0 < N)
    (hi : 1 ≤ i) (hiN : i ≤ N) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hk : 1 ≤ k) (hkN : k ≤ N) (hl : 1 ≤ l) (hlN : l ≤ N)
    (hij : i ≠ j) (hkl : k ≠ l)
    (he : (representative N i - representative N j) % modulus N =
      (representative N k - representative N l) % modulus N) : i = k ∧ j = l :=
  signed_unique hN hi hiN hj hjN hk hkN hl hlN hij hkl
    (mod_difference_eq hN hi hiN hj hjN hk hkN hl hlN he)

lemma nonzero_difference {N i j : ℤ} (hN : 0 < N)
    (hi : 1 ≤ i) (hiN : i ≤ N) (hj : 1 ≤ j) (hjN : j ≤ N) (hij : i ≠ j) :
    (representative N i - representative N j) % modulus N ≠ 0 := by
  intro he
  have he' : (representative N i - representative N j) % modulus N =
      (representative N i - representative N i) % modulus N := by simpa using he
  have hh := mod_difference_eq hN hi hiN hj hjN hi hiN hi hiN he'
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hlt := representative_strict hN (by omega) hij
    omega
  · have hlt := representative_strict hN (by omega) hji
    omega

end SlotResidues

namespace PeriodicClock

open RobustClock
open scoped BigOperators

variable {C : Type uC} [Fintype C]

lemma large_primes (N : ℕ) : ∃ p : C → ℕ,
    Function.Injective p ∧ ∀ c, Nat.Prime (p c) ∧ N < p c := by
  classical
  let s : Set ℕ := {p | Nat.Prime p ∧ N < p}
  have hs : s.Infinite := Set.infinite_of_forall_exists_gt (fun a => by
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max a N + 1)
    exact ⟨p, ⟨hprime, by omega⟩, by omega⟩)
  have : Infinite s := hs.to_subtype
  let e : C ↪ s := (Fintype.equivFin C).toEmbedding.trans
    ((Fin.valEmbedding).trans (Infinite.natEmbedding s))
  exact ⟨fun c => (e c).val, Subtype.val_injective.comp e.injective,
    fun c => (e c).property⟩

def speedMap (v : C → ℝ) : ℤ →+ (C → RobustClock.Circle) where
  toFun z c := (((z : ℝ) * v c : ℝ) : RobustClock.Circle)
  map_zero' := by ext c; simp
  map_add' x y := by ext c; simp [add_mul]

omit [Fintype C] in
@[simp] lemma speedMap_apply (v : C → ℝ) (z : ℤ) (c : C) :
    speedMap v z c = (((z : ℝ) * v c : ℝ) : RobustClock.Circle) := rfl

lemma period (n a : C → ℕ) (hn : ∀ c, 0 < n c) :
    speedMap (fun c => (a c : ℝ) / n c) ((∏ c, n c : ℕ) : ℤ) = 0 := by
  classical
  ext c
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ c)
  change (((((∏ c, n c : ℕ) : ℝ) * ((a c : ℝ) / n c)) : ℝ) : RobustClock.Circle) = 0
  rw [hk]
  push_cast
  have hnr : (n c : ℝ) ≠ 0 := by exact_mod_cast (hn c).ne'
  have he : (n c : ℝ) * k * ((a c : ℝ) / n c) = ((k * a c : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  exact coe_integer (k * a c)

lemma crt_grid (n : C → ℕ) (hn : ∀ c, 0 < n c)
    (hp : Pairwise (Function.onFun Nat.Coprime n)) (B : ℕ)
    (hB : ∀ c, Nat.Coprime B (n c)) (j : ∀ c, Fin (n c)) :
    ∃ a : ℕ, a < ∏ c, n c ∧ ∀ c,
      ((a * B : ℕ) : ZMod (n c)) = (j c : ℕ) := by
  classical
  have hnprod : 0 < ∏ c, n c := Finset.prod_pos (fun c _ => hn c)
  have : NeZero (∏ c, n c) := ⟨hnprod.ne'⟩
  let b : ∀ c, ZMod (n c) := fun c => ↑((ZMod.unitOfCoprime B (hB c))⁻¹) * (j c : ℕ)
  let r := (ZMod.prodEquivPi n hp).symm b
  refine ⟨r.val, ZMod.val_lt r, fun c => ?_⟩
  have hc := congrFun ((ZMod.prodEquivPi n hp).apply_symm_apply b) c
  rw [ZMod.prodEquivPi_apply] at hc
  have hv : (r.val : ZMod (n c)) = b c := by
    rw [← hc, ← ZMod.natCast_zmod_val r]
    simp [r]
  push_cast
  rw [hv]
  dsimp [b]
  rw [mul_right_comm, ← ZMod.coe_unitOfCoprime B (hB c), Units.inv_mul, one_mul]

lemma net (n : C → ℕ) (hn : ∀ c, 0 < n c)
    (hp : Pairwise (Function.onFun Nat.Coprime n)) (B : ℕ)
    (hB : ∀ c, Nat.Coprime B (n c)) {ε : ℝ}
    (hε : 0 < ε) (hmesh : ∀ c, 1 / (2 * (n c : ℝ)) < ε)
    (v : C → RobustClock.Circle) :
    ∃ a : ℕ, a < ∏ c, n c ∧
      dist (speedMap (fun c => 1 / (n c : ℝ)) (a * B)) v < ε := by
  classical
  choose j hj using fun c => grid_near (n c) (hn c) (-v c)
  obtain ⟨a, ha, hac⟩ := crt_grid n hn hp B hB j
  refine ⟨a, ha, (dist_pi_lt_iff hε).mpr (fun c => ?_)⟩
  have : NeZero (n c) := ⟨(hn c).ne'⟩
  have he : (a * B : ℕ) % n c = (j c : ℕ) := by
    have hv := congrArg ZMod.val (hac c)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (j c).isLt] using hv
  have heZ : ((a * B : ℕ) : ℤ) % (n c : ℤ) = j c := by exact_mod_cast he
  push_cast at heZ
  have hh : speedMap (fun c => 1 / (n c : ℝ)) (a * B) c =
      ((((j c : ℕ) : ℝ) / n c : ℝ) : RobustClock.Circle) := by
    rw [speedMap_apply, mul_one_div, ← coe_mod_fraction (n c) (hn c), heZ]
    simp only [Int.cast_natCast]
  rw [hh, dist_eq_norm]
  have hnorm := hj c
  rw [neg_add_eq_sub] at hnorm
  exact hnorm.trans_lt (hmesh c)

end PeriodicClock

namespace ScheduleCopies

lemma exists_log_linear (A C : ℝ) (hA : 0 < A) :
    ∃ μ : ℕ, 0 < μ ∧ A * Real.log μ + C < μ := by
  have hb := Real.isLittleO_log_id_atTop.bound (div_pos (by norm_num : (0 : ℝ) < 1)
    (mul_pos (by norm_num) hA) : 0 < 1 / (2 * A))
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp hb
  obtain ⟨μ, hμ⟩ := exists_nat_gt (max b (max 1 (2 * C)))
  have hm1 : (1 : ℝ) < μ :=
    (le_trans (le_max_left _ _) (le_max_right b _)).trans_lt hμ
  have hm0 : (0 : ℝ) < μ := lt_trans zero_lt_one hm1
  have hbm : b ≤ (μ : ℝ) := le_of_lt ((le_max_left _ _).trans_lt hμ)
  have hbig : 2 * C < (μ : ℝ) := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hμ)
  have hh := hb (μ : ℝ) hbm
  simp only [id_eq, Real.norm_eq_abs, abs_of_pos hm0] at hh
  have hmain : A * Real.log μ ≤ (μ : ℝ) / 2 := calc
    A * Real.log μ ≤ A * |Real.log μ| := mul_le_mul_of_nonneg_left (le_abs_self _) hA.le
    _ ≤ A * ((1 / (2 * A)) * μ) := mul_le_mul_of_nonneg_left hh hA.le
    _ = (μ : ℝ) / 2 := by field_simp
  exact ⟨μ, by exact_mod_cast hm0, by linarith⟩

lemma exists_log_polynomial (κ D A C : ℝ) (hκ : 0 ≤ κ) (hD : 0 < D) (hA : 0 < A) :
    ∃ μ : ℕ, 0 < μ ∧ A * Real.log (D * (κ * μ + 1) ^ 3) + C < μ := by
  let D' := D * (κ + 1) ^ 3
  have hD' : 0 < D' := by dsimp [D']; positivity
  obtain ⟨μ, hm, hbound⟩ := exists_log_linear (3 * A) (A * Real.log D' + C) (by positivity)
  have hmR : (1 : ℝ) ≤ μ := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < μ := lt_of_lt_of_le zero_lt_one hmR
  have hbase : κ * (μ : ℝ) + 1 ≤ (κ + 1) * μ := by nlinarith
  have hpoly : D * (κ * (μ : ℝ) + 1) ^ 3 ≤ D' * (μ : ℝ) ^ 3 := by
    dsimp [D']
    rw [mul_assoc D, ← mul_pow]
    gcongr
  have hlog : Real.log (D * (κ * (μ : ℝ) + 1) ^ 3) ≤ Real.log D' + 3 * Real.log μ := by
    have hh := Real.log_le_log (by positivity : 0 < D * (κ * (μ : ℝ) + 1) ^ 3) hpoly
    rw [Real.log_mul hD'.ne' (pow_pos hmpos 3).ne', Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  exact ⟨μ, hm, by nlinarith [mul_le_mul_of_nonneg_left hlog hA.le]⟩

end ScheduleCopies

namespace PeriodicClock

open RobustClock
open scoped BigOperators

lemma floor_approx {s ε : ℝ} (hs : 0 < s) (hs1 : s < 1) (hε : 0 < ε)
    {n : ℕ} (hn : max (1 / s) (1 / ε) < (n : ℝ)) :
    1 ≤ ⌊(n : ℝ) * s⌋₊ ∧ ⌊(n : ℝ) * s⌋₊ < n ∧
      |(⌊(n : ℝ) * s⌋₊ : ℝ) / n - s| < ε := by
  have hns : 1 / s < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hne : 1 / ε < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hnpos : (0 : ℝ) < n := (div_pos zero_lt_one hs).trans hns
  have hns' : 1 < (n : ℝ) * s := (div_lt_iff₀ hs).mp hns
  have hns0 : 0 ≤ (n : ℝ) * s := le_of_lt (mul_pos hnpos hs)
  refine ⟨(Nat.one_le_floor_iff _).mpr hns'.le,
    (Nat.floor_lt hns0).mpr (mul_lt_of_lt_one_right hnpos hs1), ?_⟩
  have hf := Nat.floor_le hns0
  have hl := Nat.lt_floor_add_one ((n : ℝ) * s)
  have hle : (⌊(n : ℝ) * s⌋₊ : ℝ) / n ≤ s := (div_le_iff₀ hnpos).mpr (by nlinarith [hf])
  have hmesh : 1 / (n : ℝ) < ε := (div_lt_iff₀ hnpos).mpr (by
    have hh := (div_lt_iff₀ hε).mp hne
    nlinarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  have ha := div_mul_cancel₀ (⌊(n : ℝ) * s⌋₊ : ℝ) hnpos.ne'
  have hb := div_mul_cancel₀ (1 : ℝ) hnpos.ne'
  have hh : -((⌊(n : ℝ) * s⌋₊ : ℝ) / n - s) < 1 / (n : ℝ) := by nlinarith
  exact hh.trans hmesh

lemma approximate_speeds {C : Type uC2} [Fintype C] (v : C → ℝ)
    (hv : ∀ c, 0 < v c ∧ v c < 1) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n a : C → ℕ, Function.Injective n ∧
      (∀ c, Nat.Prime (n c) ∧ L < n c ∧ 1 ≤ a c ∧ a c < n c) ∧
      ∀ c, |(a c : ℝ) / n c - v c| < ε := by
  classical
  choose N hN using fun c => exists_nat_gt (max (1 / v c) (1 / ε))
  obtain ⟨n, hinj, hn⟩ := large_primes (C := C) (max L (Finset.univ.sup N))
  let a := fun c => ⌊(n c : ℝ) * v c⌋₊
  have hclose c := floor_approx (hv c).1 (hv c).2 hε (n := n c) (lt_trans (hN c) (by
    exact_mod_cast lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ c))
      (lt_of_le_of_lt (le_max_right _ _) (hn c).2)))
  exact ⟨n, a, hinj, fun c => ⟨(hn c).1,
    lt_of_le_of_lt (le_max_left _ _) (hn c).2, (hclose c).1, (hclose c).2.1⟩,
    fun c => (hclose c).2.2⟩

lemma dist_coordinate_le {C : Type uC3} (v w : C → ℝ) (z : ℤ) (c : C) :
    dist (speedMap v z c) (speedMap w z c) ≤ |(z : ℝ)| * |v c - w c| := by
  rw [speedMap_apply, speedMap_apply, dist_eq_norm, ← AddCircle.coe_sub]
  exact (norm_coe_le_abs _).trans_eq (by rw [← mul_sub, abs_mul])

lemma approximate_finite {C : Type uC4} [Fintype C] (v : C → ℝ)
    (hv : ∀ c, 0 < v c ∧ v c < 1) (L : ℕ) (F : Finset ℤ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n a : C → ℕ, Function.Injective n ∧
      (∀ c, Nat.Prime (n c) ∧ L < n c ∧ 1 ≤ a c ∧ a c < n c) ∧
      ∀ z ∈ F, dist (speedMap (fun c => (a c : ℝ) / n c) z) (speedMap v z) < ε := by
  classical
  let D : ℝ := (∑ z ∈ F, |(z : ℝ)|) + 1
  have hD : 0 < D := by
    dsimp [D]
    positivity
  obtain ⟨n, a, hn, hna, he⟩ := approximate_speeds v hv L (div_pos hε hD)
  refine ⟨n, a, hn, hna, fun z hz => (dist_pi_lt_iff hε).mpr (fun c => ?_)⟩
  have hzD : |(z : ℝ)| ≤ D := by
    have hzsum := Finset.single_le_sum (fun i (_ : i ∈ F) => abs_nonneg (i : ℝ)) hz
    dsimp [D]
    linarith
  apply (dist_coordinate_le _ _ z c).trans_lt
  calc
    |(z : ℝ)| * |(a c : ℝ) / n c - v c| ≤ D * |(a c : ℝ) / n c - v c| :=
      mul_le_mul_of_nonneg_right hzD (abs_nonneg _)
    _ < D * (ε / D) := mul_lt_mul_of_pos_left (he c) hD
    _ = ε := by field_simp

lemma coprime_product_of_small {C : Type uC5} [Fintype C] (n : C → ℕ)
    (hn : ∀ c, Nat.Prime (n c)) {k : ℕ} (hk : 0 < k) (hkn : ∀ c, k < n c) :
    Nat.Coprime k (∏ c, n c) := by
  apply Nat.Coprime.prod_right
  intro c _
  apply Nat.Coprime.symm
  apply (hn c).coprime_iff_not_dvd.mpr
  intro hd
  exact (not_le_of_gt (hkn c)) (Nat.le_of_dvd hk hd)

end PeriodicClock

namespace SpacedStencil

open scoped BigOperators

lemma exists_points (N : ℕ) (K : ℤ) (U : Fin N → ℤ → Prop)
    (hU : ∀ i L, ∃ z, L < z ∧ U i z) :
    ∃ p : Fin N → ℤ, (∀ i, U i (p i) ∧ K < p i) ∧
      ∀ i j, i < j → 2 * p i + K < p j := by
  classical
  induction N with
  | zero => exact ⟨Fin.elim0, (fun i => Fin.elim0 i), fun i => Fin.elim0 i⟩
  | succ N ih =>
    obtain ⟨p, hp, hg⟩ := ih (fun i => U i.castSucc) (fun i => hU i.castSucc)
    let B : ℤ := (Finset.univ.sup (fun i => (p i).natAbs) : ℕ)
    have hB i : p i ≤ B := by
      have hb : (p i).natAbs ≤ Finset.univ.sup (fun i => (p i).natAbs) :=
        Finset.le_sup (f := fun i => (p i).natAbs) (Finset.mem_univ i)
      have hab : p i ≤ ((p i).natAbs : ℤ) := Int.le_natAbs
      dsimp [B]
      omega
    obtain ⟨q, hq, hqU⟩ := hU (Fin.last N) (max K (2 * B + K))
    refine ⟨Fin.lastCases q p, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using And.intro hqU (lt_of_le_of_lt (le_max_left _ _) hq)
      · simpa using hp i
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro h
        exact False.elim (not_lt_of_ge (Fin.le_last j) h)
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _
          simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
          have hb := hB i
          have hh := lt_of_le_of_lt (le_max_right _ _) hq
          omega
        · simpa only [Fin.lastCases_castSucc, Fin.castSucc_lt_castSucc_iff] using hg i j

variable {I : Type uI} [LinearOrder I] {p : I → ℤ} {K : ℤ}

lemma positive_gap (hK : 0 ≤ K) (hp : ∀ i, K < p i)
    (hg : ∀ i j, i < j → 2 * p i + K < p j) {i j : I} (hij : i < j) :
    K < p j - p i := by
  have h := hg i j hij
  have hi := hp i
  omega

lemma positive_differences (hK : 0 ≤ K) (hp : ∀ i, K < p i)
    (hg : ∀ i j, i < j → 2 * p i + K < p j)
    {i j k l : I} (hji : j < i) (hlk : l < k) (hne : (i, j) ≠ (k, l)) :
    K < |(p i - p j) - (p k - p l)| := by
  rcases lt_trichotomy i k with hik | hik | hki
  · have h1 := hg i k hik
    have h2 := hg l k hlk
    have h3 := hp j
    have hh : (p i - p j) - (p k - p l) < -K := by omega
    exact (lt_abs).mpr (Or.inr (by omega))
  · subst k
    have hjl : j ≠ l := by intro h; exact hne (by simp [h])
    rcases lt_or_gt_of_ne hjl with hjl | hlj
    · have hh := positive_gap hK hp hg hjl
      exact (lt_abs).mpr (Or.inl (by omega))
    · have hh := positive_gap hK hp hg hlj
      exact (lt_abs).mpr (Or.inr (by omega))
  · have h1 := hg k i hki
    have h2 := hg j i hji
    have h3 := hp l
    exact (lt_abs).mpr (Or.inl (by omega))

lemma ordered_differences (hK : 0 ≤ K) (hp : ∀ i, K < p i)
    (hg : ∀ i j, i < j → 2 * p i + K < p j)
    {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hne : (i, j) ≠ (k, l)) :
    K < |(p i - p j) - (p k - p l)| := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · rcases lt_or_gt_of_ne hkl with hkl | hlk
    · have hh := positive_differences hK hp hg hij hkl (by
        intro h
        have hh := Prod.mk.inj h
        exact hne (Prod.ext hh.2 hh.1))
      simpa only [show (p j - p i) - (p l - p k) = -((p i - p j) - (p k - p l)) by ring,
        abs_neg] using hh
    · have h1 := positive_gap hK hp hg hij
      have h2 := positive_gap hK hp hg hlk
      exact (lt_abs).mpr (Or.inr (by omega))
  · rcases lt_or_gt_of_ne hkl with hkl | hlk
    · have h1 := positive_gap hK hp hg hji
      have h2 := positive_gap hK hp hg hkl
      exact (lt_abs).mpr (Or.inl (by omega))
    · exact positive_differences hK hp hg hji hlk hne

lemma nonzero_differences (hK : 0 ≤ K) (hp : ∀ i, K < p i)
    (hg : ∀ i j, i < j → 2 * p i + K < p j) {i j : I} (hij : i ≠ j) :
    K < |p i - p j| := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hh := positive_gap hK hp hg hij
    exact (lt_abs).mpr (Or.inr (by omega))
  · exact (lt_abs).mpr (Or.inl (positive_gap hK hp hg hji))

end SpacedStencil

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace PeriodicClock

open RobustClock
open scoped BigOperators

lemma prime_mesh {C : Type uC} [Fintype C] (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : C → ℕ, Function.Injective n ∧
      (∀ c, Nat.Prime (n c) ∧ B < n c ∧ 1 / (2 * (n c : ℝ)) < ε) := by
  obtain ⟨L, hL⟩ := exists_nat_gt (1 / ε)
  obtain ⟨n, hn, hprime⟩ := large_primes (C := C) (max B L)
  refine ⟨n, hn, fun c => ⟨(hprime c).1,
    lt_of_le_of_lt (le_max_left _ _) (hprime c).2, ?_⟩⟩
  have hl : (1 / ε : ℝ) < n c := hL.trans (by
    exact_mod_cast lt_of_le_of_lt (le_max_right _ _) (hprime c).2)
  have hnpos : (0 : ℝ) < n c := by exact_mod_cast (hprime c).1.pos
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n c)).mpr
  have hh := (div_lt_iff₀ hε).mp hl
  nlinarith

lemma prime_pairwise {C : Type uC2} (n : C → ℕ) (hinj : Function.Injective n)
    (hn : ∀ c, Nat.Prime (n c)) : Pairwise (Function.onFun Nat.Coprime n) := by
  intro i j hij
  apply (hn i).coprime_iff_not_dvd.mpr
  intro hd
  have he : n i = n j := ((hn j).eq_one_or_self_of_dvd (n i) hd).resolve_left (hn i).ne_one
  exact hij (hinj he)

lemma small_coprime {p B : ℕ} (hp : Nat.Prime p) (hB : 0 < B) (hBp : B < p) :
    Nat.Coprime B p := by
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact (not_le_of_gt hBp) (Nat.le_of_dvd hB hd)

lemma unbounded_residue {C : Type uC3} [Fintype C] (n : C → ℕ)
    (hn : ∀ c, 0 < n c) (hp : Pairwise (Function.onFun Nat.Coprime n))
    {B : ℕ} (hB : 0 < B) (hBc : ∀ c, Nat.Coprime B (n c))
    {ε : ℝ} (hε : 0 < ε) (hmesh : ∀ c, 1 / (2 * (n c : ℝ)) < ε)
    (r : ℤ) (v : C → RobustClock.Circle) (L : ℤ) :
    ∃ z : ℤ, L < z ∧ z % B = r % B ∧
      dist (speedMap (fun c => 1 / (n c : ℝ)) z) v < ε := by
  classical
  let φ := speedMap (fun c => 1 / (n c : ℝ))
  let R := ∏ c, n c
  have hR : (0 : ℤ) < R := by exact_mod_cast Finset.prod_pos (fun c _ => hn c)
  have hpR : φ (R : ℤ) = 0 := by
    simpa only [φ, Nat.cast_one] using period n (fun _ => 1) hn
  obtain ⟨a, _, ha⟩ := net n hn hp B hBc hε hmesh (v - φ r)
  let b : ℤ := r + (a : ℤ) * B
  have hb : dist (φ b) v < ε := by
    dsimp [b]
    rw [map_add]
    have hh : v = φ r + (v - φ r) := by abel
    conv_lhs => rw [hh]
    rw [dist_add_left]
    exact ha
  let q : ℤ := |L| + |b| + 1
  let z := b + (q * B) * R
  have hq : 0 < q := by dsimp [q]; positivity
  have hBR : (1 : ℤ) ≤ (B : ℤ) * R := by
    have hB' : (0 : ℤ) < B := by exact_mod_cast hB
    have hh := mul_pos hB' hR
    omega
  have hzl : L < z := by
    have hh := mul_le_mul_of_nonneg_left hBR hq.le
    dsimp [z, q] at *
    have hL := le_abs_self L
    have hbb := neg_abs_le b
    nlinarith
  have hzm : z % B = r % B := by
    dsimp [z, b]
    rw [mul_right_comm q (B : ℤ) (R : ℤ), Int.add_mul_emod_self_right,
      Int.add_mul_emod_self_right]
  refine ⟨z, hzl, hzm, ?_⟩
  have hφz : φ z = φ b := by
    dsimp [z]
    have hmul := map_zsmul φ (q * B) (R : ℤ)
    simp only [zsmul_eq_mul, Int.cast_id] at hmul
    rw [map_add, hmul, hpR, smul_zero, add_zero]
  change dist (φ z) v < ε
  rwa [hφz]

end PeriodicClock

namespace ScheduleClock

open RobustClock PeriodicClock
open scoped BigOperators

theorem exists_stencil_clock {T : Type uT} {C : Type uC4} [Fintype T] [Fintype C]
    (N : ℕ) (S : Specification T (Fin N) C) (B : ℕ) (hB : 0 < B)
    (r : Fin N → ℤ) (lower : (Fin N → ℤ) → ℕ → ℕ) :
    ∃ (R : ℕ) (p : Fin N → ℤ) (n a : C → ℕ),
      0 < R ∧
      (∀ i, p i % B = r i % B ∧ (2 * (B * R) + 2 : ℤ) < p i) ∧
      (∀ i j, i < j → 2 * p i + (2 * (B * R) + 2 : ℤ) < p j) ∧
      Function.Injective n ∧
      (∀ c, Nat.Prime (n c) ∧ lower p (B * R) < n c ∧ 1 ≤ a c ∧ a c < n c) ∧
      (∀ i, dist (speedMap (fun c => (a c : ℝ) / n c) (p i)) (S.v i) < S.η) ∧
      (∀ v : C → RobustClock.Circle, ∃ j : ℕ, j < R ∧
        dist (speedMap (fun c => (a c : ℝ) / n c) (j * B)) v < S.ρ) := by
  classical
  let ε := min (S.ρ / 3) (S.η / 3)
  have hε : 0 < ε := lt_min (div_pos S.radius_pos (by norm_num))
    (div_pos S.tolerance_pos (by norm_num))
  obtain ⟨n₀, hn₀inj, hn₀⟩ := prime_mesh (C := C) B hε
  have hprim c := (hn₀ c).1
  have hn₀pos c := (hprim c).pos
  have hpair := prime_pairwise n₀ hn₀inj hprim
  have hcop c := small_coprime (hprim c) hB (hn₀ c).2.1
  let R := ∏ c, n₀ c
  have hR : 0 < R := Finset.prod_pos (fun c _ => hn₀pos c)
  obtain ⟨p, hp, hspread⟩ := SpacedStencil.exists_points N (2 * (B * R : ℕ) + 2)
    (fun i z => z % B = r i % B ∧
      dist (speedMap (fun c => 1 / (n₀ c : ℝ)) z) (S.v i) < ε)
    (fun i L => unbounded_residue n₀ hn₀pos hpair hB hcop hε
      (fun c => (hn₀ c).2.2) (r i) (S.v i) L)
  let F : Finset ℤ := Finset.univ.image p ∪ (Finset.range R).image (fun j => (j * B : ℕ))
  have hs c : 0 < (1 / (n₀ c : ℝ)) ∧ 1 / (n₀ c : ℝ) < 1 := by
    have hh : (1 : ℝ) < n₀ c := by exact_mod_cast (hprim c).one_lt
    exact ⟨by positivity, (div_lt_one (by positivity)).mpr hh⟩
  obtain ⟨n, a, hn, hna, hclose⟩ := approximate_finite (fun c => 1 / (n₀ c : ℝ)) hs
    (lower p (B * R)) F hε
  refine ⟨R, p, n, a, hR, fun i => ⟨(hp i).1.1, (hp i).2⟩, hspread,
    hn, hna, ?_, ?_⟩
  · intro i
    have hc := hclose (p i) (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, rfl⟩))
    have ht := (dist_triangle _ _ _).trans_lt (add_lt_add hc (hp i).1.2)
    have he : ε ≤ S.η / 3 := min_le_right _ _
    exact ht.trans (by linarith [S.tolerance_pos])
  · intro v
    obtain ⟨j, hj, hjv⟩ := net n₀ hn₀pos hpair B hcop hε (fun c => (hn₀ c).2.2) v
    have hc := hclose ((j * B : ℕ) : ℤ) (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr hj, rfl⟩))
    refine ⟨j, hj, ?_⟩
    have ht := (dist_triangle _ _ _).trans_lt (add_lt_add hc hjv)
    have he : ε ≤ S.ρ / 3 := min_le_left _ _
    exact ht.trans (by linarith [S.radius_pos])

end ScheduleClock

namespace EpisodeEnd

open LocalMarkers

variable {Alphabet : Type uAlphabet}

def FirstMismatch (w v : ℤ → Alphabet) (z : ℤ) (K : ℕ) (q : ℤ) : Prop :=
  z + K ≤ q ∧ w q ≠ v q ∧ AgreesOn w v z q

lemma firstMismatch_unique {w v : ℤ → Alphabet} {z z' q q' : ℤ} {K : ℕ}
    (h : FirstMismatch w v z K q) (h' : FirstMismatch w v z' K q')
    (hover : |z - z'| < K) : q = q' := by
  have hq := h.1
  have hq' := h'.1
  have hz : z ≤ q' := by
    have hh := (abs_lt.mp hover).2
    omega
  have hz' : z' ≤ q := by
    have hh := (abs_lt.mp hover).1
    omega
  rcases lt_trichotomy q q' with hq | hq | hq
  · exact False.elim (h.2.1 (h'.2.2 q hz' hq))
  · exact hq
  · exact False.elim (h'.2.1 (h.2.2 q' hz hq))

lemma shortCont_congr {d K : ℕ} {w w' v : ℤ → Alphabet} {z : ℤ}
    (he : AgreesOn w w' z (z + K)) :
    ShortContinuation d K w z v ↔ ShortContinuation d K w' z v := by
  constructor <;> intro h
  · refine ⟨h.1, fun x hx hx' => ?_⟩
    exact (he x hx hx').symm.trans (h.2 x hx hx')
  · refine ⟨h.1, fun x hx hx' => ?_⟩
    exact (he x hx hx').trans (h.2 x hx hx')

def EndAt (d K : ℕ) (tail : ℤ) (w : ℤ → Alphabet) (z : ℤ)
    (η : Option ℤ) (b : ℤ) : Prop :=
  match η with
  | some q => b = q + tail
  | none => ∃ v, ShortContinuation d K w z v ∧ FirstMismatch w v z K (b - tail)

def clockAnchor (ζ : Option ℤ) (b tail : ℤ) : ℤ := ζ.getD (b - tail)

lemma EndAt.unique {d K : ℕ} {tail z b b' : ℤ} {w : ℤ → Alphabet} {η : Option ℤ}
    (hK : (d : ℤ) ^ 2 ≤ K) (hKpos : 0 < K)
    (h : EndAt d K tail w z η b) (h' : EndAt d K tail w z η b') : b = b' := by
  cases η with
  | some q => exact h.trans h'.symm
  | none =>
    obtain ⟨v, hv, hm⟩ := h
    obtain ⟨v', hv', hm'⟩ := h'
    have he := short_continuations_equal hv hv' (by simpa using hK)
    subst v'
    have hh := firstMismatch_unique hm hm' (by simpa using hKpos)
    omega

lemma shared_end {d K : ℕ} {tail s z z' b b' : ℤ}
    {w w' : ℤ → Alphabet} {η : Option ℤ}
    (htail : 0 < tail) (hover : (d : ℤ) ^ 2 ≤ (K : ℤ) - |z - z'|)
    (hover' : |z - z'| < K)
    (hseed : s ≤ z ∧ z + K ≤ min b b' ∧ s ≤ z' ∧ z' + K ≤ min b b')
    (he : AgreesOn w w' s (min b b'))
    (h : EndAt d K tail w z η b) (h' : EndAt d K tail w' z' η b') :
    b = b' := by
  cases η with
  | some q => exact h.trans h'.symm
  | none =>
    obtain ⟨v, hv, hm⟩ := h
    obtain ⟨v', hv', hm'⟩ := h'
    have hseed' : AgreesOn w w' z' (z' + K) := by
      intro x hx hx'
      exact he x (hseed.2.2.1.trans hx) (lt_of_lt_of_le hx' hseed.2.2.2)
    have hvw : ShortContinuation d K w z' v' := (shortCont_congr hseed').mpr hv'
    have hvv := short_continuations_equal hv hvw hover
    subst v'
    have hmlo := hm.1
    have hmlo' := hm'.1
    have hz : z ≤ b' - tail := by
      have hh := (abs_lt.mp hover').2
      omega
    have hz' : z' ≤ b - tail := by
      have hh := (abs_lt.mp hover').1
      omega
    rcases lt_trichotomy b b' with hb | hb | hb
    · have hq : b - tail < b' - tail := by omega
      have hqbounds : s ≤ b - tail ∧ b - tail < min b b' := by omega
      have hletter := he (b - tail) hqbounds.1 hqbounds.2
      exact False.elim (hm.2.1 (hletter.trans (hm'.2.2 _ hz' hq)))
    · exact hb
    · have hq : b' - tail < b - tail := by omega
      have hqbounds : s ≤ b' - tail ∧ b' - tail < min b b' := by omega
      have hletter := he (b' - tail) hqbounds.1 hqbounds.2
      exact False.elim (hm'.2.1 (hletter.symm.trans (hm.2.2 _ hz hq)))

lemma transfer_end {d K : ℕ} {tail z z' b : ℤ} {w : ℤ → Alphabet} {η : Option ℤ}
    (hover : (d : ℤ) ^ 2 ≤ (K : ℤ) - |z - z'|)
    (hover' : |z - z'| < K)
    (hseed : η = none → ∃ v', ShortContinuation d K w z' v')
    (h : EndAt d K tail w z η b) : EndAt d K tail w z' η b := by
  cases η with
  | some q => exact h
  | none =>
    obtain ⟨v, hv, hm⟩ := h
    obtain ⟨v', hv'⟩ := hseed rfl
    have he := short_continuations_equal hv hv' hover
    subst v'
    refine ⟨v, hv', ?_⟩
    have hmlo := hm.1
    have hz' : z' ≤ b - tail := by
      have hh := (abs_lt.mp hover').1
      omega
    have hq : z' + K ≤ b - tail := by
      by_contra hn
      exact hm.2.1 (hv'.2 _ hz' (by omega))
    refine ⟨hq, hm.2.1, fun x hx hx' => ?_⟩
    by_cases hxz : z ≤ x
    · exact hm.2.2 x hxz hx'
    · apply hv'.2 x hx
      have hh := (abs_lt.mp hover').2
      omega

end EpisodeEnd

namespace LocalMarkers

variable (Alphabet : Type uAlphabet2) (d K : ℕ)

structure Rule where
  r : ℤ
  radius_ge : (K : ℤ) ≤ r
  markers : (ℤ → Alphabet) → Set ℤ
  separated : ∀ w x, x ∈ markers w → ∀ y, y ∈ markers w → x ≠ y →
    (d : ℤ) ≤ |x - y|
  locality : ∀ w w' x, AgreesOn w w' (x - r) (x + r) →
    (x ∈ markers w ↔ x ∈ markers w')
  translate : ∀ w a x, x ∈ markers (fun i => w (i + a)) ↔ x + a ∈ markers w
  periodic : ∀ w z, (∀ x : ℤ, z - d ≤ x → x ≤ z + d → x ∉ markers w) →
    ∃ a : ℕ, 0 < a ∧ a < d ∧ Period (fun i : Fin K => w (z + i.val)) a

lemma nonempty_rule [Fintype Alphabet] (hd : 2 ≤ d) (hK : 3 * d ^ 2 < K) :
    Nonempty (Rule Alphabet d K) := by
  obtain ⟨r, hr, m, hsep, hloc, htrans, hper⟩ := exists_markers (Alphabet := Alphabet) hd hK
  exact ⟨⟨r, hr, m, hsep, hloc, htrans, hper⟩⟩

end LocalMarkers

namespace EndSearch

open LocalMarkers

lemma search_congr {S S' : Set ℤ} {B D a z : ℤ}
    (he : ∀ m, z - (a + (B - 1) * D) ≤ m → m ≤ z + (a + (B - 1) * D) →
      (m ∈ S ↔ m ∈ S')) : search S B D a z = search S' B D a z := by
  have hf : eligibleSet S B D a z = eligibleSet S' B D a z := by
    ext m
    simp only [eligibleSet, Finset.mem_filter, Finset.mem_Icc, Eligible]
    constructor
    · rintro ⟨⟨hl, hr⟩, hm, hw⟩
      exact ⟨⟨hl, hr⟩, (he m hl hr).mp hm, hw⟩
    · rintro ⟨⟨hl, hr⟩, hm, hw⟩
      exact ⟨⟨hl, hr⟩, (he m hl hr).mpr hm, hw⟩
  simp only [search, hf]

lemma search_local {Alphabet : Type uAlphabet3} {d K : ℕ} (R : Rule Alphabet d K)
    (B D a z : ℤ) {w w' : ℤ → Alphabet}
    (he : AgreesOn w w' (z - (a + (B - 1) * D) - R.r)
      (z + (a + (B - 1) * D) + R.r)) :
    search (R.markers w) B D a z = search (R.markers w') B D a z := by
  apply search_congr
  intro m hm hm'
  apply R.locality
  intro x hx hx'
  exact he x (by omega) (by omega)

lemma absent_continuation {Alphabet : Type uAlphabet4} {d K : ℕ} (R : Rule Alphabet d K)
    (hK : d ≤ K) {B D z : ℤ} {w : ℤ → Alphabet} (hB : 0 < B) (hD : 0 ≤ D)
    (hn : search (R.markers w) B D d z = none) :
    ∃ v, ShortContinuation d K w z v := by
  apply short_continuation_exists hK
  apply R.periodic
  intro m hlo hhi hm
  apply (search_none hB hD).mp hn m
  exact ⟨hm, (abs_le.mpr (show -(d : ℤ) ≤ m - z ∧ m - z ≤ d by omega)).trans
    (width_bounds hB hD).1⟩

end EndSearch

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace WordIntervals

open LocalMarkers

variable {Alphabet : Type uAlphabet}

def segment (f : ℤ → Alphabet) (s : ℤ) (n : ℕ) : List Alphabet :=
  List.ofFn (fun i : Fin n => f (s + i.val))

@[simp] lemma length_segment (f : ℤ → Alphabet) (s : ℤ) (n : ℕ) :
    (segment f s n).length = n := List.length_ofFn

lemma segment_add (f : ℤ → Alphabet) (s : ℤ) (n m : ℕ) :
    segment f s (n + m) = segment f s n ++ segment f (s + n) m := by
  rw [segment, List.ofFn_add]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  congr 1
  simp only [Fin.val_natAdd, Nat.cast_add]
  omega

lemma segment_congr {f g : ℤ → Alphabet} {s : ℤ} {n : ℕ}
    (he : AgreesOn f g s (s + n)) : segment f s n = segment g s n := by
  apply List.ofFn_inj.mpr
  funext i
  exact he _ (by omega) (by omega)

lemma segment_translate (f : ℤ → Alphabet) (s a : ℤ) (n : ℕ) :
    segment (fun x => f (x + a)) s n = segment f (s + a) n := by
  apply List.ofFn_inj.mpr
  funext i
  change f (s + (i.val : ℤ) + a) = f (s + a + i.val)
  congr 1
  omega

def Realizes (w : List Alphabet) (s : ℤ) (f : ℤ → Alphabet) : Prop :=
  ∀ i : Fin w.length, f (s + i.val) = w[i.val]

lemma realizes_iff_segment {w : List Alphabet} {s : ℤ} {f : ℤ → Alphabet} :
    Realizes w s f ↔ segment f s w.length = w := by
  constructor
  · intro h
    calc
      segment f s w.length = List.ofFn (fun i : Fin w.length => w[i.val]) :=
        List.ofFn_inj.mpr (funext h)
      _ = w := List.ofFn_getElem
  · intro h i
    have he := congrArg (fun w => w[i.val]?) h
    simpa [segment, List.getElem?_eq_getElem, i.isLt] using he

lemma realizes_segment (f : ℤ → Alphabet) (s : ℤ) (n : ℕ) :
    Realizes (segment f s n) s f := by
  apply realizes_iff_segment.mpr
  simp

lemma realizes_exists [Nonempty Alphabet] (w : List Alphabet) (s : ℤ) :
    ∃ f, Realizes w s f := by
  classical
  let f (x : ℤ) : Alphabet :=
    if h : 0 ≤ x - s ∧ x - s < w.length then
      w[(x - s).toNat]'(by omega) else Classical.choice inferInstance
  refine ⟨f, fun i => ?_⟩
  dsimp [f]
  simp only [add_sub_cancel_left, Nat.cast_nonneg, i.isLt, Nat.cast_lt, and_self, dite_true,
    Int.toNat_natCast]

lemma Realizes.prefix {u v : List Alphabet} {s : ℤ} {f : ℤ → Alphabet}
    (h : Realizes v s f) (hp : u <+: v) : Realizes u s f := by
  intro i
  exact (h ⟨i.val, lt_of_lt_of_le i.isLt hp.length_le⟩).trans (hp.getElem i.isLt).symm

lemma Realizes.agrees {u v : List Alphabet} {s : ℤ} {f g : ℤ → Alphabet}
    (hf : Realizes u s f) (hg : Realizes v s g) (hp : u <+: v) :
    AgreesOn f g s (s + u.length) := by
  have hg' := hg.prefix hp
  intro x hx hx'
  let i : Fin u.length := ⟨(x - s).toNat, by omega⟩
  have hi : s + (i.val : ℤ) = x := by dsimp [i]; omega
  exact hi ▸ (hf i).trans (hg' i).symm

lemma Realizes.append {u v : List Alphabet} {s : ℤ} {f : ℤ → Alphabet}
    (hu : Realizes u s f) (hv : Realizes v (s + u.length) f) : Realizes (u ++ v) s f := by
  apply realizes_iff_segment.mpr
  rw [List.length_append, segment_add, realizes_iff_segment.mp hu, realizes_iff_segment.mp hv]

lemma Realizes.append_left {u v : List Alphabet} {s : ℤ} {f : ℤ → Alphabet}
    (h : Realizes (u ++ v) s f) : Realizes u s f := h.prefix ⟨v, rfl⟩

lemma Realizes.append_right {u v : List Alphabet} {s : ℤ} {f : ℤ → Alphabet}
    (h : Realizes (u ++ v) s f) : Realizes v (s + u.length) f := by
  intro i
  have he := h ⟨u.length + i.val, by simp only [List.length_append]; omega⟩
  change f (s + ((u.length + i.val : ℕ) : ℤ)) = (u ++ v)[u.length + i.val] at he
  have hp : s + ((u.length + i.val : ℕ) : ℤ) = s + u.length + i.val := by push_cast; ring
  rw [hp, List.getElem_append_right (show u.length ≤ u.length + i.val by omega)] at he
  simpa only [Nat.add_sub_cancel_left] using he

def piece (f : ℤ → Alphabet) (s t : ℤ) : List Alphabet := segment f s (t - s).toNat

lemma length_piece {f : ℤ → Alphabet} {s t : ℤ} (hst : s ≤ t) :
    ((piece f s t).length : ℤ) = t - s := by
  simp only [piece, length_segment]
  exact Int.toNat_of_nonneg (by omega)

lemma piece_append (f : ℤ → Alphabet) {s t u : ℤ} (hst : s ≤ t) (htu : t ≤ u) :
    piece f s u = piece f s t ++ piece f t u := by
  have hn : (u - s).toNat = (t - s).toNat + (u - t).toNat := by omega
  have hs : s + ((t - s).toNat : ℤ) = t := by omega
  simp only [piece, hn, segment_add, hs]

lemma piece_congr {f g : ℤ → Alphabet} {s t : ℤ} (hst : s ≤ t)
    (he : AgreesOn f g s t) : piece f s t = piece g s t := by
  apply segment_congr
  have hs : s + ((t - s).toNat : ℤ) = t := by omega
  simpa only [hs] using he

lemma realizes_piece {f : ℤ → Alphabet} {w : List Alphabet} {s : ℤ}
    (h : Realizes w s f) : piece f s (s + w.length) = w := by
  simpa only [piece, add_sub_cancel_left, Int.toNat_natCast] using realizes_iff_segment.mp h

variable {M : Type uM} [Monoid M]

def product (h : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet) (s t : ℤ) : M := h (piece f s t)

lemma product_append (h : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {s t u : ℤ} (hst : s ≤ t) (htu : t ≤ u) :
    product h f s u = product h f s t * product h f t u := by
  unfold product
  rw [piece_append f hst htu]
  exact map_mul h _ _

lemma product_congr (h : FreeMonoid Alphabet →* M) {f g : ℤ → Alphabet} {s t : ℤ}
    (hst : s ≤ t) (he : AgreesOn f g s t) : product h f s t = product h g s t :=
  congrArg h (piece_congr hst he)

end WordIntervals

namespace CanonicalEpisodes

open LocalMarkers WordIntervals EpisodeEnd

variable {Alphabet : Type uAlphabet2}

structure Parameters (Alphabet : Type uAlphabet3) where
  B : ℤ
  S : ℤ
  d : ℕ
  K : ℕ
  offset : ℤ
  tail : ℤ
  rule : Rule Alphabet d K
  B_pos : 0 < B
  S_nonneg : 0 ≤ S
  d_ge : 2 ≤ d
  seed_long : 3 * d ^ 2 < K
  tail_pos : 0 < tail

namespace Parameters

variable (C : Parameters Alphabet)

def width : ℤ := 3 * C.d + (C.B - 1) * C.S

noncomputable def small (f : ℤ → Alphabet) (z : ℤ) : Option ℤ :=
  EndSearch.search (C.rule.markers f) C.B C.S C.d z

noncomputable def large (f : ℤ → Alphabet) (z : ℤ) : Option ℤ :=
  EndSearch.search (C.rule.markers f) C.B C.S (3 * C.d) z

def Visible (s b z : ℤ) : Prop :=
  s ≤ z - C.width - C.rule.r ∧ z + C.width + C.rule.r ≤ b ∧
    s ≤ z ∧ z + C.K ≤ b

lemma Visible.mono {s b s' b' z : ℤ} (h : C.Visible s b z)
    (hs : s' ≤ s) (hb : b ≤ b') : C.Visible s' b' z := by
  rcases h with ⟨h₁,h₂,h₃,h₄⟩
  exact ⟨hs.trans h₁,h₂.trans hb,hs.trans h₃,h₄.trans hb⟩

lemma width_nonneg : 0 ≤ C.width := by
  have hB : 0 ≤ C.B - 1 := by have := C.B_pos; omega
  have hS := C.S_nonneg
  dsimp [width]
  positivity

lemma small_width_le : (C.d : ℤ) + (C.B - 1) * C.S ≤ C.width := by
  dsimp [width]
  omega

lemma searches_congr {f g : ℤ → Alphabet} {s b z : ℤ}
    (hv : C.Visible s b z) (he : AgreesOn f g s b) :
    C.small f z = C.small g z ∧ C.large f z = C.large g z := by
  have hw := C.small_width_le
  rcases hv with ⟨hv₁,hv₂,hv₃,hv₄⟩
  constructor
  · apply EndSearch.search_local C.rule
    intro x hx hx'
    exact he x (by omega) (by omega)
  · apply EndSearch.search_local C.rule
    intro x hx hx'
    exact he x (by dsimp [width] at hv₁; omega) (by dsimp [width] at hv₂; omega)

lemma seed_pos : 0 < C.K := lt_of_le_of_lt (Nat.zero_le _) C.seed_long

lemma seed_square : (C.d : ℤ) ^ 2 ≤ C.K := by
  have hh := C.seed_long
  have hn : C.d ^ 2 ≤ C.K := by omega
  exact_mod_cast hn

def complete (lag : ℤ) : Language Alphabet :=
  {w | ∃ f : ℤ → Alphabet, Realizes w 0 f ∧
    C.Visible 0 w.length (lag + C.offset) ∧
    EndAt C.d C.K C.tail f (lag + C.offset) (C.small f (lag + C.offset)) w.length}

lemma not_nil (lag : ℤ) : [] ∉ C.complete lag := by
  rintro ⟨f,hf,hv,he⟩
  have hp := C.seed_pos
  have h₁ := hv.2.2.1
  have h₂ := hv.2.2.2
  simp only [List.length_nil, Nat.cast_zero] at h₁ h₂
  omega

lemma prefix_code (lag : ℤ) : EpisodeAlgebra.PrefixCode (C.complete lag) := by
  refine ⟨C.not_nil lag, ?_⟩
  rintro u ⟨f,hf,hvf,hu⟩ v ⟨g,hg,hvg,hv⟩ hp
  have hl := hp.length_le
  have he : AgreesOn f g 0 (u.length : ℤ) := by simpa using hf.agrees hg hp
  have hη := (C.searches_congr hvf he).1
  have hmin : min (u.length : ℤ) (v.length : ℤ) = u.length := min_eq_left (by exact_mod_cast hl)
  have hseed : 0 ≤ (lag + C.offset) ∧ (lag + C.offset) + C.K ≤ min (u.length : ℤ) v.length ∧
      0 ≤ (lag + C.offset) ∧ (lag + C.offset) + C.K ≤ min (u.length : ℤ) v.length := by
    rw [hmin]
    exact ⟨hvf.2.2.1,hvf.2.2.2,hvf.2.2.1,hvf.2.2.2⟩
  have heq := shared_end C.tail_pos (by simpa using C.seed_square)
    (by simpa using C.seed_pos) hseed (by simpa [hmin] using he) hu (hη ▸ hv)
  exact hp.eq_of_length (by exact_mod_cast heq)

def Guard (O : Finset ℤ) (reference s b : ℤ) (f : ℤ → Alphabet) : Prop :=
  reference ∈ O ∧ (∀ t ∈ O, C.Visible s b (t + C.offset)) ∧
    (∀ t ∈ O, C.small f (t + C.offset) = C.small f (reference + C.offset) ∧
      C.large f (t + C.offset) = C.large f (reference + C.offset)) ∧
    EndAt C.d C.K C.tail f (reference + C.offset)
      (C.small f (reference + C.offset)) b

lemma guard_shared_end {O : Finset ℤ} {reference t s b b' : ℤ}
    {f g : ℤ → Alphabet}
    (ht : t ∈ O) (hguard : C.Guard O reference s b' g)
    (hvis : ∀ t' ∈ O, C.Visible s b (t' + C.offset))
    (he : AgreesOn f g s (min b b'))
    (hover : (C.d : ℤ)^2 ≤ (C.K : ℤ) - |t - reference|)
    (hover' : |t - reference| < C.K)
    (hend : EndAt C.d C.K C.tail f (t + C.offset) (C.small f (t + C.offset)) b) :
    b = b' ∧ clockAnchor (C.large f (t + C.offset)) b C.tail =
      clockAnchor (C.large g (reference + C.offset)) b' C.tail := by
  have hvt := hvis t ht
  have hvt' := hguard.2.1 t ht
  have hvr := hvis reference hguard.1
  have hvr' := hguard.2.1 reference hguard.1
  have hvtmin : C.Visible s (min b b') (t + C.offset) := by
    exact ⟨hvt.1, le_min hvt.2.1 hvt'.2.1, hvt.2.2.1, le_min hvt.2.2.2 hvt'.2.2.2⟩
  have hsearch := C.searches_congr hvtmin he
  have hη := hsearch.1.trans (hguard.2.2.1 t ht).1
  have hζ := hsearch.2.trans (hguard.2.2.1 t ht).2
  have hseed : s ≤ t + C.offset ∧ t + C.offset + C.K ≤ min b b' ∧
      s ≤ reference + C.offset ∧ reference + C.offset + C.K ≤ min b b' :=
    ⟨hvt.2.2.1, le_min hvt.2.2.2 hvt'.2.2.2,
      hvr.2.2.1, le_min hvr.2.2.2 hvr'.2.2.2⟩
  have hh : (t + C.offset) - (reference + C.offset) = t - reference := by ring
  have hb := shared_end C.tail_pos (by simpa only [hh] using hover)
    (by simpa only [hh] using hover') hseed he hend (hη ▸ hguard.2.2.2)
  exact ⟨hb, by rw [hb,hζ]⟩

lemma guard_available {O : Finset ℤ} {reference t s b : ℤ} {f : ℤ → Alphabet}
    (hr : reference ∈ O)
    (hvis : ∀ t' ∈ O, C.Visible s b (t' + C.offset))
    (hstable : ∀ t' ∈ O, C.small f (t' + C.offset) = C.small f (t + C.offset) ∧
      C.large f (t' + C.offset) = C.large f (t + C.offset))
    (hover : (C.d : ℤ)^2 ≤ (C.K : ℤ) - |t - reference|)
    (hover' : |t - reference| < C.K)
    (hend : EndAt C.d C.K C.tail f (t + C.offset) (C.small f (t + C.offset)) b) :
    C.Guard O reference s b f := by
  have href := hstable reference hr
  refine ⟨hr,hvis,fun t' ht' => ⟨(hstable t' ht').1.trans href.1.symm,
    (hstable t' ht').2.trans href.2.symm⟩, ?_⟩
  rw [href.1]
  have hh : (t + C.offset) - (reference + C.offset) = t - reference := by ring
  apply transfer_end (by simpa only [hh] using hover) (by simpa only [hh] using hover')
    (h := hend)
  intro hn
  apply EndSearch.absent_continuation C.rule (by nlinarith [C.seed_long]) C.B_pos C.S_nonneg
  exact href.1.trans hn

end Parameters

end CanonicalEpisodes

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace SplitMetadata

variable {M : Type uM} {S : Type uS} {K : Type uK} [Field K] [AddCommGroup S] [Module K S]

abbrev Omitted (M : Type uM2) (g : ℕ) (j : Fin g) := {i : Fin g // i ≠ j} → M

def insert {g : ℕ} (j : Fin g) (d : Omitted M g j) (a : M) : Fin g → M :=
  fun i => if h : i = j then a else d ⟨i,h⟩

@[simp] lemma insert_at {g : ℕ} (j : Fin g) (d : Omitted M g j) (a : M) :
    insert j d a j = a := by simp [insert]

lemma insert_away {g : ℕ} (j i : Fin g) (d : Omitted M g j) (a : M) (h : i ≠ j) :
    insert j d a i = d ⟨i,h⟩ := by simp [insert,h]

lemma insert_actual {g : ℕ} (j : Fin g) (d : Fin g → M) :
    insert j (fun i => d i) (d j) = d := by
  funext i
  by_cases h : i = j <;> simp [insert,h]

lemma insert_eq_update {g : ℕ} (j : Fin g) (d : Fin g → M) (a : M) :
    insert j (fun i => d i) a = Function.update d j a := by
  funext i
  by_cases h : i = j <;> simp [insert,h]

structure MainTag (M : Type uM3) (S : Type uS2) (g B : ℕ) where
  j : Fin g
  u : Fin B
  A : M
  C : M
  entries : Omitted M g j
  input : S
  output : S

noncomputable instance [Fintype M] [Fintype S] {g B : ℕ} : Fintype (MainTag M S g B) := by
  classical
  apply Fintype.ofInjective (fun t : MainTag M S g B =>
    (⟨t.j, (t.u,t.A,t.C,t.entries,t.input,t.output)⟩ :
      Σ j : Fin g, Fin B × M × M × Omitted M g j × S × S))
  intro a b he
  cases a with | mk aj au aa ac ad ax ay =>
    cases b with | mk bj bu ba bc bd bx byy =>
      have hj : aj = bj := congrArg Sigma.fst he
      subst bj
      have hh : (au,aa,ac,ad,ax,ay) = (bu,ba,bc,bd,bx,byy) :=
        eq_of_heq (Sigma.mk.inj_iff.mp he).2
      simp only [Prod.mk.injEq] at hh
      rcases hh with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      rfl

structure PeriodicTag (M : Type uM4) (S : Type uS3) (g B : ℕ) where
  j : Fin (g + 1)
  u : Fin B
  prefixProduct : M
  input : S
  output : S
  deriving Fintype

abbrev Tag (M : Type uM5) (S : Type uS4) (g B : ℕ) := MainTag M S g B ⊕ PeriodicTag M S g B

def Tag.input {g B : ℕ} : Tag M S g B → S
  | .inl a => a.input
  | .inr a => a.input

def Tag.output {g B : ℕ} : Tag M S g B → S
  | .inl a => a.output
  | .inr a => a.output

def Tag.residue {g B : ℕ} : Tag M S g B → Fin B
  | .inl a => a.u
  | .inr a => a.u

structure Kind (M : Type uM6) (S : Type uS5) (K : Type uK2) [CommSemiring K] [AddCommMonoid S] [Module K S] (g : ℕ) where
  j : Fin g
  input : S
  output : S
  entries : Omitted M g j
  hypothetical : M → (S →ₗ[K] S)

noncomputable instance [Fintype M] [Fintype S] {g : ℕ} : Fintype (Kind M S K g) := by
  classical
  apply Fintype.ofInjective (fun t : Kind M S K g =>
    (⟨t.j, (t.input,t.output,t.entries, fun a x => t.hypothetical a x)⟩ :
      Σ j : Fin g, S × S × Omitted M g j × (M → S → S)))
  intro a b he
  cases a with | mk aj ax ay ad af =>
    cases b with | mk bj bx byy bd bf =>
      have hj : aj = bj := congrArg Sigma.fst he
      subst bj
      have hh : (ax,ay,ad,fun a x => af a x) = (bx,byy,bd,fun a x => bf a x) :=
        eq_of_heq (Sigma.mk.inj_iff.mp he).2
      have hp := Prod.mk.inj hh
      have hp' := Prod.mk.inj hp.2
      have hp'' := Prod.mk.inj hp'.2
      have hf : af = bf := by
        funext a
        ext x
        exact congrFun (congrFun hp''.2 a) x
      cases hp.1; cases hp'.1; cases hp''.1; cases hf
      rfl

abbrev Roster (M : Type uM7) (S : Type uS6) (K : Type uK3) [CommSemiring K] [AddCommMonoid S] [Module K S]
    (g μ : ℕ) := Kind M S K g × Fin μ

lemma certificate_at_actual {g : ℕ} (f : (Fin g → M) → (S →ₗ[K] S))
    (β : (Fin g → M) → S) (d : Fin g → M) (j : Fin g) (x y : S)
    (h : ∀ a, f (insert j (fun i => d i) a) x + β (insert j (fun i => d i) a) = y) :
    f d x + β d = y := by
  simpa only [insert_actual] using h (d j)

lemma certificate_available {g : ℕ} (f : (Fin g → M) → (S →ₗ[K] S))
    (β : (Fin g → M) → S) (hβ : ShiftTableProperty g f β)
    (d : Fin g → M) (x : S) :
    ∃ j : Fin g, ∀ a, f (insert j (fun i => d i) a) x +
      β (insert j (fun i => d i) a) = f d x + β d := by
  obtain ⟨j,hj⟩ := hβ d x
  exact ⟨j, fun a => by simpa only [insert_eq_update] using hj a⟩

end SplitMetadata

namespace IntegerSchedules

lemma multiple_gt (B : ℤ) (hB : 0 < B) (L : ℤ) :
    ∃ x : ℤ, 0 < x ∧ B ∣ x ∧ L < x := by
  refine ⟨B * (|L| + 1), mul_pos hB (by positivity), dvd_mul_right B _, ?_⟩
  have hBn : 1 ≤ B := hB
  have habs := le_abs_self L
  have ha := abs_nonneg L
  nlinarith

structure Inner (B n R size d K : ℕ) (r h : ℤ) where
  lag : ℤ
  extension : ℤ
  H : Fin B → ℤ
  Hmax : ℤ
  halfGap : ℤ
  lag_pos : 0 < lag
  lag_multiple : (B : ℤ) ∣ lag
  lag_bound : r + (size + 2 : ℕ) * (d : ℤ) < lag
  extension_bound : lag + (n * d * size.factorial * B : ℕ) + 2 * d < extension
  H_pos : ∀ u, 0 < H u
  H_multiple : ∀ u, (B : ℤ) ∣ H u
  H_large : ∀ u, 2 * (d : ℤ) < H u
  H_bounded : ∀ u, H u ≤ Hmax
  H_separated : ∀ u v, u ≠ v →
    2 * h + 2 * max extension (B * R : ℕ) + 2 < |H u - H v|
  gap_pos : 0 < halfGap
  gap_multiple : (B : ℤ) ∣ halfGap
  gap_bound : 10 * (Hmax + extension + r + K + d + (B * R : ℕ) + 1) < 2 * halfGap

lemma exists_inner (B n R size d K : ℕ) (r h : ℤ) (hB : 0 < B) :
    Nonempty (Inner B n R size d K r h) := by
  have hBi : (0 : ℤ) < B := by exact_mod_cast hB
  obtain ⟨lag,hlag,hlagB,hlagbound⟩ := multiple_gt B hBi (r + (size + 2 : ℕ) * (d : ℤ))
  let extension : ℤ := lag + (n * d * size.factorial * B : ℕ) + 2 * d + 1
  obtain ⟨base,hbase,hbaseB,hbasebound⟩ := multiple_gt B hBi (2 * d)
  obtain ⟨step,hstep,hstepB,hstepbound⟩ := multiple_gt B hBi
    (2 * h + 2 * max extension (B * R : ℕ) + 2)
  let H (u : Fin B) : ℤ := base + u.val * step
  let Hmax : ℤ := base + (B - 1 : ℕ) * step
  obtain ⟨gap,hgap,hgapB,hgapbound⟩ := multiple_gt B hBi
    (10 * (Hmax + extension + r + K + d + (B * R : ℕ) + 1))
  refine ⟨⟨lag,extension,H,Hmax,gap,hlag,hlagB,hlagbound,?_,?_,?_,?_,?_,?_,
    hgap,hgapB,by omega⟩⟩
  · dsimp [extension]; omega
  · intro u; dsimp [H]; positivity
  · intro u
    exact dvd_add hbaseB (dvd_mul_of_dvd_right hstepB _)
  · intro u
    dsimp [H]
    have hh : 0 ≤ (u.val : ℤ) * step := mul_nonneg (by positivity) hstep.le
    omega
  · intro u
    dsimp [H,Hmax]
    have hu : (u.val : ℤ) ≤ (B - 1 : ℕ) := by exact_mod_cast Nat.le_pred_of_lt u.isLt
    exact add_le_add_right (mul_le_mul_of_nonneg_right hu hstep.le) _
  · intro u v huv
    have hne : (u.val : ℤ) ≠ v.val := by
      intro he
      apply huv
      exact Fin.ext (by exact_mod_cast he)
    have hd : 1 ≤ |(u.val : ℤ) - v.val| := by
      have hp : 0 < |(u.val : ℤ) - v.val| := abs_pos.mpr (sub_ne_zero.mpr hne)
      omega
    have he : H u - H v = ((u.val : ℤ) - v.val) * step := by dsimp [H]; ring
    rw [he,abs_mul,abs_of_pos hstep]
    exact hstepbound.trans_le (le_mul_of_one_le_left hstep.le hd)

end IntegerSchedules

namespace IntegerSchedules.Inner

variable {B n R size d K : ℕ} {r h : ℤ} (S : Inner B n R size d K r h)

lemma extension_pos : 0 < S.extension := by
  have hl := S.lag_pos
  have he := S.extension_bound
  omega

lemma max_pos (hB : 0 < B) : 0 < S.Hmax :=
  (S.H_pos ⟨0,hB⟩).trans_le (S.H_bounded _)

lemma halfGap_large (hB : 0 < B) (hr : 0 ≤ r) :
    S.Hmax + r < S.halfGap ∧ (B * R : ℕ) + r < S.halfGap := by
  have hp := S.max_pos hB
  have he := S.extension_pos
  have hb := S.gap_bound
  constructor <;> omega

def boundary (j : ℕ) : ℤ := (j + 1 : ℕ) * (2 * S.halfGap)

def mainBase (j : ℕ) : ℤ := (2 * j + 3 : ℕ) * S.halfGap

def mainOffset (j a : ℕ) : ℤ := S.mainBase j + a * B

def periodicOffset (j : ℕ) (u : Fin B) (a : ℕ) : ℤ :=
  S.boundary j + S.H u + S.lag + a * B

lemma main_multiple (j a : ℕ) : (B : ℤ) ∣ S.mainOffset j a := by
  apply dvd_add
  · exact dvd_mul_of_dvd_right S.gap_multiple _
  · exact dvd_mul_left _ _

lemma periodic_multiple (j : ℕ) (u : Fin B) (a : ℕ) :
    (B : ℤ) ∣ S.periodicOffset j u a := by
  apply dvd_add
  · apply dvd_add
    · exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right S.gap_multiple _) _)
        (S.H_multiple u)
    · exact S.lag_multiple
  · exact dvd_mul_left _ _

lemma main_before (hB : 0 < B) (hr : 0 ≤ r) (i j a : ℕ) (u : Fin B) (hij : i ≤ j) :
    S.boundary i + S.H u + r < S.mainOffset j a := by
  have hh := (S.halfGap_large hB hr).1
  have hwidth := S.H_bounded u
  have hgap := S.gap_pos
  have hi : ((i + 1 : ℕ) : ℤ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hij 1
  have hmul := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ 2 * S.halfGap)
  have ha : 0 ≤ (a : ℤ) * B := by positivity
  dsimp [boundary,mainOffset,mainBase]
  push_cast at hmul ⊢
  nlinarith

lemma main_after (hB : 0 < B) (hr : 0 ≤ r) (i j a' : ℕ) (k : ℤ)
    (hji : j + 1 ≤ i) (ha : a' < R) :
    k < (k - S.mainBase j - a' * B) + S.boundary i - r := by
  have hh := (S.halfGap_large hB hr).2
  have hgap := S.gap_pos
  have hi : ((j + 2 : ℕ) : ℤ) ≤ (i + 1 : ℕ) := by exact_mod_cast (by omega : j + 2 ≤ i + 1)
  have hmul := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ 2 * S.halfGap)
  have hab : (a' : ℤ) * B < (B * R : ℕ) := by
    have hn : a' * B < R * B := Nat.mul_lt_mul_of_pos_right ha hB
    simpa only [Nat.cast_mul, mul_comm] using (show ((a' * B : ℕ) : ℤ) < ((R * B : ℕ) : ℤ) by exact_mod_cast hn)
  dsimp [mainBase,boundary]
  push_cast at hmul hh ⊢
  nlinarith

lemma periodic_before (j a : ℕ) (u : Fin B) :
    S.boundary j + S.H u + r < S.periodicOffset j u a := by
  have hl := S.lag_bound
  have hn : 0 ≤ ((size + 2 : ℕ) : ℤ) * d := by positivity
  have ha : 0 ≤ (a : ℤ) * B := by positivity
  dsimp [periodicOffset]
  omega

end IntegerSchedules.Inner

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace ClockAffine

open scoped Classical
open RobustClock

variable {T : Type uT} {P : Type uP} {C : Type uC} {M : Type uM} {S : Type uS} {K : Type uK} [Fintype T] [Fintype P] [Fintype C]
  [Monoid M] [Field K] [AddCommGroup S] [Module K S]

variable (clock : Specification T P C)

def Edge (z : C → RobustClock.Circle) (a b : T) : Prop :=
  ∃ i ∈ clock.I a, ∃ j ∈ clock.J b, i + j = z

noncomputable def offChoice (z : C → RobustClock.Circle) : Option (T × T) :=
  if h : ∃ ab : T × T, ab.1 ≠ ab.2 ∧ Edge clock z ab.1 ab.2 then some h.choose else none

lemma offChoice_some {z : C → RobustClock.Circle} {ab : T × T}
    (he : offChoice clock z = some ab) :
    ab.1 ≠ ab.2 ∧ Edge clock z ab.1 ab.2 ∧
      ∀ a b, Edge clock z a b → a = ab.1 ∧ b = ab.2 := by
  classical
  unfold offChoice at he
  split_ifs at he with hx
  · have hab := Option.some.inj he
    have hh := hab ▸ hx.choose_spec
    refine ⟨hh.1,hh.2,?_⟩
    rcases clock.graph z with hd | ⟨a,b,_,_,hu⟩
    · exact False.elim (hh.1 (hd _ _ hh.2))
    · have ht := hu _ _ hh.2
      intro a' b' he'
      exact ⟨(hu _ _ he').1.trans ht.1.symm,(hu _ _ he').2.trans ht.2.symm⟩

lemma offChoice_none {z : C → RobustClock.Circle} (he : offChoice clock z = none)
    {a b : T} (hab : Edge clock z a b) : a = b := by
  classical
  by_contra hn
  have hx : ∃ ab : T × T, ab.1 ≠ ab.2 ∧ Edge clock z ab.1 ab.2 := ⟨(a,b),hn,hab⟩
  simp only [offChoice,dite_eq_left hx] at he
  cases he

lemma offChoice_of_offedge {z : C → RobustClock.Circle} {a b : T}
    (hn : a ≠ b) (he : Edge clock z a b) : offChoice clock z = some (a,b) := by
  cases hh : offChoice clock z with
  | none => exact False.elim (hn (offChoice_none clock hh he))
  | some ab =>
    have hp := (offChoice_some clock hh).2.2 _ _ he
    rcases ab with ⟨a',b'⟩
    dsimp at hp
    rcases hp with ⟨rfl,rfl⟩
    rfl

lemma edge_add (φ : ℤ →+ (C → RobustClock.Circle)) {q t k : ℤ} {a b : T}
    (hp : φ (k-t) ∈ clock.I a) (hs : φ (q-k) ∈ clock.J b) :
    Edge clock (φ (q-t)) a b := by
  refine ⟨_,hp,_,hs,?_⟩
  rw [← map_add]
  congr 1
  ring

variable (ρ : M → (S →ₗ[K] S))

def productTable {g : ℕ} (A C : M) (d : Fin g → M) : S →ₗ[K] S :=
  ρ (A * (List.ofFn d).prod * C)

structure Factors (M : Type uM2) (g : ℕ) where
  A : M
  entries : Fin g → M
  C : M

structure Snapshot (M : Type uM3) [Monoid M] (g : ℕ) where
  product : M
  boundaries : Option (Factors M g)
  product_eq : ∀ f, boundaries = some f → product = f.A * (List.ofFn f.entries).prod * f.C

variable {g : ℕ}
variable (β : M → M → (Fin g → M) → S) (X Y : T → S)

noncomputable def shift (z : C → RobustClock.Circle) (D : Snapshot M g) : S :=
  match offChoice clock z with
  | some ab => Y ab.2 - ρ D.product (X ab.1)
  | none => match D.boundaries with
    | none => 0
    | some f => β f.A f.C f.entries

noncomputable def update (z : C → RobustClock.Circle) (D : Snapshot M g) (x : S) : S :=
  ρ D.product x + shift clock ρ β X Y z D

lemma update_off {z : C → RobustClock.Circle} {a b : T} (D : Snapshot M g)
    (hn : a ≠ b) (he : Edge clock z a b) :
    update clock ρ β X Y z D (X a) = Y b := by
  simp only [update,shift,offChoice_of_offedge clock hn he]
  abel

lemma update_main {z : C → RobustClock.Circle} {f : Factors M g} (D : Snapshot M g)
    (hc : offChoice clock z = none) (hf : D.boundaries = some f) (x : S) :
    update clock ρ β X Y z D x = productTable ρ f.A f.C f.entries x + β f.A f.C f.entries := by
  simp only [update,shift,hc,hf,productTable,D.product_eq f hf]

lemma update_periodic {z : C → RobustClock.Circle} (D : Snapshot M g)
    (hc : offChoice clock z = none) (hf : D.boundaries = none) (x : S) :
    update clock ρ β X Y z D x = ρ D.product x := by
  simp only [update,shift,hc,hf,add_zero]

lemma independent_pair {z : C → RobustClock.Circle} {a b : T} (D : Snapshot M g)
    (he : Edge clock z a b)
    (hdiag : a = b → offChoice clock z = none →
      ρ D.product (X a) + (match D.boundaries with
        | none => 0
        | some f => β f.A f.C f.entries) = Y b) :
    update clock ρ β X Y z D (X a) = Y b := by
  cases hc : offChoice clock z with
  | none =>
    have hab := offChoice_none clock hc he
    simpa only [update,shift,hc] using hdiag hab hc
  | some ab =>
    have hh := offChoice_some clock hc
    have hab := hh.2.2 _ _ he
    have hn : a ≠ b := fun heq => hh.1 (hab.1.symm.trans (heq.trans hab.2))
    exact update_off clock ρ β X Y D hn he

structure Later (M : Type uM4) [Monoid M] (g : ℕ) where
  tailProduct : M
  boundaries : Option (Factors M g)
  tail_eq : ∀ f, boundaries = some f → tailProduct = f.A * (List.ofFn f.entries).prod * f.C

def Later.substitute (D : Later M g) (m : M) : Snapshot M g where
  product := m * D.tailProduct
  boundaries := D.boundaries.map (fun f => ⟨m * f.A,f.entries,f.C⟩)
  product_eq := by
    intro f hf
    obtain ⟨a,ha,hf⟩ := Option.map_eq_some_iff.mp hf
    subst f
    simp only [D.tail_eq a ha,mul_assoc]

noncomputable def hypothetical (z : C → RobustClock.Circle) (D : Later M g) :
    M → (S × K →ₗ[K] S × K) := fun m =>
  Homogenization.lift (ρ (m * D.tailProduct))
    (shift clock ρ β X Y z (D.substitute m))

lemma hypothetical_at (z : C → RobustClock.Circle) (D : Later M g) (m : M) (x : S) :
    hypothetical clock ρ β X Y z D m (x,1) =
      (update clock ρ β X Y z (D.substitute m) x,1) := by
  simp only [hypothetical,Homogenization.lift_apply_one,update,Later.substitute]

lemma hypothetical_actual (z : C → RobustClock.Circle) (D : Later M g) (m : M) :
    hypothetical clock ρ β X Y z D m =
      Homogenization.lift (ρ (D.substitute m).product)
        (shift clock ρ β X Y z (D.substitute m)) := rfl

end ClockAffine

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace ExceptionalOrigins

open scoped Classical
open LocalMarkers

variable {Alphabet : Type uAlphabet} {J : Type uJ} {C : Type uC}

structure Parameters (Alphabet : Type uAlphabet2) (J : Type uJ2) (C : Type uC2) where
  endRule : CanonicalEpisodes.Parameters Alphabet
  d : ℕ
  K : ℕ
  B : ℕ
  B_pos : 0 < B
  end_modulus : endRule.B = B
  innerRule : Rule Alphabet d K
  offset : J → ℤ
  H : Fin B → ℤ
  w : ℤ
  w₀ : ℤ
  ext : ℤ
  φ : ℤ →+ (C → RobustClock.Circle)
  W : Set (C → RobustClock.Circle)

namespace Parameters

variable (A : Parameters Alphabet J C)

def residue (z : ℤ) : Fin A.B := by
  have hB : (0 : ℤ) < A.B := by exact_mod_cast A.B_pos
  exact ⟨(z % A.B).toNat, (Int.toNat_lt (Int.emod_nonneg z (ne_of_gt hB))).mpr
    (Int.emod_lt_of_pos z hB)⟩

lemma residue_val (z : ℤ) : ((A.residue z).val : ℤ) = z % A.B := by
  have hB : (0 : ℤ) < A.B := by exact_mod_cast A.B_pos
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (ne_of_gt hB))

lemma residue_ne {Q t δ δ' : ℤ} (hd : δ % A.B ≠ δ' % A.B) :
    A.residue (Q - (t + δ)) ≠ A.residue (Q - (t + δ')) := by
  intro he
  have hh := congrArg (fun u : Fin A.B => (u.val : ℤ)) he
  rw [A.residue_val,A.residue_val] at hh
  have hmod := (show Int.ModEq (A.B : ℤ) (Q - (t + δ)) (Q - (t + δ')) from hh).sub_left (Q-t)
  apply hd
  change Int.ModEq (A.B : ℤ) δ δ'
  convert hmod using 1 <;> ring

noncomputable def inner (f : ℤ → Alphabet) (j : J) (u : Fin A.B) (t : ℤ) : Option ℤ :=
  MarkerSearch.search (A.innerRule.markers f) (t + A.offset j) (t + A.offset j + A.H u)

def Z (f : ℤ → Alphabet) (t : ℤ) : Prop :=
  EndSearch.Unstable (A.endRule.rule.markers f) A.B A.endRule.S A.endRule.d
    (t + A.endRule.offset) A.w ∨
  EndSearch.Unstable (A.endRule.rule.markers f) A.B A.endRule.S (3 * A.endRule.d)
    (t + A.endRule.offset) A.w

def Star (f : ℤ → Alphabet) (t Q : ℤ) : Prop :=
  A.φ (Q-t) ∈ A.W ∨ ∃ j, MarkerSearch.InnerFailure (A.innerRule.markers f)
    (t + A.offset j) (A.H (A.residue (Q-t))) A.w₀ A.ext

def Failed (f : ℤ → Alphabet) (t Q : ℤ) : Prop := A.Z f t ∨ A.Star f t Q

noncomputable def anchor (f : ℤ → Alphabet) (q₀ t : ℤ) : ℤ :=
  (A.endRule.large f (t + A.endRule.offset)).getD q₀

noncomputable def bad {P : Type uPBad} [Fintype P] (p : P → ℤ) (f : ℤ → Alphabet) (t q₀ : ℤ) : Finset (P × P) :=
  Finset.univ.filter fun ij => ij.1 ≠ ij.2 ∧
    A.Failed f (t + (p ij.1 - p ij.2)) (A.anchor f q₀ (t + (p ij.1 - p ij.2)))

lemma width_inner_count {P : Type uP} (pairs : Finset (P × P)) (δ : P × P → ℤ)
    (h : ℤ) (hw₀ : 0 ≤ A.w₀) (hinner : 2 * h + 2 * A.w₀ < A.d)
    (hbound : ∀ ij ∈ pairs, |δ ij| ≤ h)
    (hgap : ∀ ij ∈ pairs, ∀ kl ∈ pairs, ij ≠ kl → 2 * A.w₀ < |δ ij - δ kl|)
    (hmod : ∀ ij ∈ pairs, ∀ kl ∈ pairs, ij ≠ kl → δ ij % A.B ≠ δ kl % A.B)
    (hwidth : ∀ u v, u ≠ v → 2 * h + 2 * max A.ext A.w₀ < |A.H u - A.H v|)
    (f : ℤ → Alphabet) (t Q : ℤ) (j : J) :
    (pairs.filter fun ij => MarkerSearch.InnerFailure (A.innerRule.markers f)
      (t + A.offset j + δ ij) (A.H (A.residue (Q - (t + δ ij)))) A.w₀ A.ext).card ≤ 3 := by
  classical
  apply MarkerSearch.innerFailure_card pairs δ
    (fun ij => A.H (A.residue (Q - (t + δ ij)))) (A.innerRule.separated f) hw₀ hinner hbound hgap
  intro ij hij kl hkl hn
  have hu := A.residue_ne (Q := Q) (t := t) (hmod ij hij kl hkl hn)
  have hw := hwidth _ _ hu
  have hi := abs_le.mp (hbound ij hij)
  have hk := abs_le.mp (hbound kl hkl)
  let a := A.H (A.residue (Q - (t + δ ij)))
  let b := A.H (A.residue (Q - (t + δ kl)))
  let z := t + A.offset j
  have hh : |a - b| ≤ |(z + δ ij + a) - (z + δ kl + b)| + |δ kl - δ ij| := by
    calc
      |a - b| = |((z + δ ij + a) - (z + δ kl + b)) + (δ kl - δ ij)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hd : |δ kl - δ ij| ≤ 2 * h := abs_le.mpr ⟨by omega,by omega⟩
  change 2 * max A.ext A.w₀ < |(z + δ ij + a) - (z + δ kl + b)|
  change 2 * h + 2 * max A.ext A.w₀ < |a - b| at hw
  omega

lemma bad_card {P : Type uP2} {T : Type uT} [Fintype P] [Fintype T] [Fintype C] [Fintype J]
    (clock : RobustClock.Specification T P C) (p : P → ℤ) (h hgap : ℤ)
    (hW : A.W = clock.W) (hpert : ∀ i, dist (A.φ (p i)) (clock.v i) < clock.η)
    (hbound : ∀ i j, |p i - p j| ≤ h)
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (p i - p j) % A.B ≠ (p i' - p j') % A.B)
    (hdiff : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      hgap < |(p i - p j) - (p i' - p j')|)
    (hw₀ : 0 ≤ A.w₀) (hgap₀ : 2 * A.w₀ ≤ hgap)
    (hinner : 2 * h + 2 * A.w₀ < A.d)
    (hwidth : ∀ u v, u ≠ v → 2 * h + 2 * max A.ext A.w₀ < |A.H u - A.H v|)
    (hS : 2 * h + 2 * A.w < A.endRule.S)
    (hend : 2 * h + (A.B - 1) * A.endRule.S + 2 * A.w < A.endRule.d)
    (hanchor : 2 * h + 2 * (A.B - 1) * A.endRule.S < A.endRule.d)
    (μ : ℕ)
    (hμ : 20 * (10000000 * Real.log (2 * Fintype.card T) + 4 * Fintype.card J) + 10 < μ)
    (f : ℤ → Alphabet) (t q₀ : ℤ) : (A.bad p f t q₀).card < μ := by
  classical
  let : DecidableEq (P × P) := fun a b => Classical.propDecidable (a = b)
  let pairs : Finset (P × P) := Finset.univ.filter fun ij => ij.1 ≠ ij.2
  let δ : P × P → ℤ := fun ij => p ij.1 - p ij.2
  let Qs : Finset ℤ := (Finset.univ : Finset (P × P)).image
    (fun ij => A.anchor f q₀ (t + δ ij))
  let unstable := pairs.filter fun ij => A.Z f (t + δ ij)
  let clocks := fun Q => pairs.filter fun ij => A.φ (Q - (t + δ ij)) ∈ A.W
  let inners := fun Q j => pairs.filter fun ij => MarkerSearch.InnerFailure
    (A.innerRule.markers f) (t + A.offset j + δ ij)
      (A.H (A.residue (Q - (t + δ ij)))) A.w₀ A.ext
  have hB : (0 : ℤ) < A.B := by exact_mod_cast A.B_pos
  have hbound' : ∀ ij ∈ pairs, |δ ij| ≤ h := fun ij _ => hbound ij.1 ij.2
  have hmod' : ∀ ij ∈ pairs, ∀ kl ∈ pairs, ij ≠ kl → δ ij % A.B ≠ δ kl % A.B := by
    intro ij hij kl hkl hn
    exact hmod ij.1 ij.2 kl.1 kl.2 (Finset.mem_filter.mp hij).2
      (Finset.mem_filter.mp hkl).2 hn
  have hsepEnd : MarkerSearch.Separated (A.endRule.rule.markers f) A.endRule.d :=
    A.endRule.rule.separated f
  have hQs : Qs.card ≤ 20 := by
    have he := EndSearch.anchor_card (Finset.univ : Finset (P × P))
      (z := t + A.endRule.offset) (q₀ := q₀) δ hB A.endRule.S_nonneg
      (by have := A.endRule.d_ge; omega) hsepEnd hanchor (fun ij _ => hbound ij.1 ij.2)
    have hQeq : Qs = (Finset.univ : Finset (P × P)).image
        (fun ij => (EndSearch.search (A.endRule.rule.markers f) A.B A.endRule.S
          (3 * A.endRule.d) (t + A.endRule.offset + δ ij)).getD q₀) := by
      simp only [Qs,anchor,CanonicalEpisodes.Parameters.large,A.end_modulus,add_right_comm t]
    rw [hQeq]
    exact he.trans (by norm_num)
  have hUnstable : unstable.card ≤ 4 := by
    have he := EndSearch.two_searches_card (a₀ := A.endRule.d) (a₁ := 3 * A.endRule.d)
      (z := t + A.endRule.offset) pairs δ hB hS A.endRule.S_nonneg hsepEnd hend hbound' hmod'
    simpa only [unstable,Z,add_right_comm t] using he
  have hc : 0 ≤ 10000000 * Real.log (2 * Fintype.card T) := by
    by_cases hT : Fintype.card T = 0
    · simp [hT]
    · apply mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * Fintype.card T)))
  apply StencilSparsity.whole_stencil (A.bad p f t q₀) unstable Qs Finset.univ clocks inners
    (10000000 * Real.log (2 * Fintype.card T)) μ hc hQs hUnstable
  · intro Q _
    have hcc := clock.count (fun i => A.φ (p i)) hpert (A.φ (Q-t))
    have he : clocks Q = RobustClock.badPairs clock.W (A.φ (Q-t)) (fun i => A.φ (p i)) := by
      ext ij
      simp only [clocks,pairs,RobustClock.badPairs,Finset.mem_filter,Finset.mem_univ,true_and,hW]
      rw [show Q - (t + δ ij) = (Q-t) + p ij.2 - p ij.1 by dsimp [δ]; ring,
        map_sub,map_add]
    rw [he]
    exact hcc
  · intro Q _ j _
    exact A.width_inner_count pairs δ h hw₀ hinner hbound'
      (fun ij hij kl hkl hn => hgap₀.trans_lt (hdiff ij.1 ij.2 kl.1 kl.2
        (Finset.mem_filter.mp hij).2 (Finset.mem_filter.mp hkl).2 hn)) hmod' hwidth f t Q j
  · intro ij hij
    obtain ⟨_,hn,hfail⟩ := Finset.mem_filter.mp hij
    have hijp : ij ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
    rcases hfail with hz | hc' | ⟨j,hj⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hijp,hz⟩)
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨A.anchor f q₀ (t + δ ij),Finset.mem_image.mpr ⟨ij,Finset.mem_univ _,rfl⟩,?_⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hijp,hc'⟩)
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨A.anchor f q₀ (t + δ ij),Finset.mem_image.mpr ⟨ij,Finset.mem_univ _,rfl⟩,?_⟩
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hijp,by simpa only [add_right_comm t] using hj⟩⟩
  · simpa only [Finset.card_univ] using hμ

end Parameters

end ExceptionalOrigins

namespace MarkerSearch

lemma search_congr {S S' : Set ℤ} {l r : ℤ}
    (h : ∀ m, l ≤ m → m ≤ r → (m ∈ S ↔ m ∈ S')) : search S l r = search S' l r := by
  classical
  have he : (Finset.Icc l r).filter (· ∈ S) = (Finset.Icc l r).filter (· ∈ S') := by
    ext m
    simp only [Finset.mem_filter,Finset.mem_Icc]
    exact and_congr_right fun hm => h m hm.1 hm.2
  simp only [search,he]

lemma innerFailure_congr {S S' : Set ℤ} {z H w E : ℤ} (hw : 0 ≤ w)
    (h : ∀ m, z-w ≤ m → m ≤ z+H+max E w → (m ∈ S ↔ m ∈ S')) :
    InnerFailure S z H w E ↔ InnerFailure S' z H w E := by
  have hsearch : ∀ v, |v| ≤ w → search S (z+v) (z+H+v) = search S' (z+v) (z+H+v) := by
    intro v hv
    have hb := abs_le.mp hv
    apply search_congr
    intro m hm hm'
    exact h m (by omega) (by have := le_max_right E w; omega)
  have hzero := hsearch 0 (by simpa using hw)
  simp only [add_zero] at hzero
  have hex : (∃ m ∈ S, z ≤ m ∧ m ≤ z+H+E) ↔ (∃ m ∈ S', z ≤ m ∧ m ≤ z+H+E) := by
    constructor <;> rintro ⟨m,hm,hl,hr⟩
    · exact ⟨m,(h m (by omega) (by have := le_max_left E w; omega)).mp hm,hl,hr⟩
    · exact ⟨m,(h m (by omega) (by have := le_max_left E w; omega)).mpr hm,hl,hr⟩
  simp only [InnerFailure,hzero,hex]
  apply or_congr_left
  apply exists_congr
  intro v
  apply and_congr_right
  intro hv
  rw [hsearch v hv]

end MarkerSearch

namespace EndSearch

lemma unstable_congr {S S' : Set ℤ} {B D a z w : ℤ}
    (hzero : search S B D a z = search S' B D a z)
    (hshift : ∀ v, B ∣ v → |v| ≤ w → search S B D a (z+v) = search S' B D a (z+v)) :
    Unstable S B D a z w ↔ Unstable S' B D a z w := by
  unfold Unstable
  apply exists_congr
  intro v
  apply and_congr_right
  intro hv
  apply and_congr_right
  intro hw
  rw [hzero,hshift v hv hw]

end EndSearch

namespace ExceptionalOrigins.Parameters

open LocalMarkers

variable {Alphabet : Type uAlphabet3} {J : Type uJ3} {C : Type uC3} (A : ExceptionalOrigins.Parameters Alphabet J C)

structure Visible (s b t Q : ℤ) : Prop where
  base : A.endRule.Visible s b (t + A.endRule.offset)
  ends : ∀ v, (A.B : ℤ) ∣ v → |v| ≤ A.w →
    s ≤ t + A.endRule.offset + v - A.endRule.width - A.endRule.rule.r ∧
      t + A.endRule.offset + v + A.endRule.width + A.endRule.rule.r ≤ b
  inner : ∀ j,
    s ≤ t + A.offset j - A.w₀ - A.innerRule.r ∧
      t + A.offset j + A.H (A.residue (Q-t)) + max A.ext A.w₀ + A.innerRule.r ≤ b

lemma Visible.mono {s b s' b' t Q : ℤ} (hv : A.Visible s b t Q)
    (hs : s' ≤ s) (hb : b ≤ b') : A.Visible s' b' t Q := by
  refine ⟨CanonicalEpisodes.Parameters.Visible.mono A.endRule hv.base hs hb,?_,?_⟩
  · intro v hd hw
    exact ⟨hs.trans (hv.ends v hd hw).1,(hv.ends v hd hw).2.trans hb⟩
  · intro j
    exact ⟨hs.trans (hv.inner j).1,(hv.inner j).2.trans hb⟩

lemma Visible.min {s b b' t Q : ℤ} (hv : A.Visible s b t Q)
    (hv' : A.Visible s b' t Q) : A.Visible s (min b b') t Q := by
  refine ⟨⟨hv.base.1,le_min hv.base.2.1 hv'.base.2.1,
    hv.base.2.2.1,le_min hv.base.2.2.2 hv'.base.2.2.2⟩,?_,?_⟩
  · intro v hd hw
    exact ⟨(hv.ends v hd hw).1,le_min (hv.ends v hd hw).2 (hv'.ends v hd hw).2⟩
  · intro j
    exact ⟨(hv.inner j).1,le_min (hv.inner j).2 (hv'.inner j).2⟩

lemma Z_congr {s b t Q : ℤ} {f g : ℤ → Alphabet}
    (hv : A.Visible s b t Q) (he : AgreesOn f g s b) : A.Z f t ↔ A.Z g t := by
  have h0 := A.endRule.searches_congr hv.base he
  have hsh : ∀ v, (A.B : ℤ) ∣ v → |v| ≤ A.w →
      A.endRule.small f (t + A.endRule.offset + v) = A.endRule.small g (t + A.endRule.offset + v) ∧
      A.endRule.large f (t + A.endRule.offset + v) = A.endRule.large g (t + A.endRule.offset + v) := by
    intro v hd hw
    have hbounds := hv.ends v hd hw
    have hwidth := A.endRule.small_width_le
    constructor
    · apply EndSearch.search_local A.endRule.rule
      intro x hx hx'
      exact he x (by omega) (by omega)
    · apply EndSearch.search_local A.endRule.rule
      intro x hx hx'
      exact he x (by dsimp [CanonicalEpisodes.Parameters.width] at hbounds; omega)
        (by dsimp [CanonicalEpisodes.Parameters.width] at hbounds; omega)
  have hη : EndSearch.Unstable (A.endRule.rule.markers f) A.endRule.B A.endRule.S A.endRule.d
      (t + A.endRule.offset) A.w ↔ EndSearch.Unstable (A.endRule.rule.markers g)
        A.endRule.B A.endRule.S A.endRule.d (t + A.endRule.offset) A.w :=
    EndSearch.unstable_congr h0.1 (fun v hv hw => (hsh v (A.end_modulus ▸ hv) hw).1)
  have hζ : EndSearch.Unstable (A.endRule.rule.markers f) A.endRule.B A.endRule.S (3 * A.endRule.d)
      (t + A.endRule.offset) A.w ↔ EndSearch.Unstable (A.endRule.rule.markers g)
        A.endRule.B A.endRule.S (3 * A.endRule.d) (t + A.endRule.offset) A.w :=
    EndSearch.unstable_congr h0.2 (fun v hv hw => (hsh v (A.end_modulus ▸ hv) hw).2)
  simpa only [Z,A.end_modulus] using or_congr hη hζ

lemma Failed_congr {s b t Q : ℤ} {f g : ℤ → Alphabet}
    (hw₀ : 0 ≤ A.w₀) (hv : A.Visible s b t Q) (he : AgreesOn f g s b) :
    A.Failed f t Q ↔ A.Failed g t Q := by
  apply or_congr (A.Z_congr hv he)
  apply or_congr_right
  apply exists_congr
  intro j
  apply MarkerSearch.innerFailure_congr hw₀
  intro m hm hm'
  apply A.innerRule.locality
  intro x hx hx'
  exact he x (by have := (hv.inner j).1; omega) (by have := (hv.inner j).2; omega)

end ExceptionalOrigins.Parameters

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace SuffixDecoder

open LocalMarkers EpisodeEnd

variable {Alphabet : Type uAlphabet} {J : Type uJ} {C : Type uC} {P : Type uP} (A : ExceptionalOrigins.Parameters Alphabet J C)

def origin (p : P → ℤ) (lag k : ℤ) (i : P) : ℤ := k + lag - p i

structure Test (τ : P → ℤ) (reference : P) (k b : ℤ) (f : ℤ → Alphabet)
    (decoded : P) : Prop where
  visible : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i))
  reference_guard : (∃ i, A.endRule.large f (τ i + A.endRule.offset) = none) →
    (∀ i, A.endRule.small f (τ i + A.endRule.offset) = none) ∧
    EndAt A.endRule.d A.endRule.K A.endRule.tail f (τ reference + A.endRule.offset)
      (A.endRule.small f (τ reference + A.endRule.offset)) b
  unique : A.Failed f (τ decoded) (A.anchor f (b-A.endRule.tail) (τ decoded)) ∧
    ∀ i, A.Failed f (τ i) (A.anchor f (b-A.endRule.tail) (τ i)) → i = decoded
  final_guard : EndAt A.endRule.d A.endRule.K A.endRule.tail f
    (τ decoded + A.endRule.offset) (A.endRule.small f (τ decoded + A.endRule.offset)) b

lemma searches_agree {τ : P → ℤ} {reference decoded : P} {k b b' : ℤ}
    {f g : ℤ → Alphabet} (htest : Test A τ reference k b' g decoded)
    (hvis : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i)))
    (he : AgreesOn f g k (min b b')) (i : P) :
    A.endRule.small f (τ i + A.endRule.offset) = A.endRule.small g (τ i + A.endRule.offset) ∧
      A.endRule.large f (τ i + A.endRule.offset) = A.endRule.large g (τ i + A.endRule.offset) := by
  have hv := (hvis i).base
  have hv' := (htest.visible i).base
  apply A.endRule.searches_congr
    (show A.endRule.Visible k (min b b') (τ i + A.endRule.offset) from
      ⟨hv.1,le_min hv.2.1 hv'.2.1,hv.2.2.1,le_min hv.2.2.2 hv'.2.2.2⟩) he

lemma reference_forces_end {τ : P → ℤ} {reference actual decoded : P} {k b b' : ℤ}
    {f g : ℤ → Alphabet} (htest : Test A τ reference k b' g decoded)
    (hvis : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i)))
    (he : AgreesOn f g k (min b b'))
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K - |τ actual - τ reference|)
    (hover' : |τ actual - τ reference| < A.endRule.K)
    (hend : EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (τ actual + A.endRule.offset) (A.endRule.small f (τ actual + A.endRule.offset)) b)
    (habsent : ∃ i, A.endRule.large g (τ i + A.endRule.offset) = none) : b = b' := by
  obtain ⟨hsmall,href⟩ := htest.reference_guard habsent
  have hη := (searches_agree A htest hvis he actual).1.trans (hsmall actual)
  rw [hη] at hend
  rw [hsmall reference] at href
  have hv := (hvis actual).base
  have hv' := (htest.visible actual).base
  have hr := (hvis reference).base
  have hr' := (htest.visible reference).base
  apply shared_end A.endRule.tail_pos (by simpa only [add_sub_add_right_eq_sub] using hover)
    (by simpa only [add_sub_add_right_eq_sub] using hover')
    ⟨hv.2.2.1,le_min hv.2.2.2 hv'.2.2.2,hr.2.2.1,le_min hr.2.2.2 hr'.2.2.2⟩ he hend href

lemma true_anchor {τ : P → ℤ} {reference actual decoded : P} {k b b' : ℤ}
    {f g : ℤ → Alphabet} (htest : Test A τ reference k b' g decoded)
    (hvis : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i)))
    (he : AgreesOn f g k (min b b'))
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K - |τ actual - τ reference|)
    (hover' : |τ actual - τ reference| < A.endRule.K)
    (hend : EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (τ actual + A.endRule.offset) (A.endRule.small f (τ actual + A.endRule.offset)) b) :
    A.anchor f (b-A.endRule.tail) (τ actual) = A.anchor g (b'-A.endRule.tail) (τ actual) := by
  have hs := (searches_agree A htest hvis he actual).2
  cases hz : A.endRule.large g (τ actual + A.endRule.offset) with
  | none =>
    have hb := reference_forces_end A htest hvis he hover hover' hend ⟨actual,hz⟩
    simp only [ExceptionalOrigins.Parameters.anchor,hs,hz,hb]
  | some q => simp only [ExceptionalOrigins.Parameters.anchor,hs,hz,Option.getD_some]

lemma sound {τ : P → ℤ} {reference actual decoded : P} {k b b' : ℤ}
    {f g : ℤ → Alphabet} (hw₀ : 0 ≤ A.w₀) (htest : Test A τ reference k b' g decoded)
    (hvis : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i)))
    (he : AgreesOn f g k (min b b'))
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K - |τ actual - τ reference|)
    (hover' : |τ actual - τ reference| < A.endRule.K)
    (hend : EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (τ actual + A.endRule.offset) (A.endRule.small f (τ actual + A.endRule.offset)) b)
    (hfailed : A.Failed f (τ actual) (A.anchor f (b-A.endRule.tail) (τ actual))) :
    decoded = actual ∧ b' = b := by
  have hQ := true_anchor A htest hvis he hover hover' hend
  have hv' := htest.visible actual
  rw [← hQ] at hv'
  have hv := ExceptionalOrigins.Parameters.Visible.min A (hvis actual) hv'
  have hf := (A.Failed_congr hw₀ hv he).mp hfailed
  rw [hQ] at hf
  have hd := htest.unique.2 actual hf
  subst decoded
  refine ⟨rfl,?_⟩
  have hη := (searches_agree A htest hvis he actual).1
  have hguard := htest.final_guard
  rw [← hη] at hguard
  have hb := (hvis actual).base
  have hb' := (htest.visible actual).base
  have hseed := le_min hb.2.2.2 hb'.2.2.2
  have hh := shared_end A.endRule.tail_pos
    (by simpa only [sub_self,abs_zero,sub_zero] using A.endRule.seed_square)
    (by simpa only [sub_self,abs_zero] using
      (show (0 : ℤ) < A.endRule.K by exact_mod_cast A.endRule.seed_pos))
    ⟨hb.2.2.1,hseed,hb.2.2.1,hseed⟩ he hend hguard
  exact hh.symm

lemma all_small_absent {τ : P → ℤ} {f : ℤ → Alphabet} {H : ℤ}
    (hnear : ∀ i j, |τ i - τ j| ≤ H)
    (hnest : (A.endRule.d : ℤ) + (A.endRule.B-1)*A.endRule.S + H ≤ 3*A.endRule.d)
    (habsent : ∃ i, A.endRule.large f (τ i + A.endRule.offset) = none) :
    ∀ i, A.endRule.small f (τ i + A.endRule.offset) = none := by
  obtain ⟨j,hj⟩ := habsent
  intro i
  by_contra hi
  apply (EndSearch.nested A.endRule.B_pos A.endRule.S_nonneg hnest
    (by simpa only [add_sub_add_right_eq_sub] using hnear j i) hi) hj

lemma available_at {τ : P → ℤ} {reference actual : P} {k b H : ℤ} {f : ℤ → Alphabet}
    (hvis : ∀ i, A.Visible k b (τ i) (A.anchor f (b-A.endRule.tail) (τ i)))
    (hnear : ∀ i j, |τ i - τ j| ≤ H)
    (hnest : (A.endRule.d : ℤ) + (A.endRule.B-1)*A.endRule.S + H ≤ 3*A.endRule.d)
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K - |τ actual - τ reference|)
    (hover' : |τ actual - τ reference| < A.endRule.K)
    (hend : EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (τ actual + A.endRule.offset) (A.endRule.small f (τ actual + A.endRule.offset)) b)
    (hfailed : A.Failed f (τ actual) (A.anchor f (b-A.endRule.tail) (τ actual)))
    (hothers : ∀ i, i ≠ actual → ¬ A.Failed f (τ i) (A.anchor f (b-A.endRule.tail) (τ i))) :
    Test A τ reference k b f actual := by
  refine ⟨hvis,?_,⟨hfailed,?_⟩,hend⟩
  · intro ha
    have hsmall := all_small_absent A hnear hnest ha
    refine ⟨hsmall,?_⟩
    have he := hend
    rw [hsmall actual] at he
    rw [hsmall reference]
    apply transfer_end (by simpa only [add_sub_add_right_eq_sub] using hover)
      (by simpa only [add_sub_add_right_eq_sub] using hover') (h := he)
    intro _
    exact EndSearch.absent_continuation A.endRule.rule
      (by nlinarith [A.endRule.seed_long]) A.endRule.B_pos A.endRule.S_nonneg (hsmall reference)
  · intro i hi
    by_contra hn
    exact hothers i hn hi

end SuffixDecoder

namespace PeriodicCuts

open LocalMarkers WordIntervals

variable {Alphabet : Type uAlphabet2} {M : Type uM} [Monoid M] [Fintype M]

lemma markerless_run {d K : ℕ} (R : Rule Alphabet d K) (hd : 2 ≤ d)
    (hK : 3 * d^2 < K) (f : ℤ → Alphabet) (z H ext : ℤ)
    (hlen : 2 * (d : ℤ) ≤ H + ext)
    (hn : ∀ x, z ≤ x → x ≤ z + H + ext → x ∉ R.markers f) :
    ∃ v : ℤ → Alphabet, (∃ a : ℕ, 0 < a ∧ a < d ∧ Function.Periodic v (a : ℤ)) ∧
      AgreesOn f v (z + d) (z + H + ext - d + K) := by
  apply periodic_run hd hK f (z + d) (z + H + ext - d) (by omega)
  intro x hx hx'
  apply R.periodic
  intro y hy hy'
  exact hn y (by omega) (by omega)

lemma segment_shift_period {v : ℤ → Alphabet} {p : ℕ}
    (hp : Function.Periodic v (p : ℤ)) (s : ℤ) (m n : ℕ) :
    segment v (s + m * p) n = segment v s n := by
  apply List.ofFn_inj.mpr
  funext i
  simpa only [add_right_comm] using hp.nat_mul m (s + i.val)

omit [Fintype M] in
lemma product_periods (T : FreeMonoid Alphabet →* M) {v : ℤ → Alphabet} {p : ℕ}
    (hp : Function.Periodic v (p : ℤ)) (s : ℤ) (m : ℕ) :
    T (segment v s (m * p)) = T (segment v s p) ^ m := by
  induction m with
  | zero =>
    simp only [Nat.zero_mul,WordIntervals.segment,List.ofFn_zero,pow_zero]
    exact map_one T
  | succ m ih =>
    rw [Nat.succ_mul,segment_add]
    rw [show T (segment v s (m*p) ++ segment v (s + (m*p : ℕ)) p) =
      T (segment v s (m*p)) * T (segment v (s + (m*p : ℕ)) p) from map_mul T _ _,ih]
    push_cast
    rw [segment_shift_period hp, pow_succ]

lemma fixed_prefix (T : FreeMonoid Alphabet →* M) {f v : ℤ → Alphabet}
    {p : ℕ} (hp : Function.Periodic v (p : ℤ)) (s k₀ : ℤ) (q : ℕ)
    (hs : s ≤ k₀ - Fintype.card M * p)
    (he : AgreesOn f v (k₀ - Fintype.card M * p)
      (k₀ + (q * (Fintype.card M).factorial : ℕ) * p)) :
    product T f s (k₀ + (q * (Fintype.card M).factorial : ℕ) * p) =
      product T f s k₀ := by
  let N := Fintype.card M
  let x := k₀ - N * p
  have hxp : x ≤ k₀ := by
    have hn : (0 : ℤ) ≤ N * p := by positivity
    dsimp [x]
    omega
  have hk : k₀ ≤ k₀ + (q * N.factorial : ℕ) * p := by
    have hn : (0 : ℤ) ≤ (q * N.factorial : ℕ) * p := by positivity
    omega
  have hleft : product T f x k₀ = T (segment v x p) ^ N := by
    rw [product_congr T hxp (fun i hi hi' => he i hi (hi'.trans_le hk))]
    have hh : k₀ - x = (N*p : ℕ) := by dsimp [x]; ring
    simp only [product,piece,hh,Int.toNat_natCast]
    exact product_periods T hp x N
  have hright : product T f x (k₀ + (q * N.factorial : ℕ) * p) =
      T (segment v x p) ^ (N + q * N.factorial) := by
    rw [product_congr T (hxp.trans hk) he]
    have hh : k₀ + (q * N.factorial : ℕ) * p - x = ((N + q * N.factorial)*p : ℕ) := by
      dsimp [x]; ring
    simp only [product,piece,hh,Int.toNat_natCast]
    exact product_periods T hp x _
  rw [product_append T f hs (hxp.trans hk),product_append T f hs hxp,hright,hleft]
  rw [FiniteMonoidPeriod.pow_factorial _ (le_refl _) q]

lemma progression {B n R d K : ℕ} {r h : ℤ}
    (S : IntegerSchedules.Inner B n R (Fintype.card M) d K r h)
    (rule : Rule Alphabet d K) (hd : 2 ≤ d) (hK : 3*d^2 < K)
    (hr : 0 ≤ r) (hB : 0 < B) (hn : 0 < n)
    (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet) (s z : ℤ) (u : Fin B)
    (hs : s ≤ z + d)
    (hnomarker : ∀ x, z ≤ x → x ≤ z + S.H u + S.extension → x ∉ rule.markers f) :
    ∃ p : ℕ, 0 < p ∧ p < d ∧
      ∀ a : ℕ, a < n →
        a * p * (Fintype.card M).factorial < n * d * (Fintype.card M).factorial ∧
        product T f s (z + S.H u + S.lag + (a*p*(Fintype.card M).factorial*B : ℕ)) =
          product T f s (z + S.H u + S.lag) := by
  have hH := S.H_large u
  have hext := S.extension_pos
  obtain ⟨v,⟨p,hp,hpd,hv⟩,he⟩ := markerless_run rule hd hK f z (S.H u) S.extension
    (by omega) hnomarker
  refine ⟨p,hp,hpd,fun a ha => ?_⟩
  have hap : a * p < n * d := (Nat.mul_lt_mul_of_pos_right ha hp).trans
    (Nat.mul_lt_mul_of_pos_left hpd hn)
  have hfact := Nat.factorial_pos (Fintype.card M)
  have hindex : a * p * (Fintype.card M).factorial < n * d * (Fintype.card M).factorial :=
    Nat.mul_lt_mul_of_pos_right hap hfact
  refine ⟨hindex,?_⟩
  have hpz : (p : ℤ) < d := by exact_mod_cast hpd
  have hN : 0 ≤ (Fintype.card M : ℤ) := by positivity
  have hpre : z + d ≤ z + S.H u + S.lag - Fintype.card M * p := by
    have hl := S.lag_bound
    push_cast at hl
    nlinarith [mul_le_mul_of_nonneg_left hpz.le hN]
  have hlast : z + S.H u + S.lag + (a*p*(Fintype.card M).factorial*B : ℕ) <
      z + S.H u + S.extension - d + K := by
    have hb : a*p*(Fintype.card M).factorial*B < n*d*(Fintype.card M).factorial*B :=
      Nat.mul_lt_mul_of_pos_right hindex hB
    have hbz : ((a*p*(Fintype.card M).factorial*B : ℕ) : ℤ) <
        (n*d*(Fintype.card M).factorial*B : ℕ) := by exact_mod_cast hb
    have hh := S.extension_bound
    omega
  have hstep : ((a*B*(Fintype.card M).factorial : ℕ) : ℤ) * p =
      (a*p*(Fintype.card M).factorial*B : ℕ) := by push_cast; ring
  simpa only [hstep] using fixed_prefix T hv s (z + S.H u + S.lag) (a*B)
    (hs.trans hpre) (fun i hi hi' => he i (hpre.trans hi) (by rw [hstep] at hi'; omega))

end PeriodicCuts

namespace PeriodicClock

open scoped BigOperators

lemma map_modEq {G : Type uG} [AddCommGroup G] (φ : ℤ →+ G) {n x y : ℤ}
    (hn : φ n = 0) (he : Int.ModEq n x y) : φ x = φ y := by
  obtain ⟨a,ha⟩ := Int.modEq_iff_dvd.mp he
  have hh : φ (y-x) = 0 := by
    rw [ha,mul_comm,← Int.zsmul_eq_mul,map_zsmul,hn,smul_zero]
  rw [map_sub,sub_eq_zero] at hh
  exact hh.symm

lemma sweep {G : Type uG2} [AddCommGroup G] (φ : ℤ →+ G) {n p : ℕ}
    (hn : 0 < n) (hφ : φ n = 0) (hcop : Nat.Coprime p n) (x y : ℤ) :
    ∃ a : ℕ, a < n ∧ φ (x + a*p) = φ (x+y) := by
  have : NeZero n := ⟨hn.ne'⟩
  let b : ZMod n := ↑((ZMod.unitOfCoprime p hcop)⁻¹) * (y : ZMod n)
  refine ⟨b.val,ZMod.val_lt b,?_⟩
  have he : (b.val : ZMod n) * p = (y : ZMod n) := by
    rw [ZMod.natCast_zmod_val]
    dsimp [b]
    rw [mul_right_comm,← ZMod.coe_unitOfCoprime p hcop,Units.inv_mul,one_mul]
  have hm : Int.ModEq (n : ℤ) ((b.val : ℤ)*p) y := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simpa only [Int.cast_mul,Int.cast_natCast] using he
  rw [map_add,map_add,map_modEq φ hφ hm]

lemma progression_coprime {C : Type uC2} [Fintype C] (n : C → ℕ)
    (hn : ∀ c, Nat.Prime (n c)) {p N B d : ℕ}
    (hp : 0 < p) (hpd : p < d) (hN : 0 < N) (hB : 0 < B)
    (hlarge : ∀ c, d < n c ∧ N < n c ∧ B < n c) :
    Nat.Coprime (p*N*B) (∏ c, n c) := by
  exact (coprime_product_of_small n hn hp (fun c => hpd.trans (hlarge c).1)).mul_left
    (coprime_product_of_small n hn hN (fun c => (hlarge c).2.1)) |>.mul_left
    (coprime_product_of_small n hn hB (fun c => (hlarge c).2.2))

end PeriodicClock

namespace SuffixDecoder

open ExceptionalOrigins EpisodeEnd

variable {Alphabet : Type uAlphabet3} {J : Type uJ2} {C : Type uC3} {Kind : Type uKind} [Fintype Kind] {μ : ℕ}
    (A : Parameters Alphabet J C)

lemma available_copy (p : Kind × Fin μ → ℤ) (lag s b H : ℤ)
    (f : ℤ → Alphabet) (reference : Kind × Fin μ) (kind : Kind)
    (hbad : (A.bad p f (s+lag) (b-A.endRule.tail)).card < μ)
    (hvis : ∀ a i, A.Visible (s+p a) b (s+lag+(p a-p i))
      (A.anchor f (b-A.endRule.tail) (s+lag+(p a-p i))))
    (hnear : ∀ i j, |p i-p j| ≤ H)
    (hnest : (A.endRule.d : ℤ)+(A.endRule.B-1)*A.endRule.S+H ≤ 3*A.endRule.d)
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K-H)
    (hover' : H < A.endRule.K)
    (hend : EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (s+lag+A.endRule.offset) (A.endRule.small f (s+lag+A.endRule.offset)) b)
    (hfailed : A.Failed f (s+lag) (A.anchor f (b-A.endRule.tail) (s+lag))) :
    ∃ copy : Fin μ, Test A (origin p lag (s+p (kind,copy))) reference
      (s+p (kind,copy)) b f (kind,copy) := by
  classical
  obtain ⟨copy,hcopy⟩ := StencilSparsity.good_copy μ _ hbad kind
  let actual := (kind,copy)
  have ht : ∀ i, origin p lag (s+p actual) i = s+lag+(p actual-p i) := by
    intro i
    dsimp [origin]
    ring
  have htactual : origin p lag (s+p actual) actual = s+lag := by
    rw [ht]
    ring
  refine ⟨copy, available_at A (τ := origin p lag (s+p actual)) (actual := actual) (H := H) ?_ ?_
    hnest ?_ ?_ ?_ ?_ ?_⟩
  · intro i
    rw [ht]
    exact hvis actual i
  · intro i j
    rw [ht,ht,show s+lag+(p actual-p i)-(s+lag+(p actual-p j)) = p j-p i by ring]
    exact hnear j i
  · rw [ht,ht,show s+lag+(p actual-p actual)-(s+lag+(p actual-p reference)) =
      p reference-p actual by ring]
    exact hover.trans (by have := hnear reference actual; omega)
  · rw [ht,ht,show s+lag+(p actual-p actual)-(s+lag+(p actual-p reference)) =
      p reference-p actual by ring]
    exact (hnear reference actual).trans_lt hover'
  · simpa only [htactual] using hend
  · simpa only [htactual] using hfailed
  · intro i hi hfail
    apply hcopy i
    simp only [Parameters.bad,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨Ne.symm hi,?_⟩
    simpa only [ht] using hfail

end SuffixDecoder

namespace SpacedStencil

lemma exists_points_fintype {P : Type uP2} [Fintype P] [LinearOrder P]
    (K : ℤ) (U : P → ℤ → Prop) (hU : ∀ i L, ∃ q, L < q ∧ U i q) :
    ∃ p : P → ℤ, (∀ i, U i (p i) ∧ K < p i) ∧
      ∀ i j, i < j → 2*p i+K < p j := by
  let e := Fintype.orderIsoFinOfCardEq P rfl
  obtain ⟨q,hq,hsep⟩ := exists_points (Fintype.card P) K (fun i => U (e i))
    (fun i L => hU (e i) L)
  refine ⟨fun i => q (e.symm i),?_,?_⟩
  · intro i
    simpa only [e.apply_symm_apply] using hq (e.symm i)
  · intro i j hij
    exact hsep _ _ (e.symm.strictMono hij)

lemma exists_boundaries {P : Type uP3} [Fintype P] {g : ℕ}
    (label : P → Fin g) (p : P → ℤ)
    (honto : Function.Surjective label) (hpos : ∀ a, 0 < p a)
    (hgap : ∀ a b, label a < label b → p a+1 < p b) :
    ∃ β : Fin (g+1) → ℤ, β 0 = 0 ∧ StrictMono β ∧
      ∀ a, β (label a).castSucc < p a ∧ p a < β (label a).succ := by
  classical
  have hsep : ∀ j : Fin (g+1), ∃ z : ℤ, (j=0 → z=0) ∧
      (∀ a, (label a).val < j.val → p a < z) ∧
      (∀ a, j.val ≤ (label a).val → z < p a) := by
    intro j
    by_cases hj : j=0
    · subst j
      exact ⟨0,fun _ => rfl,fun a ha => False.elim (Nat.not_lt_zero _ ha),fun a _ => hpos a⟩
    · have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj
      let F := Finset.univ.filter (fun a => (label a).val < j.val)
      have hF : F.Nonempty := by
        have hg : 0 < g := by omega
        obtain ⟨a,ha⟩ := honto ⟨0,hg⟩
        refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
        simpa only [ha] using hjpos
      obtain ⟨a,ha,hamax⟩ := Finset.exists_max_image F p hF
      have halabel := (Finset.mem_filter.mp ha).2
      refine ⟨p a+1,fun h => False.elim (hj h),?_,?_⟩
      · intro b hb
        have hh := hamax b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)
        omega
      · intro b hb
        exact hgap a b (by change (label a).val < (label b).val; omega)
  choose β hβ using hsep
  refine ⟨β,(hβ 0).1 rfl,?_,?_⟩
  · intro i j hij
    have hi : i.val < g := by have := j.isLt; exact lt_of_lt_of_le hij (Nat.le_of_lt_succ this)
    obtain ⟨a,ha⟩ := honto ⟨i.val,hi⟩
    have hleft := (hβ i).2.2 a (by simp only [ha]; exact le_refl _)
    have hright := (hβ j).2.1 a (by simp only [ha]; exact hij)
    exact hleft.trans hright
  · intro a
    exact ⟨(hβ (label a).castSucc).2.2 a (le_refl _),
      (hβ (label a).succ).2.1 a (Nat.lt_succ_self _)⟩

end SpacedStencil

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace WordIntervals

variable {Alphabet : Type uAlphabet} {M : Type uM} [Monoid M]

@[simp] lemma product_self (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet) (s : ℤ) :
    product T f s s = 1 := by
  simp only [product,piece,sub_self,Int.toNat_zero,segment,List.ofFn_zero]
  exact map_one T

lemma product_chain (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {g : ℕ} (p : Fin (g+1) → ℤ) (hp : Monotone p) :
    (List.ofFn (fun i : Fin g => product T f (p i.castSucc) (p i.succ))).prod =
      product T f (p 0) (p (Fin.last g)) := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [List.ofFn_succ,List.prod_cons]
    have htail := ih (fun i => p i.succ) (hp.comp (fun _ _ hab => Fin.succ_le_succ_iff.mpr hab))
    change product T f (p 0) (p 1) *
      (List.ofFn (fun i : Fin g => product T f (p i.castSucc.succ) (p i.succ.succ))).prod = _
    rw [htail]
    exact (product_append T f (hp (Fin.zero_le _)) (hp (Fin.le_last _))).symm

lemma product_chain_with_ends (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {g : ℕ} (p : Fin (g+1) → ℤ) (hp : Monotone p) {s b : ℤ}
    (hs : s ≤ p 0) (hb : p (Fin.last g) ≤ b) :
    product T f s b = product T f s (p 0) *
      (List.ofFn (fun i : Fin g => product T f (p i.castSucc) (p i.succ))).prod *
      product T f (p (Fin.last g)) b := by
  rw [product_chain T f p hp]
  rw [← product_append T f hs (hp (Fin.zero_le _))]
  exact product_append T f (hs.trans (hp (Fin.zero_le _))) hb

end WordIntervals

namespace ScheduleClock

open RobustClock PeriodicClock
open scoped BigOperators

theorem exists_ordered_stencil_clock {T : Type uT} {P : Type uP} {C : Type uC} [Fintype T] [Fintype P]
    [LinearOrder P] [Fintype C] (S : Specification T P C) (B : ℕ) (hB : 0 < B)
    (r : P → ℤ) (lower : (P → ℤ) → ℕ → ℕ) :
    ∃ (R : ℕ) (p : P → ℤ) (n a : C → ℕ),
      0 < R ∧
      (∀ i, p i % B = r i % B ∧ (2 * (B * R) + 2 : ℤ) < p i) ∧
      (∀ i j, i < j → 2 * p i + (2 * (B * R) + 2 : ℤ) < p j) ∧
      Function.Injective n ∧
      (∀ c, Nat.Prime (n c) ∧ lower p (B * R) < n c ∧ 1 ≤ a c ∧ a c < n c) ∧
      (∀ i, dist (speedMap (fun c => (a c : ℝ) / n c) (p i)) (S.v i) < S.η) ∧
      (∀ v : C → RobustClock.Circle, ∃ j : ℕ, j < R ∧
        dist (speedMap (fun c => (a c : ℝ) / n c) (j * B)) v < S.ρ) := by
  classical
  let ε := min (S.ρ / 3) (S.η / 3)
  have hε : 0 < ε := lt_min (div_pos S.radius_pos (by norm_num))
    (div_pos S.tolerance_pos (by norm_num))
  obtain ⟨n₀, hn₀inj, hn₀⟩ := prime_mesh (C := C) B hε
  have hprim c := (hn₀ c).1
  have hn₀pos c := (hprim c).pos
  have hpair := prime_pairwise n₀ hn₀inj hprim
  have hcop c := small_coprime (hprim c) hB (hn₀ c).2.1
  let R := ∏ c, n₀ c
  have hR : 0 < R := Finset.prod_pos (fun c _ => hn₀pos c)
  obtain ⟨p, hp, hspread⟩ := SpacedStencil.exists_points_fintype (2 * (B * R : ℕ) + 2)
    (fun i z => z % B = r i % B ∧
      dist (speedMap (fun c => 1 / (n₀ c : ℝ)) z) (S.v i) < ε)
    (fun i L => unbounded_residue n₀ hn₀pos hpair hB hcop hε
      (fun c => (hn₀ c).2.2) (r i) (S.v i) L)
  let F : Finset ℤ := Finset.univ.image p ∪ (Finset.range R).image (fun j => (j * B : ℕ))
  have hs c : 0 < (1 / (n₀ c : ℝ)) ∧ 1 / (n₀ c : ℝ) < 1 := by
    have hh : (1 : ℝ) < n₀ c := by exact_mod_cast (hprim c).one_lt
    exact ⟨by positivity, (div_lt_one (by positivity)).mpr hh⟩
  obtain ⟨n, a, hn, hna, hclose⟩ := approximate_finite (fun c => 1 / (n₀ c : ℝ)) hs
    (lower p (B * R)) F hε
  refine ⟨R, p, n, a, hR, fun i => ⟨(hp i).1.1, (hp i).2⟩, hspread,
    hn, hna, ?_, ?_⟩
  · intro i
    have hc := hclose (p i) (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, rfl⟩))
    have ht := (dist_triangle _ _ _).trans_lt (add_lt_add hc (hp i).1.2)
    have he : ε ≤ S.η / 3 := min_le_right _ _
    exact ht.trans (by linarith [S.tolerance_pos])
  · intro v
    obtain ⟨j, hj, hjv⟩ := net n₀ hn₀pos hpair B hcop hε (fun c => (hn₀ c).2.2) v
    have hc := hclose ((j * B : ℕ) : ℤ) (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr hj, rfl⟩))
    refine ⟨j, hj, ?_⟩
    have ht := (dist_triangle _ _ _).trans_lt (add_lt_add hc hjv)
    have he : ε ≤ S.ρ / 3 := min_le_left _ _
    exact ht.trans (by linarith [S.radius_pos])

end ScheduleClock

namespace ClockAffine

@[ext] lemma Snapshot.ext {M : Type uM2} [Monoid M] {g : ℕ} {a b : Snapshot M g}
    (hp : a.product = b.product) (hb : a.boundaries = b.boundaries) : a = b := by
  cases a; cases b; cases hp; cases hb; rfl

end ClockAffine

namespace BoundarySnapshot

open WordIntervals

variable {Alphabet : Type uAlphabet2} {M : Type uM3} [Monoid M] {g : ℕ}

def Present (search : Fin (g+1) → Option ℤ) (s b : ℤ) : Prop :=
  ∃ p : Fin (g+1) → ℤ, (∀ i, search i = some (p i)) ∧
    Monotone p ∧ s ≤ p 0 ∧ p (Fin.last g) ≤ b

lemma present_unique {search : Fin (g+1) → Option ℤ} {p q : Fin (g+1) → ℤ}
    (hp : ∀ i, search i = some (p i)) (hq : ∀ i, search i = some (q i)) : p = q := by
  funext i
  exact Option.some.inj ((hp i).symm.trans (hq i))

noncomputable def factors (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (s b : ℤ) (search : Fin (g+1) → Option ℤ) : Option (ClockAffine.Factors M g) := by
  classical
  exact if h : Present search s b then
    some ⟨product T f s (h.choose 0),
      (fun i => product T f (h.choose i.castSucc) (h.choose i.succ)),
      product T f (h.choose (Fin.last g)) b⟩
  else none

lemma factors_present (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {s b : ℤ} {search : Fin (g+1) → Option ℤ} {p : Fin (g+1) → ℤ}
    (hp : ∀ i, search i = some (p i)) (hmono : Monotone p)
    (hs : s ≤ p 0) (hb : p (Fin.last g) ≤ b) :
    factors T f s b search = some ⟨product T f s (p 0),
      (fun i => product T f (p i.castSucc) (p i.succ)),product T f (p (Fin.last g)) b⟩ := by
  have h : Present search s b := ⟨p,hp,hmono,hs,hb⟩
  rw [factors,dite_eq_left h]
  have he := present_unique h.choose_spec.1 hp
  simp only [he]

lemma factors_absent (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {s b : ℤ} {search : Fin (g+1) → Option ℤ} {i : Fin (g+1)}
    (hi : search i = none) : factors T f s b search = none := by
  unfold factors
  split_ifs with hp
  · have hh := (hp.choose_spec.1 i).symm.trans hi
    cases hh
  · rfl

noncomputable def actual (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (s b : ℤ) (search : Fin (g+1) → Option ℤ) : ClockAffine.Snapshot M g where
  product := product T f s b
  boundaries := factors T f s b search
  product_eq := by
    intro d hd
    unfold factors at hd
    split_ifs at hd with hp
    · cases Option.some.inj hd
      exact product_chain_with_ends T f hp.choose hp.choose_spec.2.1
        hp.choose_spec.2.2.1 hp.choose_spec.2.2.2

noncomputable def later (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (a b : ℤ) (search : Fin (g+1) → Option ℤ) : ClockAffine.Later M g where
  tailProduct := product T f a b
  boundaries := factors T f a b search
  tail_eq := (actual T f a b search).product_eq

lemma actual_eq_substitute (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {s a b : ℤ} {search : Fin (g+1) → Option ℤ}
    (hsa : s ≤ a) (hab : a ≤ b)
    (hstart : ∀ i p, search i = some p → a ≤ p)
 :
    actual T f s b search = (later T f a b search).substitute (product T f s a) := by
  classical
  have hpres : Present search s b ↔ Present search a b := by
    constructor
    · rintro ⟨p,hp,hm,_,hb⟩
      exact ⟨p,hp,hm,hstart 0 _ (hp 0),hb⟩
    · rintro ⟨p,hp,hm,ha,hb⟩
      exact ⟨p,hp,hm,hsa.trans ha,hb⟩
  have hprod := product_append T f hsa hab
  apply ClockAffine.Snapshot.ext
  · exact hprod
  · change factors T f s b search = (factors T f a b search).map _
    by_cases hh : Present search a b
    · let p := hh.choose
      have hp : ∀ i, search i = some (p i) := hh.choose_spec.1
      rw [factors_present T f hp hh.choose_spec.2.1
        (hsa.trans hh.choose_spec.2.2.1) hh.choose_spec.2.2.2,
        factors_present T f hp hh.choose_spec.2.1 hh.choose_spec.2.2.1 hh.choose_spec.2.2.2]
      simp only [Option.map_some]
      congr 2
      exact product_append T f hsa hh.choose_spec.2.2.1
    · simp only [factors,dite_eq_right hh,dite_eq_right (fun h => hh (hpres.mp h)),Option.map_none]

end BoundarySnapshot

namespace CanonicalEpisodes.Parameters

open EpisodeEnd

variable {Alphabet : Type uAlphabet3} (C : CanonicalEpisodes.Parameters Alphabet)

lemma end_lower {f : ℤ → Alphabet} {t b : ℤ}
    (he : EndAt C.d C.K C.tail f (t+C.offset) (C.small f (t+C.offset)) b) :
    t+C.offset - ((C.d : ℤ)+(C.B-1)*C.S) + C.tail ≤ b := by
  cases h : C.small f (t+C.offset) with
  | none =>
    rw [h] at he
    obtain ⟨v,hv,hm⟩ := he
    have hwidth : 0 ≤ (C.d : ℤ)+(C.B-1)*C.S := by
      have hB : 0 ≤ C.B-1 := by have := C.B_pos; omega
      have hS := C.S_nonneg
      positivity
    have hh := hm.1
    omega
  | some q =>
    rw [h] at he
    have hq := ((EndSearch.search_some C.B_pos C.S_nonneg).mp h).1.2
    have hw := (EndSearch.width_bounds (x := q-(t+C.offset)) (a := C.d)
      C.B_pos C.S_nonneg).2
    have hl := (abs_le.mp (hq.trans hw)).1
    dsimp only [EndAt] at he
    omega

end CanonicalEpisodes.Parameters

namespace ClockAffine

open RobustClock

variable {T : Type uT2} {P : Type uP2} {C : Type uC2} [Fintype T] [Fintype P] [Fintype C]
    (clock : Specification T P C)

lemma no_off_outside {z : C → RobustClock.Circle} (hz : z ∉ clock.W) :
    offChoice clock z = none := by
  cases hc : offChoice clock z with
  | none => rfl
  | some ab =>
    have hh := offChoice_some clock hc
    exact False.elim (hh.1 ((clock.diagonal z hz ab.1 ab.2).mp hh.2.1))

lemma net_cut (φ : ℤ →+ (C → RobustClock.Circle)) (B : ℕ) {R : ℕ}
    (hnet : ∀ v : C → RobustClock.Circle, ∃ a : ℕ, a < R ∧ dist (φ (a*B)) v < clock.ρ)
    {z : C → RobustClock.Circle} (hz : z ∉ clock.W) (tag : T) (base : ℤ) :
    ∃ a : ℕ, a < R ∧ φ (base+a*B) ∈ clock.I tag ∧ z-φ (base+a*B) ∈ clock.J tag := by
  obtain ⟨i,hi⟩ := clock.interior z hz tag
  obtain ⟨a,ha,had⟩ := hnet (i-φ base)
  refine ⟨a,ha,hi _ ?_⟩
  rw [map_add]
  have he : i = φ base + (i-φ base) := by abel
  rw [he]
  simpa only [dist_add_left] using had

end ClockAffine

namespace BoundarySnapshot

variable {g : ℕ}

def positions (search : Fin (g+1) → Option ℤ) : Fin (g+1) → ℤ :=
  fun i => (search i).getD 0

lemma positions_return {search : Fin (g+1) → Option ℤ} {i : Fin (g+1)}
    (hi : search i ≠ none) : search i = some (positions search i) := by
  cases h : search i with
  | none => exact False.elim (hi h)
  | some q => simp [positions,h]

lemma present_of_bounds {search : Fin (g+1) → Option ℤ} {s b : ℤ}
    (hp : ∀ i, search i ≠ none)
    (hstart : ∀ i p, search i = some p → s ≤ p)
    (hend : ∀ i p, search i = some p → p ≤ b)
    (horder : ∀ i j p q, i ≤ j → search i = some p → search j = some q → p ≤ q) :
    Present search s b :=
  ⟨positions search,fun i => positions_return (hp i),
    fun i j hij => horder i j _ _ hij (positions_return (hp i)) (positions_return (hp j)),
    hstart _ _ (positions_return (hp _)),hend _ _ (positions_return (hp _))⟩

lemma factors_positions {Alphabet : Type uAlphabet4} {M : Type uM4} [Monoid M]
    (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {search : Fin (g+1) → Option ℤ} {s b : ℤ} (hp : Present search s b) :
    factors T f s b search = some ⟨WordIntervals.product T f s (positions search 0),
      (fun i => WordIntervals.product T f (positions search i.castSucc) (positions search i.succ)),
      WordIntervals.product T f (positions search (Fin.last g)) b⟩ := by
  obtain ⟨p,hp,hm,hs,hb⟩ := hp
  have he : positions search = p := by
    funext i
    simp only [positions,hp,Option.getD_some]
  simpa only [he] using factors_present T f hp hm hs hb

end BoundarySnapshot

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace ObservedMain

open WordIntervals BoundarySnapshot SplitMetadata ClockAffine

variable {Alphabet : Type uAlphabet} {M : Type uM} {S : Type uS} {K : Type uK} {C : Type uC} [Monoid M] [Field K] [AddCommGroup S] [Module K S]
    {g B : ℕ}

variable (T : FreeMonoid Alphabet →* M) (ρ : M → (S →ₗ[K] S))
    (β : M → M → (Fin g → M) → S)

def Certificate (tag : MainTag M S g B) : Prop :=
  ∀ a, productTable ρ tag.A tag.C (insert tag.j tag.entries a) tag.input +
    β tag.A tag.C (insert tag.j tag.entries a) = tag.output

structure Prefix (tag : MainTag M S g B) (f : ℤ → Alphabet) (s : ℤ)
    (search : Fin (g+1) → Option ℤ) : Prop where
  present : ∀ i, i.val ≤ tag.j.val → search i ≠ none
  initial : product T f s (positions search 0) = tag.A
  earlier : ∀ i : {i : Fin g // i ≠ tag.j}, i.val < tag.j →
    product T f (positions search i.val.castSucc) (positions search i.val.succ) = tag.entries i
  certificate : Certificate ρ β tag

structure Suffix (tag : MainTag M S g B) (f : ℤ → Alphabet) (b : ℤ)
    (search : Fin (g+1) → Option ℤ) : Prop where
  present : ∀ i, tag.j.val < i.val → search i ≠ none
  final : product T f (positions search (Fin.last g)) b = tag.C
  later : ∀ i : {i : Fin g // i ≠ tag.j}, tag.j < i.val →
    product T f (positions search i.val.castSucc) (positions search i.val.succ) = tag.entries i

lemma pair_present {tag : MainTag M S g B} {f : ℤ → Alphabet} {s b : ℤ}
    {search : Fin (g+1) → Option ℤ} (hp : Prefix T ρ β tag f s search)
    (hq : Suffix T tag f b search) : ∀ i, search i ≠ none := by
  intro i
  by_cases hi : i.val ≤ tag.j.val
  · exact hp.present i hi
  · exact hq.present i (by omega)

lemma pair_entries {tag : MainTag M S g B} {f : ℤ → Alphabet} {s b : ℤ}
    {search : Fin (g+1) → Option ℤ} (hp : Prefix T ρ β tag f s search)
    (hq : Suffix T tag f b search) :
    ∀ i : {i : Fin g // i ≠ tag.j},
      product T f (positions search i.val.castSucc) (positions search i.val.succ) = tag.entries i := by
  intro i
  rcases lt_or_gt_of_ne i.property with hi | hi
  · exact hp.earlier i hi
  · exact hq.later i hi

lemma pair_sound {tag : MainTag M S g B} {f : ℤ → Alphabet} {s b : ℤ}
    {search : Fin (g+1) → Option ℤ} (hp : Prefix T ρ β tag f s search)
    (hq : Suffix T tag f b search) (hm : Present search s b) :
    ρ (actual T f s b search).product tag.input +
      (match (actual T f s b search).boundaries with
        | none => 0
        | some a => β a.A a.C a.entries) = tag.output := by
  have hf := factors_positions T f hm
  let d : Fin g → M := fun i => product T f (positions search i.castSucc) (positions search i.succ)
  have hentries : tag.entries = fun i => d i.val := by
    funext i
    exact (pair_entries T ρ β hp hq i).symm
  have hprod := (actual T f s b search).product_eq _ hf
  rw [hp.initial,hq.final] at hprod hf
  change ρ (actual T f s b search).product tag.input +
    (match factors T f s b search with | none => 0 | some a => β a.A a.C a.entries) = _
  rw [hf,hprod]
  change productTable ρ tag.A tag.C d tag.input + β tag.A tag.C d = _
  have hh := hp.certificate (d tag.j)
  simpa only [hentries,insert_actual] using hh

lemma available (f : ℤ → Alphabet) (s b : ℤ) (search : Fin (g+1) → Option ℤ)
    (hm : Present search s b) (u : Fin B) (x : S)
    (hβ : ∀ A C, ShiftTableProperty g (productTable ρ A C) (β A C)) :
    ∃ tag : MainTag M S g B, tag.u = u ∧ tag.input = x ∧
      Prefix T ρ β tag f s search ∧ Suffix T tag f b search ∧
      tag.output = ρ (actual T f s b search).product x +
        (match (actual T f s b search).boundaries with
          | none => 0
          | some a => β a.A a.C a.entries) := by
  let A := product T f s (positions search 0)
  let C' := product T f (positions search (Fin.last g)) b
  let d : Fin g → M := fun i => product T f (positions search i.castSucc) (positions search i.succ)
  obtain ⟨j,hj⟩ := certificate_available (productTable ρ A C') (β A C') (hβ A C') d x
  let tag : MainTag M S g B := ⟨j,u,A,C',fun i => d i.val,x,
    productTable ρ A C' d x + β A C' d⟩
  have hp : ∀ i, search i ≠ none := by
    obtain ⟨p,hp,_,_,_⟩ := hm
    intro i hi
    rw [hp i] at hi
    cases hi
  have hpre : Prefix T ρ β tag f s search :=
    ⟨fun i _ => hp i,rfl,fun _ _ => rfl,hj⟩
  have hsuf : Suffix T tag f b search := ⟨fun i _ => hp i,rfl,fun _ _ => rfl⟩
  exact ⟨tag,rfl,rfl,hpre,hsuf,(pair_sound T ρ β hpre hsuf hm).symm⟩

end ObservedMain

namespace SplitMetadata

open scoped BigOperators

variable {M : Type uM2} {S : Type uS2} [Fintype M] [Fintype S]

def tagCoefficient (M : Type uM3) (S : Type uS3) [Fintype M] [Fintype S] (g : ℕ) : ℕ :=
  Fintype.card S ^ 2 *
    (g * Fintype.card M ^ (g+1) + (g+1)*Fintype.card M)

lemma mainTag_card (g B : ℕ) (hg : 0 < g) :
    Fintype.card (MainTag M S g B) =
      B * Fintype.card S ^ 2 * g * Fintype.card M ^ (g+1) := by
  classical
  let e : MainTag M S g B ≃
      (Σ j : Fin g, Fin B × M × M × Omitted M g j × S × S) :=
    ⟨fun t => ⟨t.j, t.u,t.A,t.C,t.entries,t.input,t.output⟩,
      fun t => ⟨t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2.1,t.2.2.2.2.2.2⟩,
      fun t => by cases t; rfl, fun t => by cases t; rfl⟩
  have hc (j : Fin g) : Fintype.card {i : Fin g // i ≠ j} = g-1 := by
    simpa only [Fintype.card_fin,Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun i : Fin g => i=j)
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp only [Fintype.card_prod,Fintype.card_fin,Omitted,Fintype.card_fun,hc,
    Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have he : g+1 = (g-1)+2 := by omega
  rw [he,pow_add,pow_two]
  ring

lemma periodicTag_card (g B : ℕ) :
    Fintype.card (PeriodicTag M S g B) = B * Fintype.card S ^ 2 * (g+1) * Fintype.card M := by
  let e : PeriodicTag M S g B ≃ Fin (g+1) × Fin B × M × S × S :=
    ⟨fun t => (t.j,t.u,t.prefixProduct,t.input,t.output),
      fun t => ⟨t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2⟩,
      fun t => by cases t; rfl, fun t => by cases t; rfl⟩
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod,Fintype.card_fin]
  ring

lemma tag_card (g B : ℕ) (hg : 0 < g) :
    Fintype.card (Tag M S g B) = B * tagCoefficient M S g := by
  simp only [Tag,Fintype.card_sum,mainTag_card g B hg,periodicTag_card,tagCoefficient]
  ring

lemma tagCoefficient_pos (g : ℕ) [Nonempty M] [Nonempty S] :
    0 < tagCoefficient M S g := by
  have hM : 0 < Fintype.card M := Fintype.card_pos
  have hS : 0 < Fintype.card S := Fintype.card_pos
  dsimp [tagCoefficient]
  positivity

lemma exists_copies (g κ : ℕ) [Nonempty M] [Nonempty S] (hg : 0 < g) :
    ∃ μ : ℕ, 0 < μ ∧
      20 * (10000000 * Real.log
        (2 * Fintype.card (Tag M S g (20*(κ*μ+1)^3))) + 4*(g+1)) + 10 < μ := by
  have hD := tagCoefficient_pos (M := M) (S := S) g
  obtain ⟨μ,hμ,hbound⟩ := ScheduleCopies.exists_log_polynomial (κ : ℝ)
    (40 * tagCoefficient M S g) 200000000 (80*(g+1)+10)
    (by positivity) (by positivity) (by norm_num)
  refine ⟨μ,hμ,?_⟩
  rw [tag_card g _ hg]
  push_cast
  have he : (2:ℝ) * (20*((κ:ℝ)*μ+1)^3 * tagCoefficient M S g) =
      40 * tagCoefficient M S g * ((κ:ℝ)*μ+1)^3 := by ring
  rw [he]
  linarith

end SplitMetadata

namespace SourceSchedule

open scoped BigOperators

@[instance_reducible] noncomputable def blockOrder {P : Type uP} [Fintype P] {g : ℕ} (label : P → Fin g) :
    LinearOrder P :=
  LinearOrder.lift' (fun p => toLex (label p,(Fintype.equivFin P) p)) (by
    intro a b he
    have hh := congrArg (fun x => (ofLex x).2) he
    exact (Fintype.equivFin P).injective hh)

lemma block_lt {P : Type uP2} [Fintype P] {g : ℕ} (label : P → Fin g)
    {a b : P} (hab : label a < label b) :
    @LT.lt P (blockOrder label).toLT a b :=
  Prod.Lex.left _ _ hab

noncomputable def absoluteBound {P : Type uP3} [Fintype P] (p : P → ℤ) : ℕ :=
  Finset.univ.sup (fun i => (p i).natAbs)

lemma abs_le_absoluteBound {P : Type uP4} [Fintype P] (p : P → ℤ) (i : P) :
    |p i| ≤ (absoluteBound p : ℤ) := by
  have hh : (p i).natAbs ≤ absoluteBound p :=
    Finset.le_sup (f := fun i => (p i).natAbs) (Finset.mem_univ i)
  simpa only [Int.natCast_natAbs] using (show ((p i).natAbs : ℤ) ≤ absoluteBound p by exact_mod_cast hh)

lemma difference_bound {P : Type uP5} [Fintype P] (p : P → ℤ) (i j : P) :
    |p i-p j| ≤ 2 * (absoluteBound p : ℤ)+1 := by
  exact (abs_sub _ _).trans (by linarith [abs_le_absoluteBound p i,abs_le_absoluteBound p j])

noncomputable def innerD {P : Type uP6} [Fintype P] (p : P → ℤ) (w₀ : ℕ) : ℕ :=
  10*(2*(2*absoluteBound p+1)+2*w₀+5)+1

lemma innerD_ge {P : Type uP7} [Fintype P] (p : P → ℤ) (w₀ : ℕ) : 2 ≤ innerD p w₀ := by
  dsimp [innerD]
  omega

lemma innerD_bound {P : Type uP8} [Fintype P] (p : P → ℤ) (w₀ : ℕ) :
    10*(2*(2*(absoluteBound p : ℤ)+1)+2*w₀+5) < innerD p w₀ := by
  simp only [innerD,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  omega

structure Early {Alphabet : Type uAlphabet2} {T : Type uT} {P : Type uP9} {C : Type uC2} [Fintype T] [Fintype P] [Fintype C]
    {g' : ℕ} (clock : RobustClock.Specification T P C) (B size : ℕ)
    (label : P → Fin g') (reserved : P → ℤ) where
  R : ℕ
  p : P → ℤ
  β : Fin (g'+1) → ℤ
  denominator : C → ℕ
  numerator : C → ℕ
  R_pos : 0 < R
  reserved_eq : ∀ i, p i % B = reserved i % B
  p_pos : ∀ i, 0 < p i
  separated : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
    (2*(B*R)+2 : ℤ) < |(p i-p j)-(p i'-p j')|
  separated_zero : ∀ i j, i ≠ j → (2*(B*R)+2 : ℤ) < |p i-p j|
  β_zero : β 0 = 0
  β_strict : StrictMono β
  block : ∀ i, β (label i).castSucc < p i ∧ p i < β (label i).succ
  prime : ∀ c, Nat.Prime (denominator c)
  den_injective : Function.Injective denominator
  den_large : ∀ c, max B (max (innerD p (B*R)) size.factorial) < denominator c
  num_bounds : ∀ c, 1 ≤ numerator c ∧ numerator c < denominator c
  approximate : ∀ i, dist
    (PeriodicClock.speedMap (fun c => (numerator c : ℝ)/denominator c) (p i)) (clock.v i) < clock.η
  net : ∀ v : C → RobustClock.Circle, ∃ a : ℕ, a<R ∧ dist
    (PeriodicClock.speedMap (fun c => (numerator c : ℝ)/denominator c) (a*B)) v < clock.ρ
  rule : LocalMarkers.Rule Alphabet (innerD p (B*R)) (3*(innerD p (B*R))^2+1)
  inner : IntegerSchedules.Inner B (∏c,denominator c) R size (innerD p (B*R))
    (3*(innerD p (B*R))^2+1) rule.r (2*(absoluteBound p : ℤ)+1)

lemma exists_early {Alphabet : Type uAlphabet3} {T : Type uT2} {P : Type uP10} {C : Type uC3} [Fintype Alphabet] [Fintype T]
    [Fintype P] [Fintype C] {g' : ℕ} (clock : RobustClock.Specification T P C)
    (B size : ℕ) (hB : 0 < B) (label : P → Fin g') (honto : Function.Surjective label)
    (reserved : P → ℤ) : Nonempty (Early (Alphabet := Alphabet) clock B size label reserved) := by
  classical
  let : LinearOrder P := blockOrder label
  obtain ⟨R,p,n,a,hR,hp,hspread,hn,hna,hpert,hnet⟩ :=
    ScheduleClock.exists_ordered_stencil_clock clock B hB reserved
      (fun p w₀ => max B (max (innerD p w₀) size.factorial))
  have hK : (0 : ℤ) ≤ 2*(B*R)+2 := by positivity
  have hp' : ∀ i, (2*(B*R)+2 : ℤ) < p i := fun i => (hp i).2
  have hpos : ∀ i, 0 < p i := fun i => hK.trans_lt (hp' i)
  obtain ⟨β,hβ₀,hβ,hblock⟩ := SpacedStencil.exists_boundaries label p honto hpos (by
    intro i j hij
    have hh := hspread i j (block_lt label hij)
    have hi := hpos i
    omega)
  obtain ⟨rule⟩ := LocalMarkers.nonempty_rule (Alphabet := Alphabet)
    (d := innerD p (B*R)) (K := 3*(innerD p (B*R))^2+1)
    (innerD_ge p (B*R)) (by omega)
  obtain ⟨inner⟩ := IntegerSchedules.exists_inner B (∏c,n c) R size
    (innerD p (B*R)) (3*(innerD p (B*R))^2+1) rule.r
    (2*(absoluteBound p : ℤ)+1) hB
  exact ⟨⟨R,p,β,n,a,hR,fun i => (hp i).1,hpos,
    fun _ _ _ _ hij hkl hne => SpacedStencil.ordered_differences hK hp' hspread hij hkl hne,
    fun _ _ hij => SpacedStencil.nonzero_differences hK hp' hspread hij,
    hβ₀,hβ,hblock,fun c => (hna c).1,hn,fun c => (hna c).2.1,
    fun c => (hna c).2.2,hpert,hnet,rule,inner⟩⟩

end SourceSchedule

namespace ObservedInner

open WordIntervals SplitMetadata

variable {Alphabet : Type uAlphabet4} {M : Type uM4} {U : Type uU} {K : Type uK2} [Monoid M] [Field K]
  [AddCommGroup U] [Module K U] {g : ℕ}

def table (ψ : M → (U →ₗ[K] U)) (d : Fin g → M) : U →ₗ[K] U :=
  ψ (List.ofFn d).prod

variable (T : FreeMonoid Alphabet →* M)
  (β : (M → (U →ₗ[K] U)) → (Fin g → M) → U)

def Certificate (kind : Kind M U K g) : Prop :=
  ∀ a, table kind.hypothetical (insert kind.j kind.entries a) kind.input +
    β kind.hypothetical (insert kind.j kind.entries a) = kind.output

structure Prefix (kind : Kind M U K g) (f : ℤ → Alphabet)
    (boundary : Fin (g+1) → ℤ) : Prop where
  earlier : ∀ i : {i : Fin g // i ≠ kind.j}, i.val < kind.j →
    product T f (boundary i.val.castSucc) (boundary i.val.succ) = kind.entries i
  certificate : Certificate β kind

structure Suffix (kind : Kind M U K g) (f : ℤ → Alphabet)
    (boundary : Fin (g+1) → ℤ) (ψ : M → (U →ₗ[K] U)) : Prop where
  later : ∀ i : {i : Fin g // i ≠ kind.j}, kind.j < i.val →
    product T f (boundary i.val.castSucc) (boundary i.val.succ) = kind.entries i
  hypothetical_eq : ψ = kind.hypothetical

lemma prefix_congr {kind : Kind M U K g} {f f' : ℤ → Alphabet}
    {boundary : Fin (g+1) → ℤ} {k : ℤ} (hm : Monotone boundary)
    (hk : boundary kind.j.castSucc ≤ k)
    (he : LocalMarkers.AgreesOn f f' (boundary 0) k)
    (hp : Prefix T β kind f boundary) : Prefix T β kind f' boundary := by
  refine ⟨?_,hp.certificate⟩
  intro i hi
  rw [← hp.earlier i hi]
  apply product_congr T (hm (Fin.castSucc_le_succ i.val))
  intro x hx hx'
  exact (he x ((hm (Fin.zero_le _)).trans hx) (hx'.trans_le ((hm (by
    change i.val.val + 1 ≤ kind.j.val
    exact hi)).trans hk))).symm

lemma suffix_congr {kind : Kind M U K g} {f f' : ℤ → Alphabet}
    {boundary : Fin (g+1) → ℤ} {k : ℤ} {ψ : M → (U →ₗ[K] U)}
    (hm : Monotone boundary) (hk : k ≤ boundary kind.j.succ)
    (he : LocalMarkers.AgreesOn f f' k (boundary (Fin.last g)))
    (hq : Suffix T kind f boundary ψ) : Suffix T kind f' boundary ψ := by
  refine ⟨?_,hq.hypothetical_eq⟩
  intro i hi
  rw [← hq.later i hi]
  apply product_congr T (hm (Fin.castSucc_le_succ i.val))
  intro x hx hx'
  exact (he x ((hk.trans (hm (by change kind.j.val + 1 ≤ i.val.val; exact hi))).trans hx)
    (hx'.trans_le (hm (Fin.le_last _)))).symm

lemma pair_sound {kind : Kind M U K g} {f : ℤ → Alphabet}
    {boundary : Fin (g+1) → ℤ} {ψ : M → (U →ₗ[K] U)}
    (hp : Prefix T β kind f boundary) (hq : Suffix T kind f boundary ψ) :
    let d := fun i : Fin g => product T f (boundary i.castSucc) (boundary i.succ)
    table ψ d kind.input + β ψ d = kind.output := by
  let d := fun i : Fin g => product T f (boundary i.castSucc) (boundary i.succ)
  have he : kind.entries = fun i => d i.val := by
    funext i
    rcases lt_or_gt_of_ne i.property with hi | hi
    · exact (hp.earlier i hi).symm
    · exact (hq.later i hi).symm
  have hh := hp.certificate (d kind.j)
  rw [he,insert_actual] at hh
  simpa only [hq.hypothetical_eq] using hh

lemma available (f : ℤ → Alphabet) (boundary : Fin (g+1) → ℤ)
    (ψ : M → (U →ₗ[K] U)) (x : U)
    (hβ : ShiftTableProperty g (table ψ) (β ψ)) :
    ∃ kind : Kind M U K g, kind.input = x ∧
      Prefix T β kind f boundary ∧ Suffix T kind f boundary ψ ∧
      kind.output = table ψ
        (fun i => product T f (boundary i.castSucc) (boundary i.succ)) x +
        β ψ (fun i => product T f (boundary i.castSucc) (boundary i.succ)) := by
  let d := fun i : Fin g => product T f (boundary i.castSucc) (boundary i.succ)
  obtain ⟨j,hj⟩ := certificate_available (table ψ) (β ψ) hβ d x
  let kind : Kind M U K g := ⟨j,x,table ψ d x + β ψ d,fun i => d i.val,ψ⟩
  exact ⟨kind,rfl,⟨fun _ _ => rfl,hj⟩,⟨fun _ _ => rfl,rfl⟩,rfl⟩

lemma linear_part (f : ℤ → Alphabet) (boundary : Fin (g+1) → ℤ)
    (hm : Monotone boundary) (ψ : M → (U →ₗ[K] U)) :
    table ψ (fun i => product T f (boundary i.castSucc) (boundary i.succ)) =
      ψ (product T f (boundary 0) (boundary (Fin.last g))) := by
  exact congrArg ψ (product_chain T f boundary hm)

end ObservedInner

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace PeriodicTemplates

open WordIntervals LocalMarkers

variable {Alphabet : Type uAlphabet}

lemma segment_power {v : ℤ → Alphabet} {p : ℕ}
    (hp : Function.Periodic v (p : ℤ)) (s : ℤ) (q : ℕ) :
    segment v s (q*p) = wordPower (segment v s p) q := by
  induction q with
  | zero => simp [WordIntervals.segment]
  | succ q ih =>
    rw [Nat.succ_mul,segment_add,ih,wordPower_add,wordPower_one]
    congr 1
    simpa only [Nat.cast_mul] using PeriodicCuts.segment_shift_period hp s q p

lemma decompose_middle {w : List Alphabet} {f v : ℤ → Alphabet} {N tail p : ℕ}
    (hf : Realizes w 0 f) (hlen : N+tail ≤ w.length) (hp : 0 < p)
    (hper : Function.Periodic v (p : ℤ))
    (he : AgreesOn f v N (w.length-tail)) :
    ∃ a c b : List Alphabet, a.length = N ∧ c.length = p ∧ b.length < p+tail ∧
      ∃ q, w = a ++ wordPower c q ++ b := by
  let m := w.length-N-tail
  let q := m/p
  let r := m%p
  have hr : r<p := Nat.mod_lt _ hp
  have hm : m = q*p+r := by
    simpa only [q,r,Nat.mul_comm] using (Nat.div_add_mod m p).symm
  have hlen' : w.length = N+m+tail := by
    have : m = w.length-N-tail := rfl
    omega
  let a := segment f 0 N
  let c := segment v N p
  let b := segment v N r ++ segment f (N+m) tail
  refine ⟨a,c,b,length_segment _ _ _,length_segment _ _ _,?_,q,?_⟩
  · simpa only [b,List.length_append,length_segment] using Nat.add_lt_add_right hr tail
  · have hw : w = segment f 0 w.length := (realizes_iff_segment.mp hf).symm
    rw [hw,hlen',segment_add,segment_add]
    simp only [zero_add,Nat.cast_add]
    have he' : segment f N m = segment v N m := by
      apply segment_congr
      intro x hx hx'
      apply he x hx
      rw [hlen']
      push_cast
      omega
    rw [he',hm,segment_add,segment_power hper]
    have hs : segment v ((N : ℤ)+(q*p : ℕ)) r = segment v N r := by
      simpa only [Nat.cast_mul] using PeriodicCuts.segment_shift_period hper N q r
    rw [hs]
    simp only [a,c,b,List.append_assoc]
    rw [← hm]

noncomputable def boundedTemplates [Finite Alphabet] (A C B : ℕ) :
    Finset (Template Alphabet) :=
  (List.finite_length_le Alphabet A).toFinset ×ˢ
    ((List.finite_length_le Alphabet C).toFinset ×ˢ
      (List.finite_length_le Alphabet B).toFinset)

lemma mem_boundedTemplates [Finite Alphabet] (A C B : ℕ) (a c b : List Alphabet) :
    (a,c,b) ∈ boundedTemplates A C B ↔ a.length≤A ∧ c.length≤C ∧ b.length≤B := by
  simp only [boundedTemplates,Finset.mem_product,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

lemma finite_cover_of_middle [Finite Alphabet] (L : Language Alphabet) (short N tail d : ℕ)
    (h : ∀ w ∈ L, w.length ≤ short ∨
      ∃ (f v : ℤ → Alphabet) (p : ℕ), Realizes w 0 f ∧ N+tail≤w.length ∧
        0<p ∧ p≤d ∧ Function.Periodic v (p : ℤ) ∧
        AgreesOn f v N (w.length-tail)) :
    ∃ templates : Finset (Template Alphabet),
      ∀ w ∈ L, ∃ t ∈ templates, ∃ i, w = instanceWord t i := by
  refine ⟨boundedTemplates (max short N) d (d+tail),?_⟩
  intro w hw
  rcases h w hw with hs | ⟨f,v,p,hf,hlen,hp,hpd,hper,he⟩
  · refine ⟨(w,[],[]),(mem_boundedTemplates _ _ _ _ _ _).mpr ?_,0,?_⟩
    · exact ⟨hs.trans (le_max_left _ _),by simp,by simp⟩
    · simp [instanceWord]
  · obtain ⟨a,c,b,ha,hc,hb,q,hq⟩ := decompose_middle hf hlen hp hper he
    refine ⟨(a,c,b),(mem_boundedTemplates _ _ _ _ _ _).mpr ?_,q,hq⟩
    exact ⟨ha ▸ le_max_right _ _,hc ▸ hpd,hb.le.trans (Nat.add_le_add_right hpd tail)⟩

lemma regular_middle_height [Finite Alphabet] (L : Language Alphabet) (hL : L.IsRegular)
    (short N tail d : ℕ)
    (h : ∀ w ∈ L, w.length ≤ short ∨
      ∃ (f v : ℤ → Alphabet) (p : ℕ), Realizes w 0 f ∧ N+tail≤w.length ∧
        0<p ∧ p≤d ∧ Function.Periodic v (p : ℤ) ∧
        AgreesOn f v N (w.length-tail)) : HasHeightAtMost L 1 := by
  obtain ⟨templates,hcover⟩ := finite_cover_of_middle L short N tail d h
  exact regular_cover_height L hL templates hcover

end PeriodicTemplates

namespace ExceptionalOrigins.Parameters

open LocalMarkers

variable {Alphabet : Type uAlphabet2} {J : Type uJ} {C : Type uC} (A : ExceptionalOrigins.Parameters Alphabet J C)

def InnerVisible (s b t : ℤ) (j : J) (u : Fin A.B) : Prop :=
  s ≤ t+A.offset j-A.innerRule.r ∧ t+A.offset j+A.H u+A.innerRule.r ≤ b

lemma inner_congr {f g : ℤ → Alphabet} {s b t : ℤ} {j : J} {u : Fin A.B}
    (hv : A.InnerVisible s b t j u) (he : AgreesOn f g s b) :
    A.inner f j u t = A.inner g j u t := by
  apply MarkerSearch.search_congr
  intro m hm hm'
  apply A.innerRule.locality
  intro x hx hx'
  exact he x (by have := hv.1; omega) (by have := hv.2; omega)

lemma inner_bounds {f : ℤ → Alphabet} {j : J} {u : Fin A.B} {t p : ℤ}
    (hp : A.inner f j u t = some p) : t+A.offset j ≤ p ∧ p ≤ t+A.offset j+A.H u := by
  exact ⟨(MarkerSearch.search_some.mp hp).1.2.1,(MarkerSearch.search_some.mp hp).2⟩

lemma inner_position_bounds {g : ℕ} (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    {f : ℤ → Alphabet} {u : Fin A.B} {s b t : ℤ} {j : Fin (g+1)}
    (hv : A.InnerVisible s b t j u) (hp : A.inner f j u t ≠ none) :
    s ≤ BoundarySnapshot.positions (fun i => A.inner f i u t) j ∧
      BoundarySnapshot.positions (fun i => A.inner f i u t) j ≤ b := by
  have hb := A.inner_bounds (f := f) (t := t) (j := j) (u := u)
    (BoundarySnapshot.positions_return (search := fun i => A.inner f i u t) (i := j) hp)
  have hr := A.innerRule.radius_ge
  exact ⟨by have := hv.1;omega,by have := hv.2;omega⟩

end ExceptionalOrigins.Parameters

namespace ObservedMain

open WordIntervals BoundarySnapshot SplitMetadata

variable {Alphabet : Type uAlphabet3} {M : Type uM} {S : Type uS} {K : Type uK} [Monoid M] [Field K] [AddCommGroup S] [Module K S]
    {g B : ℕ}
variable (T : FreeMonoid Alphabet →* M) (ρ : M → (S →ₗ[K] S))
    (β : M → M → (Fin g → M) → S)

structure PrefixRead (tag : MainTag M S g B) (f : ℤ → Alphabet) (s k : ℤ)
    (search : Fin (g+1) → Option ℤ) : Prop extends Prefix T ρ β tag f s search where
  bounds : ∀ i, i.val ≤ tag.j.val → s ≤ positions search i ∧ positions search i ≤ k
  ordered : ∀ i : Fin g, i < tag.j → positions search i.castSucc ≤ positions search i.succ

structure SuffixRead (tag : MainTag M S g B) (f : ℤ → Alphabet) (k b : ℤ)
    (search : Fin (g+1) → Option ℤ) : Prop extends Suffix T tag f b search where
  bounds : ∀ i, tag.j.val < i.val → k ≤ positions search i ∧ positions search i ≤ b
  ordered : ∀ i : Fin g, tag.j < i → positions search i.castSucc ≤ positions search i.succ

lemma PrefixRead.transfer {tag : MainTag M S g B} {f f' : ℤ → Alphabet} {s k : ℤ}
    {search search' : Fin (g+1) → Option ℤ}
    (hp : PrefixRead T ρ β tag f s k search) (he : LocalMarkers.AgreesOn f f' s k)
    (hs : ∀ i, i.val ≤ tag.j.val → search i = search' i) :
    PrefixRead T ρ β tag f' s k search' := by
  have hpos : ∀ i, i.val ≤ tag.j.val → positions search i = positions search' i := by
    intro i hi
    simp only [positions,hs i hi]
  have hzero : (0 : Fin (g+1)).val ≤ tag.j.val := by simp
  have hp0 := hp.bounds 0 hzero
  refine ⟨⟨?_,?_,?_,hp.certificate⟩,?_,?_⟩
  · intro i hi; rw [←hs i hi]; exact hp.present i hi
  · rw [←hpos 0 hzero,←hp.initial]
    symm
    apply product_congr T hp0.1
    intro z hz hz'
    exact he z hz (hz'.trans_le hp0.2)
  · intro i hi
    have h₁ : i.val.castSucc.val ≤ tag.j.val := Nat.le_of_lt hi
    have h₂ : i.val.succ.val ≤ tag.j.val := hi
    rw [←hpos _ h₁,←hpos _ h₂,←hp.earlier i hi]
    symm
    apply product_congr T (hp.ordered i.val hi)
    intro z hz hz'
    exact he z ((hp.bounds _ h₁).1.trans hz) (hz'.trans_le (hp.bounds _ h₂).2)
  · intro i hi; rw [←hpos i hi]; exact hp.bounds i hi
  · intro i hi
    rw [←hpos _ (Nat.le_of_lt hi),←hpos _ (show i.val+1 ≤ tag.j.val from hi)]
    exact hp.ordered i hi

omit [AddCommGroup S] in
lemma SuffixRead.transfer {tag : MainTag M S g B} {f f' : ℤ → Alphabet} {k b : ℤ}
    {search search' : Fin (g+1) → Option ℤ}
    (hq : SuffixRead T tag f k b search) (he : LocalMarkers.AgreesOn f f' k b)
    (hs : ∀ i, tag.j.val < i.val → search i = search' i) :
    SuffixRead T tag f' k b search' := by
  have hpos : ∀ i, tag.j.val < i.val → positions search i = positions search' i := by
    intro i hi
    simp only [positions,hs i hi]
  have hlast : tag.j.val < (Fin.last g).val := tag.j.isLt
  have hp0 := hq.bounds (Fin.last g) hlast
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro i hi; rw [←hs i hi]; exact hq.present i hi
  · rw [←hpos _ hlast,←hq.final]
    symm
    apply product_congr T hp0.2
    intro z hz hz'
    exact he z (hp0.1.trans hz) hz'
  · intro i hi
    have h₁ : tag.j.val < i.val.castSucc.val := hi
    have h₂ : tag.j.val < i.val.succ.val := Nat.lt_succ_of_lt hi
    rw [←hpos _ h₁,←hpos _ h₂,←hq.later i hi]
    symm
    apply product_congr T (hq.ordered i.val hi)
    intro z hz hz'
    exact he z ((hq.bounds _ h₁).1.trans hz) (hz'.trans_le (hq.bounds _ h₂).2)
  · intro i hi; rw [←hpos i hi]; exact hq.bounds i hi
  · intro i hi
    rw [←hpos _ hi,←hpos _ (Nat.lt_succ_of_lt hi)]
    exact hq.ordered i hi

end ObservedMain

namespace OuterStream

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical

structure Cuts (g B : ℕ) where
  main : Fin g → ℤ
  periodic : Fin (g+1) → Fin B → ℤ
  R : ℕ
  N : ℕ
  R_pos : 0 < R
  N_pos : 0 < N

namespace Cuts

variable {g B : ℕ} (H : Cuts g B)

abbrev Role (_H : Cuts g B) := Fin g ⊕ (Fin (g+1) × Fin B)

def base : H.Role → ℤ
  | .inl j => H.main j
  | .inr (j,u) => H.periodic j u

def count : H.Role → ℕ
  | .inl _ => H.R
  | .inr _ => H.N

noncomputable def offsets : Finset ℤ :=
  Finset.univ.biUnion fun role : H.Role => (Finset.range (H.count role)).image
    (fun a : ℕ => H.base role + (a:ℤ)*(B:ℤ))

lemma offset_mem (role : H.Role) (a : ℕ) (ha : a < H.count role) :
    H.base role+a*B ∈ H.offsets := by
  exact Finset.mem_biUnion.mpr ⟨role,Finset.mem_univ _,Finset.mem_image.mpr
    ⟨a,Finset.mem_range.mpr ha,rfl⟩⟩

def tagRole (H : Cuts g B) {M : Type uM2} {S : Type uS2} : Tag M S g B → H.Role
  | .inl m => .inl m.j
  | .inr p => .inr (p.j,p.u)

noncomputable def origins (k : ℤ) : Finset ℤ := H.offsets.image (fun h => k-h)

lemma true_origin {M : Type uM3} {S : Type uS3} (tag : Tag M S g B) {t k : ℤ}
    (hcut : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*B) :
    t ∈ H.origins k := by
  obtain ⟨a,ha,hk⟩ := hcut
  apply Finset.mem_image.mpr
  exact ⟨_,H.offset_mem _ _ ha,by omega⟩

end Cuts

variable {Alphabet : Type uAlphabet4} {M : Type uM4} {V : Type uV} {K : Type uK2} {P : Type uP} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}

variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

noncomputable def search (f : ℤ → Alphabet) (u : Fin A.B) (t : ℤ) : Fin (g+1) → Option ℤ :=
  fun i => A.inner f i u t

noncomputable def snapshot (f : ℤ → Alphabet) (s b t : ℤ) : ClockAffine.Snapshot M g :=
  actual T f s b (search A f (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t)

noncomputable def update (f : ℤ → Alphabet) (s b t : ℤ) (x : V) : V :=
  ClockAffine.update clock ρ β Tag.input Tag.output
    (A.φ (A.anchor f (b-A.endRule.tail) t-t)) (snapshot A T f s b t) x

structure PrefixMain (tag : MainTag M V g A.B) (f : ℤ → Alphabet) (s t k : ℤ) : Prop where
  visible : ∀ i, i.val ≤ tag.j.val → A.InnerVisible s k t i tag.u
  observed : ObservedMain.PrefixRead T ρ β tag f s k (search A f tag.u t)

structure PrefixPeriodic (tag : PeriodicTag M V g A.B) (f : ℤ → Alphabet)
    (s t k : ℤ) : Prop where
  visible : A.InnerVisible s k t tag.j tag.u
  absent : A.inner f tag.j tag.u t = none
  product_eq : product T f s k = tag.prefixProduct

structure Prefix (tag : Tag M V g A.B) (f : ℤ → Alphabet) (s t k : ℤ) : Prop where
  positive : s < k
  cut : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*A.B
  clock_mem : A.φ (k-t) ∈ clock.I tag
  letter_test : match tag with
    | .inl tag => PrefixMain A T ρ β tag f s t k
    | .inr tag => PrefixPeriodic A T tag f s t k

structure SuffixMain (tag : MainTag M V g A.B) (f : ℤ → Alphabet) (k b : ℤ) : Prop where
  visible : ∀ a : ℕ, a < H.R → ∀ i, tag.j.val < i.val →
    A.InnerVisible k b (k-H.main tag.j-a*A.B) i tag.u
  stable : ∀ a : ℕ, a < H.R → ∀ i, tag.j.val < i.val →
    A.inner f i tag.u (k-H.main tag.j-a*A.B) = A.inner f i tag.u (k-H.main tag.j)
  observed : ObservedMain.SuffixRead T tag f k b (search A f tag.u (k-H.main tag.j))

noncomputable def suffixAnchor (reference k b : ℤ) (f : ℤ → Alphabet) : ℤ :=
  A.anchor f (b-A.endRule.tail) (k-reference)

structure Suffix (reference : ℤ) (tag : Tag M V g A.B) (f : ℤ → Alphabet)
    (k b : ℤ) : Prop where
  ordered : k ≤ b
  guard : A.endRule.Guard (H.origins k) (k-reference) k b f
  clock_mem : A.φ (suffixAnchor A reference k b f-k) ∈ clock.J tag
  residue_eq : A.residue (suffixAnchor A reference k b f-k) = tag.residue
  letter_test : match tag with
    | .inl tag => SuffixMain A H T tag f k b
    | .inr tag => tag.output = ρ (tag.prefixProduct * product T f k b) tag.input

end OuterStream

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace OuterStream

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical

variable {Alphabet : Type uAlphabet} {M : Type uM} {V : Type uV} {K : Type uK} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

structure Geometry : Prop where
  multiple : ∀ role : H.Role, (A.B : ℤ) ∣ H.base role
  boundary_order : ∀ (u : Fin A.B) (i j : Fin (g+1)), i < j →
    A.offset i + A.H u ≤ A.offset j
  end_left : ∀ h ∈ H.offsets, h + A.endRule.width + A.endRule.rule.r ≤ A.endRule.offset
  end_right : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets,
    h-h'+A.endRule.width+A.endRule.rule.r+
      ((A.endRule.d : ℤ)+(A.endRule.B-1)*A.endRule.S) ≤ A.endRule.tail
  seed_right : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets,
    h-h'+A.endRule.K+((A.endRule.d : ℤ)+(A.endRule.B-1)*A.endRule.S) ≤ A.endRule.tail
  overlap : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets,
    (A.endRule.d : ℤ)^2 + |h-h'| ≤ A.endRule.K

variable {A H}

omit [Monoid M] [AddCommGroup V] [Fintype M] [Fintype V] [Fintype C] in
lemma Geometry.actual_visibility (G : Geometry A H) {f : ℤ → Alphabet} {t k b : ℤ}
    {tag : Tag M V g A.B}
    (hc : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*A.B)
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b) :
    ∀ o ∈ H.origins k, A.endRule.Visible k b (o+A.endRule.offset) := by
  obtain ⟨a,ha,hk⟩ := hc
  have hmem := H.offset_mem (H.tagRole tag) a ha
  have hb := A.endRule.end_lower he
  have hw := A.endRule.width_nonneg
  have hr := A.endRule.rule.radius_ge
  intro o ho
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp ho
  have hleft := G.end_left h hh
  have hright := G.end_right _ hmem h hh
  have hseed := G.seed_right _ hmem h hh
  refine ⟨by omega,by omega,by omega,by omega⟩

omit [Monoid M] [AddCommGroup V] [Fintype M] [Fintype V] [Fintype C] in
lemma Geometry.origin_overlap (G : Geometry A H) {t k r : ℤ} {tag : Tag M V g A.B}
    (hc : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*A.B)
    (hr : r ∈ H.origins k) :
    (A.endRule.d : ℤ)^2 ≤ (A.endRule.K : ℤ)-|t-r| ∧ |t-r| < A.endRule.K := by
  obtain ⟨a,ha,hk⟩ := hc
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hr
  have hmem := H.offset_mem (H.tagRole tag) a ha
  have hov := G.overlap _ hmem h hh
  have heq : t-(k-h) = -(H.base (H.tagRole tag)+(a:ℤ)*A.B-h) := by omega
  have hd := A.endRule.d_ge
  have hd' : (2:ℤ) ≤ A.endRule.d := by exact_mod_cast hd
  rw [heq,abs_neg]
  constructor <;> nlinarith

omit [Fintype C] in
lemma Geometry.present (G : Geometry A H) {f : ℤ → Alphabet} {u : Fin A.B} {s b t : ℤ}
    (hv : ∀ j, A.InnerVisible s b t j u) (hp : ∀ j, A.inner f j u t ≠ none) :
    Present (search A f u t) s b := by
  apply present_of_bounds hp
  · intro i p he
    have hb := A.inner_bounds he
    have hh := (hv i).1
    have hr := A.innerRule.radius_ge
    omega
  · intro i p he
    have hb := A.inner_bounds he
    have hh := (hv i).2
    have hr := A.innerRule.radius_ge
    omega
  · intro i j p q hij hi hj
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_of_eq (Option.some.inj (hi.symm.trans hj))
    · have hp' := A.inner_bounds hi
      have hq' := A.inner_bounds hj
      have ho := G.boundary_order u i j hij
      omega

lemma consumes (G : Geometry A H) {reference s t k b b' : ℤ}
    {f fp fq : ℤ → Alphabet} {a btag : Tag M V g A.B}
    (hp : Prefix A H clock T ρ β a fp s t k)
    (hq : Suffix A H clock T ρ reference btag fq k b')
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b)
    (hag : AgreesOn f fq k (min b b')) :
    b=b' ∧ A.anchor f (b-A.endRule.tail) t = suffixAnchor A reference k b' fq := by
  have hover := G.origin_overlap hp.cut hq.guard.1
  exact A.endRule.guard_shared_end (H.true_origin a hp.cut) hq.guard
    (G.actual_visibility hp.cut he) hag hover.1 hover.2 he

omit [Monoid M] [AddCommGroup V] [Fintype M] [Fintype V] [Fintype C] in
lemma Geometry.cut_multiple (G : Geometry A H) {tag : Tag M V g A.B} {t k : ℤ}
    (hc : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*A.B) :
    (A.B : ℤ) ∣ k-t := by
  obtain ⟨a,ha,rfl⟩ := hc
  rw [show t+H.base (H.tagRole tag)+(a:ℤ)*A.B-t = H.base (H.tagRole tag)+(a:ℤ)*A.B by ring]
  exact dvd_add (G.multiple (H.tagRole tag)) (dvd_mul_left (A.B:ℤ) (a:ℤ))

omit [Fintype C] in
lemma residue_shift {q t k : ℤ} (hm : (A.B:ℤ) ∣ k-t) :
    A.residue (q-t) = A.residue (q-k) := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [A.residue_val,A.residue_val]
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  apply Int.emod_eq_zero_of_dvd
  convert hm using 1
  ring

lemma pair_sound (G : Geometry A H) {reference s t k b b' : ℤ}
    {f fp fq : ℤ → Alphabet} {a btag : Tag M V g A.B}
    (hp : Prefix A H clock T ρ β a fp s t k)
    (hq : Suffix A H clock T ρ reference btag fq k b')
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b)
    (hprefix : AgreesOn fp f s k) (hsuffix : AgreesOn fq f k (min b b')) :
    b=b' ∧ update A clock T ρ β f s b t a.input = btag.output := by
  have hconsume := consumes clock T ρ β G hp hq he (fun z hz hz' => (hsuffix z hz hz').symm)
  obtain rfl := hconsume.1
  have hsuffix' : AgreesOn fq f k b := by simpa using hsuffix
  have hclock : A.φ (A.anchor f (b-A.endRule.tail) t-k) ∈ clock.J btag := by
    rw [hconsume.2]
    exact hq.clock_mem
  have hedge := ClockAffine.edge_add clock A.φ hp.clock_mem hclock
  refine ⟨rfl,?_⟩
  apply ClockAffine.independent_pair clock ρ β Tag.input Tag.output _ hedge
  intro hab _
  subst btag
  have hu : A.residue (A.anchor f (b-A.endRule.tail) t-t) = a.residue := by
    rw [residue_shift (G.cut_multiple hp.cut),hconsume.2]
    exact hq.residue_eq
  cases a with
  | inl tag =>
    have hp' := hp.letter_test
    have hq' := hq.letter_test
    change PrefixMain A T ρ β tag fp s t k at hp'
    change SuffixMain A H T tag fq k b at hq'
    have hpre : ObservedMain.PrefixRead T ρ β tag f s k (search A f tag.u t) :=
      hp'.observed.transfer T ρ β hprefix (fun i hi => A.inner_congr (hp'.visible i hi) hprefix)
    obtain ⟨a,ha,hk⟩ := hp.cut
    have ht : k-H.main tag.j-a*A.B=t := by simpa [Cuts.base,Cuts.tagRole] using (show k-H.main tag.j-a*A.B=t by change k=t+H.main tag.j+a*A.B at hk;omega)
    have hpost : ObservedMain.SuffixRead T tag f k b (search A f tag.u t) := by
      apply hq'.observed.transfer T hsuffix'
      intro i hi
      have hst := hq'.stable a ha i hi
      have hver := hq'.visible a ha i hi
      rw [ht] at hst hver
      exact hst.symm.trans (A.inner_congr hver hsuffix')
    have hv : ∀ i, A.InnerVisible s b t i tag.u := by
      intro i
      by_cases hi : i.val ≤ tag.j.val
      · have hh := hp'.visible i hi
        exact ⟨hh.1,hh.2.trans hq.ordered⟩
      · have hh := hq'.visible a ha i (by omega)
        rw [ht] at hh
        exact ⟨hp.positive.le.trans hh.1,hh.2⟩
    have hm := G.present hv (ObservedMain.pair_present T ρ β hpre.toPrefix hpost.toSuffix)
    have hh := ObservedMain.pair_sound T ρ β hpre.toPrefix hpost.toSuffix hm
    simp only [snapshot,hu,Tag.residue,Tag.input,Tag.output]
    cases hboundaries : (actual T f s b (search A f tag.u t)).boundaries <;>
      simpa only [hboundaries] using hh
  | inr tag =>
    have hp' := hp.letter_test
    change PrefixPeriodic A T tag fp s t k at hp'
    have hn : A.inner f tag.j tag.u t = none :=
      (A.inner_congr hp'.visible hprefix).symm.trans hp'.absent
    have hprod := product_congr T hp.positive.le hprefix
    have hsprod := product_congr T hq.ordered hsuffix'
    have happ := product_append T f hp.positive.le hq.ordered
    have hnone := factors_absent T f (s := s) (b := b) (search := search A f tag.u t)
      (i := tag.j) hn
    have hout := hq.letter_test
    change tag.output = ρ (tag.prefixProduct * product T fq k b) tag.input at hout
    rw [←hp'.product_eq,hprod,hsprod,←happ] at hout
    simpa only [snapshot,hu,Tag.residue,Tag.input,Tag.output,actual,hnone,add_zero] using hout.symm

end OuterStream

namespace BoundarySnapshot

open WordIntervals LocalMarkers
variable {Alphabet : Type uAlphabet2} {M : Type uM2} [Monoid M] {g : ℕ}

lemma factors_congr (T : FreeMonoid Alphabet →* M) {f f' : ℤ → Alphabet}
    {a b : ℤ} {search : Fin (g+1) → Option ℤ} (he : AgreesOn f f' a b) :
    factors T f a b search = factors T f' a b search := by
  classical
  by_cases hp : Present search a b
  · rw [factors_positions T f hp,factors_positions T f' hp]
    obtain ⟨p,hp,hm,ha,hb⟩ := hp
    have hpos : positions search = p := by funext i;simp [positions,hp]
    simp only [hpos]
    congr 2
    · apply product_congr T ha
      intro z hz hz'
      exact he z hz (hz'.trans_le ((hm (Fin.zero_le _)).trans hb))
    · funext i
      apply product_congr T (hm (Fin.castSucc_le_succ i))
      intro z hz hz'
      exact he z ((ha.trans (hm (Fin.zero_le _))).trans hz)
        (hz'.trans_le ((hm (Fin.le_last _)).trans hb))
    · apply product_congr T hb
      intro z hz hz'
      exact he z ((ha.trans (hm (Fin.zero_le _))).trans hz) hz'
  · simp only [factors,dite_eq_right hp]

@[ext] lemma later_ext {D E : ClockAffine.Later M g}
    (hp : D.tailProduct=E.tailProduct) (hb : D.boundaries=E.boundaries) : D=E := by
  cases D;cases E;cases hp;cases hb;rfl

lemma later_congr (T : FreeMonoid Alphabet →* M) {f f' : ℤ → Alphabet}
    {a b : ℤ} (hab : a ≤ b) {search search' : Fin (g+1) → Option ℤ}
    (hs : search=search') (he : AgreesOn f f' a b) :
    later T f a b search = later T f' a b search' := by
  subst search'
  apply later_ext
  · exact product_congr T hab he
  · exact factors_congr T he

end BoundarySnapshot

namespace ExceptionalOrigins.Parameters

variable {Alphabet : Type uAlphabet3} {J : Type uJ} {C : Type uC2} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma Visible.innerVisible {s b t Q : ℤ} (hv : A.Visible s b t Q)
    (hw : 0 ≤ A.w₀) (j : J) : A.InnerVisible s b t j (A.residue (Q-t)) := by
  have hi := hv.inner j
  have hm := le_max_right A.ext A.w₀
  exact ⟨by omega,by omega⟩

end ExceptionalOrigins.Parameters

namespace InnerStream

open WordIntervals LocalMarkers SplitMetadata BoundarySnapshot

variable {Alphabet : Type uAlphabet4} {M : Type uM3} {V : Type uV2} {K : Type uK2} {P : Type uP2} {C : Type uC3} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g g' μ : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)
    (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)

noncomputable def hypothetical (f : ℤ → Alphabet) (s b t : ℤ) :
    M → (V × K →ₗ[K] V × K) :=
  let q := A.anchor f (b-A.endRule.tail) t
  ClockAffine.hypothetical clock ρ β Tag.input Tag.output (A.φ (q-t))
    (later T f (s+early (Fin.last g')) b (OuterStream.search A f (A.residue (q-t)) t))

noncomputable def update (f : ℤ → Alphabet) (s b t : ℤ) (x : V × K) : V × K :=
  let ψ := hypothetical A clock T ρ β early f s b t
  let d := fun i : Fin g' => product T f (s+early i.castSucc) (s+early i.succ)
  ObservedInner.table ψ d x + γ ψ d

lemma hypothetical_congr {f f' : ℤ → Alphabet} {s b t k : ℤ}
    (hk : k ≤ s+early (Fin.last g')) (hb : s+early (Fin.last g') ≤ b)
    (he : AgreesOn f f' k b)
    (hq : A.anchor f (b-A.endRule.tail) t = A.anchor f' (b-A.endRule.tail) t)
    (hv : ∀ j, A.InnerVisible k b t j (A.residue (A.anchor f (b-A.endRule.tail) t-t))) :
    hypothetical A clock T ρ β early f s b t = hypothetical A clock T ρ β early f' s b t := by
  have hs : OuterStream.search A f (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t =
      OuterStream.search A f' (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t := by
    funext j
    exact A.inner_congr (hv j) he
  have hl := later_congr T hb hs (fun z hz hz' => he z (hk.trans hz) hz')
  dsimp only [hypothetical]
  rw [←hq,hl]

variable (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

structure Prefix (slot : Roster M (V × K) K g' μ) (f : ℤ → Alphabet) (s k : ℤ) : Prop where
  cut : k=s+p slot
  observed : ObservedInner.Prefix T γ slot.1 f (fun i => s+early i)

structure Suffix (reference slot : Roster M (V × K) K g' μ) (f : ℤ → Alphabet)
    (k b : ℤ) : Prop where
  decoder : SuffixDecoder.Test A (SuffixDecoder.origin p lag k) reference k b f slot
  observed : ObservedInner.Suffix T slot.1 f (fun i => k-p slot+early i)
    (hypothetical A clock T ρ β early f (k-p slot) b (k-p slot+lag))

omit [Fintype M] [Fintype V] in
lemma prefix_actual (hearly : StrictMono early) (hearly₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    {s k : ℤ} {f fp : ℤ → Alphabet} {actual : Roster M (V × K) K g' μ}
    (hp : Prefix T early γ p actual fp s k) (hprefix : AgreesOn fp f s k) :
    ObservedInner.Prefix T γ actual.1 f (fun i => s+early i) := by
  have hbound : Monotone (fun i => s+early i) := fun _ _ h => add_le_add_right (hearly.monotone h) s
  apply ObservedInner.prefix_congr T γ hbound
    (show s+early actual.1.j.castSucc ≤ k by rw [hp.cut];exact (add_lt_add_right (hblock actual).1 s).le)
    _ hp.observed
  simpa only [hearly₀,add_zero] using hprefix

lemma suffix_actual (hearly : StrictMono early)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (hw : 0 ≤ A.w₀) {s k b : ℤ} {f fq : ℤ → Alphabet}
    {reference actual : Roster M (V × K) K g' μ}
    (hcut : k=s+p actual)
    (hq : Suffix A clock T ρ β early p lag reference actual fq k b)
    (hvis : ∀ i, A.Visible k b (SuffixDecoder.origin p lag k i)
      (A.anchor f (b-A.endRule.tail) (SuffixDecoder.origin p lag k i)))
    (hb : s+early (Fin.last g') ≤ b) (hsuffix : AgreesOn f fq k b) :
    ObservedInner.Suffix T actual.1 f (fun i => s+early i)
      (hypothetical A clock T ρ β early f s b (s+lag)) := by
  have ht : SuffixDecoder.origin p lag k actual=s+lag := by dsimp [SuffixDecoder.origin];rw [hcut];ring
  have hk : k ≤ s+early (Fin.last g') := by
    rw [hcut]
    exact add_le_add_right ((hblock actual).2.le.trans (hearly.monotone (Fin.le_last _))) s
  have hqeq : A.anchor f (b-A.endRule.tail) (s+lag) = A.anchor fq (b-A.endRule.tail) (s+lag) := by
    have hh := (SuffixDecoder.searches_agree A hq.decoder hvis (by simpa using hsuffix) actual).2
    rw [ht] at hh
    simp only [ExceptionalOrigins.Parameters.anchor,hh]
  have hψ := hypothetical_congr A clock T ρ β early hk hb hsuffix hqeq (by
    intro j
    have hh := ExceptionalOrigins.Parameters.Visible.innerVisible A (hvis actual) hw j
    simpa only [ht] using hh)
  have hx : k-p actual=s := by rw [hcut];ring
  have hh := hq.observed
  rw [hx,←hψ] at hh
  have hbound : Monotone (fun i => s+early i) := fun _ _ h => add_le_add_right (hearly.monotone h) s
  apply ObservedInner.suffix_congr T hbound
    (show k ≤ s+early actual.1.j.succ by rw [hcut];exact (add_lt_add_right (hblock actual).2 s).le)
    _ hh
  intro z hz hz'
  exact (hsuffix z hz (hz'.trans_le hb)).symm

lemma same_slot_sound (hearly : StrictMono early) (hearly₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (hw : 0 ≤ A.w₀) {s k b : ℤ} {f fp fq : ℤ → Alphabet}
    {reference actual : Roster M (V × K) K g' μ}
    (hp : Prefix T early γ p actual fp s k)
    (hq : Suffix A clock T ρ β early p lag reference actual fq k b)
    (hvis : ∀ i, A.Visible k b (SuffixDecoder.origin p lag k i)
      (A.anchor f (b-A.endRule.tail) (SuffixDecoder.origin p lag k i)))
    (hb : s+early (Fin.last g') ≤ b)
    (hprefix : AgreesOn fp f s k) (hsuffix : AgreesOn f fq k b) :
    update A clock T ρ β early γ f s b (s+lag) actual.1.input = actual.1.output := by
  have hpre := prefix_actual T early γ p hearly hearly₀ hblock hp hprefix
  have hpost := suffix_actual A clock T ρ β early p lag hearly hblock hw hp.cut hq hvis hb hsuffix
  dsimp only [update]
  exact ObservedInner.pair_sound (K := K) (U := V × K) (g := g') T γ
    (kind := actual.1) (boundary := fun i => s+early i)
    (ψ := hypothetical A clock T ρ β early f s b (s+lag)) hpre hpost

lemma pair_sound (hearly : StrictMono early) (hearly₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (hw : 0 ≤ A.w₀) {s k b b' : ℤ} {f fp fq : ℤ → Alphabet}
    {reference actual decoded : Roster M (V × K) K g' μ}
    (hp : Prefix T early γ p actual fp s k)
    (hq : Suffix A clock T ρ β early p lag reference decoded fq k b')
    (hvis : ∀ i, A.Visible k b (SuffixDecoder.origin p lag k i)
      (A.anchor f (b-A.endRule.tail) (SuffixDecoder.origin p lag k i)))
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K-|p actual-p reference|)
    (hover' : |p actual-p reference| < A.endRule.K)
    (hb : s+early (Fin.last g') ≤ b)
    (hend : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (s+lag+A.endRule.offset) (A.endRule.small f (s+lag+A.endRule.offset)) b)
    (hfailed : A.Failed f (s+lag) (A.anchor f (b-A.endRule.tail) (s+lag)))
    (hprefix : AgreesOn fp f s k) (hsuffix : AgreesOn f fq k (min b b')) :
    decoded=actual ∧ b'=b ∧ update A clock T ρ β early γ f s b (s+lag) actual.1.input = decoded.1.output := by
  have ht : SuffixDecoder.origin p lag k actual=s+lag := by dsimp [SuffixDecoder.origin];rw [hp.cut];ring
  have hdiff : SuffixDecoder.origin p lag k actual-SuffixDecoder.origin p lag k reference =
      p reference-p actual := by dsimp [SuffixDecoder.origin];ring
  have hdec := SuffixDecoder.sound A hw hq.decoder hvis hsuffix
    (by simpa only [hdiff,abs_sub_comm] using hover)
    (by simpa only [hdiff,abs_sub_comm] using hover') (ht ▸ hend) (ht ▸ hfailed)
  have hnew : Suffix A clock T ρ β early p lag reference actual fq k b := by
    simpa only [hdec.1,hdec.2] using hq
  have hsuffix' : AgreesOn f fq k b := by simpa only [hdec.2,min_self] using hsuffix
  refine ⟨hdec.1,hdec.2,?_⟩
  rw [hdec.1]
  exact same_slot_sound A clock T ρ β early γ p lag hearly hearly₀ hblock hw hp hnew hvis hb hprefix hsuffix'

lemma hypothetical_actual {f : ℤ → Alphabet} {s b t : ℤ}
    (hsa : s ≤ s+early (Fin.last g')) (hab : s+early (Fin.last g') ≤ b)
    (hstart : ∀ i q, A.inner f i (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t=some q →
      s+early (Fin.last g') ≤ q) :
    hypothetical A clock T ρ β early f s b t (product T f s (s+early (Fin.last g'))) =
      Homogenization.lift (ρ (product T f s b))
        (ClockAffine.shift clock ρ β Tag.input Tag.output (A.φ (A.anchor f (b-A.endRule.tail) t-t))
          (OuterStream.snapshot A T f s b t)) := by
  have hh := actual_eq_substitute T f hsa hab hstart
  change ClockAffine.hypothetical clock ρ β Tag.input Tag.output _ _ _ = _
  rw [ClockAffine.hypothetical_actual]
  unfold OuterStream.search
  rw [←hh]
  rfl

end InnerStream

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace SourceSchedule

structure Late (Alphabet : Type uAlphabet) (B : ℕ) (h w E earlyLast : ℤ) where
  endRule : CanonicalEpisodes.Parameters Alphabet
  lag : ℤ
  modulus : endRule.B=B
  spacing : 4*(h+w+1) < endRule.S
  separation : 10*(B:ℤ)*endRule.S+10*(h+w+1) < endRule.d
  lag_pos : 0 < lag
  lag_margin : earlyLast < lag-E
  offset_margin : E < endRule.offset-(2*w+endRule.width+endRule.rule.r+endRule.K+1)
  tail_margin : (endRule.d:ℤ)+(endRule.B-1)*endRule.S+
    (2*w+endRule.width+endRule.rule.r+endRule.K+1) < endRule.tail

lemma exists_late {Alphabet : Type uAlphabet2} [Fintype Alphabet] (B : ℕ) (hB : 0 < B)
    (h w E earlyLast : ℤ) (hh : 0 ≤ h) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    Nonempty (Late Alphabet B h w E earlyLast) := by
  let S : ℤ := 4*(h+w+1)+1
  have hS : 0 ≤ S := by dsimp [S];omega
  let D : ℤ := 10*(B:ℤ)*S+10*(h+w+1)
  have hD : 0 ≤ D := by dsimp [D];positivity
  let d : ℕ := D.toNat+2
  have hd : (d:ℤ)=D+2 := by simp only [d,Nat.cast_add,Int.toNat_of_nonneg hD,Nat.cast_ofNat]
  have hd₂ : 2 ≤ d := by dsimp [d];omega
  let K : ℕ := 3*d^2+1
  obtain ⟨rule⟩ := LocalMarkers.nonempty_rule (Alphabet := Alphabet) (d := d) (K := K) hd₂
    (show 3*d^2<K by dsimp [K];omega)
  let width : ℤ := 3*d+((B:ℤ)-1)*S
  have hwidth : 0 ≤ width := by
    have hBb : (0:ℤ) ≤ (B:ℤ)-1 := by
      have : (1:ℤ) ≤ B := by exact_mod_cast hB
      omega
    dsimp [width];positivity
  let endE : ℤ := 2*w+width+rule.r+K+1
  have hr := rule.radius_ge
  have hendE : 0 ≤ endE := by dsimp [endE];omega
  let tail : ℤ := d+((B:ℤ)-1)*S+endE+2
  have htail : 0 < tail := by
    have hBb : (0:ℤ) ≤ (B:ℤ)-1 := by
      have : (1:ℤ) ≤ B := by exact_mod_cast hB
      omega
    dsimp [tail];positivity
  let er : CanonicalEpisodes.Parameters Alphabet :=
    ⟨B,S,d,K,E+endE+1,tail,rule,by exact_mod_cast hB,hS,hd₂,
      by dsimp [K];omega,htail⟩
  refine ⟨⟨er,|earlyLast|+E+1,rfl,?_,?_,?_,?_,?_,?_⟩⟩
  · dsimp [er,S];omega
  · change D < (d:ℤ);omega
  · positivity
  · have := le_abs_self earlyLast;omega
  · change E < E+endE+1-endE;omega
  · change (d:ℤ)+((B:ℤ)-1)*S+endE < tail
    dsimp [tail];omega

namespace Late

variable {Alphabet : Type uAlphabet3} {B : ℕ} {h w E earlyLast : ℤ}
    (L : Late Alphabet B h w E earlyLast)

lemma radius_nonneg : 0 ≤ L.endRule.rule.r :=
  (show (0:ℤ) ≤ L.endRule.K by positivity).trans L.endRule.rule.radius_ge

lemma overlap (hh : 0 ≤ h) (hw : 0 ≤ w) :
    (L.endRule.d:ℤ)^2+w ≤ L.endRule.K := by
  have hd := L.separation
  have hS := L.endRule.S_nonneg
  have hprod : 0 ≤ 10*(B:ℤ)*L.endRule.S := by positivity
  have hseed : 3*(L.endRule.d:ℤ)^2 < L.endRule.K := by exact_mod_cast L.endRule.seed_long
  have hd₂ : (2:ℤ) ≤ L.endRule.d := by exact_mod_cast L.endRule.d_ge
  nlinarith

lemma complete_lower {f : ℤ → Alphabet} {s b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b) :
    s+L.lag+L.endRule.offset+(2*w+L.endRule.width+L.endRule.rule.r+L.endRule.K+1) < b := by
  have hb := L.endRule.end_lower he
  have ht := L.tail_margin
  omega

lemma visible {J : Type uJ} {C : Type uC} (A : ExceptionalOrigins.Parameters Alphabet J C)
    (heq : A.endRule=L.endRule) (hw : A.w=w) (hwpos : 0 ≤ w) (hE : 0 ≤ E)
    (hinleft : ∀ j, -E ≤ A.offset j-w-A.w₀-A.innerRule.r)
    (hinright : ∀ j u, A.offset j+w+A.H u+max A.ext A.w₀+A.innerRule.r ≤ E)
    {f : ℤ → Alphabet} {s b δ Q : ℤ} (hδ : |δ| ≤ w)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b) :
    A.Visible (s+earlyLast) b (s+L.lag+δ) Q := by
  have hlo := L.lag_margin
  have hoff := L.offset_margin
  have hb := L.complete_lower he
  have hδ' := abs_le.mp hδ
  have hr := L.radius_nonneg
  have hwidth := L.endRule.width_nonneg
  have hK : (0:ℤ) ≤ L.endRule.K := by positivity
  have hlower : s+earlyLast < s+L.lag-E := by omega
  refine ⟨?_,?_,?_⟩
  · rw [heq]
    refine ⟨?_,?_,?_,?_⟩ <;> omega
  · intro v _ hav
    rw [hw] at hav
    have hv := abs_le.mp hav
    rw [heq]
    constructor <;> omega
  · intro j
    have hj := hinleft j
    have hj' := hinright j (A.residue (Q-(s+L.lag+δ)))
    have hEend : 0 ≤ 2*w+L.endRule.width+L.endRule.rule.r+L.endRule.K+1 := by omega
    constructor <;> omega

end Late

end SourceSchedule

namespace SourceSchedule

noncomputable def finiteBound (F : Finset ℤ) : ℕ := F.sup Int.natAbs

lemma abs_le_finiteBound {F : Finset ℤ} {x : ℤ} (hx : x ∈ F) :
    |x| ≤ (finiteBound F:ℤ) := by
  have hh : x.natAbs ≤ finiteBound F := Finset.le_sup (f := Int.natAbs) hx
  simpa only [Int.natCast_natAbs] using (show (x.natAbs:ℤ) ≤ finiteBound F by exact_mod_cast hh)

namespace Early

open scoped BigOperators

variable {Alphabet : Type uAlphabet4} {T : Type uT} {P : Type uP} {C : Type uC2} [Fintype T] [Fintype P] [Fintype C]
    {g' B size : ℕ} {clock : RobustClock.Specification T P C}
    {label : P → Fin g'} {reserved : P → ℤ}
    (S : Early (Alphabet := Alphabet) clock B size label reserved)

noncomputable def period : ℕ := ∏ c, S.denominator c

lemma period_pos : 0 < S.period := Finset.prod_pos (fun c _ => (S.prime c).pos)

noncomputable def cuts (g : ℕ) : OuterStream.Cuts g B where
  main j := S.inner.mainBase j.val
  periodic j u := S.inner.periodicOffset j.val u 0
  R := S.R
  N := S.period * innerD S.p (B*S.R) * size.factorial
  R_pos := S.R_pos
  N_pos := Nat.mul_pos (Nat.mul_pos S.period_pos (by have := innerD_ge S.p (B*S.R);omega))
    (Nat.factorial_pos _)

noncomputable def diameter : ℤ := 2*(absoluteBound S.p:ℤ)+1

lemma diameter_pos : 0 < S.diameter := by dsimp [diameter];positivity

noncomputable def sweepWidth (g : ℕ) : ℤ :=
  2*S.diameter+2*(finiteBound (S.cuts g).offsets:ℤ)+1

lemma sweepWidth_large (g : ℕ) : 2*S.diameter < S.sweepWidth g := by
  dsimp [sweepWidth];omega

lemma sweepWidth_pos (g : ℕ) : 0 < S.sweepWidth g := by
  have := S.diameter_pos;have := S.sweepWidth_large g;omega

lemma offsets_difference (g : ℕ) {a b : ℤ} (ha : a ∈ (S.cuts g).offsets)
    (hb : b ∈ (S.cuts g).offsets) : |a-b| < S.sweepWidth g := by
  have ha' := abs_le_finiteBound ha
  have hb' := abs_le_finiteBound hb
  have hh := abs_sub a b
  have hd := S.diameter_pos
  dsimp [sweepWidth]
  omega

lemma stencil_difference (g : ℕ) (i j : P) : |S.p i-S.p j| < S.sweepWidth g := by
  have hh := difference_bound S.p i j
  have hw := S.sweepWidth_large g
  have hd := S.diameter_pos
  change |S.p i-S.p j| ≤ S.diameter at hh
  omega

noncomputable def envelope (g : ℕ) : ℤ :=
  S.sweepWidth g+2*|((B*S.R:ℕ):ℤ)|+|S.rule.r|+
    (absoluteBound (fun j : Fin (g+1) => S.inner.boundary j.val):ℤ)+
    (absoluteBound S.inner.H:ℤ)+|S.inner.extension|+
    (3*(innerD S.p (B*S.R))^2+1:ℕ)+
    (size*innerD S.p (B*S.R):ℕ)+(finiteBound (S.cuts g).offsets:ℤ)+1

lemma envelope_pos (g : ℕ) : 0 < S.envelope g := by
  have := S.sweepWidth_pos g
  dsimp [envelope];positivity

lemma inner_left (g : ℕ) (j : Fin (g+1)) :
    -S.envelope g ≤ S.inner.boundary j.val-S.sweepWidth g-(B*S.R:ℕ)-S.rule.r := by
  have hj := abs_le_absoluteBound (fun j : Fin (g+1) => S.inner.boundary j.val) j
  have hab := neg_abs_le (S.inner.boundary j.val)
  have hr := le_abs_self S.rule.r
  have hw := le_abs_self ((B*S.R:ℕ):ℤ)
  have hH : (0:ℤ) ≤ absoluteBound S.inner.H := by positivity
  have := abs_nonneg S.inner.extension
  have := abs_nonneg ((B*S.R:ℕ):ℤ)
  have := sq_nonneg (innerD S.p (B*S.R):ℤ)
  have : (0:ℤ) ≤ (size:ℤ)*(innerD S.p (B*S.R):ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  simp only [envelope,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]
  simp only [Nat.cast_mul] at *
  omega

lemma inner_right (g : ℕ) (j : Fin (g+1)) (u : Fin B) :
    S.inner.boundary j.val+S.sweepWidth g+S.inner.H u+
      max S.inner.extension (B*S.R:ℕ)+S.rule.r ≤ S.envelope g := by
  have hj := (le_abs_self (S.inner.boundary j.val)).trans
    (abs_le_absoluteBound (fun j : Fin (g+1) => S.inner.boundary j.val) j)
  have hH := (le_abs_self (S.inner.H u)).trans (abs_le_absoluteBound S.inner.H u)
  have hr := le_abs_self S.rule.r
  have he := le_abs_self S.inner.extension
  have hw := le_abs_self ((B*S.R:ℕ):ℤ)
  have hwpos := abs_nonneg ((B*S.R:ℕ):ℤ)
  have hepos := abs_nonneg S.inner.extension
  have hm : max S.inner.extension (B*S.R:ℕ) ≤ |S.inner.extension|+|((B*S.R:ℕ):ℤ)| := by
    apply max_le <;> omega
  have := sq_nonneg (innerD S.p (B*S.R):ℤ)
  have : (0:ℤ) ≤ (size:ℤ)*(innerD S.p (B*S.R):ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  simp only [envelope,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]
  simp only [Nat.cast_mul] at *
  omega

lemma exists_full_late [Fintype Alphabet] (hB : 0 < B) (g : ℕ) :
    Nonempty (Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g'))) :=
  exists_late B hB _ _ _ _ S.diameter_pos.le (S.sweepWidth_pos g).le (S.envelope_pos g).le

variable (g : ℕ) (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))

noncomputable def parameters (hB : 0 < B) : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C where
  endRule := L.endRule
  d := innerD S.p (B*S.R)
  K := 3*(innerD S.p (B*S.R))^2+1
  B := B
  B_pos := hB
  end_modulus := L.modulus
  innerRule := S.rule
  offset j := S.inner.boundary j.val
  H := S.inner.H
  w := S.sweepWidth g
  w₀ := (B*S.R:ℕ)
  ext := S.inner.extension
  φ := PeriodicClock.speedMap (fun c => (S.numerator c:ℝ)/S.denominator c)
  W := clock.W

lemma geometry (hB : 0 < B) : OuterStream.Geometry (S.parameters g L hB) (S.cuts g) := by
  have hw := (S.sweepWidth_pos g).le
  have hr := L.radius_nonneg
  have hwidth := L.endRule.width_nonneg
  have hK : (0:ℤ) ≤ L.endRule.K := by positivity
  have he := (S.envelope_pos g).le
  have hbound : ∀ a ∈ (S.cuts g).offsets, |a| ≤ S.envelope g := by
    intro a ha
    have hh := abs_le_finiteBound ha
    have hw' := S.sweepWidth_pos g
    dsimp [envelope]
    have hrest : 0 ≤ 2*|((B*S.R:ℕ):ℤ)|+|S.rule.r|+
        (absoluteBound (fun j : Fin (g+1) => S.inner.boundary j.val):ℤ)+
        (absoluteBound S.inner.H:ℤ)+|S.inner.extension|+
        (3*(innerD S.p (B*S.R))^2+1:ℕ)+(size*innerD S.p (B*S.R):ℕ) := by positivity
    push_cast at *
    omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro role
    cases role with
    | inl j => simpa only [parameters,cuts,OuterStream.Cuts.base,IntegerSchedules.Inner.mainOffset,Nat.cast_zero,zero_mul,add_zero]
        using S.inner.main_multiple j.val 0
    | inr ju => exact S.inner.periodic_multiple ju.1.val ju.2 0
  · intro u i j hij
    have hh := (S.inner.halfGap_large hB (by have := S.rule.radius_ge;omega)).1
    have hH := S.inner.H_bounded u
    have hgap := S.inner.gap_pos
    have hrule : 0 ≤ S.rule.r := (show (0:ℤ) ≤ 3*(innerD S.p (B*S.R))^2+1 by positivity).trans S.rule.radius_ge
    have hij' : (i.val:ℤ)+1 ≤ j.val := by exact_mod_cast (show i.val+1 ≤ j.val from hij)
    have hm := mul_le_mul_of_nonneg_right hij' (show 0 ≤ 2*S.inner.halfGap by positivity)
    change S.inner.boundary i.val+S.inner.H u ≤ S.inner.boundary j.val
    dsimp [IntegerSchedules.Inner.boundary]
    nlinarith
  · intro a ha
    have hh := (le_abs_self a).trans (hbound a ha)
    have hoff := L.offset_margin
    change a+L.endRule.width+L.endRule.rule.r ≤ L.endRule.offset
    omega
  · intro a ha b hb
    have hh := (le_abs_self (a-b)).trans (S.offsets_difference g ha hb).le
    have ht := L.tail_margin
    change a-b+L.endRule.width+L.endRule.rule.r+
      ((L.endRule.d:ℤ)+(L.endRule.B-1)*L.endRule.S) ≤ L.endRule.tail
    omega
  · intro a ha b hb
    have hh := (le_abs_self (a-b)).trans (S.offsets_difference g ha hb).le
    have ht := L.tail_margin
    change a-b+L.endRule.K+((L.endRule.d:ℤ)+(L.endRule.B-1)*L.endRule.S) ≤ L.endRule.tail
    omega
  · intro a ha b hb
    exact (add_le_add_right (S.offsets_difference g ha hb).le _).trans
      (L.overlap S.diameter_pos.le hw)

lemma actual_visible (hB : 0 < B) {f : ℤ → Alphabet} {s b δ Q : ℤ}
    (hδ : |δ| ≤ S.sweepWidth g)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b) :
    (S.parameters g L hB).Visible (s+S.β (Fin.last g')) b (s+L.lag+δ) Q :=
  L.visible (S.parameters g L hB) rfl rfl (S.sweepWidth_pos g).le (S.envelope_pos g).le
    (S.inner_left g) (S.inner_right g) hδ he

end Early

end SourceSchedule

namespace ExceptionalOrigins.Parameters

variable {Alphabet : Type uAlphabet5} {J : Type uJ2} {C : Type uC3} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma not_failed_clock {f : ℤ → Alphabet} {t Q : ℤ} (hn : ¬A.Failed f t Q) :
    A.φ (Q-t) ∉ A.W := fun h => hn (Or.inr (Or.inl h))

lemma not_failed_inner {f : ℤ → Alphabet} {t Q δ : ℤ} (hn : ¬A.Failed f t Q)
    (hδ : |δ| ≤ A.w₀) (j : J) :
    A.inner f j (A.residue (Q-t)) (t+δ) = A.inner f j (A.residue (Q-t)) t := by
  by_contra he
  apply hn
  right;right
  refine ⟨j,Or.inl ⟨δ,hδ,?_⟩⟩
  simpa only [inner,add_right_comm t δ,add_right_comm (t+A.offset j) δ] using Ne.symm he

lemma not_failed_absent {f : ℤ → Alphabet} {t Q : ℤ} (hn : ¬A.Failed f t Q)
    (j : J) (hj : A.inner f j (A.residue (Q-t)) t = none) :
    ∀ x, t+A.offset j ≤ x → x ≤ t+A.offset j+A.H (A.residue (Q-t))+A.ext →
      x ∉ A.innerRule.markers f := by
  intro x hx hx' hm
  exact hn (Or.inr (Or.inr ⟨j,Or.inr ⟨hj,x,hm,hx,hx'⟩⟩))

lemma not_failed_end {f : ℤ → Alphabet} {t Q δ : ℤ} (hn : ¬A.Failed f t Q)
    (hδ : |δ| ≤ A.w) (hm : (A.B:ℤ) ∣ δ) :
    A.endRule.small f (t+δ+A.endRule.offset) = A.endRule.small f (t+A.endRule.offset) ∧
    A.endRule.large f (t+δ+A.endRule.offset) = A.endRule.large f (t+A.endRule.offset) := by
  constructor
  · by_contra he
    apply hn
    left;left
    refine ⟨δ,hm,hδ,?_⟩
    simpa only [CanonicalEpisodes.Parameters.small,←A.end_modulus,add_right_comm t δ]
      using Ne.symm he
  · by_contra he
    apply hn
    left;right
    refine ⟨δ,hm,hδ,?_⟩
    simpa only [CanonicalEpisodes.Parameters.large,←A.end_modulus,add_right_comm t δ]
      using Ne.symm he

end ExceptionalOrigins.Parameters

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace OuterStream

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical

variable {Alphabet : Type uAlphabet} {M : Type uM} {V : Type uV} {K : Type uK} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

omit [Monoid M] [AddCommGroup V] [Fintype M] [Fintype V] [Fintype C] in
lemma Cuts.multiple (G : Geometry A H) {h : ℤ} (hh : h ∈ H.offsets) : (A.B:ℤ) ∣ h := by
  obtain ⟨role,_,hh⟩ := Finset.mem_biUnion.mp hh
  obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp hh
  exact dvd_add (G.multiple role) (dvd_mul_left _ _)

omit [Monoid M] [AddCommGroup V] [Fintype M] [Fintype V] [Fintype C] in
lemma available_guard (G : Geometry A H)
    (hwidth : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets, |h-h'| ≤ A.w)
    {t k b Q reference : ℤ} {f : ℤ → Alphabet} {tag : Tag M V g A.B}
    (hc : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*A.B)
    (hr : reference ∈ H.offsets) (hn : ¬A.Failed f t Q)
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b) :
    A.endRule.Guard (H.origins k) (k-reference) k b f ∧
      suffixAnchor A reference k b f = A.anchor f (b-A.endRule.tail) t := by
  have hm : k-reference ∈ H.origins k := Finset.mem_image.mpr ⟨reference,hr,rfl⟩
  have hstable : ∀ o ∈ H.origins k,
      A.endRule.small f (o+A.endRule.offset) = A.endRule.small f (t+A.endRule.offset) ∧
      A.endRule.large f (o+A.endRule.offset) = A.endRule.large f (t+A.endRule.offset) := by
    intro o ho
    obtain ⟨a,ha,hk⟩ := hc
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp ho
    have hmem := H.offset_mem (H.tagRole tag) a ha
    have heq : k-h = t+(H.base (H.tagRole tag)+a*A.B-h) := by omega
    rw [heq]
    exact A.not_failed_end hn (hwidth _ hmem h hh)
      (dvd_sub (H.multiple A G hmem) (H.multiple A G hh))
  have hover := G.origin_overlap hc hm
  refine ⟨A.endRule.guard_available hm (G.actual_visibility hc he) hstable hover.1 hover.2 he,?_⟩
  simp only [suffixAnchor,ExceptionalOrigins.Parameters.anchor,(hstable _ hm).2]

end OuterStream

namespace OuterStream

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical

variable {Alphabet : Type uAlphabet2} {M : Type uM2} {V : Type uV2} {K : Type uK2} {P : Type uP2} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

lemma net_displacement {B R a a' : ℕ} (ha : a<R) (ha' : a'<R) :
    |(a:ℤ)*B-a'*B| ≤ (B*R:ℕ) := by
  have haB := Nat.mul_le_mul_right B ha.le
  have haB' := Nat.mul_le_mul_right B ha'.le
  have h₁ : (a:ℤ)*B ≤ (R:ℤ)*B := by exact_mod_cast haB
  have h₂ : (a':ℤ)*B ≤ (R:ℤ)*B := by exact_mod_cast haB'
  have hp : 0 ≤ (a:ℤ)*B := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hp' : 0 ≤ (a':ℤ)*B := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  rw [abs_le,Nat.cast_mul,mul_comm (B:ℤ)]
  omega

lemma available_main (G : Geometry A H) (hW : A.W=clock.W)
    (hnet : ∀ v : C → RobustClock.Circle, ∃ a : ℕ, a<H.R ∧ dist (A.φ (a*A.B)) v < clock.ρ)
    (hw₀ : (A.B*H.R:ℕ) ≤ A.w₀)
    (hwidth : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets, |h-h'| ≤ A.w)
    (hβ : ∀ a c, ShiftTableProperty g (ClockAffine.productTable ρ a c) (β a c))
    {s t b reference : ℤ} {f : ℤ → Alphabet}
    (hr : reference ∈ H.offsets)
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b)
    (hn : ¬A.Failed f t (A.anchor f (b-A.endRule.tail) t))
    (hpos : ∀ (j : Fin g) (a : ℕ), a<H.R → s<t+H.main j+a*A.B ∧ t+H.main j+a*A.B≤b)
    (hpre : ∀ (j : Fin g) (a : ℕ), a<H.R → ∀ (i : Fin (g+1)), i.val≤j.val →
      A.InnerVisible s (t+H.main j+a*A.B) t i (A.residue (A.anchor f (b-A.endRule.tail) t-t)))
    (hpost : ∀ (j : Fin g) (a : ℕ), a<H.R → ∀ a', a'<H.R → ∀ (i : Fin (g+1)), j.val < i.val →
      A.InnerVisible (t+H.main j+a*A.B) b (t+(a*A.B-a'*A.B)) i
        (A.residue (A.anchor f (b-A.endRule.tail) t-t)))
    (hv : ∀ i, A.InnerVisible s b t i (A.residue (A.anchor f (b-A.endRule.tail) t-t)))
    (hp : ∀ i, A.inner f i (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t ≠ none)
    (x : V) :
    ∃ (tag : MainTag M V g A.B) (k : ℤ), tag.input=x ∧
      Prefix A H clock T ρ β (.inl tag) f s t k ∧
      Suffix A H clock T ρ reference (.inl tag) f k b ∧
      tag.output=update A clock T ρ β f s b t x := by
  let q := A.anchor f (b-A.endRule.tail) t
  let u := A.residue (q-t)
  have hz : A.φ (q-t) ∉ clock.W := by rw [←hW]; exact A.not_failed_clock hn
  have hpres := G.present hv hp
  obtain ⟨tag,hu,hx,hp',hq',hout⟩ := ObservedMain.available T ρ β f s b (search A f u t) hpres u x hβ
  obtain ⟨a,ha,hi,hj⟩ := ClockAffine.net_cut clock A.φ A.B hnet hz (.inl tag) (H.main tag.j)
  let k := t+H.main tag.j+a*A.B
  have hc : ∃ a : ℕ, a<H.count (H.tagRole (.inl tag)) ∧ k=t+H.base (H.tagRole (.inl tag))+a*A.B :=
    ⟨a,ha,rfl⟩
  have hst : ∀ a', a'<H.R → ∀ i,
      A.inner f i u (t+(a*A.B-a'*A.B)) = A.inner f i u t := by
    intro a' ha' i
    exact A.not_failed_inner hn ((net_displacement ha ha').trans hw₀) i
  have hsref : ∀ i, A.inner f i u (k-H.main tag.j) = A.inner f i u t := by
    intro i
    convert hst 0 H.R_pos i using 1; dsimp [k]; congr 1; ring
  have hmpos : Monotone (positions (search A f u t)) := by
    obtain ⟨pos,hpos,hm,_,_⟩ := hpres
    change ∀ i, search A f u t i=some (pos i) at hpos
    have heq : positions (search A f u t)=pos := by
      funext i
      simp only [positions,hpos,Option.getD_some]
    rw [heq]
    exact hm
  have hprefix : Prefix A H clock T ρ β (.inl tag) f s t k := by
    refine ⟨(hpos tag.j a ha).1,hc,?_,?_⟩
    · convert hi using 1; dsimp [k]; congr 1; ring
    · change PrefixMain A T ρ β tag f s t k
      refine ⟨?_,?_⟩
      · simpa only [hu] using hpre tag.j a ha
      · rw [hu]
        refine ⟨hp',?_,?_⟩
        · intro i hii
          exact A.inner_position_bounds (hpre tag.j a ha i hii) (hp i)
        · intro i _
          exact hmpos (Fin.castSucc_le_succ i)
  obtain ⟨hguard,hanchor⟩ := available_guard A H G hwidth hc hr hn he
  have hsuffix : Suffix A H clock T ρ reference (.inl tag) f k b := by
    refine ⟨(hpos tag.j a ha).2,hguard,?_,?_,?_⟩
    · rw [hanchor]
      convert hj using 1
      rw [←map_sub]
      congr 1
      dsimp [q,k]
      ring
    · rw [hanchor]
      change A.residue (q-k)=tag.u
      exact (residue_shift (A := A) (G.cut_multiple hc)).symm.trans hu.symm
    · change SuffixMain A H T tag f k b
      refine ⟨?_,?_,?_⟩
      · rw [hu]
        intro a' ha' i hii
        convert hpost tag.j a ha a' ha' i hii using 1; dsimp [k]; ring
      · rw [hu]
        intro a' ha' i _
        rw [hsref]
        convert hst a' ha' i using 1; dsimp [k]; congr 1; ring
      · rw [hu]
        have hread : ObservedMain.SuffixRead T tag f k b (search A f u t) := by
          refine ⟨hq',?_,?_⟩
          · intro i hii
            have hvis := hpost tag.j a ha a ha i hii
            rw [sub_self,add_zero] at hvis
            exact A.inner_position_bounds hvis (hp i)
          · intro i _; exact hmpos (Fin.castSucc_le_succ i)
        apply hread.transfer T (fun _ _ _ => rfl)
        intro i _
        exact (hsref i).symm
  refine ⟨tag,k,hx,hprefix,hsuffix,?_⟩
  change tag.output = ClockAffine.update clock ρ β Tag.input Tag.output
    (A.φ (q-t)) (actual T f s b (search A f u t)) x
  simp only [ClockAffine.update,ClockAffine.shift,ClockAffine.no_off_outside clock hz]
  cases hboundaries : (actual T f s b (search A f u t)).boundaries <;>
    simpa only [hboundaries] using hout

end OuterStream

namespace OuterStream

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical

variable {Alphabet : Type uAlphabet3} {M : Type uM3} {V : Type uV3} {K : Type uK3} {P : Type uP3} {C : Type uC3} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

lemma available_periodic (G : Geometry A H) (hW : A.W=clock.W)
    (hnet : ∀ v : C → RobustClock.Circle, ∃ a : ℕ, a<H.R ∧ dist (A.φ (a*A.B)) v < clock.ρ)
    (hwidth : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets, |h-h'| ≤ A.w)
    {s t b reference : ℤ} {f : ℤ → Alphabet}
    (hr : reference ∈ H.offsets)
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b)
    (hn : ¬A.Failed f t (A.anchor f (b-A.endRule.tail) t))
    (hpos : ∀ (j : Fin (g+1)) (u : Fin A.B) (a : ℕ), a<H.N →
      s<t+H.periodic j u+a*A.B ∧ t+H.periodic j u+a*A.B≤b)
    (hpre : ∀ (j : Fin (g+1)) (a : ℕ), a<H.N →
      A.InnerVisible s (t+H.periodic j (A.residue (A.anchor f (b-A.endRule.tail) t-t))+a*A.B)
        t j (A.residue (A.anchor f (b-A.endRule.tail) t-t)))
    (j : Fin (g+1))
    (hp : A.inner f j (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t = none)
    {n step : ℕ} (hnpos : 0<n) (hnperiod : A.φ n=0)
    (hcop : Nat.Coprime (step*A.B) n)
    (hprog : ∀ a : ℕ, a<n → a*step<H.N ∧
      product T f s (t+H.periodic j (A.residue (A.anchor f (b-A.endRule.tail) t-t))+a*step*A.B) =
        product T f s (t+H.periodic j (A.residue (A.anchor f (b-A.endRule.tail) t-t))))
    (x : V) :
    ∃ (tag : PeriodicTag M V g A.B) (k : ℤ), tag.input=x ∧
      Prefix A H clock T ρ β (.inr tag) f s t k ∧
      Suffix A H clock T ρ reference (.inr tag) f k b ∧
      tag.output=update A clock T ρ β f s b t x := by
  let q := A.anchor f (b-A.endRule.tail) t
  let u := A.residue (q-t)
  let tag : PeriodicTag M V g A.B := ⟨j,u,product T f s (t+H.periodic j u),x,ρ (product T f s b) x⟩
  have hz : A.φ (q-t) ∉ clock.W := by rw [←hW]; exact A.not_failed_clock hn
  obtain ⟨a₀,_,hi,hj⟩ := ClockAffine.net_cut clock A.φ A.B hnet hz (.inr tag) (H.periodic j u)
  obtain ⟨a,ha,hclock⟩ := PeriodicClock.sweep A.φ hnpos hnperiod hcop (H.periodic j u) (a₀*A.B)
  have hindex := (hprog a ha).1
  let k := t+H.periodic j u+(a*step:ℕ)*A.B
  have hkeq : k-t=H.periodic j u+(a:ℤ)*(step*A.B:ℕ) := by
    dsimp [k]
    ring
  have hpreclock : A.φ (k-t) ∈ clock.I (.inr tag) := by rw [hkeq,hclock];exact hi
  have hpostclock : A.φ (q-k) ∈ clock.J (.inr tag) := by
    rw [show q-k=(q-t)-(k-t) by ring,map_sub,hkeq,hclock]
    exact hj
  have hc : ∃ a' : ℕ, a'<H.count (H.tagRole (.inr tag)) ∧
      k=t+H.base (H.tagRole (.inr tag))+a'*A.B := ⟨a*step,hindex,rfl⟩
  have hprod : product T f s k=tag.prefixProduct := by
    simpa only [k, Nat.cast_mul] using (hprog a ha).2
  have hk := hpos j u (a*step) hindex
  have hprefix : Prefix A H clock T ρ β (.inr tag) f s t k :=
    ⟨hk.1,hc,hpreclock,⟨hpre j (a*step) hindex,hp,hprod⟩⟩
  obtain ⟨hguard,hanchor⟩ := available_guard A H G hwidth hc hr hn he
  have hsuffix : Suffix A H clock T ρ reference (.inr tag) f k b := by
    refine ⟨hk.2,hguard,?_,?_,?_⟩
    · rw [hanchor];exact hpostclock
    · rw [hanchor]
      exact (residue_shift (A := A) (G.cut_multiple hc)).symm
    · change ρ (product T f s b) x = ρ (tag.prefixProduct*product T f k b) x
      rw [←hprod,←product_append T f hk.1.le hk.2]
  refine ⟨tag,k,rfl,hprefix,hsuffix,?_⟩
  have hnone := factors_absent T f (s := s) (b := b) (search := search A f u t) (i := j) hp
  change ρ (product T f s b) x = ClockAffine.update clock ρ β Tag.input Tag.output
    (A.φ (q-t)) (actual T f s b (search A f u t)) x
  rw [ClockAffine.update_periodic clock ρ β Tag.input Tag.output _
    (ClockAffine.no_off_outside clock hz) hnone]
  rfl

end OuterStream

namespace ExceptionalOrigins.Parameters

variable {Alphabet : Type uAlphabet4} {J : Type uJ} {C : Type uC4} (A : Parameters Alphabet J C)

lemma residue_cast (u : Fin A.B) : A.residue u=u := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [residue_val,Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast u.isLt)]

end ExceptionalOrigins.Parameters

namespace SourceSchedule.Early

open WordIntervals LocalMarkers SplitMetadata BoundarySnapshot
open scoped Classical BigOperators

variable {Alphabet : Type uAlphabet5} {T : Type uT} {P : Type uP4} {C : Type uC5} [Fintype T] [Fintype P] [Fintype C]
    {g' B size : ℕ} {clock : RobustClock.Specification T P C}
    {label : P → Fin g'} {reserved : P → ℤ}
    (S : Early (Alphabet := Alphabet) clock B size label reserved)
    (g : ℕ) (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))

lemma earlyLast_nonneg : 0 ≤ S.β (Fin.last g') := by
  rw [←S.β_zero]
  exact S.β_strict.monotone (Fin.zero_le _)

lemma offset_envelope {a : ℤ} (ha : a ∈ (S.cuts g).offsets) : |a| ≤ S.envelope g := by
  have hh := abs_le_finiteBound ha
  have hw' := S.sweepWidth_pos g
  have hrest : 0 ≤ 2*|((B*S.R:ℕ):ℤ)|+|S.rule.r|+
      (absoluteBound (fun j : Fin (g+1) => S.inner.boundary j.val):ℤ)+
      (absoluteBound S.inner.H:ℤ)+|S.inner.extension|+
      (3*(innerD S.p (B*S.R))^2+1:ℕ)+(size*innerD S.p (B*S.R):ℕ) := by positivity
  dsimp only [envelope]
  omega

lemma cut_bounds {f : ℤ → Alphabet} {s b a : ℤ} (ha : a ∈ (S.cuts g).offsets)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b) :
    s<s+L.lag+a ∧ s+L.lag+a<b := by
  have hbound := abs_le.mp (S.offset_envelope g ha)
  have hlag := L.lag_margin
  have hlast := S.earlyLast_nonneg
  have hoff := L.offset_margin
  have hb := L.complete_lower he
  have hw := (S.sweepWidth_pos g).le
  have hwidth := L.endRule.width_nonneg
  have hr := L.radius_nonneg
  have hK : (0:ℤ) ≤ L.endRule.K := Int.natCast_nonneg _
  constructor <;> omega

lemma shifted_inner_visible (hB : 0<B) {f : ℤ → Alphabet} {s b δ : ℤ}
    (hδ : |δ| ≤ S.sweepWidth g)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (j : Fin (g+1)) (u : Fin B) :
    (S.parameters g L hB).InnerVisible (s+S.β (Fin.last g')) b (s+L.lag+δ) j u := by
  let A := S.parameters g L hB
  have hh := S.actual_visible g L hB (Q := s+L.lag+δ+u) hδ he
  have hw : 0 ≤ A.w₀ := Int.natCast_nonneg _
  have hv := ExceptionalOrigins.Parameters.Visible.innerVisible A hh hw j
  rw [show s+L.lag+δ+(u:ℤ)-(s+L.lag+δ)=(u:ℤ) by ring] at hv
  have hres : A.residue (u:ℤ)=u := A.residue_cast u
  rw [hres] at hv
  exact hv

lemma main_prefix_visible (hB : 0<B) {f : ℤ → Alphabet} {s b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (j : Fin g) (a : ℕ) (i : Fin (g+1)) (hi : i.val≤j.val) (u : Fin B) :
    (S.parameters g L hB).InnerVisible s (s+L.lag+(S.cuts g).main j+a*B) (s+L.lag) i u := by
  have hw : |(0:ℤ)|≤S.sweepWidth g := by simpa using (S.sweepWidth_pos g).le
  have hv := S.shifted_inner_visible g L hB hw he i u
  have hm := S.inner.main_before hB (by have := S.rule.radius_ge;omega) i.val j.val a u hi
  have hlast := S.earlyLast_nonneg
  constructor
  · have hh := hv.1
    change s + S.β (Fin.last g') ≤ s + L.lag + 0 + S.inner.boundary i.val - S.rule.r at hh
    change s ≤ s + L.lag + S.inner.boundary i.val - S.rule.r
    omega
  · change s+L.lag+S.inner.boundary i.val+S.inner.H u+S.rule.r ≤
      s+L.lag+S.inner.mainBase j.val+a*B
    change S.inner.boundary i.val+S.inner.H u+S.rule.r < S.inner.mainBase j.val+a*B at hm
    omega

lemma main_suffix_visible (hB : 0<B) {f : ℤ → Alphabet} {s b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (j : Fin g) (a a' : ℕ) (ha : a<S.R) (ha' : a'<S.R)
    (i : Fin (g+1)) (hi : j.val < i.val) (u : Fin B) :
    (S.parameters g L hB).InnerVisible (s+L.lag+(S.cuts g).main j+a*B) b
      (s+L.lag+(a*B-a'*B)) i u := by
  have hδ : |(a:ℤ)*B-a'*B|≤S.sweepWidth g := by
    have hh := S.offsets_difference g ((S.cuts g).offset_mem (.inl j) a ha)
      ((S.cuts g).offset_mem (.inl j) a' ha')
    change |(S.cuts g).main j+a*B-((S.cuts g).main j+a'*B)|<S.sweepWidth g at hh
    rw [show (S.cuts g).main j+(a:ℤ)*B-((S.cuts g).main j+a'*B)=a*B-a'*B by ring] at hh
    exact hh.le
  have hv := S.shifted_inner_visible g L hB hδ he i u
  have hm := S.inner.main_after hB (by have := S.rule.radius_ge;omega)
    i.val j.val a' (s+L.lag+S.inner.mainBase j.val+a*B) hi ha'
  constructor
  · change s+L.lag+S.inner.mainBase j.val+a*B ≤
      s+L.lag+(a*B-a'*B)+S.inner.boundary i.val-S.rule.r
    omega
  · exact hv.2

lemma periodic_prefix_visible (hB : 0<B) {f : ℤ → Alphabet} {s b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (j : Fin (g+1)) (u : Fin B) (a : ℕ) :
    (S.parameters g L hB).InnerVisible s (s+L.lag+(S.cuts g).periodic j u+a*B) (s+L.lag) j u := by
  have hw : |(0:ℤ)|≤S.sweepWidth g := by simpa using (S.sweepWidth_pos g).le
  have hv := S.shifted_inner_visible g L hB hw he j u
  have hm := S.inner.periodic_before j.val a u
  have hlast := S.earlyLast_nonneg
  constructor
  · have hh := hv.1
    change s + S.β (Fin.last g') ≤ s + L.lag + 0 + S.inner.boundary j.val - S.rule.r at hh
    change s ≤ s + L.lag + S.inner.boundary j.val - S.rule.r
    omega
  · change s+L.lag+S.inner.boundary j.val+S.inner.H u+S.rule.r ≤
      s+L.lag+(S.inner.boundary j.val+S.inner.H u+S.inner.lag+0*B)+a*B
    change S.inner.boundary j.val+S.inner.H u+S.rule.r <
      S.inner.boundary j.val+S.inner.H u+S.inner.lag+a*B at hm
    omega

end SourceSchedule.Early

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace SourceSchedule.Early

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical BigOperators

variable {Alphabet : Type uAlphabet} {M : Type uM} {V : Type uV} {K : Type uK} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C]
    {g g' B : ℕ} {clock : RobustClock.Specification (Tag M V g B) P C}
    {label : P → Fin g'} {reserved : P → ℤ}
    (S : Early (Alphabet := Alphabet) clock B (Fintype.card M) label reserved)
    (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))
    (hB : 0<B) (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

lemma outer_available
    (hβ : ∀ a c, ShiftTableProperty g (ClockAffine.productTable ρ a c) (β a c))
    {f : ℤ → Alphabet} {s b reference : ℤ}
    (hr : reference ∈ (S.cuts g).offsets)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (hn : ¬(S.parameters g L hB).Failed f (s+L.lag)
      ((S.parameters g L hB).anchor f (b-L.endRule.tail) (s+L.lag))) (x : V) :
    ∃ (tag : Tag M V g B) (k : ℤ), tag.input=x ∧
      OuterStream.Prefix (S.parameters g L hB) (S.cuts g) clock T ρ β tag f s (s+L.lag) k ∧
      OuterStream.Suffix (S.parameters g L hB) (S.cuts g) clock T ρ reference tag f k b ∧
      tag.output=OuterStream.update (S.parameters g L hB) clock T ρ β f s b (s+L.lag) x := by
  let A := S.parameters g L hB
  let H := S.cuts g
  let t := s+L.lag
  let q := A.anchor f (b-A.endRule.tail) t
  let u := A.residue (q-t)
  have hpos : ∀ (role : H.Role) (a : ℕ), a<H.count role →
      s<t+H.base role+a*B ∧ t+H.base role+a*B ≤ b := by
    intro role a ha
    have hh := S.cut_bounds g L (H.offset_mem role a ha) he
    dsimp only [t]
    exact ⟨by omega,by omega⟩
  have hvis : ∀ i, A.InnerVisible s b t i u := by
    intro i
    have hh := S.shifted_inner_visible g L hB
      (δ := 0) (by simpa using (S.sweepWidth_pos g).le) he i u
    simp only [add_zero] at hh
    have hlast := S.earlyLast_nonneg
    exact ⟨by have := hh.1;dsimp only [A,t] at *;omega,hh.2⟩
  have hwidth : ∀ a ∈ H.offsets, ∀ a' ∈ H.offsets, |a-a'| ≤ A.w := by
    intro a ha a' ha'
    exact (S.offsets_difference g ha ha').le
  by_cases hp : ∀ i, A.inner f i u t ≠ none
  · obtain ⟨tag,k,hx,hpre,hsuf,hout⟩ := OuterStream.available_main A H clock T ρ β
      (S.geometry g L hB) rfl S.net (le_refl _) hwidth hβ hr he hn
      (fun j a ha => hpos (.inl j) a ha)
      (fun j a _ i hi => S.main_prefix_visible g L hB he j a i hi u)
      (fun j a ha a' ha' i hi => S.main_suffix_visible g L hB he j a a' ha ha' i hi u)
      hvis hp x
    exact ⟨.inl tag,k,hx,hpre,hsuf,hout⟩
  · push Not at hp
    obtain ⟨j,hj⟩ := hp
    let z := t+S.inner.boundary j.val
    have hboundary : 0 ≤ S.inner.boundary j.val := by
      exact mul_nonneg (Int.natCast_nonneg _) (by have := S.inner.gap_pos;omega)
    have hs : s ≤ z+innerD S.p (B*S.R) := by
      have hl := L.lag_pos
      have hd : (0:ℤ) ≤ innerD S.p (B*S.R) := Int.natCast_nonneg _
      dsimp [z,t]
      omega
    have hnomarker : ∀ y, z ≤ y → y ≤ z+S.inner.H u+S.inner.extension → y∉S.rule.markers f :=
      A.not_failed_absent hn j hj
    obtain ⟨p,hp,hpd,hprogress⟩ := PeriodicCuts.progression S.inner S.rule
      (innerD_ge S.p (B*S.R)) (by omega) (by have := S.rule.radius_ge;omega)
      hB S.period_pos T f s z u hs hnomarker
    have hcop : Nat.Coprime (p*(Fintype.card M).factorial*B) S.period := by
      apply PeriodicClock.progression_coprime S.denominator S.prime hp hpd
        (Nat.factorial_pos _) hB
      intro c
      have hh := S.den_large c
      exact ⟨(le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hh),
        (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hh),
        (le_max_left _ _).trans_lt hh⟩
    have hprog : ∀ a : ℕ, a<S.period → a*(p*(Fintype.card M).factorial)<H.N ∧
        product T f s (t+H.periodic j u+(a:ℤ)*(p*(Fintype.card M).factorial:ℕ)*B) =
          product T f s (t+H.periodic j u) := by
      intro a ha
      obtain ⟨ha',hprod⟩ := hprogress a ha
      refine ⟨by simpa only [H,cuts,period,Nat.mul_assoc] using ha',?_⟩
      have h₁ : t+H.periodic j u+(a:ℤ)*(p*(Fintype.card M).factorial:ℕ)*B =
          z+S.inner.H u+S.inner.lag+(a*p*(Fintype.card M).factorial*B:ℕ) := by
        dsimp only [H,cuts,IntegerSchedules.Inner.periodicOffset,z]
        push_cast
        ring
      have h₂ : t+H.periodic j u=z+S.inner.H u+S.inner.lag := by
        dsimp only [H,cuts,IntegerSchedules.Inner.periodicOffset,z]
        ring
      rw [h₁,h₂]
      exact hprod
    obtain ⟨tag,k,hx,hpre,hsuf,hout⟩ := OuterStream.available_periodic A H clock T ρ β
      (S.geometry g L hB) rfl S.net hwidth hr he hn
      (fun j u a ha => hpos (.inr (j,u)) a ha)
      (fun j a _ => S.periodic_prefix_visible g L hB he j u a) j hj S.period_pos
      (PeriodicClock.period S.denominator S.numerator (fun c => (S.prime c).pos)) hcop hprog x
    exact ⟨.inr tag,k,hx,hpre,hsuf,hout⟩

end SourceSchedule.Early

namespace InnerStream

open WordIntervals SplitMetadata LocalMarkers

variable {Alphabet : Type uAlphabet2} {M : Type uM2} {V : Type uV2} {K : Type uK2} {P : Type uP2} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype K] [Fintype P] [Fintype C] {g g' μ : ℕ}
    (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)
    (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

lemma available
    (hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ))
    {s b H : ℤ} {f : ℤ → Alphabet} (reference : Roster M (V × K) K g' μ)
    (hbad : (A.bad p f (s+lag) (b-A.endRule.tail)).card < μ)
    (hvis : ∀ a i, A.Visible (s+p a) b (s+lag+(p a-p i))
      (A.anchor f (b-A.endRule.tail) (s+lag+(p a-p i))))
    (hnear : ∀ i j, |p i-p j| ≤ H)
    (hnest : (A.endRule.d : ℤ)+(A.endRule.B-1)*A.endRule.S+H ≤ 3*A.endRule.d)
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K-H) (hover' : H<A.endRule.K)
    (hend : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (s+lag+A.endRule.offset) (A.endRule.small f (s+lag+A.endRule.offset)) b)
    (hfailed : A.Failed f (s+lag) (A.anchor f (b-A.endRule.tail) (s+lag))) (x : V × K) :
    ∃ (slot : Roster M (V × K) K g' μ) (k : ℤ), slot.1.input=x ∧
      Prefix T early γ p slot f s k ∧
      Suffix A clock T ρ β early p lag reference slot f k b ∧
      slot.1.output=update A clock T ρ β early γ f s b (s+lag) x := by
  let ψ := hypothetical A clock T ρ β early f s b (s+lag)
  obtain ⟨kind,hx,hp,hq,hout⟩ := ObservedInner.available T γ f (fun i => s+early i) ψ x (hγ ψ)
  obtain ⟨copy,hcopy⟩ := SuffixDecoder.available_copy A p lag s b H f reference kind
    hbad hvis hnear hnest hover hover' hend hfailed
  let slot : Roster M (V × K) K g' μ := (kind,copy)
  have hs : s+p slot-p slot=s := by ring
  refine ⟨slot,s+p slot,hx,⟨rfl,hp⟩,⟨hcopy,?_⟩,hout⟩
  simpa only [hs] using hq

end InnerStream

namespace SourceSchedule.Late

variable {Alphabet : Type uAlphabet3} {B : ℕ} {h w E earlyLast : ℤ}
    (L : Late Alphabet B h w E earlyLast)

lemma count_margins (hB : 0<B) (hh : 0 ≤ h) (hw : 0 ≤ w) :
    2*h+2*w<L.endRule.S ∧
    2*h+((B:ℤ)-1)*L.endRule.S+2*w<L.endRule.d ∧
    2*h+2*((B:ℤ)-1)*L.endRule.S<L.endRule.d := by
  have hS := L.endRule.S_nonneg
  have hBi : (1:ℤ) ≤ B := by exact_mod_cast hB
  have hBS : 0 ≤ (B:ℤ)*L.endRule.S := mul_nonneg (by omega) hS
  have hs := L.spacing
  have hd := L.separation
  constructor
  · omega
  constructor <;> nlinarith

lemma decoder_margins (hB : 0<B) (hh : 0 ≤ h) (hw : 0 ≤ w) :
    (L.endRule.d:ℤ)+(L.endRule.B-1)*L.endRule.S+h ≤ 3*L.endRule.d ∧
    (L.endRule.d:ℤ)^2 ≤ L.endRule.K-h ∧ h<L.endRule.K := by
  have hBi : (1:ℤ) ≤ B := by exact_mod_cast hB
  have hS := L.endRule.S_nonneg
  have hBS : 0 ≤ (B:ℤ)*L.endRule.S := mul_nonneg (by omega) hS
  have hd := L.separation
  have hd₂ : (2:ℤ) ≤ L.endRule.d := by exact_mod_cast L.endRule.d_ge
  have hK := L.endRule.seed_long
  have hK' : 3*(L.endRule.d:ℤ)^2<L.endRule.K := by exact_mod_cast hK
  rw [L.modulus]
  have hh' : h<L.endRule.d := by nlinarith
  refine ⟨?_,?_,?_⟩ <;> nlinarith [sq_nonneg (L.endRule.d:ℤ)]

end SourceSchedule.Late

namespace SourceSchedule.Early

open scoped Classical

variable {Alphabet : Type uAlphabet4} {T : Type uT} {P : Type uP3} {C : Type uC3} [Fintype T] [Fintype P] [Fintype C]
    {g' B size : ℕ} {clock : RobustClock.Specification T P C}
    {label : P → Fin g'} {reserved : P → ℤ}
    (S : Early (Alphabet := Alphabet) clock B size label reserved)
    (g : ℕ) (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))
    (hB : 0<B)

lemma full_bad_card
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (reserved i-reserved j)%B ≠ (reserved i'-reserved j')%B)
    (μ : ℕ) (hμ : 20*(10000000*Real.log (2*Fintype.card T)+4*(g+1))+10<μ)
    (f : ℤ → Alphabet) (t q₀ : ℤ) :
    ((S.parameters g L hB).bad S.p f t q₀).card<μ := by
  have hm : ∀ i j, (S.p i-S.p j)%B=(reserved i-reserved j)%B := by
    intro i j
    rw [Int.sub_emod,S.reserved_eq,S.reserved_eq,←Int.sub_emod]
  have hmar := L.count_margins hB S.diameter_pos.le (S.sweepWidth_pos g).le
  have hmod' : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (S.p i-S.p j)%(S.parameters g L hB).B ≠
        (S.p i'-S.p j')%(S.parameters g L hB).B := by
    intro i j i' j' hij hij' hn
    change (S.p i-S.p j)%B ≠ (S.p i'-S.p j')%B
    rw [hm,hm]
    exact hmod i j i' j' hij hij' hn
  have hgap₀ : 2*(S.parameters g L hB).w₀ ≤ 2*(B*S.R:ℕ)+2 := by
    change 2*((B*S.R:ℕ):ℤ) ≤ 2*((B*S.R:ℕ):ℤ)+2
    omega
  have hinner : 2*S.diameter+2*(S.parameters g L hB).w₀ < (S.parameters g L hB).d := by
    have hh := innerD_bound S.p (B*S.R)
    change 2*S.diameter+2*(B*S.R:ℕ)<(innerD S.p (B*S.R):ℤ)
    have hpos := S.diameter_pos
    have hBR : (0:ℤ) ≤ (B*S.R:ℕ) := Int.natCast_nonneg _
    change 10*(2*S.diameter+2*(B*S.R:ℕ)+5)<(innerD S.p (B*S.R):ℤ) at hh
    omega
  have hwidth : ∀ u v, u ≠ v → 2*S.diameter+
      2*max (S.parameters g L hB).ext (S.parameters g L hB).w₀ <
        |(S.parameters g L hB).H u-(S.parameters g L hB).H v| := by
    intro u v huv
    have hh := S.inner.H_separated u v huv
    change 2*S.diameter+2*max S.inner.extension (B*S.R:ℕ) < |S.inner.H u-S.inner.H v|
    change 2*S.diameter+2*max S.inner.extension (B*S.R:ℕ)+2 < |S.inner.H u-S.inner.H v| at hh
    omega
  exact ExceptionalOrigins.Parameters.bad_card (S.parameters g L hB) clock S.p S.diameter
    (2*(B*S.R)+2) rfl S.approximate
    (fun i j => difference_bound S.p i j) hmod' S.separated (Int.natCast_nonneg _)
    hgap₀ hinner hwidth hmar.1 hmar.2.1 hmar.2.2 μ
    (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hμ) f t q₀

end SourceSchedule.Early

namespace SourceSchedule.Early

open WordIntervals SplitMetadata LocalMarkers

variable {Alphabet : Type uAlphabet5} {M : Type uM3} {V : Type uV3} {K : Type uK3} {C : Type uC4} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype K] [Fintype C]
    {g g' μ B : ℕ}
    {clock : RobustClock.Specification (Tag M V g B) (Roster M (V × K) K g' μ) C}
    {reserved : Roster M (V × K) K g' μ → ℤ}
    (S : Early (Alphabet := Alphabet) clock B (Fintype.card M) (fun i => i.1.j) reserved)
    (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))
    (hB : 0<B) (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)

omit [Monoid M] in
lemma roster_visible {f : ℤ → Alphabet} {s b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (a i : Roster M (V × K) K g' μ) :
    (S.parameters g L hB).Visible (s+S.p a) b (s+L.lag+(S.p a-S.p i))
      ((S.parameters g L hB).anchor f (b-L.endRule.tail) (s+L.lag+(S.p a-S.p i))) := by
  apply ExceptionalOrigins.Parameters.Visible.mono _
    (S.actual_visible g L hB (S.stencil_difference g a i).le he) _ (le_refl _)
  have hb := (S.block a).2.trans_le (S.β_strict.monotone (Fin.le_last _))
  omega

lemma inner_available
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (reserved i-reserved j)%B ≠ (reserved i'-reserved j')%B)
    (hμ : 20*(10000000*Real.log (2*Fintype.card (Tag M V g B))+4*(g+1))+10<μ)
    (hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ))
    {f : ℤ → Alphabet} {s b : ℤ} (reference : Roster M (V × K) K g' μ)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (hf : (S.parameters g L hB).Failed f (s+L.lag)
      ((S.parameters g L hB).anchor f (b-L.endRule.tail) (s+L.lag))) (x : V × K) :
    ∃ (slot : Roster M (V × K) K g' μ) (k : ℤ), slot.1.input=x ∧
      InnerStream.Prefix T S.β γ S.p slot f s k ∧
      InnerStream.Suffix (S.parameters g L hB) clock T ρ β S.β S.p L.lag reference slot f k b ∧
      slot.1.output=InnerStream.update (S.parameters g L hB) clock T ρ β S.β γ f s b (s+L.lag) x := by
  have hm := L.decoder_margins hB S.diameter_pos.le (S.sweepWidth_pos g).le
  exact InnerStream.available (S.parameters g L hB) clock T ρ β S.β γ S.p L.lag hγ reference
    (S.full_bad_card g L hB hmod μ hμ f (s+L.lag) (b-L.endRule.tail))
    (S.roster_visible L hB he) (difference_bound S.p) hm.1 hm.2.1 hm.2.2 he hf x

end SourceSchedule.Early

namespace SlotResidues

variable (P : Type uP4) [Fintype P]

noncomputable def slotIndex (p : P) : ℤ := ((Fintype.equivFin P) p).val+1
noncomputable def reserved (p : P) : ℤ := representative (Fintype.card P) (slotIndex P p)
noncomputable def slotModulus : ℕ := 20*(Fintype.card P+1)^3

lemma slotIndex_bounds (p : P) : 1 ≤ slotIndex P p ∧ slotIndex P p ≤ Fintype.card P := by
  have hh := ((Fintype.equivFin P) p).isLt
  dsimp [slotIndex]
  omega

lemma slotIndex_injective : Function.Injective (slotIndex P) := by
  intro a b hh
  apply (Fintype.equivFin P).injective
  apply Fin.ext
  dsimp [slotIndex] at hh
  omega

lemma reserved_distinct (i j i' j' : P) (hij : i ≠ j) (hij' : i' ≠ j')
    (hn : (i,j) ≠ (i',j')) :
    (reserved P i-reserved P j)%slotModulus P ≠
      (reserved P i'-reserved P j')%slotModulus P := by
  have hi := slotIndex_bounds P i
  have hj := slotIndex_bounds P j
  have hi' := slotIndex_bounds P i'
  have hj' := slotIndex_bounds P j'
  have hN : (0:ℤ)<Fintype.card P := by omega
  intro hh
  have hB : (slotModulus P:ℤ)=modulus (Fintype.card P) := by
    simp only [slotModulus,modulus,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  rw [hB] at hh
  obtain ⟨h₁,h₂⟩ := distinct_differences hN hi.1 hi.2 hj.1 hj.2 hi'.1 hi'.2 hj'.1 hj'.2
    ((slotIndex_injective P).ne hij) ((slotIndex_injective P).ne hij') hh
  exact hn (Prod.ext ((slotIndex_injective P) h₁) ((slotIndex_injective P) h₂))

lemma slotModulus_pos : 0<slotModulus P := by dsimp [slotModulus];positivity

end SlotResidues

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace FiniteRecognition

variable {Alphabet : Type uAlphabet}

lemma regular_mul {L R : Language Alphabet} (hL : L.IsRegular) (hR : R.IsRegular) :
    (L*R).IsRegular := by
  let combine (q : Language Alphabet) (s : Set (Language Alphabet)) : Language Alphabet :=
    let U : Language Alphabet := {w | ∃ r ∈ s, w ∈ r}
    q*R + U
  apply Language.IsRegular.of_finite_range_leftQuotient
  apply (hL.finite_range_leftQuotient.image2 combine hR.finite_range_leftQuotient.powerset).subset
  rintro _ ⟨x,rfl⟩
  let s : Set (Language Alphabet) := {r | ∃ u v, x=u++v ∧ u∈L ∧ r=R.leftQuotient v}
  refine ⟨L.leftQuotient x, ⟨x,rfl⟩, s, ?_, ?_⟩
  · rintro r ⟨u,v,_,_,rfl⟩
    exact ⟨v,rfl⟩
  · ext y
    change (y∈(L.leftQuotient x)*R ∨ ∃ r∈s,y∈r) ↔ x++y∈L*R
    constructor
    · rintro (hy | ⟨r,⟨u,v,hx,hu,hr⟩,hy⟩)
      · obtain ⟨u,hu,v,hv,rfl⟩ := Language.mem_mul.mp hy
        exact Language.mem_mul.mpr ⟨x++u,hu,v,hv,by simp⟩
      · rw [hr] at hy
        exact Language.mem_mul.mpr ⟨u,hu,v++y,hy,by simp [hx]⟩
    · rintro ⟨u,hu,v,hv,he⟩
      rcases List.append_eq_append_iff.mp he.symm with ⟨a,ha,hy⟩ | ⟨a,ha,hv'⟩
      · left
        refine Language.mem_mul.mpr ⟨a,?_,v,hv,hy.symm⟩
        change x++a∈L
        rwa [←ha]
      · right
        refine ⟨R.leftQuotient a,⟨u,a,ha,hu,rfl⟩,?_⟩
        change a++y∈R
        rw [←hv']
        exact hv

lemma regular_finite {L : Language Alphabet} (hL : (L : Set (List Alphabet)).Finite) :
    L.IsRegular := by
  let S : Set (List Alphabet) := ⋃ w∈L, {v | v∈w.tails}
  have hS : S.Finite := hL.biUnion (fun w _ => w.tails.finite_toSet)
  apply Language.IsRegular.of_finite_range_leftQuotient
  apply hS.powerset.subset
  rintro _ ⟨x,rfl⟩ y hy
  exact Set.mem_iUnion_of_mem (x++y) (Set.mem_iUnion_of_mem hy
    ((List.mem_tails _ _).mpr ⟨x,rfl⟩))

lemma regular_singleton (w : List Alphabet) : ({w} : Language Alphabet).IsRegular :=
  regular_finite (Set.finite_singleton w)

lemma regular_finset_iSup {I : Type uI} (s : Finset I) (L : I → Language Alphabet)
    (h : ∀ i∈s, (L i).IsRegular) : (⨆ i∈s,L i).IsRegular := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty,iSup_false,iSup_bot]
    exact regular_finite Set.finite_empty
  | @insert i s hi ih =>
    have he : (⨆ j∈insert i s,L j)=L i+(⨆ j∈s,L j) := by
      ext w
      simp only [Language.mem_iSup,Finset.mem_insert,Language.mem_add]
      aesop
    rw [he]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma regular_iSup {I : Type uI2} [Finite I] (L : I → Language Alphabet)
    (h : ∀ i, (L i).IsRegular) : (⨆ i,L i).IsRegular := by
  classical
  let := Fintype.ofFinite I
  simpa only [Finset.mem_univ, iSup_pos] using
    regular_finset_iSup (Finset.univ : Finset I) L (fun i _ => h i)

lemma regular_recognized {M : Type uM} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) (F : Set M) :
    Language.IsRegular ({w | T (FreeMonoid.ofList w)∈F} : Language Alphabet) := by
  let A : DFA Alphabet M := ⟨fun q a => q*T (FreeMonoid.of a),1,F⟩
  have he : ∀ (w : List Alphabet) (q : M), A.evalFrom q w=q*T (FreeMonoid.ofList w) := by
    intro w
    induction w with
    | nil => intro q;simp [DFA.evalFrom]
    | cons a w ih =>
      intro q
      rw [DFA.evalFrom_cons,ih]
      change q*T (FreeMonoid.of a)*T (FreeMonoid.ofList w)=q*T (FreeMonoid.of a*FreeMonoid.ofList w)
      rw [map_mul,mul_assoc]
  apply Language.isRegular_iff.mpr
  refine ⟨M,inferInstance,A,?_⟩
  ext w
  simp only [DFA.mem_accepts,DFA.eval,he]
  change 1*T (FreeMonoid.ofList w)∈F ↔ T (FreeMonoid.ofList w)∈F
  rw [one_mul]

lemma regular_sandwich [Finite Alphabet] {M : Type uM2} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) (N tail : ℕ) (L : Language Alphabet)
    (hc : ∀ (a b x y : List Alphabet), a.length=N → b.length=tail →
      T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y) →
      (a++x++b∈L ↔ a++y++b∈L)) : L.IsRegular := by
  classical
  let small : Language Alphabet := {w | w.length<N+tail ∧ w∈L}
  have hsmall : small.IsRegular := regular_finite
    ((List.finite_length_le Alphabet (N+tail)).subset (fun w hw => hw.1.le))
  let As := (List.finite_length_le Alphabet N).toFinset.filter (fun a => a.length=N)
  let Bs := (List.finite_length_le Alphabet tail).toFinset.filter (fun b => b.length=tail)
  let F (a b : List Alphabet) : Set M := {q | ∃ x, T (FreeMonoid.ofList x)=q ∧ a++x++b∈L}
  let R (a b : List Alphabet) : Language Alphabet :=
    let mid : Language Alphabet := {x | T (FreeMonoid.ofList x)∈F a b}
    ({a} : Language Alphabet)*mid*({b} : Language Alphabet)
  have hR : ∀ a b, (R a b).IsRegular := fun a b =>
    regular_mul (regular_mul (regular_singleton a) (regular_recognized T (F a b)))
      (regular_singleton b)
  have he : L=small+(⨆ a∈As,⨆ b∈Bs,R a b) := by
    ext w
    constructor
    · intro hw
      by_cases hl : w.length<N+tail
      · exact Or.inl ⟨hl,hw⟩
      · let a := w.take N
        let x := (w.drop N).take (w.length-N-tail)
        let b := w.drop (w.length-tail)
        have ha : a.length=N := by simp only [a,List.length_take];omega
        have hb : b.length=tail := by simp only [b,List.length_drop];omega
        have hw' : a++x++b=w := by
          have hcut : N+(w.length-N-tail)=w.length-tail := by omega
          dsimp [a,x,b]
          rw [←hcut,←List.drop_drop,List.append_assoc,List.take_append_drop,List.take_append_drop]
        right
        apply Language.mem_iSup.mpr
        refine ⟨a,Language.mem_iSup.mpr ⟨?_,Language.mem_iSup.mpr ⟨b,Language.mem_iSup.mpr ⟨?_,?_⟩⟩⟩⟩
        · simp only [As,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,ha,le_refl,and_self]
        · simp only [Bs,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,hb,le_refl,and_self]
        · rw [←hw']
          exact Language.append_mem_mul (Language.append_mem_mul (Set.mem_singleton _)
            ⟨x,rfl,by simpa only [hw'] using hw⟩) (Set.mem_singleton _)
    · rintro (⟨_,hw⟩ | hw)
      · exact hw
      · obtain ⟨a,hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨ha,hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨b,hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨hb,hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨u,hu,v,hv,rfl⟩ := Language.mem_mul.mp hw
        obtain ⟨a',ha',x,hx,rfl⟩ := Language.mem_mul.mp hu
        have ha'eq : a'=a := ha'
        subst a'
        have hveq : v=b := hv
        subst v
        obtain ⟨y,hy,hyL⟩ := hx
        exact (hc a b y x (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hy).mp hyL
  rw [he]
  exact hsmall.add (regular_finset_iSup As _ (fun a _ =>
    regular_finset_iSup Bs _ (fun b _ => hR a b)))

end FiniteRecognition
namespace PeriodicSummary

variable {Alphabet : Type uAlphabet2} {p : ℕ}

noncomputable def matcher (v : ZMod p → Alphabet) : DFA Alphabet (Option (ZMod p)) := by
  classical
  exact ⟨fun q a => q.bind (fun i => if a=v i then some (i+1) else none),some 0, {q | q.isSome}⟩

def Fits (v : ZMod p → Alphabet) : ZMod p → List Alphabet → Prop
  | _, [] => True
  | q, a::w => a=v q ∧ Fits v (q+1) w

lemma eval_none (v : ZMod p → Alphabet) (w : List Alphabet) :
    (matcher v).evalFrom none w=none := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [DFA.evalFrom_cons,matcher] using ih

lemma eval_isSome (v : ZMod p → Alphabet) (w : List Alphabet) (q : ZMod p) :
    ((matcher v).evalFrom (some q) w).isSome ↔ Fits v q w := by
  classical
  induction w generalizing q with
  | nil => simp [DFA.evalFrom_nil,Fits]
  | cons a w ih =>
    rw [DFA.evalFrom_cons]
    change ((matcher v).evalFrom (if a=v q then some (q+1) else none) w).isSome ↔ _
    by_cases h : a=v q
    · rw [ite_eq_left h,ih]
      simp only [Fits,h,true_and]
    · rw [ite_eq_right h,eval_none]
      simp only [Option.isSome_none,Bool.false_eq_true,Fits,h,false_and]

lemma fits_iff (v : ZMod p → Alphabet) (w : List Alphabet) (q : ZMod p) :
    Fits v q w ↔ ∀ i : Fin w.length, w[i.val]=v (q+i.val) := by
  induction w generalizing q with
  | nil => simp [Fits]
  | cons a w ih =>
    simp only [Fits,ih,List.length_cons,Fin.forall_fin_succ,List.getElem_cons_zero,
      List.getElem_cons_succ,Fin.val_zero,Nat.cast_zero,add_zero,Fin.val_succ,Nat.cast_add,
      Nat.cast_one]
    constructor
    · rintro ⟨ha,hw⟩
      exact ⟨ha,fun i => by simpa [add_assoc,add_comm,add_left_comm] using hw i⟩
    · rintro ⟨ha,hw⟩
      exact ⟨ha,fun i => by simpa [add_assoc,add_comm,add_left_comm] using hw i⟩

noncomputable def transition : FreeMonoid Alphabet →*
    ((ZMod p → Alphabet) → (Function.End (Option (ZMod p)))ᵐᵒᵖ) :=
  MonoidHom.pi (fun v => FiniteRecognition.transition (matcher v))

lemma fits_congr {x y : List Alphabet}
    (h : transition (p := p) (FreeMonoid.ofList x)=transition (FreeMonoid.ofList y))
    (v : ZMod p → Alphabet) (q : ZMod p) : Fits v q x ↔ Fits v q y := by
  have he := congrArg (fun t => (t v).unop (some q)) h
  change (matcher v).evalFrom (some q) x=(matcher v).evalFrom (some q) y at he
  rw [←eval_isSome,←eval_isSome,he]

end PeriodicSummary

namespace PeriodicSummary

variable {Alphabet : Type uAlphabet3}

def lengthMod (n : ℕ) : FreeMonoid Alphabet →* Multiplicative (ZMod n) where
  toFun w := Multiplicative.ofAdd (w.toList.length:ZMod n)
  map_one' := by simp only [FreeMonoid.toList_one,List.length_nil,Nat.cast_zero]; rfl
  map_mul' x y := by
    change Multiplicative.ofAdd ((x.toList++y.toList).length:ZMod n)=_
    simp only [List.length_append,Nat.cast_add]
    rfl

lemma lengthMod_dvd {n : ℕ} {x y : List Alphabet}
    (h : lengthMod n (FreeMonoid.ofList x)=lengthMod n (FreeMonoid.ofList y)) :
    (n:ℤ) ∣ (y.length:ℤ)-x.length := by
  have he : (x.length:ZMod n)=(y.length:ZMod n) := congrArg Multiplicative.toAdd h
  have hz : ((x.length:ℤ):ZMod n)=((y.length:ℤ):ZMod n) := by simpa only [Int.cast_natCast] using he
  exact ((ZMod.intCast_eq_intCast_iff _ _ _).mp hz).dvd

end PeriodicSummary
namespace StreamSplice

open WordIntervals LocalMarkers

variable {Alphabet : Type uAlphabet4}

noncomputable def splice (f : ℤ → Alphabet) (N : ℤ) (x y : List Alphabet) (z : ℤ) : Alphabet :=
  if h : z<N then f z else if h' : z<N+y.length then
    y[(z-N).toNat]'(by omega) else f (z-((y.length:ℤ)-x.length))

lemma splice_left (f : ℤ → Alphabet) (N : ℤ) (x y : List Alphabet) {z : ℤ} (hz : z<N) :
    splice f N x y z=f z := by simp only [splice,dite_eq_left hz]

lemma splice_right (f : ℤ → Alphabet) (N : ℤ) (x y : List Alphabet) {z : ℤ}
    (hz : N+y.length≤z) : splice f N x y z=f (z-((y.length:ℤ)-x.length)) := by
  have hy : (0:ℤ)≤y.length := Int.natCast_nonneg _
  simp only [splice,dite_eq_right (show ¬z<N by omega),dite_eq_right (show ¬z<N+y.length by omega)]

lemma splice_middle (f : ℤ → Alphabet) (N : ℤ) (x y : List Alphabet) :
    Realizes y N (splice f N x y) := by
  intro i
  rw [splice,dite_eq_right (show ¬N+(i.val:ℤ)<N by omega),
    dite_eq_left (show N+(i.val:ℤ)<N+y.length by omega)]
  simp only [add_sub_cancel_left,Int.toNat_natCast]

lemma splice_realizes {f : ℤ → Alphabet} {a b x : List Alphabet}
    (hf : Realizes (a++x++b) 0 f) (y : List Alphabet) :
    Realizes (a++y++b) 0 (splice f a.length x y) := by
  have ha := hf.append_left.append_left
  have hb := hf.append_right
  apply Realizes.append
  · apply Realizes.append
    · intro i
      rw [splice_left f a.length x y (by omega)]
      exact ha i
    · simpa only [zero_add] using splice_middle f a.length x y
  · intro i
    rw [splice_right f a.length x y (by simp only [List.length_append,Nat.cast_add];omega)]
    have hh := hb i
    simp only [List.length_append,Nat.cast_add,zero_add] at hh ⊢
    convert hh using 2
    omega

structure Frame (f f' : ℤ → Alphabet) (N : ℤ) (x y : List Alphabet) : Prop where
  left : ∀ z, z<N → f' z=f z
  oldMiddle : Realizes x N f
  newMiddle : Realizes y N f'
  right : ∀ z, N+y.length≤z → f' z=f (z-((y.length:ℤ)-x.length))

lemma splice_frame {f : ℤ → Alphabet} {a b x : List Alphabet}
    (hf : Realizes (a++x++b) 0 f) (y : List Alphabet) :
    Frame f (splice f a.length x y) a.length x y := by
  refine ⟨fun z hz => splice_left f a.length x y hz,?_,splice_middle f a.length x y,
    fun z hz => splice_right f a.length x y hz⟩
  simpa only [zero_add] using hf.append_left.append_right

namespace Frame

variable {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet} (H : Frame f f' N x y)

include H

lemma agrees_left {s t : ℤ} (ht : t≤N) : AgreesOn f f' s t := by
  intro z _ hz
  exact (H.left z (hz.trans_le ht)).symm

lemma piece_left {s t : ℤ} (hst : s ≤ t) (ht : t≤N) : piece f s t=piece f' s t :=
  piece_congr hst (H.agrees_left ht)

lemma piece_right {s t : ℤ} (hs : N+x.length ≤ s) :
    piece f' (s+((y.length:ℤ)-x.length)) (t+((y.length:ℤ)-x.length))=piece f s t := by
  dsimp [piece]
  have hl : (t+((y.length:ℤ)-x.length)-(s+((y.length:ℤ)-x.length))).toNat=(t-s).toNat := by
    congr 1;ring
  rw [hl]
  apply List.ofFn_inj.mpr
  funext i
  rw [H.right _ (by omega)]
  congr 1
  ring

lemma product {M : Type uM3} [Monoid M] (T : FreeMonoid Alphabet →* M)
    (hT : T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y)) {s b : ℤ}
    (hs : s≤N) (hb : N+x.length≤b) :
    WordIntervals.product T f' s (b+((y.length:ℤ)-x.length))=WordIntervals.product T f s b := by
  have hx : N≤N+(x.length:ℤ) := by omega
  have hy : N≤N+(y.length:ℤ) := by omega
  have hb' : N+(y.length:ℤ)≤b+((y.length:ℤ)-x.length) := by omega
  unfold WordIntervals.product
  rw [piece_append f' hs (hy.trans hb'),piece_append f hs (hx.trans hb)]
  rw [piece_append f' hy hb',piece_append f hx hb]
  rw [H.piece_left hs (le_refl _),WordIntervals.realizes_piece H.oldMiddle,
    WordIntervals.realizes_piece H.newMiddle]
  have ht : piece f' (N+y.length) (b+((y.length:ℤ)-x.length))=piece f (N+x.length) b := by
    have hh := H.piece_right (s := N+x.length) (t := b) (le_refl _)
    simpa only [show N+(x.length:ℤ)+((y.length:ℤ)-x.length)=N+y.length by ring] using hh
  rw [ht]
  change T (FreeMonoid.ofList (piece f' s N)*(FreeMonoid.ofList y*
      FreeMonoid.ofList (piece f (N+x.length) b)))=
    T (FreeMonoid.ofList (piece f' s N)*(FreeMonoid.ofList x*
      FreeMonoid.ofList (piece f (N+x.length) b)))
  simp only [map_mul,hT]

end Frame
end StreamSplice

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace StreamSplice

open LocalMarkers WordIntervals PeriodicSummary

variable {Alphabet : Type uAlphabet}

lemma periodic_of_dvd {v : ℤ → Alphabet} {p δ : ℤ} (h : Function.Periodic v p)
    (hd : p∣δ) : Function.Periodic v δ := by
  obtain ⟨k,rfl⟩ := hd
  simpa only [Int.cast_id,mul_comm] using h.int_mul k

lemma periodic_pattern {p : ℕ} [NeZero p] {v : ℤ → Alphabet}
    (h : Function.Periodic v (p:ℤ)) (N : ℤ) (i : ℕ) :
    v (N+(((i:ZMod p).val:ℕ):ℤ))=v (N+i) := by
  have he := ZMod.val_intCast (n := p) (i:ℤ)
  simp only [Int.cast_natCast] at he
  rw [he]
  exact (periodic_remainder h N (N+i) |>.trans (by rw [add_sub_cancel_left])).symm

lemma fits_realizes {p : ℕ} [NeZero p] {v f : ℤ → Alphabet} {N : ℤ} {w : List Alphabet}
    (hp : Function.Periodic v (p:ℤ)) (hf : Realizes w N f) :
    Fits (fun q : ZMod p => v (N+q.val)) 0 w ↔ AgreesOn f v N (N+w.length) := by
  rw [fits_iff]
  simp only [zero_add]
  constructor
  · intro h z hz hz'
    let i : Fin w.length := ⟨(z-N).toNat,by omega⟩
    have hi : N+(i.val:ℤ)=z := by dsimp [i];omega
    rw [←hi,hf i,h i,periodic_pattern hp]
  · intro h i
    rw [←hf i,periodic_pattern hp]
    exact h _ (by omega) (by omega)

namespace Frame

variable {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet} (H : Frame f f' N x y)

include H

lemma symm : Frame f' f N y x := by
  refine ⟨fun z hz => (H.left z hz).symm,H.newMiddle,H.oldMiddle,?_⟩
  intro z hz
  have he := H.right (z-((x.length:ℤ)-y.length)) (by omega)
  rw [show z-((x.length:ℤ)-y.length)-((y.length:ℤ)-x.length)=z by ring] at he
  exact he.symm

include H

lemma agrees_periodic {p : ℕ} [NeZero p] {v : ℤ → Alphabet}
    (hp : Function.Periodic v (p:ℤ))
    (hd : (p:ℤ) ∣ (y.length:ℤ)-x.length)
    (hm : PeriodicSummary.transition (p := p) (FreeMonoid.ofList x)=
      PeriodicSummary.transition (FreeMonoid.ofList y)) {z q : ℤ}
    (hz : z≤N) (hq : N+x.length≤q) (ha : AgreesOn f v z q) :
    AgreesOn f' v z (q+((y.length:ℤ)-x.length)) := by
  have hmidx : AgreesOn f v N (N+x.length) := by
    intro t ht ht'
    exact ha t (hz.trans ht) (ht'.trans_le hq)
  have hmidx' := (fits_realizes hp H.oldMiddle).mpr hmidx
  have hmidy := (fits_realizes hp H.newMiddle).mp ((fits_congr hm _ 0).mp hmidx')
  have hδ := periodic_of_dvd hp hd
  intro t ht ht'
  by_cases htN : t<N
  · rw [H.left t htN]
    exact ha t ht (by omega)
  · by_cases htY : t<N+y.length
    · exact hmidy t (by omega) htY
    · rw [H.right t (by omega)]
      rw [ha _ (by omega) (by omega)]
      have he := hδ (t-((y.length:ℤ)-x.length))
      rw [sub_add_cancel] at he
      exact he.symm

lemma mismatch_periodic {p : ℕ} [NeZero p] {v : ℤ → Alphabet}
    (hp : Function.Periodic v (p:ℤ)) (hd : (p:ℤ) ∣ (y.length:ℤ)-x.length)
    {q : ℤ} (hq : N+x.length≤q) :
    f' (q+((y.length:ℤ)-x.length)) ≠ v (q+((y.length:ℤ)-x.length)) ↔ f q ≠ v q := by
  rw [H.right _ (by omega)]
  rw [add_sub_cancel_right,(periodic_of_dvd hp hd) q]

end Frame
end StreamSplice
namespace StreamSplice.Frame

open LocalMarkers WordIntervals EpisodeEnd

variable {Alphabet : Type uAlphabet2} {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet}
    (H : Frame f f' N x y)

lemma short_period_factorial {d K : ℕ} {v : ℤ → Alphabet} {z : ℤ}
    (hv : ShortContinuation d K f z v) : Function.Periodic v (d.factorial:ℤ) := by
  obtain ⟨p,hp,hpd,hper⟩ := hv.1
  apply periodic_of_dvd hper
  exact_mod_cast Nat.dvd_factorial hp hpd.le

include H

lemma endAt_none {d K : ℕ} {tail z b : ℤ}
    (hseed : z+(K:ℤ)≤N) (hb : N+x.length≤b-tail)
    (hd : (d.factorial:ℤ) ∣ (y.length:ℤ)-x.length)
    (hm : PeriodicSummary.transition (p := d.factorial) (FreeMonoid.ofList x)=
      PeriodicSummary.transition (FreeMonoid.ofList y))
    (he : EndAt d K tail f z none b) :
    EndAt d K tail f' z none (b+((y.length:ℤ)-x.length)) := by
  obtain ⟨v,hv,hmis⟩ := he
  have : NeZero d.factorial := ⟨Nat.factorial_ne_zero d⟩
  have hp := short_period_factorial hv
  refine ⟨v,(shortCont_congr (H.agrees_left hseed)).mp hv,?_,?_,?_⟩
  · omega
  · have hh := (H.mismatch_periodic hp hd hb).mpr hmis.2.1
    convert hh using 1 <;> congr 1 <;> ring
  · rw [show b+((y.length:ℤ)-x.length)-tail=(b-tail)+((y.length:ℤ)-x.length) by ring]
    exact H.agrees_periodic hp hd hm (by omega) hb hmis.2.2

lemma endAt {C : CanonicalEpisodes.Parameters Alphabet} {z b : ℤ}
    (hvis : C.Visible (-N) N z) (hstrict : z+(C.d:ℤ)+(C.B-1)*C.S<N)
    (hb : N+x.length≤b-C.tail)
    (hd : (C.d.factorial:ℤ) ∣ (y.length:ℤ)-x.length)
    (hm : PeriodicSummary.transition (p := C.d.factorial) (FreeMonoid.ofList x)=
      PeriodicSummary.transition (FreeMonoid.ofList y))
    (he : EndAt C.d C.K C.tail f z (C.small f z) b) :
    EndAt C.d C.K C.tail f' z (C.small f' z) (b+((y.length:ℤ)-x.length)) := by
  have hs := (C.searches_congr hvis (H.agrees_left (le_refl N))).1
  rw [←hs]
  cases hη : C.small f z with
  | some q =>
    have hq := (EndSearch.search_some C.B_pos C.S_nonneg).mp hη
    have hw := (EndSearch.width_bounds (x := q-z) (a := C.d) C.B_pos C.S_nonneg).2
    have hbd := (abs_le.mp (hq.1.2.trans hw)).2
    rw [hη] at he
    change b=q+C.tail at he
    omega
  | none =>
    rw [hη] at he
    exact H.endAt_none hvis.2.2.2 hb hd hm he

end StreamSplice.Frame

namespace CanonicalEpisodes.Parameters

open LocalMarkers WordIntervals EpisodeEnd StreamSplice

variable {Alphabet : Type uAlphabet3} (C : CanonicalEpisodes.Parameters Alphabet)

lemma exists_horizon (z : ℤ) : ∃ N : ℕ,
    C.Visible (-(N:ℤ)) N z ∧ z+(C.d:ℤ)+(C.B-1)*C.S<N := by
  obtain ⟨N,hN⟩ := exists_nat_gt (|z|+C.width+|C.rule.r|+C.K+1)
  have hz := abs_le.mp (le_refl |z|)
  have hr := abs_le.mp (le_refl |C.rule.r|)
  have hw := C.width_nonneg
  have hs := C.small_width_le
  refine ⟨N,⟨by omega,by omega,by omega,by omega⟩,by omega⟩

lemma visible_long {z : ℤ} {N : ℕ} (h : C.Visible (-(N:ℤ)) N z)
    {b : ℤ} (hb : (N:ℤ)≤b) (hl : 0≤z-C.width-C.rule.r) (hz : 0≤z) :
    C.Visible 0 b z := ⟨hl,h.2.1.trans hb,hz,h.2.2.2.trans hb⟩

lemma complete_regular [Finite Alphabet] (lag : ℤ) : (C.complete lag).IsRegular := by
  classical
  obtain ⟨N,hN,hs⟩ := C.exists_horizon (lag+C.offset)
  let : NeZero C.d.factorial := ⟨Nat.factorial_ne_zero C.d⟩
  let T := (PeriodicSummary.lengthMod C.d.factorial (Alphabet := Alphabet)).prod
    (PeriodicSummary.transition (p := C.d.factorial))
  let : Fintype Alphabet := Fintype.ofFinite Alphabet
  let : Fintype (Function.End (Option (ZMod C.d.factorial)))ᵐᵒᵖ :=
    Fintype.ofEquiv (Option (ZMod C.d.factorial) → Option (ZMod C.d.factorial))
      (Equiv.refl _ |>.trans MulOpposite.opEquiv)
  apply FiniteRecognition.regular_sandwich T N C.tail.toNat
  intro a b x y ha hb he
  have hh : C.tail.toNat=C.tail := Int.toNat_of_nonneg C.tail_pos.le
  have trans : ∀ (x y : List Alphabet), T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y) →
      a++x++b∈C.complete lag → a++y++b∈C.complete lag := by
    intro x y he hw
    obtain ⟨f,hf,hv,hend⟩ := hw
    let f' := splice f N x y
    have H : Frame f f' N x y := by simpa only [ha] using splice_frame hf y
    have hnew := H.endAt hN hs (by simp only [List.length_append,Nat.cast_add,ha,hb];omega)
      (PeriodicSummary.lengthMod_dvd (congrArg Prod.fst he)) (congrArg Prod.snd he) hend
    refine ⟨f',?_,?_,?_⟩
    · simpa only [f',ha] using splice_realizes hf y
    · exact C.visible_long hN (by simp only [List.length_append,Nat.cast_add,ha,hb];omega)
        hv.1 hv.2.2.1
    · convert hnew using 1
      simp only [List.length_append,Nat.cast_add]
      omega
  exact ⟨trans x y he,trans y x he.symm⟩

end CanonicalEpisodes.Parameters
namespace EpisodeAlgebra

variable {Alphabet : Type uAlphabet4}

def remainder (E : Language Alphabet) : Language Alphabet :=
  {w | ∀ e∈E, ¬ e <+: w}

lemma remainder_eq (E : Language Alphabet) : remainder E=(E*⊤)ᶜ := by
  ext w
  constructor
  · intro h hw
    obtain ⟨e,he,v,_,rfl⟩ := hw
    exact h e he ⟨v,rfl⟩
  · intro h e he ⟨v,hv⟩
    exact h ⟨e,he,v,Set.mem_univ _,hv⟩

lemma factor_remainder {E : Language Alphabet} (hnil : []∉E) (w : List Alphabet) :
    ∃ es r, AllIn E es ∧ r∈remainder E ∧ w=es.flatten++r := by
  classical
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases h : w∈remainder E
    · exact ⟨[],w,by simp [AllIn],h,by simp⟩
    · change ¬∀ e∈E, ¬ e <+: w at h
      push Not at h
      obtain ⟨e,he,hp⟩ := h
      obtain ⟨v,rfl⟩ := hp
      have hpos : 0<e.length := by
        by_contra h
        exact hnil ((List.length_eq_zero_iff.mp (by omega : e.length=0)) ▸ he)
      obtain ⟨es,r,hes,hr,hv⟩ := ih v.length (by simp only [List.length_append] at hlen;omega) v rfl
      refine ⟨e::es,r,fun a ha => ?_,hr,?_⟩
      · rcases List.mem_cons.mp ha with rfl|ha
        · exact he
        · exact hes a ha
      · simp only [List.flatten_cons,List.append_assoc,hv]

end EpisodeAlgebra

namespace EpisodeEnd

open LocalMarkers
variable {Alphabet : Type uAlphabet5}

lemma firstMismatch_of_disagrees {d K : ℕ} {f v : ℤ → Alphabet} {z q : ℤ}
    (hv : ShortContinuation d K f z v) (hq : z≤q) (hm : f q≠v q) :
    ∃ q', q'≤q ∧ FirstMismatch f v z K q' := by
  rcases MarkerSearch.search_some_or_none {x | f x≠v x} z q with hn|⟨q',hq',hle⟩
  · exact False.elim (hn q hm hq le_rfl)
  · refine ⟨q',hle,?_,hq'.1,?_⟩
    · by_contra h
      exact hq'.1 (hv.2 q' hq'.2.1 (by omega))
    · intro x hx hx'
      by_contra h
      exact (not_le_of_gt hx') (hq'.2.2 x h hx)

end EpisodeEnd

namespace CanonicalEpisodes.Parameters

open LocalMarkers WordIntervals EpisodeEnd EpisodeAlgebra

variable {Alphabet : Type uAlphabet6} (C : CanonicalEpisodes.Parameters Alphabet)

lemma complete_prefix {lag b : ℤ} {w : List Alphabet} {f : ℤ → Alphabet}
    (hf : Realizes w 0 f) (hv : C.Visible 0 b (lag+C.offset))
    (he : EndAt C.d C.K C.tail f (lag+C.offset) (C.small f (lag+C.offset)) b)
    (hb : b≤w.length) : ∃ e∈C.complete lag, e<+:w := by
  have hb0 : 0≤b := hv.2.2.1.trans (le_trans (by omega) hv.2.2.2)
  let e := w.take b.toNat
  have hl : (e.length:ℤ)=b := by
    simp only [e,List.length_take]
    omega
  refine ⟨e,⟨f,hf.prefix (List.take_prefix _ _),?_,?_⟩,List.take_prefix _ _⟩
  · simpa only [hl] using hv
  · simpa only [hl] using he

lemma remainder_middle [Nonempty Alphabet] (lag : ℤ)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EndAt C.d C.K C.tail f (lag+C.offset) (C.small f (lag+C.offset)) b →
      C.Visible 0 b (lag+C.offset)) :
    ∃ N : ℕ, ∀ w∈remainder (C.complete lag),
      w.length≤N+C.tail.toNat ∨ ∃ (f v : ℤ → Alphabet) (p : ℕ),
        Realizes w 0 f ∧ N+C.tail.toNat≤w.length ∧ 0<p ∧ p≤C.d ∧
          Function.Periodic v (p:ℤ) ∧ AgreesOn f v N (w.length-C.tail.toNat) := by
  obtain ⟨N,hN,hs⟩ := C.exists_horizon (lag+C.offset)
  refine ⟨N,?_⟩
  intro w hw
  by_cases hlen : w.length≤N+C.tail.toNat
  · exact Or.inl hlen
  · right
    obtain ⟨f,hf⟩ := realizes_exists w 0
    have htail : (C.tail.toNat:ℤ)=C.tail := Int.toNat_of_nonneg C.tail_pos.le
    have hnone : C.small f (lag+C.offset)=none := by
      cases hη : C.small f (lag+C.offset) with
      | none => rfl
      | some q =>
        have hq := ((EndSearch.search_some C.B_pos C.S_nonneg).mp hη).1.2
        have hwidth := (EndSearch.width_bounds (x := q-(lag+C.offset)) (a := C.d)
          C.B_pos C.S_nonneg).2
        have hright := (abs_le.mp (hq.trans hwidth)).2
        have he : EndAt C.d C.K C.tail f (lag+C.offset)
            (C.small f (lag+C.offset)) (q+C.tail) := by rw [hη];rfl
        obtain ⟨e,he,hp⟩ := C.complete_prefix hf (hvisible f _ he) he (by omega)
        exact False.elim (hw e he hp)
    obtain ⟨v,hv⟩ := EndSearch.absent_continuation C.rule
      (by nlinarith [C.seed_long]) C.B_pos C.S_nonneg hnone
    obtain ⟨p,hp,hpd,hper⟩ := hv.1
    refine ⟨f,v,p,hf,by omega,hp,hpd.le,hper,?_⟩
    intro q hq hq'
    by_contra hm
    have hzq : lag+C.offset≤q := by have := hN.2.2.2;omega
    obtain ⟨q',hle,hm'⟩ := firstMismatch_of_disagrees hv hzq hm
    have he : EndAt C.d C.K C.tail f (lag+C.offset)
        (C.small f (lag+C.offset)) (q'+C.tail) := by
      rw [hnone]
      exact ⟨v,hv,by simpa only [add_sub_cancel_right] using hm'⟩
    obtain ⟨e,he,hpre⟩ := C.complete_prefix hf (hvisible f _ he) he (by omega)
    exact hw e he hpre

lemma remainder_regular [Finite Alphabet] (lag : ℤ) :
    (remainder (C.complete lag)).IsRegular := by
  rw [remainder_eq]
  apply Language.IsRegular.compl
  apply FiniteRecognition.regular_mul (C.complete_regular lag)
  have ht : (⊤ : Language Alphabet)=(0 : Language Alphabet)ᶜ := by
    ext w
    change True ↔ ¬False
    simp
  rw [ht]
  exact Language.IsRegular.compl (FiniteRecognition.regular_finite Set.finite_empty)

lemma remainder_height [Finite Alphabet] [Nonempty Alphabet] (lag : ℤ)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EndAt C.d C.K C.tail f (lag+C.offset) (C.small f (lag+C.offset)) b →
      C.Visible 0 b (lag+C.offset)) :
    HasHeightAtMost (remainder (C.complete lag)) 1 := by
  obtain ⟨N,hN⟩ := C.remainder_middle lag hvisible
  exact PeriodicTemplates.regular_middle_height _ (C.remainder_regular lag)
    (N+C.tail.toNat) N C.tail.toNat C.d hN

end CanonicalEpisodes.Parameters
namespace ExceptionalOrigins.Parameters

open LocalMarkers
variable {Alphabet : Type uAlphabet7} {J : Type uJ} {C : Type uC} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma residue_eq_of_dvd {x y : ℤ} (h : (A.B:ℤ)∣y-x) : A.residue x=A.residue y := by
  apply Fin.ext
  have he : x%A.B=y%A.B := Int.modEq_iff_dvd.mpr h
  exact congrArg Int.toNat he

lemma exists_horizon [Fintype J] (D : ℕ) : ∃ N : ℕ, D<N ∧
    ∀ (t : ℤ), |t|≤(D:ℤ) → ∀ Q, A.Visible (-(N:ℤ)) N t Q := by
  let U : ℤ := (SourceSchedule.absoluteBound A.offset:ℤ)
  let H : ℤ := (SourceSchedule.absoluteBound A.H:ℤ)
  obtain ⟨N,hN⟩ := exists_nat_gt ((D:ℤ)+|A.endRule.offset|+A.endRule.width+
    |A.endRule.rule.r|+A.endRule.K+|A.w|+U+H+|A.w₀|+|A.ext|+|A.innerRule.r|+1)
  have hwidth := A.endRule.width_nonneg
  have hU : 0≤U := by dsimp [U];positivity
  have hH : 0≤H := by dsimp [H];positivity
  have hoff := abs_le.mp (le_refl |A.endRule.offset|)
  have hr := abs_le.mp (le_refl |A.endRule.rule.r|)
  have hir := abs_le.mp (le_refl |A.innerRule.r|)
  have hw := abs_le.mp (le_refl |A.w|)
  have hw₀ := abs_le.mp (le_refl |A.w₀|)
  have hext := abs_le.mp (le_refl |A.ext|)
  refine ⟨N,by omega,?_⟩
  intro t ht Q
  have ht' := abs_le.mp ht
  refine ⟨⟨by omega,by omega,by omega,by omega⟩,?_,?_⟩
  · intro v _ hv
    have hv' := abs_le.mp hv
    constructor <;> omega
  · intro j
    have hj : |A.offset j|≤U := SourceSchedule.abs_le_absoluteBound A.offset j
    have hH' : |A.H (A.residue (Q-t))|≤H := SourceSchedule.abs_le_absoluteBound A.H _
    have hj' := abs_le.mp hj
    have hH'' := abs_le.mp hH'
    have hmax : max A.ext A.w₀≤|A.ext|+|A.w₀| := by apply max_le <;> omega
    constructor <;> omega

lemma Failed_phase_congr {s b t Q Q' : ℤ} {f g : ℤ → Alphabet}
    (hw₀ : 0≤A.w₀) (hv : A.Visible s b t Q) (he : AgreesOn f g s b)
    (hφ : A.φ (Q-t)=A.φ (Q'-t)) (hu : A.residue (Q-t)=A.residue (Q'-t)) :
    A.Failed f t Q ↔ A.Failed g t Q' := by
  rw [A.Failed_congr hw₀ hv he]
  simp only [Failed,Star,hφ,hu]

end ExceptionalOrigins.Parameters

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace StreamSplice.Frame

open LocalMarkers WordIntervals
variable {Alphabet : Type uAlphabet} {J : Type uJ} {C : Type uC} {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet}
    (H : Frame f f' N x y) (A : ExceptionalOrigins.Parameters Alphabet J C)

include H

lemma anchor_phase {t b : ℤ} (hv : A.endRule.Visible (-N) N (t+A.endRule.offset))
    (hd : (A.B:ℤ) ∣ (y.length:ℤ)-x.length)
    (hφ : A.φ ((y.length:ℤ)-x.length)=0) :
    A.residue (A.anchor f (b-A.endRule.tail) t-t)=
      A.residue (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) t-t) ∧
    A.φ (A.anchor f (b-A.endRule.tail) t-t)=
      A.φ (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) t-t) := by
  have hs := (A.endRule.searches_congr hv (H.agrees_left (le_refl N))).2
  unfold ExceptionalOrigins.Parameters.anchor
  rw [←hs]
  cases hζ : A.endRule.large f (t+A.endRule.offset) with
  | some q => simp only [Option.getD_some,and_self]
  | none =>
    simp only [Option.getD_none]
    constructor
    · apply A.residue_eq_of_dvd
      convert hd using 1
      ring
    · rw [show b+((y.length:ℤ)-x.length)-A.endRule.tail-t=
        (b-A.endRule.tail-t)+((y.length:ℤ)-x.length) by ring,map_add,hφ,add_zero]

lemma failed {t b : ℤ} (hw₀ : 0≤A.w₀)
    (hv : A.Visible (-N) N t (A.anchor f (b-A.endRule.tail) t))
    (hd : (A.B:ℤ) ∣ (y.length:ℤ)-x.length)
    (hφ : A.φ ((y.length:ℤ)-x.length)=0) :
    A.Failed f t (A.anchor f (b-A.endRule.tail) t) ↔
      A.Failed f' t (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) t) := by
  have hphase := H.anchor_phase A (b := b) hv.base hd hφ
  exact A.Failed_phase_congr hw₀ hv (H.agrees_left (le_refl N)) hphase.2 hphase.1

end StreamSplice.Frame

namespace ExceptionalOrigins.Parameters

open LocalMarkers WordIntervals StreamSplice
variable {Alphabet : Type uAlphabet2} {J : Type uJ2} {C : Type uC2} (A : ExceptionalOrigins.Parameters Alphabet J C)

def failedLanguage (t : ℤ) : Language Alphabet := {w | ∃ f : ℤ → Alphabet,
  Realizes w 0 f ∧ A.Failed f t (A.anchor f (w.length-A.endRule.tail) t)}

lemma failed_regular [Finite Alphabet] [Fintype J] (n : ℕ) (hn : 0<n)
    (hφ : A.φ (n:ℤ)=0) (hw₀ : 0≤A.w₀) (t : ℤ) : (A.failedLanguage t).IsRegular := by
  classical
  obtain ⟨N,_,hN⟩ := A.exists_horizon t.natAbs
  have ht : |t|≤(t.natAbs:ℤ) := by rw [Int.natCast_natAbs]
  let : NeZero (A.B*n) := ⟨Nat.ne_of_gt (Nat.mul_pos A.B_pos hn)⟩
  let T := PeriodicSummary.lengthMod (Alphabet := Alphabet) (A.B*n)
  apply FiniteRecognition.regular_sandwich T N 0
  intro a b x y ha hb he
  have hbnil : b=[] := List.length_eq_zero_iff.mp hb
  subst b
  have trans : ∀ x y : List Alphabet, T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y) →
      a++x++[]∈A.failedLanguage t → a++y++[]∈A.failedLanguage t := by
    intro x y he ⟨f,hf,hfail⟩
    let f' := splice f N x y
    have H : Frame f f' N x y := by simpa only [ha] using splice_frame hf y
    have hdiv := PeriodicSummary.lengthMod_dvd he
    have hB : (A.B:ℤ)∣(y.length:ℤ)-x.length :=
      (show (A.B:ℤ)∣(A.B*n:ℕ) by exact_mod_cast dvd_mul_right A.B n).trans hdiv
    have hn' : (n:ℤ)∣(y.length:ℤ)-x.length :=
      (show (n:ℤ)∣(A.B*n:ℕ) by exact_mod_cast dvd_mul_left n A.B).trans hdiv
    have hδ : A.φ ((y.length:ℤ)-x.length)=0 := by
      obtain ⟨k,hk⟩ := hn'
      rw [hk,mul_comm,←Int.zsmul_eq_mul,map_zsmul,hφ,smul_zero]
    have hh := (H.failed A hw₀ (hN t ht _) hB hδ).mp hfail
    refine ⟨f',by simpa only [ha] using splice_realizes hf y,?_⟩
    have hl : ((a++y++[]).length:ℤ)=((a++x++[]).length:ℤ)+((y.length:ℤ)-x.length) := by
      simp only [List.length_append,List.length_nil,Nat.cast_add,Nat.cast_zero]
      omega
    rw [hl]
    exact hh
  exact ⟨trans x y he,trans y x he.symm⟩

end ExceptionalOrigins.Parameters
namespace CanonicalEpisodes.Parameters

open LocalMarkers
variable {Alphabet : Type uAlphabet3} (C : CanonicalEpisodes.Parameters Alphabet)

lemma exists_uniform_horizon (D : ℕ) : ∃ N : ℕ, D<N ∧ ∀ (t : ℤ), |t|≤(D:ℤ) →
    C.Visible (-(N:ℤ)) N (t+C.offset) ∧
      t+C.offset+(C.d:ℤ)+(C.B-1)*C.S<N := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((D:ℤ)+|C.offset|+C.width+|C.rule.r|+C.K+1)
  have ho := abs_le.mp (le_refl |C.offset|)
  have hr := abs_le.mp (le_refl |C.rule.r|)
  have hw := C.width_nonneg
  have hs := C.small_width_le
  refine ⟨N,by omega,?_⟩
  intro t ht
  have ht' := abs_le.mp ht
  exact ⟨⟨by omega,by omega,by omega,by omega⟩,by omega⟩

end CanonicalEpisodes.Parameters

namespace ExceptionalOrigins.Parameters

open LocalMarkers
variable {Alphabet : Type uAlphabet4} {J : Type uJ3} {C : Type uC3} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma exists_inner_horizon [Fintype J] (D : ℕ) : ∃ N : ℕ, D<N ∧
    ∀ (t : ℤ), |t|≤(D:ℤ) → ∀ j u, A.InnerVisible (-(N:ℤ)) N t j u := by
  let U : ℤ := (SourceSchedule.absoluteBound A.offset:ℤ)
  let H : ℤ := (SourceSchedule.absoluteBound A.H:ℤ)
  obtain ⟨N,hN⟩ := exists_nat_gt ((D:ℤ)+U+H+|A.innerRule.r|+1)
  have hU : 0≤U := by dsimp [U];positivity
  have hH : 0≤H := by dsimp [H];positivity
  have hr := abs_le.mp (le_refl |A.innerRule.r|)
  refine ⟨N,by omega,?_⟩
  intro t ht j u
  have ht' := abs_le.mp ht
  have hj' := abs_le.mp (SourceSchedule.abs_le_absoluteBound A.offset j)
  have hu' := abs_le.mp (SourceSchedule.abs_le_absoluteBound A.H u)
  change -↑N≤t+A.offset j-A.innerRule.r ∧ t+A.offset j+A.H u+A.innerRule.r≤N
  dsimp [U,H] at hN
  constructor <;> omega

lemma InnerVisible.mono {s b s' b' t : ℤ} {j : J} {u : Fin A.B}
    (hv : A.InnerVisible s b t j u) (hs : s' ≤ s) (hb : b ≤ b') :
    A.InnerVisible s' b' t j u := ⟨hs.trans hv.1,hv.2.trans hb⟩

lemma Visible.from_bounds {s b s' N b' t Q Q' : ℤ}
    (hv : A.Visible s b t Q) (hN : A.Visible s' N t Q')
    (hb : N ≤ b') : A.Visible s b' t Q' := by
  refine ⟨⟨hv.base.1,hN.base.2.1.trans hb,hv.base.2.2.1,hN.base.2.2.2.trans hb⟩,?_,?_⟩
  · intro v hv' hw
    exact ⟨(hv.ends v hv' hw).1,(hN.ends v hv' hw).2.trans hb⟩
  · intro j
    exact ⟨(hv.inner j).1,(hN.inner j).2.trans hb⟩

end ExceptionalOrigins.Parameters

namespace StreamSplice.Frame

open LocalMarkers WordIntervals BoundarySnapshot
variable {Alphabet : Type uAlphabet5} {M : Type uM} [Monoid M] {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet}
    (H : Frame f f' N x y) (T : FreeMonoid Alphabet →* M)

include H

lemma factors {g : ℕ} {s b : ℤ} (hb : N+x.length≤b)
    (hT : T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y))
    (search : Fin (g+1) → Option ℤ) (hsearch : ∀ i q, search i=some q → q≤N) :
    BoundarySnapshot.factors T f' s (b+((y.length:ℤ)-x.length)) search=
      BoundarySnapshot.factors T f s b search := by
  classical
  have hbN : N≤b := by omega
  have hbN' : N≤b+((y.length:ℤ)-x.length) := by omega
  have hp : Present search s b ↔ Present search s (b+((y.length:ℤ)-x.length)) := by
    constructor
    · rintro ⟨p,hp,hm,hs,_⟩
      exact ⟨p,hp,hm,hs,(hsearch _ _ (hp _)).trans hbN'⟩
    · rintro ⟨p,hp,hm,hs,_⟩
      exact ⟨p,hp,hm,hs,(hsearch _ _ (hp _)).trans hbN⟩
  by_cases hpres : Present search s b
  · obtain ⟨p,hp',hm,hs',hb'⟩ := hpres
    rw [factors_present T f hp' hm hs' hb',
      factors_present T f' hp' hm hs' ((hsearch _ _ (hp' _)).trans hbN')]
    congr 2
    · exact (product_congr T hs' (H.agrees_left (hsearch _ _ (hp' _)))).symm
    · funext i
      exact (product_congr T (hm (Fin.castSucc_le_succ i))
        (H.agrees_left (hsearch _ _ (hp' _)))).symm
    · exact H.product T hT (hsearch _ _ (hp' _)) hb
  · simp only [BoundarySnapshot.factors,dite_eq_right hpres,dite_eq_right (mt hp.mpr hpres)]

lemma later {g : ℕ} {s b : ℤ} (hs : s≤N) (hb : N+x.length≤b)
    (hT : T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y))
    (search : Fin (g+1) → Option ℤ) (hsearch : ∀ i q, search i=some q → q≤N) :
    BoundarySnapshot.later T f' s (b+((y.length:ℤ)-x.length)) search=
      BoundarySnapshot.later T f s b search := by
  apply BoundarySnapshot.later_ext
  · exact H.product T hT hs hb
  · exact H.factors T hb hT search hsearch

end StreamSplice.Frame

namespace StreamSplice.Frame

open LocalMarkers WordIntervals
variable {Alphabet : Type uAlphabet6} {J : Type uJ4} {C : Type uC4} {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet}
    (H : Frame f f' N x y)

include H

lemma guard (E : CanonicalEpisodes.Parameters Alphabet) {O : Finset ℤ} {r k b : ℤ}
    (hN : ∀ t∈O, E.Visible (-N) N (t+E.offset) ∧
      t+E.offset+(E.d:ℤ)+(E.B-1)*E.S<N)
    (hb : N+x.length≤b-E.tail)
    (hd : (E.d.factorial:ℤ)∣(y.length:ℤ)-x.length)
    (hm : PeriodicSummary.transition (p := E.d.factorial) (FreeMonoid.ofList x)=
      PeriodicSummary.transition (FreeMonoid.ofList y))
    (hg : E.Guard O r k b f) : E.Guard O r k (b+((y.length:ℤ)-x.length)) f' := by
  have hbN : N≤b+((y.length:ℤ)-x.length) := by have := E.tail_pos;omega
  have hs := fun t ht => E.searches_congr (hN t ht).1 (H.agrees_left (le_refl N))
  refine ⟨hg.1,?_,?_,H.endAt (hN r hg.1).1 (hN r hg.1).2 hb hd hm hg.2.2.2⟩
  · intro t ht
    have hv := hg.2.1 t ht
    have hv' := (hN t ht).1
    exact ⟨hv.1,hv'.2.1.trans hbN,hv.2.2.1,hv'.2.2.2.trans hbN⟩
  · intro t ht
    rw [←(hs t ht).1,←(hs r hg.1).1,←(hs t ht).2,←(hs r hg.1).2]
    exact hg.2.2.1 t ht

lemma anchor_relative_phase (A : ExceptionalOrigins.Parameters Alphabet J C) {t b r : ℤ}
    (hv : A.endRule.Visible (-N) N (t+A.endRule.offset))
    (hd : (A.B:ℤ)∣(y.length:ℤ)-x.length)
    (hφ : A.φ ((y.length:ℤ)-x.length)=0) :
    A.residue (A.anchor f (b-A.endRule.tail) t-r)=
      A.residue (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) t-r) ∧
    A.φ (A.anchor f (b-A.endRule.tail) t-r)=
      A.φ (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) t-r) := by
  have hs := (A.endRule.searches_congr hv (H.agrees_left (le_refl N))).2
  unfold ExceptionalOrigins.Parameters.anchor
  rw [←hs]
  cases A.endRule.large f (t+A.endRule.offset) with
  | some q => simp only [Option.getD_some,and_self]
  | none =>
    simp only [Option.getD_none]
    constructor
    · apply A.residue_eq_of_dvd
      convert hd using 1
      ring
    · rw [show b+((y.length:ℤ)-x.length)-A.endRule.tail-r=
        (b-A.endRule.tail-r)+((y.length:ℤ)-x.length) by ring,map_add,hφ,add_zero]

lemma decoder (A : ExceptionalOrigins.Parameters Alphabet J C) {P : Type uP}
    {τ : P → ℤ} {reference decoded : P} {k b : ℤ} (hw₀ : 0≤A.w₀)
    (hN : ∀ t, A.Visible (-N) N (τ t) (A.anchor f (b-A.endRule.tail) (τ t)))
    (hN' : ∀ t Q, A.Visible (-N) N (τ t) Q)
    (hstrict : ∀ t, τ t+A.endRule.offset+(A.endRule.d:ℤ)+
      (A.endRule.B-1)*A.endRule.S<N)
    (hb : N+x.length≤b-A.endRule.tail)
    (hd : (A.endRule.d.factorial:ℤ)∣(y.length:ℤ)-x.length)
    (hm : PeriodicSummary.transition (p := A.endRule.d.factorial) (FreeMonoid.ofList x)=
      PeriodicSummary.transition (FreeMonoid.ofList y))
    (hB : (A.B:ℤ)∣(y.length:ℤ)-x.length) (hφ : A.φ ((y.length:ℤ)-x.length)=0)
    (ht : SuffixDecoder.Test A τ reference k b f decoded) :
    SuffixDecoder.Test A τ reference k (b+((y.length:ℤ)-x.length)) f' decoded := by
  have hbN : N≤b+((y.length:ℤ)-x.length) := by have := A.endRule.tail_pos;omega
  have hs := fun t => A.endRule.searches_congr (hN t).base (H.agrees_left (le_refl N))
  have hfail := fun t => H.failed A hw₀ (hN t) hB hφ
  refine ⟨?_,?_,⟨(hfail decoded).mp ht.unique.1,?_⟩,?_⟩
  · intro t
    exact ExceptionalOrigins.Parameters.Visible.from_bounds A (ht.visible t) (hN' t _) hbN
  · intro habsent
    have ha : ∃ i, A.endRule.large f (τ i+A.endRule.offset)=none := by
      obtain ⟨i,hi⟩ := habsent
      exact ⟨i,(hs i).2.trans hi⟩
    have hg := ht.reference_guard ha
    refine ⟨fun i => (hs i).1.symm.trans (hg.1 i),?_⟩
    exact H.endAt (hN reference).base (hstrict reference) hb hd hm hg.2
  · intro i hi
    exact ht.unique.2 i ((hfail i).mpr hi)
  · exact H.endAt (hN decoded).base (hstrict decoded) hb hd hm ht.final_guard

end StreamSplice.Frame
namespace StreamSplice

open LocalMarkers WordIntervals
variable {Alphabet : Type uAlphabet7} {M : Type uM2} {J : Type uJ5} {C : Type uC5} [Monoid M]

def wordTest (R : (ℤ → Alphabet) → ℤ → Prop) : Language Alphabet :=
  {w | ∃ f, Realizes w 0 f ∧ R f w.length}

structure SummaryEq (A : ExceptionalOrigins.Parameters Alphabet J C)
    (T : FreeMonoid Alphabet →* M) (x y : List Alphabet) : Prop where
  monoid_eq : T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y)
  residue_dvd : (A.B:ℤ)∣(y.length:ℤ)-x.length
  period_dvd : (A.endRule.d.factorial:ℤ)∣(y.length:ℤ)-x.length
  matcher_eq : PeriodicSummary.transition (p := A.endRule.d.factorial) (FreeMonoid.ofList x)=
    PeriodicSummary.transition (FreeMonoid.ofList y)
  clock_eq : A.φ ((y.length:ℤ)-x.length)=0

lemma clock_eq_of_dvd (φ : ℤ →+ (C → RobustClock.Circle)) {n : ℕ}
    (hφ : φ (n:ℤ)=0) {δ : ℤ} (hδ : (n:ℤ)∣δ) : φ δ=0 := by
  obtain ⟨k,rfl⟩ := hδ
  rw [mul_comm,←Int.zsmul_eq_mul,map_zsmul,hφ,smul_zero]

lemma wordTest_regular [Finite Alphabet] [Finite M]
    (A : ExceptionalOrigins.Parameters Alphabet J C) (T : FreeMonoid Alphabet →* M)
    (n : ℕ) (hn : 0<n) (hφ : A.φ (n:ℤ)=0) (N : ℕ)
    (R : (ℤ → Alphabet) → ℤ → Prop)
    (hc : ∀ (f f' : ℤ → Alphabet) (b : ℤ) (x y : List Alphabet),
      Frame f f' N x y → (N:ℤ)+x.length≤b-A.endRule.tail →
      SummaryEq A T x y → R f b → R f' (b+((y.length:ℤ)-x.length))) :
    (wordTest R).IsRegular := by
  classical
  let p := A.endRule.d.factorial
  let m := A.B*n*p
  have hp : 0<p := Nat.factorial_pos _
  have hm : 0 < m := Nat.mul_pos (Nat.mul_pos A.B_pos hn) hp
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let : Fintype Alphabet := Fintype.ofFinite Alphabet
  let : Fintype M := Fintype.ofFinite M
  let : Fintype ((Function.End (Option (ZMod p)))ᵐᵒᵖ) :=
    Fintype.ofEquiv (Option (ZMod p) → Option (ZMod p))
      (Equiv.refl _ |>.trans MulOpposite.opEquiv)
  let U := (T.prod (PeriodicSummary.lengthMod m)).prod (PeriodicSummary.transition (p := p))
  apply FiniteRecognition.regular_sandwich U N A.endRule.tail.toNat
  intro a b x y ha hb he
  have ht : (A.endRule.tail.toNat:ℤ)=A.endRule.tail := Int.toNat_of_nonneg A.endRule.tail_pos.le
  have trans : ∀ (x y : List Alphabet), U (FreeMonoid.ofList x)=U (FreeMonoid.ofList y) →
      a++x++b∈wordTest R → a++y++b∈wordTest R := by
    intro x y he ⟨f,hf,hw⟩
    let f' := splice f N x y
    have H : Frame f f' N x y := by simpa only [ha] using splice_frame hf y
    have hdiv := PeriodicSummary.lengthMod_dvd (congrArg (Prod.snd ∘ Prod.fst) he)
    have hB : (A.B:ℤ)∣(y.length:ℤ)-x.length :=
      (show (A.B:ℤ)∣(m:ℤ) by exact_mod_cast dvd_mul_of_dvd_left (dvd_mul_right A.B n) p).trans hdiv
    have hn' : (n:ℤ)∣(y.length:ℤ)-x.length :=
      (show (n:ℤ)∣(m:ℤ) by exact_mod_cast dvd_mul_of_dvd_left (dvd_mul_left n A.B) p).trans hdiv
    have hp' : (p:ℤ)∣(y.length:ℤ)-x.length :=
      (show (p:ℤ)∣(m:ℤ) by exact_mod_cast dvd_mul_left p (A.B*n)).trans hdiv
    have hh := hc f f' _ x y H (by simp only [List.length_append,Nat.cast_add,ha,hb];omega)
      ⟨congrArg (Prod.fst ∘ Prod.fst) he,hB,hp',congrArg Prod.snd he,clock_eq_of_dvd A.φ hφ hn'⟩ hw
    refine ⟨f',by simpa only [ha] using splice_realizes hf y,?_⟩
    have hl : ((a++y++b).length:ℤ)=((a++x++b).length:ℤ)+((y.length:ℤ)-x.length) := by
      simp only [List.length_append,Nat.cast_add]
      omega
    rw [hl]
    exact hh
  exact ⟨trans x y he,trans y x he.symm⟩

end StreamSplice

namespace CanonicalEpisodes.Parameters

open LocalMarkers WordIntervals EpisodeEnd
variable {Alphabet : Type uAlphabet8} (C : CanonicalEpisodes.Parameters Alphabet)

lemma ending_middle (L : Language Alphabet) (D : ℕ)
    (hL : ∀ w∈L, ∃ f t, Realizes w 0 f ∧ |t|≤(D:ℤ) ∧
      EndAt C.d C.K C.tail f (t+C.offset) (C.small f (t+C.offset)) w.length) :
    ∃ N : ℕ, ∀ w∈L, w.length≤N+C.tail.toNat ∨ ∃ (f v : ℤ → Alphabet) (p : ℕ),
      Realizes w 0 f ∧ N+C.tail.toNat≤w.length ∧ 0<p ∧ p≤C.d ∧
        Function.Periodic v (p:ℤ) ∧ AgreesOn f v N (w.length-C.tail.toNat) := by
  obtain ⟨N,_,hN⟩ := C.exists_uniform_horizon D
  refine ⟨N,?_⟩
  intro w hw
  by_cases hl : w.length≤N+C.tail.toNat
  · exact Or.inl hl
  · right
    obtain ⟨f,t,hf,ht,he⟩ := hL w hw
    have htail : (C.tail.toNat:ℤ)=C.tail := Int.toNat_of_nonneg C.tail_pos.le
    cases hη : C.small f (t+C.offset) with
    | some q =>
      have hq := ((EndSearch.search_some C.B_pos C.S_nonneg).mp hη).1.2
      have hwidth := (EndSearch.width_bounds (x := q-(t+C.offset)) (a := C.d)
        C.B_pos C.S_nonneg).2
      have hright := (abs_le.mp (hq.trans hwidth)).2
      rw [hη] at he
      change (w.length:ℤ)=q+C.tail at he
      have hs := (hN t ht).2
      omega
    | none =>
      rw [hη] at he
      obtain ⟨v,hv,hmis⟩ := he
      obtain ⟨p,hp,hpd,hper⟩ := hv.1
      refine ⟨f,v,p,hf,by omega,hp,hpd.le,hper,?_⟩
      intro z hz hz'
      have hseed := (hN t ht).1.2.2.2
      exact hmis.2.2 z (by omega) (by omega)

lemma ending_height [Finite Alphabet] (L : Language Alphabet) (hreg : L.IsRegular) (D : ℕ)
    (hL : ∀ w∈L, ∃ f t, Realizes w 0 f ∧ |t|≤(D:ℤ) ∧
      EndAt C.d C.K C.tail f (t+C.offset) (C.small f (t+C.offset)) w.length) :
    HasHeightAtMost L 1 := by
  obtain ⟨N,hN⟩ := C.ending_middle L D hL
  exact PeriodicTemplates.regular_middle_height L hreg
    (N+C.tail.toNat) N C.tail.toNat C.d hN

end CanonicalEpisodes.Parameters
namespace ExceptionalOrigins.Parameters

open LocalMarkers
variable {Alphabet : Type uAlphabet9} {J : Type uJ6} {C : Type uC6} (A : ExceptionalOrigins.Parameters Alphabet J C)

structure Inspection (D N : ℕ) : Prop where
  contains : D<N
  full : ∀ (t : ℤ), |t|≤(D:ℤ) → ∀ Q, A.Visible (-(N:ℤ)) N t Q
  inner : ∀ (t : ℤ), |t|≤(D:ℤ) → ∀ j u, A.InnerVisible (-(N:ℤ)) N t j u
  strict : ∀ (t : ℤ), |t|≤(D:ℤ) →
    t+A.endRule.offset+(A.endRule.d:ℤ)+(A.endRule.B-1)*A.endRule.S<N

lemma exists_inspection [Fintype J] (D : ℕ) : ∃ N : ℕ, A.Inspection D N := by
  obtain ⟨N₁,h₁,V₁⟩ := A.exists_horizon D
  obtain ⟨N₂,h₂,V₂⟩ := A.exists_inner_horizon D
  obtain ⟨N₃,h₃,V₃⟩ := A.endRule.exists_uniform_horizon D
  let N := max N₁ (max N₂ N₃)
  have n₁ : N₁≤N := le_max_left _ _
  have n₂ : N₂≤N := (le_max_left _ _).trans (le_max_right _ _)
  have n₃ : N₃≤N := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨N,⟨h₁.trans_le n₁,?_,?_,?_⟩⟩
  · intro t ht Q
    exact Visible.mono A (V₁ t ht Q) (by omega) (by omega)
  · intro t ht j u
    exact InnerVisible.mono A (V₂ t ht j u) (by omega) (by omega)
  · intro t ht
    exact (V₃ t ht).2.trans_le (by exact_mod_cast n₃)

end ExceptionalOrigins.Parameters

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace StreamSplice.Frame

open WordIntervals LocalMarkers
variable {Alphabet : Type uAlphabet} {M : Type uM} [Monoid M] {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet}
    (H : Frame f f' N x y)

include H

lemma piece_left_any {s t : ℤ} (ht : t≤N) : piece f s t=piece f' s t := by
  unfold piece
  apply List.ofFn_inj.mpr
  funext i
  exact (H.left _ (by have hi := i.isLt;omega)).symm

lemma product_left_any (T : FreeMonoid Alphabet →* M) {s t : ℤ} (ht : t≤N) :
    WordIntervals.product T f s t=WordIntervals.product T f' s t :=
  congrArg (fun w => T (FreeMonoid.ofList w)) (H.piece_left_any ht)

lemma observedSuffix {V : Type uV}
    {g B : ℕ} (T : FreeMonoid Alphabet →* M) {tag : SplitMetadata.MainTag M V g B}
    {k b : ℤ} {search search' : Fin (g+1) → Option ℤ}
    (hT : T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y)) (hb : N+x.length≤b)
    (hs : search=search') (hsearch : ∀ i q, search i=some q → q≤N)
    (hq : ObservedMain.SuffixRead T tag f k b search) :
    ObservedMain.SuffixRead T tag f' k (b+((y.length:ℤ)-x.length)) search' := by
  subst search'
  have hpos : ∀ i, tag.j.val < i.val → BoundarySnapshot.positions search i≤N := by
    intro i hi
    exact hsearch i _ (BoundarySnapshot.positions_return (hq.present i hi))
  have hg : tag.j.val < (Fin.last g).val := tag.j.isLt
  have hbN : N≤b+((y.length:ℤ)-x.length) := by omega
  refine ⟨⟨hq.present,?_,?_⟩,?_,hq.ordered⟩
  · rw [H.product T hT (hpos _ hg) hb]
    exact hq.final
  · intro i hi
    rw [←H.product_left_any T (hpos _ (by exact Nat.lt_succ_of_lt hi))]
    exact hq.later i hi
  · intro i hi
    exact ⟨(hq.bounds i hi).1,(hpos i hi).trans hbN⟩

end StreamSplice.Frame

namespace OuterStream

open WordIntervals LocalMarkers StreamSplice SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet2} {M : Type uM2} {V : Type uV2} {K : Type uK} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

noncomputable def originBound : ℕ := H.offsets.sup (fun h => h.natAbs)

omit [Fintype C] in
lemma origin_bound {t : ℤ} (ht : t∈H.origins 0) : |t|≤(originBound A H:ℤ) := by
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp ht
  have hle := Finset.le_sup (f := fun h : ℤ => h.natAbs) hh
  simpa only [zero_sub,abs_neg,Int.natCast_natAbs] using
    (show (h.natAbs:ℤ)≤(originBound A H:ℤ) by exact_mod_cast hle)

omit [Fintype C] in
lemma main_origin (j : Fin g) {a : ℕ} (ha : a<H.R) :
    -H.main j-a*A.B∈H.origins 0 := by
  apply Finset.mem_image.mpr
  refine ⟨H.main j+a*A.B,?_,by omega⟩
  exact H.offset_mem (.inl j) a ha

lemma suffix_splice {N : ℕ} (HN : A.Inspection (originBound A H) N)
    {f f' : ℤ → Alphabet} {x y : List Alphabet} {b reference : ℤ}
    {tag : Tag M V g A.B} (HF : Frame f f' N x y)
    (hb : (N:ℤ)+x.length≤b-A.endRule.tail) (hsum : SummaryEq A T x y)
    (hq : Suffix A H clock T ρ reference tag f 0 b) :
    Suffix A H clock T ρ reference tag f' 0 (b+((y.length:ℤ)-x.length)) := by
  have hbn : (N:ℤ)+x.length≤b := by have := A.endRule.tail_pos;omega
  have hvis := fun t ht => (HN.full t (origin_bound A H ht) (0:ℤ)).base
  have href : -reference∈H.origins 0 := by simpa only [zero_sub] using hq.guard.1
  have hphase := HF.anchor_relative_phase A (t := -reference) (b := b) (r := 0)
    (hvis _ href) hsum.residue_dvd hsum.clock_eq
  simp only [sub_zero] at hphase
  have hbN : (N:ℤ)≤b+((y.length:ℤ)-x.length) := by omega
  refine ⟨by omega,HF.guard A.endRule (fun t ht => ⟨hvis t ht,HN.strict t (origin_bound A H ht)⟩)
    hb hsum.period_dvd hsum.matcher_eq hq.guard,?_,?_,?_⟩
  · change A.φ (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) (0-reference)-0)∈clock.J tag
    simpa only [suffixAnchor,zero_sub,sub_zero,hphase.2] using hq.clock_mem
  · change A.residue (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) (0-reference)-0)=tag.residue
    simpa only [suffixAnchor,zero_sub,sub_zero,hphase.1] using hq.residue_eq
  · cases tag with
    | inr tag =>
      change tag.output=ρ (tag.prefixProduct*product T f' 0 (b+((y.length:ℤ)-x.length))) tag.input
      rw [HF.product T hsum.monoid_eq (by omega) hbn]
      exact hq.letter_test
    | inl tag =>
      have present : SuffixMain A H T tag f 0 b := hq.letter_test
      have hv (a : ℕ) (ha : a<H.R) (i : Fin (g+1)) :
          A.InnerVisible (-(N:ℤ)) N (-H.main tag.j-a*A.B) i tag.u :=
        HN.inner _ (origin_bound A H (main_origin A H tag.j ha)) i tag.u
      have hR : 0<H.R := H.R_pos
      have hzero : -H.main tag.j-0*A.B=-H.main tag.j := by ring
      have hbase (i : Fin (g+1)) : A.InnerVisible (-(N:ℤ)) N (-H.main tag.j) i tag.u := by
        simpa only [Nat.cast_zero,zero_mul,sub_zero] using hv 0 hR i
      have hsearch : search A f tag.u (-H.main tag.j)=search A f' tag.u (-H.main tag.j) := by
        funext i
        exact A.inner_congr (hbase i) (HF.agrees_left (le_refl _))
      refine ⟨?_,?_,?_⟩
      · intro a ha i hi
        have old := present.visible a ha i hi
        have new := hv a ha i
        exact ⟨old.1,by simpa only [zero_sub] using new.2.trans hbN⟩
      · intro a ha i hi
        have hs := A.inner_congr (hv a ha i) (HF.agrees_left (le_refl _))
        have ho := present.stable a ha i hi
        simp only [zero_sub] at ho ⊢
        exact hs.symm.trans (ho.trans (congrFun hsearch i))
      · have hh := HF.observedSuffix T hsum.monoid_eq hbn hsearch (fun i q hq => by
          have hb' := A.inner_bounds hq
          have hv' := (hbase i).2
          have hr := A.innerRule.radius_ge
          omega) (by simpa only [zero_sub] using present.observed)
        simpa only [zero_sub] using hh

end OuterStream
namespace InnerStream

open WordIntervals LocalMarkers StreamSplice SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet3} {M : Type uM3} {V : Type uV3} {K : Type uK2} {P : Type uP2} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g g' μ : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)

lemma hypothetical_splice {N : ℕ} {f f' : ℤ → Alphabet} {x y : List Alphabet} {s b t : ℤ}
    (HF : Frame f f' N x y) (ha : s+early (Fin.last g')≤N) (hb : (N:ℤ)+x.length≤b)
    (hend : A.endRule.Visible (-(N:ℤ)) N (t+A.endRule.offset))
    (hv : ∀ j u, A.InnerVisible (-(N:ℤ)) N t j u) (hsum : SummaryEq A T x y) :
    hypothetical A clock T ρ β early f' s (b+((y.length:ℤ)-x.length)) t=
      hypothetical A clock T ρ β early f s b t := by
  have hphase := HF.anchor_phase A (b := b) hend hsum.residue_dvd hsum.clock_eq
  let u := A.residue (A.anchor f (b-A.endRule.tail) t-t)
  have hsearch : OuterStream.search A f u t=OuterStream.search A f' u t := by
    funext j
    exact A.inner_congr (hv j u) (HF.agrees_left (le_refl _))
  have hl := HF.later T ha hb hsum.monoid_eq (OuterStream.search A f u t) (fun j q hq => by
    have hq' := A.inner_bounds hq
    have hv' := (hv j u).2
    have hr := A.innerRule.radius_ge
    omega)
  dsimp only [hypothetical]
  rw [←hphase.1,←hphase.2,←hsearch,hl]

variable [Fintype K]
    (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

noncomputable def inspectionBound : ℕ :=
  SourceSchedule.absoluteBound p + lag.natAbs + SourceSchedule.absoluteBound early

omit [Monoid M] in
lemma origin_bound (slot : Roster M (V × K) K g' μ) :
    |SuffixDecoder.origin p lag 0 slot|≤(inspectionBound early p lag:ℤ) := by
  have hp := abs_le.mp (SourceSchedule.abs_le_absoluteBound p slot)
  have hl := abs_le.mp (le_refl |lag|)
  have hn : (0:ℤ)≤SourceSchedule.absoluteBound early := Int.natCast_nonneg _
  rw [abs_le]
  simp only [SuffixDecoder.origin,zero_add,inspectionBound,Nat.cast_add,Int.natCast_natAbs]
  constructor <;> omega

omit [Monoid M] in
lemma boundary_bound (slot : Roster M (V × K) K g' μ) (i : Fin (g'+1)) :
    -p slot+early i≤(inspectionBound early p lag:ℤ) := by
  have hp := abs_le.mp (SourceSchedule.abs_le_absoluteBound p slot)
  have he := abs_le.mp (SourceSchedule.abs_le_absoluteBound early i)
  have hl : (0:ℤ)≤lag.natAbs := Int.natCast_nonneg _
  simp only [inspectionBound,Nat.cast_add]
  omega

lemma suffix_splice {N : ℕ} (HN : A.Inspection (inspectionBound early p lag) N)
    {f f' : ℤ → Alphabet} {x y : List Alphabet} {b : ℤ}
    {reference slot : Roster M (V × K) K g' μ} (hw₀ : 0≤A.w₀)
    (HF : Frame f f' N x y) (hb : (N:ℤ)+x.length≤b-A.endRule.tail)
    (hsum : SummaryEq A T x y) (hq : Suffix A clock T ρ β early p lag reference slot f 0 b) :
    Suffix A clock T ρ β early p lag reference slot f' 0 (b+((y.length:ℤ)-x.length)) := by
  have hbn : (N:ℤ)+x.length≤b := by have := A.endRule.tail_pos;omega
  have hD : (inspectionBound early p lag:ℤ)≤N := by exact_mod_cast HN.contains.le
  have hvis := fun i Q => HN.full _ (origin_bound early p lag i) Q
  have hbase (i : Roster M (V × K) K g' μ) := (hvis i (0:ℤ)).base
  refine ⟨HF.decoder A hw₀ (fun i => hvis i _) hvis
    (fun i => HN.strict _ (origin_bound early p lag i)) hb hsum.period_dvd hsum.matcher_eq
    hsum.residue_dvd hsum.clock_eq hq.decoder,?_,?_⟩
  · intro i hi
    have hb' := (boundary_bound early p lag slot i.val.succ).trans hD
    simpa only [zero_sub] using (HF.product_left_any T hb').symm.trans (by simpa only [zero_sub] using hq.observed.later i hi)
  · have hend : A.endRule.Visible (-(N:ℤ)) N (-p slot+lag+A.endRule.offset) := by
      simpa only [SuffixDecoder.origin,zero_add,add_zero,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hbase slot
    have hi : ∀ j u, A.InnerVisible (-(N:ℤ)) N (-p slot+lag) j u := by
      intro j u
      have hh := HN.inner _ (origin_bound early p lag slot) j u
      simpa only [SuffixDecoder.origin,zero_add,add_zero,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hh
    have hh := hypothetical_splice A clock T ρ β early (s := -p slot) (b := b)
      (t := -p slot+lag) HF
      ((boundary_bound early p lag slot (Fin.last g')).trans hD) hbn
      hend hi hsum
    simpa only [zero_sub] using hh.trans (by simpa only [zero_sub] using hq.observed.hypothetical_eq)

end InnerStream
namespace StreamSplice

variable {Alphabet : Type uAlphabet4}

lemma wordTest_finite [Finite Alphabet] {R : (ℤ → Alphabet) → ℤ → Prop} (N : ℕ)
    (hR : ∀ f b, R f b → b≤N) : (wordTest R : Set (List Alphabet)).Finite := by
  apply (List.finite_length_le Alphabet N).subset
  rintro w ⟨f,_,hw⟩
  exact_mod_cast hR f _ hw

end StreamSplice

namespace OuterStream

open WordIntervals LocalMarkers StreamSplice SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet5} {M : Type uM4} {V : Type uV4} {K : Type uK3} {P : Type uP3} {C : Type uC3} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

noncomputable def prefixLanguage (lag : ℤ) (x : V) : Language Alphabet :=
  ⨆ tag : {tag : Tag M V g A.B // tag.input=x},
    wordTest (fun f b => Prefix A H clock T ρ β tag.val f 0 lag b)

noncomputable def suffixLanguage (reference : ℤ) (y : V) : Language Alphabet :=
  ⨆ tag : {tag : Tag M V g A.B // tag.output=y},
    wordTest (fun f b => Suffix A H clock T ρ reference tag.val f 0 b)

lemma prefix_finite [Finite Alphabet] (lag : ℤ) (x : V) :
    (prefixLanguage A H clock T ρ β lag x : Set (List Alphabet)).Finite := by
  apply (List.finite_length_le Alphabet (lag.natAbs+originBound A H)).subset
  intro w hw
  obtain ⟨tag,f,hf,hp⟩ := Language.mem_iSup.mp hw
  obtain ⟨a,ha,hcut⟩ := hp.cut
  have hm := H.offset_mem (H.tagRole tag.val) a ha
  have hb := abs_le.mp (show |H.base (H.tagRole tag.val)+(a:ℤ)*A.B|≤(originBound A H:ℤ) by
    simpa only [originBound,Int.natCast_natAbs] using
      (show ((H.base (H.tagRole tag.val)+(a:ℤ)*A.B).natAbs:ℤ)≤(originBound A H:ℤ) from
        by exact_mod_cast Finset.le_sup (f := fun h : ℤ => h.natAbs) hm))
  have hl : lag≤(lag.natAbs:ℤ) := by simpa only [Int.natCast_natAbs] using le_abs_self lag
  have hwlen : (w.length:ℤ)≤(lag.natAbs+originBound A H:ℕ) := by
    rw [Nat.cast_add]
    omega
  exact_mod_cast hwlen

lemma prefix_height [Finite Alphabet] (lag : ℤ) (x : V) :
    HasHeightAtMost (prefixLanguage A H clock T ρ β lag x) 0 :=
  HasHeightAtMost.finite _ (prefix_finite A H clock T ρ β lag x) 0

lemma suffix_regular [Finite Alphabet] (n : ℕ) (hn : 0<n) (hφ : A.φ (n:ℤ)=0)
    (reference : ℤ) (y : V) : (suffixLanguage A H clock T ρ reference y).IsRegular := by
  obtain ⟨N,HN⟩ := A.exists_inspection (originBound A H)
  apply FiniteRecognition.regular_iSup
  intro tag
  exact wordTest_regular A T n hn hφ N _ (fun f f' b x y HF hb hs hq =>
    suffix_splice A H clock T ρ HN HF hb hs hq)

lemma suffix_height [Finite Alphabet] (n : ℕ) (hn : 0<n) (hφ : A.φ (n:ℤ)=0)
    (reference : ℤ) (y : V) : HasHeightAtMost (suffixLanguage A H clock T ρ reference y) 1 := by
  apply A.endRule.ending_height _ (suffix_regular A H clock T ρ n hn hφ reference y)
    (originBound A H)
  intro w hw
  obtain ⟨tag,f,hf,hq⟩ := Language.mem_iSup.mp hw
  refine ⟨f,-reference,hf,?_,?_⟩
  · exact origin_bound A H (by simpa only [zero_sub] using hq.guard.1)
  · simpa only [zero_sub] using hq.guard.2.2.2

end OuterStream

namespace InnerStream

open WordIntervals LocalMarkers StreamSplice SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet6} {M : Type uM5} {V : Type uV5} {K : Type uK4} {P : Type uP4} {C : Type uC4} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype K] [Fintype P] [Fintype C] {g g' μ : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)
    (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

noncomputable def prefixLanguage (x : V × K) : Language Alphabet :=
  ⨆ slot : {slot : Roster M (V × K) K g' μ // slot.1.input=x},
    wordTest (fun f b => Prefix T early γ p slot.val f 0 b)

noncomputable def suffixLanguage (reference : Roster M (V × K) K g' μ) (y : V × K) : Language Alphabet :=
  ⨆ slot : {slot : Roster M (V × K) K g' μ // slot.1.output=y},
    wordTest (fun f b => Suffix A clock T ρ β early p lag reference slot.val f 0 b)

lemma prefix_finite [Finite Alphabet] (x : V × K) :
    (prefixLanguage T early γ p x : Set (List Alphabet)).Finite := by
  apply (List.finite_length_le Alphabet (SourceSchedule.absoluteBound p)).subset
  intro w hw
  obtain ⟨slot,f,_,hp⟩ := Language.mem_iSup.mp hw
  have hb := (abs_le.mp (SourceSchedule.abs_le_absoluteBound p slot.val)).2
  have hwlen : (w.length:ℤ)≤SourceSchedule.absoluteBound p := by rw [hp.cut];simpa only [zero_add] using hb
  exact_mod_cast hwlen

lemma prefix_height [Finite Alphabet] (x : V × K) :
    HasHeightAtMost (prefixLanguage T early γ p x) 0 :=
  HasHeightAtMost.finite _ (prefix_finite T early γ p x) 0

lemma suffix_regular [Finite Alphabet] (n : ℕ) (hn : 0<n) (hφ : A.φ (n:ℤ)=0)
    (hw₀ : 0≤A.w₀) (reference : Roster M (V × K) K g' μ) (y : V × K) :
    (suffixLanguage A clock T ρ β early p lag reference y).IsRegular := by
  obtain ⟨N,HN⟩ := A.exists_inspection (inspectionBound early p lag)
  apply FiniteRecognition.regular_iSup
  intro slot
  exact wordTest_regular A T n hn hφ N _ (fun f f' b x y HF hb hs hq =>
    suffix_splice A clock T ρ β early p lag HN hw₀ HF hb hs hq)

lemma suffix_height [Finite Alphabet] (n : ℕ) (hn : 0<n) (hφ : A.φ (n:ℤ)=0)
    (hw₀ : 0≤A.w₀) (reference : Roster M (V × K) K g' μ) (y : V × K) :
    HasHeightAtMost (suffixLanguage A clock T ρ β early p lag reference y) 1 := by
  apply A.endRule.ending_height _ (suffix_regular A clock T ρ β early p lag n hn hφ hw₀ reference y)
    (inspectionBound early p lag)
  intro w hw
  obtain ⟨slot,f,hf,hq⟩ := Language.mem_iSup.mp hw
  exact ⟨f,SuffixDecoder.origin p lag 0 slot.val,hf,origin_bound early p lag slot.val,
    hq.decoder.final_guard⟩

end InnerStream

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace StreamShift

open LocalMarkers WordIntervals
variable {Alphabet : Type uAlphabet}

def shift (f : ℤ → Alphabet) (a : ℤ) : ℤ → Alphabet := fun x => f (x-a)

@[simp] lemma shift_add (f : ℤ → Alphabet) (a x : ℤ) : shift f a (x+a)=f x := by
  simp only [shift,add_sub_cancel_right]

lemma map_injective (a : ℤ) : Function.Injective (Option.map (fun x : ℤ => x+a)) := by
  intro x y h
  cases x <;> cases y <;> simp_all

lemma map_none (a : ℤ) (x : Option ℤ) : x.map (fun x => x+a)=none ↔ x=none := by
  cases x <;> simp

lemma realizes {w : List Alphabet} {f : ℤ → Alphabet} {s : ℤ}
    (hf : Realizes w s f) (a : ℤ) : Realizes w (s+a) (shift f a) := by
  intro i
  simpa only [shift,show s+a+(i.val:ℤ)-a=s+i.val by ring] using hf i

lemma piece (f : ℤ → Alphabet) (s t a : ℤ) :
    WordIntervals.piece (shift f a) (s+a) (t+a)=WordIntervals.piece f s t := by
  unfold WordIntervals.piece WordIntervals.segment
  simp only [add_sub_add_right_eq_sub]
  apply List.ofFn_inj.mpr
  funext i
  simp only [shift,Fin.val_cast,show s+a+(i.val:ℤ)-a=s+i.val by ring]

lemma product {M : Type uM} [Monoid M] (T : FreeMonoid Alphabet →* M)
    (f : ℤ → Alphabet) (s t a : ℤ) :
    WordIntervals.product T (shift f a) (s+a) (t+a)=WordIntervals.product T f s t :=
  congrArg T (piece f s t a)

lemma markers {d K : ℕ} (R : Rule Alphabet d K) (f : ℤ → Alphabet) (a x : ℤ) :
    x∈R.markers (shift f a) ↔ x-a∈R.markers f := by
  change x∈R.markers (fun i => f (i-a)) ↔ x-a∈R.markers f
  simpa only [sub_eq_add_neg] using R.translate f (-a) x

lemma marker_search {S S' : Set ℤ} (a : ℤ) (hS : ∀ x, x∈S' ↔ x-a∈S) (l r : ℤ) :
    MarkerSearch.search S' (l+a) (r+a)=(MarkerSearch.search S l r).map (fun x => x+a) := by
  cases he : MarkerSearch.search S l r with
  | none =>
    simp only [Option.map_none]
    apply MarkerSearch.search_none.mpr
    intro m hm hl hr
    exact MarkerSearch.search_none.mp he (m-a) ((hS m).mp hm) (by omega) (by omega)
  | some q =>
    simp only [Option.map_some]
    obtain ⟨⟨hq,hlo,hmin⟩,hhi⟩ := MarkerSearch.search_some.mp he
    apply MarkerSearch.search_some.mpr
    refine ⟨⟨(hS _).mpr (by simpa only [add_sub_cancel_right] using hq),by omega,?_⟩,by omega⟩
    intro m hm hl
    have hh := hmin (m-a) ((hS m).mp hm) (by omega)
    omega

lemma end_search {S S' : Set ℤ} (a : ℤ) (hS : ∀ x, x∈S' ↔ x-a∈S)
    {B D : ℤ} (hB : 0<B) (hD : 0≤D) (c z : ℤ) :
    EndSearch.search S' B D c (z+a)=(EndSearch.search S B D c z).map (fun x => x+a) := by
  have he (m : ℤ) : EndSearch.Eligible S' B D c (z+a) m ↔
      EndSearch.Eligible S B D c z (m-a) := by
    simp only [EndSearch.Eligible,hS,show m-(z+a)=m-a-z by ring]
  cases hs : EndSearch.search S B D c z with
  | none =>
    simp only [Option.map_none]
    apply (EndSearch.search_none hB hD).mpr
    intro m hm
    exact (EndSearch.search_none hB hD).mp hs (m-a) ((he m).mp hm)
  | some q =>
    simp only [Option.map_some]
    obtain ⟨hq,hmin⟩ := (EndSearch.search_some hB hD).mp hs
    apply (EndSearch.search_some hB hD).mpr
    refine ⟨(he _).mpr (by simpa only [add_sub_cancel_right] using hq),?_⟩
    intro m hm
    have hh := hmin (m-a) ((he m).mp hm)
    omega

lemma agrees {f v : ℤ → Alphabet} {s b : ℤ} (hf : AgreesOn f v s b) (a : ℤ) :
    AgreesOn (shift f a) (shift v a) (s+a) (b+a) := by
  intro x hx hx'
  exact hf (x-a) (by omega) (by omega)

lemma continuation {d K : ℕ} {f v : ℤ → Alphabet} {z : ℤ}
    (hv : ShortContinuation d K f z v) (a : ℤ) :
    ShortContinuation d K (shift f a) (z+a) (shift v a) := by
  obtain ⟨⟨p,hp,hpd,hper⟩,hv⟩ := hv
  refine ⟨⟨p,hp,hpd,?_⟩,?_⟩
  · intro x
    simpa only [shift,show x+(p:ℤ)-a=(x-a)+p by ring] using hper (x-a)
  · simpa only [show z+(K:ℤ)+a=z+a+K by ring] using agrees hv a

lemma mismatch {K : ℕ} {f v : ℤ → Alphabet} {z q : ℤ}
    (hm : EpisodeEnd.FirstMismatch f v z K q) (a : ℤ) :
    EpisodeEnd.FirstMismatch (shift f a) (shift v a) (z+a) K (q+a) := by
  refine ⟨by have := hm.1;omega,?_,agrees hm.2.2 a⟩
  simpa only [shift_add] using hm.2.1

lemma ending {d K : ℕ} {tail z b : ℤ} {f : ℤ → Alphabet} {op : Option ℤ}
    (he : EpisodeEnd.EndAt d K tail f z op b) (a : ℤ) :
    EpisodeEnd.EndAt d K tail (shift f a) (z+a) (op.map (fun x => x+a)) (b+a) := by
  cases op with
  | some q => dsimp [EpisodeEnd.EndAt] at he ⊢;omega
  | none =>
    obtain ⟨v,hv,hm⟩ := he
    refine ⟨shift v a,continuation hv a,?_⟩
    simpa only [show b-tail+a=b+a-tail by ring] using mismatch hm a

lemma inner_failure {S S' : Set ℤ} (a : ℤ) (hS : ∀ x, x∈S' ↔ x-a∈S) (z H w E : ℤ) :
    MarkerSearch.InnerFailure S' (z+a) H w E ↔ MarkerSearch.InnerFailure S z H w E := by
  have hs (v : ℤ) : MarkerSearch.search S' (z+a+v) (z+a+H+v)=
      (MarkerSearch.search S (z+v) (z+H+v)).map (fun x => x+a) := by
    rw [show z+a+v=(z+v)+a by ring,show z+a+H+v=(z+H+v)+a by ring]
    exact marker_search a hS (z+v) (z+H+v)
  have hz : MarkerSearch.search S' (z+a) (z+a+H)=
      (MarkerSearch.search S z (z+H)).map (fun x => x+a) := by
    rw [show z+a+H=(z+H)+a by ring]
    exact marker_search a hS z (z+H)
  unfold MarkerSearch.InnerFailure
  rw [hz]
  apply or_congr
  · apply exists_congr
    intro v
    rw [hs]
    exact and_congr_right (fun _ => not_congr (map_injective a).eq_iff)
  · rw [map_none]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨m,hm,hl,hr⟩
      exact ⟨m-a,(hS m).mp hm,by omega,by omega⟩
    · rintro ⟨m,hm,hl,hr⟩
      exact ⟨m+a,(hS _).mpr (by simpa only [add_sub_cancel_right] using hm),by omega,by omega⟩

lemma unstable {S S' : Set ℤ} (a : ℤ) (hS : ∀ x, x∈S' ↔ x-a∈S)
    {B D : ℤ} (hB : 0<B) (hD : 0≤D) (c z w : ℤ) :
    EndSearch.Unstable S' B D c (z+a) w ↔ EndSearch.Unstable S B D c z w := by
  unfold EndSearch.Unstable
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  rw [end_search a hS hB hD c z]
  have hs := end_search a hS hB hD c (z+v)
  rw [show z+v+a=z+a+v by ring] at hs
  rw [hs]
  exact not_congr (map_injective a).eq_iff

end StreamShift

namespace CanonicalEpisodes.Parameters

open StreamShift EpisodeEnd
variable {Alphabet : Type uAlphabet2} (C : CanonicalEpisodes.Parameters Alphabet)

lemma small_shift (f : ℤ → Alphabet) (a z : ℤ) :
    C.small (shift f a) (z+a)=(C.small f z).map (fun x => x+a) :=
  end_search a (markers C.rule f a) C.B_pos C.S_nonneg C.d z

lemma large_shift (f : ℤ → Alphabet) (a z : ℤ) :
    C.large (shift f a) (z+a)=(C.large f z).map (fun x => x+a) :=
  end_search a (markers C.rule f a) C.B_pos C.S_nonneg (3*C.d) z

lemma visible_shift {s b z : ℤ} (hv : C.Visible s b z) (a : ℤ) :
    C.Visible (s+a) (b+a) (z+a) := by
  rcases hv with ⟨h₁,h₂,h₃,h₄⟩
  exact ⟨by omega,by omega,by omega,by omega⟩

lemma end_shift {f : ℤ → Alphabet} {z b : ℤ}
    (he : EndAt C.d C.K C.tail f z (C.small f z) b) (a : ℤ) :
    EndAt C.d C.K C.tail (shift f a) (z+a) (C.small (shift f a) (z+a)) (b+a) := by
  rw [C.small_shift]
  exact ending he a

lemma guard_shift {O : Finset ℤ} {reference s b : ℤ} {f : ℤ → Alphabet}
    (hg : C.Guard O reference s b f) (a : ℤ) :
    C.Guard (O.image (fun x => x+a)) (reference+a) (s+a) (b+a) (shift f a) := by
  refine ⟨Finset.mem_image.mpr ⟨reference,hg.1,rfl⟩,?_,?_,?_⟩
  · intro t ht
    obtain ⟨t',ht',rfl⟩ := Finset.mem_image.mp ht
    simpa only [show t'+C.offset+a=t'+a+C.offset by ring] using C.visible_shift (hg.2.1 t' ht') a
  · intro t ht
    obtain ⟨t',ht',rfl⟩ := Finset.mem_image.mp ht
    have he := hg.2.2.1 t' ht'
    rw [show t'+a+C.offset=t'+C.offset+a by ring,
      show reference+a+C.offset=reference+C.offset+a by ring,C.small_shift,C.small_shift,
      C.large_shift,C.large_shift,he.1,he.2]
    exact ⟨rfl,rfl⟩
  · simpa only [show reference+C.offset+a=reference+a+C.offset by ring] using C.end_shift hg.2.2.2 a

end CanonicalEpisodes.Parameters

namespace ExceptionalOrigins.Parameters

open StreamShift
variable {Alphabet : Type uAlphabet3} {J : Type uJ} {C : Type uC} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma inner_shift (f : ℤ → Alphabet) (j : J) (u : Fin A.B) (t a : ℤ) :
    A.inner (shift f a) j u (t+a)=(A.inner f j u t).map (fun x => x+a) := by
  unfold inner
  rw [show t+a+A.offset j=(t+A.offset j)+a by ring,
    show t+A.offset j+a+A.H u=(t+A.offset j+A.H u)+a by ring]
  exact marker_search a (markers A.innerRule f a) (t+A.offset j) (t+A.offset j+A.H u)

lemma anchor_shift (f : ℤ → Alphabet) (q t a : ℤ) :
    A.anchor (shift f a) (q+a) (t+a)=A.anchor f q t+a := by
  unfold anchor
  rw [show t+a+A.endRule.offset=t+A.endRule.offset+a by ring,A.endRule.large_shift]
  cases A.endRule.large f (t+A.endRule.offset) <;> rfl

lemma innerVisible_shift {s b t : ℤ} {j : J} {u : Fin A.B}
    (hv : A.InnerVisible s b t j u) (a : ℤ) : A.InnerVisible (s+a) (b+a) (t+a) j u := by
  rcases hv with ⟨hl,hr⟩
  exact ⟨by omega,by omega⟩

lemma visible_shift {s b t Q : ℤ} (hv : A.Visible s b t Q) (a : ℤ) :
    A.Visible (s+a) (b+a) (t+a) (Q+a) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [show t+A.endRule.offset+a=t+a+A.endRule.offset by ring] using A.endRule.visible_shift hv.base a
  · intro v hd hw
    obtain ⟨hl,hr⟩ := hv.ends v hd hw
    exact ⟨by omega,by omega⟩
  · intro j
    obtain ⟨hl,hr⟩ := hv.inner j
    simp only [add_sub_add_right_eq_sub]
    exact ⟨by omega,by omega⟩

lemma failed_shift (f : ℤ → Alphabet) (t Q a : ℤ) :
    A.Failed (shift f a) (t+a) (Q+a) ↔ A.Failed f t Q := by
  have hb : (0:ℤ)<A.B := by exact_mod_cast A.B_pos
  unfold Failed Z Star
  rw [show t+a+A.endRule.offset=t+A.endRule.offset+a by ring,
    unstable a (markers A.endRule.rule f a) hb A.endRule.S_nonneg,
    unstable a (markers A.endRule.rule f a) hb A.endRule.S_nonneg]
  simp only [add_sub_add_right_eq_sub]
  apply or_congr_right
  apply or_congr_right
  apply exists_congr
  intro j
  rw [show t+a+A.offset j=t+A.offset j+a by ring]
  exact inner_failure a (markers A.innerRule f a) _ _ _ _

end ExceptionalOrigins.Parameters

namespace SuffixDecoder

open StreamShift
variable {Alphabet : Type uAlphabet4} {J : Type uJ2} {C : Type uC2} {P : Type uP}
    (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma test_shift {τ : P → ℤ} {reference decoded : P} {k b : ℤ} {f : ℤ → Alphabet}
    (ht : Test A τ reference k b f decoded) (a : ℤ) :
    Test A (fun i => τ i+a) reference (k+a) (b+a) (shift f a) decoded := by
  have ha (i : P) : A.anchor (shift f a) (b+a-A.endRule.tail) (τ i+a)=
      A.anchor f (b-A.endRule.tail) (τ i)+a := by
    rw [show b+a-A.endRule.tail=(b-A.endRule.tail)+a by ring,A.anchor_shift]
  have hs (i : P) : A.endRule.small (shift f a) (τ i+a+A.endRule.offset)=
      (A.endRule.small f (τ i+A.endRule.offset)).map (fun x => x+a) := by
    rw [show τ i+a+A.endRule.offset=τ i+A.endRule.offset+a by ring,A.endRule.small_shift]
  have hl (i : P) : A.endRule.large (shift f a) (τ i+a+A.endRule.offset)=
      (A.endRule.large f (τ i+A.endRule.offset)).map (fun x => x+a) := by
    rw [show τ i+a+A.endRule.offset=τ i+A.endRule.offset+a by ring,A.endRule.large_shift]
  have hf (i : P) : A.Failed (shift f a) (τ i+a)
      (A.anchor (shift f a) (b+a-A.endRule.tail) (τ i+a)) ↔
      A.Failed f (τ i) (A.anchor f (b-A.endRule.tail) (τ i)) := by
    rw [ha,A.failed_shift]
  refine ⟨?_,?_,⟨(hf decoded).mpr ht.unique.1,fun i hi => ht.unique.2 i ((hf i).mp hi)⟩,?_⟩
  · intro i
    rw [ha]
    exact A.visible_shift (ht.visible i) a
  · intro he
    obtain ⟨i,hi⟩ := he
    rw [hl,map_none] at hi
    obtain ⟨hn,hend⟩ := ht.reference_guard ⟨i,hi⟩
    refine ⟨fun i => ?_,?_⟩
    · rw [hs,hn,Option.map_none]
    · simpa only [show τ reference+A.endRule.offset+a=τ reference+a+A.endRule.offset by ring] using A.endRule.end_shift hend a
  · simpa only [show τ decoded+A.endRule.offset+a=τ decoded+a+A.endRule.offset by ring] using A.endRule.end_shift ht.final_guard a

end SuffixDecoder

namespace BoundarySnapshot

open StreamShift
variable {Alphabet : Type uAlphabet5} {M : Type uM2} [Monoid M] {g : ℕ}

def translated (search : Fin (g+1) → Option ℤ) (a : ℤ) : Fin (g+1) → Option ℤ :=
  fun i => (search i).map (fun x => x+a)

lemma translated_none (search : Fin (g+1) → Option ℤ) (a : ℤ) (i : Fin (g+1)) :
    translated search a i=none ↔ search i=none := map_none a (search i)

lemma translated_position {search : Fin (g+1) → Option ℤ} {i : Fin (g+1)}
    (hi : search i≠none) (a : ℤ) : positions (translated search a) i=positions search i+a := by
  cases hs : search i with
  | none => exact False.elim (hi hs)
  | some q => simp only [positions,translated,hs,Option.map_some,Option.getD_some]

lemma present_shift {search : Fin (g+1) → Option ℤ} {s b : ℤ}
    (hp : Present search s b) (a : ℤ) : Present (translated search a) (s+a) (b+a) := by
  obtain ⟨p,hp,hm,hs,hb⟩ := hp
  exact ⟨fun i => p i+a,fun i => by simp only [translated,hp,Option.map_some],
    (by intro i j hij; have := hm hij; dsimp; omega),(by dsimp;omega),(by dsimp;omega)⟩

lemma present_shift_iff (search : Fin (g+1) → Option ℤ) (s b a : ℤ) :
    Present (translated search a) (s+a) (b+a) ↔ Present search s b := by
  refine ⟨?_,fun hp => present_shift hp a⟩
  rintro ⟨p,hp,hm,hs,hb⟩
  refine ⟨fun i => p i-a,?_,(by intro i j hij; have := hm hij; dsimp; omega),(by dsimp;omega),(by dsimp;omega)⟩
  intro i
  have hi := hp i
  cases he : search i with
  | none => simp only [translated,he,Option.map_none] at hi;cases hi
  | some q =>
    simp only [translated,he,Option.map_some,Option.some.injEq] at hi
    congr 1
    dsimp
    omega

lemma factors_shift (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (search : Fin (g+1) → Option ℤ) (s b a : ℤ) :
    factors T (shift f a) (s+a) (b+a) (translated search a)=factors T f s b search := by
  classical
  by_cases hp : Present search s b
  · obtain ⟨p,hp,hm,hs,hb⟩ := hp
    have hps (i) : translated search a i=some (p i+a) := by simp only [translated,hp,Option.map_some]
    rw [factors_present T (shift f a) hps (by intro i j h; have := hm h; dsimp; omega)
      (by omega) (by omega),factors_present T f hp hm hs hb]
    simp only [StreamShift.product]
  · have hn := mt (present_shift_iff search s b a).mp hp
    simp only [factors,dite_eq_right hp,dite_eq_right hn]

lemma actual_shift (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (search : Fin (g+1) → Option ℤ) (s b a : ℤ) :
    actual T (shift f a) (s+a) (b+a) (translated search a)=actual T f s b search := by
  apply ClockAffine.Snapshot.ext (StreamShift.product T f s b a)
  exact factors_shift T f search s b a

lemma later_shift (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (search : Fin (g+1) → Option ℤ) (s b a : ℤ) :
    later T (shift f a) (s+a) (b+a) (translated search a)=later T f s b search := by
  have hp := StreamShift.product T f s b a
  have hf := factors_shift T f search s b a
  cases hl : later T (shift f a) (s+a) (b+a) (translated search a)
  cases hr : later T f s b search
  congr
  · exact (congrArg ClockAffine.Later.tailProduct hl).symm.trans
      (hp.trans (congrArg ClockAffine.Later.tailProduct hr))
  · exact (congrArg ClockAffine.Later.boundaries hl).symm.trans
      (hf.trans (congrArg ClockAffine.Later.boundaries hr))

end BoundarySnapshot

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace ObservedMain

open StreamShift BoundarySnapshot
variable {Alphabet : Type uAlphabet} {M : Type uM} {S : Type uS} {K : Type uK} [Monoid M] [Field K] [AddCommGroup S] [Module K S]
    {g B : ℕ} (T : FreeMonoid Alphabet →* M) (ρ : M → (S →ₗ[K] S))
    (β : M → M → (Fin g → M) → S)

lemma prefix_shift {tag : SplitMetadata.MainTag M S g B} {f : ℤ → Alphabet} {s k : ℤ}
    {search : Fin (g+1) → Option ℤ} (hp : PrefixRead T ρ β tag f s k search) (a : ℤ) :
    PrefixRead T ρ β tag (shift f a) (s+a) (k+a) (translated search a) := by
  have hpos (i : Fin (g+1)) (hi : i.val≤tag.j.val) := translated_position (hp.present i hi) a
  have hz : (0 : Fin (g+1)).val≤tag.j.val := Nat.zero_le _
  refine ⟨⟨fun i hi h => hp.present i hi ((translated_none search a i).mp h),?_,?_,hp.certificate⟩,?_,?_⟩
  · rw [hpos 0 hz,StreamShift.product]
    exact hp.initial
  · intro i hi
    rw [hpos i.val.castSucc (by exact hi.le),hpos i.val.succ (by exact hi),StreamShift.product]
    exact hp.earlier i hi
  · intro i hi
    rw [hpos i hi]
    have := hp.bounds i hi
    constructor <;> omega
  · intro i hi
    rw [hpos i.castSucc (by exact hi.le),hpos i.succ (by exact hi)]
    have := hp.ordered i hi
    omega

omit [Field K] [AddCommGroup S] [Module K S] in
lemma suffix_shift {tag : SplitMetadata.MainTag M S g B} {f : ℤ → Alphabet} {k b : ℤ}
    {search : Fin (g+1) → Option ℤ} (hq : SuffixRead T tag f k b search) (a : ℤ) :
    SuffixRead T tag (shift f a) (k+a) (b+a) (translated search a) := by
  have hpos (i : Fin (g+1)) (hi : tag.j.val < i.val) := translated_position (hq.present i hi) a
  have hg : tag.j.val < (Fin.last g).val := tag.j.isLt
  refine ⟨⟨fun i hi h => hq.present i hi ((translated_none search a i).mp h),?_,?_⟩,?_,?_⟩
  · rw [hpos _ hg,StreamShift.product]
    exact hq.final
  · intro i hi
    rw [hpos i.val.castSucc hi,hpos i.val.succ (by exact Nat.lt_succ_of_lt hi),StreamShift.product]
    exact hq.later i hi
  · intro i hi
    rw [hpos i hi]
    have := hq.bounds i hi
    constructor <;> omega
  · intro i hi
    rw [hpos i.castSucc hi,hpos i.succ (by exact Nat.lt_succ_of_lt hi)]
    have := hq.ordered i hi
    omega

end ObservedMain

namespace OuterStream

open StreamShift BoundarySnapshot SplitMetadata
variable {Alphabet : Type uAlphabet2} {M : Type uM2} {V : Type uV} {K : Type uK2} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

omit [Fintype C] in
lemma search_shift (f : ℤ → Alphabet) (u : Fin A.B) (t a : ℤ) :
    search A (shift f a) u (t+a)=translated (search A f u t) a := by
  funext i
  exact A.inner_shift f i u t a

omit [Fintype M] [Fintype C] in
lemma snapshot_shift (f : ℤ → Alphabet) (s b t a : ℤ) :
    snapshot A T (shift f a) (s+a) (b+a) (t+a)=snapshot A T f s b t := by
  unfold snapshot
  rw [show b+a-A.endRule.tail=(b-A.endRule.tail)+a by ring,A.anchor_shift,
    add_sub_add_right_eq_sub,search_shift,actual_shift]

lemma update_shift (f : ℤ → Alphabet) (s b t a : ℤ) (x : V) :
    update A clock T ρ β (shift f a) (s+a) (b+a) (t+a) x=update A clock T ρ β f s b t x := by
  unfold update
  rw [show b+a-A.endRule.tail=(b-A.endRule.tail)+a by ring,A.anchor_shift,
    add_sub_add_right_eq_sub,snapshot_shift]

lemma prefix_shift {tag : Tag M V g A.B} {f : ℤ → Alphabet} {s t k : ℤ}
    (hp : Prefix A H clock T ρ β tag f s t k) (a : ℤ) :
    Prefix A H clock T ρ β tag (shift f a) (s+a) (t+a) (k+a) := by
  refine ⟨by have := hp.positive;omega,?_,?_,?_⟩
  · obtain ⟨i,hi,hcut⟩ := hp.cut
    exact ⟨i,hi,by omega⟩
  · simpa only [add_sub_add_right_eq_sub] using hp.clock_mem
  · cases tag with
    | inl tag =>
      have hm : PrefixMain A T ρ β tag f s t k := hp.letter_test
      refine ⟨fun i hi => A.innerVisible_shift (hm.visible i hi) a,?_⟩
      rw [search_shift]
      exact ObservedMain.prefix_shift T ρ β hm.observed a
    | inr tag =>
      have hm : PrefixPeriodic A T tag f s t k := hp.letter_test
      refine ⟨A.innerVisible_shift hm.visible a,?_,?_⟩
      · rw [A.inner_shift,hm.absent,Option.map_none]
      · rw [StreamShift.product]
        exact hm.product_eq

omit [Monoid M] [Field K] [AddCommGroup V] [Module K V] [Fintype M] [Fintype V]
  [Fintype P] [Fintype C] in
lemma origins_shift (k a : ℤ) : H.origins (k+a)=(H.origins k).image (fun x => x+a) := by
  simp only [Cuts.origins,Finset.image_image]
  congr 1
  funext h
  dsimp
  ring

omit [Fintype C] in
lemma suffixAnchor_shift (f : ℤ → Alphabet) (reference k b a : ℤ) :
    suffixAnchor A reference (k+a) (b+a) (shift f a)=suffixAnchor A reference k b f+a := by
  unfold suffixAnchor
  rw [show b+a-A.endRule.tail=(b-A.endRule.tail)+a by ring,
    show k+a-reference=(k-reference)+a by ring,A.anchor_shift]

lemma suffix_shift {tag : Tag M V g A.B} {f : ℤ → Alphabet} {reference k b : ℤ}
    (hq : Suffix A H clock T ρ reference tag f k b) (a : ℤ) :
    Suffix A H clock T ρ reference tag (shift f a) (k+a) (b+a) := by
  refine ⟨by have := hq.ordered;omega,?_,?_,?_,?_⟩
  · rw [origins_shift,show k+a-reference=(k-reference)+a by ring]
    exact A.endRule.guard_shift hq.guard a
  · rw [suffixAnchor_shift,add_sub_add_right_eq_sub]
    exact hq.clock_mem
  · rw [suffixAnchor_shift,add_sub_add_right_eq_sub]
    exact hq.residue_eq
  · cases tag with
    | inr tag =>
      change tag.output=ρ (tag.prefixProduct*WordIntervals.product T (shift f a) (k+a) (b+a)) tag.input
      rw [StreamShift.product]
      exact hq.letter_test
    | inl tag =>
      have hm : SuffixMain A H T tag f k b := hq.letter_test
      refine ⟨?_,?_,?_⟩
      · intro i hi j hj
        simpa only [show k-H.main tag.j-(i:ℤ)*A.B+a=k+a-H.main tag.j-i*A.B by ring]
          using A.innerVisible_shift (hm.visible i hi j hj) a
      · intro i hi j hj
        rw [show k+a-H.main tag.j-(i:ℤ)*A.B=(k-H.main tag.j-i*A.B)+a by ring,
          show k+a-H.main tag.j=(k-H.main tag.j)+a by ring,A.inner_shift,A.inner_shift,hm.stable i hi j hj]
      · rw [show k+a-H.main tag.j=(k-H.main tag.j)+a by ring,search_shift]
        exact ObservedMain.suffix_shift T hm.observed a

end OuterStream

namespace InnerStream

open StreamShift BoundarySnapshot SplitMetadata
variable {Alphabet : Type uAlphabet3} {M : Type uM3} {V : Type uV2} {K : Type uK3} {P : Type uP2} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g g' μ : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)
    (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

lemma hypothetical_shift (f : ℤ → Alphabet) (s b t a : ℤ) :
    hypothetical A clock T ρ β early (shift f a) (s+a) (b+a) (t+a)=
      hypothetical A clock T ρ β early f s b t := by
  unfold hypothetical
  rw [show b+a-A.endRule.tail=(b-A.endRule.tail)+a by ring,A.anchor_shift]
  dsimp only
  rw [add_sub_add_right_eq_sub,OuterStream.search_shift,
    show s+a+early (Fin.last g')=(s+early (Fin.last g'))+a by ring,later_shift]

lemma update_shift (f : ℤ → Alphabet) (s b t a : ℤ) (x : V × K) :
    update A clock T ρ β early γ (shift f a) (s+a) (b+a) (t+a) x=
      update A clock T ρ β early γ f s b t x := by
  have hd (i : Fin g') :
      WordIntervals.product T (shift f a) (s+a+early i.castSucc) (s+a+early i.succ)=
      WordIntervals.product T f (s+early i.castSucc) (s+early i.succ) := by
    rw [show s+a+early i.castSucc=(s+early i.castSucc)+a by ring,
      show s+a+early i.succ=(s+early i.succ)+a by ring,StreamShift.product]
  simp only [update,hypothetical_shift,hd]

omit [Fintype M] [Fintype V] in
lemma prefix_shift {slot : Roster M (V × K) K g' μ} {f : ℤ → Alphabet} {s k : ℤ}
    (hp : Prefix T early γ p slot f s k) (a : ℤ) :
    Prefix T early γ p slot (shift f a) (s+a) (k+a) := by
  refine ⟨by have := hp.cut;omega,⟨?_,hp.observed.certificate⟩⟩
  intro i hi
  rw [show s+a+early i.val.castSucc=(s+early i.val.castSucc)+a by ring,
    show s+a+early i.val.succ=(s+early i.val.succ)+a by ring,StreamShift.product]
  exact hp.observed.earlier i hi

lemma suffix_shift {reference slot : Roster M (V × K) K g' μ} {f : ℤ → Alphabet} {k b : ℤ}
    (hq : Suffix A clock T ρ β early p lag reference slot f k b) (a : ℤ) :
    Suffix A clock T ρ β early p lag reference slot (shift f a) (k+a) (b+a) := by
  refine ⟨?_,⟨?_,?_⟩⟩
  · have he : SuffixDecoder.origin p lag (k+a)=fun i => SuffixDecoder.origin p lag k i+a := by
      funext i
      dsimp [SuffixDecoder.origin]
      ring
    rw [he]
    exact SuffixDecoder.test_shift A hq.decoder a
  · intro i hi
    rw [show k+a-p slot+early i.val.castSucc=(k-p slot+early i.val.castSucc)+a by ring,
      show k+a-p slot+early i.val.succ=(k-p slot+early i.val.succ)+a by ring,StreamShift.product]
    exact hq.observed.later i hi
  · rw [show k+a-p slot+lag=(k-p slot+lag)+a by ring,
      show k+a-p slot=(k-p slot)+a by ring,hypothetical_shift]
    exact hq.observed.hypothetical_eq

end InnerStream

namespace WordIntervals

variable {Alphabet : Type uAlphabet4}

noncomputable def stream [Nonempty Alphabet] (w : List Alphabet) : ℤ → Alphabet :=
  Classical.choose (realizes_exists w 0)

lemma stream_realizes [Nonempty Alphabet] (w : List Alphabet) : Realizes w 0 (stream w) :=
  Classical.choose_spec (realizes_exists w 0)

lemma Realizes.same {w : List Alphabet} {f g : ℤ → Alphabet} {s : ℤ}
    (hf : Realizes w s f) (hg : Realizes w s g) : LocalMarkers.AgreesOn f g s (s+w.length) :=
  hf.agrees hg List.prefix_rfl

lemma Realizes.pair_prefix {u v w : List Alphabet} {f : ℤ → Alphabet}
    (hf : Realizes w 0 f) (hpair : u++v <+: w) : Realizes u 0 f :=
  (hf.prefix hpair).append_left

end WordIntervals

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace CanonicalEpisodes.Parameters

open WordIntervals LocalMarkers EpisodeEnd
variable {Alphabet : Type uAlphabet} (C : CanonicalEpisodes.Parameters Alphabet)

lemma end_congr {f g : ℤ → Alphabet} {s b z : ℤ}
    (hv : C.Visible s b z) (he : AgreesOn f g s b)
    (hf : EndAt C.d C.K C.tail f z (C.small f z) b) :
    EndAt C.d C.K C.tail g z (C.small g z) b := by
  rw [←(C.searches_congr hv he).1]
  cases hη : C.small f z with
  | some q => simpa only [hη,EndAt] using hf
  | none =>
    rw [hη] at hf
    obtain ⟨v,hv',hm⟩ := hf
    refine ⟨v,(shortCont_congr (fun x hx hx' => he x (hv.2.2.1.trans hx)
      (hx'.trans_le hv.2.2.2))).mp hv',hm.1,?_,?_⟩
    · intro h
      apply hm.2.1
      exact (he _ (by have := hm.1; have := hv.2.2.1;omega) (by have := C.tail_pos;omega)).trans h
    · intro x hx hx'
      exact (he x (hv.2.2.1.trans hx) (by have := C.tail_pos;omega)).symm.trans (hm.2.2 x hx hx')

lemma complete_realizes {lag : ℤ} {w : List Alphabet} (hw : w∈C.complete lag)
    {f : ℤ → Alphabet} (hf : Realizes w 0 f) :
    C.Visible 0 w.length (lag+C.offset) ∧
      EndAt C.d C.K C.tail f (lag+C.offset) (C.small f (lag+C.offset)) w.length := by
  obtain ⟨g,hg,hv,he⟩ := hw
  refine ⟨hv,C.end_congr hv ?_ he⟩
  simpa only [zero_add] using hg.same hf

end CanonicalEpisodes.Parameters

namespace ExceptionalOrigins.Parameters

open WordIntervals LocalMarkers
variable {Alphabet : Type uAlphabet2} {J : Type uJ} {C : Type uC} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma anchor_congr {f g : ℤ → Alphabet} {s b t Q : ℤ}
    (hv : A.Visible s b t Q) (he : AgreesOn f g s b) :
    A.anchor f (b-A.endRule.tail) t=A.anchor g (b-A.endRule.tail) t := by
  unfold anchor
  rw [(A.endRule.searches_congr hv.base he).2]

lemma failedLanguage_iff {f : ℤ → Alphabet} {w : List Alphabet} {t : ℤ}
    (hw₀ : 0≤A.w₀) (hv : A.Visible 0 w.length t (A.anchor f (w.length-A.endRule.tail) t)) (hf : Realizes w 0 f) :
    w∈A.failedLanguage t ↔ A.Failed f t (A.anchor f (w.length-A.endRule.tail) t) := by
  constructor
  · rintro ⟨g,hg,hg'⟩
    have he : AgreesOn g f 0 w.length := by simpa only [zero_add] using hg.same hf
    have hq := A.anchor_congr hv he
    rw [hq] at hg'
    exact (A.Failed_congr hw₀ hv he).mp hg'
  · exact fun hh => ⟨f,hf,hh⟩

end ExceptionalOrigins.Parameters

namespace OuterStream

open WordIntervals LocalMarkers BoundarySnapshot SplitMetadata
variable {Alphabet : Type uAlphabet3} {M : Type uM} {V : Type uV} {K : Type uK} {P : Type uP} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

omit [Fintype M] [Fintype C] in
lemma snapshot_congr {f f' : ℤ → Alphabet} {s b t : ℤ} (hs : s≤b)
    (he : AgreesOn f f' s b) (hw₀ : 0≤A.w₀)
    (hv : A.Visible s b t (A.anchor f (b-A.endRule.tail) t)) :
    snapshot A T f s b t=snapshot A T f' s b t := by
  have hq := A.anchor_congr hv he
  have hsearch : search A f (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t=
      search A f' (A.residue (A.anchor f' (b-A.endRule.tail) t-t)) t := by
    rw [←hq]
    funext j
    exact A.inner_congr (hv.innerVisible A hw₀ j) he
  apply ClockAffine.Snapshot.ext (product_congr T hs he)
  change factors T f s b _=factors T f' s b _
  rw [←hsearch]
  exact factors_congr T he

lemma update_congr {f f' : ℤ → Alphabet} {s b t : ℤ} (hs : s≤b)
    (he : AgreesOn f f' s b) (hw₀ : 0≤A.w₀)
    (hv : A.Visible s b t (A.anchor f (b-A.endRule.tail) t)) (x : V) :
    update A clock T ρ β f s b t x=update A clock T ρ β f' s b t x := by
  unfold update
  rw [A.anchor_congr hv he,snapshot_congr A T hs he hw₀ hv]

noncomputable def wordUpdate [Nonempty Alphabet] (lag : ℤ) (w : List Alphabet) (x : V) : V :=
  update A clock T ρ β (stream w) 0 w.length lag x

lemma wordUpdate_eq [Nonempty Alphabet] {lag : ℤ} {w : List Alphabet} {f : ℤ → Alphabet}
    (hf : Realizes w 0 f) (hw₀ : 0≤A.w₀)
    (hv : A.Visible 0 w.length lag (A.anchor f (w.length-A.endRule.tail) lag)) (x : V) :
    wordUpdate A clock T ρ β lag w x=update A clock T ρ β f 0 w.length lag x := by
  symm
  apply update_congr A clock T ρ β (Int.natCast_nonneg _) _ hw₀ hv
  simpa only [zero_add] using hf.same (stream_realizes w)

end OuterStream

namespace InnerStream

open WordIntervals LocalMarkers SplitMetadata
variable {Alphabet : Type uAlphabet4} {M : Type uM2} {V : Type uV2} {K : Type uK2} {P : Type uP2} {C : Type uC3} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g g' : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)

lemma update_congr (hm : Monotone early) (h₀ : early 0=0)
    {f f' : ℤ → Alphabet} {s b t : ℤ} (hb : s+early (Fin.last g')≤b)
    (he : AgreesOn f f' s b) (hw₀ : 0≤A.w₀)
    (hv : A.Visible s b t (A.anchor f (b-A.endRule.tail) t)) (x : V × K) :
    update A clock T ρ β early γ f s b t x=update A clock T ρ β early γ f' s b t x := by
  have hmin (i : Fin (g'+1)) : 0≤early i := by rw [←h₀];exact hm (Fin.zero_le i)
  have hψ := hypothetical_congr A clock T ρ β early (by have := hmin (Fin.last g');omega)
    hb he (A.anchor_congr hv he) (fun j => hv.innerVisible A hw₀ j)
  have hd : (fun i : Fin g' => product T f (s+early i.castSucc) (s+early i.succ))=
      fun i : Fin g' => product T f' (s+early i.castSucc) (s+early i.succ) := by
    funext i
    apply product_congr T (by have := hm (Fin.castSucc_le_succ i);omega)
    intro z hz hz'
    exact he z (by have := hmin i.castSucc;omega) (by have := hm (Fin.le_last i.succ);omega)
  unfold update
  rw [hψ,hd]

noncomputable def wordUpdate [Nonempty Alphabet] (lag : ℤ) (w : List Alphabet) (x : V × K) : V × K :=
  update A clock T ρ β early γ (stream w) 0 w.length lag x

lemma wordUpdate_eq [Nonempty Alphabet] (hm : Monotone early) (h₀ : early 0=0)
    {lag : ℤ} {w : List Alphabet} {f : ℤ → Alphabet} (hb : early (Fin.last g')≤w.length)
    (hf : Realizes w 0 f) (hw₀ : 0≤A.w₀)
    (hv : A.Visible 0 w.length lag (A.anchor f (w.length-A.endRule.tail) lag)) (x : V × K) :
    wordUpdate A clock T ρ β early γ lag w x=update A clock T ρ β early γ f 0 w.length lag x := by
  symm
  apply update_congr A clock T ρ β early γ hm h₀ (by simpa only [zero_add] using hb) _ hw₀ hv
  simpa only [zero_add] using hf.same (stream_realizes w)

end InnerStream

namespace CanonicalEpisodes.Parameters

open WordIntervals
variable {Alphabet : Type uAlphabet5} (C : CanonicalEpisodes.Parameters Alphabet)

lemma subset_height [Finite Alphabet] {L : Language Alphabet} (lag : ℤ)
    (hreg : L.IsRegular) (hL : L≤C.complete lag) : HasHeightAtMost L 1 := by
  apply C.ending_height L hreg lag.natAbs
  intro w hw
  obtain ⟨f,hf,_,he⟩ := hL hw
  exact ⟨f,lag,hf,by simp only [Int.natCast_natAbs];exact le_rfl,he⟩

lemma complete_height [Finite Alphabet] (lag : ℤ) : HasHeightAtMost (C.complete lag) 1 :=
  C.subset_height lag (C.complete_regular lag) le_rfl

end CanonicalEpisodes.Parameters

namespace ExceptionalOrigins.Parameters

variable {Alphabet : Type uAlphabet6} {J : Type uJ2} {C : Type uC4} (A : ExceptionalOrigins.Parameters Alphabet J C)

def failedDomain (lag : ℤ) : Language Alphabet := A.endRule.complete lag ⊓ A.failedLanguage lag

lemma failedDomain_subset (lag : ℤ) : A.failedDomain lag≤A.endRule.complete lag := inf_le_left

lemma failedDomain_height [Finite Alphabet] [Fintype J] (n : ℕ) (hn : 0<n)
    (hφ : A.φ (n:ℤ)=0) (hw₀ : 0≤A.w₀) (lag : ℤ) : HasHeightAtMost (A.failedDomain lag) 1 :=
  A.endRule.subset_height lag ((A.endRule.complete_regular lag).inf (A.failed_regular n hn hφ hw₀ lag))
    (A.failedDomain_subset lag)

end ExceptionalOrigins.Parameters

namespace WordIntervals

variable {Alphabet : Type uAlphabet7}

lemma realizes_cut {w : List Alphabet} {f : ℤ → Alphabet} (hf : Realizes w 0 f)
    {k : ℤ} (hk : 0≤k) (hkb : k≤w.length) :
    ∃ u v : List Alphabet, w=u++v ∧ (u.length:ℤ)=k ∧ Realizes u 0 f ∧ Realizes v k f := by
  let u := w.take k.toNat
  let v := w.drop k.toNat
  have hw : w=u++v := (List.take_append_drop k.toNat w).symm
  have hu : (u.length:ℤ)=k := by simp only [u,List.length_take];omega
  have hh : Realizes (u++v) 0 f := hw ▸ hf
  refine ⟨u,v,hw,hu,hh.append_left,?_⟩
  simpa only [zero_add,hu] using hh.append_right

lemma prefix_eq_of_length {u v w : List Alphabet} (hu : u<+:w) (hv : v<+:w)
    (hl : u.length=v.length) : u=v := by
  rcases List.prefix_or_prefix_of_prefix hu hv with h|h
  · exact h.eq_of_length hl
  · exact (h.eq_of_length hl.symm).symm

end WordIntervals

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace OuterStream

open WordIntervals LocalMarkers StreamShift StreamSplice SplitMetadata EpisodeAlgebra
variable {Alphabet : Type uAlphabet} {M : Type uM} {V : Type uV} {K : Type uK} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

lemma word_pair {tag : Tag M V g A.B} {f : ℤ → Alphabet} {lag reference k : ℤ}
    {w : List Alphabet} (hf : Realizes w 0 f)
    (hp : Prefix A H clock T ρ β tag f 0 lag k)
    (hq : Suffix A H clock T ρ reference tag f k w.length) :
    w∈prefixLanguage A H clock T ρ β lag tag.input * suffixLanguage A H clock T ρ reference tag.output := by
  obtain ⟨u,v,hw,hu,huf,hvf⟩ := realizes_cut hf hp.positive.le hq.ordered
  have hvlen : (v.length:ℤ)=(w.length:ℤ)-k := by rw [hw,List.length_append,Nat.cast_add];omega
  apply Language.mem_mul.mpr
  refine ⟨u,?_,v,?_,hw.symm⟩
  · exact Language.mem_iSup.mpr ⟨⟨tag,rfl⟩,f,huf,by simpa only [hu] using hp⟩
  · refine Language.mem_iSup.mpr ⟨⟨tag,rfl⟩,shift f (-k),?_,?_⟩
    · simpa only [add_neg_cancel] using StreamShift.realizes hvf (-k)
    · simpa only [add_neg_cancel,←sub_eq_add_neg,←hvlen] using suffix_shift A H clock T ρ hq (-k)

lemma word_sound [Nonempty Alphabet] (G : Geometry A H) (lag reference : ℤ) (hw₀ : 0≤A.w₀)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      A.Visible 0 b lag (A.anchor f (b-A.endRule.tail) lag)) :
    SplitSound (A.endRule.complete lag) (wordUpdate A clock T ρ β lag)
      (prefixLanguage A H clock T ρ β lag) (suffixLanguage A H clock T ρ reference) := by
  intro x y es u v hes hu hv hpair
  obtain ⟨a,fp,hfp,hp⟩ := Language.mem_iSup.mp hu
  obtain ⟨btag,fq,hfq,hq⟩ := Language.mem_iSup.mp hv
  cases es with
  | nil =>
    have hu0 : u.length=0 := by have := hpair.length_le;simp only [List.flatten_nil,List.length_nil,List.length_append] at this;omega
    have hh := hp.positive
    simp only [hu0,Nat.cast_zero,lt_self_iff_false] at hh
  | cons e fs =>
    have he : e∈A.endRule.complete lag := hes e (by simp)
    let f := stream ((e::fs).flatten)
    have hf : Realizes ((e::fs).flatten) 0 f := stream_realizes _
    have hep : e<+:(e::fs).flatten := by exact ⟨fs.flatten,rfl⟩
    have hef := hf.prefix hep
    have hend := (A.endRule.complete_realizes he hef).2
    have hvis := hvisible f e.length hend
    have hpairf := hf.prefix hpair
    have hpre : AgreesOn fp f 0 u.length := by simpa only [zero_add] using hfp.same hpairf.append_left
    have hfv : Realizes v (u.length:ℤ) f := by simpa only [zero_add] using hpairf.append_right
    have hqs : Suffix A H clock T ρ reference btag.val (shift fq u.length) u.length
        ((u.length:ℤ)+v.length) := by
      simpa only [zero_add,add_comm (v.length:ℤ)] using suffix_shift A H clock T ρ hq u.length
    have hqfs : Realizes v (u.length:ℤ) (shift fq u.length) := by
      simpa only [zero_add] using StreamShift.realizes hfq u.length
    have hsuf : AgreesOn (shift fq u.length) f u.length
        (min (e.length:ℤ) ((u.length:ℤ)+v.length)) := by
      intro z hz hz'
      exact hqfs.same hfv z hz (hz'.trans_le (min_le_right _ _))
    obtain ⟨hb,hup⟩ := pair_sound clock T ρ β G hp hqs hend hpre hsuf
    have huv : u++v=e := prefix_eq_of_length hpair hep (by simp only [List.length_append];exact_mod_cast hb.symm)
    refine ⟨e,fs,rfl,huv,?_⟩
    rw [wordUpdate_eq A clock T ρ β hef hw₀ hvis]
    simpa only [a.property,btag.property] using hup

lemma word_available [Nonempty Alphabet] (lag reference : ℤ) (hw₀ : 0≤A.w₀)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      A.Visible 0 b lag (A.anchor f (b-A.endRule.tail) lag))
    (havail : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      ¬A.Failed f lag (A.anchor f (b-A.endRule.tail) lag) → ∀ x,
      ∃ tag k, tag.input=x ∧ Prefix A H clock T ρ β tag f 0 lag k ∧
        Suffix A H clock T ρ reference tag f k b ∧
        tag.output=update A clock T ρ β f 0 b lag x) :
    SplitAvailable (A.endRule.complete lag) (A.failedDomain lag) (wordUpdate A clock T ρ β lag)
      (prefixLanguage A H clock T ρ β lag) (suffixLanguage A H clock T ρ reference) := by
  intro e he hn x
  let f := stream e
  have hf : Realizes e 0 f := stream_realizes e
  have hend := (A.endRule.complete_realizes he hf).2
  have hvis := hvisible f e.length hend
  have hfail : ¬A.Failed f lag (A.anchor f (e.length-A.endRule.tail) lag) := by
    intro h
    exact hn ⟨he,(A.failedLanguage_iff hw₀ hvis hf).mpr h⟩
  obtain ⟨tag,k,hx,hp,hq,hy⟩ := havail f e.length hend hfail x
  have hh := word_pair A H clock T ρ β hf hp hq
  rw [hx,hy] at hh
  exact hh

end OuterStream

namespace InnerStream

open WordIntervals LocalMarkers StreamShift StreamSplice SplitMetadata EpisodeAlgebra
variable {Alphabet : Type uAlphabet2} {M : Type uM2} {V : Type uV2} {K : Type uK2} {P : Type uP2} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype K] [Fintype P] [Fintype C] {g g' μ : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)
    (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

omit [Fintype K] in
lemma word_pair {slot reference : Roster M (V × K) K g' μ} {f : ℤ → Alphabet} {k : ℤ}
    {w : List Alphabet} (hf : Realizes w 0 f) (hk : 0≤k) (hkb : k≤w.length)
    (hp : Prefix T early γ p slot f 0 k)
    (hq : Suffix A clock T ρ β early p lag reference slot f k w.length) :
    w∈prefixLanguage T early γ p slot.1.input * suffixLanguage A clock T ρ β early p lag reference slot.1.output := by
  obtain ⟨u,v,hw,hu,huf,hvf⟩ := realizes_cut hf hk hkb
  have hvlen : (v.length:ℤ)=(w.length:ℤ)-k := by rw [hw,List.length_append,Nat.cast_add];omega
  apply Language.mem_mul.mpr
  refine ⟨u,?_,v,?_,hw.symm⟩
  · exact Language.mem_iSup.mpr ⟨⟨slot,rfl⟩,f,huf,by simpa only [hu] using hp⟩
  · refine Language.mem_iSup.mpr ⟨⟨slot,rfl⟩,shift f (-k),?_,?_⟩
    · simpa only [add_neg_cancel] using StreamShift.realizes hvf (-k)
    · simpa only [add_neg_cancel,←sub_eq_add_neg,←hvlen] using suffix_shift A clock T ρ β early p lag hq (-k)

omit [Monoid M] [Fintype M] [Fintype V] [Fintype K] in
lemma block_bounds (hearly : Monotone early) (h₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (slot : Roster M (V × K) K g' μ) : 0<p slot ∧ p slot<early (Fin.last g') := by
  have hlo := hearly (Fin.zero_le slot.1.j.castSucc)
  have hhi := hearly (Fin.le_last slot.1.j.succ)
  have hslot := hblock slot
  rw [h₀] at hlo
  exact ⟨hlo.trans_lt hslot.1,hslot.2.trans_le hhi⟩

omit [Fintype K] in
lemma word_sound [Nonempty Alphabet] (reference : Roster M (V × K) K g' μ)
    (hearly : StrictMono early) (h₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (hw₀ : 0≤A.w₀)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      A.Visible 0 b lag (A.anchor f (b-A.endRule.tail) lag))
    (hroster : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b → ∀ a i,
      A.Visible (p a) b (SuffixDecoder.origin p lag (p a) i)
        (A.anchor f (b-A.endRule.tail) (SuffixDecoder.origin p lag (p a) i)))
    (hover : ∀ a, (A.endRule.d:ℤ)^2≤A.endRule.K-|p a-p reference|)
    (hover' : ∀ a, |p a-p reference|<A.endRule.K)
    (hendlast : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b → early (Fin.last g')≤b) :
    SplitSound (A.failedDomain lag) (wordUpdate A clock T ρ β early γ lag)
      (prefixLanguage T early γ p) (suffixLanguage A clock T ρ β early p lag reference) := by
  intro x y es u v hes hu hv hpair
  obtain ⟨a,fp,hfp,hp⟩ := Language.mem_iSup.mp hu
  obtain ⟨btag,fq,hfq,hq⟩ := Language.mem_iSup.mp hv
  have hcut : (u.length:ℤ)=p a.val := by simpa only [zero_add] using hp.cut
  cases es with
  | nil =>
    have hu0 : u.length=0 := by have := hpair.length_le;simp only [List.flatten_nil,List.length_nil,List.length_append] at this;omega
    have hpos := (block_bounds early p hearly.monotone h₀ hblock a.val).1
    simp only [hu0,Nat.cast_zero] at hcut
    omega
  | cons e fs =>
    have he : e∈A.failedDomain lag := hes e (by simp)
    let f := stream ((e::fs).flatten)
    have hf : Realizes ((e::fs).flatten) 0 f := stream_realizes _
    have hep : e<+:(e::fs).flatten := ⟨fs.flatten,rfl⟩
    have hef := hf.prefix hep
    have hend := (A.endRule.complete_realizes he.1 hef).2
    have hvis := hvisible f e.length hend
    have hfailed := (A.failedLanguage_iff hw₀ hvis hef).mp he.2
    have hlast := hendlast f e.length hend
    have hpairf := hf.prefix hpair
    have hpre : AgreesOn fp f 0 u.length := by simpa only [zero_add] using hfp.same hpairf.append_left
    have hfv : Realizes v (u.length:ℤ) f := by simpa only [zero_add] using hpairf.append_right
    have hqs : Suffix A clock T ρ β early p lag reference btag.val (shift fq u.length) u.length
        ((u.length:ℤ)+v.length) := by
      simpa only [zero_add,add_comm (v.length:ℤ)] using suffix_shift A clock T ρ β early p lag hq u.length
    have hqfs : Realizes v (u.length:ℤ) (shift fq u.length) := by
      simpa only [zero_add] using StreamShift.realizes hfq u.length
    have hsuf : AgreesOn f (shift fq u.length) u.length
        (min (e.length:ℤ) ((u.length:ℤ)+v.length)) := by
      intro z hz hz'
      exact hfv.same hqfs z hz (hz'.trans_le (min_le_right _ _))
    have hrv : ∀ i, A.Visible (u.length:ℤ) e.length (SuffixDecoder.origin p lag u.length i)
        (A.anchor f (e.length-A.endRule.tail) (SuffixDecoder.origin p lag u.length i)) := by
      rw [hcut]
      exact hroster f e.length hend a.val
    obtain ⟨_,hb,hup⟩ := pair_sound A clock T ρ β early γ p lag hearly h₀ hblock hw₀ hp hqs hrv
      (hover a.val) (hover' a.val) (by simpa only [zero_add] using hlast)
      (by simpa only [zero_add] using hend) (by simpa only [zero_add] using hfailed) hpre hsuf
    have huv : u++v=e := prefix_eq_of_length hpair hep (by simp only [List.length_append];exact_mod_cast hb)
    refine ⟨e,fs,rfl,huv,?_⟩
    rw [wordUpdate_eq A clock T ρ β early γ hearly.monotone h₀ hlast hef hw₀ hvis]
    simpa only [zero_add,a.property,btag.property] using hup

omit [Fintype K] in
lemma word_available [Nonempty Alphabet] (reference : Roster M (V × K) K g' μ)
    (hearly : Monotone early) (h₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (hw₀ : 0≤A.w₀)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      A.Visible 0 b lag (A.anchor f (b-A.endRule.tail) lag))
    (hendlast : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b → early (Fin.last g')≤b)
    (havail : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      A.Failed f lag (A.anchor f (b-A.endRule.tail) lag) → ∀ x,
      ∃ slot k, slot.1.input=x ∧ Prefix T early γ p slot f 0 k ∧
        Suffix A clock T ρ β early p lag reference slot f k b ∧
        slot.1.output=update A clock T ρ β early γ f 0 b lag x) :
    SplitAvailable (A.failedDomain lag) 0 (wordUpdate A clock T ρ β early γ lag)
      (prefixLanguage T early γ p) (suffixLanguage A clock T ρ β early p lag reference) := by
  intro e he _ x
  let f := stream e
  have hf : Realizes e 0 f := stream_realizes e
  have hend := (A.endRule.complete_realizes he.1 hf).2
  have hvis := hvisible f e.length hend
  have hfail := (A.failedLanguage_iff hw₀ hvis hf).mp he.2
  obtain ⟨slot,k,hx,hp,hq,hy⟩ := havail f e.length hend hfail x
  have hc : k=p slot := by simpa only [zero_add] using hp.cut
  have hbounds := block_bounds early p hearly h₀ hblock slot
  have hh := word_pair A clock T ρ β early γ p lag hf (by omega)
    (by have := hendlast f e.length hend;omega) hp hq
  rw [hx,hy] at hh
  exact hh

end InnerStream
namespace EpisodeAlgebra

variable {Alphabet : Type uAlphabet3} {S : Type uS} {U : Type uU}

lemma updateWord_congr {D : Language Alphabet} {G G' : List Alphabet → S → S}
    (heq : ∀ e∈D, ∀ x, G e x=G' e x) {es : List (List Alphabet)} (he : AllIn D es) (x : S) :
    updateWord G x es=updateWord G' x es := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    rw [updateWord_cons,updateWord_cons,heq e (he e (by simp))]
    exact ih (fun a ha => he a (by simp [ha])) _

lemma graph_congr {D : Language Alphabet} {G G' : List Alphabet → S → S}
    (heq : ∀ e∈D, ∀ x, G e x=G' e x) (x y : S) : graph D G x y=graph D G' x y := by
  ext w
  constructor <;> rintro ⟨es,he,hw,hxy⟩
  · exact ⟨es,he,hw,(updateWord_congr heq he x).symm.trans hxy⟩
  · exact ⟨es,he,hw,(updateWord_congr heq he x).trans hxy⟩

lemma updateWord_embed {D : Language Alphabet} {G : List Alphabet → S → S}
    {J : List Alphabet → U → U} (ι : S → U)
    (heq : ∀ e∈D, ∀ x, J e (ι x)=ι (G e x)) {es : List (List Alphabet)}
    (he : AllIn D es) (x : S) : updateWord J (ι x) es=ι (updateWord G x es) := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    rw [updateWord_cons,updateWord_cons,heq e (he e (by simp))]
    exact ih (fun a ha => he a (by simp [ha])) _

lemma graph_embed {D : Language Alphabet} {G : List Alphabet → S → S}
    {J : List Alphabet → U → U} (ι : S → U) (hi : Function.Injective ι)
    (heq : ∀ e∈D, ∀ x, J e (ι x)=ι (G e x)) (x y : S) :
    graph D G x y=graph D J (ι x) (ι y) := by
  ext w
  constructor <;> rintro ⟨es,he,hw,hxy⟩
  · exact ⟨es,he,hw,(updateWord_embed ι heq he x).trans (congrArg ι hxy)⟩
  · exact ⟨es,he,hw,hi ((updateWord_embed ι heq he x).symm.trans hxy)⟩

end EpisodeAlgebra

namespace OuterStream

open WordIntervals SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet4} {M : Type uM3} {V : Type uV3} {K : Type uK3} {P : Type uP3} {C : Type uC3} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

noncomputable def wordShift [Nonempty Alphabet] (lag : ℤ) (w : List Alphabet) : V :=
  ClockAffine.shift clock ρ β Tag.input Tag.output
    (A.φ (A.anchor (stream w) (w.length-A.endRule.tail) lag-lag))
    (snapshot A T (stream w) 0 w.length lag)

lemma wordUpdate_affine [Nonempty Alphabet] (lag : ℤ) :
    wordUpdate A clock T ρ β lag=
      AffineRecovery.affine (fun w => (ρ (T w)).toAddMonoidHom) (wordShift A clock T ρ β lag) := by
  funext w x
  have hp : product T (stream w) 0 w.length=T w := by
    unfold product
    rw [show (w.length:ℤ)=0+(w.length:ℤ) by omega,realizes_piece (stream_realizes w)]
  change ρ (product T (stream w) 0 w.length) x+_=ρ (T w) x+_
  rw [hp]
  rfl

end OuterStream

namespace InnerStream

open WordIntervals SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet5} {M : Type uM4} {V : Type uV4} {K : Type uK4} {P : Type uP4} {C : Type uC4} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g g' : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)

noncomputable def wordLinear [Nonempty Alphabet] (lag : ℤ) (w : List Alphabet) : V × K →ₗ[K] V × K :=
  ObservedInner.table (hypothetical A clock T ρ β early (stream w) 0 w.length lag)
    (fun i : Fin g' => product T (stream w) (early i.castSucc) (early i.succ))

noncomputable def wordShift [Nonempty Alphabet] (lag : ℤ) (w : List Alphabet) : V × K :=
  γ (hypothetical A clock T ρ β early (stream w) 0 w.length lag)
    (fun i : Fin g' => product T (stream w) (early i.castSucc) (early i.succ))

lemma wordUpdate_affine [Nonempty Alphabet] (lag : ℤ) :
    wordUpdate A clock T ρ β early γ lag=
      AffineRecovery.affine (fun w => (wordLinear A clock T ρ β early lag w).toAddMonoidHom)
        (wordShift A clock T ρ β early γ lag) := by
  funext w x
  simp only [wordUpdate,update,wordLinear,wordShift,zero_add,AffineRecovery.affine]
  rfl

lemma wordLinear_lift [Nonempty Alphabet] (hm : Monotone early) (h₀ : early 0=0)
    {lag : ℤ} {w : List Alphabet} (hb : early (Fin.last g')≤w.length)
    (hstart : ∀ i q, A.inner (stream w) i
      (A.residue (A.anchor (stream w) (w.length-A.endRule.tail) lag-lag)) lag=some q →
      early (Fin.last g')≤q) :
    wordLinear A clock T ρ β early lag w=
      Homogenization.lift (ρ (T w)) (OuterStream.wordShift A clock T ρ β lag w) := by
  have hprod := product_chain T (stream w) early hm
  rw [h₀] at hprod
  have hlast : 0≤early (Fin.last g') := by rw [←h₀];exact hm (Fin.zero_le _)
  have hh := hypothetical_actual A clock T ρ β early (f := stream w) (s := 0) (b := w.length)
    (t := lag) (by simpa only [zero_add] using hlast) (by simpa only [zero_add] using hb)
    (by simpa only [zero_add] using hstart)
  have hp : product T (stream w) 0 w.length=T w := by
    unfold product
    rw [show (w.length:ℤ)=0+(w.length:ℤ) by omega,realizes_piece (stream_realizes w)]
  simpa only [wordLinear,ObservedInner.table,hprod,zero_add,hp,OuterStream.wordShift] using hh

lemma linear_graph_recovery [Nonempty Alphabet] (hm : Monotone early) (h₀ : early 0=0)
    (lag : ℤ) (H : ℕ)
    (hb : ∀ w∈A.failedDomain lag, early (Fin.last g')≤w.length)
    (hstart : ∀ w∈A.failedDomain lag, ∀ i q, A.inner (stream w) i
      (A.residue (A.anchor (stream w) (w.length-A.endRule.tail) lag-lag)) lag=some q →
      early (Fin.last g')≤q)
    (hgraph : ∀ x y, HasHeightAtMost (EpisodeAlgebra.graph (A.failedDomain lag)
      (fun w => wordLinear A clock T ρ β early lag w) x y) H) (x y : V) :
    HasHeightAtMost (EpisodeAlgebra.graph (A.failedDomain lag)
      (OuterStream.wordUpdate A clock T ρ β lag) x y) H := by
  rw [EpisodeAlgebra.graph_embed (fun v : V => (v,(1:K))) (by intro a b h;exact congrArg Prod.fst h)
    (J := fun w => wordLinear A clock T ρ β early lag w)]
  · exact hgraph (x,1) (y,1)
  · intro w hw z
    rw [wordLinear_lift A clock T ρ β early hm h₀ (hb w hw) (hstart w hw),
      Homogenization.lift_apply_one,OuterStream.wordUpdate_affine]
    rfl

end InnerStream

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace SourceSchedule.Early

open WordIntervals SplitMetadata LocalMarkers
variable {Alphabet : Type uAlphabet} {T : Type uT} {P : Type uP} {C : Type uC} [Fintype T] [Fintype P] [Fintype C]
    {g' B size : ℕ} {clock : RobustClock.Specification T P C}
    {label : P → Fin g'} {reserved : P → ℤ}
    (S : Early (Alphabet := Alphabet) clock B size label reserved)
    (g : ℕ) (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))
    (hB : 0<B)

lemma clock_period : (S.parameters g L hB).φ (S.period:ℤ)=0 :=
  PeriodicClock.period S.denominator S.numerator (fun c => (S.prime c).pos)

lemma episode_last {f : ℤ → Alphabet} {b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (L.lag+L.endRule.offset) (L.endRule.small f (L.lag+L.endRule.offset)) b) :
    S.β (Fin.last g')≤b := by
  have hb := L.complete_lower (s := 0) (by simpa only [zero_add] using he)
  have hlag := L.lag_margin
  have hoff := L.offset_margin
  have hE := (S.envelope_pos g).le
  have hw := (S.sweepWidth_pos g).le
  have hr := L.radius_nonneg
  have hwidth := L.endRule.width_nonneg
  have hK : (0:ℤ)≤L.endRule.K := Int.natCast_nonneg _
  omega

lemma episode_visible {f : ℤ → Alphabet} {b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (L.lag+L.endRule.offset) (L.endRule.small f (L.lag+L.endRule.offset)) b) :
    (S.parameters g L hB).Visible 0 b L.lag
      ((S.parameters g L hB).anchor f (b-L.endRule.tail) L.lag) := by
  have hh := S.actual_visible g L hB (s := 0) (δ := 0)
    (Q := (S.parameters g L hB).anchor f (b-L.endRule.tail) L.lag)
    (by simpa only [abs_zero] using (S.sweepWidth_pos g).le)
    (by simpa only [zero_add] using he)
  simp only [zero_add,add_zero] at hh
  exact hh.mono _ S.earlyLast_nonneg (le_refl b)

lemma episode_inner_start {f : ℤ → Alphabet} {b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (L.lag+L.endRule.offset) (L.endRule.small f (L.lag+L.endRule.offset)) b)
    (i : Fin (g+1)) (q : ℤ)
    (hq : (S.parameters g L hB).inner f i
      ((S.parameters g L hB).residue ((S.parameters g L hB).anchor f (b-L.endRule.tail) L.lag-L.lag))
      L.lag=some q) : S.β (Fin.last g')≤q := by
  have hv := S.actual_visible g L hB (s := 0) (δ := 0)
    (Q := (S.parameters g L hB).anchor f (b-L.endRule.tail) L.lag)
    (by simpa only [abs_zero] using (S.sweepWidth_pos g).le)
    (by simpa only [zero_add] using he)
  have hh := (hv.inner i).1
  have hq' := (S.parameters g L hB).inner_bounds hq
  have hr : 0≤(S.parameters g L hB).innerRule.r :=
    (Int.natCast_nonneg _).trans (S.parameters g L hB).innerRule.radius_ge
  have hw : 0≤(S.parameters g L hB).w₀ := Int.natCast_nonneg _
  simp only [zero_add,add_zero] at hh
  omega

end SourceSchedule.Early
namespace SourceSchedule.Early

open WordIntervals SplitMetadata LocalMarkers EpisodeAlgebra
variable {Alphabet : Type uAlphabet2} {M : Type uM} {V : Type uV} {K : Type uK} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype K] [Fintype C] [Finite Alphabet] [Nonempty Alphabet]
    {g g' μ B : ℕ}
    {clock : RobustClock.Specification (Tag M V g B) (Roster M (V × K) K g' μ) C}
    {reserved : Roster M (V × K) K g' μ → ℤ}
    (S : Early (Alphabet := Alphabet) clock B (Fintype.card M) (fun i => i.1.j) reserved)
    (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))
    (hB : 0<B) (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)

lemma inner_graph_height
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (reserved i-reserved j)%B ≠ (reserved i'-reserved j')%B)
    (hμ : 20*(10000000*Real.log (2*Fintype.card (Tag M V g B))+4*(g+1))+10<μ)
    (hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ))
    (reference : Roster M (V × K) K g' μ) (x y : V × K) :
    HasHeightAtMost (graph ((S.parameters g L hB).failedDomain L.lag)
      (InnerStream.wordUpdate (S.parameters g L hB) clock T ρ β S.β γ L.lag) x y) 2 := by
  let A := S.parameters g L hB
  have hw₀ : 0≤A.w₀ := Int.natCast_nonneg _
  have hm := L.decoder_margins hB S.diameter_pos.le (S.sweepWidth_pos g).le
  have hs : SplitSound (A.failedDomain L.lag) (InnerStream.wordUpdate A clock T ρ β S.β γ L.lag)
      (InnerStream.prefixLanguage T S.β γ S.p)
      (InnerStream.suffixLanguage A clock T ρ β S.β S.p L.lag reference) := by
    apply InnerStream.word_sound A clock T ρ β S.β γ S.p L.lag reference
        S.β_strict S.β_zero S.block hw₀ (fun f b he => S.episode_visible g L hB he)
    · intro f b he a i
      have hh := S.roster_visible L hB (s := 0) (by simpa only [A,parameters,zero_add] using he) a i
      convert hh using 1 <;> simp only [SuffixDecoder.origin,zero_add] <;> congr 1 <;> ring
    · intro a
      have hh := difference_bound S.p a reference
      change |S.p a-S.p reference|≤S.diameter at hh
      change (L.endRule.d:ℤ)^2≤L.endRule.K-_
      omega
    · intro a
      exact (difference_bound S.p a reference).trans_lt hm.2.2
    · exact fun f b he => S.episode_last g L he
  have ha : SplitAvailable (A.failedDomain L.lag) 0 (InnerStream.wordUpdate A clock T ρ β S.β γ L.lag)
      (InnerStream.prefixLanguage T S.β γ S.p)
      (InnerStream.suffixLanguage A clock T ρ β S.β S.p L.lag reference) := by
    apply InnerStream.word_available A clock T ρ β S.β γ S.p L.lag reference
      S.β_strict.monotone S.β_zero S.block hw₀ (fun f b he => S.episode_visible g L hB he) (fun f b he => S.episode_last g L he)
    intro f b he hf x
    simpa only [zero_add] using S.inner_available L hB T ρ β γ hmod hμ hγ reference
      (s := 0) (by simpa only [A,parameters,zero_add] using he) (by simpa only [A,parameters,zero_add] using hf) x
  exact split_height (L.endRule.prefix_code L.lag) (A.failedDomain_subset L.lag) bot_le
    (InnerStream.wordUpdate A clock T ρ β S.β γ L.lag)
    (InnerStream.prefixLanguage T S.β γ S.p)
    (InnerStream.suffixLanguage A clock T ρ β S.β S.p L.lag reference) hs ha 0
    (A.failedDomain_height S.period S.period_pos (S.clock_period g L hB) hw₀ L.lag)
    (fun x => (InnerStream.prefix_height T S.β γ S.p x).mono (by decide))
    (InnerStream.suffix_height A clock T ρ β S.β S.p L.lag S.period S.period_pos
      (S.clock_period g L hB) hw₀ reference)
    (empty_skip_height _) x y

lemma failed_outer_graph_height
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (reserved i-reserved j)%B ≠ (reserved i'-reserved j')%B)
    (hμ : 20*(10000000*Real.log (2*Fintype.card (Tag M V g B))+4*(g+1))+10<μ)
    (hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ))
    (reference : Roster M (V × K) K g' μ) (x y : V) :
    HasHeightAtMost (graph ((S.parameters g L hB).failedDomain L.lag)
      (OuterStream.wordUpdate (S.parameters g L hB) clock T ρ β L.lag) x y) 2 := by
  let A := S.parameters g L hB
  have hG := S.inner_graph_height L hB T ρ β γ hmod hμ hγ reference
  have hlin := AffineRecovery.recovery_height (L.endRule.prefix_code L.lag)
    (A.failedDomain_subset L.lag)
    (fun w => (InnerStream.wordLinear A clock T ρ β S.β L.lag w).toAddMonoidHom)
    (InnerStream.wordShift A clock T ρ β S.β γ L.lag) 2 (fun x y => by
      rw [←InnerStream.wordUpdate_affine A clock T ρ β S.β γ L.lag]
      exact hG x y)
  apply InnerStream.linear_graph_recovery A clock T ρ β S.β S.β_strict.monotone S.β_zero L.lag 2
    (fun w hw => S.episode_last g L (A.endRule.complete_realizes hw.1 (stream_realizes w)).2)
    (fun w hw => S.episode_inner_start g L hB (A.endRule.complete_realizes hw.1 (stream_realizes w)).2)
    hlin x y

lemma outer_graph_height
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (reserved i-reserved j)%B ≠ (reserved i'-reserved j')%B)
    (hμ : 20*(10000000*Real.log (2*Fintype.card (Tag M V g B))+4*(g+1))+10<μ)
    (hβ : ∀ a c, ShiftTableProperty g (ClockAffine.productTable ρ a c) (β a c))
    (hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ))
    (innerReference : Roster M (V × K) K g' μ) (outerReference : ℤ)
    (hr : outerReference∈(S.cuts g).offsets) (x y : V) :
    HasHeightAtMost (graph (L.endRule.complete L.lag)
      (OuterStream.wordUpdate (S.parameters g L hB) clock T ρ β L.lag) x y) 3 := by
  let A := S.parameters g L hB
  have hw₀ : 0≤A.w₀ := Int.natCast_nonneg _
  have hs := OuterStream.word_sound A (S.cuts g) clock T ρ β (S.geometry g L hB)
    L.lag outerReference hw₀ (fun f b he => S.episode_visible g L hB he)
  have ha : SplitAvailable (L.endRule.complete L.lag) (A.failedDomain L.lag)
      (OuterStream.wordUpdate A clock T ρ β L.lag)
      (OuterStream.prefixLanguage A (S.cuts g) clock T ρ β L.lag)
      (OuterStream.suffixLanguage A (S.cuts g) clock T ρ outerReference) := by
    apply OuterStream.word_available A (S.cuts g) clock T ρ β L.lag outerReference hw₀
      (fun f b he => S.episode_visible g L hB he)
    intro f b he hn x
    simpa only [A,parameters,zero_add] using S.outer_available L hB T ρ β hβ hr
      (s := 0) (by simpa only [A,parameters,zero_add] using he) (by simpa only [A,parameters,zero_add] using hn) x
  exact split_height (L.endRule.prefix_code L.lag) le_rfl (A.failedDomain_subset L.lag)
    (OuterStream.wordUpdate A clock T ρ β L.lag)
    (OuterStream.prefixLanguage A (S.cuts g) clock T ρ β L.lag)
    (OuterStream.suffixLanguage A (S.cuts g) clock T ρ outerReference) hs ha 2
    (L.endRule.complete_height L.lag)
    (fun x => (OuterStream.prefix_height A (S.cuts g) clock T ρ β L.lag x).mono (by decide))
    (OuterStream.suffix_height A (S.cuts g) clock T ρ S.period S.period_pos
      (S.clock_period g L hB) outerReference)
    (S.failed_outer_graph_height L hB T ρ β γ hmod hμ hγ innerReference) x y

end SourceSchedule.Early
namespace CanonicalEpisodes.Parameters

open LocalMarkers WordIntervals EpisodeEnd EpisodeAlgebra
variable {Alphabet : Type uAlphabet3} (C : CanonicalEpisodes.Parameters Alphabet)

lemma remainder_fiber_height [Finite Alphabet] [Nonempty Alphabet] {M : Type uM2}
    [Monoid M] [Fintype M] (T : FreeMonoid Alphabet →* M) (d : M) (lag : ℤ)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EndAt C.d C.K C.tail f (lag+C.offset) (C.small f (lag+C.offset)) b →
      C.Visible 0 b (lag+C.offset)) :
    HasHeightAtMost ({w | w∈remainder (C.complete lag) ∧ T (FreeMonoid.ofList w)=d} : Language Alphabet) 1 := by
  obtain ⟨N,hN⟩ := C.remainder_middle lag hvisible
  have hreg : Language.IsRegular
      ({w | w∈remainder (C.complete lag) ∧ T (FreeMonoid.ofList w)=d} : Language Alphabet) :=
    (C.remainder_regular lag).inf (FiniteRecognition.regular_recognized T {d})
  exact PeriodicTemplates.regular_middle_height _ hreg
    (N+C.tail.toNat) N C.tail.toNat C.d (fun w hw => hN w hw.1)

end CanonicalEpisodes.Parameters

namespace SourceSchedule

open SplitMetadata EpisodeAlgebra

theorem episode_linear_graphs {Alphabet : Type uAlphabet4} {M : Type uM3} {V : Type uV2} {K : Type uK2}
    [Finite Alphabet] [Nonempty Alphabet] [Monoid M] [Fintype M]
    [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V]
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V)) :
    ∃ E : Language Alphabet, PrefixCode E ∧
      (∀ d : M, HasHeightAtMost ({w | w∈remainder E ∧ T (FreeMonoid.ofList w)=d} : Language Alphabet) 1) ∧
      ∀ x y : V, HasHeightAtMost (graph E (fun w => ρ (T (FreeMonoid.ofList w))) x y) 3 := by
  classical
  let : Fintype Alphabet := Fintype.ofFinite Alphabet
  obtain ⟨g,hg,hs₁⟩ := exists_shift_table (A := M) (K := K) (S := V)
  let β : M → M → (Fin g → M) → V := fun a c => (hs₁ (ClockAffine.productTable ρ a c)).choose
  have hβ : ∀ a c, ShiftTableProperty g (ClockAffine.productTable ρ a c) (β a c) :=
    fun a c => (hs₁ (ClockAffine.productTable ρ a c)).choose_spec
  obtain ⟨g',hg',hs₂⟩ := exists_shift_table (A := M) (K := K) (S := V × K)
  let γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K :=
    fun ψ => (hs₂ (ObservedInner.table ψ)).choose
  have hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ) :=
    fun ψ => (hs₂ (ObservedInner.table ψ)).choose_spec
  let κ := Fintype.card (Kind M (V × K) K g')
  obtain ⟨μ,hμpos,hμ⟩ := exists_copies (M := M) (S := V) g κ (by omega)
  let P := Roster M (V × K) K g' μ
  let B := SlotResidues.slotModulus P
  have hB : 0<B := SlotResidues.slotModulus_pos P
  have hμ' : 20*(10000000*Real.log (2*Fintype.card (Tag M V g B))+4*(g+1))+10<μ := by
    simpa only [B,SlotResidues.slotModulus,P,Fintype.card_prod,Fintype.card_fin,κ] using hμ
  let : Nonempty (Tag M V g B) := ⟨Sum.inr ⟨0,⟨0,hB⟩,1,0,0⟩⟩
  obtain ⟨clock⟩ := RobustClock.exists_clock (Tag M V g B) P
  have honto : Function.Surjective (fun i : P => i.1.j) := by
    intro j
    exact ⟨(⟨j,0,0,fun _ => 1,fun _ => 0⟩,⟨0,hμpos⟩),rfl⟩
  let reference : P := (⟨⟨0,by omega⟩,0,0,fun _ => 1,fun _ => 0⟩,⟨0,hμpos⟩)
  obtain ⟨S⟩ := exists_early (Alphabet := Alphabet) clock B (Fintype.card M) hB
    (fun i : P => i.1.j) honto (SlotResidues.reserved P)
  obtain ⟨L⟩ := S.exists_full_late hB g
  let A := S.parameters g L hB
  let j : Fin g := ⟨0,by omega⟩
  have hr : (S.cuts g).main j∈(S.cuts g).offsets := by
    simpa only [OuterStream.Cuts.base,Nat.cast_zero,zero_mul,add_zero] using
      (S.cuts g).offset_mem (.inl j) 0 S.R_pos
  have hG := S.outer_graph_height L hB T ρ β γ
    (SlotResidues.reserved_distinct P) hμ' hβ hγ reference ((S.cuts g).main j) hr
  have hlin := AffineRecovery.recovery_height (L.endRule.prefix_code L.lag) le_rfl
    (fun w => (ρ (T w)).toAddMonoidHom) (OuterStream.wordShift A clock T ρ β L.lag) 3
    (fun x y => by
      rw [←OuterStream.wordUpdate_affine A clock T ρ β L.lag]
      exact hG x y)
  refine ⟨L.endRule.complete L.lag,L.endRule.prefix_code L.lag,?_,hlin⟩
  intro d
  exact L.endRule.remainder_fiber_height T d L.lag
    (fun f b he => (S.episode_visible g L hB he).base)

end SourceSchedule

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


namespace RightRegular

open EpisodeAlgebra
open scoped Computability
variable {Alphabet : Type uAlphabet} {M : Type uM} [Monoid M] [Fintype M]

lemma updateWord_product (T : FreeMonoid Alphabet →* M)
    (es : List (List Alphabet)) (x : V M) :
    updateWord (fun w => action M (T (FreeMonoid.ofList w))) x es =
      action M (T (FreeMonoid.ofList es.flatten)) x := by
  induction es generalizing x with
  | nil =>
    change x=action M (T 1) x
    rw [map_one,action_one]
    rfl
  | cons e es ih =>
    rw [updateWord_cons,ih]
    change action M (T (FreeMonoid.ofList es.flatten))
      (action M (T (FreeMonoid.ofList e)) x) =
      action M (T (FreeMonoid.ofList e * FreeMonoid.ofList es.flatten)) x
    rw [map_mul,action_mul]
    rfl

lemma graph_fiber (T : FreeMonoid Alphabet →* M) (E : Language Alphabet) (d : M) :
    graph E (fun w => action M (T (FreeMonoid.ofList w))) (basis M 1) (basis M d) =
      ({w | w∈E∗ ∧ T (FreeMonoid.ofList w)=d} : Language Alphabet) := by
  ext w
  constructor
  · rintro ⟨es,hes,rfl,h⟩
    refine ⟨Language.join_mem_kstar hes,?_⟩
    rw [updateWord_product] at h
    exact (value_recovery M _ _).mp h
  · rintro ⟨hw,hd⟩
    obtain ⟨es,rfl,hes⟩ := Language.mem_kstar.mp hw
    refine ⟨es,hes,rfl,?_⟩
    rw [updateWord_product]
    exact (value_recovery M _ _).mpr hd

end RightRegular

namespace FiniteRecognition

open EpisodeAlgebra
open scoped Computability

theorem recognized_height_three {Alphabet : Type uAlphabet2} {M : Type uM2} [Finite Alphabet] [Nonempty Alphabet]
    [Monoid M] [Fintype M] (T : FreeMonoid Alphabet →* M) (F : Set M) :
    HasHeightAtMost ({w | T (FreeMonoid.ofList w)∈F} : Language Alphabet) 3 := by
  classical
  obtain ⟨E,hE,hB,hG⟩ := SourceSchedule.episode_linear_graphs T (RightRegular.action M)
  let A : M → Language Alphabet := fun d => {w | w∈E∗ ∧ T (FreeMonoid.ofList w)=d}
  let B : M → Language Alphabet := fun f => {w | w∈remainder E ∧ T (FreeMonoid.ofList w)=f}
  have hA : ∀ d, HasHeightAtMost (A d) 3 := by
    intro d
    change HasHeightAtMost ({w | w∈E∗ ∧ T (FreeMonoid.ofList w)=d} : Language Alphabet) 3
    rw [←RightRegular.graph_fiber T E d]
    exact hG (RightRegular.basis M 1) (RightRegular.basis M d)
  let I := {p : M × M // p.1*p.2∈F}
  have hU : HasHeightAtMost (⨆ p : I, A p.1.1 * B p.1.2) 3 :=
    HasHeightAtMost.iSup _ (fun p => (hA p.1.1).concat ((hB p.1.2).mono (by decide)))
  have heq : ({w | T (FreeMonoid.ofList w)∈F} : Language Alphabet)=
      ⨆ p : I, A p.1.1 * B p.1.2 := by
    ext w
    constructor
    · intro hw
      obtain ⟨es,r,hes,hr,hwr⟩ := factor_remainder hE.1 w
      let d := T (FreeMonoid.ofList es.flatten)
      let f := T (FreeMonoid.ofList r)
      have hdf : d*f∈F := by
        change T (FreeMonoid.ofList es.flatten)*T (FreeMonoid.ofList r)∈F
        rw [←map_mul]
        change T (FreeMonoid.ofList (es.flatten++r))∈F
        rw [←hwr]
        exact hw
      apply Language.mem_iSup.mpr
      refine ⟨⟨(d,f),hdf⟩,Language.mem_mul.mpr ⟨es.flatten,?_,r,?_,hwr.symm⟩⟩
      · exact ⟨Language.join_mem_kstar hes,rfl⟩
      · exact ⟨hr,rfl⟩
    · intro hw
      obtain ⟨p,hp⟩ := Language.mem_iSup.mp hw
      obtain ⟨a,ha,b,hb,rfl⟩ := Language.mem_mul.mp hp
      change T (FreeMonoid.ofList a * FreeMonoid.ofList b)∈F
      rw [map_mul,ha.2,hb.2]
      exact p.2
  exact heq.symm ▸ hU

end FiniteRecognition

end GeneralizedStarHeight

end OAI
end
end

section
section
namespace OAI

namespace GeneralizedStarHeight


theorem main_oai {Alphabet : Type u} [Finite Alphabet] (L : Language Alphabet) (hL : L.IsRegular) :
    HasHeightAtMost L 3 := by
  classical
  rcases isEmpty_or_nonempty Alphabet with h|h
  · let : IsEmpty Alphabet := h
    apply HasHeightAtMost.finite L _ 3
    apply (Set.finite_singleton ([] : List Alphabet)).subset
    intro w _
    cases w with
    | nil => rfl
    | cons a w => exact isEmptyElim a
  · let : Nonempty Alphabet := h
    obtain ⟨M,hM,hfin,T,F,hTF⟩ := FiniteRecognition.of_regular hL
    let : Monoid M := hM
    let : Fintype M := hfin
    have heq : L=({w | T (FreeMonoid.ofList w)∈F} : Language Alphabet) := by
      ext w
      exact hTF w
    rw [heq]
    exact FiniteRecognition.recognized_height_three T F

end GeneralizedStarHeight

end OAI
end
end

theorem solution : type_of% @OAI.GeneralizedStarHeight.main_oai := @OAI.GeneralizedStarHeight.main_oai
