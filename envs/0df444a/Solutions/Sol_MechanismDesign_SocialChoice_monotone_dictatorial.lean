-- Prove2me | solution 1 for MechanismDesign.SocialChoice.monotone_dictatorial
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:48:02.086027+00:00
-- url     : https://prove2.me/submissions/93029fcb-300c-4c7f-9a29-755e6a869a7f

/-
The Muller-Satterthwaite theorem (Börgers, Proposition 8.5, in Reny's 2001 proof): a monotone
direct mechanism that is onto an alphabet of at least three alternatives is dictatorial.

(1) Monotone and onto gives unanimity: alternatives on top of every ranking are chosen.
(2) Fix `a ≠ b`. Move the voters one at a time from "a first, b last" to "b first, a second"; the
    outcome starts at `a` and ends at `b`. Take a maximal set `W` of voters whose switch keeps the
    outcome `a`, and a voter `n ∉ W`: the voter `n` is pivotal. Monotonicity (applied to profiles
    that differ only by an adjacent swap of `a` and `b`, or by moving `a` to the bottom or `b` to
    the top) transfers the two outcomes to Reny's Figures 1', 2'.
(3) With a third alternative `c`, Figure 3 (a unchanged against everything) has outcome `a`;
    Figure 4 swaps `a` and `b` for the voters after `n`: its outcome is `a` or `b`, and not `b`,
    since `c` is above `b` for everyone and raising `c` to the top would keep `b` by monotonicity,
    contradicting unanimity. Hence the outcome is `a`.
(4) Every profile with `a` on top of the ranking of `n` is a monotone image of Figure 4 for `a`, so
    `n` dictates `a`. Two different alternatives cannot have different dictators.

Rankings are produced by `rk L`: layers `L` in increasing order, ties inside a layer by a fixed
numbering of the alternatives, so profiles that agree outside a few layers have identical
"rest" orders.
-/
import Mathlib
import Definitions.Def_MechanismDesign_SocialChoice_Model

set_option autoImplicit false

namespace MDLib
open MechanismDesign.SocialChoice

section Rank
variable {A : Type*} [Fintype A]

/-- An injective numbering of the alternatives, used to break ties inside a layer. -/
noncomputable def eN (x : A) : ℕ := (Fintype.equivFin A x : ℕ)

theorem eN_inj {x y : A} (h : eN x = eN y) : x = y :=
  (Fintype.equivFin A).injective (Fin.ext h)

/-- The linear order that lists the layers in increasing order of `L` and, inside a layer, the
alternatives in the order of `eN`. -/
noncomputable def rk (L : A → ℕ) : LinPref A where
  rel x y := toLex (L x, eN x) ≤ toLex (L y, eN y)
  total x y := le_total _ _
  trans x y z h1 h2 := le_trans h1 h2
  antisymm x y h1 h2 := by
    have := le_antisymm h1 h2
    have h3 : eN x = eN y := congrArg (fun p => p.2) (toLex.injective this)
    exact eN_inj h3

theorem rk_rel (L : A → ℕ) (x y : A) :
    (rk L).rel x y ↔ L x < L y ∨ (L x = L y ∧ eN x ≤ eN y) := by
  show toLex (L x, eN x) ≤ toLex (L y, eN y) ↔ _
  rw [Prod.Lex.le_iff]
  simp

end Rank

section Layers
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- `a ≻ rest ≻ b` -/
def t0 (a b : A) : A → ℕ := fun x => if x = a then 0 else if x = b then 2 else 1
/-- `b ≻ a ≻ rest` -/
def t1 (a b : A) : A → ℕ := fun x => if x = b then 0 else if x = a then 1 else 2
/-- `a ≻ b ≻ rest` -/
def t2 (a b : A) : A → ℕ := fun x => if x = a then 0 else if x = b then 1 else 2
/-- `b ≻ rest ≻ a` -/
def u1 (a b : A) : A → ℕ := fun x => if x = b then 0 else if x = a then 2 else 1
/-- `rest ≻ a ≻ b` -/
def u0 (a b : A) : A → ℕ := fun x => if x = b then 2 else if x = a then 1 else 0
/-- `rest ≻ c ≻ b ≻ a` -/
def w1 (a b c : A) : A → ℕ := fun x => if x = a then 3 else if x = b then 2 else if x = c then 1 else 0
/-- `a ≻ c ≻ b ≻ rest` -/
def w2 (a b c : A) : A → ℕ := fun x => if x = a then 0 else if x = c then 1 else if x = b then 2 else 3
/-- `rest ≻ c ≻ a ≻ b` -/
def w0 (a b c : A) : A → ℕ := fun x => if x = b then 3 else if x = a then 2 else if x = c then 1 else 0
/-- `c ≻ rest ≻ b ≻ a` -/
def v1 (a b c : A) : A → ℕ := fun x => if x = c then 0 else if x = a then 3 else if x = b then 2 else 1
/-- `c ≻ a ≻ b ≻ rest` -/
def v2 (a b c : A) : A → ℕ := fun x => if x = c then 0 else if x = a then 1 else if x = b then 2 else 3

variable {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
include hab

theorem c1 : ∀ x, (rk (t0 a b)).rel a x → (rk (t2 a b)).rel a x := by
  intro x _
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [Ne.symm hab, rk_rel, t2]

theorem c2 {y : A} (hya : y ≠ a) (hyb : y ≠ b) :
    ∀ x, (rk (t1 a b)).rel y x → (rk (t2 a b)).rel y x := by
  intro x h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [Ne.symm hab, rk_rel, t1, t2]

theorem c3 : ∀ x, (rk (t1 a b)).rel b x → (rk (u1 a b)).rel b x := by
  intro x _
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [Ne.symm hab, rk_rel, u1]

theorem c3' : ∀ x, (rk (t0 a b)).rel b x → (rk (u0 a b)).rel b x := by
  intro x h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [Ne.symm hab, rk_rel, t0, u0]

theorem c4 {y : A} (hya : y ≠ a) (hyb : y ≠ b) :
    ∀ x, (rk (t2 a b)).rel y x → (rk (t1 a b)).rel y x := by
  intro x h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [Ne.symm hab, rk_rel, t1, t2]

theorem c5 : ∀ x, (rk (u1 a b)).rel b x → (rk (t1 a b)).rel b x := by
  intro x _
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [Ne.symm hab, rk_rel, t1]

theorem c5' : ∀ x, (rk (u0 a b)).rel b x → (rk (t0 a b)).rel b x := by
  intro x h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [Ne.symm hab, rk_rel, t0, u0]

include hac hbc

theorem c6a : ∀ x, (rk (u1 a b)).rel a x → (rk (w1 a b c)).rel a x := by
  intro x h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    simp_all [Ne.symm hab, Ne.symm hac, Ne.symm hbc, rk_rel, u1, w1]

theorem c6b : ∀ x, (rk (t2 a b)).rel a x → (rk (w2 a b c)).rel a x := by
  intro x h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    simp_all [Ne.symm hab, Ne.symm hac, Ne.symm hbc, rk_rel, t2, w2]

theorem c6c : ∀ x, (rk (u0 a b)).rel a x → (rk (w0 a b c)).rel a x := by
  intro x h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    simp_all [Ne.symm hab, Ne.symm hac, Ne.symm hbc, rk_rel, u0, w0]

theorem c7 {y : A} (hya : y ≠ a) (hyb : y ≠ b) :
    ∀ x, (rk (w1 a b c)).rel y x → (rk (w0 a b c)).rel y x := by
  intro x h
  by_cases hyc : y = c <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    simp_all [Ne.symm hab, Ne.symm hac, Ne.symm hbc, rk_rel, w1, w0]

theorem c8a : ∀ x, (rk (w1 a b c)).rel b x → (rk (v1 a b c)).rel b x := by
  intro x h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    simp_all [Ne.symm hab, Ne.symm hac, Ne.symm hbc, rk_rel, v1, w1]

theorem c8b : ∀ x, (rk (w2 a b c)).rel b x → (rk (v2 a b c)).rel b x := by
  intro x h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    simp_all [Ne.symm hab, Ne.symm hac, Ne.symm hbc, rk_rel, v2, w2]

theorem c9 : ∀ x, (rk (w1 a b c)).rel a x → x = a := by
  intro x h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    simp_all [Ne.symm hab, Ne.symm hac, Ne.symm hbc, rk_rel, w1]

end Layers

section Tops
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- `a` on top, everything else below it in the `eN` order. -/
def tp (a : A) : A → ℕ := fun x => if x = a then 0 else 1

theorem tp_top (a : A) : ∀ x, (rk (tp a)).rel a x := by
  intro x
  by_cases h : x = a <;> simp [rk_rel, tp, h]

theorem t0_top {a b : A} (hab : a ≠ b) : ∀ x, (rk (t0 a b)).rel a x := by
  intro x
  by_cases h1 : x = a <;> by_cases h2 : x = b <;> simp_all [rk_rel, t0, Ne.symm hab]

theorem t1_top {a b : A} (hab : a ≠ b) : ∀ x, (rk (t1 a b)).rel b x := by
  intro x
  by_cases h1 : x = a <;> by_cases h2 : x = b <;> simp_all [rk_rel, t1, Ne.symm hab]

theorem v1_top {a b c : A} : ∀ x, (rk (v1 a b c)).rel c x := by
  intro x
  by_cases h1 : x = a <;> by_cases h2 : x = b <;> by_cases h3 : x = c <;> simp_all [rk_rel, v1]

theorem v2_top {a b c : A} : ∀ x, (rk (v2 a b c)).rel c x := by
  intro x
  by_cases h1 : x = a <;> by_cases h2 : x = b <;> by_cases h3 : x = c <;> simp_all [rk_rel, v2]

theorem rel_refl' (P : LinPref A) (x : A) : P.rel x x := (P.total x x).elim id id

theorem exists_top (P : LinPref A) [Nonempty A] : ∃ t, ∀ x, P.rel t x := by
  have : ∀ s : Finset A, s.Nonempty → ∃ t ∈ s, ∀ x ∈ s, P.rel t x := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => exact ⟨a, by simp, fun x hx => by simp at hx; subst hx; exact rel_refl' P _⟩
    | cons a s ha hs ih =>
      obtain ⟨t, ht, hts⟩ := ih
      rcases P.total a t with h | h
      · refine ⟨a, Finset.mem_cons_self _ _, fun x hx => ?_⟩
        rcases Finset.mem_cons.1 hx with rfl | hx
        · exact rel_refl' P _
        · exact P.trans _ _ _ h (hts x hx)
      · refine ⟨t, Finset.mem_cons.2 (Or.inr ht), fun x hx => ?_⟩
        rcases Finset.mem_cons.1 hx with rfl | hx
        · exact h
        · exact hts x hx
  obtain ⟨t, _, ht⟩ := this Finset.univ Finset.univ_nonempty
  exact ⟨t, fun x => ht x (Finset.mem_univ x)⟩

end Tops

section Main
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

/-- Three classes of voters: `n`, the voters of `W`, and all the others. -/
noncomputable def prof (W : Finset ι) (n : ι) (LW Ln Lo : A → ℕ) : ι → LinPref A :=
  fun i => if i = n then rk Ln else if i ∈ W then rk LW else rk Lo

theorem prof_mono {f : DirectMechanism ι A} (hf : IsMonotone f) {W : Finset ι} {n : ι}
    {LW Ln Lo LW' Ln' Lo' : A → ℕ} {y : A} (hy : f (prof W n LW Ln Lo) = y)
    (h1 : ∀ x, (rk LW).rel y x → (rk LW').rel y x)
    (h2 : ∀ x, (rk Ln).rel y x → (rk Ln').rel y x)
    (h3 : ∀ x, (rk Lo).rel y x → (rk Lo').rel y x) : f (prof W n LW' Ln' Lo') = y := by
  refine hf _ _ y hy (fun i x hx => ?_)
  unfold prof at hx ⊢
  by_cases hi : i = n
  · simp only [hi, if_true] at hx ⊢; exact h2 x hx
  · by_cases hiW : i ∈ W
    · simp only [hi, hiW, if_false, if_true] at hx ⊢; exact h1 x hx
    · simp only [hi, hiW, if_false] at hx ⊢; exact h3 x hx

theorem unanimity {f : DirectMechanism ι A} (hf : IsMonotone f) (hs : Function.Surjective f)
    (R : ι → LinPref A) (a : A) (h : ∀ i x, (R i).rel a x) : f R = a := by
  obtain ⟨R0, hR0⟩ := hs a
  exact hf R0 R a hR0 (fun i x _ => h i x)

theorem pivot {f : DirectMechanism ι A} (hf : IsMonotone f) (hs : Function.Surjective f)
    {a b : A} (hab : a ≠ b) :
    ∃ (W : Finset ι) (n : ι), n ∉ W ∧ f (prof W n (t1 a b) (t0 a b) (t0 a b)) = a ∧
      f (prof W n (t1 a b) (t1 a b) (t0 a b)) ≠ a := by
  classical
  let T : Finset ι → (ι → LinPref A) := fun W i => if i ∈ W then rk (t1 a b) else rk (t0 a b)
  have hT0 : f (T ∅) = a := unanimity hf hs _ a (fun i x => by simpa [T] using t0_top hab x)
  have hTu : f (T Finset.univ) = b := unanimity hf hs _ b (fun i x => by simpa [T] using t1_top hab x)
  obtain ⟨W, hW, hmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Finset ι)).filter (fun W => f (T W) = a)) Finset.card
    ⟨∅, by simp [hT0]⟩
  have hWa : f (T W) = a := (Finset.mem_filter.1 hW).2
  have hWne : W ≠ Finset.univ := by
    rintro rfl
    exact hab (hTu.symm.trans hWa).symm
  obtain ⟨n, hn⟩ : ∃ n, n ∉ W := by
    by_contra hcon
    push Not at hcon
    exact hWne (Finset.eq_univ_iff_forall.2 hcon)
  have e1 : prof W n (t1 a b) (t0 a b) (t0 a b) = T W := by
    funext i
    by_cases hi : i = n
    · subst hi; simp [prof, T, hn]
    · simp [prof, T, hi]
  have e2 : prof W n (t1 a b) (t1 a b) (t0 a b) = T (insert n W) := by
    funext i
    by_cases hi : i = n
    · subst hi; simp [prof, T]
    · by_cases hiW : i ∈ W <;> simp [prof, T, hi, hiW]
  refine ⟨W, n, hn, by rw [e1]; exact hWa, ?_⟩
  rw [e2]
  intro hcon
  have : insert n W ∈ (Finset.univ : Finset (Finset ι)).filter (fun W => f (T W) = a) := by
    simp [hcon]
  have := hmax _ this
  rw [Finset.card_insert_of_notMem hn] at this
  omega

theorem exists_dict {f : DirectMechanism ι A} (hf : IsMonotone f) (hs : Function.Surjective f)
    (hA : 3 ≤ Fintype.card A) (a : A) :
    ∃ n : ι, ∀ Q : ι → LinPref A, (∀ x, (Q n).rel a x) → f Q = a := by
  classical
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a
  have hab : a ≠ b := hba.symm
  obtain ⟨c, hc⟩ : ∃ c, c ∈ (Finset.univ.erase a).erase b := by
    apply Finset.card_pos.1
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ a)]
    · simp; omega
    · simp [hba]
  have hcb : c ≠ b := (Finset.mem_erase.1 hc).1
  have hca : c ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 hc).2).1
  have hac : a ≠ c := hca.symm
  have hbc : b ≠ c := hcb.symm
  obtain ⟨W, n, hn, h1, h2⟩ := pivot hf hs hab
  refine ⟨n, ?_⟩
  have hid : ∀ (L : A → ℕ) (x : A), (rk L).rel a x → (rk L).rel a x := fun _ _ h => h
  -- Figure 1
  have hF1 : f (prof W n (t1 a b) (t2 a b) (t0 a b)) = a :=
    prof_mono hf h1 (fun x h => h) (c1 hab) (fun x h => h)
  -- Figure 2 has outcome b
  have hF2 : f (prof W n (t1 a b) (t1 a b) (t0 a b)) = b := by
    by_contra hb
    set x := f (prof W n (t1 a b) (t1 a b) (t0 a b)) with hxdef
    have hx : x ≠ a := h2
    have := prof_mono hf (y := x) rfl (fun x h => h) (c2 hab hx hb) (fun x h => h)
    exact hx (this.symm.trans hF1)
  -- Figure 2'
  have hF2' : f (prof W n (u1 a b) (t1 a b) (u0 a b)) = b :=
    prof_mono hf hF2 (c3 hab) (fun x h => h) (c3' hab)
  -- Figure 1'
  have hF1' : f (prof W n (u1 a b) (t2 a b) (u0 a b)) = a := by
    set x := f (prof W n (u1 a b) (t2 a b) (u0 a b)) with hxdef
    by_cases hxa : x = a
    · exact hxa
    by_cases hxb : x = b
    · exfalso
      have h' : f (prof W n (t1 a b) (t2 a b) (t0 a b)) = b :=
        prof_mono hf (y := b) hxb (c5 hab) (fun x h => h) (c5' hab)
      exact hab (hF1.symm.trans h')
    · exfalso
      have := prof_mono hf (y := x) rfl (fun x h => h) (c4 hab hxa hxb) (fun x h => h)
      exact hxb (hF2'.symm.trans this).symm
  -- Figure 3
  have hF3 : f (prof W n (w1 a b c) (w2 a b c) (w0 a b c)) = a :=
    prof_mono hf hF1' (c6a hab hac hbc) (c6b hab hac hbc) (c6c hab hac hbc)
  -- Figure 4
  have hF4 : f (prof W n (w1 a b c) (w2 a b c) (w1 a b c)) = a := by
    set x := f (prof W n (w1 a b c) (w2 a b c) (w1 a b c)) with hxdef
    by_cases hxa : x = a
    · exact hxa
    by_cases hxb : x = b
    · exfalso
      have h5 : f (prof W n (v1 a b c) (v2 a b c) (v1 a b c)) = b := by
        exact prof_mono hf (y := b) hxb (c8a hab hac hbc) (c8b hab hac hbc) (c8a hab hac hbc)
      have h6 : f (prof W n (v1 a b c) (v2 a b c) (v1 a b c)) = c := by
        refine unanimity hf hs _ c (fun i y => ?_)
        unfold prof
        split_ifs
        · exact v2_top y
        · exact v1_top y
        · exact v1_top y
      exact hbc (h5.symm.trans h6)
    · exfalso
      have := prof_mono hf (y := x) rfl (fun x h => h) (fun x h => h) (c7 hab hac hbc hxa hxb)
      exact hxa (this.symm.trans hF3)
  -- the dictator
  intro Q hQ
  refine hf _ Q a hF4 (fun i x hx => ?_)
  unfold prof at hx
  by_cases hi : i = n
  · subst hi; exact hQ x
  · have : x = a := by
      split_ifs at hx
      · exact c9 hab hac hbc x hx
      · exact c9 hab hac hbc x hx
    subst this
    exact rel_refl' (Q i) _

theorem md_main (hA : 3 ≤ Fintype.card A) (f : DirectMechanism ι A)
    (hrange : Function.Surjective f) (hf : IsMonotone f) : IsDictatorial f := by
  haveI : Nonempty A := Fintype.card_pos_iff.1 (by omega)
  choose nA hnA using exists_dict hf hrange hA
  have uniq : ∀ a a' : A, a ≠ a' → nA a = nA a' := by
    intro a a' hne
    by_contra h
    let Q : ι → LinPref A := fun i => if i = nA a then rk (tp a) else rk (tp a')
    have h1 : f Q = a := hnA a Q (by simpa [Q] using tp_top a)
    have h2 : f Q = a' := by
      refine hnA a' Q ?_
      have : Q (nA a') = rk (tp a') := by simp [Q, Ne.symm h]
      rw [this]
      exact tp_top a'
    exact hne (h1.symm.trans h2)
  refine ⟨nA (Classical.arbitrary A), fun R x => ?_⟩
  obtain ⟨t, ht⟩ := exists_top (R (nA (Classical.arbitrary A)))
  have hft : f R = t := by
    by_cases h : t = Classical.arbitrary A
    · have h0 := hnA (Classical.arbitrary A) R (h ▸ ht)
      rw [h0, h]
    · have := uniq (Classical.arbitrary A) t (Ne.symm h)
      exact hnA t R (by rw [← this]; exact ht)
  rw [hft]
  exact ht x

end Main

end MDLib

open MechanismDesign.SocialChoice in
theorem solution {ι A : Type*} [Fintype ι] [Fintype A]
    (hA : 3 ≤ Fintype.card A) (f : DirectMechanism ι A) (hrange : Function.Surjective f)
    (hf : IsMonotone f) : IsDictatorial f := by
  classical
  exact MDLib.md_main hA f hrange hf
