-- Prove2me | solution 1 for HypercubeLineVISTSym2_parentExistsStrong
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:36:07.206162+00:00
-- url     : https://prove2.me/submissions/eabaf68b-23fd-418c-9aed-4c8b9d71a3e4

import Mathlib
import Mathlib.Data.Sym.Sym2

set_option autoImplicit false

namespace P2MBc0747b8

def hd {n : Nat} (a x : Fin n → Bool) : Nat :=
  (Finset.univ.filter (fun i => x i ≠ a i)).card

def flip1 {n : Nat} (w : Fin n → Bool) (j : Fin n) : Fin n → Bool :=
  Function.update w j (!w j)

lemma hd_flip {n : Nat} (a w : Fin n → Bool) (j : Fin n) (hj : w j ≠ a j) :
    hd a (flip1 w j) + 1 = hd a w := by
  unfold hd flip1
  have hs : (Finset.univ.filter (fun i => Function.update w j (!w j) i ≠ a i)) =
      (Finset.univ.filter (fun i => w i ≠ a i)).erase j := by
    ext i
    by_cases h : i = j
    · subst h
      have ha : a i = !w i := by
        cases hw : w i <;> cases ha : a i <;> simp_all
      simp [ha]
    · simp [h]
  rw [hs, Finset.card_erase_add_one]
  simp [hj]

lemma hd_eq_zero {n : Nat} (a x : Fin n → Bool) (h : hd a x = 0) : x = a := by
  unfold hd at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  funext i
  have := h (Finset.mem_univ i)
  simpa using this

lemma flip_valid {n : Nat} (w : Fin n → Bool) (j : Fin n) :
    (∀ i : Fin n, i ≠ j → w i = flip1 w j i) ∧ w j ≠ flip1 w j j := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp [flip1, Function.update_of_ne hi]
  · simp [flip1]

noncomputable def wsel {n : Nat} (a : Fin n → Bool) (v : Sym2 (Fin n → Bool)) : Fin n → Bool :=
  if hd a v.out.1 ≤ hd a v.out.2 then v.out.1 else v.out.2

noncomputable def mu {n : Nat} (a : Fin n → Bool) (v : Sym2 (Fin n → Bool)) : Nat :=
  min (hd a v.out.1) (hd a v.out.2)

lemma hd_wsel {n : Nat} (a : Fin n → Bool) (v : Sym2 (Fin n → Bool)) :
    hd a (wsel a v) = mu a v := by
  unfold wsel mu
  split_ifs with h <;> omega

lemma out_mk {n : Nat} (v : Sym2 (Fin n → Bool)) : s(v.out.1, v.out.2) = v :=
  Quot.out_eq v

lemma wsel_mem {n : Nat} (a : Fin n → Bool) (v : Sym2 (Fin n → Bool)) :
    ∃ y, v = s(wsel a v, y) := by
  unfold wsel
  split_ifs with h
  · exact ⟨v.out.2, (out_mk v).symm⟩
  · refine ⟨v.out.1, ?_⟩
    rw [Sym2.eq_swap]
    exact (out_mk v).symm

lemma mu_mk {n : Nat} (a x y : Fin n → Bool) : mu a s(x, y) = min (hd a x) (hd a y) := by
  have h := out_mk s(x, y)
  unfold mu
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, min_comm]

noncomputable def par {n : Nat} (a : Fin n → Bool) (r v : Sym2 (Fin n → Bool)) :
    Sym2 (Fin n → Bool) := by
  classical
  exact if v = r then r else
    if h : wsel a v = a then r else
      s(wsel a v, flip1 (wsel a v) (Classical.choose (Function.ne_iff.mp h)))

lemma par_self {n : Nat} (a : Fin n → Bool) (r : Sym2 (Fin n → Bool)) : par a r r = r := by
  simp [par]

lemma par_cases {n : Nat} (a : Fin n → Bool) (r v : Sym2 (Fin n → Bool)) (hv : v ≠ r) :
    (wsel a v = a ∧ par a r v = r) ∨
    (∃ j, wsel a v j ≠ a j ∧ par a r v = s(wsel a v, flip1 (wsel a v) j)) := by
  by_cases h : wsel a v = a
  · left; exact ⟨h, by simp [par, hv, h]⟩
  · right
    refine ⟨Classical.choose (Function.ne_iff.mp h), Classical.choose_spec (Function.ne_iff.mp h), ?_⟩
    simp [par, hv, h]

lemma reach {n : Nat} (a : Fin n → Bool) (r : Sym2 (Fin n → Bool)) :
    ∀ N, ∀ v, mu a v = N → ∃ m, (par a r)^[m] v = r := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro v hv
    by_cases h1 : v = r
    · exact ⟨0, h1⟩
    rcases par_cases a r v h1 with ⟨_, hp⟩ | ⟨j, hj, hp⟩
    · exact ⟨1, by simpa using hp⟩
    · have hf := hd_flip a (wsel a v) j hj
      have hw := hd_wsel a v
      have hlt : mu a (par a r v) < N := by
        rw [hp, mu_mk]
        omega
      obtain ⟨m, hm⟩ := ih _ hlt (par a r v) rfl
      exact ⟨m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩

end P2MBc0747b8

theorem solution (n : Nat) (hn : 3 < n) :
    ∀ (rSym2 : Sym2 (Fin n → Bool)) (a b : Fin n → Bool) (d0 : Fin n),
      rSym2 = Sym2.mk a b →
      (∃ c0 : Fin n, (∀ j : Fin n, j ≠ c0 → a j = b j) ∧ a c0 ≠ b c0) →
      ∃ parentSym2 : Fin (2 * n - 2) → Sym2 (Fin n → Bool) → Sym2 (Fin n → Bool),
        (∀ k : Fin (2 * n - 2), parentSym2 k rSym2 = rSym2) ∧
        (∀ k : Fin (2 * n - 2), ∀ v : Sym2 (Fin n → Bool),
          (∃ x y c : Fin n → Bool, ∃ cc : Fin n,
            v = Sym2.mk x y ∧ (∀ j : Fin n, j ≠ cc → x j = y j) ∧ x cc ≠ y cc) →
          (∃ x y c : Fin n → Bool, ∃ cc : Fin n,
            parentSym2 k v = Sym2.mk x y ∧ (∀ j : Fin n, j ≠ cc → x j = y j) ∧ x cc ≠ y cc)) ∧
        (∀ k : Fin (2 * n - 2), ∀ v : Sym2 (Fin n → Bool), v ≠ rSym2 →
          ∃ x y1 y2 : Fin n → Bool, v = Sym2.mk x y1 ∧ parentSym2 k v = Sym2.mk x y2) ∧
        (∀ k : Fin (2 * n - 2), ∀ v : Sym2 (Fin n → Bool),
          ∃ m : Nat, (parentSym2 k)^[m] v = rSym2) := by
  intro rSym2 a b _d0 hr hc
  obtain ⟨c0, hc1, hc2⟩ := hc
  refine ⟨fun _ => P2MBc0747b8.par a rSym2, fun _ => P2MBc0747b8.par_self a rSym2, ?_, ?_, ?_⟩
  · intro _ v _
    by_cases h1 : v = rSym2
    · subst h1
      exact ⟨a, b, a, c0, by show P2MBc0747b8.par a v v = _; rw [P2MBc0747b8.par_self, hr], hc1, hc2⟩
    rcases P2MBc0747b8.par_cases a rSym2 v h1 with ⟨_, hp⟩ | ⟨j, _, hp⟩
    · exact ⟨a, b, a, c0, by show P2MBc0747b8.par a rSym2 v = _; rw [hp, hr], hc1, hc2⟩
    · obtain ⟨hv1, hv2⟩ := P2MBc0747b8.flip_valid (P2MBc0747b8.wsel a v) j
      exact ⟨_, _, a, j, hp, hv1, hv2⟩
  · intro _ v hv
    obtain ⟨y, hy⟩ := P2MBc0747b8.wsel_mem a v
    rcases P2MBc0747b8.par_cases a rSym2 v hv with ⟨hw, hp⟩ | ⟨j, _, hp⟩
    · refine ⟨a, y, b, ?_, by show P2MBc0747b8.par a rSym2 v = _; rw [hp, hr]⟩
      rw [← hw]; exact hy
    · exact ⟨_, y, _, hy, hp⟩
  · intro _ v
    exact P2MBc0747b8.reach a rSym2 _ v rfl
