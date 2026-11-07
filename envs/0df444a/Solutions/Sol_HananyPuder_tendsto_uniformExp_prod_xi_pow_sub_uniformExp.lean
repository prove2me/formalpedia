-- Prove2me | solution 1 for HananyPuder.tendsto_uniformExp_prod_xi_pow_sub_uniformExp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T08:16:54.275212+00:00
-- url     : https://prove2.me/submissions/fd7009c7-ce01-43c4-b576-89e8b335f65e

import Definitions.Def_StrongConv
import Mathlib

section
section
/-! HP13: the word/permutation definitions of the q202 Blueprint (`StrongConv.Q202L2`), copied verbatim. -/


noncomputable section

namespace StrongConv.Q202L2

open StrongConv

/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-- The permutation a word stands for (product in the order the letters appear). -/
def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

/-- Number of fixed points. -/
def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => π x = x).card

/-- The inverse letter. -/
def letterInv {d : ℕ} : Letter d → Letter d
  | none => none
  | some s => some s.swap

/-- `r` is cyclically reduced: no letter is followed (cyclically) by its inverse. -/
def CycRed {d : ℕ} (r : List (Letter d)) : Prop :=
  ∀ t : Fin r.length,
    r.get ⟨(t.val + 1) % r.length, Nat.mod_lt _ (by have := t.2; omega)⟩ ≠ letterInv (r.get t)

/-- `r^k` as a word. -/
def powList {d : ℕ} (r : List (Letter d)) (k : ℕ) : List (Letter d) :=
  (List.replicate k r).flatten


end StrongConv.Q202L2

end
end
end

section
section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5

/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-! ## Part Root: roots in free groups -/

/-! ## Part Perm: words as permutations -/

/-! ## Part Comb: the expected number of fixed points -/

/-! ## Part Alg: clearing denominators -/

end StrongConv.S5

end
end
end

section
section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartPerm

open scoped InnerProductSpace

/-! ### The left-regular representation -/

end StrongConv.S5.PartPerm

end
end
end

section
section
/-!
# Part Comb: the expected number of fixed points of a random word permutation

Proof of `StrongConv.S5.exists_fixCount_expectation` (stated in `Blueprint.lean`).
-/

open Finset

noncomputable section

namespace StrongConv.S5.PartComb

open StrongConv StrongConv.S5

/-! ## Counting permutations extending a partial injection -/

section Count

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite set of pairs is the graph of a partial injection. -/
def PInj (E : Finset (α × α)) : Prop :=
  ∀ p ∈ E, ∀ q ∈ E, (p.1 = q.1 ↔ p.2 = q.2)

instance (E : Finset (α × α)) : Decidable (PInj E) := by
  unfold PInj; infer_instance

end Count

/-! ## Paths along a word -/

section Word

variable {d : ℕ} (w : List (Letter d))

/-- The label `i` of a letter `sᵢ` or `sᵢ*`. -/
def lab : Letter d → Option (Fin d)
  | none => none
  | some (Sum.inl i) => some i
  | some (Sum.inr i) => some i

/-- The directed edge `(a', b')` with `σᵢ a' = b'` forced by a step `xₜ = letter (xₜ₊₁)`, where
`a = xₜ`, `b = xₜ₊₁`. -/
def edge {α : Type*} : Letter d → α → α → α × α
  | some (Sum.inl _), a, b => (b, a)
  | _, a, b => (a, b)

/-- The edge set of label `i` of a path. -/
def Es {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) (i : Fin d) :
    Finset (α × α) :=
  (univ.filter fun t : Fin w.length => lab (w.get t) = some i).image
    fun t => edge (w.get t) (x t.castSucc) (x t.succ)

/-- The path stands still at the `none` letters. -/
def Cons {α : Type*} (x : Fin (w.length + 1) → α) : Prop :=
  ∀ t : Fin w.length, w.get t = none → x t.castSucc = x t.succ

/-- A closed consistent path whose edge sets are partial injections. -/
def Good {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) : Prop :=
  Cons w x ∧ (∀ i, PInj (Es w x i)) ∧ x 0 = x (Fin.last _)

instance {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) : Decidable (Cons w x) := by
  unfold Cons; infer_instance

instance {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) :
    Decidable (Good w x) := by
  unfold Good; infer_instance

/-- `σ` realises the path `x`. -/
def Rz {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) : Prop :=
  ∀ t : Fin w.length, x t.castSucc = letterPerm σ (w.get t) (x t.succ)

instance {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Decidable (Rz w σ x) := by
  unfold Rz; infer_instance

end Word

/-! ## Canonical representatives of kernels -/

section Canon

variable {n : ℕ} {α : Type*} [DecidableEq α]

end Canon

/-! ## Invariance under relabelling -/

section Invariance

variable {d : ℕ} (w : List (Letter d))

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

variable (c : Fin (w.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ

end Invariance

/-! ## The bounds on the invariants -/

section Bounds

variable {d : ℕ} (w : List (Letter d)) {α : Type*} [DecidableEq α]

end Bounds

end StrongConv.S5.PartComb

end
end
end

section
section
/-!
# CGTvH Lemma 5.2 (Nica): Blueprint

`E[fix w(σ)] = ∑_{c} N^{(V c)} / ∏ᵢ N^{(Eᵢ c)}` over the canonical consistent colourings `c` of the
closed path of `w` (S5 PartComb). For `w` replaced by `r^k`, `r` a cyclically reduced word of a
conjugate of the non-power `v`, every colouring has `V ≤ E`, and exactly `d(k)` have `V = E`
(the periodic ones).
-/

open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb

noncomputable section

namespace StrongConv.N52

/-- `r^k` as a word. -/
def powList {d : ℕ} (r : List (Letter d)) (k : ℕ) : List (Letter d) :=
  (List.replicate k r).flatten

/-! ## Part W: words and free groups -/

/-! ## Part G: the colourings -/

/-! ## Part M: assembly -/

end StrongConv.N52

end
end
end

section
section
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartG

section Gen

variable {d : ℕ} {α : Type*} [DecidableEq α]

/-- The labelled edge of step `t`. -/
def ee (a : ℕ → Letter d) (x : ℕ → α) (t : ℕ) : Option (Fin d) × (α × α) :=
  (lab (a t), edge (a t) (x t) (x (t + 1)))

/-- The vertices visited at times `≤ k`. -/
def UU (x : ℕ → α) (k : ℕ) : Finset α := (range (k + 1)).image x

/-- The labelled edges of steps `< k`. -/
def EE (a : ℕ → Letter d) (x : ℕ → α) (k : ℕ) : Finset (Option (Fin d) × (α × α)) :=
  (range k).image (ee a x)

/-- Step `k` is a closing step. -/
def closing (a : ℕ → Letter d) (x : ℕ → α) (k : ℕ) : Prop :=
  x (k + 1) ∈ UU x k ∧ ee a x k ∉ EE a x k

instance (a : ℕ → Letter d) (x : ℕ → α) : DecidablePred (closing a x) := by
  intro k; unfold closing; infer_instance

variable {L : ℕ} {a : ℕ → Letter d} {x : ℕ → α}

end Gen

section Bridge

variable {d : ℕ}

/-- The letters of a word, `none` past its end. -/
def A (u : List (Letter d)) (t : ℕ) : Letter d := u.getD t none

end Bridge

section Divisors

variable {d : ℕ}

lemma getD_flat {β : Type*} (s : List β) (dflt : β) (hs : s ≠ []) :
    ∀ j t, t < j * s.length →
      ((List.replicate j s).flatten).getD t dflt = s.getD (t % s.length) dflt
  | 0, t, h => by simp at h
  | j + 1, t, h => by
      rw [List.replicate_succ, List.flatten_cons]
      by_cases ht : t < s.length
      · rw [List.getD_append _ _ _ _ ht, Nat.mod_eq_of_lt ht]
      · rw [Nat.succ_mul] at h
        rw [List.getD_append_right _ _ _ _ (by omega), getD_flat s dflt hs j _ (by omega)]
        congr 1
        conv_rhs => rw [show t = t - s.length + s.length by omega]
        rw [Nat.add_mod_right]

lemma A_pow (r : List (Letter d)) (hne : r ≠ []) (k t : ℕ) (ht : t < k * r.length) :
    A (powList r k) t = A r (t % r.length) :=
  getD_flat r none hne k t ht

lemma wordFree_append (l1 l2 : List (Letter d)) :
    wordFree (l1 ++ l2) = wordFree l1 * wordFree l2 := by
  unfold wordFree; rw [List.map_append, List.prod_append]

lemma wordFree_flat (s : List (Letter d)) : ∀ j,
    wordFree ((List.replicate j s).flatten) = wordFree s ^ j
  | 0 => by simp [wordFree]
  | j + 1 => by
      rw [List.replicate_succ, List.flatten_cons, wordFree_append, wordFree_flat s j, pow_succ']

/-- `p` is a period of `f`. -/
def IsPer {β : Type*} (f : ℕ → β) (p : ℕ) : Prop := ∀ t, f (t + p) = f t

lemma per_mul {β : Type*} {f : ℕ → β} {p : ℕ} (h : IsPer f p) : ∀ m, IsPer f (p * m)
  | 0 => fun t => by simp
  | m + 1 => fun t => by
      rw [Nat.mul_succ, ← add_assoc, h, per_mul h m t]

lemma per_sub {β : Type*} {f : ℕ → β} {p q : ℕ} (hp : IsPer f p) (hq : IsPer f q) (hqp : q ≤ p) :
    IsPer f (p - q) := fun t => by
  rw [← hq (t + (p - q)), add_assoc, Nat.sub_add_cancel hqp, hp]

lemma per_gcd {β : Type*} (f : ℕ → β) (m n : ℕ) : IsPer f m → IsPer f n → IsPer f (Nat.gcd m n) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => intro _ hn; simpa using hn
  | H1 m n hm ih =>
    intro hpm hpn
    rw [Nat.gcd_rec]
    apply ih _ hpm
    have e : n % m = n - m * (n / m) := by
      have := Nat.div_add_mod n m; omega
    rw [e]
    exact per_sub hpn (per_mul hpm _) (Nat.mul_div_le n m)

lemma A_take (r : List (Letter d)) {g j : ℕ} (hj : j < g) : A (r.take g) j = A r j := by
  unfold A
  simp [List.getD_eq_getElem?_getD, hj]

lemma per_dvd (r : List (Letter d)) (hne : r ≠ []) (hnp : IsNonPower (wordFree r)) (k : ℕ)
    (hk : 1 ≤ k) (M : ℕ) (hM : 1 ≤ M) (hML : M ∣ k * r.length)
    (hper : ∀ t < k * r.length, A (powList r k) t = A (powList r k) (t % M)) :
    r.length ∣ M := by
  have hn0 : 0 < r.length := List.length_pos_iff.2 hne
  have hL0 : 0 < k * r.length := Nat.mul_pos (by omega) hn0
  have hnL : r.length ∣ k * r.length := Dvd.intro_left k rfl
  let f : ℕ → Letter d := fun t => A r (t % r.length)
  have hfL : ∀ t, f t = A (powList r k) (t % (k * r.length)) := by
    intro t
    rw [A_pow r hne k _ (Nat.mod_lt _ hL0), Nat.mod_mod_of_dvd _ hnL]
  have hfM : ∀ t, f t = A (powList r k) (t % M) := by
    intro t; rw [hfL, hper _ (Nat.mod_lt _ hL0), Nat.mod_mod_of_dvd _ hML]
  have pn : IsPer f r.length := fun t => by simp only [f, Nat.add_mod_right]
  have pM : IsPer f M := fun t => by rw [hfM, hfM, Nat.add_mod_right]
  have pg := per_gcd f M r.length pM pn
  set g := Nat.gcd M r.length with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgn : g ∣ r.length := Nat.gcd_dvd_right M r.length
  have hgle : g ≤ r.length := Nat.le_of_dvd hn0 hgn
  have hrt : ∀ t < r.length, A r t = A r (t % g) := by
    intro t ht
    have h1 : f t = A r t := by simp only [f, Nat.mod_eq_of_lt ht]
    have h2 : f (t % g) = A r (t % g) := by
      simp only [f, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) ht)]
    rw [← h1, ← h2]
    conv_lhs => rw [← Nat.mod_add_div t g]
    exact per_mul pg (t / g) (t % g)
  have htk : (r.take g).length = g := by simp [hgle]
  have htk0 : r.take g ≠ [] := by
    intro h; rw [h] at htk; simp at htk; omega
  have hreq : r = (List.replicate (r.length / g) (r.take g)).flatten := by
    have hlen : ((List.replicate (r.length / g) (r.take g)).flatten).length = r.length := by
      simp [List.length_flatten, List.map_replicate, List.sum_replicate, htk,
        Nat.div_mul_cancel hgn]
    apply List.ext_getElem hlen.symm
    intro t h1 h2
    rw [← List.getD_eq_getElem _ none h1, ← List.getD_eq_getElem _ none h2,
      getD_flat _ none htk0 _ t (by rw [htk, Nat.div_mul_cancel hgn]; exact h1), htk]
    show A r t = A (r.take g) (t % g)
    rw [A_take r (Nat.mod_lt _ hg0)]
    exact hrt t h1
  have hw : wordFree r = wordFree (r.take g) ^ (r.length / g) := by
    conv_lhs => rw [hreq]
    exact wordFree_flat _ _
  have h1 : r.length / g < 2 := by
    by_contra h
    exact hnp.2 _ _ (by omega) hw
  have h2 : 0 < r.length / g := Nat.div_pos hgle hg0
  have h3 : r.length = g := by
    have := Nat.div_mul_cancel hgn
    rw [show r.length / g = 1 by omega, one_mul] at this
    exact this.symm
  rw [h3]
  exact Nat.gcd_dvd_left M r.length

end Divisors

end StrongConv.N52.PartG

end
end
end

section
section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartM

/-- `N^{(m)} / N^m → 1`. -/
lemma tendsto_descFactorial_div_pow (m : ℕ) :
    Tendsto (fun N : ℕ => (N.descFactorial m : ℝ) / (N : ℝ) ^ m) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => ∏ j ∈ range m, (1 - (j : ℝ) / N)) atTop
      (𝓝 (∏ j ∈ range m, (1 - 0 : ℝ))) :=
    tendsto_finsetProd _ fun j _ =>
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ))
  simp only [sub_zero, prod_const_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (max m 1)] with N hN
  have hNm : m ≤ N := le_of_max_le_left hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : 1 ≤ N := le_of_max_le_right hN
    exact_mod_cast (show N ≠ 0 by omega)
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
    show (N : ℝ) ^ m = ∏ _j ∈ range m, (N : ℝ) by simp, ← prod_div_distrib]
  refine prod_congr rfl fun j hj => ?_
  have hj : j < m := mem_range.1 hj
  rw [Nat.cast_sub (by omega), sub_div, div_self hN0]

/-- `N^a / N^b → [a = b]` for `a ≤ b`. -/
lemma tendsto_pow_div_pow (a b : ℕ) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ a / (N : ℝ) ^ b) atTop (𝓝 (if a = b then 1 else 0)) := by
  split_ifs with h
  · subst h
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [div_self (pow_ne_zero _ hN0)]
  · have h1 : Tendsto (fun N : ℕ => ((N : ℝ) ^ (b - a))⁻¹) atTop (𝓝 0) :=
      ((tendsto_pow_atTop (by omega : b - a ≠ 0)).comp
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [pow_sub₀ _ hN0 hab]
    field_simp

lemma tendsto_term {ι : Type*} [Fintype ι] (a : ℕ) (b : ι → ℕ) (hab : a ≤ ∑ i, b i) :
    Tendsto (fun N : ℕ => (N.descFactorial a : ℝ) / ∏ i, (N.descFactorial (b i) : ℝ)) atTop
      (𝓝 (if a = ∑ i, b i then 1 else 0)) := by
  have hA := tendsto_descFactorial_div_pow a
  have hB : Tendsto (fun N : ℕ => ∏ i, (N.descFactorial (b i) : ℝ) / (N : ℝ) ^ (b i)) atTop
      (𝓝 (∏ _i : ι, (1 : ℝ))) :=
    tendsto_finsetProd _ fun i _ => tendsto_descFactorial_div_pow (b i)
  rw [prod_const_one] at hB
  have hP := tendsto_pow_div_pow a (∑ i, b i) hab
  have h := (hA.div hB one_ne_zero).mul hP
  rw [div_one, one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [Pi.div_apply]
  rw [prod_div_distrib, prod_pow_eq_pow_sum]
  by_cases hz : ∏ i, (N.descFactorial (b i) : ℝ) = 0
  · simp [hz]
  · field_simp

end StrongConv.N52.PartM

end
end
end

section
section
/-!
# q202 leaf 2, Part M: `multiwalk_limit` (the several-cycle Nica limit)

The colouring machinery (`PInj`, `Es`, `EsM`, `GoodM`, `canon`, `nv`, …) is copied from
`Q202L1PartR.lean` (sections Count–Multi), whose module does not currently build.

Proof: `E[∏ fix] = ∑_c N^{(v_c)} / ∏_i N^{(e_{c,i})}` over canonical good colourings (`expect_eq`).
Counting used half-edges (`Hs`, `deg`): every vertex of a cyclically reduced closed walk has
degree `≥ 2`, and the half-edges number `2e`, so `v ≤ e` (`nv_le_e`); `v = e` forces degree `2`
everywhere (`deg_le_two`), hence walks through a common vertex run in lockstep forwards or
backwards (`fwd`, `bwd`), so a vertex determines the phase mod `|r|` (`phase`: `r` primitive,
`r` not a rotation of its inverse). Restriction to positions `≡ 0 mod |r|` and periodic extension
are inverse bijections between the `v = e` colourings for `r` and all good colourings of the
walks `g₁^{m_t}` (`card_B`); the latter number `F s m` is `E[∏ fix(σ^{m_t})]` for `N ≥ ∑ m`
(`Fm_bound`), so `F s m ≤ (1 + ∑ m)^s`.
-/

open Polynomial Filter Topology Finset

noncomputable section

namespace StrongConv.Q202L2.PartM

open StrongConv StrongConv.Q202L2

section Count

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite set of pairs is the graph of a partial injection. -/
def PInj (E : Finset (α × α)) : Prop :=
  ∀ p ∈ E, ∀ q ∈ E, (p.1 = q.1 ↔ p.2 = q.2)

instance (E : Finset (α × α)) : Decidable (PInj E) := by
  unfold PInj; infer_instance

lemma card_stab (A : Finset α) :
    (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      (Fintype.card α - A.card).factorial := by
  have e := Equiv.Perm.subtypeEquivSubtypePerm (fun a : α => a ∉ A)
  have h1 : (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      Fintype.card { f : Equiv.Perm α // ∀ a, ¬ (a ∉ A) → f a = a } := by
    rw [Fintype.card_subtype]; congr 1; ext π; simp
  rw [h1, ← Fintype.card_congr e, Fintype.card_perm, Fintype.card_subtype]
  congr 1
  rw [← Finset.card_compl]
  congr 1
  ext a; simp

lemma exists_ext (E : Finset (α × α)) (h : PInj E) :
    ∃ τ : Equiv.Perm α, ∀ p ∈ E, τ p.1 = p.2 := by
  have key : ∀ a ∈ E.image Prod.fst, ∃ p ∈ E, p.1 = a := by
    intro a ha; simpa using ha
  let f : {a // a ∈ E.image Prod.fst} → {b // b ∈ E.image Prod.snd} := fun a =>
    ⟨(Classical.choose (key a.1 a.2)).2,
      mem_image_of_mem _ (Classical.choose_spec (key a.1 a.2)).1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have h1 := Classical.choose_spec (key a.1 a.2)
      have h2 := Classical.choose_spec (key a'.1 a'.2)
      have : (Classical.choose (key a.1 a.2)).2 = (Classical.choose (key a'.1 a'.2)).2 :=
        congrArg Subtype.val haa
      apply Subtype.ext
      rw [← h1.2, ← h2.2]
      exact (h _ h1.1 _ h2.1).2 this
    · intro b
      obtain ⟨q, hq, hqb⟩ := mem_image.1 b.2
      refine ⟨⟨q.1, mem_image_of_mem _ hq⟩, Subtype.ext ?_⟩
      have h1 := Classical.choose_spec (key q.1 (mem_image_of_mem _ hq))
      show (Classical.choose (key q.1 (mem_image_of_mem _ hq))).2 = b.1
      rw [← hqb]
      exact (h _ h1.1 _ hq).1 h1.2
  refine ⟨(Equiv.ofBijective f hf).extendSubtype, fun p hp => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem _ _ (mem_image_of_mem _ hp)]
  have h1 := Classical.choose_spec (key p.1 (mem_image_of_mem _ hp))
  exact (h _ h1.1 _ hp).1 h1.2

lemma card_ext (E : Finset (α × α)) :
    (univ.filter fun τ : Equiv.Perm α => ∀ p ∈ E, τ p.1 = p.2).card =
      if PInj E then (Fintype.card α - E.card).factorial else 0 := by
  split_ifs with h
  · obtain ⟨τ₀, hτ₀⟩ := exists_ext E h
    have hA : (E.image Prod.fst).card = E.card :=
      card_image_of_injOn (fun p hp q hq hpq => Prod.ext hpq ((h p hp q hq).1 hpq))
    rw [← hA, ← card_stab]
    refine card_nbij' (fun τ => τ₀⁻¹ * τ) (fun π => τ₀ * π) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
      intro a ha
      obtain ⟨p, hp, rfl⟩ : ∃ p ∈ E, p.1 = a := by simpa using ha
      rw [Equiv.Perm.mul_apply, hτ p hp, ← hτ₀ p hp]
      simp
    · intro π hπ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
      intro p hp
      rw [Equiv.Perm.mul_apply, hπ p.1 (mem_image_of_mem _ hp), hτ₀ p hp]
    · intro τ _; simp
    · intro π _; simp
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro τ _ hτ
    apply h
    intro p hp q hq
    constructor
    · intro e; rw [← hτ p hp, ← hτ q hq, e]
    · intro e; apply τ.injective; rw [hτ p hp, hτ q hq, e]

end Count

/-! ## Paths along a word -/

section Word

variable {d : ℕ} (w : List (Letter d))

/-- The label `i` of a letter `sᵢ` or `sᵢ*`. -/
def lab : Letter d → Option (Fin d)
  | none => none
  | some (Sum.inl i) => some i
  | some (Sum.inr i) => some i

/-- The directed edge `(a', b')` with `σᵢ a' = b'` forced by a step `xₜ = letter (xₜ₊₁)`, where
`a = xₜ`, `b = xₜ₊₁`. -/
def edge {α : Type*} : Letter d → α → α → α × α
  | some (Sum.inl _), a, b => (b, a)
  | _, a, b => (a, b)

lemma edge_cases {α : Type*} (l : Letter d) (a b : α) :
    ((edge l a b).1 = a ∧ (edge l a b).2 = b) ∨ ((edge l a b).1 = b ∧ (edge l a b).2 = a) := by
  rcases l with _ | i | i <;> simp [edge]

lemma edge_map {α β : Type*} (φ : β → α) (l : Letter d) (a b : β) :
    edge l (φ a) (φ b) = Prod.map φ φ (edge l a b) := by
  rcases l with _ | i | i <;> simp [edge]

/-- The edge set of label `i` of a path. -/
def Es {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) (i : Fin d) :
    Finset (α × α) :=
  (univ.filter fun t : Fin w.length => lab (w.get t) = some i).image
    fun t => edge (w.get t) (x t.castSucc) (x t.succ)

/-- The path stands still at the `none` letters. -/
def Cons {α : Type*} (x : Fin (w.length + 1) → α) : Prop :=
  ∀ t : Fin w.length, w.get t = none → x t.castSucc = x t.succ

/-- A closed consistent path whose edge sets are partial injections. -/
def Good {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) : Prop :=
  Cons w x ∧ (∀ i, PInj (Es w x i)) ∧ x 0 = x (Fin.last _)

instance {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) : Decidable (Cons w x) := by
  unfold Cons; infer_instance

instance {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) :
    Decidable (Good w x) := by
  unfold Good; infer_instance

/-- `σ` realises the path `x`. -/
def Rz {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) : Prop :=
  ∀ t : Fin w.length, x t.castSucc = letterPerm σ (w.get t) (x t.succ)

instance {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Decidable (Rz w σ x) := by
  unfold Rz; infer_instance

/-- The path of `y` under `σ`. -/
def path {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) : Fin (w.length + 1) → Fin N :=
  fun t => wordPerm σ (w.drop t) y

lemma wordPerm_cons_apply {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (l : Letter d)
    (ws : List (Letter d)) (y : Fin N) :
    wordPerm σ (l :: ws) y = letterPerm σ l (wordPerm σ ws y) := by
  simp [wordPerm, Equiv.Perm.mul_apply]

lemma path_last {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) :
    path w σ y (Fin.last _) = y := by
  simp [path, wordPerm]

lemma path_zero {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) :
    path w σ y 0 = wordPerm σ w y := by
  simp [path]

lemma path_step {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) (t : Fin w.length) :
    path w σ y t.castSucc = letterPerm σ (w.get t) (path w σ y t.succ) := by
  simp only [path, Fin.val_castSucc, Fin.val_succ]
  rw [List.drop_eq_getElem_cons t.2, wordPerm_cons_apply]
  rfl

lemma eq_path {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N)
    (hx : Rz w σ x) : x = path w σ (x (Fin.last _)) := by
  funext t
  induction t using Fin.reverseInduction with
  | last => rw [path_last]
  | cast t ih => rw [hx t, path_step, ← ih]

lemma fixCount_eq {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    fixCount (wordPerm σ w) =
      (univ.filter fun x : Fin (w.length + 1) → Fin N => Rz w σ x ∧ x 0 = x (Fin.last _)).card := by
  unfold fixCount
  symm
  refine card_nbij' (fun x => x (Fin.last _)) (path w σ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have := eq_path w σ x hx.1
    conv_rhs => rw [← hx.2, this]
    rw [path_zero]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    exact ⟨fun t => path_step w σ y t, by rw [path_zero, path_last, hy]⟩
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    exact (eq_path w σ x hx.1).symm
  · intro y _
    exact path_last w σ y

lemma Rz_iff {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Rz w σ x ↔ Cons w x ∧ ∀ i, ∀ p ∈ Es w x i, σ i p.1 = p.2 := by
  constructor
  · intro h
    refine ⟨fun t ht => by have := h t; rw [ht] at this; simpa [letterPerm] using this, ?_⟩
    intro i p hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
    rw [mem_filter] at ht
    have h' := h t
    generalize w.get t = l at ht h'
    rcases l with _ | j | j
    · simp [lab] at ht
    · simp only [lab, Option.some.injEq] at ht
      obtain ⟨-, rfl⟩ := ht
      simp only [edge]; exact h'.symm
    · simp only [lab, Option.some.injEq] at ht
      obtain ⟨-, rfl⟩ := ht
      simp only [edge, letterPerm] at h' ⊢
      rw [h']; simp
  · rintro ⟨hc, he⟩ t
    have hmem : ∀ j, lab (w.get t) = some j →
        edge (w.get t) (x t.castSucc) (x t.succ) ∈ Es w x j := fun j hj =>
      mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hj⟩, rfl⟩
    have hct := hc t
    generalize w.get t = l at hmem hct
    rcases l with _ | j | j
    · simp [letterPerm, hct rfl]
    · have := he j _ (hmem j rfl)
      simp only [edge] at this
      simp [letterPerm, this]
    · have := he j _ (hmem j rfl)
      simp only [edge] at this
      simp [letterPerm, ← this]

end Word

/-! ## Canonical representatives of kernels -/

section Canon

variable {n : ℕ} {α : Type*} [DecidableEq α]

/-- The first position where `x` takes the value `x t`. -/
def canon (x : Fin n → α) (t : Fin n) : Fin n :=
  (univ.filter fun s => x s = x t).min' ⟨t, by simp⟩

lemma canon_spec (x : Fin n → α) (t : Fin n) : x (canon x t) = x t := by
  unfold canon
  exact (mem_filter.1 (min'_mem (univ.filter fun s => x s = x t) _)).2

lemma canon_eq_of_ker {β : Type*} [DecidableEq β] (x : Fin n → α) (y : Fin n → β)
    (h : ∀ s t, x s = x t ↔ y s = y t) : canon x = canon y := by
  funext t
  simp only [canon, h]

lemma canon_ker (x : Fin n → α) (s t : Fin n) : canon x s = canon x t ↔ x s = x t := by
  constructor
  · intro h
    have := congrArg x h
    rwa [canon_spec x s, canon_spec x t] at this
  · intro h
    have : ∀ r, (x r = x s) ↔ (x r = x t) := fun r => by rw [h]
    simp only [canon, this]

lemma canon_canon (x : Fin n → α) : canon (canon x) = canon x :=
  canon_eq_of_ker _ _ (canon_ker x)

lemma canon_canon_apply (x : Fin n → α) (t : Fin n) : canon x (canon x t) = canon x t :=
  (canon_ker x _ _).2 (canon_spec x t)

lemma injOn_canon (x : Fin n → α) : Set.InjOn x (Set.range (canon x)) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
  rw [canon_spec x s, canon_spec x t] at h
  exact (canon_ker x s t).2 h

lemma comp_canon (x : Fin n → α) : x ∘ canon x = x := funext (canon_spec x)

/-- The number of values of a path. -/
def nv (x : Fin n → α) : ℕ := (univ.image x).card

lemma card_fiber [Fintype α] (c : Fin n → Fin n) (hc : canon c = c) :
    (univ.filter fun x : Fin n → α => canon x = c).card =
      (Fintype.card α).descFactorial (nv c) := by
  have hcc : ∀ t, c (c t) = c t := fun t => by
    have := canon_canon_apply c t; rwa [hc] at this
  have hmem : ∀ t, c t ∈ univ.image c := fun t => mem_image_of_mem _ (mem_univ _)
  rw [nv, ← Fintype.card_coe (univ.image c), ← Fintype.card_embedding_eq, ← card_univ]
  refine card_bij' (fun x hx => ⟨fun s => x s.1, ?_⟩) (fun φ _ => fun t => φ ⟨c t, hmem t⟩)
    (fun _ _ => mem_univ _) ?_ ?_ ?_
  · rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hx : canon x = c := (mem_filter.1 hx).2
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    obtain ⟨t', -, rfl⟩ := mem_image.1 hs'
    simp only at h
    apply Subtype.ext
    simp only
    rw [← hx] at h ⊢
    rw [canon_spec x t, canon_spec x t'] at h
    exact (canon_ker x t t').2 h
  · intro φ _
    simp only [mem_filter, mem_univ, true_and]
    refine Eq.trans ?_ hc
    refine canon_eq_of_ker _ _ fun s t => ?_
    rw [φ.injective.eq_iff, Subtype.mk.injEq]
  · intro x hx
    have hx : canon x = c := (mem_filter.1 hx).2
    funext t
    show x (c t) = x t
    rw [← hx]
    exact canon_spec x t
  · intro φ _
    apply Function.Embedding.ext
    rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    show φ ⟨c (c t), hmem (c t)⟩ = φ ⟨c t, hs⟩
    congr 2
    exact hcc t

end Canon

/-! ## Invariance under relabelling -/

section Invariance

variable {d : ℕ} (w : List (Letter d))

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype α] [Fintype β] in
lemma Es_comp (c : Fin (w.length + 1) → β) (φ : β → α) (i : Fin d) :
    Es w (φ ∘ c) i = (Es w c i).image (Prod.map φ φ) := by
  simp only [Es, image_image]
  refine image_congr fun t _ => ?_
  simp [edge_map]

omit [Fintype β] in
lemma Es_range (c : Fin (w.length + 1) → β) (i : Fin d) (p : β × β) (hp : p ∈ Es w c i) :
    p.1 ∈ Set.range c ∧ p.2 ∈ Set.range c := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 hp
  rcases edge_cases (w.get t) (c t.castSucc) (c t.succ) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

variable (c : Fin (w.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ

end Invariance

/-! ## The bounds on the invariants -/

section Bounds

variable {d : ℕ} (w : List (Letter d)) {α : Type*} [DecidableEq α]

lemma sum_card_Es_le (x : Fin (w.length + 1) → α) : ∑ i, (Es w x i).card ≤ w.length := by
  calc ∑ i, (Es w x i).card
      ≤ ∑ i, (univ.filter fun t : Fin w.length => lab (w.get t) = some i).card :=
        sum_le_sum fun i _ => card_image_le
    _ = (univ.biUnion fun i => univ.filter fun t : Fin w.length => lab (w.get t) = some i).card := by
        rw [card_biUnion]
        intro i _ j _ hij
        show Disjoint _ _
        rw [disjoint_filter]
        intro t _ hi hj
        exact hij (Option.some.inj (hi.symm.trans hj))
    _ ≤ w.length := (card_le_univ _).trans (Fintype.card_fin _).le

end Bounds

/-! ## Several closed walks -/

section Multi

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))

/-- Positions of the closed walks. -/
abbrev Pos := Σ k : ι, Fin ((u k).length + 1)

/-- Number of positions. -/
def nP : ℕ := Fintype.card (Pos u)

/-- An enumeration of the positions. -/
def eP : Pos u ≃ Fin (nP u) := Fintype.equivFin _

/-- The `k`-th walk of a labelling of the positions. -/
def cmp {α : Type*} (x : Fin (nP u) → α) (k : ι) : Fin ((u k).length + 1) → α :=
  fun j => x (eP u ⟨k, j⟩)

/-- All edges of label `i`. -/
def EsM {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) (i : Fin d) : Finset (α × α) :=
  univ.biUnion fun k => Es (u k) (cmp u x k) i

/-- Every walk is closed. -/
def ClM {α : Type*} (x : Fin (nP u) → α) : Prop :=
  ∀ k, cmp u x k 0 = cmp u x k (Fin.last _)

/-- Every walk stands still at `none`. -/
def ConsM {α : Type*} (x : Fin (nP u) → α) : Prop :=
  ∀ k, Cons (u k) (cmp u x k)

/-- Good labellings. -/
def GoodM {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) : Prop :=
  ConsM u x ∧ (∀ i, PInj (EsM u x i)) ∧ ClM u x

instance {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) : Decidable (ClM u x) := by
  unfold ClM; infer_instance

instance {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) : Decidable (ConsM u x) := by
  unfold ConsM; infer_instance

instance {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (nP u) → α) :
    Decidable (GoodM u x) := by
  unfold GoodM; infer_instance

/-- `σ` realises all walks. -/
def RzM {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (nP u) → Fin N) : Prop :=
  ∀ k, Rz (u k) σ (cmp u x k)

instance {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (nP u) → Fin N) :
    Decidable (RzM u σ x) := by
  unfold RzM; infer_instance

/-- The weight. -/
def GM (N : ℕ) {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (nP u) → α) : ℕ :=
  if GoodM u x then ∏ i, (N - (EsM u x i).card).factorial else 0

lemma prod_fixCount_eq {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    ∏ k, fixCount (wordPerm σ (u k)) =
      (univ.filter fun x : Fin (nP u) → Fin N => RzM u σ x ∧ ClM u x).card := by
  have hk : ∀ k, fixCount (wordPerm σ (u k)) =
      (univ.filter fun y : Fin ((u k).length + 1) → Fin N =>
        Rz (u k) σ y ∧ y 0 = y (Fin.last _)).card := fun k => fixCount_eq (u k) σ
  rw [prod_congr rfl (fun k _ => hk k), ← Fintype.card_piFinset]
  symm
  refine card_bij' (fun x _ => fun k => cmp u x k)
    (fun y _ => fun v => y ((eP u).symm v).1 ((eP u).symm v).2) ?_ ?_ ?_ ?_
  · intro x hx
    have hx := (mem_filter.1 hx).2
    rw [Fintype.mem_piFinset]
    exact fun k => mem_filter.2 ⟨mem_univ _, hx.1 k, hx.2 k⟩
  · intro y hy
    rw [Fintype.mem_piFinset] at hy
    have : ∀ k, cmp u (fun v => y ((eP u).symm v).1 ((eP u).symm v).2) k = y k := by
      intro k; funext j; simp only [cmp]; rw [Equiv.symm_apply_apply]
    refine mem_filter.2 ⟨mem_univ _, fun k => ?_, fun k => ?_⟩
    · rw [this]; exact (mem_filter.1 (hy k)).2.1
    · show cmp u _ k 0 = cmp u _ k _
      rw [this]; exact (mem_filter.1 (hy k)).2.2
  · intro x _
    funext v
    simp only [cmp]
    rw [Sigma.eta, Equiv.apply_symm_apply]
  · intro y _
    funext k j
    simp only [cmp]
    rw [Equiv.symm_apply_apply]

lemma RzM_iff {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (nP u) → Fin N) :
    RzM u σ x ↔ ConsM u x ∧ ∀ i, ∀ p ∈ EsM u x i, σ i p.1 = p.2 := by
  constructor
  · intro h
    refine ⟨fun k => ((Rz_iff (u k) σ _).1 (h k)).1, fun i p hp => ?_⟩
    obtain ⟨k, -, hk⟩ := mem_biUnion.1 hp
    exact ((Rz_iff (u k) σ _).1 (h k)).2 i p hk
  · rintro ⟨h1, h2⟩ k
    exact (Rz_iff (u k) σ _).2 ⟨h1 k, fun i p hp =>
      h2 i p (mem_biUnion.2 ⟨k, mem_univ _, hp⟩)⟩

lemma card_RzM {N : ℕ} (x : Fin (nP u) → Fin N) :
    (univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => RzM u σ x).card =
      if ConsM u x then
        ∏ i, (if PInj (EsM u x i) then (N - (EsM u x i).card).factorial else 0)
      else 0 := by
  split_ifs with hc
  · have : (univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => RzM u σ x) =
        Fintype.piFinset (fun i => univ.filter fun τ : Equiv.Perm (Fin N) =>
          ∀ p ∈ EsM u x i, τ p.1 = p.2) := by
      ext σ; simp [RzM_iff, hc, Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset]
    refine prod_congr rfl fun i _ => ?_
    rw [card_ext, Fintype.card_fin]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro σ _ h
    exact hc ((RzM_iff u σ x).1 h).1

lemma sum_prod_fixCount (N : ℕ) :
    ∑ σ : Fin d → Equiv.Perm (Fin N), ∏ k, fixCount (wordPerm σ (u k)) =
      ∑ x : Fin (nP u) → Fin N, GM u N x := by
  simp only [prod_fixCount_eq, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← card_filter]
  by_cases hcl : ClM u x
  · simp only [hcl, and_true]
    rw [card_RzM, GM]
    by_cases hg : GoodM u x
    · rw [if_pos hg, if_pos hg.1]
      exact prod_congr rfl fun i _ => if_pos (hg.2.1 i)
    · rw [if_neg hg]
      split_ifs with hc
      · have : ¬ ∀ i, PInj (EsM u x i) := fun h => hg ⟨hc, h, hcl⟩
        push Not at this
        obtain ⟨i, hi⟩ := this
        exact prod_eq_zero (mem_univ i) (if_neg hi)
      · rfl
  · simp only [hcl, and_false, GM]
    rw [if_neg (fun h => hcl h.2.2)]
    simp

section InvM

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype α] [Fintype β] in
lemma EsM_comp (c : Fin (nP u) → β) (φ : β → α) (i : Fin d) :
    EsM u (φ ∘ c) i = (EsM u c i).image (Prod.map φ φ) := by
  unfold EsM
  rw [biUnion_image]
  refine biUnion_congr rfl fun k _ => ?_
  exact Es_comp (u k) (cmp u c k) φ i

omit [Fintype β] in
lemma EsM_range (c : Fin (nP u) → β) (i : Fin d) (p : β × β) (hp : p ∈ EsM u c i) :
    p.1 ∈ Set.range c ∧ p.2 ∈ Set.range c := by
  obtain ⟨k, -, hk⟩ := mem_biUnion.1 hp
  have h := Es_range (u k) (cmp u c k) i p hk
  obtain ⟨⟨j1, hj1⟩, ⟨j2, hj2⟩⟩ := h
  exact ⟨⟨_, hj1⟩, ⟨_, hj2⟩⟩

variable (c : Fin (nP u) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ

omit [Fintype α] [Fintype β] in
lemma card_EsM_comp (i : Fin d) : (EsM u (φ ∘ c) i).card = (EsM u c i).card := by
  rw [EsM_comp]
  refine card_image_of_injOn fun p hp q hq hpq => ?_
  have hp' := EsM_range u c i p hp
  have hq' := EsM_range u c i q hq
  simp only [Prod.map, Prod.mk.injEq] at hpq
  exact Prod.ext (hφ hp'.1 hq'.1 hpq.1) (hφ hp'.2 hq'.2 hpq.2)

omit [Fintype α] [Fintype β] in
lemma goodM_comp : GoodM u (φ ∘ c) ↔ GoodM u c := by
  have key : ∀ s t, φ (c s) = φ (c t) ↔ c s = c t := fun s t =>
    hφ.eq_iff ⟨s, rfl⟩ ⟨t, rfl⟩
  have hP : ∀ i, PInj (EsM u (φ ∘ c) i) ↔ PInj (EsM u c i) := by
    intro i
    rw [EsM_comp]
    unfold PInj
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Prod.map_fst,
      Prod.map_snd]
    refine forall₂_congr fun p hp => forall₂_congr fun q hq => ?_
    have hp' := EsM_range u c i p hp
    have hq' := EsM_range u c i q hq
    rw [hφ.eq_iff hp'.1 hq'.1, hφ.eq_iff hp'.2 hq'.2]
  unfold GoodM ConsM ClM Cons cmp
  simp only [Function.comp, key, hP]

lemma GM_comp (N : ℕ) : GM u N (φ ∘ c) = GM u N c := by
  unfold GM
  simp only [goodM_comp u c φ hφ, card_EsM_comp u c φ hφ]

end InvM

section BoundsM

variable {α : Type*} [DecidableEq α]

lemma sum_card_EsM_le (x : Fin (nP u) → α) : ∑ i, (EsM u x i).card ≤ ∑ k, (u k).length := by
  calc ∑ i, (EsM u x i).card ≤ ∑ i, ∑ k, (Es (u k) (cmp u x k) i).card :=
        sum_le_sum fun i _ => card_biUnion_le
    _ = ∑ k, ∑ i, (Es (u k) (cmp u x k) i).card := sum_comm
    _ ≤ ∑ k, (u k).length := sum_le_sum fun k _ => sum_card_Es_le (u k) _

end BoundsM

/-! ## Walks read along `ℤ` -/

section Walks

variable {α : Type*} [DecidableEq α]

lemma emod_nn (j : ℤ) {n : ℕ} (hn : 0 < n) : 0 ≤ j % (n : ℤ) := Int.emod_nonneg _ (by omega)

lemma emod_lt (j : ℤ) {n : ℕ} (hn : 0 < n) : j % (n : ℤ) < n := Int.emod_lt_of_pos _ (by omega)

lemma toNat_emod (j : ℤ) {n : ℕ} (hn : 0 < n) : ((j % (n : ℤ)).toNat : ℤ) = j % n :=
  Int.toNat_of_nonneg (emod_nn j hn)

lemma toNat_emod_lt (j : ℤ) {n : ℕ} (hn : 0 < n) : (j % (n : ℤ)).toNat < n := by
  have := emod_lt j hn; have := emod_nn j hn; omega

/-- Walk `k` of a labelling, read periodically along `ℤ`. -/
def W (x : Fin (nP u) → α) (k : ι) (j : ℤ) : α :=
  cmp u x k ⟨min (j % ((u k).length : ℤ)).toNat (u k).length,
    Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The letter of step `j` of walk `k`. -/
def Al (k : ι) (j : ℤ) : Letter d := (u k).getD (j % ((u k).length : ℤ)).toNat none

lemma W_eq_of_val (x : Fin (nP u) → α) (k : ι) (j : ℤ) (jj : Fin ((u k).length + 1))
    (h : min (j % ((u k).length : ℤ)).toNat (u k).length = jj.val) :
    W u x k j = cmp u x k jj := by
  unfold W; congr 1; exact Fin.ext h

lemma W_mem (x : Fin (nP u) → α) (k : ι) (j : ℤ) : W u x k j ∈ univ.image x :=
  mem_image_of_mem _ (mem_univ _)

lemma W_mod (x : Fin (nP u) → α) (k : ι) {j j' : ℤ}
    (h : j % ((u k).length : ℤ) = j' % ((u k).length : ℤ)) : W u x k j = W u x k j' := by
  unfold W; simp only [h]

lemma Al_mod (k : ι) {j j' : ℤ}
    (h : j % ((u k).length : ℤ) = j' % ((u k).length : ℤ)) : Al u k j = Al u k j' := by
  unfold Al; rw [h]

lemma W_fin (x : Fin (nP u) → α) (hcl : ClM u x) (k : ι) (jj : Fin ((u k).length + 1)) :
    W u x k (jj.val : ℤ) = cmp u x k jj := by
  rcases Nat.lt_or_ge jj.val (u k).length with h | h
  · apply W_eq_of_val
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    simp; omega
  · have hj : jj = Fin.last _ := Fin.ext (by simp; omega)
    subst hj
    rw [← hcl k]
    apply W_eq_of_val
    simp

lemma Al_val (k : ι) (n : ℕ) (hn : n < (u k).length) : Al u k n = (u k).get ⟨n, hn⟩ := by
  unfold Al
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  simp [List.getElem?_eq_getElem hn]

lemma step (x : Fin (nP u) → α) (hcl : ClM u x) (k : ι) (hL : 0 < (u k).length) (j : ℤ) :
    ∃ t : Fin (u k).length, W u x k j = cmp u x k t.castSucc ∧
      W u x k (j + 1) = cmp u x k t.succ ∧ Al u k j = (u k).get t := by
  have h1 := toNat_emod j hL
  have h2 := toNat_emod_lt j hL
  refine ⟨⟨(j % ((u k).length : ℤ)).toNat, h2⟩, ?_, ?_, ?_⟩
  · apply W_eq_of_val; simp; omega
  · have : W u x k (j + 1) = W u x k (((j % ((u k).length : ℤ)).toNat + 1 : ℕ) : ℤ) := by
      apply W_mod
      push_cast
      rw [h1, Int.emod_add_emod]
    rw [this]
    exact W_fin u x hcl k (Fin.succ ⟨(j % ((u k).length : ℤ)).toNat, h2⟩)
  · rw [show Al u k j = Al u k ((j % ((u k).length : ℤ)).toNat : ℕ) from Al_mod u k (by rw [h1, Int.emod_emod_of_dvd _ (dvd_refl _)])]
    exact Al_val u k _ h2

lemma mem_EsM_iff (x : Fin (nP u) → α) (hcl : ClM u x) (hL : ∀ k, 0 < (u k).length)
    (i : Fin d) (p : α × α) :
    p ∈ EsM u x i ↔ ∃ k, ∃ j : ℤ, lab (Al u k j) = some i ∧
      edge (Al u k j) (W u x k j) (W u x k (j + 1)) = p := by
  constructor
  · intro hp
    obtain ⟨k, -, hk⟩ := mem_biUnion.1 hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hk
    have ht := (mem_filter.1 ht).2
    refine ⟨k, t.val, ?_, ?_⟩
    · rw [Al_val u k t.val t.2]; exact ht
    · rw [Al_val u k t.val t.2]
      have e1 := W_fin u x hcl k t.castSucc
      have e2 := W_fin u x hcl k t.succ
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at e1 e2
      rw [e1, e2]
  · rintro ⟨k, j, hl, rfl⟩
    obtain ⟨t, e1, e2, e3⟩ := step u x hcl k (hL k) j
    rw [e1, e2, e3]
    rw [e3] at hl
    exact mem_biUnion.2 ⟨k, mem_univ _, mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl⟩, rfl⟩⟩

end Walks

/-! ## Half-edges and degrees -/

section Half

variable {α : Type*} [DecidableEq α]

/-- The used half-edges: `(z, l)` means that a step with letter `l` leaves `z` along an edge. -/
def Hs (x : Fin (nP u) → α) : Finset (α × Letter d) :=
  univ.biUnion fun i => (EsM u x i).image (fun p => (p.2, some (Sum.inl i))) ∪
    (EsM u x i).image (fun p => (p.1, some (Sum.inr i)))

lemma letterInv_letterInv (l : Letter d) : letterInv (letterInv l) = l := by
  rcases l with _ | i | i <;> rfl

lemma letterInv_ne_self {l : Letter d} (h : l ≠ none) : letterInv l ≠ l := by
  rcases l with _ | i | i <;> simp_all [letterInv]

lemma card_Hs (x : Fin (nP u) → α) (hP : ∀ i, PInj (EsM u x i)) :
    (Hs u x).card = 2 * ∑ i, (EsM u x i).card := by
  unfold Hs
  rw [card_biUnion, mul_sum]
  · refine sum_congr rfl fun i _ => ?_
    rw [card_union_of_disjoint]
    · rw [card_image_of_injOn, card_image_of_injOn]
      · ring
      · intro p hp q hq h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 ((hP i p hp q hq).1 h.1)
      · intro p hp q hq h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext ((hP i p hp q hq).2 h.1) h.1
    · rw [disjoint_left]
      intro z h1 h2
      obtain ⟨p, -, rfl⟩ := mem_image.1 h1
      obtain ⟨q, -, h⟩ := mem_image.1 h2
      simp at h
  · intro i _ j _ hij
    rw [Function.onFun, disjoint_left]
    intro z h1 h2
    rcases mem_union.1 h1 with h1 | h1 <;> rcases mem_union.1 h2 with h2 | h2 <;>
    · obtain ⟨p, -, rfl⟩ := mem_image.1 h1
      obtain ⟨q, -, h⟩ := mem_image.1 h2
      simp only [Prod.mk.injEq, Option.some.injEq, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, and_false] at h
      all_goals exact hij h.2.symm

lemma Hs_fst (x : Fin (nP u) → α) {z : α} {l : Letter d} (h : (z, l) ∈ Hs u x) :
    z ∈ univ.image x := by
  simp only [Hs, mem_biUnion, mem_univ, true_and, mem_union, mem_image] at h
  obtain ⟨i, ⟨p, hp, hpz⟩ | ⟨p, hp, hpz⟩⟩ := h
  · simp only [Prod.mk.injEq] at hpz
    obtain ⟨-, ⟨j, hj⟩⟩ := EsM_range u x i p hp
    rw [← hpz.1, ← hj]; exact mem_image_of_mem _ (mem_univ _)
  · simp only [Prod.mk.injEq] at hpz
    obtain ⟨⟨j, hj⟩, -⟩ := EsM_range u x i p hp
    rw [← hpz.1, ← hj]; exact mem_image_of_mem _ (mem_univ _)

lemma mem_Hs_step (x : Fin (nP u) → α) (hcl : ClM u x) (hL : ∀ k, 0 < (u k).length)
    (k : ι) (j : ℤ) (hn : Al u k j ≠ none) :
    (W u x k j, Al u k j) ∈ Hs u x ∧ (W u x k (j + 1), letterInv (Al u k j)) ∈ Hs u x := by
  have hmem : ∀ i, lab (Al u k j) = some i →
      edge (Al u k j) (W u x k j) (W u x k (j + 1)) ∈ EsM u x i :=
    fun i hi => (mem_EsM_iff u x hcl hL i _).2 ⟨k, j, hi, rfl⟩
  generalize Al u k j = l at hmem hn
  rcases l with _ | i | i
  · exact absurd rfl hn
  · have h := hmem i rfl
    simp only [edge] at h
    constructor
    · exact mem_biUnion.2 ⟨i, mem_univ _, mem_union_left _ (mem_image.2 ⟨_, h, rfl⟩)⟩
    · exact mem_biUnion.2 ⟨i, mem_univ _, mem_union_right _ (mem_image.2 ⟨_, h, rfl⟩)⟩
  · have h := hmem i rfl
    simp only [edge] at h
    constructor
    · exact mem_biUnion.2 ⟨i, mem_univ _, mem_union_right _ (mem_image.2 ⟨_, h, rfl⟩)⟩
    · exact mem_biUnion.2 ⟨i, mem_univ _, mem_union_left _ (mem_image.2 ⟨_, h, rfl⟩)⟩

lemma Hs_desc (x : Fin (nP u) → α) (hcl : ClM u x) (hL : ∀ k, 0 < (u k).length)
    {z : α} {l : Letter d} (h : (z, l) ∈ Hs u x) :
    ∃ k, ∃ j : ℤ, W u x k j = z ∧ (l = Al u k j ∨ l = letterInv (Al u k (j - 1))) := by
  simp only [Hs, mem_biUnion, mem_univ, true_and, mem_union, mem_image] at h
  obtain ⟨i, ⟨p, hp, hpz⟩ | ⟨p, hp, hpz⟩⟩ := h
  · simp only [Prod.mk.injEq] at hpz
    obtain ⟨k, j, hl, rfl⟩ := (mem_EsM_iff u x hcl hL i p).1 hp
    obtain ⟨rfl, rfl⟩ := hpz
    generalize ha : Al u k j = a at hl
    rcases a with _ | i' | i' <;> simp only [lab, reduceCtorEq, Option.some.injEq] at hl
    · subst hl
      exact ⟨k, j, by simp [edge], Or.inl ha.symm⟩
    · subst hl
      refine ⟨k, j + 1, by simp [edge], Or.inr ?_⟩
      rw [add_sub_cancel_right, ha]; rfl
  · simp only [Prod.mk.injEq] at hpz
    obtain ⟨k, j, hl, rfl⟩ := (mem_EsM_iff u x hcl hL i p).1 hp
    obtain ⟨rfl, rfl⟩ := hpz
    generalize ha : Al u k j = a at hl
    rcases a with _ | i' | i' <;> simp only [lab, reduceCtorEq, Option.some.injEq] at hl
    · subst hl
      refine ⟨k, j + 1, by simp [edge], Or.inr ?_⟩
      rw [add_sub_cancel_right, ha]; rfl
    · subst hl
      exact ⟨k, j, by simp [edge], Or.inl ha.symm⟩

/-- The degree of `z`: the number of used half-edges at `z`. -/
def deg (x : Fin (nP u) → α) (z : α) : ℕ := ((Hs u x).filter (fun p => p.1 = z)).card

lemma sum_deg (x : Fin (nP u) → α) :
    (Hs u x).card = ∑ z ∈ univ.image x, deg u x z := by
  unfold deg
  exact card_eq_sum_card_fiberwise (fun p hp => Hs_fst u x (z := p.1) (l := p.2) hp)

/-- The standing hypotheses on the walks. -/
structure WH : Prop where
  len : ∀ k, 0 < (u k).length
  nn : ∀ k j, Al u k j ≠ none
  cr : ∀ k j, Al u k (j + 1) ≠ letterInv (Al u k j)

variable {u}

lemma two_le_deg (hw : WH u) (x : Fin (nP u) → α) (hcl : ClM u x) (k : ι) (j : ℤ) :
    2 ≤ deg u x (W u x k j) := by
  have h1 := (mem_Hs_step u x hcl hw.len k j (hw.nn k j)).1
  have h2 := (mem_Hs_step u x hcl hw.len k (j - 1) (hw.nn k (j - 1))).2
  rw [sub_add_cancel] at h2
  have hne : Al u k j ≠ letterInv (Al u k (j - 1)) := by
    have := hw.cr k (j - 1); rwa [sub_add_cancel] at this
  unfold deg
  have hsub : ({(W u x k j, Al u k j), (W u x k j, letterInv (Al u k (j - 1)))} :
      Finset (α × Letter d)) ⊆ (Hs u x).filter (fun p => p.1 = W u x k j) := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact mem_filter.2 ⟨h1, rfl⟩
    · exact mem_filter.2 ⟨h2, rfl⟩
  have := card_le_card hsub
  rw [card_pair (by simpa using hne)] at this
  exact this

lemma two_le_deg' (hw : WH u) (x : Fin (nP u) → α) (hcl : ClM u x) (z : α)
    (hz : z ∈ univ.image x) : 2 ≤ deg u x z := by
  obtain ⟨q, -, rfl⟩ := mem_image.1 hz
  have hq : x q = W u x ((eP u).symm q).1 (((eP u).symm q).2.val : ℤ) := by
    rw [W_fin u x hcl]
    simp [cmp]
  rw [hq]
  exact two_le_deg hw x hcl _ _

theorem nv_le_e (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x) :
    nv x ≤ ∑ i, (EsM u x i).card := by
  have h1 := card_Hs u x hg.2.1
  rw [sum_deg] at h1
  have h2 : ∑ z ∈ univ.image x, 2 ≤ ∑ z ∈ univ.image x, deg u x z :=
    sum_le_sum fun z hz => two_le_deg' hw x hg.2.2 z hz
  rw [sum_const, smul_eq_mul] at h2
  unfold nv
  omega

theorem deg_le_two (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x)
    (heq : nv x = ∑ i, (EsM u x i).card) : ∀ z ∈ univ.image x, deg u x z ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨z0, hz0, hlt⟩ := hc
  have h1 := card_Hs u x hg.2.1
  rw [sum_deg] at h1
  have h2 : ∑ z ∈ univ.image x, 2 < ∑ z ∈ univ.image x, deg u x z :=
    sum_lt_sum (fun z hz => two_le_deg' hw x hg.2.2 z hz) ⟨z0, hz0, hlt⟩
  rw [sum_const, smul_eq_mul] at h2
  unfold nv at heq
  omega

theorem e_le_nv (x : Fin (nP u) → α) (hP : ∀ i, PInj (EsM u x i))
    (hdeg : ∀ z ∈ univ.image x, deg u x z ≤ 2) : ∑ i, (EsM u x i).card ≤ nv x := by
  have h1 := card_Hs u x hP
  rw [sum_deg] at h1
  have h2 : ∑ z ∈ univ.image x, deg u x z ≤ ∑ z ∈ univ.image x, 2 := sum_le_sum hdeg
  rw [sum_const, smul_eq_mul] at h2
  unfold nv
  omega

lemma three {β : Type*} [DecidableEq β] {S : Finset β} (hS : S.card ≤ 2) {a b c : β}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hcb : c ≠ b) : c = a := by
  by_contra hca
  have hsub : ({a, b, c} : Finset β) ⊆ S := by
    intro y hy; simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hab, Ne.symm hca]),
    card_pair (Ne.symm hcb)] at this
  omega

/-! ## Determinism and lockstep -/

lemma edge_iff (l : Letter d) {a b a' b' : α} (h : a = a' ↔ b = b') :
    (edge l a b).1 = (edge l a' b').1 ↔ (edge l a b).2 = (edge l a' b').2 := by
  rcases l with _ | i | i <;> simp only [edge] <;> tauto

lemma edge_inv {l : Letter d} (hl : l ≠ none) (a b : α) :
    edge (letterInv l) a b = edge l b a := by
  rcases l with _ | i | i
  · exact absurd rfl hl
  · rfl
  · rfl

lemma lab_inv (l : Letter d) : lab (letterInv l) = lab l := by
  rcases l with _ | i | i <;> rfl

lemma lab_ne_none' {l : Letter d} (h : l ≠ none) : lab l ≠ none := by
  rcases l with _ | i | i <;> simp_all [lab]

lemma pinj_edge {E : Finset (α × α)} (hP : PInj E) (l : Letter d) {a b a' b' : α}
    (hp : edge l a b ∈ E) (hq : edge l a' b' ∈ E) : (a = a' ↔ b = b') := by
  have := hP _ hp _ hq
  rcases l with _ | i | i <;> simp only [edge] at this
  · exact this
  · exact this.symm
  · exact this

lemma step_mem (x : Fin (nP u) → α) (hcl : ClM u x) (hL : ∀ k, 0 < (u k).length)
    (k : ι) (j : ℤ) (i : Fin d) (hi : lab (Al u k j) = some i) :
    edge (Al u k j) (W u x k j) (W u x k (j + 1)) ∈ EsM u x i :=
  (mem_EsM_iff u x hcl hL i _).2 ⟨k, j, hi, rfl⟩

lemma det (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x) (k k' : ι) (j j' : ℤ)
    (hA : Al u k j = Al u k' j') :
    W u x k j = W u x k' j' ↔ W u x k (j + 1) = W u x k' (j' + 1) := by
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (lab_ne_none' (hw.nn k j))
  have hp := step_mem x hg.2.2 hw.len k j i hi
  have hq := step_mem x hg.2.2 hw.len k' j' i (hA ▸ hi)
  rw [← hA] at hq
  exact pinj_edge (hg.2.1 i) _ hp hq

lemma det_iter (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x) (k k' : ι) (j j' : ℤ)
    (hA : ∀ i : ℕ, Al u k (j + i) = Al u k' (j' + i)) :
    ∀ n : ℕ, (W u x k j = W u x k' j' ↔ W u x k (j + n) = W u x k' (j' + n)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, det hw x hg k k' _ _ (hA n)]
    push_cast
    simp only [add_assoc]

lemma fwd (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x)
    (hdeg : ∀ z ∈ univ.image x, deg u x z ≤ 2) (k k' : ι) (j j' : ℤ)
    (hW : W u x k j = W u x k' j') (hA : Al u k j = Al u k' j') :
    ∀ n : ℕ, W u x k (j + n) = W u x k' (j' + n) ∧ Al u k (j + n) = Al u k' (j' + n) := by
  intro n
  induction n with
  | zero => simpa using ⟨hW, hA⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e1 : W u x k (j + n + 1) = W u x k' (j' + n + 1) := (det hw x hg k k' _ _ ih2).1 ih1
    have hcl := hg.2.2
    have m1 := (mem_Hs_step u x hcl hw.len k (j + n + 1) (hw.nn _ _)).1
    have m2 := (mem_Hs_step u x hcl hw.len k (j + n) (hw.nn _ _)).2
    have m3 := (mem_Hs_step u x hcl hw.len k' (j' + n + 1) (hw.nn _ _)).1
    rw [← e1] at m3
    have hS := hdeg _ (W_mem u x k (j + n + 1))
    unfold deg at hS
    have := three hS (mem_filter.2 ⟨m1, rfl⟩) (mem_filter.2 ⟨m2, rfl⟩)
      (mem_filter.2 ⟨m3, rfl⟩)
      (by simpa using hw.cr k (j + n))
      (by have := hw.cr k' (j' + n); rw [← ih2] at this; simpa using this)
    simp only [Prod.mk.injEq, true_and] at this
    push_cast
    simp only [← add_assoc]
    exact ⟨e1, this.symm⟩

lemma bwd (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x)
    (hdeg : ∀ z ∈ univ.image x, deg u x z ≤ 2) (k k' : ι) (j j' : ℤ)
    (hW : W u x k j = W u x k' j') (hA : Al u k' j' = letterInv (Al u k (j - 1))) :
    ∀ n : ℕ, W u x k (j - n) = W u x k' (j' + n) ∧
      Al u k' (j' + n) = letterInv (Al u k (j - 1 - n)) := by
  intro n
  induction n with
  | zero => simpa using ⟨hW, hA⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hcl := hg.2.2
    set a0 := j - 1 - (n : ℤ) with ha0
    have q1 : a0 + 1 = j - n := by rw [ha0]; ring
    have q2 : j - ((n + 1 : ℕ) : ℤ) = a0 := by rw [ha0]; push_cast; ring
    have q3 : j' + ((n + 1 : ℕ) : ℤ) = j' + n + 1 := by push_cast; ring
    have q4 : j - 1 - ((n + 1 : ℕ) : ℤ) = a0 - 1 := by rw [ha0]; push_cast; ring
    rw [q2, q3, q4]
    have hl := hw.nn k a0
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (lab_ne_none' hl)
    have hp := step_mem x hcl hw.len k a0 i hi
    have hq := step_mem x hcl hw.len k' (j' + n) i (by rw [ih2, lab_inv]; exact hi)
    rw [ih2, edge_inv hl] at hq
    have e1 : W u x k a0 = W u x k' (j' + n + 1) :=
      (pinj_edge (hg.2.1 i) _ hp hq).2 (by rw [q1]; exact ih1)
    have m1 := (mem_Hs_step u x hcl hw.len k a0 hl).1
    have m2 := (mem_Hs_step u x hcl hw.len k (a0 - 1) (hw.nn _ _)).2
    rw [sub_add_cancel] at m2
    have m3 := (mem_Hs_step u x hcl hw.len k' (j' + n + 1) (hw.nn _ _)).1
    rw [← e1] at m3
    have hS := hdeg _ (W_mem u x k a0)
    unfold deg at hS
    have := three hS (mem_filter.2 ⟨m2, rfl⟩) (mem_filter.2 ⟨m1, rfl⟩)
      (mem_filter.2 ⟨m3, rfl⟩) ?_ ?_
    · simp only [Prod.mk.injEq, true_and] at this
      exact ⟨e1, this⟩
    · have := hw.cr k (a0 - 1)
      rw [sub_add_cancel] at this
      simpa using (Ne.symm this)
    · have := hw.cr k' (j' + n)
      rw [ih2, letterInv_letterInv] at this
      simpa using this

end Half

/-! ## Powers of a cyclically reduced non-power -/

section Pow

variable {d : ℕ} (r : List (Letter d))

/-- The letters of `r`, read periodically along `ℤ`. -/
def R (j : ℤ) : Letter d := r.getD (j % (r.length : ℤ)).toNat none

lemma R_congr {j j' : ℤ} (h : j ≡ j' [ZMOD (r.length : ℤ)]) : R r j = R r j' := by
  unfold R; rw [show j % (r.length : ℤ) = j' % (r.length : ℤ) from h]

lemma R_add_mul (j q : ℤ) : R r (j + q * r.length) = R r j :=
  R_congr r (Int.add_mul_emod_self_right j q _)

lemma R_natCast (n : ℕ) : R r n = r.getD (n % r.length) none := by
  unfold R; rw [← Int.natCast_mod, Int.toNat_natCast]

lemma length_powList' (k : ℕ) : (powList r k).length = k * r.length := by
  simp [powList, List.length_flatten, List.map_replicate, List.sum_replicate]

variable {r}

lemma R_ne_none (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none) (j : ℤ) : R r j ≠ none := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  unfold R
  have h := toNat_emod_lt j hℓ
  rw [List.getD_eq_getElem _ _ h]
  exact hnone _ (List.getElem_mem h)

lemma R_cr (hr : r ≠ []) (hcyc : CycRed r) (j : ℤ) : R r (j + 1) ≠ letterInv (R r j) := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have h := toNat_emod_lt j hℓ
  have key := hcyc ⟨(j % (r.length : ℤ)).toNat, h⟩
  simp only [List.get_eq_getElem] at key
  have e1 : R r j = r[(j % (r.length : ℤ)).toNat] := by
    unfold R; rw [List.getD_eq_getElem _ _ h]
  have e2 : R r (j + 1) = r[((j % (r.length : ℤ)).toNat + 1) % r.length]'(Nat.mod_lt _ hℓ) := by
    rw [R_congr r (j' := ((((j % (r.length : ℤ)).toNat + 1) % r.length : ℕ) : ℤ)), R_natCast,
      Nat.mod_mod, List.getD_eq_getElem _ _ (Nat.mod_lt _ hℓ)]
    show (j + 1) % (r.length : ℤ) = _ % _
    push_cast
    rw [Int.emod_emod_of_dvd _ (dvd_refl _), toNat_emod j hℓ, Int.emod_add_emod]
  rw [e1, e2]; exact key

/-- `r` is primitive: equal shifted letter sequences have congruent shifts. -/
lemma prim (hr : r ≠ []) (hnp : IsNonPower (wordFree r)) (j j' : ℤ)
    (h : ∀ n : ℕ, R r (j + n) = R r (j' + n)) : j ≡ j' [ZMOD (r.length : ℤ)] := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  let f : ℕ → Letter d := fun t => R r t
  have hδc := toNat_emod (j' - j) hℓ
  have hδℓ := toNat_emod_lt (j' - j) hℓ
  set δ := ((j' - j) % (r.length : ℤ)).toNat with hδ
  have hper : N52.PartG.IsPer f δ := by
    intro t
    have := h ((((t : ℤ) - j) % r.length).toNat)
    rw [toNat_emod _ hℓ] at this
    simp only [f]
    push_cast
    rw [R_congr r (j := (t : ℤ)) (j' := j + ((t : ℤ) - j) % r.length), this]
    · apply R_congr
      rw [hδc]
      have h1 := ((Int.mod_modEq ((t : ℤ) - j) r.length).add_left j')
      have h2 := ((Int.mod_modEq (j' - j) r.length).add_left (t : ℤ))
      refine h2.trans ?_
      rw [show (t : ℤ) + (j' - j) = j' + ((t : ℤ) - j) by ring]
      exact h1.symm
    · have h1 := ((Int.mod_modEq ((t : ℤ) - j) r.length).add_left j)
      refine (h1.trans ?_).symm
      ring_nf; rfl
  have hperℓ : N52.PartG.IsPer f r.length := by
    intro t
    simp only [f]
    push_cast
    exact R_congr r (Int.add_emod_right _ _)
  by_cases hδ0 : δ = 0
  · rw [hδ0] at hδc
    exact (Int.modEq_iff_dvd.2 (Int.dvd_of_emod_eq_zero (by simpa using hδc.symm)))
  · exfalso
    have hg := N52.PartG.per_gcd f δ r.length hper hperℓ
    set g := Nat.gcd δ r.length
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgδ : g ≤ δ := Nat.gcd_le_left _ (by omega)
    have hgℓ : g ∣ 1 * r.length := by rw [one_mul]; exact Nat.gcd_dvd_right _ _
    have hfA : ∀ t, f t = N52.PartG.A r (t % r.length) := by
      intro t; simp only [f, R_natCast]; rfl
    have := N52.PartG.per_dvd r hr hnp 1 le_rfl g hg0 hgℓ (by
      intro t ht
      rw [one_mul] at ht
      rw [N52.PartG.A_pow r hr 1 t (by omega),
        N52.PartG.A_pow r hr 1 (t % g) (by have := Nat.mod_lt t hg0; omega), ← hfA, ← hfA]
      have := N52.PartG.per_mul hg (t / g) (t % g)
      rw [Nat.mod_add_div] at this
      exact this)
    have := Nat.le_of_dvd hg0 this
    omega

/-- A cyclically reduced word is not a rotation of its inverse. -/
lemma no_refl (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none) (hcyc : CycRed r) (a b : ℤ)
    (h : ∀ n : ℕ, R r (a + n) = letterInv (R r (b - n))) : False := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hall : ∀ y : ℤ, R r y = letterInv (R r (a + b - y)) := by
    intro y
    have := h (((y - a) % r.length).toNat)
    rw [toNat_emod _ hℓ] at this
    have h1 := (Int.mod_modEq (y - a) r.length).add_left a
    rw [R_congr r (j := y) (j' := a + (y - a) % r.length) (by
      refine (h1.trans ?_).symm; ring_nf; rfl), this]
    congr 1
    apply R_congr
    have h2 := (Int.mod_modEq (y - a) r.length).sub_left b
    refine h2.trans ?_; ring_nf; rfl
  set c := (a + b) % (r.length : ℤ) with hcdef
  have hc0 := emod_nn (a + b) hℓ
  have hcℓ := emod_lt (a + b) hℓ
  have hc : ∀ y, R r y = letterInv (R r (c - y)) := by
    intro y
    rw [hall y]
    congr 1
    apply R_congr
    exact ((Int.mod_modEq (a + b) r.length).sub_right y).symm
  obtain ⟨e, he | he⟩ := Int.even_or_odd' c
  · have := hc e
    rw [show c - e = e by omega] at this
    exact letterInv_ne_self (R_ne_none hr hnone e) this.symm
  · obtain ⟨f, hf | hf⟩ := Nat.even_or_odd' r.length
    · have := hc e
      rw [show c - e = e + 1 by omega] at this
      exact R_cr hr hcyc e (by rw [this, letterInv_letterInv])
    · have := hc (e + f + 1)
      rw [show c - (e + f + 1) = (e + f + 1) + (-1) * (r.length : ℤ) by rw [hf]; push_cast; omega,
        R_add_mul] at this
      exact letterInv_ne_self (R_ne_none hr hnone _) this.symm

variable (r) {s : ℕ} (m : Fin s → ℕ)

/-- The walks `r ^ m_t`. -/
def uR : Fin s → List (Letter d) := fun t => powList r (m t)

lemma len_uR (k : Fin s) : (uR r m k).length = m k * r.length := length_powList' r _

variable {r m}

lemma Al_uR (hr : r ≠ []) (hm : ∀ t, 1 ≤ m t) (k : Fin s) (j : ℤ) :
    Al (uR r m) k j = R r j := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hL : 0 < (uR r m k).length := by rw [len_uR]; exact Nat.mul_pos (hm k) hℓ
  have hn := toNat_emod_lt j hL
  unfold Al
  rw [show (uR r m k) = (List.replicate (m k) r).flatten from rfl,
    N52.PartG.getD_flat r none hr (m k) _ (by rw [← len_uR r m k]; exact hn)]
  unfold R
  congr 1
  have e : ((((j % ((uR r m k).length : ℤ)).toNat % r.length : ℕ)) : ℤ) =
      ((j % (r.length : ℤ)).toNat : ℤ) := by
    push_cast
    rw [toNat_emod _ hL, toNat_emod _ hℓ]
    exact Int.emod_emod_of_dvd _ ⟨m k, by rw [len_uR]; push_cast; ring⟩
  exact_mod_cast e

lemma WH_uR (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none) (hcyc : CycRed r) (hm : ∀ t, 1 ≤ m t) :
    WH (uR r m) where
  len k := by rw [len_uR]; exact Nat.mul_pos (hm k) (List.length_pos_iff.2 hr)
  nn k j := by rw [Al_uR hr hm]; exact R_ne_none hr hnone j
  cr k j := by rw [Al_uR hr hm, Al_uR hr hm]; exact R_cr hr hcyc j

/-- In a colouring of degree `≤ 2`, a vertex determines the phase modulo `|r|`. -/
theorem phase {α : Type*} [DecidableEq α] (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hnp : IsNonPower (wordFree r)) (hm : ∀ t, 1 ≤ m t)
    (x : Fin (nP (uR r m)) → α) (hg : GoodM (uR r m) x)
    (hdeg : ∀ z ∈ univ.image x, deg (uR r m) x z ≤ 2) (k k' : Fin s) (j j' : ℤ)
    (hW : W (uR r m) x k j = W (uR r m) x k' j') : j ≡ j' [ZMOD (r.length : ℤ)] := by
  have hw := WH_uR hr hnone hcyc hm
  have hcl := hg.2.2
  have m1 := (mem_Hs_step _ x hcl hw.len k j (hw.nn _ _)).1
  have m2 := (mem_Hs_step _ x hcl hw.len k (j - 1) (hw.nn _ _)).2
  rw [sub_add_cancel] at m2
  have m3 := (mem_Hs_step _ x hcl hw.len k' j' (hw.nn _ _)).1
  rw [← hW] at m3
  have hS := hdeg _ (W_mem _ x k j)
  unfold deg at hS
  have hab : Al (uR r m) k j ≠ letterInv (Al (uR r m) k (j - 1)) := by
    have := hw.cr k (j - 1); rwa [sub_add_cancel] at this
  have hor : Al (uR r m) k' j' = Al (uR r m) k j ∨
      Al (uR r m) k' j' = letterInv (Al (uR r m) k (j - 1)) := by
    by_contra hc
    push Not at hc
    have := three hS (mem_filter.2 ⟨m1, rfl⟩) (mem_filter.2 ⟨m2, rfl⟩) (mem_filter.2 ⟨m3, rfl⟩)
      (by simpa using hab) (by simpa using hc.2)
    simp only [Prod.mk.injEq, true_and] at this
    exact hc.1 this
  rcases hor with h1 | h1
  · have := fwd hw x hg hdeg k k' j j' hW h1.symm
    apply prim hr hnp j j'
    intro n
    have := (this n).2
    rwa [Al_uR hr hm, Al_uR hr hm] at this
  · have := bwd hw x hg hdeg k k' j j' hW h1
    exfalso
    apply no_refl hr hnone hcyc j' (j - 1)
    intro n
    have := (this n).2
    rwa [Al_uR hr hm, Al_uR hr hm] at this

end Pow

/-! ## The bijection with the colourings of `g₁ ^ m_t` -/

section Bij

/-- Canonical good colourings. -/
def CGM {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d)) :
    Finset (Fin (nP u) → Fin (nP u)) :=
  (univ.filter fun c : Fin (nP u) → Fin (nP u) => canon c = c).filter (GoodM u)

lemma nv_canon {n : ℕ} {β : Type*} [DecidableEq β] (y : Fin n → β) : nv (canon y) = nv y := by
  unfold nv
  conv_rhs => rw [← comp_canon y, ← image_image]
  refine (card_image_of_injOn ?_).symm
  intro a ha b hb hab
  simp only [coe_image, coe_univ, Set.image_univ] at ha hb
  exact injOn_canon y ha hb hab

lemma arith (j : ℤ) (M ℓ : ℕ) (hM : 0 < M) (hℓ : 0 < ℓ) :
    (j % ((M * ℓ : ℕ) : ℤ)).toNat / ℓ = ((j / ℓ) % M).toNat ∧
      (j % ((M * ℓ : ℕ) : ℤ)).toNat % ℓ = (j % ℓ).toNat := by
  have hj := Int.mul_ediv_add_emod j ℓ
  have ha := Int.mul_ediv_add_emod (j / ℓ) M
  have hb0 := emod_nn j hℓ
  have hbℓ := emod_lt j hℓ
  have ham0 := emod_nn (j / ℓ) hM
  have hamM := emod_lt (j / ℓ) hM
  have hℓ' : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  have key : j % ((M * ℓ : ℕ) : ℤ) = ℓ * ((j / ℓ) % M) + j % ℓ := by
    have := (Int.ediv_emod_unique (a := j) (b := ((M * ℓ : ℕ) : ℤ))
      (q := (j / ℓ) / M) (r := ℓ * ((j / ℓ) % M) + j % ℓ) (by positivity)).2
      ⟨by push_cast; linear_combination hj + (ℓ : ℤ) * ha, by positivity, by
        push_cast; nlinarith⟩
    exact this.2
  have hn : ((j % ((M * ℓ : ℕ) : ℤ)).toNat : ℤ) = ℓ * ((j / ℓ) % M) + j % ℓ := by
    rw [Int.toNat_of_nonneg (by rw [key]; positivity), key]
  push_cast at hn
  constructor
  · have : (((j % ((M * ℓ : ℕ) : ℤ)).toNat / ℓ : ℕ) : ℤ) = (((j / ℓ) % M).toNat : ℤ) := by
      push_cast
      rw [hn, toNat_emod _ hM, add_comm, Int.add_mul_ediv_left _ _ (by omega),
        Int.ediv_eq_zero_of_lt hb0 hbℓ, zero_add]
    exact_mod_cast this
  · have : (((j % ((M * ℓ : ℕ) : ℤ)).toNat % ℓ : ℕ) : ℤ) = ((j % ℓ).toNat : ℤ) := by
      push_cast
      rw [hn, toNat_emod _ hℓ, add_comm, Int.add_mul_emod_self_left, Int.emod_emod_of_dvd _
        (dvd_refl _)]
    exact_mod_cast this

lemma ediv_succ (j : ℤ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    (j + 1) / ℓ = if j % ℓ + 1 < ℓ then j / ℓ else j / ℓ + 1 := by
  have hj := Int.mul_ediv_add_emod j ℓ
  have hb0 := emod_nn j hℓ
  have hbℓ := emod_lt j hℓ
  have hℓ' : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  split_ifs with h
  · exact ((Int.ediv_emod_unique hℓ').2 ⟨by linear_combination hj, by omega, h⟩).1
  · have h' : j % (ℓ : ℤ) + 1 = ℓ := by omega
    exact ((Int.ediv_emod_unique (r := 0) hℓ').2 ⟨by linear_combination hj - h', le_refl _,
      hℓ'⟩).1

variable {d : ℕ} (r : List (Letter d)) {s : ℕ} (m : Fin s → ℕ)

/-- The one-letter word `g₁`. -/
abbrev l0 : Letter 1 := some (Sum.inl 0)

/-- The walks `g₁ ^ m_t`. -/
def u0 : Fin s → List (Letter 1) := fun t => powList [l0] (m t)

lemma len_u0 (k : Fin s) : (u0 m k).length = m k := by
  rw [u0, length_powList']; simp

variable {m}

lemma Al_u0 (hm : ∀ t, 1 ≤ m t) (k : Fin s) (j : ℤ) : Al (u0 m) k j = l0 := by
  have hL : 0 < (u0 m k).length := by rw [len_u0]; exact hm k
  have hn := toNat_emod_lt j hL
  unfold Al
  rw [show u0 m k = (List.replicate (m k) [l0]).flatten from rfl,
    N52.PartG.getD_flat [l0] none (by simp) (m k) _ (by simpa [len_u0] using hn)]
  simp only [List.length_singleton, Nat.mod_one]
  rfl

lemma WH_u0 (hm : ∀ t, 1 ≤ m t) : WH (u0 m) where
  len k := by rw [len_u0]; exact hm k
  nn k j := by rw [Al_u0 hm]; simp
  cr k j := by rw [Al_u0 hm, Al_u0 hm]; simp [letterInv]

variable {r}

lemma phi_bound (k : Fin s) (a : ℕ) (h : a < (u0 m k).length + 1) :
    a * r.length < (uR r m k).length + 1 := by
  have e1 := len_u0 m k
  have e2 := len_uR r m k
  have h3 : a ≤ m k := by omega
  have := Nat.mul_le_mul_right r.length h3
  omega

lemma psi_bound (k : Fin s) (a : ℕ) (h : a < (uR r m k).length + 1) :
    a / r.length < (u0 m k).length + 1 := by
  have e1 := len_u0 m k
  have e2 := len_uR r m k
  have : a / r.length ≤ m k := Nat.div_le_of_le_mul (by rw [mul_comm]; omega)
  omega

/-- Position `(k, a)` of a `g₁`-walk goes to position `(k, a |r|)`. -/
def phiS (p : Pos (u0 m)) : Pos (uR r m) := ⟨p.1, ⟨p.2.val * r.length, phi_bound p.1 _ p.2.2⟩⟩

def phi (q : Fin (nP (u0 m))) : Fin (nP (uR r m)) := eP (uR r m) (phiS ((eP (u0 m)).symm q))

/-- Position `(k, j)` of an `r`-walk goes to position `(k, ⌊j / |r|⌋)`. -/
def psiS (p : Pos (uR r m)) : Pos (u0 m) := ⟨p.1, ⟨p.2.val / r.length, psi_bound p.1 _ p.2.2⟩⟩

def psi (q : Fin (nP (uR r m))) : Fin (nP (u0 m)) := eP (u0 m) (psiS ((eP (uR r m)).symm q))

/-- The phase `j mod |r|`. -/
def phS (p : Pos (uR r m)) : ℕ := p.2.val % r.length

def ph (q : Fin (nP (uR r m))) : ℕ := phS ((eP (uR r m)).symm q)

/-- The periodic extension of a colouring of the `g₁`-walks. -/
def ext {β : Type*} (c₀ : Fin (nP (u0 m)) → β) : Fin (nP (uR r m)) → β × ℕ :=
  fun q => (c₀ (psi (r := r) q), ph q)

lemma cmp_phi {β : Type*} (c : Fin (nP (uR r m)) → β) (k : Fin s)
    (jj : Fin ((u0 m k).length + 1)) :
    cmp (u0 m) (c ∘ phi) k jj = cmp (uR r m) c k ⟨jj.val * r.length, phi_bound k _ jj.2⟩ := by
  simp only [cmp, Function.comp, phi, Equiv.symm_apply_apply]
  rfl

lemma cmp_ext {β : Type*} (c₀ : Fin (nP (u0 m)) → β) (k : Fin s)
    (jj : Fin ((uR r m k).length + 1)) :
    cmp (uR r m) (ext c₀) k jj = (cmp (u0 m) c₀ k ⟨jj.val / r.length, psi_bound k _ jj.2⟩,
      jj.val % r.length) := by
  simp only [cmp, ext, psi, ph, Equiv.symm_apply_apply]
  rfl

lemma psi_phi (hr : r ≠ []) (q : Fin (nP (u0 m))) : psi (r := r) (phi q) = q := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  simp only [psi, phi, Equiv.symm_apply_apply]
  conv_rhs => rw [← (eP (u0 m)).apply_symm_apply q]
  congr 1
  generalize (eP (u0 m)).symm q = p
  obtain ⟨k, jj⟩ := p
  simp only [psiS, phiS]
  congr 1
  exact Fin.ext (Nat.mul_div_cancel _ hℓ)

lemma ph_phi (q : Fin (nP (u0 m))) : ph (r := r) (phi q) = 0 := by
  unfold ph phi
  rw [Equiv.symm_apply_apply]
  simp [phS, phiS]

lemma ClM_res {β : Type*} (c : Fin (nP (uR r m)) → β) (hcl : ClM (uR r m) c) :
    ClM (u0 m) (c ∘ phi) := by
  intro k
  rw [cmp_phi, cmp_phi]
  convert hcl k using 2 <;> apply Fin.ext <;> simp [len_u0, len_uR]

lemma ClM_ext {β : Type*} (hr : r ≠ []) (c₀ : Fin (nP (u0 m)) → β) (hcl : ClM (u0 m) c₀) :
    ClM (uR r m) (ext (r := r) c₀) := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  intro k
  rw [cmp_ext, cmp_ext]
  refine Prod.ext ?_ ?_
  · convert hcl k using 2 <;> apply Fin.ext <;> simp [len_u0, len_uR, Nat.mul_div_cancel _ hℓ]
  · simp [len_uR]

lemma W_res {β : Type*} [DecidableEq β] (hr : r ≠ []) (hm : ∀ t, 1 ≤ m t)
    (c : Fin (nP (uR r m)) → β) (hcl : ClM (uR r m) c) (k : Fin s) (a : ℤ) :
    W (u0 m) (c ∘ phi) k a = W (uR r m) c k (a * r.length) := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hℓ' : (0 : ℤ) < r.length := by exact_mod_cast hℓ
  have hL : 0 < (u0 m k).length := by rw [len_u0]; exact hm k
  have h1 := toNat_emod_lt a hL
  rw [W_eq_of_val (u0 m) (c ∘ phi) k a ⟨(a % ((u0 m k).length : ℤ)).toNat, by omega⟩
    (by simp; omega), cmp_phi, ← W_fin _ c hcl]
  apply W_mod
  simp only [Fin.val_mk]
  push_cast
  rw [toNat_emod a hL]
  have e1 : ((u0 m k).length : ℤ) = m k := by rw [len_u0]
  have e2 : ((uR r m k).length : ℤ) = r.length * m k := by rw [len_uR]; push_cast; ring
  rw [e1, e2, mul_comm _ (r.length : ℤ), mul_comm a (r.length : ℤ),
    Int.mul_emod_mul_of_pos _ _ hℓ', Int.mul_emod_mul_of_pos _ _ hℓ',
    Int.emod_emod_of_dvd _ (dvd_refl _)]

lemma W_ext {β : Type*} [DecidableEq β] (hr : r ≠ []) (hm : ∀ t, 1 ≤ m t)
    (c₀ : Fin (nP (u0 m)) → β) (k : Fin s) (j : ℤ) :
    W (uR r m) (ext (r := r) c₀) k j =
      (W (u0 m) c₀ k (j / r.length), (j % (r.length : ℤ)).toNat) := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hL : 0 < (uR r m k).length := by rw [len_uR]; exact Nat.mul_pos (hm k) hℓ
  have h1 := toNat_emod_lt j hL
  rw [W_eq_of_val (uR r m) _ k j ⟨(j % ((uR r m k).length : ℤ)).toNat, by omega⟩
    (by simp; omega), cmp_ext]
  have har := arith j (m k) r.length (hm k) hℓ
  rw [← len_uR] at har
  rw [har.2]
  congr 1
  have hL0 : 0 < (u0 m k).length := by rw [len_u0]; exact hm k
  refine (W_eq_of_val (u0 m) c₀ k _ _ ?_).symm
  simp only
  rw [har.1, len_u0]
  have := toNat_emod_lt (j / r.length) (hm k)
  omega

end Bij

/-! ## Goodness of the restriction and of the extension; the count -/

section Count

variable {d : ℕ} {r : List (Letter d)} {s : ℕ} {m : Fin s → ℕ}

lemma lab_cases {l l' : Letter d} (hl : l ≠ none) (h : lab l = lab l') :
    l' = l ∨ l' = letterInv l := by
  rcases l with _ | i | i <;> rcases l' with _ | j | j <;> simp_all [lab, letterInv]

theorem good_res {β : Type*} [DecidableEq β] (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hm : ∀ t, 1 ≤ m t) (c : Fin (nP (uR r m)) → β)
    (hg : GoodM (uR r m) c) : GoodM (u0 m) (c ∘ phi) := by
  have hw := WH_uR hr hnone hcyc hm
  have hw0 := WH_u0 hm
  have hcl0 := ClM_res c hg.2.2
  refine ⟨?_, ?_, hcl0⟩
  · intro k t ht
    exfalso
    have := hw0.nn k t.val
    rw [Al_val (u0 m) k t.val t.2] at this
    exact this ht
  · intro i p hp q hq
    obtain ⟨k, a, -, rfl⟩ := (mem_EsM_iff _ _ hcl0 hw0.len i p).1 hp
    obtain ⟨k', a', -, rfl⟩ := (mem_EsM_iff _ _ hcl0 hw0.len i q).1 hq
    rw [Al_u0 hm, Al_u0 hm]
    apply edge_iff
    rw [W_res hr hm c hg.2.2, W_res hr hm c hg.2.2, W_res hr hm c hg.2.2,
      W_res hr hm c hg.2.2]
    have := det_iter hw c hg k k' (a * r.length) (a' * r.length) ?_ r.length
    · rw [this, show (a + 1) * (r.length : ℤ) = a * r.length + r.length by ring,
        show (a' + 1) * (r.length : ℤ) = a' * r.length + r.length by ring]
    · intro i
      simp only [Al_uR hr hm]
      rw [add_comm (a * _), add_comm (a' * _), R_add_mul, R_add_mul]

lemma Y_phase {β : Type*} [DecidableEq β] (hr : r ≠ []) (hm : ∀ t, 1 ≤ m t)
    (c₀ : Fin (nP (u0 m)) → β) {k k' : Fin s} {j j' : ℤ}
    (h : W (uR r m) (ext (r := r) c₀) k j = W (uR r m) (ext (r := r) c₀) k' j') :
    j ≡ j' [ZMOD (r.length : ℤ)] := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  rw [W_ext hr hm, W_ext hr hm, Prod.mk.injEq] at h
  have := congrArg (fun n : ℕ => (n : ℤ)) h.2
  simp only [toNat_emod _ hℓ] at this
  exact this

theorem good_ext {β : Type*} [DecidableEq β] (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hm : ∀ t, 1 ≤ m t) (c₀ : Fin (nP (u0 m)) → β)
    (hg₀ : GoodM (u0 m) c₀) : GoodM (uR r m) (ext (r := r) c₀) := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hw := WH_uR hr hnone hcyc hm
  have hw0 := WH_u0 hm
  have hcl := ClM_ext hr c₀ hg₀.2.2
  have Ydet : ∀ k k' j j', (W (uR r m) (ext (r := r) c₀) k j = W (uR r m) (ext (r := r) c₀) k' j' ↔
      W (uR r m) (ext (r := r) c₀) k (j + 1) = W (uR r m) (ext (r := r) c₀) k' (j' + 1)) := by
    intro k k' j j'
    by_cases hph : j ≡ j' [ZMOD (r.length : ℤ)]
    · rw [W_ext hr hm, W_ext hr hm, W_ext hr hm, W_ext hr hm]
      simp only [Prod.mk.injEq]
      have p1 : (j % (r.length : ℤ)).toNat = (j' % (r.length : ℤ)).toNat := by
        rw [show j % (r.length : ℤ) = j' % (r.length : ℤ) from hph]
      have p2 : ((j + 1) % (r.length : ℤ)).toNat = ((j' + 1) % (r.length : ℤ)).toNat := by
        rw [show (j + 1) % (r.length : ℤ) = (j' + 1) % (r.length : ℤ) from hph.add_right 1]
      simp only [p1, p2, and_true]
      rw [ediv_succ j hℓ, ediv_succ j' hℓ,
        show j' % (r.length : ℤ) = j % (r.length : ℤ) from hph.symm]
      split_ifs
      · exact Iff.rfl
      · exact det hw0 c₀ hg₀ k k' _ _ (by rw [Al_u0 hm, Al_u0 hm])
    · exact iff_of_false (fun h => hph (Y_phase hr hm c₀ h))
        (fun h => hph (Int.ModEq.add_right_cancel' 1 (Y_phase hr hm c₀ h)))
  refine ⟨?_, ?_, hcl⟩
  · intro k t ht
    exfalso
    have := hw.nn k t.val
    rw [Al_val (uR r m) k t.val t.2] at this
    exact this ht
  · intro i p hp q hq
    obtain ⟨k, j, hl, rfl⟩ := (mem_EsM_iff _ _ hcl hw.len i p).1 hp
    obtain ⟨k', j', hl', rfl⟩ := (mem_EsM_iff _ _ hcl hw.len i q).1 hq
    rcases lab_cases (hw.nn k j) (hl.trans hl'.symm) with h | h
    · rw [h]; exact edge_iff _ (Ydet k k' j j')
    · rw [h, edge_inv (hw.nn k j)]
      apply edge_iff
      refine iff_of_false (fun he => ?_) (fun he => ?_)
      · have := Y_phase hr hm c₀ he
        apply hw.cr k' j'
        simp only [Al_uR hr hm] at h ⊢
        rw [h, letterInv_letterInv]
        exact (R_congr r this).symm
      · have := Y_phase hr hm c₀ he
        apply hw.cr k j
        simp only [Al_uR hr hm] at h ⊢
        rw [← h]
        exact R_congr r this

lemma deg_ext {β : Type*} [DecidableEq β] (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hm : ∀ t, 1 ≤ m t) (c₀ : Fin (nP (u0 m)) → β)
    (hg₀ : GoodM (u0 m) c₀) :
    ∀ z ∈ univ.image (ext (r := r) c₀), deg (uR r m) (ext (r := r) c₀) z ≤ 2 := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hw := WH_uR hr hnone hcyc hm
  have hcl := ClM_ext hr c₀ hg₀.2.2
  intro z _
  unfold deg
  have hsub : (Hs (uR r m) (ext (r := r) c₀)).filter (fun p => p.1 = z) ⊆
      {(z, R r (z.2 : ℤ)), (z, letterInv (R r ((z.2 : ℤ) - 1)))} := by
    rintro ⟨z', l⟩ hp'
    obtain ⟨hp, hpz⟩ := mem_filter.1 hp'
    simp only at hpz
    subst hpz
    obtain ⟨k, j, hW, hl⟩ := Hs_desc _ _ hcl hw.len hp
    rw [W_ext hr hm] at hW
    subst hW
    simp only [Al_uR hr hm] at hl
    simp only [mem_insert, mem_singleton, Prod.mk.injEq, true_and]
    rcases hl with rfl | rfl
    · left
      apply R_congr
      rw [toNat_emod j hℓ]
      exact (Int.mod_modEq j _).symm
    · right
      congr 1
      apply R_congr
      rw [toNat_emod j hℓ]
      exact ((Int.mod_modEq j _).sub_right 1).symm
  exact (card_le_card hsub).trans (card_insert_le _ _)

lemma key_iff {β : Type*} [DecidableEq β] (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hnp : IsNonPower (wordFree r)) (hm : ∀ t, 1 ≤ m t)
    (c : Fin (nP (uR r m)) → β) (hg : GoodM (uR r m) c)
    (hdeg : ∀ z ∈ univ.image c, deg (uR r m) c z ≤ 2) (k k' : Fin s) (jj jj' : ℕ) :
    W (uR r m) c k jj = W (uR r m) c k' jj' ↔
      W (uR r m) c k ((jj / r.length * r.length : ℕ) : ℤ) =
        W (uR r m) c k' ((jj' / r.length * r.length : ℕ) : ℤ) ∧
        jj % r.length = jj' % r.length := by
  have hw := WH_uR hr hnone hcyc hm
  have hA : ∀ i : ℕ, Al (uR r m) k (((jj / r.length * r.length : ℕ) : ℤ) + i) =
      Al (uR r m) k' (((jj' / r.length * r.length : ℕ) : ℤ) + i) := by
    intro i
    simp only [Al_uR hr hm]
    push_cast
    rw [add_comm _ (i : ℤ), add_comm _ (i : ℤ), R_add_mul, R_add_mul]
  have hdi := det_iter hw c hg k k' _ _ hA
  have e1 : ((jj / r.length * r.length : ℕ) : ℤ) + ((jj % r.length : ℕ) : ℤ) = jj := by
    exact_mod_cast Nat.div_add_mod' jj r.length
  constructor
  · intro h
    have hp := phase hr hnone hcyc hnp hm c hg hdeg k k' jj jj' h
    have hp' : jj % r.length = jj' % r.length := by
      unfold Int.ModEq at hp; exact_mod_cast hp
    have e2 : ((jj' / r.length * r.length : ℕ) : ℤ) + ((jj % r.length : ℕ) : ℤ) = jj' := by
      rw [hp']; exact_mod_cast Nat.div_add_mod' jj' r.length
    refine ⟨(hdi (jj % r.length)).2 ?_, hp'⟩
    rw [e1, e2]; exact h
  · rintro ⟨h, hp'⟩
    have e2 : ((jj' / r.length * r.length : ℕ) : ℤ) + ((jj % r.length : ℕ) : ℤ) = jj' := by
      rw [hp']; exact_mod_cast Nat.div_add_mod' jj' r.length
    rw [← e1, ← e2]
    exact (hdi _).1 h

lemma c_phi_psi {β : Type*} (c : Fin (nP (uR r m)) → β) (k : Fin s)
    (jj : Fin ((uR r m k).length + 1)) :
    c (phi (psi (r := r) (eP (uR r m) ⟨k, jj⟩))) =
      cmp (uR r m) c k ⟨jj.val / r.length * r.length,
        phi_bound k _ (psi_bound k _ jj.2)⟩ := by
  simp only [psi, phi, Equiv.symm_apply_apply]
  rfl

lemma ph_eP (k : Fin s) (jj : Fin ((uR r m k).length + 1)) :
    ph (r := r) (eP (uR r m) ⟨k, jj⟩) = jj.val % r.length := by
  unfold ph
  rw [Equiv.symm_apply_apply]
  rfl

theorem card_B (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none) (hcyc : CycRed r)
    (hnp : IsNonPower (wordFree r)) (hm : ∀ t, 1 ≤ m t) :
    ((CGM (uR r m)).filter (fun c => nv c = ∑ i, (EsM (uR r m) c i).card)).card =
      (CGM (u0 m)).card := by
  have hw := WH_uR hr hnone hcyc hm
  refine card_bij' (fun c _ => canon (c ∘ phi)) (fun c₀ _ => canon (ext (r := r) c₀))
    ?_ ?_ ?_ ?_
  · intro c hc
    simp only [CGM, mem_filter, mem_univ, true_and] at hc ⊢
    refine ⟨canon_canon _, ?_⟩
    have := goodM_comp (u0 m) (canon (c ∘ phi)) (c ∘ phi) (injOn_canon _)
    rw [comp_canon] at this
    exact this.1 (good_res hr hnone hcyc hm c hc.1.2)
  · intro c₀ hc₀
    simp only [CGM, mem_filter, mem_univ, true_and] at hc₀ ⊢
    have hgy := good_ext hr hnone hcyc hm c₀ hc₀.2
    have := goodM_comp (uR r m) (canon (ext (r := r) c₀)) (ext (r := r) c₀) (injOn_canon _)
    rw [comp_canon] at this
    refine ⟨⟨canon_canon _, this.1 hgy⟩, ?_⟩
    rw [nv_canon]
    have e : ∀ i, (EsM (uR r m) (canon (ext (r := r) c₀)) i).card =
        (EsM (uR r m) (ext (r := r) c₀) i).card := fun i => by
      have := card_EsM_comp (uR r m) (canon (ext (r := r) c₀)) (ext (r := r) c₀)
        (injOn_canon _) i
      rw [comp_canon] at this
      exact this.symm
    simp only [e]
    exact le_antisymm (nv_le_e hw _ hgy)
      (e_le_nv _ hgy.2.1 (deg_ext hr hnone hcyc hm c₀ hc₀.2))
  · intro c hc
    simp only [CGM, mem_filter, mem_univ, true_and] at hc
    obtain ⟨⟨hcan, hg⟩, hve⟩ := hc
    have hdeg := deg_le_two hw c hg hve
    show canon (ext (r := r) (canon (c ∘ phi))) = c
    conv_rhs => rw [← hcan]
    apply canon_eq_of_ker
    intro q q'
    obtain ⟨⟨k, jj⟩, rfl⟩ := (eP (uR r m)).surjective q
    obtain ⟨⟨k', jj'⟩, rfl⟩ := (eP (uR r m)).surjective q'
    simp only [ext, Prod.mk.injEq, canon_ker, Function.comp, c_phi_psi, ph_eP]
    have h1 : ∀ k (jj : Fin ((uR r m k).length + 1)), c (eP (uR r m) ⟨k, jj⟩) =
        W (uR r m) c k (jj.val : ℤ) := fun k jj => (W_fin _ c hg.2.2 k jj).symm
    rw [h1, h1, ← W_fin _ c hg.2.2, ← W_fin _ c hg.2.2]
    exact (key_iff hr hnone hcyc hnp hm c hg hdeg k k' jj jj').symm
  · intro c₀ hc₀
    simp only [CGM, mem_filter, mem_univ, true_and] at hc₀
    show canon (canon (ext (r := r) c₀) ∘ phi) = c₀
    conv_rhs => rw [← hc₀.1]
    apply canon_eq_of_ker
    intro a b
    simp only [Function.comp, canon_ker, ext, Prod.mk.injEq, psi_phi hr, ph_phi, and_true]

end Count

/-! ## The expectation formula and the limit -/

section Main

theorem expect_eq {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
    (N : ℕ) (hL : ∑ k, (u k).length ≤ N) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ((∏ k, fixCount (wordPerm σ (u k)) : ℕ) : ℝ)) =
      ∑ c ∈ CGM u, (N.descFactorial (nv c) : ℝ) / ∏ i, (N.descFactorial (EsM u c i).card : ℝ) := by
  have h1 : ∑ σ : Fin d → Equiv.Perm (Fin N), ∏ k, fixCount (wordPerm σ (u k)) =
      ∑ c ∈ (univ.filter fun c : Fin (nP u) → Fin (nP u) => canon c = c),
        if GoodM u c then N.descFactorial (nv c) * ∏ i, (N - (EsM u c i).card).factorial
        else 0 := by
    rw [sum_prod_fixCount, ← sum_fiberwise_of_maps_to (s := univ)
      (t := univ.filter fun c : Fin (nP u) → Fin (nP u) => canon c = c)
      (g := canon) (fun x _ => mem_filter.2 ⟨mem_univ _, canon_canon x⟩)]
    refine sum_congr rfl fun c hc => ?_
    have hc := (mem_filter.1 hc).2
    have hG : ∀ x ∈ univ.filter fun x : Fin (nP u) → Fin N => canon x = c,
        GM u N x = GM u N c := by
      intro x hx
      have hx := (mem_filter.1 hx).2
      rw [← hx]
      conv_lhs => rw [← comp_canon x]
      exact GM_comp u (canon x) x (injOn_canon x) N
    rw [sum_congr rfl hG, sum_const, card_fiber c hc, Fintype.card_fin, smul_eq_mul, GM]
    split_ifs <;> simp
  unfold uniformExp
  rw [← Nat.cast_sum, h1, ← sum_filter]
  have hcard : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) = (N.factorial : ℝ) ^ d := by
    simp [Fintype.card_perm]
  rw [hcard, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun c _ => ?_
  have he : ∀ i, (EsM u c i).card ≤ N := fun i =>
    (single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)).trans
      ((sum_card_EsM_le u c).trans hL)
  have hfac : (N.factorial : ℝ) ^ d =
      (∏ i, (N.descFactorial (EsM u c i).card : ℝ)) *
        ∏ i, ((N - (EsM u c i).card).factorial : ℝ) := by
    rw [← prod_mul_distrib,
      show (N.factorial : ℝ) ^ d = ∏ _i : Fin d, (N.factorial : ℝ) by simp]
    refine prod_congr rfl fun i _ => ?_
    rw [← Nat.cast_mul, mul_comm, Nat.factorial_mul_descFactorial (he i)]
  simp only [Nat.cast_mul, Nat.cast_prod]
  rw [hfac, mul_div_mul_right _ _ (prod_ne_zero_iff.2 fun i _ => by positivity)]

/-- The limit: the number of canonical good colourings of the walks `g₁ ^ m_t`. -/
def Fm (s : ℕ) (m : Fin s → ℕ) : ℕ := by
  classical exact if ∀ t, 1 ≤ m t then (CGM (u0 m)).card else 0

lemma deg_u0 {s : ℕ} {m : Fin s → ℕ} {β : Type*} [DecidableEq β] (x : Fin (nP (u0 m)) → β) :
    ∀ z ∈ univ.image x, deg (u0 m) x z ≤ 2 := by
  intro z _
  unfold deg
  have hsub : (Hs (u0 m) x).filter (fun p => p.1 = z) ⊆
      {(z, some (Sum.inl 0)), (z, some (Sum.inr 0))} := by
    rintro ⟨z', l⟩ hp'
    obtain ⟨hp, hpz⟩ := mem_filter.1 hp'
    simp only at hpz
    subst hpz
    simp only [Hs, mem_biUnion, mem_univ, true_and, mem_union, mem_image, Prod.mk.injEq] at hp
    obtain ⟨i, ⟨p, -, -, rfl⟩ | ⟨p, -, -, rfl⟩⟩ := hp
    · simp [Subsingleton.elim i 0]
    · simp [Subsingleton.elim i 0]
  exact (card_le_card hsub).trans (card_insert_le _ _)

theorem Fm_bound (s : ℕ) (m : Fin s → ℕ) :
    (Fm s m : ℝ) ≤ (1 + ∑ t, (m t : ℝ)) ^ (2 * s) := by
  classical
  have h1 : (1 : ℝ) ≤ 1 + ∑ t, (m t : ℝ) := by
    have : (0 : ℝ) ≤ ∑ t, (m t : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
    linarith
  by_cases hm : ∀ t, 1 ≤ m t
  swap
  · unfold Fm; rw [if_neg hm]; simp only [Nat.cast_zero]; positivity
  unfold Fm
  rw [if_pos hm]
  set N := 1 + ∑ t, m t with hN
  have hL : ∑ k, (u0 m k).length ≤ N := by simp only [len_u0]; omega
  have hE := expect_eq (u0 m) N hL
  have hw0 := WH_u0 hm
  have hterm : ∀ c ∈ CGM (u0 m),
      (N.descFactorial (nv c) : ℝ) / ∏ i, (N.descFactorial (EsM (u0 m) c i).card : ℝ) = 1 := by
    intro c hc
    have hg := (mem_filter.1 hc).2
    have hve : nv c = ∑ i, (EsM (u0 m) c i).card :=
      le_antisymm (nv_le_e hw0 c hg) (e_le_nv c hg.2.1 (deg_u0 c))
    rw [Fin.sum_univ_one] at hve
    rw [Fin.prod_univ_one, hve]
    have : (EsM (u0 m) c 0).card ≤ N := by
      have := (single_le_sum (fun j _ => Nat.zero_le _) (mem_univ (0 : Fin 1))).trans
        ((sum_card_EsM_le (u0 m) c).trans hL)
      exact this
    have hpos : (0 : ℝ) < N.descFactorial (EsM (u0 m) c 0).card := by
      exact_mod_cast Nat.descFactorial_pos.2 this
    exact div_self hpos.ne'
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul, mul_one] at hE
  rw [← hE]
  have hle : ∀ σ : Fin 1 → Equiv.Perm (Fin N),
      ((∏ k, fixCount (wordPerm σ (u0 m k)) : ℕ) : ℝ) ≤ (N : ℝ) ^ s := by
    intro σ
    have : ∏ k, fixCount (wordPerm σ (u0 m k)) ≤ N ^ s := by
      have := Finset.prod_le_pow_card (s := (univ : Finset (Fin s)))
        (f := fun k => fixCount (wordPerm σ (u0 m k))) (n := N) (fun k _ => by
          unfold fixCount
          exact (card_filter_le _ _).trans (by simp))
      simpa using this
    exact_mod_cast this
  have hE2 : uniformExp (fun σ : Fin 1 → Equiv.Perm (Fin N) =>
      ((∏ k, fixCount (wordPerm σ (u0 m k)) : ℕ) : ℝ)) ≤ (N : ℝ) ^ s := by
    unfold uniformExp
    have hc : (0 : ℝ) < Fintype.card (Fin 1 → Equiv.Perm (Fin N)) := by
      exact_mod_cast Fintype.card_pos
    rw [div_le_iff₀ hc]
    calc ∑ σ, ((∏ k, fixCount (wordPerm σ (u0 m k)) : ℕ) : ℝ)
        ≤ ∑ _σ : Fin 1 → Equiv.Perm (Fin N), (N : ℝ) ^ s := sum_le_sum fun σ _ => hle σ
      _ = (N : ℝ) ^ s * Fintype.card (Fin 1 → Equiv.Perm (Fin N)) := by
        rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]
  refine hE2.trans ?_
  have hNc : (N : ℝ) = 1 + ∑ t, (m t : ℝ) := by rw [hN]; push_cast; ring
  rw [hNc]
  exact pow_le_pow_right₀ h1 (by omega)

theorem multiwalk_limit :
    ∃ F : (s : ℕ) → (Fin s → ℕ) → ℕ,
      (∀ s (m : Fin s → ℕ), (F s m : ℝ) ≤ (1 + ∑ t, (m t : ℝ)) ^ (2 * s)) ∧
      ∀ {d : ℕ} (r : List (Letter d)), r ≠ [] → (∀ l ∈ r, l ≠ none) → CycRed r →
        IsNonPower (wordFree r) → ∀ (s : ℕ) (m : Fin s → ℕ), (∀ t, 1 ≤ m t) →
          Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
              ((∏ t, fixCount (wordPerm σ (powList r (m t))) : ℕ) : ℝ)))
            atTop (𝓝 (F s m : ℝ)) := by
  classical
  refine ⟨Fm, Fm_bound, ?_⟩
  intro d r hr hnone hcyc hnp s m hm
  have hw := WH_uR hr hnone hcyc hm
  have hT : ∀ c ∈ CGM (uR r m), Tendsto (fun N : ℕ =>
      (N.descFactorial (nv c) : ℝ) / ∏ i, (N.descFactorial (EsM (uR r m) c i).card : ℝ)) atTop
      (𝓝 (if nv c = ∑ i, (EsM (uR r m) c i).card then 1 else 0)) := fun c hc =>
    N52.PartM.tendsto_term (nv c) (fun i => (EsM (uR r m) c i).card)
      (nv_le_e hw c (mem_filter.1 hc).2)
  have hsum := tendsto_finsetSum (CGM (uR r m)) hT
  rw [sum_boole, card_B hr hnone hcyc hnp hm] at hsum
  have hF : (Fm s m : ℝ) = ((CGM (u0 m)).card : ℝ) := by
    unfold Fm; rw [if_pos hm]
  rw [hF]
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (∑ k, (uR r m k).length)] with N hN
  exact (expect_eq (uR r m) N hN).symm

end Main

end Multi

end StrongConv.Q202L2.PartM

end
end
end

section
section
/-!
# HP13: Hanany–Puder Theorem 1.3 from the several-cycle limit `multiwalk_limit`

`E[∏ᵢ ξ_{i+1}(v(σ)^k)^{αᵢ}]` and `E[∏ᵢ ξ_{(i+1)k}(σ)^{αᵢ}]` are both the joint fixed-point moment of
the powers `m = ((i+1)k repeated αᵢ times)` of a cyclically reduced non-power: of a cyclic
reduction `r` of `v` (fixed-point counts are conjugation-invariant) in the first case, of the
one-letter word in `d = 1` in the second. Both tend to the same `F s m`.
-/

open Filter Topology Finset StrongConv StrongConv.Q202L2

noncomputable section

namespace StrongConv.HP13

/-- A `Mathlib` free-group letter as a CGTvH letter. -/
def toLetter {d : ℕ} (x : Fin d × Bool) : Letter d :=
  if x.2 then some (Sum.inl x.1) else some (Sum.inr x.1)

lemma wordFree_map_toLetter {d : ℕ} (L : List (Fin d × Bool)) :
    wordFree (L.map toLetter) = FreeGroup.mk L := by
  have : FreeGroup.mk L = FreeGroup.lift FreeGroup.of (FreeGroup.mk L) := by
    rw [FreeGroup.lift_of_eq_id]; rfl
  rw [this, FreeGroup.lift_mk, wordFree, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, _ | _⟩ _ <;> rfl

lemma wordPerm_powList {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (r : List (Letter d)) (m : ℕ) :
    wordPerm σ (powList r m) = (wordPerm σ r) ^ m := by
  simp [wordPerm, powList, List.map_flatten, List.prod_flatten, List.map_replicate,
    List.prod_replicate]

lemma fixCount_conj {N : ℕ} (τ π : Equiv.Perm (Fin N)) :
    fixCount (τ * π * τ⁻¹) = fixCount π := by
  unfold fixCount
  symm
  apply Finset.card_equiv τ
  intro x
  rw [Finset.mem_filter, Finset.mem_filter, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    show τ⁻¹ (τ x) = x from τ.symm_apply_apply x]
  simp only [Finset.mem_univ, true_and]
  exact τ.injective.eq_iff.symm

lemma isNonPower_conj {d : ℕ} {v : FreeGroup (Fin d)} (hv : IsNonPower v) (c : FreeGroup (Fin d)) :
    IsNonPower (c⁻¹ * v * c) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply hv.1
    have : v = c * (c⁻¹ * v * c) * c⁻¹ := by group
    rw [this, h]; group
  · intro w k hk h
    apply hv.2 (c * w * c⁻¹) k hk
    rw [conj_pow, ← h]; group

/-- A cyclic reduction of a reduced word, as a CGTvH word, is cyclically reduced. -/
lemma cycRed_map_toLetter {d : ℕ} (R : List (Fin d × Bool)) (h : FreeGroup.IsCyclicallyReduced R) :
    CycRed (R.map toLetter) := by
  have key : ∀ x y : Fin d × Bool, (x.1 = y.1 → x.2 = y.2) → toLetter y ≠ letterInv (toLetter x) := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    cases a2 <;> cases b2 <;> simp_all [toLetter, letterInv] <;> exact fun e => h e.symm
  rintro ⟨t, ht⟩
  simp only [List.length_map] at ht
  simp only [List.get_eq_getElem, List.getElem_map, List.length_map]
  by_cases h1 : t + 1 < R.length
  · simp only [Nat.mod_eq_of_lt h1]
    exact key _ _ (h.1.getElem t h1)
  · have htn : t + 1 = R.length := by omega
    simp only [htn, Nat.mod_self]
    refine key _ _ (h.2 _ ?_ _ ?_)
    · rw [List.getLast?_eq_getElem?]
      simp [show R.length - 1 = t by omega]
    · rw [List.head?_eq_getElem?]
      simp

/-- `v` is conjugate to a cyclically reduced, nonempty, `none`-free word `r`. -/
lemma exists_cycRed {d : ℕ} (v : FreeGroup (Fin d)) (hv : IsNonPower v) :
    ∃ (r : List (Letter d)) (c : FreeGroup (Fin d)), r ≠ [] ∧ (∀ l ∈ r, l ≠ none) ∧ CycRed r ∧
      IsNonPower (wordFree r) ∧ v = c * wordFree r * c⁻¹ := by
  classical
  set L := v.toWord
  set R := FreeGroup.reduceCyclically L
  set C := FreeGroup.reduceCyclically.conjugator L
  have hL : FreeGroup.mk C * FreeGroup.mk R * (FreeGroup.mk C)⁻¹ = v := by
    rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk,
      FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically, FreeGroup.mk_toWord]
  have hv' : v = FreeGroup.mk C * wordFree (R.map toLetter) * (FreeGroup.mk C)⁻¹ := by
    rw [wordFree_map_toLetter, hL]
  refine ⟨R.map toLetter, FreeGroup.mk C, ?_, ?_, ?_, ?_, hv'⟩
  · intro h
    rw [List.map_eq_nil_iff] at h
    apply hv.1
    have hR : FreeGroup.mk R = 1 := by rw [h]; rfl
    rw [← hL, hR]; group
  · intro l hl
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hl
    unfold toLetter; split <;> simp
  · exact cycRed_map_toLetter R (FreeGroup.reduceCyclically.isCyclicallyReduced
      FreeGroup.isReduced_toWord)
  · have : wordFree (R.map toLetter) = (FreeGroup.mk C)⁻¹ * v * FreeGroup.mk C := by
      rw [hv']; group
    rw [this]; exact isNonPower_conj hv _

lemma isNonPower_of_one : IsNonPower (FreeGroup.of (0 : Fin 1)) := by
  let f : FreeGroup (Fin 1) →* Multiplicative ℤ := FreeGroup.lift fun _ => Multiplicative.ofAdd 1
  have hf : f (FreeGroup.of 0) = Multiplicative.ofAdd 1 := by simp [f]
  refine ⟨?_, ?_⟩
  · intro h
    have : f (FreeGroup.of 0) = f 1 := by rw [h]
    rw [hf, f.map_one] at this
    exact absurd (congrArg Multiplicative.toAdd this) (by decide)
  · intro w k hk h
    have := congrArg (fun x => Multiplicative.toAdd (f x)) h
    simp only [hf, map_pow, toAdd_pow, toAdd_ofAdd] at this
    have hk' : (k : ℤ) ∣ 1 := ⟨_, this⟩
    have := Int.eq_one_of_dvd_one (by positivity) hk'
    omega

lemma cycRed_single : CycRed ([some (Sum.inl 0)] : List (Letter 1)) := by
  unfold CycRed; decide

lemma uniformExp_equiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (f : Y → ℝ) :
    uniformExp (fun x => f (e x)) = uniformExp f := by
  unfold uniformExp
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

lemma prod_flatten {r : ℕ} (α : Fin r → ℕ) (g : Fin r → ℝ) :
    ∏ t : Fin (∑ i, α i), g (finSigmaFinEquiv.symm t).1 = ∏ i, g i ^ α i := by
  rw [← Fintype.prod_equiv finSigmaFinEquiv (fun p => g p.1) _ (fun p => by simp)]
  rw [Fintype.prod_sigma]
  simp

lemma lift_wordFree {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    FreeGroup.lift σ (wordFree w) = wordPerm σ w := by
  rw [wordFree, map_list_prod, List.map_map, wordPerm]
  congr 1
  apply List.map_congr_left
  rintro (_ | _ | _) _ <;> simp [letterPerm]

lemma xi_eq_fixCount {N : ℕ} (j : ℕ) (π : Equiv.Perm (Fin N)) : xi j π = fixCount (π ^ j) := rfl

lemma xi_lift_eq {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) {v c : FreeGroup (Fin d)}
    {w : List (Letter d)} (hvc : v = c * wordFree w * c⁻¹) (j k : ℕ) :
    xi j (FreeGroup.lift σ (v ^ k)) = fixCount (wordPerm σ (powList w (j * k))) := by
  rw [xi_eq_fixCount, ← map_pow, ← pow_mul, hvc, conj_pow, map_mul, map_mul, map_inv,
    fixCount_conj, map_pow, lift_wordFree, wordPerm_powList, mul_comm]

lemma wordPerm_single {N : ℕ} (σ : Fin 1 → Equiv.Perm (Fin N)) (j : ℕ) :
    wordPerm σ (powList ([some (Sum.inl 0)] : List (Letter 1)) j) = σ 0 ^ j := by
  rw [wordPerm_powList]; simp [wordPerm, letterPerm]

theorem main {d r : ℕ} (v : FreeGroup (Fin d))
    (hv : IsNonPower v) (k : ℕ) (hk : 1 ≤ k) (α : Fin r → ℕ) :
    Tendsto (fun N : ℕ =>
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
            ∏ i : Fin r, ((xi ((i : ℕ) + 1) (FreeGroup.lift σ (v ^ k)) : ℕ) : ℝ) ^ α i) -
          uniformExp (fun σ : Equiv.Perm (Fin N) =>
            ∏ i : Fin r, ((xi (((i : ℕ) + 1) * k) σ : ℕ) : ℝ) ^ α i))
      atTop (𝓝 0) := by
  classical
  obtain ⟨F, -, hF⟩ := PartM.multiwalk_limit
  obtain ⟨w, c, hw0, hwn, hwc, hwp, hvc⟩ := exists_cycRed v hv
  let m : Fin (∑ i, α i) → ℕ := fun t => ((finSigmaFinEquiv.symm t).1 + 1) * k
  have hm : ∀ t, 1 ≤ m t := fun t => Nat.one_le_iff_ne_zero.2 (by positivity)
  have h1 := hF w hw0 hwn hwc hwp _ m hm
  have h2 := hF ([some (Sum.inl 0)] : List (Letter 1)) (by simp) (by simp) cycRed_single
    (by simpa [wordFree] using isNonPower_of_one) _ m hm
  have e1 : ∀ N, uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      ((∏ t, fixCount (wordPerm σ (powList w (m t))) : ℕ) : ℝ)) =
      uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ∏ i : Fin r, ((xi ((i : ℕ) + 1) (FreeGroup.lift σ (v ^ k)) : ℕ) : ℝ) ^ α i) := by
    intro N
    congr 1; funext σ
    rw [Nat.cast_prod,
      ← prod_flatten α (fun i => ((xi ((i : ℕ) + 1) (FreeGroup.lift σ (v ^ k)) : ℕ) : ℝ))]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [xi_lift_eq σ hvc]
  have e2 : ∀ N, uniformExp (fun σ : Fin 1 → Equiv.Perm (Fin N) =>
      ((∏ t, fixCount (wordPerm σ (powList [some (Sum.inl 0)] (m t))) : ℕ) : ℝ)) =
      uniformExp (fun σ : Equiv.Perm (Fin N) =>
        ∏ i : Fin r, ((xi (((i : ℕ) + 1) * k) σ : ℕ) : ℝ) ^ α i) := by
    intro N
    rw [← uniformExp_equiv (Equiv.funUnique (Fin 1) (Equiv.Perm (Fin N))).symm]
    congr 1; funext σ
    rw [Nat.cast_prod,
      ← prod_flatten α (fun i => ((xi (((i : ℕ) + 1) * k) σ : ℕ) : ℝ))]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [wordPerm_single]
    rfl
  have := (h1.sub h2)
  rw [sub_self] at this
  refine this.congr fun N => ?_
  rw [e1, e2]

end StrongConv.HP13

namespace HananyPuder

alias tendsto_uniformExp_prod_xi_pow_sub_uniformExp_dev := StrongConv.HP13.main

end HananyPuder

end
end
end

section
open HananyPuder

open Filter Topology StrongConv


theorem solution {d r : ℕ} (v : FreeGroup (Fin d))
    (hv : IsNonPower v) (k : ℕ) (hk : 1 ≤ k) (α : Fin r → ℕ) :
    Tendsto (fun N : ℕ =>
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
            ∏ i : Fin r, ((xi ((i : ℕ) + 1) (FreeGroup.lift σ (v ^ k)) : ℕ) : ℝ) ^ α i) -
          uniformExp (fun σ : Equiv.Perm (Fin N) =>
            ∏ i : Fin r, ((xi (((i : ℕ) + 1) * k) σ : ℕ) : ℝ) ^ α i))
      atTop (𝓝 0) := by
  exact HananyPuder.tendsto_uniformExp_prod_xi_pow_sub_uniformExp_dev v hv k hk α

end
