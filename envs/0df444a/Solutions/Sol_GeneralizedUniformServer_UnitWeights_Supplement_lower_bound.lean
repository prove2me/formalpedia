-- Prove2me | solution 1 for GeneralizedUniformServer.UnitWeights.Supplement.lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:22:51.6078+00:00
-- url     : https://prove2.me/submissions/8e1b40bf-906d-46ed-8397-27394fe26460

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_Online

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
/-!
# Blueprint for `GeneralizedUniformServer.UnitWeights.Supplement.lower_bound` (Theorem 1.2)

Paper §4. `X = [k]^k` is `Cfg k`; configurations are `Fin k → Fin k`, servers and points 0-based.
Constants: `ε = 1/10`, `α = 9/10`, `δ = 1/25`, `η = 2/25`, `β = 77/100`, `h = ⌊α ln k⌋`.

Two halves joined by `GoodSet`:
* the random permutation CSP (§4.1–4.3): `exists_good` (CB) from the exact counts
  `sum_Z`, `card_acc`, `sum_Zd`, `lx_G2`, `lx_G3` (CA), then `goodSet_of_good` (CC);
* the adversary (§4.4–4.6) against any serving `GenOnlineAlg`: `cost_split`, `law_sum`,
  `law_serves` (A1), `confine`, `opt_append`, `opt_nil` (A2), `one_phase` (A3), and the
  theorem `lower_main` (A4).
-/
/-- Configurations of `k` servers on `k` copies of `[k]`. -/
abbrev Cfg (k : ℕ) := Config (fun _ : Fin k => Fin k)

end GeneralizedUniformServer.Dev.LB
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
/-! ## The CSP side -/
/-- A family `π = (π_1, …, π_k)` of bijections of `[k]`. -/
abbrev Fam (k : ℕ) := Fin k → Equiv.Perm (Fin k)

/-- A system `F = (π^1, …, π^h)`. -/
abbrev Sys (k h : ℕ) := Fin h → Fam k

/-- `π(x) = (π_1(x_1), …, π_k(x_k))`. -/
def app (π : Fam k) (x : Cfg k) : Cfg k := fun i => π i (x i)

/-- `x` is a permutation. -/
def IsPerm (x : Cfg k) : Prop := Function.Injective x

open Classical in
/-- `Q(F)`: the permutations accepted by every family of `F`. -/
def Qset {h : ℕ} (F : Sys k h) : Finset (Cfg k) :=
  univ.filter fun x => IsPerm x ∧ ∀ j, IsPerm (app (F j) x)

/-- `Z(F) = |Q(F)|`. -/
def Z {h : ℕ} (F : Sys k h) : ℕ := (Qset F).card

open Classical in
/-- Hamming distance (equal to `UnitWeights.dist`). -/
def hd (x y : Cfg k) : ℕ := (univ.filter fun i => x i ≠ y i).card

open Classical in
/-- `Z_d(F)`: ordered pairs of `Q(F)` at distance `d`. -/
def Zd {h : ℕ} (F : Sys k h) (d : ℕ) : ℕ :=
  ((Qset F ×ˢ Qset F).filter fun p => hd p.1 p.2 = d).card

open Classical in
/-- Definition 4.6: `L_x(I)`. -/
def Lx {h : ℕ} (F : Sys k h) (x : Cfg k) (I : Finset (Fin k)) : Finset (Fin k × Fin k) :=
  (I ×ˢ univ).filter fun ib =>
    ib.2 ∈ I.image x ∧ ib.2 ≠ x ib.1 ∧ ∀ j, F j ib.1 ib.2 ∈ I.image (app (F j) x)

/-- `h = ⌊α ln k⌋`. -/
def hh (k : ℕ) : ℕ := ⌊(9 / 10 : ℝ) * Real.log k⌋₊

/-- `s_d = C(k,d) D_d (D_d/(k-1)^d)^h`. -/
def sd (k h d : ℕ) : ℝ :=
  (k.choose d : ℝ) * numDerangements d * ((numDerangements d : ℝ) / ((k : ℝ) - 1) ^ d) ^ h

/-- The system is good: (G1), (G2), (G3). -/
def Good {h : ℕ} (F : Sys k h) : Prop :=
  (∀ x ∈ Qset F, ∀ y ∈ Qset F,
      ¬ ((1 / 25 : ℝ) * k ≤ hd x y ∧ (hd x y : ℝ) ≤ (77 / 100 : ℝ) * k)) ∧
  (∀ x ∈ Qset F, ∀ I : Finset (Fin k),
      ¬ ((2 / 25 : ℝ) * k ≤ I.card ∧ (I.card : ℝ) < (2 / 25 + 1 / 25 : ℝ) * k ∧
          ∀ i ∈ I, ∃ b, (i, b) ∈ Lx F x I)) ∧
  (∀ x ∈ Qset F, ∀ I : Finset (Fin k),
      ¬ ((I.card : ℝ) < (2 / 25 : ℝ) * k ∧ k ≤ (Lx F x I).card))

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
open scoped Nat
variable {k : ℕ}
/-!
# Part CB: existence of a good system (Lemmas 4.2, 4.5, 4.9, 4.10)

Counting form over `Sys k h` (`ΣZ = ∑_F Z F`):
* Paley–Zygmund: with `T = {F : E/2 ≤ Z F}` (`E = k! p^h`, `ΣZ = |Sys| E`),
  `(ΣZ/2)² ≤ |T| ∑_F Z² = |T| S2 ΣZ` (`Z² = ∑_d Z_d`, `sum_Zd`).
* Bad systems lie in `U1 ∪ U2 ∪ U3` (union bounds over `d`, `(x, I)`, `(x, I, P)`), with
  `|U| ≤ ΣZ (W1 + W2 + W3)` by `sum_Zd`, `lx_G2`, `lx_G3` and `∑_x #{F : x ∈ Q F} = ΣZ`.
* `4 S2 (W1 + W2 + W3) < 1` (`PartCB_Analysis`) gives `|U| < |T|`.
The real estimates are in `PartCB_Analysis.lean`.
-/
lemma perm_of_mem {h : ℕ} {F : Sys k h} {x : Cfg k} (hx : x ∈ Qset F) : IsPerm x := by
  classical
  unfold Qset at hx; rw [Finset.mem_filter] at hx; exact hx.2.1

open Classical in
lemma hd_le (x y : Cfg k) : hd x y ≤ k := by
  unfold hd
  exact (card_filter_le _ _).trans (by simp)

open Classical in
/-- `∑_x #{F : x ∈ Q(F)} = ∑_F Z(F)`. -/
lemma sum_acc (h : ℕ) :
    (∑ x : Cfg k, ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ)) =
      ∑ F : Sys k h, (Z F : ℝ) := by
  have e1 : ∀ x : Cfg k, ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) =
      ∑ F : Sys k h, if x ∈ Qset F then (1 : ℝ) else 0 := by
    intro x; rw [Finset.sum_boole]
  simp_rw [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [Finset.sum_boole]; unfold Z; congr 2; ext x; simp

open Classical in
lemma Z_sq {h : ℕ} (F : Sys k h) :
    (Z F : ℝ) ^ 2 = ∑ d ∈ range (k + 1), (Zd F d : ℝ) := by
  have e := Finset.card_eq_sum_card_fiberwise (s := Qset F ×ˢ Qset F) (t := range (k + 1))
    (f := fun p : Cfg k × Cfg k => hd p.1 p.2)
    (fun p _ => mem_range.2 (Nat.lt_succ_of_le (hd_le p.1 p.2)))
  rw [card_product] at e
  unfold Z Zd
  rw [sq]; exact_mod_cast e

end GeneralizedUniformServer.Dev.LB.PartCB
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
/-- The output of §4.1–4.3 used by the adversary: setup requests `R0` cutting out a set `Q`
of permutations, split into components that are far apart, small and rigid. -/
structure GoodSet (k : ℕ) where
  R0 : List (Cfg k)
  Q : Finset (Cfg k)
  serves_iff : ∀ x, (∀ r ∈ R0, Serves x r) ↔ x ∈ Q
  perm : ∀ x ∈ Q, IsPerm x
  card : Real.exp ((k : ℝ) * Real.log k / 10 - k) / 2 ≤ (Q.card : ℝ)
  comp : Cfg k → Finset (Cfg k)
  comp_self : ∀ x ∈ Q, x ∈ comp x
  comp_sub : ∀ x ∈ Q, comp x ⊆ Q
  comp_eq : ∀ x ∈ Q, ∀ y ∈ comp x, comp y = comp x
  far : ∀ x ∈ Q, ∀ y ∈ Q, y ∉ comp x → (77 / 100 : ℝ) * k < hd x y
  small : ∀ x ∈ Q, (comp x).card < 2 ^ k
  rigid : ∀ x ∈ Q,
    (((univ.filter fun i => ∃ y ∈ comp x, y i ≠ x i).card : ℕ) : ℝ) < (2 / 25 : ℝ) * k

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCC
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}
/-!
# Part CC: components of a good system (Lemmas 4.1, 4.7, 4.11)

* `R0`: the setup requests `(a, …, a)` and `r_{j,a}` (Lemma 4.1, `serves_R0_iff`).
* `comp F x`: the configurations of `Q(F)` reachable from `x` along edges joining
  configurations of `Q(F)` at distance `< δk` (`Relation.ReflTransGen`).
* Lemma 4.7 (`mem_Lx_of_agree`), Lemma 4.11: `rigid_comp` (a maximal subset of the component
  containing `x` with `|I| < ηk` must be the whole component, using (G2)), `small_comp` ((G3)).
-/
lemma mem_Qset {h : ℕ} {F : Sys k h} {x : Cfg k} :
    x ∈ Qset F ↔ IsPerm x ∧ ∀ j, IsPerm (app (F j) x) := by
  classical
  unfold Qset; simp

/-! ## Lemma 4.1 -/
/-- The setup requests of `F`. -/
def R0 {h : ℕ} (F : Sys k h) : List (Cfg k) :=
  ((univ.image fun a : Fin k => (fun _ : Fin k => a)) ∪
    (univ.image fun ja : Fin h × Fin k => fun i => (F ja.1 i).symm ja.2)).toList

lemma perm_iff_surj (x : Cfg k) : IsPerm x ↔ ∀ a, ∃ i, x i = a := by
  unfold IsPerm
  rw [Finite.injective_iff_surjective]
  rfl

lemma serves_R0_iff {h : ℕ} (F : Sys k h) (x : Cfg k) :
    (∀ r ∈ R0 F, Serves x r) ↔ x ∈ Qset F := by
  rw [mem_Qset, perm_iff_surj]
  simp only [perm_iff_surj, app]
  unfold R0
  simp only [mem_toList, mem_union, mem_image, mem_univ, true_and]
  constructor
  · intro H
    refine ⟨fun a => ?_, fun j a => ?_⟩
    · exact H _ (Or.inl ⟨a, rfl⟩)
    · obtain ⟨i, hi⟩ := H _ (Or.inr ⟨(j, a), rfl⟩)
      exact ⟨i, by rw [hi]; simp⟩
  · rintro ⟨H1, H2⟩ r (⟨a, rfl⟩ | ⟨⟨j, a⟩, rfl⟩)
    · exact H1 a
    · obtain ⟨i, hi⟩ := H2 j a
      exact ⟨i, by simp [← hi]⟩

/-! ## Lemma 4.7 -/
lemma mem_image_of_agree {u v : Cfg k} (hu : IsPerm u) (hv : IsPerm v) {I : Finset (Fin k)}
    (hag : ∀ l, l ∉ I → v l = u l) {i : Fin k} (hi : i ∈ I) : v i ∈ I.image u := by
  obtain ⟨l, hl⟩ := (perm_iff_surj u).1 hu (v i)
  by_cases hlI : l ∈ I
  · exact mem_image.2 ⟨l, hlI, hl⟩
  · have : v l = v i := by rw [hag l hlI, hl]
    have := hv this
    subst this
    exact absurd hi hlI

lemma mem_Lx_of_agree {h : ℕ} {F : Sys k h} {x y : Cfg k} (hx : x ∈ Qset F) (hy : y ∈ Qset F)
    {I : Finset (Fin k)} (hag : ∀ l, l ∉ I → y l = x l) {i : Fin k} (hi : i ∈ I)
    (hne : y i ≠ x i) : (i, y i) ∈ Lx F x I := by
  classical
  rw [mem_Qset] at hx hy
  unfold Lx
  rw [mem_filter]
  refine ⟨by simp [hi], mem_image_of_agree hx.1 hy.1 hag hi, hne, fun j => ?_⟩
  have := mem_image_of_agree (hx.2 j) (hy.2 j) (I := I) (fun l hl => by
    simp only [app]; rw [hag l hl]) hi
  simpa [app] using this

/-! ## Components -/
/-- Edges of the component graph. -/
def Adj {h : ℕ} (F : Sys k h) (x y : Cfg k) : Prop :=
  x ∈ Qset F ∧ y ∈ Qset F ∧ (hd x y : ℝ) < (1 / 25 : ℝ) * k

open Classical in
/-- The component of `x`. -/
def comp {h : ℕ} (F : Sys k h) (x : Cfg k) : Finset (Cfg k) :=
  (Qset F).filter fun y => Relation.ReflTransGen (Adj F) x y

lemma hd_comm (x y : Cfg k) : hd x y = hd y x := by
  classical
  unfold hd
  congr 1
  ext i
  simp [ne_comm]

lemma adj_symm {h : ℕ} (F : Sys k h) {x y : Cfg k} (hxy : Adj F x y) : Adj F y x := by
  obtain ⟨hx, hy, hd⟩ := hxy
  exact ⟨hy, hx, by rwa [hd_comm]⟩

lemma rtg_symm {h : ℕ} (F : Sys k h) {x y : Cfg k} (hxy : Relation.ReflTransGen (Adj F) x y) :
    Relation.ReflTransGen (Adj F) y x := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (adj_symm F hbc)).trans ih

lemma mem_comp {h : ℕ} {F : Sys k h} {x y : Cfg k} :
    y ∈ comp F x ↔ y ∈ Qset F ∧ Relation.ReflTransGen (Adj F) x y := by
  classical
  unfold comp; simp

lemma exists_exit {α : Type*} {r : α → α → Prop} {M : Finset α} {x z : α} (hx : x ∈ M)
    (hz : z ∉ M) (hr : Relation.ReflTransGen r x z) :
    ∃ m ∈ M, ∃ y, y ∉ M ∧ r m y ∧ Relation.ReflTransGen r x y := by
  induction hr with
  | refl => exact absurd hx hz
  | @tail b c hab hbc ih =>
    by_cases hb : b ∈ M
    · exact ⟨b, hb, c, hz, hbc, hab.tail hbc⟩
    · exact ih hb

/-- The coordinates in which `S` varies from `x`. -/
def Ivar (x : Cfg k) (S : Finset (Cfg k)) : Finset (Fin k) :=
  univ.filter fun i => ∃ y ∈ S, y i ≠ x i

lemma Ivar_mono (x : Cfg k) {S T : Finset (Cfg k)} (h : S ⊆ T) : Ivar x S ⊆ Ivar x T := by
  intro i; simp only [Ivar, mem_filter, mem_univ, true_and]
  rintro ⟨y, hy, hne⟩; exact ⟨y, h hy, hne⟩

lemma agree_of_Ivar {x y : Cfg k} {S : Finset (Cfg k)} (hy : y ∈ S) :
    ∀ l, l ∉ Ivar x S → y l = x l := by
  intro l hl
  by_contra hne
  exact hl (by simp only [Ivar, mem_filter, mem_univ, true_and]; exact ⟨y, hy, hne⟩)

lemma card_Ivar_insert (x m y : Cfg k) (S : Finset (Cfg k)) (hm : m ∈ S) :
    (Ivar x (insert y S)).card ≤ (Ivar x S).card + hd m y := by
  classical
  have hsub : Ivar x (insert y S) ⊆ Ivar x S ∪ univ.filter fun i => m i ≠ y i := by
    intro i
    simp only [Ivar, mem_filter, mem_univ, true_and, mem_union, mem_insert]
    rintro ⟨w, hw | hw, hne⟩
    · subst hw
      by_cases hmi : m i = x i
      · right; rw [hmi]; exact Ne.symm hne
      · left; exact ⟨m, hm, hmi⟩
    · left; exact ⟨w, hw, hne⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (le_of_eq ?_))
  unfold hd
  congr 2

/-! ## Lemma 4.11 -/
lemma rigid_comp (hk : 2 ≤ k) {h : ℕ} {F : Sys k h} (hG : Good F) {x : Cfg k}
    (hx : x ∈ Qset F) :
    ((Ivar x (comp F x)).card : ℝ) < (2 / 25 : ℝ) * k := by
  classical
  set C := comp F x with hCdef
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hxC : x ∈ C := mem_comp.2 ⟨hx, Relation.ReflTransGen.refl⟩
  set fam := C.powerset.filter
    (fun S => x ∈ S ∧ ((Ivar x S).card : ℝ) < (2 / 25 : ℝ) * k) with hfam
  have hsing : ({x} : Finset (Cfg k)) ∈ fam := by
    rw [hfam, mem_filter, mem_powerset]
    refine ⟨singleton_subset_iff.2 hxC, mem_singleton_self x, ?_⟩
    have : Ivar x {x} = ∅ := by
      ext i; simp [Ivar]
    rw [this]; simp; linarith
  obtain ⟨M, hMf, hMmax⟩ := exists_max_image fam card ⟨_, hsing⟩
  rw [hfam, mem_filter, mem_powerset] at hMf
  obtain ⟨hMC, hxM, hMI⟩ := hMf
  have hCM : C ⊆ M := by
    intro z hz
    by_contra hzM
    obtain ⟨m, hm, y, hyM, hadj, hreach⟩ := exists_exit hxM hzM (mem_comp.1 hz).2
    have hyC : y ∈ C := mem_comp.2 ⟨hadj.2.1, hreach⟩
    have hM'C : insert y M ⊆ C := insert_subset hyC hMC
    have hcard := card_Ivar_insert x m y M hm
    have hcardR : ((Ivar x (insert y M)).card : ℝ) < (2 / 25 + 1 / 25 : ℝ) * k := by
      have : ((Ivar x (insert y M)).card : ℝ) ≤ (Ivar x M).card + hd m y := by
        exact_mod_cast hcard
      linarith [hadj.2.2]
    by_cases hlt : ((Ivar x (insert y M)).card : ℝ) < (2 / 25 : ℝ) * k
    · have hmem : insert y M ∈ fam := by
        rw [hfam, mem_filter, mem_powerset]
        exact ⟨hM'C, mem_insert_of_mem hxM, hlt⟩
      have := hMmax _ hmem
      rw [card_insert_of_notMem hyM] at this
      omega
    · apply hG.2.1 x hx (Ivar x (insert y M))
      refine ⟨le_of_not_gt hlt, hcardR, fun i hi => ?_⟩
      have hi' := hi
      simp only [Ivar, mem_filter, mem_univ, true_and] at hi'
      obtain ⟨w, hw, hne⟩ := hi'
      exact ⟨w i, mem_Lx_of_agree hx (mem_comp.1 (hM'C hw)).1 (agree_of_Ivar hw) hi hne⟩
  exact lt_of_le_of_lt (by exact_mod_cast card_le_card (Ivar_mono x hCM)) hMI

lemma small_comp (hk : 2 ≤ k) {h : ℕ} {F : Sys k h} (hG : Good F) {x : Cfg k}
    (hx : x ∈ Qset F) : (comp F x).card < 2 ^ k := by
  classical
  set C := comp F x with hCdef
  have hxC : x ∈ C := mem_comp.2 ⟨hx, Relation.ReflTransGen.refl⟩
  set A : Fin k → Finset (Fin k) := fun i => C.image fun y => y i with hA
  have hxA : ∀ i, x i ∈ A i := fun i => mem_image.2 ⟨x, hxC, rfl⟩
  have h1 : C.card ≤ ∏ i, (A i).card := by
    rw [← Fintype.card_piFinset]
    apply card_le_card
    intro y hy
    rw [Fintype.mem_piFinset]
    intro i; exact mem_image.2 ⟨y, hy, rfl⟩
  have h2 : ∏ i, (A i).card ≤ 2 ^ (∑ i, ((A i).erase (x i)).card) := by
    rw [← prod_pow_eq_pow_sum]
    apply prod_le_prod'
    intro i _
    rw [← card_erase_add_one (hxA i)]
    exact Nat.lt_two_pow_self
  set P := (univ : Finset (Fin k)).sigma fun i => (A i).erase (x i) with hP
  have h3 : ∑ i, ((A i).erase (x i)).card = P.card := by
    rw [hP, card_sigma]
  have h4 : P.card ≤ (Lx F x (Ivar x C)).card := by
    apply card_le_card_of_injOn (fun p => (p.1, p.2))
    · rintro ⟨i, b⟩ hp
      simp only [hP, coe_sigma, Set.mem_sigma_iff, coe_univ, Set.mem_univ, true_and,
        mem_coe, mem_erase, hA, mem_image] at hp
      obtain ⟨hbx, y, hy, rfl⟩ := hp
      have hiI : i ∈ Ivar x C := by
        simp only [Ivar, mem_filter, mem_univ, true_and]; exact ⟨y, hy, hbx⟩
      exact mem_Lx_of_agree hx (mem_comp.1 hy).1 (agree_of_Ivar hy) hiI hbx
    · rintro ⟨a1, a2⟩ _ ⟨b1, b2⟩ _ hab
      simp only [Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      rfl
  have h5 : (Lx F x (Ivar x C)).card < k := by
    by_contra hge
    exact hG.2.2 x hx (Ivar x C) ⟨rigid_comp hk hG hx, le_of_not_gt hge⟩
  calc C.card ≤ 2 ^ (∑ i, ((A i).erase (x i)).card) := h1.trans h2
    _ < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- **CC** (Lemmas 4.1, 4.7, 4.11). -/
theorem goodSet_of_good (hk : 2 ≤ k) {h : ℕ} (F : Sys k h) (hG : Good F)
    (hZ : Real.exp ((k : ℝ) * Real.log k / 10 - k) / 2 ≤ (Z F : ℝ)) : Nonempty (GoodSet k) := by
  refine ⟨{
    R0 := R0 F
    Q := Qset F
    serves_iff := serves_R0_iff F
    perm := fun x hx => (mem_Qset.1 hx).1
    card := hZ
    comp := comp F
    comp_self := fun x hx => mem_comp.2 ⟨hx, Relation.ReflTransGen.refl⟩
    comp_sub := fun x _ y hy => (mem_comp.1 hy).1
    comp_eq := ?_
    far := ?_
    small := fun x hx => small_comp hk hG hx
    rigid := fun x hx => rigid_comp hk hG hx }⟩
  · intro x hx y hy
    have hxy := (mem_comp.1 hy).2
    have hyx : Relation.ReflTransGen (Adj F) y x := rtg_symm F hxy
    ext z
    rw [mem_comp, mem_comp]
    constructor
    · rintro ⟨hz, hr⟩; exact ⟨hz, hxy.trans hr⟩
    · rintro ⟨hz, hr⟩; exact ⟨hz, hyx.trans hr⟩
  · intro x hx y hy hyc
    have hnadj : ¬ Adj F x y := fun ha =>
      hyc (mem_comp.2 ⟨hy, Relation.ReflTransGen.single ha⟩)
    have hge : (1 / 25 : ℝ) * k ≤ hd x y := by
      by_contra hlt
      exact hnadj ⟨hx, hy, lt_of_not_ge hlt⟩
    by_contra hle
    exact hG.1 x hx y hy ⟨hge, le_of_not_gt hle⟩

end GeneralizedUniformServer.Dev.LB.PartCC
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias goodSet_of_good := GeneralizedUniformServer.Dev.LB.PartCC.goodSet_of_good

/-! ## The adversary side -/
/-- `E[ALG(ρ)]` as a real number. -/
def ecost (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k)) (a : Cfg k) (ρ : List (Cfg k)) : ℝ :=
  (genExpectedCost A a ρ).toReal

/-- `μ_ρ(y)`: the probability that `ALG` is at `y` after serving `ρ`. -/
def law (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k)) (a : Cfg k) (ρ : List (Cfg k))
    (y : Cfg k) : ℝ :=
  (((genTrajLaw A a ρ ρ.length).map fun p => p.headD a) y).toReal

/-- The competitive guarantee. -/
def Compet (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k)) (a : Cfg k) (γ c : ℝ) : Prop :=
  ∀ ρ : List (Cfg k), ecost A a ρ ≤ γ * (optCost a ρ : ℝ) + c

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA1
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
/-!
# Part A1: the laws of the algorithm (paper pp. 8, 15)

* `law_sum`: `law A a ρ` is (the real part of) a PMF on the finite type `Cfg k`.
* `law_serves`: the last step draws from `A … r`, whose support serves `r`.
* `cost_split`: `genTrajLaw` is online, and the trajectory at time `|ρ| + n` drops (by `n`
  entries) to the trajectory at time `|ρ|`; the path cost of the full trajectory is at least the
  cost of its first `|ρ|` steps plus the distance between the two heads (triangle inequality).
  `J` is the joint law of the two heads.
-/
/-! ## Expectations under a PMF -/
/-- Expectation of `g` under a PMF, in `ℝ≥0∞`. -/
def E {α : Type*} (μ : PMF α) (g : α → ENNReal) : ENNReal := ∑' p, μ p * g p

lemma E_bind {α β : Type*} (μ : PMF α) (f : α → PMF β) (g : β → ENNReal) :
    E (μ.bind f) g = E μ (fun a => E (f a) g) := by
  unfold E
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1
  ext a
  simp_rw [← ENNReal.tsum_mul_left, mul_assoc]

lemma E_pure {α : Type*} (b : α) (g : α → ENNReal) : E (PMF.pure b) g = g b := by
  simp [E, PMF.pure_apply]

lemma E_map {α β : Type*} (h : α → β) (μ : PMF α) (g : β → ENNReal) :
    E (μ.map h) g = E μ (fun a => g (h a)) := by
  have : μ.map h = μ.bind (PMF.pure ∘ h) := rfl
  rw [this, E_bind]
  simp [E_pure]

lemma E_add {α : Type*} (μ : PMF α) (f g : α → ENNReal) :
    E μ (fun a => f a + g a) = E μ f + E μ g := by
  simp [E, mul_add, ENNReal.tsum_add]

lemma E_const {α : Type*} (μ : PMF α) (c : ENNReal) : E μ (fun _ => c) = c := by
  unfold E
  rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

lemma E_mono_supp {α : Type*} (μ : PMF α) {f g : α → ENNReal}
    (h : ∀ a ∈ μ.support, f a ≤ g a) : E μ f ≤ E μ g := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ μ.support
  · gcongr; exact h a ha
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

end GeneralizedUniformServer.Dev.LB.PartA1
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA1
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}
/-! ## Basic facts on `genTrajLaw` -/
abbrev Alg (k : ℕ) := GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k)

lemma traj_succ (A : Alg k) (a : Cfg k) (σ : List (Cfg k)) (t : ℕ) (ht : t < σ.length) :
    genTrajLaw A a σ (t + 1) =
      (genTrajLaw A a σ t).bind fun p => (A (σ.take t) p σ[t]).map fun y => y :: p := by
  rw [genTrajLaw]
  congr 1
  funext p
  rw [dif_pos ht]

/-- Online: the trajectory up to time `t ≤ |ρ|` does not see `ρ'`. -/
lemma traj_append (A : Alg k) (a : Cfg k) (ρ ρ' : List (Cfg k)) (t : ℕ) (ht : t ≤ ρ.length) :
    genTrajLaw A a (ρ ++ ρ') t = genTrajLaw A a ρ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ht' : t < ρ.length := ht
    rw [traj_succ A a (ρ ++ ρ') t (by simp; omega), traj_succ A a ρ t ht', ih ht'.le]
    congr 1
    funext p
    rw [List.take_append_of_le_length ht'.le, List.getElem_append_left ht']

/-- Dropping the newest entry of the trajectory at time `t + 1` gives the trajectory at `t`. -/
lemma traj_tail (A : Alg k) (a : Cfg k) (σ : List (Cfg k)) (t : ℕ) (ht : t < σ.length) :
    (genTrajLaw A a σ (t + 1)).map List.tail = genTrajLaw A a σ t := by
  rw [traj_succ A a σ t ht, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure (genTrajLaw A a σ t)]
  congr 1
  funext p
  rw [PMF.map_comp]
  have : (List.tail ∘ fun y : Cfg k => y :: p) = Function.const _ p := by
    funext y; rfl
  rw [this, PMF.map_const]

lemma traj_drop (A : Alg k) (a : Cfg k) (σ : List (Cfg k)) (t n : ℕ) (h : t + n ≤ σ.length) :
    (genTrajLaw A a σ (t + n)).map (List.drop n) = genTrajLaw A a σ t := by
  induction n with
  | zero =>
    have : (List.drop 0 : List (Cfg k) → List (Cfg k)) = id := by funext p; simp
    rw [this, PMF.map_id]; rfl
  | succ n ih =>
    have e : (List.drop (n + 1) : List (Cfg k) → List (Cfg k)) = List.drop n ∘ List.tail := by
      funext p; simp
    rw [e, ← PMF.map_comp, ← Nat.add_assoc, traj_tail A a σ (t + n) (by omega), ih (by omega)]

lemma traj_length (A : Alg k) (a : Cfg k) (σ : List (Cfg k)) (t : ℕ) (ht : t ≤ σ.length)
    (p : List (Cfg k)) (hp : p ∈ (genTrajLaw A a σ t).support) : p.length = t + 1 := by
  induction t generalizing p with
  | zero =>
    simp only [genTrajLaw, PMF.support_pure, Set.mem_singleton_iff] at hp
    simp [hp]
  | succ t ih =>
    rw [traj_succ A a σ t ht, PMF.mem_support_bind_iff] at hp
    obtain ⟨q, hq, hp⟩ := hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨y, -, rfl⟩ := hp
    simp [ih (by omega) q hq]

/-! ## Distances -/
lemma dist_eq (x y : Cfg k) :
    UnitWeights.dist x y = (Finset.univ.filter fun i => x i ≠ y i).card := by
  unfold UnitWeights.dist
  congr 1
  ext i
  simp

lemma hd_eq_dist (x y : Cfg k) : hd x y = UnitWeights.dist x y := by
  rw [dist_eq]
  unfold hd
  congr 1

lemma dist_self' (x : Cfg k) : UnitWeights.dist x x = 0 := by
  rw [dist_eq]
  simp

lemma dist_le_k (x y : Cfg k) : UnitWeights.dist x y ≤ k := by
  rw [dist_eq]
  calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := by simp

lemma dist_tri (x y z : Cfg k) :
    UnitWeights.dist x z ≤ UnitWeights.dist x y + UnitWeights.dist y z := by
  rw [dist_eq, dist_eq, dist_eq]
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
  by_contra h
  push Not at h
  exact hi (h.1.trans h.2)

lemma pathCost_drop (a : Cfg k) (n : ℕ) (p : List (Cfg k)) (hn : n < p.length) :
    UnitWeights.dist ((p.drop n).headD a) (p.headD a) + pathCost (p.drop n) ≤ pathCost p := by
  induction n generalizing p with
  | zero => simp [dist_self']
  | succ n ih =>
    match p, hn with
    | x :: y :: rest, hn =>
      have hn' : n < (y :: rest).length := by simp at hn ⊢; omega
      have := ih (y :: rest) hn'
      simp only [List.drop_succ_cons, List.headD_cons] at this ⊢
      rw [pathCost]
      have t := dist_tri (((y :: rest).drop n).headD a) y x
      omega
    | [x], hn => simp at hn

lemma pathCost_le (p : List (Cfg k)) : pathCost p ≤ k * p.length := by
  induction p with
  | nil => simp [pathCost]
  | cons x q ih =>
    match q, ih with
    | [], _ => simp [pathCost]
    | y :: rest, ih =>
      rw [pathCost]
      have := dist_le_k y x
      simp only [List.length_cons] at ih ⊢
      nlinarith

/-! ## The three stubs -/
theorem law_sum (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k)) (a : Cfg k)
    (ρ : List (Cfg k)) : ∑ y, law A a ρ y = 1 := by
  unfold law
  rw [← ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top _ y)]
  have h := PMF.tsum_coe ((genTrajLaw A a ρ ρ.length).map fun p => p.headD a)
  rw [tsum_fintype] at h
  rw [h]
  simp

end GeneralizedUniformServer.Dev.LB.PartA1
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias law_sum := GeneralizedUniformServer.Dev.LB.PartA1.law_sum

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA1
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}
theorem law_serves (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k))
    (hA : IsServing Serves A) (a : Cfg k) (ρ : List (Cfg k)) (r y : Cfg k)
    (hy : law A a (ρ ++ [r]) y ≠ 0) : Serves y r := by
  unfold law at hy
  have hy' : ((genTrajLaw A a (ρ ++ [r]) (ρ ++ [r]).length).map fun p => p.headD a) y ≠ 0 := by
    intro h; apply hy; rw [h]; rfl
  rw [← PMF.mem_support_iff, PMF.mem_support_map_iff] at hy'
  obtain ⟨p, hp, rfl⟩ := hy'
  have hl : (ρ ++ [r]).length = ρ.length + 1 := by simp
  rw [hl, traj_succ A a _ _ (by simp), PMF.mem_support_bind_iff] at hp
  obtain ⟨q, -, hq⟩ := hp
  rw [PMF.mem_support_map_iff] at hq
  obtain ⟨z, hz, rfl⟩ := hq
  have := hA _ _ _ _ hz
  simpa using this

end GeneralizedUniformServer.Dev.LB.PartA1
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias law_serves := GeneralizedUniformServer.Dev.LB.PartA1.law_serves

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA1
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}
lemma marg_fst (ν : PMF (Cfg k × Cfg k)) (y : Cfg k) :
    ∑ y', ν (y, y') = (ν.map Prod.fst) y := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  symm
  rw [Finset.sum_eq_single y (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

lemma marg_snd (ν : PMF (Cfg k × Cfg k)) (y' : Cfg k) :
    ∑ y, ν (y, y') = (ν.map Prod.snd) y' := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only
  rw [Finset.sum_eq_single y' (fun b _ hb => by rw [if_neg (Ne.symm hb)]) (by simp)]
  simp

theorem cost_split (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k)) (a : Cfg k)
    (ρ ρ' : List (Cfg k)) :
    ∃ J : Cfg k × Cfg k → ℝ, (∀ p, 0 ≤ J p) ∧
      (∀ y, ∑ y', J (y, y') = law A a ρ y) ∧
      (∀ y', ∑ y, J (y, y') = law A a (ρ ++ ρ') y') ∧
      ecost A a ρ + ∑ p, J p * (hd p.1 p.2 : ℝ) ≤ ecost A a (ρ ++ ρ') := by
  set n := ρ'.length
  set L := ρ.length
  set μ := genTrajLaw A a (ρ ++ ρ') (ρ ++ ρ').length with hμ
  have hlen : (ρ ++ ρ').length = L + n := by simp [L, n]
  have hdrop : μ.map (List.drop n) = genTrajLaw A a ρ L := by
    rw [hμ, hlen, traj_drop A a _ L n (by simp [L, n]), traj_append A a ρ ρ' L le_rfl]
  set f : List (Cfg k) → Cfg k × Cfg k := fun p => ((p.drop n).headD a, p.headD a) with hf
  set ν := μ.map f with hν
  refine ⟨fun q => (ν q).toReal, fun q => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · intro y
    rw [← ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _), marg_fst]
    unfold law
    rw [hν, PMF.map_comp, ← hdrop, PMF.map_comp]
    rfl
  · intro y'
    rw [← ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _), marg_snd]
    unfold law
    rw [hν, PMF.map_comp]
    rfl
  · -- the cost inequality, in `ℝ≥0∞`
    have hsupp : ∀ p ∈ μ.support, n < p.length := by
      intro p hp
      have := traj_length A a (ρ ++ ρ') _ le_rfl p hp
      rw [hlen] at this; omega
    have key : E μ (fun p => (pathCost (p.drop n) : ENNReal)) +
        E μ (fun p => (UnitWeights.dist (f p).1 (f p).2 : ENNReal)) ≤
        E μ (fun p => (pathCost p : ENNReal)) := by
      rw [← E_add]
      refine E_mono_supp μ fun p hp => ?_
      have := pathCost_drop a n p (hsupp p hp)
      simp only [hf]
      exact_mod_cast (by omega : pathCost (p.drop n) +
        UnitWeights.dist ((p.drop n).headD a) (p.headD a) ≤ pathCost p)
    have hfin : E μ (fun p => (pathCost p : ENNReal)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ((k * (L + n + 1) : ℕ) : ENNReal)) (ENNReal.natCast_ne_top _) ?_
      rw [← E_const μ ((k * (L + n + 1) : ℕ) : ENNReal)]
      refine E_mono_supp μ fun p hp => ?_
      have h1 := traj_length A a (ρ ++ ρ') _ le_rfl p hp
      rw [hlen] at h1
      have := pathCost_le p
      rw [h1] at this
      exact_mod_cast this
    have e1 : E μ (fun p => (pathCost (p.drop n) : ENNReal)) = genExpectedCost A a ρ := by
      show _ = E (genTrajLaw A a ρ L) (fun p => (pathCost p : ENNReal))
      rw [← hdrop, E_map]
    have e2 : E μ (fun p => (UnitWeights.dist (f p).1 (f p).2 : ENNReal)) =
        ∑ q, ν q * (UnitWeights.dist q.1 q.2 : ENNReal) := by
      rw [hν, ← E_map (g := fun q : Cfg k × Cfg k => (UnitWeights.dist q.1 q.2 : ENNReal))]
      unfold E
      rw [tsum_fintype]
    have e3 : E μ (fun p => (pathCost p : ENNReal)) = genExpectedCost A a (ρ ++ ρ') := rfl
    rw [e1, e2, e3] at key
    rw [e3] at hfin
    have hb : ∑ q, ν q * (UnitWeights.dist q.1 q.2 : ENNReal) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (le_trans le_add_self key)
    have ha : genExpectedCost A a ρ ≠ ⊤ := ne_top_of_le_ne_top hfin (le_trans le_self_add key)
    have := ENNReal.toReal_mono hfin key
    rw [ENNReal.toReal_add ha hb, ENNReal.toReal_sum (fun q _ => ENNReal.mul_ne_top
      (PMF.apply_ne_top _ _) (by simp))] at this
    unfold ecost
    convert this using 3 with q
    rw [ENNReal.toReal_mul, hd_eq_dist]
    simp

end GeneralizedUniformServer.Dev.LB.PartA1
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias cost_split := GeneralizedUniformServer.Dev.LB.PartA1.cost_split

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA2
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}
/-!
# Part A2: offline facts and confinement (Lemma 4.15, paper p. 15)

* `opt_nil`: the empty solution costs `0`.
* `opt_append`: an optimal solution for `ρ` (attained: `o_t = r_t` is feasible for `k ≥ 1`),
  then a move to `q` at the first appended request (cost `≤ k`), then stay.
* `confine`: if the mass of `law` outside `Q_R` stayed `> τ` for every sequence from `R`, the
  greedy construction (append a request of `R` failed by a configuration `u` of mass
  `> τ / |Cfg k|`) raises `ecost` by `> τ / |Cfg k|` per step (`cost_split`, `law_serves`),
  while `optCost` stays `≤ optCost a ρ0 + k`; this contradicts `Compet`.
-/
lemma dist_eq' (x y : Cfg k) :
    UnitWeights.dist x y = (Finset.univ.filter fun i => x i ≠ y i).card := by
  unfold UnitWeights.dist
  congr 1
  ext i
  simp

lemma dist_self'' (x : Cfg k) : UnitWeights.dist x x = 0 := by
  rw [dist_eq']
  simp

lemma dist_le_k' (x y : Cfg k) : UnitWeights.dist x y ≤ k := by
  rw [dist_eq']
  calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := by simp

theorem opt_nil (a : Cfg k) : optCost a ([] : List (Cfg k)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  refine ⟨fun _ => a, ?_, rfl, ?_⟩
  · intro s
    exact s.elim0
  · simp [offlineCost]

end GeneralizedUniformServer.Dev.LB.PartA2
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias opt_nil := GeneralizedUniformServer.Dev.LB.PartA2.opt_nil

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA2
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}
theorem opt_append (hk : 1 ≤ k) (a : Cfg k) (ρ ρ' : List (Cfg k)) (q : Cfg k)
    (hq : ∀ r ∈ ρ', Serves q r) : optCost a (ρ ++ ρ') ≤ optCost a ρ + k := by
  set L := ρ.length with hL
  have hne : {C : ℕ | ∃ o : Fin (ρ.length + 1) → Cfg k,
      IsOfflineSolution ρ o ∧ o 0 = a ∧ offlineCost ρ o = C}.Nonempty := by
    refine ⟨_, fun t => if h : (t : ℕ) = 0 then a else ρ[(t : ℕ) - 1]'(by omega), ?_, rfl, rfl⟩
    intro s
    simp only [Fin.val_succ, Nat.add_one_ne_zero, dif_neg, not_false_eq_true,
      Nat.add_sub_cancel, Fin.getElem_fin]
    exact ⟨⟨0, hk⟩, rfl⟩
  obtain ⟨o, ho, ho0, hoc⟩ := Nat.sInf_mem hne
  let f : ℕ → Cfg k := fun t => if h : t ≤ L then o ⟨t, by omega⟩ else q
  let o' : Fin ((ρ ++ ρ').length + 1) → Cfg k := fun t => f t
  have hfeas : IsOfflineSolution (ρ ++ ρ') o' := by
    intro s
    show Serves (f ((s : ℕ) + 1)) (ρ ++ ρ')[(s : ℕ)]
    by_cases hs : (s : ℕ) < L
    · have h1 : f ((s : ℕ) + 1) = o (⟨s, hs⟩ : Fin ρ.length).succ := by
        simp only [f, dif_pos (show (s : ℕ) + 1 ≤ L by omega)]
        rfl
      rw [h1, List.getElem_append_left hs]
      exact ho ⟨s, hs⟩
    · have h1 : f ((s : ℕ) + 1) = q := by
        simp only [f, dif_neg (show ¬ ((s : ℕ) + 1 ≤ L) by omega)]
      rw [h1, List.getElem_append_right (by omega)]
      exact hq _ (List.getElem_mem _)
  have h0 : o' 0 = a := by
    show f 0 = a
    simp only [f, dif_pos (Nat.zero_le L)]
    exact ho0
  have c1 : offlineCost (ρ ++ ρ') o' =
      ∑ s ∈ range (L + ρ'.length), UnitWeights.dist (f s) (f (s + 1)) := by
    unfold offlineCost
    rw [← List.length_append]
    exact Fin.sum_univ_eq_sum_range (fun s => UnitWeights.dist (f s) (f (s + 1))) _
  have c2 : offlineCost ρ o = ∑ s ∈ range L, UnitWeights.dist (f s) (f (s + 1)) := by
    unfold offlineCost
    rw [← Fin.sum_univ_eq_sum_range]
    refine Fintype.sum_congr _ _ fun s => ?_
    have e1 : f s = o s.castSucc := by
      simp only [f, dif_pos (show (s : ℕ) ≤ L by omega)]
      rfl
    have e2 : f ((s : ℕ) + 1) = o s.succ := by
      simp only [f, dif_pos (show (s : ℕ) + 1 ≤ L by omega)]
      rfl
    rw [e1, e2]
  have c4 : ∑ j ∈ range ρ'.length, UnitWeights.dist (f (L + j)) (f (L + j + 1)) ≤ k := by
    rcases Nat.eq_zero_or_pos ρ'.length with h | h
    · rw [h]; simp
    · obtain ⟨m, hm⟩ : ∃ m, ρ'.length = m + 1 := ⟨ρ'.length - 1, by omega⟩
      rw [hm, Finset.sum_range_succ']
      have hz : ∀ j ∈ range m, UnitWeights.dist (f (L + (j + 1))) (f (L + (j + 1) + 1)) = 0 := by
        intro j _
        have e1 : f (L + (j + 1)) = q := by simp only [f, dif_neg (show ¬ (L + (j + 1) ≤ L) by omega)]
        have e2 : f (L + (j + 1) + 1) = q := by
          simp only [f, dif_neg (show ¬ (L + (j + 1) + 1 ≤ L) by omega)]
        rw [e1, e2, dist_self'']
      rw [Finset.sum_eq_zero hz, zero_add]
      exact dist_le_k' _ _
  have hle : offlineCost (ρ ++ ρ') o' ≤ optCost a ρ + k := by
    rw [c1, Finset.sum_range_add]
    have : optCost a ρ = offlineCost ρ o := hoc.symm
    rw [this, c2]
    exact Nat.add_le_add_left c4 _
  exact le_trans (Nat.sInf_le ⟨o', hfeas, h0, rfl⟩) hle

end GeneralizedUniformServer.Dev.LB.PartA2
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias opt_append := GeneralizedUniformServer.Dev.LB.PartA2.opt_append

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA2
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}

lemma hd_pos (x y : Cfg k) (h : x ≠ y) : 1 ≤ hd x y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  unfold hd
  apply Finset.card_pos.mpr
  exact ⟨i, by simp [hi]⟩

open Classical in
/-- One greedy step: a configuration `u ∉ Q_R` of mass `> τ / N` and a request `r ∈ R` it fails
raise `ecost` by more than `τ / N`. -/
lemma step (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k))
    (hA : IsServing Serves A) (a : Cfg k) (ρ : List (Cfg k)) (R : List (Cfg k)) (τ : ℝ)
    (hτ : 0 < τ) (hbig : τ < ∑ u ∈ univ.filter (fun u : Cfg k => ¬ ∀ r ∈ R, Serves u r), law A a ρ u) :
    ∃ r ∈ R, ecost A a ρ + τ / (Fintype.card (Cfg k) : ℝ) ≤ ecost A a (ρ ++ [r]) := by
  set N : ℝ := (Fintype.card (Cfg k) : ℝ) with hNdef
  have hN : 0 < N := by
    have : Nonempty (Cfg k) := ⟨fun i => i⟩
    rw [hNdef]; exact_mod_cast Fintype.card_pos
  obtain ⟨u, hu, hlaw⟩ : ∃ u ∈ univ.filter (fun u : Cfg k => ¬ ∀ r ∈ R, Serves u r),
      τ / N < law A a ρ u := by
    by_contra hno
    have hno' : ∀ u ∈ univ.filter (fun u : Cfg k => ¬ ∀ r ∈ R, Serves u r),
        law A a ρ u ≤ τ / N := fun u hu => le_of_not_gt fun h => hno ⟨u, hu, h⟩
    have h1 := Finset.sum_le_sum hno'
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : ((univ.filter (fun u : Cfg k => ¬ ∀ r ∈ R, Serves u r)).card : ℝ) ≤ N := by
      rw [hNdef]; exact_mod_cast Finset.card_filter_le _ _
    have h3 : ((univ.filter (fun u : Cfg k => ¬ ∀ r ∈ R, Serves u r)).card : ℝ) * (τ / N)
        ≤ N * (τ / N) := mul_le_mul_of_nonneg_right h2 (div_nonneg hτ.le hN.le)
    rw [mul_div_cancel₀ _ hN.ne'] at h3
    linarith
  have hu' : ¬ ∀ r ∈ R, Serves u r := (Finset.mem_filter.mp hu).2
  push Not at hu'
  obtain ⟨r, hr, hur⟩ := hu'
  refine ⟨r, hr, ?_⟩
  obtain ⟨J, hJ0, hJ1, hJ2, hJc⟩ := cost_split A a ρ [r]
  have hJle : ∀ y', J (u, y') ≤ J (u, y') * (hd u y' : ℝ) := by
    intro y'
    rcases (hJ0 (u, y')).eq_or_lt with h | h
    · rw [← h]; simp
    · have hle : J (u, y') ≤ law A a (ρ ++ [r]) y' := by
        rw [← hJ2 y']
        exact Finset.single_le_sum (f := fun y => J (y, y')) (fun y _ => hJ0 _)
          (Finset.mem_univ u)
      have hs : Serves y' r := law_serves A hA a ρ r y' (by linarith)
      have hne : u ≠ y' := by rintro rfl; exact hur hs
      have := hd_pos u y' hne
      have h1 : (1 : ℝ) ≤ hd u y' := by exact_mod_cast this
      nlinarith
  have hsum : law A a ρ u ≤ ∑ p, J p * (hd p.1 p.2 : ℝ) := by
    rw [← hJ1 u, Fintype.sum_prod_type]
    calc ∑ y', J (u, y') ≤ ∑ y', J (u, y') * (hd u y' : ℝ) := Finset.sum_le_sum fun y' _ => hJle y'
      _ ≤ ∑ x, ∑ y', J (x, y') * (hd x y' : ℝ) :=
          Finset.single_le_sum (f := fun x => ∑ y', J (x, y') * (hd x y' : ℝ))
            (fun x _ => Finset.sum_nonneg fun y' _ => mul_nonneg (hJ0 _) (by positivity))
            (Finset.mem_univ u)
  linarith

open Classical in
theorem confine (hk : 1 ≤ k) (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k))
    (hA : IsServing Serves A) (a : Cfg k) (γ c : ℝ) (hC : Compet A a γ c)
    (ρ0 R : List (Cfg k)) (hR : ∃ q, ∀ r ∈ R, Serves q r) (τ : ℝ) (hτ : 0 < τ) :
    ∃ ρ1 : List (Cfg k), (∀ r ∈ ρ1, r ∈ R) ∧
      ∑ u ∈ univ.filter (fun u : Cfg k => ¬ ∀ r ∈ R, Serves u r), law A a (ρ0 ++ ρ1) u ≤ τ := by
  by_contra hcon0
  have hcon : ∀ ρ1 : List (Cfg k), (∀ r ∈ ρ1, r ∈ R) →
      τ < ∑ u ∈ univ.filter (fun u : Cfg k => ¬ ∀ r ∈ R, Serves u r), law A a (ρ0 ++ ρ1) u :=
    fun ρ1 h1 => lt_of_not_ge fun h => hcon0 ⟨ρ1, h1, h⟩
  set N : ℝ := (Fintype.card (Cfg k) : ℝ) with hNdef
  have hN : 0 < N := by
    have : Nonempty (Cfg k) := ⟨fun i => i⟩
    rw [hNdef]; exact_mod_cast Fintype.card_pos
  obtain ⟨q, hq⟩ := hR
  have grow : ∀ n : ℕ, ∃ ρ1 : List (Cfg k), (∀ r ∈ ρ1, r ∈ R) ∧
      ecost A a ρ0 + n * (τ / N) ≤ ecost A a (ρ0 ++ ρ1) := by
    intro n
    induction n with
    | zero => exact ⟨[], by simp, by simp⟩
    | succ n ih =>
      obtain ⟨ρ1, h1, he⟩ := ih
      obtain ⟨r, hr, hst⟩ := step A hA a (ρ0 ++ ρ1) R τ hτ (hcon ρ1 h1)
      refine ⟨ρ1 ++ [r], ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact h1 x hx
        · rw [List.mem_singleton.mp hx]; exact hr
      · rw [← List.append_assoc]
        push_cast
        linarith
  set B := max γ 0 * ((optCost a ρ0 : ℝ) + k) + c
  have hbound : ∀ ρ1 : List (Cfg k), (∀ r ∈ ρ1, r ∈ R) → ecost A a (ρ0 ++ ρ1) ≤ B := by
    intro ρ1 h1
    have h2 := hC (ρ0 ++ ρ1)
    have h3 : ((optCost a (ρ0 ++ ρ1) : ℕ) : ℝ) ≤ (optCost a ρ0 : ℝ) + k := by
      exact_mod_cast PartA2.opt_append hk a ρ0 ρ1 q (fun r hr => hq r (h1 r hr))
    have h4 : γ * (optCost a (ρ0 ++ ρ1) : ℝ) ≤ max γ 0 * ((optCost a ρ0 : ℝ) + k) :=
      calc γ * (optCost a (ρ0 ++ ρ1) : ℝ) ≤ max γ 0 * (optCost a (ρ0 ++ ρ1) : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max γ 0 * ((optCost a ρ0 : ℝ) + k) :=
            mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
    linarith
  have he0 : 0 ≤ ecost A a ρ0 := ENNReal.toReal_nonneg
  obtain ⟨n, hn⟩ := exists_nat_gt ((B - ecost A a ρ0) / (τ / N))
  obtain ⟨ρ1, h1, he⟩ := grow n
  have := hbound ρ1 h1
  have hτN : 0 < τ / N := div_pos hτ hN
  rw [div_lt_iff₀ hτN] at hn
  linarith

end GeneralizedUniformServer.Dev.LB.PartA2
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias confine := GeneralizedUniformServer.Dev.LB.PartA2.confine

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA3
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
open Classical
variable {k : ℕ}
/-!
# Part A3: one phase of the adversary (paper §4.4–4.6, Lemmas 4.12–4.14, 4.16)

## Plan of the inequalities

Fix `X : Setup k` (good set `G`, algorithm `A`, guarantee `Compet`, history `ρ0`, `k ≥ 2`, `τ > 0`;
at the end `τ = 1/k²`). Write `Q = G.Q`, `N = |Q|`, `M = k(k-1)`, `β = 77/100`, `η = 2/25`,
`c₁ = β(β-η) = 5313/10000`.

* `req (i,a)`: coordinate `i` is some `b ≠ a`, the others `a` (Lemma 4.12, `serves_req`:
  a permutation `x` serves it iff `x i ≠ a`).
* draws `D : Fin t → Fin k × Fin k`, newest first (`D 0` is the latest pair);
  `Rl D = R0 ++ [req (D s)]_s`; requests `S t D`:
  `S 0 D = R0 ++ conf (ρ0 ++ R0) (Rl D)`,
  `S (t+1) D = S t (tail D) ++ req (D 0) :: conf (ρ0 ++ S t (tail D) ++ [req (D 0)]) (Rl D)`,
  where `conf ρ R` is `Classical.choose` of `confine` (or `[]`).  Every element of `S t D`
  lies in `Rl D`; if `σ ∈ Q` avoids every pair of `D`, `σ` serves `Rl D`.
* weights `pw t σ D = ∏_s av σ (D s) / M` with `av σ (i,a) = 1[σ i ≠ a]`; `∑_D pw t σ D = 1`;
  `0 ≤ pw ≤ 1/M^t`.  `μ_t D = law (ρ0 ++ S t D)`.
* `E t = ∑_{σ ∈ Q} ∑_D pw t σ D * ecost (ρ0 ++ S t D)`.

(1) `E 0 ≥ N · ecost ρ0` (cost_split, all terms nonneg).
(2) Step (★), for `σ ∈ Q` avoiding `D` and `d`:
    `ecost (ρ0 ++ S (t+1) (cons d D)) ≥ ecost (ρ0 ++ S t D) + βk ∑_y f_d y μ_t D y - βkτ`,
    `f_d y = 1[y ∈ Q ∧ ∀ z ∈ comp y, ¬ Serves z (req d)]`
    (cost_split; `J p · hd p ≥ βk (J p f_d p.1 - J p 1[p.2 ⊭ Rl (cons d D)])`, the last mass `≤ τ`).
(3) Lemma 4.13: `σ, y ∈ Q`, `σ ∉ comp y` ⟹ `∑_d av σ d f_d y ≥ (β-η) k`, hence
    `βk/M ∑_d av σ d f_d y ≥ c₁ (1[y ∈ Q] - 1[y ∈ Q ∧ σ ∈ comp y])` for all `y`.
    Averaging (★) over `d` (weights `av σ d / M`, total 1) and `∑_y μ 1[y ∈ Q] ≥ 1 - τ`:
    `∑_d av σ d / M · ecost₊ ≥ ecost_t - βkτ + c₁(1-τ) - c₁ b_t σ D`,
    `b_t σ D = ∑_y μ_t D y 1[y ∈ Q ∧ σ ∈ comp y]`.
    Hence `E (t+1) ≥ E t + N (c₁(1-τ) - βkτ) - c₁ B_t`, `B_t = ∑_σ ∑_D pw b`.
(4) Lemma 4.14: `B_t ≤ (k k)^t 2^k / M^t = 2^k (k/(k-1))^t ≤ 2^k e^{t/(k-1)} ≤ N / k`
    for `t ≤ (2/21) k² ln k`, `ln k ≥ 1000` (`N ≥ e^{k ln k/10 - k}/2`).
(5) With `τ = 1/k²`: `E (t+1) ≥ E t + N (c₁ - 3/k)`; `T = ⌊(2/21) k² ln k⌋ + 1`;
    `E T / N ≥ ecost ρ0 + T (c₁ - 3/k) ≥ ecost ρ0 + k² ln k / 20` since
    `(2/21)(c₁ - 3/k) ≥ 1/20` for `k ≥ 477`.
`P = ∑_{σ ∈ Q} ∑_D single (S T D) (pw T σ D / N)`.
-/
/-! ## Requests forbidding one position (Lemma 4.12) -/
/-- Some element different from `a` (if there is one). -/
def other (a : Fin k) : Fin k := if h : ∃ b : Fin k, b ≠ a then h.choose else a

lemma other_ne (hk : 2 ≤ k) (a : Fin k) : other a ≠ a := by
  have h : ∃ b : Fin k, b ≠ a := by
    by_cases ha : a.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
  unfold other; rw [dif_pos h]; exact h.choose_spec

/-- `⟨i, a⟩`. -/
def req (p : Fin k × Fin k) : Cfg k := fun j => if j = p.1 then other p.2 else p.2

/-- Lemma 4.12. -/
lemma serves_req (hk : 2 ≤ k) (x : Cfg k) (hx : IsPerm x) (p : Fin k × Fin k) :
    Serves x (req p) ↔ x p.1 ≠ p.2 := by
  constructor
  · rintro ⟨j, hj⟩ h
    unfold req at hj
    split_ifs at hj with hji
    · rw [hji, h] at hj; exact other_ne hk _ hj.symm
    · exact hji (hx (hj.trans h.symm))
  · intro h
    obtain ⟨l, hl⟩ := Finite.surjective_of_injective hx p.2
    have hl' : l ≠ p.1 := fun e => h (e ▸ hl)
    exact ⟨l, by simp [req, hl', hl]⟩

/-! ## Weights of the draws -/
/-- `1[σ i ≠ a]`. -/
def av (σ : Cfg k) (p : Fin k × Fin k) : ℝ := if σ p.1 ≠ p.2 then 1 else 0

/-- `M = k(k-1)`. -/
def MM (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) - 1)

lemma MM_pos (hk : 2 ≤ k) : 0 < MM k := by
  have : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold MM; nlinarith

lemma MM_le (hk : 2 ≤ k) : MM k ≤ (k : ℝ) ^ 2 := by
  have : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold MM; nlinarith

/-- `pw t σ D = ∏_s av σ (D s) / M`. -/
def pw (t : ℕ) (σ : Cfg k) (D : Fin t → Fin k × Fin k) : ℝ := ∏ s, av σ (D s) / MM k

lemma av_nonneg (σ : Cfg k) (p : Fin k × Fin k) : 0 ≤ av σ p := by
  unfold av; split_ifs <;> norm_num

lemma av_le_one (σ : Cfg k) (p : Fin k × Fin k) : av σ p ≤ 1 := by
  unfold av; split_ifs <;> norm_num

lemma pw_cons (t : ℕ) (σ : Cfg k) (d : Fin k × Fin k) (D : Fin t → Fin k × Fin k) :
    pw (t + 1) σ (Fin.cons d D) = av σ d / MM k * pw t σ D := by
  simp only [pw, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma pw_nonneg (hk : 2 ≤ k) (t : ℕ) (σ : Cfg k) (D : Fin t → Fin k × Fin k) : 0 ≤ pw t σ D :=
  Finset.prod_nonneg fun _ _ => div_nonneg (av_nonneg _ _) (MM_pos hk).le

lemma pw_le (hk : 2 ≤ k) (t : ℕ) (σ : Cfg k) (D : Fin t → Fin k × Fin k) :
    pw t σ D ≤ 1 / MM k ^ t := by
  unfold pw
  calc ∏ s, av σ (D s) / MM k ≤ ∏ _s : Fin t, 1 / MM k :=
        Finset.prod_le_prod (fun s _ => div_nonneg (av_nonneg _ _) (MM_pos hk).le)
          (fun s _ => div_le_div_of_nonneg_right (av_le_one _ _) (MM_pos hk).le)
    _ = 1 / MM k ^ t := by simp

lemma pw_ne_zero {t : ℕ} {σ : Cfg k} {D : Fin t → Fin k × Fin k} (h : pw t σ D ≠ 0) :
    ∀ s, σ (D s).1 ≠ (D s).2 := by
  intro s hs
  apply h
  unfold pw
  exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [av, hs])

lemma sum_cons {α : Type*} [Fintype α] {t : ℕ} (F : (Fin (t + 1) → α) → ℝ) :
    ∑ D, F D = ∑ d, ∑ D : Fin t → α, F (Fin.cons d D) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

lemma sum_av (hk : 2 ≤ k) (σ : Cfg k) : ∑ d, av σ d / MM k = 1 := by
  have h1 : ∑ d, av σ d = MM k := by
    rw [Fintype.sum_prod_type]
    have : ∀ i : Fin k, ∑ a : Fin k, av σ (i, a) = (k : ℝ) - 1 := by
      intro i
      simp only [av]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      have : (univ.filter fun a : Fin k => σ i ≠ a) = univ.erase (σ i) := by
        ext a; simp [eq_comm]
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      have : 1 ≤ k := by omega
      push_cast [this]; ring
    simp [this, MM]; ring
  rw [← Finset.sum_div, h1, div_self (MM_pos hk).ne']

/-- Expectation over one more draw. -/
lemma sum_pw_succ (t : ℕ) (σ : Cfg k) (F : (Fin (t + 1) → Fin k × Fin k) → ℝ) :
    ∑ D, pw (t + 1) σ D * F D = ∑ D : Fin t → Fin k × Fin k,
      pw t σ D * ∑ d, av σ d / MM k * F (Fin.cons d D) := by
  rw [sum_cons, Finset.sum_comm]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pw_cons]; ring

lemma sum_pw (hk : 2 ≤ k) (t : ℕ) (σ : Cfg k) : ∑ D : Fin t → Fin k × Fin k, pw t σ D = 1 := by
  induction t with
  | zero => simp [pw]
  | succ t ih =>
    have := sum_pw_succ t σ (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    simp [sum_av hk, ih]

/-! ## The setup of one phase -/
structure Setup (k : ℕ) where
  G : GoodSet k
  a : Cfg k
  A : GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k)
  hA : IsServing Serves A
  γ : ℝ
  c : ℝ
  hC : Compet A a γ c
  ρ0 : List (Cfg k)
  hk : 2 ≤ k
  τ : ℝ
  hτ : 0 < τ

end GeneralizedUniformServer.Dev.LB.PartA3
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA3
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
open Classical
variable {k : ℕ}
namespace Setup
variable (X : Setup k)
lemma hk1 (X : Setup k) : 1 ≤ k := by have := X.hk; omega

open Classical in
/-- The confinement sequence of Lemma 4.15 (or `[]`). -/
def conf (ρ R : List (Cfg k)) : List (Cfg k) :=
  if h : ∃ q, ∀ r ∈ R, Serves q r then
    Classical.choose (confine X.hk1 X.A X.hA X.a X.γ X.c X.hC ρ R h X.τ X.hτ)
  else []

lemma conf_sub (ρ R : List (Cfg k)) : ∀ r ∈ X.conf ρ R, r ∈ R := by
  unfold conf
  split_ifs with h
  · exact (Classical.choose_spec (confine X.hk1 X.A X.hA X.a X.γ X.c X.hC ρ R h X.τ X.hτ)).1
  · simp

/-- Mass of `law (ρ ++ conf ρ R)` outside the configurations serving `R`. -/
lemma conf_spec (ρ R : List (Cfg k)) (h : ∃ q, ∀ r ∈ R, Serves q r) :
    ∑ u : Cfg k, (if ∀ r ∈ R, Serves u r then 0 else law X.A X.a (ρ ++ X.conf ρ R) u) ≤ X.τ := by
  classical
  have := (Classical.choose_spec (confine X.hk1 X.A X.hA X.a X.γ X.c X.hC ρ R h X.τ X.hτ)).2
  unfold conf
  rw [dif_pos h]
  convert this using 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> simp_all

/-- `R0 ++ [req (D s)]_s`. -/
def Rl {t : ℕ} (D : Fin t → Fin k × Fin k) : List (Cfg k) :=
  X.G.R0 ++ List.ofFn (fun s => req (D s))

lemma mem_Rl {t : ℕ} (D : Fin t → Fin k × Fin k) (r : Cfg k) :
    r ∈ X.Rl D ↔ r ∈ X.G.R0 ∨ ∃ s, req (D s) = r := by
  simp [Rl, List.mem_ofFn]

/-- The requests of the phase up to the confinement after the `t`-th draw. -/
def S : (t : ℕ) → (Fin t → Fin k × Fin k) → List (Cfg k)
  | 0, D => X.G.R0 ++ X.conf (X.ρ0 ++ X.G.R0) (X.Rl D)
  | t + 1, D => S t (Fin.tail D) ++
      (req (D 0) :: X.conf (X.ρ0 ++ S t (Fin.tail D) ++ [req (D 0)]) (X.Rl D))

lemma S_cons (t : ℕ) (d : Fin k × Fin k) (D : Fin t → Fin k × Fin k) :
    X.S (t + 1) (Fin.cons d D) = X.S t D ++
      (req d :: X.conf (X.ρ0 ++ X.S t D ++ [req d]) (X.Rl (Fin.cons d D : Fin (t+1) → _))) := by
  simp only [S, Fin.tail_cons, Fin.cons_zero]

lemma mem_S : ∀ (t : ℕ) (D : Fin t → Fin k × Fin k), ∀ r ∈ X.S t D, r ∈ X.Rl D := by
  intro t
  induction t with
  | zero =>
    intro D r hr
    simp only [S, List.mem_append] at hr
    rcases hr with hr | hr
    · exact (X.mem_Rl D r).2 (Or.inl hr)
    · exact X.conf_sub _ _ r hr
  | succ t ih =>
    intro D r hr
    simp only [S, List.mem_append, List.mem_cons] at hr
    rcases hr with hr | hr | hr
    · rcases (X.mem_Rl _ r).1 (ih _ r hr) with h | ⟨s, hs⟩
      · exact (X.mem_Rl D r).2 (Or.inl h)
      · exact (X.mem_Rl D r).2 (Or.inr ⟨s.succ, hs⟩)
    · exact (X.mem_Rl D r).2 (Or.inr ⟨0, hr.symm⟩)
    · exact X.conf_sub _ _ r hr

lemma serves_Rl {t : ℕ} (D : Fin t → Fin k × Fin k) (σ : Cfg k) (hσ : σ ∈ X.G.Q)
    (hD : ∀ s, σ (D s).1 ≠ (D s).2) : ∀ r ∈ X.Rl D, Serves σ r := by
  intro r hr
  rcases (X.mem_Rl D r).1 hr with h | ⟨s, rfl⟩
  · exact (X.G.serves_iff σ).2 hσ r h
  · exact (serves_req X.hk σ (X.G.perm σ hσ) (D s)).2 (hD s)

lemma serves_S {t : ℕ} (D : Fin t → Fin k × Fin k) (σ : Cfg k) (hσ : σ ∈ X.G.Q)
    (hD : ∀ s, σ (D s).1 ≠ (D s).2) : ∀ r ∈ X.S t D, Serves σ r :=
  fun r hr => X.serves_Rl D σ hσ hD r (X.mem_S t D r hr)

/-- `μ_t D`. -/
def μ (t : ℕ) (D : Fin t → Fin k × Fin k) (y : Cfg k) : ℝ := law X.A X.a (X.ρ0 ++ X.S t D) y

lemma μ_nonneg (t : ℕ) (D : Fin t → Fin k × Fin k) (y : Cfg k) : 0 ≤ X.μ t D y :=
  ENNReal.toReal_nonneg

lemma μ_sum (t : ℕ) (D : Fin t → Fin k × Fin k) : ∑ y, X.μ t D y = 1 :=
  law_sum _ _ _

/-- Confinement after every step. -/
lemma μ_conf (t : ℕ) (D : Fin t → Fin k × Fin k) (h : ∃ q, ∀ r ∈ X.Rl D, Serves q r) :
    ∑ u : Cfg k, (if ∀ r ∈ X.Rl D, Serves u r then 0 else X.μ t D u) ≤ X.τ := by
  cases t with
  | zero =>
    have := X.conf_spec (X.ρ0 ++ X.G.R0) (X.Rl D) h
    simpa [μ, S, List.append_assoc] using this
  | succ t =>
    have := X.conf_spec (X.ρ0 ++ X.S t (Fin.tail D) ++ [req (D 0)]) (X.Rl D) h
    simpa [μ, S, List.append_assoc] using this

/-- `f_d y = 1[y ∈ Q ∧ req d eliminates comp y]`. -/
def f (d : Fin k × Fin k) (y : Cfg k) : ℝ :=
  if y ∈ X.G.Q ∧ ∀ z ∈ X.G.comp y, ¬ Serves z (req d) then 1 else 0

lemma f_nonneg (d : Fin k × Fin k) (y : Cfg k) : 0 ≤ X.f d y := by
  unfold f; split_ifs <;> norm_num

/-- (★) One draw, one confinement: the cost grows by `βk · Pr[elimination] - βkτ`. -/
lemma step_star (t : ℕ) (σ : Cfg k) (hσ : σ ∈ X.G.Q) (D : Fin t → Fin k × Fin k)
    (hD : ∀ s, σ (D s).1 ≠ (D s).2) (d : Fin k × Fin k) (hdd : σ d.1 ≠ d.2) :
    ecost X.A X.a (X.ρ0 ++ X.S t D) + (77 / 100 * (k : ℝ)) * ∑ y, X.f d y * X.μ t D y
      - (77 / 100 * (k : ℝ)) * X.τ ≤ ecost X.A X.a (X.ρ0 ++ X.S (t + 1) (Fin.cons d D)) := by
  set R := X.Rl (Fin.cons d D : Fin (t + 1) → Fin k × Fin k) with hR
  obtain ⟨J, hJ0, hJ1, hJ2, hJc⟩ := cost_split X.A X.a (X.ρ0 ++ X.S t D)
    (req d :: X.conf (X.ρ0 ++ X.S t D ++ [req d]) R)
  have heq : X.ρ0 ++ X.S t D ++ (req d :: X.conf (X.ρ0 ++ X.S t D ++ [req d]) R) =
      X.ρ0 ++ X.S (t + 1) (Fin.cons d D) := by
    rw [S_cons, ← hR]; simp
  rw [heq] at hJ2 hJc
  have hDc : ∀ s, σ ((Fin.cons d D : Fin (t + 1) → Fin k × Fin k) s).1 ≠
      ((Fin.cons d D : Fin (t + 1) → Fin k × Fin k) s).2 := by
    intro s
    refine Fin.cases ?_ (fun s => ?_) s
    · exact hdd
    · exact hD s
  have hserv : ∃ q, ∀ r ∈ R, Serves q r := ⟨σ, X.serves_Rl _ σ hσ hDc⟩
  have hτ' := X.μ_conf (t + 1) (Fin.cons d D) hserv
  have hR0 : ∀ r ∈ X.G.R0, r ∈ R := fun r hr => (X.mem_Rl _ r).2 (Or.inl hr)
  have hRd : req d ∈ R := (X.mem_Rl _ _).2 (Or.inr ⟨0, by simp⟩)
  set g : Cfg k → ℝ := fun y' => if ∀ r ∈ R, Serves y' r then 0 else 1 with hg
  have key : ∀ p : Cfg k × Cfg k,
      (77 / 100 * (k : ℝ)) * (J p * X.f d p.1 - J p * g p.2) ≤ J p * (hd p.1 p.2 : ℝ) := by
    intro p
    have hJp := hJ0 p
    have hhd : (0 : ℝ) ≤ hd p.1 p.2 := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    by_cases hf : p.1 ∈ X.G.Q ∧ ∀ z ∈ X.G.comp p.1, ¬ Serves z (req d)
    · by_cases hgp : ∀ r ∈ R, Serves p.2 r
      · have hQ2 : p.2 ∈ X.G.Q := (X.G.serves_iff p.2).1 (fun r hr => hgp r (hR0 r hr))
        have hn : p.2 ∉ X.G.comp p.1 := fun hm => hf.2 p.2 hm (hgp _ hRd)
        have hfar := X.G.far p.1 hf.1 p.2 hQ2 hn
        simp only [f, if_pos hf, hg, if_pos hgp]
        nlinarith
      · simp only [f, if_pos hf, hg, if_neg hgp]
        nlinarith
    · simp only [f, if_neg hf]
      have : 0 ≤ g p.2 := by simp only [hg]; split_ifs <;> norm_num
      nlinarith [mul_nonneg hJp hhd,
        mul_nonneg (by positivity : (0 : ℝ) ≤ 77 / 100 * k) (mul_nonneg hJp this)]
  have hs1 : ∑ p : Cfg k × Cfg k, J p * X.f d p.1 = ∑ y, X.f d y * X.μ t D y := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only
    rw [← Finset.sum_mul, hJ1 y, mul_comm]; rfl
  have hs2 : ∑ p : Cfg k × Cfg k, J p * g p.2 ≤ X.τ := by
    rw [Fintype.sum_prod_type_right]
    refine le_trans (le_of_eq ?_) hτ'
    refine Finset.sum_congr rfl fun y' _ => ?_
    simp only
    rw [← Finset.sum_mul, hJ2 y']
    simp only [hg, μ]
    split_ifs <;> simp
  have hsum := Finset.sum_le_sum fun p (_ : p ∈ (univ : Finset (Cfg k × Cfg k))) => key p
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hs1] at hsum
  have hk0 : (0 : ℝ) ≤ 77 / 100 * k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hs2 hk0]

/-- `1[y ∈ Q]`. -/
def qi (y : Cfg k) : ℝ := if y ∈ X.G.Q then 1 else 0

/-- `1[y ∈ Q ∧ σ ∈ comp y]`. -/
def ci (σ y : Cfg k) : ℝ := if y ∈ X.G.Q ∧ σ ∈ X.G.comp y then 1 else 0

lemma ci_nonneg (σ y : Cfg k) : 0 ≤ X.ci σ y := by
  unfold ci; split_ifs <;> norm_num

/-- Lemma 4.13 (counting form). -/
lemma lem413 (σ : Cfg k) (hσ : σ ∈ X.G.Q) (y : Cfg k) (hy : y ∈ X.G.Q) (hn : σ ∉ X.G.comp y) :
    (69 / 100 : ℝ) * k ≤ ∑ d, av σ d * X.f d y := by
  have hfar := X.G.far y hy σ hσ hn
  have hrig := X.G.rigid y hy
  unfold hd at hfar
  obtain ⟨I1, hI1c, hI1⟩ : ∃ I1 : Finset (Fin k), (77 / 100 : ℝ) * k < I1.card ∧
      ∀ i ∈ I1, y i ≠ σ i :=
    ⟨_, hfar, fun i hi => (Finset.mem_filter.1 hi).2⟩
  obtain ⟨I2, hI2c, hI2⟩ : ∃ I2 : Finset (Fin k), (I2.card : ℝ) < (2 / 25 : ℝ) * k ∧
      ∀ i, i ∉ I2 → ∀ z ∈ X.G.comp y, z i = y i :=
    ⟨_, hrig, fun i hi z hz => by
      by_contra h
      exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, z, hz, h⟩)⟩
  have hcard : (I1.card : ℝ) ≤ ((I1 \ I2).card : ℝ) + I2.card := by
    exact_mod_cast Finset.card_le_card_sdiff_add_card
  have hge : ((I1 \ I2).card : ℝ) ≤ ∑ d, av σ d * X.f d y := by
    rw [Fintype.sum_prod_type]
    calc ((I1 \ I2).card : ℝ) = ∑ i ∈ I1 \ I2, av σ (i, y i) * X.f (i, y i) y := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          obtain ⟨hi1, hi2⟩ := Finset.mem_sdiff.1 hi
          have h1 : σ i ≠ y i := fun e => hI1 i hi1 e.symm
          have h2 : y ∈ X.G.Q ∧ ∀ z ∈ X.G.comp y, ¬ Serves z (req (i, y i)) := by
            refine ⟨hy, fun z hz => ?_⟩
            have hzQ := X.G.comp_sub y hy hz
            rw [serves_req X.hk z (X.G.perm z hzQ)]
            simp [hI2 i hi2 z hz]
          simp only [av, f]
          rw [if_pos h1, if_pos h2]
          norm_num
      _ ≤ ∑ i, av σ (i, y i) * X.f (i, y i) y :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => mul_nonneg (av_nonneg _ _) (X.f_nonneg _ _))
      _ ≤ ∑ i, ∑ a, av σ (i, a) * X.f (i, a) y :=
          Finset.sum_le_sum fun i _ =>
            Finset.single_le_sum (f := fun a => av σ (i, a) * X.f (i, a) y)
              (fun a _ => mul_nonneg (av_nonneg _ _) (X.f_nonneg _ _)) (Finset.mem_univ (y i))
  linarith

lemma avg_bound (σ : Cfg k) (hσ : σ ∈ X.G.Q) (y : Cfg k) :
    (5313 / 10000 : ℝ) * (X.qi y - X.ci σ y) ≤
      (77 / 100 * (k : ℝ)) * ∑ d, av σ d / MM k * X.f d y := by
  have hM := MM_pos X.hk
  have hMle := MM_le X.hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hS0 : 0 ≤ ∑ d, av σ d * X.f d y :=
    Finset.sum_nonneg fun d _ => mul_nonneg (av_nonneg _ _) (X.f_nonneg _ _)
  have heq : ∑ d, av σ d / MM k * X.f d y = (∑ d, av σ d * X.f d y) / MM k := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun d _ => by ring
  rw [heq]
  have hnn : 0 ≤ (77 / 100 * (k : ℝ)) * ((∑ d, av σ d * X.f d y) / MM k) :=
    mul_nonneg (by positivity) (div_nonneg hS0 hM.le)
  by_cases hy : y ∈ X.G.Q
  · by_cases hn : σ ∈ X.G.comp y
    · simp only [qi, ci, if_pos hy, if_pos (And.intro hy hn), sub_self, mul_zero]
      exact hnn
    · simp only [qi, ci, if_pos hy, if_neg (fun h : y ∈ X.G.Q ∧ σ ∈ X.G.comp y => hn h.2),
        sub_zero, mul_one]
      have h413 := X.lem413 σ hσ y hy hn
      rw [mul_div_assoc', le_div_iff₀ hM]
      nlinarith [mul_le_mul_of_nonneg_left h413 (by positivity : (0 : ℝ) ≤ 77 / 100 * k)]
  · simp only [qi, ci, if_neg hy, if_neg (fun h : y ∈ X.G.Q ∧ σ ∈ X.G.comp y => hy h.1),
      sub_self, mul_zero]
    exact hnn

/-- `b_t σ D = Pr[Y_t ∈ Q, σ ∈ C(Y_t)]` for fixed draws. -/
def b (t : ℕ) (σ : Cfg k) (D : Fin t → Fin k × Fin k) : ℝ := ∑ y, X.μ t D y * X.ci σ y

lemma b_nonneg (t : ℕ) (σ : Cfg k) (D : Fin t → Fin k × Fin k) : 0 ≤ X.b t σ D :=
  Finset.sum_nonneg fun y _ => mul_nonneg (X.μ_nonneg t D y) (X.ci_nonneg σ y)

lemma mass_Q (t : ℕ) (σ : Cfg k) (hσ : σ ∈ X.G.Q) (D : Fin t → Fin k × Fin k)
    (hD : ∀ s, σ (D s).1 ≠ (D s).2) : 1 - X.τ ≤ ∑ y, X.μ t D y * X.qi y := by
  have hserv : ∃ q, ∀ r ∈ X.Rl D, Serves q r := ⟨σ, X.serves_Rl D σ hσ hD⟩
  have h1 := X.μ_conf t D hserv
  have h2 := X.μ_sum t D
  have h3 : ∀ y, X.μ t D y ≤ X.μ t D y * X.qi y +
      (if ∀ r ∈ X.Rl D, Serves y r then 0 else X.μ t D y) := by
    intro y
    have := X.μ_nonneg t D y
    by_cases hs : ∀ r ∈ X.Rl D, Serves y r
    · have hyQ : y ∈ X.G.Q :=
        (X.G.serves_iff y).1 (fun r hr => hs r ((X.mem_Rl D r).2 (Or.inl hr)))
      rw [if_pos hs]; simp [qi, hyQ]
    · simp only [if_neg hs]; unfold qi; split_ifs <;> linarith
  have h4 := Finset.sum_le_sum fun y (_ : y ∈ (univ : Finset (Cfg k))) => h3 y
  rw [Finset.sum_add_distrib, h2] at h4
  linarith

/-- (★★) (★) averaged over the next draw. -/
lemma avg_step (t : ℕ) (σ : Cfg k) (hσ : σ ∈ X.G.Q) (D : Fin t → Fin k × Fin k)
    (hD : ∀ s, σ (D s).1 ≠ (D s).2) :
    ecost X.A X.a (X.ρ0 ++ X.S t D) - (77 / 100 * (k : ℝ)) * X.τ
      + (5313 / 10000 : ℝ) * (1 - X.τ) - (5313 / 10000 : ℝ) * X.b t σ D ≤
      ∑ d, av σ d / MM k * ecost X.A X.a (X.ρ0 ++ X.S (t + 1) (Fin.cons d D)) := by
  set E0 := ecost X.A X.a (X.ρ0 ++ X.S t D)
  have hM := MM_pos X.hk
  have h1 : ∀ d, av σ d / MM k *
      (E0 - (77 / 100 * (k : ℝ)) * X.τ + (77 / 100 * (k : ℝ)) * ∑ y, X.f d y * X.μ t D y) ≤
      av σ d / MM k * ecost X.A X.a (X.ρ0 ++ X.S (t + 1) (Fin.cons d D)) := by
    intro d
    by_cases hdd : σ d.1 ≠ d.2
    · apply mul_le_mul_of_nonneg_left _ (div_nonneg (av_nonneg _ _) hM.le)
      have := X.step_star t σ hσ D hD d hdd
      linarith
    · have : av σ d = 0 := by simp only [av]; rw [if_neg hdd]
      simp [this]
  have h2 := Finset.sum_le_sum fun d (_ : d ∈ (univ : Finset (Fin k × Fin k))) => h1 d
  refine le_trans ?_ h2
  have h3a : ∑ d, av σ d / MM k *
      (E0 - (77 / 100 * (k : ℝ)) * X.τ + (77 / 100 * (k : ℝ)) * ∑ y, X.f d y * X.μ t D y) =
      ∑ d, av σ d / MM k * (E0 - (77 / 100 * (k : ℝ)) * X.τ) +
        ∑ d, av σ d / MM k * ((77 / 100 * (k : ℝ)) * ∑ y, X.f d y * X.μ t D y) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  have h3b : ∑ d, av σ d / MM k * ((77 / 100 * (k : ℝ)) * ∑ y, X.f d y * X.μ t D y) =
      ∑ y, X.μ t D y * ((77 / 100 * (k : ℝ)) * ∑ d, av σ d / MM k * X.f d y) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun d _ => by ring
  rw [h3a, h3b, ← Finset.sum_mul, sum_av X.hk, one_mul]
  have h4 : ∀ y, X.μ t D y * ((5313 / 10000 : ℝ) * (X.qi y - X.ci σ y)) ≤
      X.μ t D y * ((77 / 100 * (k : ℝ)) * ∑ d, av σ d / MM k * X.f d y) :=
    fun y => mul_le_mul_of_nonneg_left (X.avg_bound σ hσ y) (X.μ_nonneg t D y)
  have h5 := Finset.sum_le_sum fun y (_ : y ∈ (univ : Finset (Cfg k))) => h4 y
  have h6 : ∑ y, X.μ t D y * ((5313 / 10000 : ℝ) * (X.qi y - X.ci σ y)) =
      (5313 / 10000 : ℝ) * ∑ y, X.μ t D y * X.qi y - (5313 / 10000 : ℝ) * X.b t σ D := by
    simp only [b, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h7 := X.mass_Q t σ hσ D hD
  linarith

/-- `E t = ∑_σ ∑_D pw · ecost`. -/
def E (t : ℕ) : ℝ :=
  ∑ σ ∈ X.G.Q, ∑ D : Fin t → Fin k × Fin k, pw t σ D * ecost X.A X.a (X.ρ0 ++ X.S t D)

/-- `B t = ∑_σ ∑_D pw · b`. -/
def B (t : ℕ) : ℝ := ∑ σ ∈ X.G.Q, ∑ D : Fin t → Fin k × Fin k, pw t σ D * X.b t σ D

lemma E_succ (t : ℕ) :
    X.E t + (X.G.Q.card : ℝ) * ((5313 / 10000 : ℝ) * (1 - X.τ) - (77 / 100 * (k : ℝ)) * X.τ)
      - (5313 / 10000 : ℝ) * X.B t ≤ X.E (t + 1) := by
  set K := (5313 / 10000 : ℝ) * (1 - X.τ) - (77 / 100 * (k : ℝ)) * X.τ with hK
  have h : ∀ σ ∈ X.G.Q, ∑ D : Fin t → Fin k × Fin k, pw t σ D *
      (ecost X.A X.a (X.ρ0 ++ X.S t D) + K - (5313 / 10000 : ℝ) * X.b t σ D) ≤
      ∑ D, pw (t + 1) σ D * ecost X.A X.a (X.ρ0 ++ X.S (t + 1) D) := by
    intro σ hσ
    rw [sum_pw_succ]
    refine Finset.sum_le_sum fun D _ => ?_
    by_cases hp : pw t σ D = 0
    · simp [hp]
    · apply mul_le_mul_of_nonneg_left _ (pw_nonneg X.hk t σ D)
      have := X.avg_step t σ hσ D (pw_ne_zero hp)
      rw [hK]; linarith
  have h' : ∀ σ ∈ X.G.Q, ∑ D : Fin t → Fin k × Fin k, pw t σ D *
      (ecost X.A X.a (X.ρ0 ++ X.S t D) + K - (5313 / 10000 : ℝ) * X.b t σ D) =
      ∑ D : Fin t → Fin k × Fin k, pw t σ D * ecost X.A X.a (X.ρ0 ++ X.S t D) + K -
        (5313 / 10000 : ℝ) * ∑ D : Fin t → Fin k × Fin k, pw t σ D * X.b t σ D := by
    intro σ _
    have h1 : ∑ D : Fin t → Fin k × Fin k, pw t σ D *
        (ecost X.A X.a (X.ρ0 ++ X.S t D) + K - (5313 / 10000 : ℝ) * X.b t σ D) =
        ∑ D : Fin t → Fin k × Fin k, pw t σ D * ecost X.A X.a (X.ρ0 ++ X.S t D) +
          K * ∑ D : Fin t → Fin k × Fin k, pw t σ D -
          (5313 / 10000 : ℝ) * ∑ D : Fin t → Fin k × Fin k, pw t σ D * X.b t σ D := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun D _ => by ring
    rw [h1, sum_pw X.hk, mul_one]
  have h2 := Finset.sum_le_sum h
  rw [Finset.sum_congr rfl h', Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum] at h2
  unfold E B
  linarith

lemma ecost_mono (ρ ρ' : List (Cfg k)) : ecost X.A X.a ρ ≤ ecost X.A X.a (ρ ++ ρ') := by
  obtain ⟨J, hJ0, -, -, hJc⟩ := cost_split X.A X.a ρ ρ'
  have : 0 ≤ ∑ p, J p * (hd p.1 p.2 : ℝ) :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hJ0 p) (Nat.cast_nonneg _)
  linarith

lemma E_zero : (X.G.Q.card : ℝ) * ecost X.A X.a X.ρ0 ≤ X.E 0 := by
  unfold E
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun σ _ => ?_
  calc ecost X.A X.a X.ρ0 = ∑ D : Fin 0 → Fin k × Fin k, pw 0 σ D * ecost X.A X.a X.ρ0 := by
        rw [← Finset.sum_mul, sum_pw X.hk, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun D _ =>
        mul_le_mul_of_nonneg_left (X.ecost_mono _ _) (pw_nonneg X.hk 0 σ D)

/-- Lemma 4.14 (counting form). -/
lemma B_le (t : ℕ) : X.B t ≤ ((k : ℝ) * k) ^ t * 2 ^ k / MM k ^ t := by
  have hM := MM_pos X.hk
  have hinner : ∀ y, ∑ σ ∈ X.G.Q, X.ci σ y ≤ 2 ^ k := by
    intro y
    by_cases hy : y ∈ X.G.Q
    · have h1 : ∑ σ ∈ X.G.Q, X.ci σ y = ∑ σ ∈ X.G.Q.filter (fun σ => σ ∈ X.G.comp y), (1 : ℝ) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun σ _ => by simp [ci, hy]
      rw [h1, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h2 : (X.G.Q.filter (fun σ => σ ∈ X.G.comp y)).card ≤ (X.G.comp y).card :=
        Finset.card_le_card fun σ h => (Finset.mem_filter.1 h).2
      have h3 := X.G.small y hy
      have : (X.G.Q.filter (fun σ => σ ∈ X.G.comp y)).card ≤ 2 ^ k := by omega
      exact_mod_cast this
    · have : ∀ σ ∈ X.G.Q, X.ci σ y = 0 := fun σ _ => by
        simp only [ci]; rw [if_neg (fun h => hy h.1)]
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
      positivity
  have hD : ∀ D : Fin t → Fin k × Fin k, ∑ σ ∈ X.G.Q, X.b t σ D ≤ 2 ^ k := by
    intro D
    calc ∑ σ ∈ X.G.Q, X.b t σ D = ∑ y, X.μ t D y * ∑ σ ∈ X.G.Q, X.ci σ y := by
          simp only [b, Finset.mul_sum]; rw [Finset.sum_comm]
      _ ≤ ∑ y, X.μ t D y * 2 ^ k := Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hinner y) (X.μ_nonneg t D y)
      _ = 2 ^ k := by rw [← Finset.sum_mul, X.μ_sum, one_mul]
  have hMt : 0 ≤ 1 / MM k ^ t := div_nonneg zero_le_one (pow_nonneg hM.le t)
  calc X.B t ≤ ∑ σ ∈ X.G.Q, ∑ D : Fin t → Fin k × Fin k, 1 / MM k ^ t * X.b t σ D :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun D _ =>
          mul_le_mul_of_nonneg_right (pw_le X.hk t σ D) (X.b_nonneg t σ D)
    _ = ∑ D : Fin t → Fin k × Fin k, 1 / MM k ^ t * ∑ σ ∈ X.G.Q, X.b t σ D := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ D : Fin t → Fin k × Fin k, 1 / MM k ^ t * 2 ^ k :=
        Finset.sum_le_sum fun D _ => mul_le_mul_of_nonneg_left (hD D) hMt
    _ = ((k : ℝ) * k) ^ t * 2 ^ k / MM k ^ t := by
        rw [Finset.sum_const, Finset.card_univ]
        simp
        ring

end Setup
end GeneralizedUniformServer.Dev.LB.PartA3
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA3
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
open Classical
variable {k : ℕ}
/-! ## Numerics -/
lemma numeric (k L t : ℝ) (hL : 1000 ≤ L) (hLk : L ≤ k)
    (ht : t ≤ 2 / 21 * k ^ 2 * L) : t / (k - 1) + k + L + 1 ≤ k * L / 10 - k := by
  have hk1 : 0 < k - 1 := by linarith
  have h1 : t / (k - 1) ≤ 2 / 21 * (k + 2) * L := by
    rw [div_le_iff₀ hk1]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k - 2) (by linarith : (0 : ℝ) ≤ L)]
  nlinarith [mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ k)]

lemma B_num (hk : 2 ≤ k) (t : ℕ) (hL : 1000 ≤ Real.log k) (hLk : Real.log k ≤ k)
    (ht : (t : ℝ) ≤ 2 / 21 * (k : ℝ) ^ 2 * Real.log k) :
    ((k : ℝ) * k) ^ t * 2 ^ k / MM k ^ t * k * 2 ≤
      Real.exp ((k : ℝ) * Real.log k / 10 - k) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hM := MM_pos hk
  have e1 : ((k : ℝ) * k) ^ t / MM k ^ t ≤ Real.exp (t / ((k : ℝ) - 1)) := by
    rw [← div_pow]
    have h : (k : ℝ) * k / MM k = 1 / ((k : ℝ) - 1) + 1 := by
      have : (k : ℝ) - 1 ≠ 0 := by linarith
      unfold MM; field_simp; ring
    rw [h]
    calc (1 / ((k : ℝ) - 1) + 1) ^ t ≤ Real.exp (1 / ((k : ℝ) - 1)) ^ t :=
          pow_le_pow_left₀ (by have : (0 : ℝ) < k - 1 := by linarith
                               positivity) (Real.add_one_le_exp _) t
      _ = Real.exp (t / ((k : ℝ) - 1)) := by rw [← Real.exp_nat_mul]; ring_nf
  have e4 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have e2 : (2 : ℝ) ^ k ≤ Real.exp k := by
    calc (2 : ℝ) ^ k ≤ Real.exp 1 ^ k := pow_le_pow_left₀ (by norm_num) e4 k
      _ = Real.exp k := by rw [← Real.exp_nat_mul]; ring_nf
  have e3 : (k : ℝ) = Real.exp (Real.log k) := (Real.exp_log (by linarith)).symm
  have hnum := numeric k (Real.log k) t hL hLk ht
  calc ((k : ℝ) * k) ^ t * 2 ^ k / MM k ^ t * k * 2
        = (((k : ℝ) * k) ^ t / MM k ^ t) * 2 ^ k * k * 2 := by ring
    _ ≤ Real.exp (t / ((k : ℝ) - 1)) * Real.exp k * Real.exp (Real.log k) * Real.exp 1 := by
        apply mul_le_mul _ e4 (by norm_num) (by positivity)
        apply mul_le_mul _ e3.le (by positivity) (by positivity)
        exact mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = Real.exp (t / ((k : ℝ) - 1) + k + Real.log k + 1) := by
        simp only [Real.exp_add]
    _ ≤ Real.exp ((k : ℝ) * Real.log k / 10 - k) := Real.exp_le_exp.2 hnum

end GeneralizedUniformServer.Dev.LB.PartA3
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA3
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
open Classical
variable {k : ℕ}
namespace Setup
variable (X : Setup k)
/-! ## One phase -/
lemma main (hkR : (1001 : ℝ) ≤ k) (hL : 1000 ≤ Real.log k) (hτ : X.τ = 1 / (k : ℝ) ^ 2) :
    ∃ P : List (Cfg k) →₀ ℝ, (∀ ρ', 0 ≤ P ρ') ∧ (P.sum fun _ x => x) = 1 ∧
      (∀ ρ' ∈ P.support, ∃ q, ∀ r ∈ ρ', Serves q r) ∧
      ecost X.A X.a X.ρ0 + (k : ℝ) ^ 2 * Real.log k / 20 ≤
        P.sum fun ρ' x => x * ecost X.A X.a (X.ρ0 ++ ρ') := by
  have hkpos : (0 : ℝ) < k := by linarith
  have hLk : Real.log k ≤ k := by have := Real.log_le_sub_one_of_pos hkpos; linarith
  set N : ℝ := (X.G.Q.card : ℝ) with hN
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) X.G.card
  set T := ⌊(2 / 21 : ℝ) * k ^ 2 * Real.log k⌋₊ + 1 with hT
  set δ : ℝ := 5313 / 10000 - 3 / k with hδ
  have hK : δ ≤ (5313 / 10000 : ℝ) * (1 - X.τ) - (77 / 100 * (k : ℝ)) * X.τ -
      (5313 / 10000 : ℝ) * (1 / k) := by
    rw [hτ, hδ]
    have hu : (k : ℝ) * (1 / k) = 1 := by field_simp
    have hu0 : 0 < 1 / (k : ℝ) := by positivity
    have hu1 : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hkpos]; linarith
    have e1 : 1 / (k : ℝ) ^ 2 = (1 / k) * (1 / k) := by ring
    have e2 : 77 / 100 * (k : ℝ) * (1 / (k : ℝ) ^ 2) = 77 / 100 * (1 / k) := by
      rw [e1, ← mul_assoc, mul_assoc (77 / 100 : ℝ), hu, mul_one]
    have e3 : (3 : ℝ) / k = 3 * (1 / k) := by ring
    rw [e2, e1, e3]
    nlinarith
  have hstep : ∀ t, t < T → X.E t + N * δ ≤ X.E (t + 1) := by
    intro t ht
    have h1 := X.E_succ t
    have h2 := X.B_le t
    have ht' : (t : ℝ) ≤ 2 / 21 * (k : ℝ) ^ 2 * Real.log k := by
      have : t ≤ ⌊(2 / 21 : ℝ) * k ^ 2 * Real.log k⌋₊ := by omega
      exact le_trans (Nat.cast_le.2 this) (Nat.floor_le (by positivity))
    have h3 := B_num X.hk t hL hLk ht'
    have h4 := X.G.card
    have hB : X.B t * k ≤ N := by
      have := mul_le_mul_of_nonneg_right h2 hkpos.le
      nlinarith
    have hB' : X.B t ≤ N * (1 / k) := by
      rw [mul_one_div, le_div_iff₀ hkpos]; exact hB
    have := mul_le_mul_of_nonneg_left hK hNpos.le
    rw [← hN] at h1
    nlinarith
  have hind : ∀ t, t ≤ T → X.E 0 + t * (N * δ) ≤ X.E t := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have := ih (by omega)
      have := hstep t (by omega)
      push_cast
      linarith
  have hET := hind T le_rfl
  have hE0 := X.E_zero
  rw [← hN] at hE0
  -- the distribution
  let P : List (Cfg k) →₀ ℝ := ∑ σ ∈ X.G.Q, ∑ D : Fin T → Fin k × Fin k,
    Finsupp.single (X.S T D) (pw T σ D / N)
  have hPsum : ∀ g : List (Cfg k) → ℝ → ℝ, (∀ ρ, g ρ 0 = 0) →
      (∀ ρ x y, g ρ (x + y) = g ρ x + g ρ y) →
      P.sum g = ∑ σ ∈ X.G.Q, ∑ D : Fin T → Fin k × Fin k, g (X.S T D) (pw T σ D / N) := by
    intro g h0 hadd
    simp only [P]
    rw [← Finsupp.sum_finsetSum_index h0 hadd]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Finsupp.sum_finsetSum_index h0 hadd]
    exact Finset.sum_congr rfl fun D _ => Finsupp.sum_single_index (h0 _)
  have hPapp : ∀ ρ', P ρ' = ∑ σ ∈ X.G.Q, ∑ D : Fin T → Fin k × Fin k,
      (if X.S T D = ρ' then pw T σ D / N else 0) := by
    intro ρ'
    simp only [P, Finsupp.finsetSum_apply, Finsupp.single_apply]
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro ρ'
    rw [hPapp]
    exact Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun D _ => by
      split_ifs
      · exact div_nonneg (pw_nonneg X.hk T σ D) hNpos.le
      · exact le_rfl
  · rw [hPsum (fun _ x => x) (fun _ => rfl) (fun _ _ _ => rfl)]
    simp only [← Finset.sum_div, sum_pw X.hk]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, ← hN, div_self hNpos.ne']
  · intro ρ' hρ'
    rw [Finsupp.mem_support_iff, hPapp] at hρ'
    by_contra hno
    apply hρ'
    refine Finset.sum_eq_zero fun σ hσ => Finset.sum_eq_zero fun D _ => ?_
    split_ifs with hS
    · by_contra hw
      have hpw : pw T σ D ≠ 0 := fun h => hw (by rw [h, zero_div])
      exact hno ⟨σ, hS ▸ X.serves_S D σ hσ (pw_ne_zero hpw)⟩
    · rfl
  · rw [hPsum (fun ρ' x => x * ecost X.A X.a (X.ρ0 ++ ρ')) (fun _ => zero_mul _)
      (fun _ _ _ => add_mul _ _ _)]
    have hEq : ∑ σ ∈ X.G.Q, ∑ D : Fin T → Fin k × Fin k,
        pw T σ D / N * ecost X.A X.a (X.ρ0 ++ X.S T D) = X.E T / N := by
      unfold E
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun D _ => by ring
    rw [hEq, le_div_iff₀ hNpos]
    have hTge : (2 / 21 : ℝ) * k ^ 2 * Real.log k ≤ T := by
      rw [hT]; push_cast
      exact (Nat.lt_floor_add_one _).le
    have hδ' : (21 / 40 : ℝ) ≤ δ := by
      rw [hδ]
      have : (3 : ℝ) / k ≤ 3 / 1001 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkR
      linarith
    have hL0 : 0 ≤ (k : ℝ) ^ 2 * Real.log k := by positivity
    have h1 : (k : ℝ) ^ 2 * Real.log k / 20 ≤ T * δ := by
      have := mul_le_mul hTge hδ' (by norm_num) (by positivity)
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hNpos.le
    nlinarith

end Setup
end GeneralizedUniformServer.Dev.LB.PartA3
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA3
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
open Classical
variable {k : ℕ}
theorem one_phase : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (G : GoodSet k) (a : Cfg k)
    (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Cfg k)), IsServing Serves A →
    ∀ γ c : ℝ, Compet A a γ c → ∀ ρ0 : List (Cfg k),
      ∃ P : List (Cfg k) →₀ ℝ, (∀ ρ', 0 ≤ P ρ') ∧ (P.sum fun _ x => x) = 1 ∧
        (∀ ρ' ∈ P.support, ∃ q, ∀ r ∈ ρ', Serves q r) ∧
        ecost A a ρ0 + (k : ℝ) ^ 2 * Real.log k / 20 ≤
          P.sum fun ρ' x => x * ecost A a (ρ0 ++ ρ') := by
  refine ⟨⌈Real.exp 1000⌉₊, fun k hk0 G a A hA γ c hC ρ0 => ?_⟩
  have hke : Real.exp 1000 ≤ k := Nat.ceil_le.1 hk0
  have hexp : (1001 : ℝ) ≤ Real.exp 1000 := by
    have := Real.add_one_le_exp (1000 : ℝ); linarith
  have hkR : (1001 : ℝ) ≤ k := le_trans hexp hke
  have hk2 : 2 ≤ k := by exact_mod_cast (show (2 : ℝ) ≤ k by linarith)
  have hkpos : (0 : ℝ) < k := by linarith
  have hL : 1000 ≤ Real.log k := by rw [Real.le_log_iff_exp_le hkpos]; exact hke
  exact Setup.main ⟨G, a, A, hA, γ, c, hC, ρ0, hk2, 1 / (k : ℝ) ^ 2, by positivity⟩ hkR hL rfl

end GeneralizedUniformServer.Dev.LB.PartA3
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias one_phase := GeneralizedUniformServer.Dev.LB.PartA3.one_phase

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA4
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
/-!
# Part A4: Theorem 1.2 (paper p. 16)

From `exists_good` and `goodSet_of_good` we get a `GoodSet`. Each phase (`one_phase`) is a finitely
supported distribution of request lists, each served by one configuration, with expected `ecost`
gain `≥ k² ln k / 20`; averaging gives one outcome with that gain, whose `optCost` grows by at most
`k` (`opt_append`). By induction on `L` there is `ρ` with `ecost ρ ≥ L k² ln k / 20` and
`optCost ρ ≤ L k` (`opt_nil` at the start). With `Compet`: `L k² ln k/20 ≤ max(γ,0) L k + c` for all
`L`, so `γ ≥ k ln k / 20`.
-/
/-- Averaging: a probability vector with expectation `≥ X` has a support point with value `≥ X`. -/
lemma exists_ge_of_avg {α : Type*} (P : α →₀ ℝ) (hP0 : ∀ x, 0 ≤ P x)
    (hP1 : (P.sum fun _ x => x) = 1) (f : α → ℝ) (X : ℝ)
    (hX : X ≤ P.sum fun x p => p * f x) : ∃ x ∈ P.support, X ≤ f x := by
  by_contra hno
  have hlt : ∀ x ∈ P.support, f x < X := fun x hx => lt_of_not_ge fun h => hno ⟨x, hx, h⟩
  have hne : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    unfold Finsupp.sum at hP1
    rw [h, Finset.sum_empty] at hP1
    exact zero_ne_one hP1
  have h1 : (P.sum fun x p => p * f x) < P.sum fun _ p => p * X := by
    unfold Finsupp.sum
    refine Finset.sum_lt_sum_of_nonempty hne fun x hx => ?_
    have hpos : 0 < P x := lt_of_le_of_ne (hP0 x) (Ne.symm (Finsupp.mem_support_iff.mp hx))
    exact mul_lt_mul_of_pos_left (hlt x hx) hpos
  have h2 : (P.sum fun _ p => p * X) = X := by
    unfold Finsupp.sum at hP1 ⊢
    rw [← Finset.sum_mul, hP1, one_mul]
  linarith

end GeneralizedUniformServer.Dev.LB.PartA4
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCA
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset Equiv
open Classical
variable {k : ℕ}
/-!
# Part CA, basic counts of permutations and families
-/
/-- Fibres of `σ ↦ σ a` inside a set closed under left multiplication by a swap. -/
lemma card_fib_swap (s : Finset (Perm (Fin k))) (a b b' : Fin k)
    (hs : ∀ σ ∈ s, swap b b' * σ ∈ s) :
    (s.filter fun σ => σ a = b).card = (s.filter fun σ => σ a = b').card := by
  refine Finset.card_bij' (fun σ _ => swap b b' * σ) (fun σ _ => swap b b' * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [mem_filter] at hσ ⊢
    refine ⟨hs σ hσ.1, ?_⟩
    simp [Perm.mul_apply, hσ.2]
  · intro σ hσ
    rw [mem_filter] at hσ ⊢
    refine ⟨hs σ hσ.1, ?_⟩
    simp [Perm.mul_apply, hσ.2]
  · intro σ _; simp [← mul_assoc]
  · intro σ _; simp [← mul_assoc]

/-- `k · #{σ : σ a = b} = k!`. -/
lemma card_one (a b : Fin k) :
    k * (univ.filter fun σ : Perm (Fin k) => σ a = b).card = k.factorial := by
  have h1 : (univ : Finset (Perm (Fin k))).card =
      ∑ c ∈ (univ : Finset (Fin k)), ((univ : Finset (Perm (Fin k))).filter fun σ => σ a = c).card :=
    card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin k) => σ a) (by intro _ _; simp)
  have h2 : ∀ c : Fin k, ((univ : Finset (Perm (Fin k))).filter fun σ => σ a = c).card =
      (univ.filter fun σ : Perm (Fin k) => σ a = b).card := fun c =>
    card_fib_swap _ a c b (by intro _ _; simp)
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  rw [h1, Finset.sum_congr rfl (fun c _ => h2 c), sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul]

lemma card_one_real (a b : Fin k) :
    ((univ.filter fun σ : Perm (Fin k) => σ a = b).card : ℝ) = (k.factorial : ℝ) / k := by
  have hk : (k : ℝ) ≠ 0 := by
    have := a.pos; positivity
  rw [eq_div_iff hk, mul_comm]
  exact_mod_cast card_one a b

/-- `(k-1) · #{σ : σ a = b, σ a' = b'} = #{σ : σ a = b}` for `a ≠ a'`, `b ≠ b'`. -/
lemma card_two (a a' b b' : Fin k) (ha : a ≠ a') (hb : b ≠ b') :
    (k - 1) * (univ.filter fun σ : Perm (Fin k) => σ a = b ∧ σ a' = b').card =
      (univ.filter fun σ : Perm (Fin k) => σ a = b).card := by
  set s := univ.filter fun σ : Perm (Fin k) => σ a = b with hs
  have h1 : s.card = ∑ c ∈ (univ.erase b), (s.filter fun σ => σ a' = c).card := by
    refine card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin k) => σ a') ?_
    intro σ hσ
    simp only [hs, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ
    simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    intro h; rw [← hσ] at h; exact ha (σ.injective h).symm
  have h2 : ∀ c ∈ univ.erase b, (s.filter fun σ => σ a' = c).card =
      (s.filter fun σ => σ a' = b').card := by
    intro c hc
    refine card_fib_swap _ a' c b' ?_
    intro σ hσ
    simp only [hs, mem_filter, mem_univ, true_and] at hσ ⊢
    have hc' : b ≠ c := fun h => by simp [h] at hc
    rw [Perm.mul_apply, hσ, swap_apply_of_ne_of_ne hc' hb]
  rw [Finset.sum_congr rfl h2, sum_const, card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin, smul_eq_mul, hs, filter_filter] at h1
  exact h1.symm

lemma card_two_real (hk : 2 ≤ k) (a a' b b' : Fin k) (ha : a ≠ a') (hb : b ≠ b') :
    ((univ.filter fun σ : Perm (Fin k) => σ a = b ∧ σ a' = b').card : ℝ) =
      (k.factorial : ℝ) / k / ((k : ℝ) - 1) := by
  have hk1 : ((k : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [← card_one_real a b, eq_div_iff hk1, mul_comm]
  have := card_two a a' b b' ha hb
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [← hc]; exact_mod_cast this

/-- Counting families coordinatewise. -/
lemma card_fam_pi (P : Fin k → Perm (Fin k) → Prop) [∀ i, DecidablePred (P i)] :
    (univ.filter fun π : Fam k => ∀ i, P i (π i)).card =
      ∏ i, (univ.filter fun σ : Perm (Fin k) => P i σ).card := by
  rw [← Fintype.card_piFinset]
  congr 1
  ext π
  simp [Fintype.mem_piFinset]

/-- Counting systems coordinatewise. -/
lemma card_sys_pi (h : ℕ) (Q : Fam k → Prop) [DecidablePred Q] :
    (univ.filter fun F : Sys k h => ∀ j, Q (F j)).card =
      (univ.filter fun π : Fam k => Q π).card ^ h := by
  have : (univ.filter fun F : Sys k h => ∀ j, Q (F j)) =
      Fintype.piFinset (fun _ : Fin h => univ.filter fun π : Fam k => Q π) := by
    ext F; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]

lemma card_sys (h : ℕ) : Fintype.card (Sys k h) = (k.factorial ^ k) ^ h := by
  simp [Sys, Fam, Fintype.card_perm]

/-- One fibre of `π ↦ π(x)`. -/
lemma card_fibre (x v : Cfg k) :
    ((univ.filter fun π : Fam k => app π x = v).card : ℝ) = ((k.factorial : ℝ) / k) ^ k := by
  have : (univ.filter fun π : Fam k => app π x = v) =
      (univ.filter fun π : Fam k => ∀ i, π i (x i) = v i) := by
    ext π; simp [app, funext_iff]
  rw [this, card_fam_pi (fun i σ => σ (x i) = v i)]
  push_cast
  simp_rw [card_one_real]
  simp [div_pow]

/-- The number of permutations in `Cfg k`. -/
lemma card_perms : (univ.filter fun v : Cfg k => IsPerm v).card = k.factorial := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (show {x : Cfg k // IsPerm x} ≃ (Fin k ↪ Fin k) from
      Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin k)),
    Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  exact Nat.descFactorial_self k

/-- The number of families accepting a configuration. -/
lemma card_acc_fam (x : Cfg k) :
    ((univ.filter fun π : Fam k => IsPerm (app π x)).card : ℝ) =
      (k.factorial : ℝ) * ((k.factorial : ℝ) / k) ^ k := by
  set s := univ.filter fun π : Fam k => IsPerm (app π x)
  have h1 : s.card = ∑ v ∈ univ.filter (fun v : Cfg k => IsPerm v),
      (s.filter fun π => app π x = v).card :=
    card_eq_sum_card_fiberwise (f := fun π : Fam k => app π x) (by
      intro π hπ; simpa [s] using hπ)
  have h2 : ∀ v ∈ univ.filter (fun v : Cfg k => IsPerm v),
      (s.filter fun π => app π x = v).card = (univ.filter fun π : Fam k => app π x = v).card := by
    intro v hv
    congr 1
    ext π
    simp only [s, mem_filter, mem_univ, true_and] at hv ⊢
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hv, h⟩
  rw [h1, Finset.sum_congr rfl h2]
  push_cast
  simp_rw [card_fibre]
  rw [sum_const, card_perms, nsmul_eq_mul]

end GeneralizedUniformServer.Dev.LB.PartCA
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCA
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}
/-!
# Part CA: exact counts (Lemmas 4.2–4.5, 4.8)
-/
open Classical in
lemma acc_eq (h : ℕ) (x : Cfg k) (hx : IsPerm x) :
    ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) =
      ((k.factorial : ℝ) * ((k.factorial : ℝ) / k) ^ k) ^ h := by
  have e : (univ.filter fun F : Sys k h => x ∈ Qset F) =
      univ.filter fun F : Sys k h => ∀ j, IsPerm (app (F j) x) := by
    ext F; simp [Qset, hx]
  rw [e, card_sys_pi h (fun π => IsPerm (app π x))]
  push_cast
  rw [card_acc_fam]

open Classical in
/-- **CA2**: a fixed permutation is in `Q(F)` for a `p^h` fraction of systems. -/
theorem card_acc (h : ℕ) (x : Cfg k) (hx : IsPerm x) :
    ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) =
      (Fintype.card (Sys k h) : ℝ) * ((k.factorial : ℝ) / (k : ℝ) ^ k) ^ h := by
  rw [acc_eq h x hx, card_sys]
  push_cast
  rw [← pow_mul, pow_mul, ← mul_pow, div_pow]
  congr 1
  ring

open Classical in
lemma sum_acc (h : ℕ) :
    (∑ x : Cfg k, ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ)) =
      ∑ F : Sys k h, (Z F : ℝ) := by
  have e1 : ∀ x : Cfg k, ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) =
      ∑ F : Sys k h, if x ∈ Qset F then (1 : ℝ) else 0 := by
    intro x; rw [Finset.sum_boole]
  simp_rw [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [Finset.sum_boole]; unfold Z; congr 2; ext x; simp

/-- **CA1** (Lemma 4.2): `∑_F Z(F) = |Sys| · k! · (k!/k^k)^h`. -/
theorem sum_Z (h : ℕ) :
    (∑ F : Sys k h, (Z F : ℝ)) =
      (Fintype.card (Sys k h) : ℝ) * (k.factorial : ℝ) * ((k.factorial : ℝ) / (k : ℝ) ^ k) ^ h := by
  classical
  rw [← sum_acc]
  have e : ∀ x : Cfg k, ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) =
      if IsPerm x then (Fintype.card (Sys k h) : ℝ) * ((k.factorial : ℝ) / (k : ℝ) ^ k) ^ h
      else 0 := by
    intro x
    split_ifs with hx
    · exact card_acc h x hx
    · have : (univ.filter fun F : Sys k h => x ∈ Qset F) = ∅ := by
        ext F; simp [Qset, hx]
      simp [this]
  simp_rw [e]
  rw [← Finset.sum_filter, sum_const, card_perms, nsmul_eq_mul]
  ring

end GeneralizedUniformServer.Dev.LB.PartCA
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias sum_Z := GeneralizedUniformServer.Dev.LB.PartCA.sum_Z

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCA
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset Equiv
open Classical
variable {k : ℕ}
/-!
# Part CA, the falling-factorial bound behind Lemma 4.8

`S(B) = {σ : σ a = c, σ(B) ⊆ T}` with `c ∉ T`, `a ∉ B`:
`#S(B) (k-1)^{|B|} ≤ #S(∅) |T|^{|B|}`.
-/
/-- `S(B)`. -/
def Sset (a c : Fin k) (T B : Finset (Fin k)) : Finset (Perm (Fin k)) :=
  univ.filter fun σ => σ a = c ∧ ∀ b ∈ B, σ b ∈ T

lemma swap_fix {σ : Perm (Fin k)} {b b' e : Fin k} {B : Finset (Fin k)} (hb : b ∉ B)
    (he : e ∉ B.image σ) (hb' : b' ∈ B) : swap (σ b) e (σ b') = σ b' := by
  refine swap_apply_of_ne_of_ne ?_ ?_
  · intro h; exact hb (σ.injective h ▸ hb')
  · intro h; exact he (mem_image.2 ⟨b', hb', h⟩)

lemma not_mem_img {σ : Perm (Fin k)} {b e : Fin k} {B : Finset (Fin k)} (hb : b ∉ B)
    (he : e ∉ B.image σ) : σ b ∉ B.image (swap (σ b) e * σ) := by
  intro h
  obtain ⟨b'', hb'', h''⟩ := mem_image.1 h
  rw [Perm.mul_apply, swap_fix hb he hb''] at h''
  exact hb (σ.injective h'' ▸ hb'')

lemma card_filter_prod {α β : Type*} (s : Finset α) (t : Finset β) (p : α × β → Prop)
    [DecidablePred p] :
    ((s ×ˢ t).filter p).card = ∑ a ∈ s, (t.filter fun b => p (a, b)).card := by
  rw [card_filter, sum_product]
  simp_rw [card_filter]

lemma mem_Sset {a c : Fin k} {T B : Finset (Fin k)} {σ : Perm (Fin k)} :
    σ ∈ Sset a c T B ↔ σ a = c ∧ ∀ b ∈ B, σ b ∈ T := by
  simp [Sset]

/-- The exchange step: `#S(B ∪ {b}) (k-1-|B|) = #S(B) (|T| - |B|)`. -/
lemma Sset_step (a b c : Fin k) (T B : Finset (Fin k)) (hcT : c ∉ T) (haB : a ∉ B)
    (hbB : b ∉ B) (hab : b ≠ a) :
    (Sset a c T (insert b B)).card * (k - 1 - B.card) =
      (Sset a c T B).card * (T.card - B.card) := by
  set X := (Sset a c T B ×ˢ T).filter fun p => p.2 ∉ B.image p.1 with hX
  set Y := (Sset a c T (insert b B) ×ˢ univ).filter
    fun p => p.2 ≠ c ∧ p.2 ∉ B.image p.1 with hY
  have hXc : X.card = (Sset a c T B).card * (T.card - B.card) := by
    rw [hX, card_filter_prod, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun σ hσ => ?_
    rw [mem_Sset] at hσ
    have hsub : B.image σ ⊆ T := by
      intro z hz; obtain ⟨b', hb', rfl⟩ := mem_image.1 hz; exact hσ.2 b' hb'
    have e : (T.filter fun z => (σ, z).2 ∉ B.image (σ, z).1) = T \ B.image σ := by
      ext z; simp
    rw [e, card_sdiff_of_subset hsub, card_image_of_injective _ σ.injective]
  have hYc : Y.card = (Sset a c T (insert b B)).card * (k - 1 - B.card) := by
    rw [hY, card_filter_prod, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun σ hσ => ?_
    rw [mem_Sset] at hσ
    have hc : c ∉ B.image σ := by
      intro hz; obtain ⟨b', hb', hb'c⟩ := mem_image.1 hz
      rw [← hσ.1] at hb'c; exact haB (σ.injective hb'c ▸ hb')
    have e : (univ.filter fun z => (σ, z).2 ≠ c ∧ (σ, z).2 ∉ B.image (σ, z).1) =
        univ \ insert c (B.image σ) := by
      ext z; simp
    rw [e, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
      card_insert_of_notMem hc, card_image_of_injective _ σ.injective]
    omega
  rw [← hXc, ← hYc]
  symm
  refine Finset.card_bij' (fun p _ => (swap (p.1 b) p.2 * p.1, p.1 b))
    (fun p _ => (swap (p.1 b) p.2 * p.1, p.1 b)) ?_ ?_ ?_ ?_
  · rintro ⟨σ, e⟩ hp
    simp only [hX, mem_filter, mem_product, mem_Sset] at hp
    obtain ⟨⟨⟨hσa, hσB⟩, heT⟩, heB⟩ := hp
    have hcb : c ≠ σ b := fun h => hab (σ.injective (h.symm.trans hσa.symm))
    have hce : c ≠ e := fun h => hcT (h ▸ heT)
    simp only [hY, mem_filter, mem_product, mem_Sset, mem_univ, and_true]
    refine ⟨⟨?_, ?_⟩, ?_, not_mem_img hbB heB⟩
    · rw [Perm.mul_apply, hσa, swap_apply_of_ne_of_ne hcb hce]
    · intro b' hb'
      rcases mem_insert.1 hb' with rfl | hb'
      · rw [Perm.mul_apply, swap_apply_left]; exact heT
      · rw [Perm.mul_apply, swap_fix hbB heB hb']; exact hσB b' hb'
    · exact fun h => hcb h.symm
  · rintro ⟨σ, e⟩ hp
    simp only [hY, mem_filter, mem_product, mem_Sset, mem_univ, and_true] at hp
    obtain ⟨⟨hσa, hσB⟩, hec, heB⟩ := hp
    have hbT : σ b ∈ T := hσB b (mem_insert_self _ _)
    have hcb : c ≠ σ b := fun h => hcT (h ▸ hbT)
    simp only [hX, mem_filter, mem_product, mem_Sset]
    refine ⟨⟨⟨?_, ?_⟩, hbT⟩, not_mem_img hbB heB⟩
    · rw [Perm.mul_apply, hσa, swap_apply_of_ne_of_ne hcb (Ne.symm hec)]
    · intro b' hb'
      rw [Perm.mul_apply, swap_fix hbB heB hb']; exact hσB b' (mem_insert_of_mem hb')
  · rintro ⟨σ, e⟩ _
    simp [swap_comm e (σ b), ← mul_assoc]
  · rintro ⟨σ, e⟩ _
    simp [swap_comm e (σ b), ← mul_assoc]

lemma sub_mul_le_aux (t n K : ℕ) (h : t ≤ K) : (t - n) * K ≤ t * (K - n) := by
  rcases le_total n t with hnt | hnt
  · obtain ⟨t', rfl⟩ := Nat.exists_eq_add_of_le hnt
    obtain ⟨K', rfl⟩ := Nat.exists_eq_add_of_le (hnt.trans h)
    simp only [Nat.add_sub_cancel_left]
    have : t' ≤ K' := by omega
    nlinarith
  · simp [Nat.sub_eq_zero_of_le hnt]

/-- `#S(B) (k-1)^{|B|} ≤ #S(∅) |T|^{|B|}`. -/
lemma Sset_bound (a c : Fin k) (T : Finset (Fin k)) (hcT : c ∉ T) (B : Finset (Fin k))
    (haB : a ∉ B) :
    (Sset a c T B).card * (k - 1) ^ B.card ≤ (Sset a c T ∅).card * T.card ^ B.card := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hbB ih =>
    have haB' : a ∉ B := fun h => haB (mem_insert_of_mem h)
    have hab : b ≠ a := fun h => haB (h ▸ mem_insert_self _ _)
    have ih := ih haB'
    have step := Sset_step a b c T B hcT haB' hbB hab
    have hcard : B.card + 2 ≤ k := by
      have h1 : (insert a (insert b B)).card ≤ k := by
        simpa using card_le_univ (insert a (insert b B))
      rw [card_insert_of_notMem haB, card_insert_of_notMem hbB] at h1; omega
    have hT : T.card ≤ k - 1 := by
      have h1 : T ⊆ univ.erase c := fun z hz => mem_erase.2 ⟨fun h => hcT (h ▸ hz), mem_univ _⟩
      have h2 := card_le_card h1
      rwa [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h2
    set S' := (Sset a c T (insert b B)).card
    set S := (Sset a c T B).card
    set S0 := (Sset a c T ∅).card
    set n := B.card
    set t := T.card
    have key : S' * (k - 1) ≤ S * t := by
      refine Nat.le_of_mul_le_mul_right (a := S' * (k - 1)) (b := S * t) (c := k - 1 - n) ?_
        (by omega)
      calc S' * (k - 1) * (k - 1 - n) = S' * (k - 1 - n) * (k - 1) := by ring
        _ = S * (t - n) * (k - 1) := by rw [step]
        _ = S * ((t - n) * (k - 1)) := by ring
        _ ≤ S * (t * (k - 1 - n)) := Nat.mul_le_mul_left _ (sub_mul_le_aux t n (k - 1) hT)
        _ = S * t * (k - 1 - n) := by ring
    rw [card_insert_of_notMem hbB, pow_succ, pow_succ]
    calc S' * ((k - 1) ^ n * (k - 1)) = (S' * (k - 1)) * (k - 1) ^ n := by ring
      _ ≤ (S * t) * (k - 1) ^ n := Nat.mul_le_mul_right _ key
      _ = (S * (k - 1) ^ n) * t := by ring
      _ ≤ (S0 * t ^ n) * t := Nat.mul_le_mul_right _ ih
      _ = S0 * (t ^ n * t) := by ring

/-!
# Part CA, the per-family bound behind Lemma 4.8
-/
/-- One coordinate: `#{σ : σ a = c, σ(B) ⊆ U} ≤ (k!/k) ((|U|-1)/(k-1))^{|B|}` for `c ∈ U`. -/
lemma coord_bound (hk : 2 ≤ k) (a c : Fin k) (U B : Finset (Fin k)) (hcU : c ∈ U)
    (haB : a ∉ B) :
    ((univ.filter fun σ : Perm (Fin k) => σ a = c ∧ ∀ b ∈ B, σ b ∈ U).card : ℝ) ≤
      (k.factorial : ℝ) / k * (((U.card : ℝ) - 1) / ((k : ℝ) - 1)) ^ B.card := by
  have e : (univ.filter fun σ : Perm (Fin k) => σ a = c ∧ ∀ b ∈ B, σ b ∈ U) =
      Sset a c (U.erase c) B := by
    ext σ
    simp only [Sset, mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun b hb => ⟨fun h => ?_, h2 b hb⟩⟩
      rw [← h1] at h; exact haB (σ.injective h ▸ hb)
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun b hb => (h2 b hb).2⟩
  have e0 : (Sset a c (U.erase c) ∅).card = (univ.filter fun σ : Perm (Fin k) => σ a = c).card := by
    congr 1; ext σ; simp [Sset]
  have hb := Sset_bound a c (U.erase c) (notMem_erase c U) B haB
  rw [e0, card_erase_of_mem hcU] at hb
  have hU : 1 ≤ U.card := card_pos.2 ⟨c, hcU⟩
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hbR : ((Sset a c (U.erase c) B).card : ℝ) * ((k : ℝ) - 1) ^ B.card ≤
      ((univ.filter fun σ : Perm (Fin k) => σ a = c).card : ℝ) * ((U.card : ℝ) - 1) ^ B.card := by
    have := (Nat.cast_le (α := ℝ)).2 hb
    push_cast [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub hU] at this
    exact this
  rw [card_one_real] at hbR
  rw [e, div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hk1 _)]
  exact hbR

/-- `∑_i #{b : (i,b) ∈ P} = |P|`. -/
lemma sum_card_slices (P : Finset (Fin k × Fin k)) :
    ∑ i, (univ.filter fun b => (i, b) ∈ P).card = P.card := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (by intro _ _; simp)]
  refine sum_congr rfl fun i _ => ?_
  refine Finset.card_bij' (fun b _ => (i, b)) (fun p _ => p.2) ?_ ?_ ?_ ?_
  · intro b hb; simp only [mem_filter, mem_univ, true_and] at hb; simp [hb]
  · intro p hp; simp only [mem_filter] at hp; obtain ⟨hp, rfl⟩ := hp; simpa using hp
  · intro b _; rfl
  · intro p hp; simp only [mem_filter] at hp; obtain ⟨_, rfl⟩ := hp; rfl

/-- The per-family form of Lemma 4.8(a). -/
lemma fam_lx (hk : 2 ≤ k) (x : Cfg k) (I : Finset (Fin k)) (hI : I.Nonempty)
    (P : Finset (Fin k × Fin k)) (hP : ∀ ib ∈ P, ib.1 ∈ I ∧ ib.2 ≠ x ib.1) :
    ((univ.filter fun π : Fam k =>
        IsPerm (app π x) ∧ ∀ ib ∈ P, π ib.1 ib.2 ∈ I.image (app π x)).card : ℝ) ≤
      ((univ.filter fun π : Fam k => IsPerm (app π x)).card : ℝ) *
        (((I.card : ℝ) - 1) / ((k : ℝ) - 1)) ^ P.card := by
  set r : ℝ := ((I.card : ℝ) - 1) / ((k : ℝ) - 1) with hr
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hr0 : 0 ≤ r := by
    have h1 : (1 : ℝ) ≤ I.card := by exact_mod_cast hI.card_pos
    exact div_nonneg (by linarith) hk1.le
  set s := univ.filter fun π : Fam k =>
    IsPerm (app π x) ∧ ∀ ib ∈ P, π ib.1 ib.2 ∈ I.image (app π x) with hs
  set Pm := univ.filter fun v : Cfg k => IsPerm v with hPm
  set Pi : Fin k → Finset (Fin k) := fun i => univ.filter fun b => (i, b) ∈ P with hPi
  have h1 : s.card = ∑ v ∈ Pm, (s.filter fun π => app π x = v).card :=
    card_eq_sum_card_fiberwise (f := fun π : Fam k => app π x) (by
      intro π hπ
      simp only [hs, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ
      simp [hPm, hπ.1])
  have h2 : ∀ v ∈ Pm, ((s.filter fun π => app π x = v).card : ℝ) ≤
      ((k.factorial : ℝ) / k) ^ k * r ^ P.card := by
    intro v hv
    simp only [hPm, mem_filter, mem_univ, true_and] at hv
    have e : (s.filter fun π => app π x = v) =
        univ.filter fun π : Fam k => ∀ i, π i (x i) = v i ∧ ∀ b ∈ Pi i, π i b ∈ I.image v := by
      ext π
      simp only [hs, hPi, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, h2⟩, rfl⟩ i
        exact ⟨rfl, fun b hb => h2 (i, b) hb⟩
      · intro h
        have hv' : app π x = v := funext fun i => (h i).1
        subst hv'
        exact ⟨⟨hv, fun ib hib => (h ib.1).2 ib.2 hib⟩, rfl⟩
    rw [e, card_fam_pi (fun i σ => σ (x i) = v i ∧ ∀ b ∈ Pi i, σ b ∈ I.image v)]
    push_cast
    calc (∏ i, ((univ.filter fun σ : Perm (Fin k) =>
            σ (x i) = v i ∧ ∀ b ∈ Pi i, σ b ∈ I.image v).card : ℝ))
        ≤ ∏ i, ((k.factorial : ℝ) / k * r ^ (Pi i).card) := by
          refine prod_le_prod (fun _ _ => by positivity) fun i _ => ?_
          by_cases hPe : Pi i = ∅
          · have e' : (univ.filter fun σ : Perm (Fin k) =>
                σ (x i) = v i ∧ ∀ b ∈ Pi i, σ b ∈ I.image v) =
                univ.filter fun σ : Perm (Fin k) => σ (x i) = v i := by
              ext σ; simp [hPe]
            rw [e', card_one_real, hPe, card_empty, pow_zero, mul_one]
          · obtain ⟨b, hb⟩ := nonempty_iff_ne_empty.2 hPe
            simp only [hPi, mem_filter, mem_univ, true_and] at hb
            have hi : i ∈ I := (hP _ hb).1
            have hxi : x i ∉ Pi i := by
              intro h
              simp only [hPi, mem_filter, mem_univ, true_and] at h
              exact (hP _ h).2 rfl
            have := coord_bound hk (x i) (v i) (I.image v) (Pi i) (mem_image_of_mem v hi) hxi
            rwa [card_image_of_injective _ hv] at this
      _ = ((k.factorial : ℝ) / k) ^ k * r ^ P.card := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum,
            hPi, sum_card_slices]
  rw [h1]
  push_cast
  calc (∑ v ∈ Pm, ((s.filter fun π => app π x = v).card : ℝ))
      ≤ ∑ v ∈ Pm, ((k.factorial : ℝ) / k) ^ k * r ^ P.card := sum_le_sum h2
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, hPm, card_perms, card_acc_fam]
      ring

/-!
# Part CA, pair counts (Lemmas 4.4–4.5)
-/
/-- Permutations agreeing with `v` exactly off `J`: `D_{|J|}` of them. -/
lemma card_der (v : Cfg k) (hv : IsPerm v) (J : Finset (Fin k)) :
    (univ.filter fun w : Cfg k => IsPerm w ∧ ∀ i, (w i = v i ↔ i ∉ J)).card =
      numDerangements J.card := by
  have h1 : Fintype.card {f : Perm (Fin k) // ∀ a, ¬ (a ∈ J) ↔ a ∈ Function.fixedPoints f} =
      numDerangements J.card := by
    rw [← Fintype.card_congr (derangements.subtypeEquiv (fun a : Fin k => a ∈ J)),
      card_derangements_eq_numDerangements]
    simp
  rw [← h1, Fintype.card_subtype]
  have hvb : Function.Bijective v := Finite.injective_iff_bijective.mp hv
  set V := Equiv.ofBijective v hvb
  symm
  refine Finset.card_bij (fun ρ _ => fun i => v (ρ i)) ?_ ?_ ?_
  · intro ρ hρ
    simp only [mem_filter, mem_univ, true_and, Function.mem_fixedPoints,
      Function.IsFixedPt] at hρ ⊢
    refine ⟨hv.comp ρ.injective, fun i => ?_⟩
    rw [hv.eq_iff, hρ i]
  · intro ρ₁ _ ρ₂ _ h
    ext i
    have := congrFun h i
    simp only at this
    rw [hv this]
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    have hwb : Function.Bijective w := Finite.injective_iff_bijective.mp hw.1
    refine ⟨(Equiv.ofBijective w hwb).trans V.symm, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and, Function.mem_fixedPoints,
        Function.IsFixedPt]
      intro i
      rw [← hw.2 i]
      simp only [Equiv.trans_apply, Equiv.ofBijective_apply]
      rw [Equiv.symm_apply_eq]
      simp [V, eq_comm]
    · funext i
      exact V.apply_symm_apply (w i)

/-- The coordinate count for two prescribed values. -/
lemma card_pair_real (hk : 2 ≤ k) (a a' b b' : Fin k) :
    ((univ.filter fun σ : Perm (Fin k) => σ a = b ∧ σ a' = b').card : ℝ) =
      if (b' = b ↔ a' = a) then
        (if a' = a then (k.factorial : ℝ) / k else (k.factorial : ℝ) / k / ((k : ℝ) - 1))
      else 0 := by
  by_cases ha : a' = a
  · subst ha
    by_cases hb : b' = b
    · subst hb; simp [card_one_real]
    · have : (univ.filter fun σ : Perm (Fin k) => σ a' = b ∧ σ a' = b') = ∅ := by
        ext σ; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨h1, h2⟩; exact hb (h2.symm.trans h1)
      simp [this, hb]
  · by_cases hb : b' = b
    · have : (univ.filter fun σ : Perm (Fin k) => σ a = b ∧ σ a' = b') = ∅ := by
        ext σ; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨h1, h2⟩; exact ha (σ.injective (h2.trans (hb.trans h1.symm)))
      rw [this, card_empty]; simp [hb, ha]
    · simp only [hb, ha, iff_self, if_true, if_false]
      exact card_two_real hk a a' b b' (Ne.symm ha) (Ne.symm hb)

/-- `A(x, y) = k! D_d (k!/k)^k (k-1)^{-d}` with `d = hd x y`. -/
lemma card_acc2 (hk : 2 ≤ k) (x y : Cfg k) :
    ((univ.filter fun π : Fam k => IsPerm (app π x) ∧ IsPerm (app π y)).card : ℝ) =
      (k.factorial : ℝ) * numDerangements (hd x y) * ((k.factorial : ℝ) / k) ^ k *
        (((k : ℝ) - 1)⁻¹) ^ (hd x y) := by
  set J := univ.filter fun i => x i ≠ y i with hJ
  have hdJ : hd x y = J.card := rfl
  set C : ℝ := ((k.factorial : ℝ) / k) ^ k * (((k : ℝ) - 1)⁻¹) ^ J.card with hC
  set s := univ.filter fun π : Fam k => IsPerm (app π x) ∧ IsPerm (app π y)
  set Pm := univ.filter fun v : Cfg k => IsPerm v
  have h1 : s.card = ∑ p ∈ Pm ×ˢ Pm, (s.filter fun π => (app π x, app π y) = p).card :=
    card_eq_sum_card_fiberwise (f := fun π : Fam k => (app π x, app π y)) (by
      intro π hπ; simp only [s, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ
      simp [Pm, hπ.1, hπ.2])
  have h2 : ∀ p ∈ Pm ×ˢ Pm, ((s.filter fun π => (app π x, app π y) = p).card : ℝ) =
      if ∀ i, (p.2 i = p.1 i ↔ i ∉ J) then C else 0 := by
    intro p hp
    simp only [Pm, mem_product, mem_filter, mem_univ, true_and] at hp
    have e : (s.filter fun π => (app π x, app π y) = p) =
        univ.filter fun π : Fam k => ∀ i, π i (x i) = p.1 i ∧ π i (y i) = p.2 i := by
      ext π
      simp only [s, mem_filter, mem_univ, true_and, Prod.ext_iff, app, funext_iff]
      constructor
      · rintro ⟨_, h1, h2⟩ i; exact ⟨h1 i, h2 i⟩
      · intro h
        refine ⟨⟨?_, ?_⟩, fun i => (h i).1, fun i => (h i).2⟩
        · have : (fun i => π i (x i)) = p.1 := funext fun i => (h i).1
          unfold IsPerm; rw [show (app π x) = p.1 from this]; exact hp.1
        · have : (fun i => π i (y i)) = p.2 := funext fun i => (h i).2
          unfold IsPerm; rw [show (app π y) = p.2 from this]; exact hp.2
    rw [e, card_fam_pi (fun i σ => σ (x i) = p.1 i ∧ σ (y i) = p.2 i)]
    push_cast
    simp_rw [card_pair_real hk]
    rw [Finset.prod_ite_zero]
    have hiff : (∀ i ∈ (univ : Finset (Fin k)), (p.2 i = p.1 i ↔ y i = x i)) ↔
        ∀ i, (p.2 i = p.1 i ↔ i ∉ J) := by
      simp [hJ, eq_comm]
    by_cases hh : ∀ i, (p.2 i = p.1 i ↔ i ∉ J)
    · rw [if_pos (hiff.mpr hh), if_pos hh, hC]
      have : ∀ i, (if y i = x i then (k.factorial : ℝ) / k else (k.factorial : ℝ) / k / ((k : ℝ) - 1))
          = (k.factorial : ℝ) / k * (if i ∈ J then ((k : ℝ) - 1)⁻¹ else 1) := by
        intro i
        by_cases hi : y i = x i
        · simp [hJ, hi]
        · simp [hJ, hi, Ne.symm hi, div_eq_mul_inv]
      simp_rw [this]
      rw [Finset.prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, Finset.prod_ite_mem,
        univ_inter, prod_const]
    · rw [if_neg (fun h => hh (hiff.mp h)), if_neg hh]
  rw [h1]
  push_cast
  rw [Finset.sum_congr rfl h2, Finset.sum_product]
  have h3 : ∀ v ∈ Pm, (∑ w ∈ Pm, if ∀ i, ((v, w).2 i = (v, w).1 i ↔ i ∉ J) then C else 0) =
      (numDerangements J.card : ℝ) * C := by
    intro v hv
    simp only [Pm, mem_filter, mem_univ, true_and] at hv
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, filter_filter, card_der v hv J]
  rw [Finset.sum_congr rfl h3, sum_const, nsmul_eq_mul, card_perms, hC, hdJ]
  ring

end GeneralizedUniformServer.Dev.LB.PartCA
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCA
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}
open Classical in
lemma pair_count (hk : 2 ≤ k) (h d : ℕ) (x y : Cfg k) :
    ((univ.filter fun F : Sys k h => x ∈ Qset F ∧ y ∈ Qset F ∧ hd x y = d).card : ℝ) =
      if IsPerm x ∧ (IsPerm y ∧ hd x y = d) then
        ((k.factorial : ℝ) * numDerangements d * ((k.factorial : ℝ) / k) ^ k *
          (((k : ℝ) - 1)⁻¹) ^ d) ^ h
      else 0 := by
  split_ifs with hxy
  · obtain ⟨hx, hy, hd'⟩ := hxy
    have e : (univ.filter fun F : Sys k h => x ∈ Qset F ∧ y ∈ Qset F ∧ hd x y = d) =
        univ.filter fun F : Sys k h => ∀ j, IsPerm (app (F j) x) ∧ IsPerm (app (F j) y) := by
      ext F; simp [Qset, hx, hy, hd', forall_and]
    rw [e, card_sys_pi h (fun π => IsPerm (app π x) ∧ IsPerm (app π y))]
    push_cast
    rw [card_acc2 hk, hd']
  · have e : (univ.filter fun F : Sys k h => x ∈ Qset F ∧ y ∈ Qset F ∧ hd x y = d) = ∅ := by
      ext F
      simp only [Qset, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨⟨hx, _⟩, ⟨hy, _⟩, hd'⟩
      exact hxy ⟨hx, hy, hd'⟩
    simp [e]

end GeneralizedUniformServer.Dev.LB.PartCA
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCA
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset Equiv
open Classical
variable {k : ℕ}
/-- `#{y : perm, hd x y = d} = C(k,d) D_d`. -/
lemma card_dist (x : Cfg k) (hx : IsPerm x) (d : ℕ) :
    (univ.filter fun y : Cfg k => IsPerm y ∧ hd x y = d).card =
      k.choose d * numDerangements d := by
  set s := univ.filter fun y : Cfg k => IsPerm y ∧ hd x y = d
  have h1 : s.card = ∑ J ∈ powersetCard d (univ : Finset (Fin k)),
      (s.filter fun y => (univ.filter fun i => x i ≠ y i) = J).card :=
    card_eq_sum_card_fiberwise (f := fun y : Cfg k => univ.filter fun i => x i ≠ y i) (by
      intro y hy
      simp only [s, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
      simp only [mem_coe, mem_powersetCard, subset_univ, true_and]
      exact hy.2)
  have h2 : ∀ J ∈ powersetCard d (univ : Finset (Fin k)),
      (s.filter fun y => (univ.filter fun i => x i ≠ y i) = J).card = numDerangements d := by
    intro J hJ
    rw [mem_powersetCard] at hJ
    rw [← hJ.2, ← card_der x hx J]
    congr 1
    ext y
    simp only [s, mem_filter, mem_univ, true_and, hd]
    constructor
    · rintro ⟨⟨hy, _⟩, rfl⟩
      exact ⟨hy, fun i => by simp [eq_comm]⟩
    · rintro ⟨hy, hJ'⟩
      have e : (univ.filter fun i => x i ≠ y i) = J := by
        ext i
        have := hJ' i
        rw [eq_comm] at this
        simp only [mem_filter, mem_univ, true_and]
        tauto
      exact ⟨⟨hy, by rw [e, hJ.2]⟩, e⟩
  rw [h1, Finset.sum_congr rfl h2, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
    smul_eq_mul]

end GeneralizedUniformServer.Dev.LB.PartCA
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCA
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}
/-- **CA3** (Lemma 4.5): `E₀ Z_d = s_d E₀ Z`. -/
theorem sum_Zd (hk : 2 ≤ k) (h d : ℕ) :
    (∑ F : Sys k h, (Zd F d : ℝ)) = sd k h d * ∑ F : Sys k h, (Z F : ℝ) := by
  classical
  have e1 : ∀ F : Sys k h, (Zd F d : ℝ) =
      ∑ p : Cfg k × Cfg k, if p.1 ∈ Qset F ∧ p.2 ∈ Qset F ∧ hd p.1 p.2 = d then (1 : ℝ) else 0 := by
    intro F
    rw [Finset.sum_boole]
    unfold Zd
    congr 2
    ext p
    simp [and_assoc]
  simp_rw [e1]
  rw [Finset.sum_comm]
  have e2 : ∀ p : Cfg k × Cfg k,
      (∑ F : Sys k h, if p.1 ∈ Qset F ∧ p.2 ∈ Qset F ∧ hd p.1 p.2 = d then (1 : ℝ) else 0) =
      ((univ.filter fun F : Sys k h => p.1 ∈ Qset F ∧ p.2 ∈ Qset F ∧ hd p.1 p.2 = d).card : ℝ) :=
    fun p => Finset.sum_boole _ _
  simp_rw [e2, pair_count hk h d, Fintype.sum_prod_type]
  set V : ℝ := ((k.factorial : ℝ) * numDerangements d * ((k.factorial : ℝ) / k) ^ k *
          (((k : ℝ) - 1)⁻¹) ^ d) ^ h with hV
  have e3 : ∀ x : Cfg k, (∑ y : Cfg k, if IsPerm x ∧ (IsPerm y ∧ hd x y = d) then V else 0) =
      if IsPerm x then (k.choose d * numDerangements d : ℝ) * V else 0 := by
    intro x
    by_cases hx : IsPerm x
    · simp only [hx, true_and, if_true]
      rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, card_dist x hx d]
      push_cast; ring
    · simp [hx]
  simp_rw [e3]
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, card_perms, sum_Z, card_sys, hV, sd]
  push_cast
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : ((k : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  simp only [div_pow, mul_pow, inv_pow, ← pow_mul]
  field_simp

end GeneralizedUniformServer.Dev.LB.PartCA
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias sum_Zd := GeneralizedUniformServer.Dev.LB.PartCA.sum_Zd

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCA
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
variable {k : ℕ}
open Classical in
/-- **CA5** (Lemma 4.8(a)). -/
theorem lx_G3 (hk : 2 ≤ k) (h : ℕ) (x : Cfg k) (hx : IsPerm x) (I : Finset (Fin k))
    (hI : I.Nonempty) (P : Finset (Fin k × Fin k))
    (hP : ∀ ib ∈ P, ib.1 ∈ I ∧ ib.2 ∈ I.image x ∧ ib.2 ≠ x ib.1) :
    ((univ.filter fun F : Sys k h => x ∈ Qset F ∧ P ⊆ Lx F x I).card : ℝ) ≤
      ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) *
        (((I.card : ℝ) - 1) / ((k : ℝ) - 1)) ^ (h * P.card) := by
  have e : (univ.filter fun F : Sys k h => x ∈ Qset F ∧ P ⊆ Lx F x I) =
      univ.filter fun F : Sys k h => ∀ j,
        IsPerm (app (F j) x) ∧ ∀ ib ∈ P, F j ib.1 ib.2 ∈ I.image (app (F j) x) := by
    ext F
    simp only [Qset, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hQ⟩, hPL⟩ j
      refine ⟨hQ j, fun ib hib => ?_⟩
      have := hPL hib
      rw [Lx, mem_filter] at this
      exact this.2.2.2 j
    · intro hF
      refine ⟨⟨hx, fun j => (hF j).1⟩, fun ib hib => ?_⟩
      rw [Lx, mem_filter]
      obtain ⟨h1, h2, h3⟩ := hP ib hib
      exact ⟨mem_product.2 ⟨h1, mem_univ _⟩, h2, h3, fun j => (hF j).2 ib hib⟩
  have e2 : (univ.filter fun F : Sys k h => x ∈ Qset F) =
      univ.filter fun F : Sys k h => ∀ j, IsPerm (app (F j) x) := by
    ext F; simp [Qset, hx]
  rw [e, e2, card_sys_pi h (fun π => IsPerm (app π x) ∧
      ∀ ib ∈ P, π ib.1 ib.2 ∈ I.image (app π x)),
    card_sys_pi h (fun π => IsPerm (app π x))]
  push_cast
  rw [mul_comm h P.card, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity)
    (PartCA.fam_lx hk x I hI P fun ib hib => ⟨(hP ib hib).1, (hP ib hib).2.2⟩) h

open Classical in
/-- **CA4** (Lemma 4.8(b)). -/
theorem lx_G2 (hk : 2 ≤ k) (h : ℕ) (x : Cfg k) (hx : IsPerm x) (I : Finset (Fin k))
    (hI : I.Nonempty) :
    ((univ.filter fun F : Sys k h => x ∈ Qset F ∧ ∀ i ∈ I, ∃ b, (i, b) ∈ Lx F x I).card : ℝ) ≤
      ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) *
        (((I.card : ℝ) - 1) * ((((I.card : ℝ) - 1) / ((k : ℝ) - 1)) ^ h)) ^ I.card := by
  set r : ℝ := ((I.card : ℝ) - 1) / ((k : ℝ) - 1) with hr
  set B : Fin k → Finset (Fin k) := fun i => if i ∈ I then (I.image x).erase (x i) else {x i}
    with hB
  set Pb : (Fin k → Fin k) → Finset (Fin k × Fin k) := fun β => I.image fun i => (i, β i)
    with hPb
  have hPbc : ∀ β, (Pb β).card = I.card := fun β =>
    card_image_of_injective _ (fun i j hij => (Prod.ext_iff.1 hij).1)
  have hPbP : ∀ β ∈ Fintype.piFinset B, ∀ ib ∈ Pb β,
      ib.1 ∈ I ∧ ib.2 ∈ I.image x ∧ ib.2 ≠ x ib.1 := by
    intro β hβ ib hib
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hib
    have := Fintype.mem_piFinset.1 hβ i
    simp only [hB, if_pos hi, mem_erase] at this
    exact ⟨hi, this.2, this.1⟩
  have hsub : (univ.filter fun F : Sys k h => x ∈ Qset F ∧ ∀ i ∈ I, ∃ b, (i, b) ∈ Lx F x I) ⊆
      (Fintype.piFinset B).biUnion fun β =>
        univ.filter fun F : Sys k h => x ∈ Qset F ∧ Pb β ⊆ Lx F x I := by
    intro F hF
    simp only [mem_filter, mem_univ, true_and] at hF
    obtain ⟨hQ, hL⟩ := hF
    set β : Fin k → Fin k := fun i => if hi : i ∈ I then Classical.choose (hL i hi) else x i
      with hβ
    have hβL : ∀ i ∈ I, (i, β i) ∈ Lx F x I := by
      intro i hi
      simp only [hβ, dif_pos hi]
      exact Classical.choose_spec (hL i hi)
    rw [mem_biUnion]
    refine ⟨β, Fintype.mem_piFinset.2 fun i => ?_, ?_⟩
    · by_cases hi : i ∈ I
      · have := hβL i hi
        rw [Lx, mem_filter] at this
        simp only [hB, if_pos hi, mem_erase]
        exact ⟨this.2.2.1, this.2.1⟩
      · simp [hB, hβ, hi]
    · simp only [mem_filter, mem_univ, true_and]
      refine ⟨hQ, fun ib hib => ?_⟩
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hib
      exact hβL i hi
  have hcardB : (Fintype.piFinset B).card = (I.card - 1) ^ I.card := by
    rw [Fintype.card_piFinset]
    have : ∀ i, (B i).card = if i ∈ I then I.card - 1 else 1 := by
      intro i
      by_cases hi : i ∈ I
      · simp only [hB, if_pos hi]
        rw [card_erase_of_mem (mem_image_of_mem x hi), card_image_of_injective _ hx]
      · simp [hB, hi]
    simp_rw [this]
    rw [prod_ite, prod_const_one, mul_one, prod_const, filter_mem_eq_inter, univ_inter]
  calc ((univ.filter fun F : Sys k h => x ∈ Qset F ∧ ∀ i ∈ I, ∃ b, (i, b) ∈ Lx F x I).card : ℝ)
      ≤ (((Fintype.piFinset B).biUnion fun β =>
          univ.filter fun F : Sys k h => x ∈ Qset F ∧ Pb β ⊆ Lx F x I).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ β ∈ Fintype.piFinset B,
          ((univ.filter fun F : Sys k h => x ∈ Qset F ∧ Pb β ⊆ Lx F x I).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ β ∈ Fintype.piFinset B,
          ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) * r ^ (h * I.card) := by
        refine sum_le_sum fun β hβ => ?_
        have := lx_G3 hk h x hx I hI (Pb β) (hPbP β hβ)
        rwa [hPbc β] at this
    _ = _ := by
        rw [sum_const, nsmul_eq_mul, hcardB]
        push_cast [Nat.cast_sub (hI.card_pos : 1 ≤ I.card)]
        rw [mul_pow, pow_mul]
        ring

end GeneralizedUniformServer.Dev.LB.PartCA
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias lx_G2 := GeneralizedUniformServer.Dev.LB.PartCA.lx_G2

alias lx_G3 := GeneralizedUniformServer.Dev.LB.PartCA.lx_G3

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
open scoped Nat
variable {k : ℕ}
lemma sum_Z_sq (hk : 2 ≤ k) (h : ℕ) :
    (∑ F : Sys k h, (Z F : ℝ) ^ 2) =
      (∑ d ∈ range (k + 1), sd k h d) * ∑ F : Sys k h, (Z F : ℝ) := by
  simp_rw [Z_sq]
  rw [Finset.sum_comm]
  simp_rw [sum_Zd hk]
  rw [Finset.sum_mul]

/-- Paley–Zygmund in counting form. -/
lemma pz_count {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : (Fintype.card α : ℝ) * θ ≤ (∑ a, f a) / 2) :
    ((∑ a, f a) / 2) ^ 2 ≤ ((univ.filter fun a => θ ≤ f a).card : ℝ) * ∑ a, f a ^ 2 := by
  set T := univ.filter fun a => θ ≤ f a
  have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun a => θ ≤ f a) f
  have hnot : (∑ a ∈ univ.filter (fun a => ¬ θ ≤ f a), f a) ≤ (Fintype.card α : ℝ) * θ := by
    calc (∑ a ∈ univ.filter (fun a => ¬ θ ≤ f a), f a)
        ≤ ∑ a ∈ univ.filter (fun a => ¬ θ ≤ f a), θ := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mem_filter] at ha; exact (not_le.1 ha.2).le
      _ = ((univ.filter (fun a => ¬ θ ≤ f a)).card : ℝ) * θ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card α : ℝ) * θ := by
          apply mul_le_mul_of_nonneg_right _ hθ0
          exact_mod_cast (card_filter_le _ _).trans (le_of_eq Finset.card_univ)
  have hT : (∑ a, f a) / 2 ≤ ∑ a ∈ T, f a := by linarith
  have h0 : 0 ≤ (∑ a, f a) / 2 := by
    have := Finset.sum_nonneg fun a (_ : a ∈ (univ : Finset α)) => hf a; linarith
  calc ((∑ a, f a) / 2) ^ 2 ≤ (∑ a ∈ T, f a) ^ 2 := pow_le_pow_left₀ h0 hT 2
    _ ≤ (T.card : ℝ) * ∑ a ∈ T, f a ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (T.card : ℝ) * ∑ a, f a ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun a _ _ => sq_nonneg _

lemma card_pos_le_sum {α : Type*} [Fintype α] (f : α → ℕ) :
    (((univ.filter fun a => 0 < f a).card : ℕ) : ℝ) ≤ ∑ a, (f a : ℝ) := by
  classical
  rw [← Finset.sum_boole]
  refine Finset.sum_le_sum fun a _ => ?_
  split_ifs with h
  · exact_mod_cast h
  · exact Nat.cast_nonneg _

/-! ## Bad systems -/
open Classical in
/-- Systems violating (G1) (contained in). -/
def U1 (k h : ℕ) : Finset (Sys k h) :=
  ((range (k + 1)).filter
      (fun d : ℕ => (1 / 25 : ℝ) * k ≤ d ∧ (d : ℝ) ≤ (77 / 100 : ℝ) * k)).biUnion
    fun d => univ.filter fun F : Sys k h => 0 < Zd F d

open Classical in
def I2set (k : ℕ) : Finset (Finset (Fin k)) := univ.filter fun I : Finset (Fin k) =>
  (2 / 25 : ℝ) * k ≤ I.card ∧ (I.card : ℝ) < (2 / 25 + 1 / 25 : ℝ) * k

open Classical in
/-- Systems violating (G2) (contained in). -/
def U2 (k h : ℕ) : Finset (Sys k h) :=
  ((univ : Finset (Cfg k)) ×ˢ I2set k).biUnion fun xI =>
    univ.filter fun F : Sys k h => xI.1 ∈ Qset F ∧ ∀ i ∈ xI.2, ∃ b, (i, b) ∈ Lx F xI.1 xI.2

open Classical in
def I3set (k : ℕ) : Finset (Finset (Fin k)) := univ.filter fun I : Finset (Fin k) =>
  (I.card : ℝ) < (2 / 25 : ℝ) * k ∧ I.Nonempty

open Classical in
/-- Systems violating (G3) (contained in). -/
def U3 (k h : ℕ) : Finset (Sys k h) :=
  ((univ : Finset (Cfg k)) ×ˢ
      (I3set k ×ˢ (univ : Finset (Fin k × Fin k)).powersetCard k)).biUnion
    fun t => univ.filter fun F : Sys k h => t.1 ∈ Qset F ∧ t.2.2 ⊆ Lx F t.1 t.2.1

open Classical in
lemma good_of_not_mem (hk : 1 ≤ k) {h : ℕ} (F : Sys k h) (h1 : F ∉ U1 k h) (h2 : F ∉ U2 k h)
    (h3 : F ∉ U3 k h) : Good F := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    apply h1
    unfold U1
    rw [mem_biUnion]
    refine ⟨hd x y, mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (hd_le x y)), hxy⟩, ?_⟩
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    unfold Zd
    exact card_pos.2 ⟨(x, y), mem_filter.2 ⟨mem_product.2 ⟨hx, hy⟩, rfl⟩⟩
  · intro x hx I hI
    apply h2
    unfold U2
    rw [mem_biUnion]
    refine ⟨(x, I), mem_product.2 ⟨mem_univ _, ?_⟩, ?_⟩
    · unfold I2set; exact mem_filter.2 ⟨mem_univ _, hI.1, hI.2.1⟩
    · exact mem_filter.2 ⟨mem_univ _, hx, hI.2.2⟩
  · intro x hx I hI
    obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hI.2
    have hne : I.Nonempty := by
      have : (Lx F x I).Nonempty := by
        rw [← card_pos]; omega
      obtain ⟨⟨i, b⟩, hib⟩ := this
      unfold Lx at hib
      rw [mem_filter, mem_product] at hib
      exact ⟨i, hib.1.1⟩
    apply h3
    unfold U3
    rw [mem_biUnion]
    refine ⟨(x, (I, P)), mem_product.2 ⟨mem_univ _, mem_product.2 ⟨?_, ?_⟩⟩, ?_⟩
    · unfold I3set; exact mem_filter.2 ⟨mem_univ _, hI.1, hne⟩
    · exact mem_powersetCard.2 ⟨subset_univ _, hPcard⟩
    · exact mem_filter.2 ⟨mem_univ _, hx, hPsub⟩

open Classical in
lemma card_U1 (hk : 2 ≤ k) (h : ℕ) :
    ((U1 k h).card : ℝ) ≤
      (∑ d ∈ (range (k + 1)).filter
          (fun d : ℕ => (1 / 25 : ℝ) * k ≤ d ∧ (d : ℝ) ≤ (77 / 100 : ℝ) * k), sd k h d) *
        ∑ F : Sys k h, (Z F : ℝ) := by
  unfold U1
  refine (Nat.cast_le.2 (card_biUnion_le)).trans ?_
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [← sum_Zd hk]
  exact card_pos_le_sum (fun F : Sys k h => Zd F d)

open Classical in
lemma card_U2 (hk : 2 ≤ k) (h : ℕ) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ c : ℕ, (2 / 25 : ℝ) * k ≤ c → (c : ℝ) < (2 / 25 + 1 / 25 : ℝ) * k →
      (((c : ℝ) - 1) * ((((c : ℝ) - 1) / ((k : ℝ) - 1)) ^ h)) ^ c ≤ A) :
    ((U2 k h).card : ℝ) ≤ 2 ^ k * A * ∑ F : Sys k h, (Z F : ℝ) := by
  unfold U2
  refine (Nat.cast_le.2 (card_biUnion_le)).trans ?_
  push_cast
  rw [Finset.sum_product]
  have hterm : ∀ x : Cfg k, ∀ I ∈ I2set k,
      (((univ.filter fun F : Sys k h => x ∈ Qset F ∧
          ∀ i ∈ I, ∃ b, (i, b) ∈ Lx F x I).card : ℕ) : ℝ) ≤
        ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) * A := by
    intro x I hI
    unfold I2set at hI
    rw [mem_filter] at hI
    by_cases hx : IsPerm x
    · have hIne : I.Nonempty := by
        rw [← card_pos]
        have : (0 : ℝ) < I.card := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk
          linarith [hI.2.1]
        exact_mod_cast this
      refine (lx_G2 hk h x hx I hIne).trans ?_
      exact mul_le_mul_of_nonneg_left (hA _ hI.2.1 hI.2.2) (Nat.cast_nonneg _)
    · have : (univ.filter fun F : Sys k h => x ∈ Qset F ∧
          ∀ i ∈ I, ∃ b, (i, b) ∈ Lx F x I) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro F _ hF; exact hx (perm_of_mem hF.1)
      rw [this, card_empty, Nat.cast_zero]
      exact mul_nonneg (Nat.cast_nonneg _) hA0
  calc (∑ x : Cfg k, ∑ I ∈ I2set k,
        (((univ.filter fun F : Sys k h => x ∈ Qset F ∧
          ∀ i ∈ I, ∃ b, (i, b) ∈ Lx F x I).card : ℕ) : ℝ))
      ≤ ∑ x : Cfg k, ∑ I ∈ I2set k,
          ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) * A :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun I hI => hterm x I hI
    _ = ((I2set k).card : ℝ) * A *
          ∑ x : Cfg k, ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 ^ k * A * ∑ F : Sys k h, (Z F : ℝ) := by
        rw [sum_acc]
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_right _ hA0
        have : (I2set k).card ≤ 2 ^ k := by
          unfold I2set
          refine (card_filter_le _ _).trans (le_of_eq ?_)
          simp
        exact_mod_cast this

open Classical in
lemma card_U3 (hk : 2 ≤ k) (h : ℕ) :
    ((U3 k h).card : ℝ) ≤
      (2 : ℝ) ^ k * ((k * k).choose k : ℝ) * (2 / 25 : ℝ) ^ (h * k) *
        ∑ F : Sys k h, (Z F : ℝ) := by
  unfold U3
  refine (Nat.cast_le.2 (card_biUnion_le)).trans ?_
  push_cast
  rw [Finset.sum_product]
  set c : ℝ := (2 / 25 : ℝ) ^ (h * k) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hterm : ∀ x : Cfg k, ∀ IP ∈ I3set k ×ˢ (univ : Finset (Fin k × Fin k)).powersetCard k,
      (((univ.filter fun F : Sys k h => x ∈ Qset F ∧ IP.2 ⊆ Lx F x IP.1).card : ℕ) : ℝ) ≤
        ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) * c := by
    rintro x ⟨I, P⟩ hIP
    rw [mem_product] at hIP
    obtain ⟨hI, hP⟩ := hIP
    unfold I3set at hI
    rw [mem_filter] at hI
    rw [mem_powersetCard] at hP
    by_cases hgood : IsPerm x ∧ ∀ ib ∈ P, ib.1 ∈ I ∧ ib.2 ∈ I.image x ∧ ib.2 ≠ x ib.1
    · refine (lx_G3 hk h x hgood.1 I hI.2.2 P hgood.2).trans ?_
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [hP.2, hcdef]
      have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have hI1 : (1 : ℝ) ≤ I.card := by exact_mod_cast card_pos.2 hI.2.2
      apply pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith))
      rw [div_le_iff₀ (by linarith)]
      linarith [hI.2.1]
    · have : (univ.filter fun F : Sys k h => x ∈ Qset F ∧ P ⊆ Lx F x I) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro F _ hF
        apply hgood
        refine ⟨perm_of_mem hF.1, fun ib hib => ?_⟩
        have := hF.2 hib
        unfold Lx at this
        rw [mem_filter, mem_product] at this
        exact ⟨this.1.1, this.2.1, this.2.2.1⟩
      rw [this, card_empty, Nat.cast_zero]
      exact mul_nonneg (Nat.cast_nonneg _) hc0
  calc (∑ x : Cfg k, ∑ IP ∈ I3set k ×ˢ (univ : Finset (Fin k × Fin k)).powersetCard k,
        (((univ.filter fun F : Sys k h => x ∈ Qset F ∧ IP.2 ⊆ Lx F x IP.1).card : ℕ) : ℝ))
      ≤ ∑ x : Cfg k, ∑ IP ∈ I3set k ×ˢ (univ : Finset (Fin k × Fin k)).powersetCard k,
          ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) * c :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun IP hIP => hterm x IP hIP
    _ = ((I3set k ×ˢ (univ : Finset (Fin k × Fin k)).powersetCard k).card : ℝ) * c *
          ∑ x : Cfg k, ((univ.filter fun F : Sys k h => x ∈ Qset F).card : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (2 : ℝ) ^ k * ((k * k).choose k : ℝ) * c * ∑ F : Sys k h, (Z F : ℝ) := by
        rw [sum_acc]
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_right _ hc0
        have h1 : (I3set k).card ≤ 2 ^ k := by
          unfold I3set
          refine (card_filter_le _ _).trans (le_of_eq ?_)
          simp
        have h2 : ((univ : Finset (Fin k × Fin k)).powersetCard k).card = (k * k).choose k := by
          rw [card_powersetCard]; simp
        rw [card_product, h2]
        push_cast
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast h1

lemma sd_nonneg (hk : 1 ≤ k) (h d : ℕ) : 0 ≤ sd k h d := by
  unfold sd
  have : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  positivity

end GeneralizedUniformServer.Dev.LB.PartCB
end
end

section
set_option autoImplicit false
noncomputable section

end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset Real
open scoped Nat
/-!
# Part CB, real-analysis estimates

Plan (`K = k`, `L = log K`, `h = hh k`, so `0.9 L - 1 < h ≤ 0.9 L`; all "large k" facts follow
from `L ≥ 20000`, which also gives `0.9 L (3 + L/2) ≤ K` because `K = e^L ≥ L³/6`).

* `s_d` (`2 ≤ d ≤ k`): `C(k,d) D_d ≤ k^d`; `D_d ≤ d! ≤ e √d (d/e)^d` (Stirling sequence is
  antitone); `(K-1)^d ≥ e^{dL-2}`. With `Λ = d (log d - L) - d ∈ [-K, 0]`:
  `log (D_d/(K-1)^d) ≤ Λ + 3 + log d / 2`, so
  `h·(…) ≤ (0.9L - 1) Λ + 0.9 L (3 + L/2) ≤ 0.9 L Λ + 2K`, and
  `s_d ≤ exp (dL + 0.9LΛ + 2K) = exp (K L g(d/K) + 2K)`, `g u = u/10 + 0.9 u log u`.
* `S2 = ∑_{d ≤ k} s_d ≤ (K+1) e^{0.1 KL + 2K}` since `g u ≤ u/10 ≤ 1/10` on `(0,1]`
  (`s_0 = 1`, `s_1 = 0`).
* (G1) `g` convex, `g(1/25) ≤ -0.1031`, `g(77/100) ≤ -0.1031` (from `log 25 ≥ 4.5 log 2`,
  `log (100/77) ≥ (3/8) log 2`), so `W1 = ∑_{δK ≤ d ≤ βK} s_d ≤ (K+1) e^{-0.1031 KL + 2K}`.
* (G2) `c = |I| ∈ [0.08K, 0.12K)`, `u = c/K`, `r = (c-1)/(K-1) ≤ u`:
  `((c-1) r^h)^c ≤ (K u^h)^c ≤ exp (c (L + 0.9 L log u + 11.5)) ≤ exp (K L f(u) + 12K)`,
  `f u = u + 0.9 u log u` convex, `f(0.08) ≤ -0.1018` (from `3 log 12.5 ≥ 11 log 2 - 0.048576`),
  `f(0.12) ≤ -0.1018` (from `log (25/3) ≥ 3 log 2`).
* (G3) `2^k C(k², k) (2/25)^{hk} ≤ e^K e^{2KL} e^{K(-2.2725 L + 11.5)}`.
* `E₀Z = k! (k!/k^k)^h ≥ e^{KL-K} e^{-hK} ≥ e^{0.1 KL - K}` (`K^k/k! ≤ e^K`).
* Final: `4 S2 (W1 + W2 + W3) ≤ 12 e^{0.1KL + 3K} e^{-0.1018 KL + 13K} ≤ 12 e^{-20K} < 1`.
-/
/-! ## Numerical facts -/
lemma log25_ge : (9 / 2) * Real.log 2 ≤ Real.log 25 := by
  have h := Real.log_le_log (by norm_num) (show ((2 : ℝ) ^ 9) ≤ (25 : ℝ) ^ 2 by norm_num)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

lemma log_100_77_ge : (3 / 8) * Real.log 2 ≤ Real.log (100 / 77) := by
  have h := Real.log_le_log (by norm_num) (show ((2 : ℝ) ^ 3) ≤ (100 / 77 : ℝ) ^ 8 by norm_num)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

lemma log_12_5_ge : 11 * Real.log 2 - 0.048576 ≤ 3 * Real.log (25 / 2) := by
  have e : ((2 : ℝ) ^ 11) = (25 / 2 : ℝ) ^ 3 * 1.048576 := by norm_num
  have h1 : Real.log ((2 : ℝ) ^ 11) = 3 * Real.log (25 / 2) + Real.log 1.048576 := by
    rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have h2 : Real.log (1.048576 : ℝ) ≤ 1.048576 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  rw [Real.log_pow] at h1; push_cast at h1; linarith

lemma log_25_3_ge : 3 * Real.log 2 ≤ Real.log (25 / 3) := by
  have h := Real.log_le_log (by norm_num) (show ((2 : ℝ) ^ 3) ≤ (25 / 3 : ℝ) by norm_num)
  rw [Real.log_pow] at h; push_cast at h; linarith

/-- `g u = u/10 + 0.9 u log u` (the second-moment exponent). -/
def gfun (u : ℝ) : ℝ := u / 10 + 9 / 10 * (u * Real.log u)

/-- `f u = u + 0.9 u log u` (the (G2) exponent). -/
def ffun (u : ℝ) : ℝ := u + 9 / 10 * (u * Real.log u)

lemma convex_aux (a : ℝ) (ha : 0 ≤ a) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun u : ℝ => a * u + 9 / 10 * (u * Real.log u)) := by
  have h1 := (convexOn_id (convex_Ici (0 : ℝ))).smul ha
  have h2 := Real.convexOn_mul_log.smul (show (0 : ℝ) ≤ 9 / 10 by norm_num)
  have h3 := h1.add h2
  have e : (fun u : ℝ => a * u + 9 / 10 * (u * Real.log u)) =
      ((fun x : ℝ => a • id x) + fun x => (9 / 10 : ℝ) • (x * Real.log x)) := by
    funext u; simp [smul_eq_mul]
  rw [e]; exact h3

lemma gfun_G1 (u : ℝ) (hu : u ∈ Set.Icc (1 / 25 : ℝ) (77 / 100)) : gfun u ≤ -0.1031 := by
  have hc : ConvexOn ℝ (Set.Ici (0 : ℝ)) gfun := by
    convert convex_aux (1 / 10) (by norm_num) using 1; funext u; simp [gfun]; ring
  have hm := hc.le_max_of_mem_Icc (show (1 / 25 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (77 / 100 : ℝ) ∈ Set.Ici 0 by norm_num) hu
  have l2 := Real.log_two_gt_d9
  have e1 : Real.log (1 / 25 : ℝ) = - Real.log 25 := by rw [one_div, Real.log_inv]
  have e2 : Real.log (77 / 100 : ℝ) = - Real.log (100 / 77) := by
    rw [← Real.log_inv]; norm_num
  have a1 := log25_ge
  have a2 := log_100_77_ge
  have g1 : gfun (1 / 25) ≤ -0.1031 := by simp only [gfun]; rw [e1]; nlinarith
  have g2 : gfun (77 / 100) ≤ -0.1031 := by simp only [gfun]; rw [e2]; nlinarith
  exact hm.trans (max_le g1 g2)

lemma ffun_G2 (u : ℝ) (hu : u ∈ Set.Icc (2 / 25 : ℝ) (3 / 25)) : ffun u ≤ -0.1018 := by
  have hc : ConvexOn ℝ (Set.Ici (0 : ℝ)) ffun := by
    convert convex_aux 1 (by norm_num) using 1; funext u; simp [ffun]
  have hm := hc.le_max_of_mem_Icc (show (2 / 25 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (3 / 25 : ℝ) ∈ Set.Ici 0 by norm_num) hu
  have l2 := Real.log_two_gt_d9
  have e1 : Real.log (2 / 25 : ℝ) = - Real.log (25 / 2) := by
    rw [← Real.log_inv]; norm_num
  have e2 : Real.log (3 / 25 : ℝ) = - Real.log (25 / 3) := by
    rw [← Real.log_inv]; norm_num
  have a1 := log_12_5_ge
  have a2 := log_25_3_ge
  have g1 : ffun (2 / 25) ≤ -0.1018 := by simp only [ffun]; rw [e1]; nlinarith
  have g2 : ffun (3 / 25) ≤ -0.1018 := by simp only [ffun]; rw [e2]; nlinarith
  exact hm.trans (max_le g1 g2)

/-! ## Factorials, derangements, `hh` -/
lemma numDer_le_fact (n : ℕ) : numDerangements n ≤ n ! := by
  have key : ∀ n, numDerangements n ≤ n ! ∧ numDerangements (n + 1) ≤ (n + 1)! := by
    intro n
    induction n with
    | zero => simp [numDerangements_zero, numDerangements_one]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [numDerangements_add_two]
      have e : (n + 1 + 1)! = (n + 1) * (n ! + (n + 1)!) := by
        simp [Nat.factorial_succ]; ring
      rw [e]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add ih.1 ih.2)
  exact (key n).1

lemma fact_le_exp (n : ℕ) (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ Real.exp (1 + Real.log n / 2 + n * Real.log n - n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have h : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le (n - 1))
    simp only [Function.comp] at this
    rwa [Nat.succ_eq_add_one, Nat.sub_add_cancel hn] at this
  rw [Stirling.stirlingSeq_one] at h
  unfold Stirling.stirlingSeq at h
  have hd : 0 < √(2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n := by positivity
  rw [div_le_iff₀ hd] at h
  have hs : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]
  have h2 : (n ! : ℝ) ≤ Real.exp 1 * √(n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n := by
    have : Real.exp 1 / √2 * (√(2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) =
        Real.exp 1 * √(n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n := by
      rw [hs]; field_simp
    linarith
  refine h2.trans (le_of_eq ?_)
  have e1 : √(n : ℝ) = Real.exp (Real.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]; ring_nf
  have e2 : ((n : ℝ) / Real.exp 1) ^ n = Real.exp (n * Real.log n - n) := by
    rw [← Real.exp_log (show (0 : ℝ) < n / Real.exp 1 by positivity), ← Real.exp_nat_mul,
      Real.log_div hpos.ne' (Real.exp_pos 1).ne', Real.log_exp]; ring_nf
  rw [e1, e2, ← Real.exp_add, ← Real.exp_add]; ring_nf

lemma fact_ge_exp (n : ℕ) : Real.exp (n * Real.log n - n) ≤ (n ! : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.pow_div_factorial_le_exp (n : ℝ) (le_of_lt hpos) n
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  have e : (n : ℝ) ^ n = Real.exp (n * Real.log n) := by
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  rw [e] at h
  rw [Real.exp_sub, div_le_iff₀ (Real.exp_pos _)]; linarith

lemma hh_le (k : ℕ) : (hh k : ℝ) ≤ 9 / 10 * Real.log k := by
  unfold hh; exact Nat.floor_le (by have := Real.log_natCast_nonneg k; positivity)

lemma hh_gt (k : ℕ) : 9 / 10 * Real.log k - 1 < hh k := by
  have := Nat.lt_floor_add_one (9 / 10 * Real.log (k : ℝ)); unfold hh; linarith

/-- `(K-1)^d ≥ e^{dL - 2}`. -/
lemma pow_sub_one_ge (K : ℝ) (hK : 2 ≤ K) (d : ℕ) (hd : (d : ℝ) ≤ K) :
    Real.exp (d * Real.log K - 2) ≤ (K - 1) ^ d := by
  have h1 : 0 < K - 1 := by linarith
  have hl : Real.log K - Real.log (K - 1) ≤ 1 / (K - 1) := by
    rw [← Real.log_div (by linarith) h1.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < K / (K - 1) by positivity)
    have e : K / (K - 1) - 1 = 1 / (K - 1) := by field_simp; ring
    linarith
  have hdK : (d : ℝ) / (K - 1) ≤ 2 := by
    rw [div_le_iff₀ h1]; linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [← Real.exp_log h1, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have : (d : ℝ) * (Real.log K - Real.log (K - 1)) ≤ d * (1 / (K - 1)) :=
    mul_le_mul_of_nonneg_left hl hd0
  have e : (d : ℝ) * (1 / (K - 1)) = d / (K - 1) := by ring
  nlinarith

/-! ## The second-moment terms `s_d` -/
lemma sd_le {k h d : ℕ} (hk : 2 ≤ k) (hd : 2 ≤ d) (hdk : d ≤ k)
    (hh1 : 9 / 10 * Real.log k - 1 ≤ h) (hh2 : (h : ℝ) ≤ 9 / 10 * Real.log k)
    (hpoly : 9 / 10 * Real.log k * (3 + Real.log k / 2) ≤ k) :
    sd k h d ≤ Real.exp (k * Real.log k * gfun (d / k) + 2 * k) := by
  set K : ℝ := (k : ℝ) with hKdef
  set L : ℝ := Real.log K with hLdef
  set D : ℝ := (d : ℝ) with hDdef
  have hK2 : (2 : ℝ) ≤ K := by rw [hKdef]; exact_mod_cast hk
  have hD2 : (2 : ℝ) ≤ D := by rw [hDdef]; exact_mod_cast hd
  have hDK : D ≤ K := by rw [hDdef, hKdef]; exact_mod_cast hdk
  have hDpos : 0 < D := by linarith
  have hKpos : 0 < K := by linarith
  have hlogD : Real.log D ≤ L := Real.log_le_log hDpos hDK
  have hlogD0 : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  -- `C(k,d) D_d ≤ k^d`
  have hA : (k.choose d : ℝ) * numDerangements d ≤ K ^ d := by
    have : k.choose d * numDerangements d ≤ k ^ d := by
      calc k.choose d * numDerangements d ≤ k.choose d * d ! :=
            Nat.mul_le_mul_left _ (numDer_le_fact d)
        _ = k.descFactorial d := by rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
        _ ≤ k ^ d := Nat.descFactorial_le_pow k d
    rw [hKdef]; exact_mod_cast this
  have hKd : K ^ d = Real.exp (D * L) := by
    rw [hLdef, Real.exp_nat_mul, Real.exp_log hKpos]
  set Λ : ℝ := D * (Real.log D - L) - D with hΛdef
  -- `D_d / (K-1)^d ≤ e^{Λ + 3 + log d / 2}`
  have ht : (numDerangements d : ℝ) / (K - 1) ^ d ≤ Real.exp (Λ + 3 + Real.log D / 2) := by
    have h1 : (numDerangements d : ℝ) ≤ Real.exp (1 + Real.log D / 2 + D * Real.log D - D) :=
      (by exact_mod_cast numDer_le_fact d : (numDerangements d : ℝ) ≤ d !).trans
        (fact_le_exp d (by omega))
    have h2 := pow_sub_one_ge K hK2 d hDK
    calc (numDerangements d : ℝ) / (K - 1) ^ d
        ≤ Real.exp (1 + Real.log D / 2 + D * Real.log D - D) / Real.exp (D * L - 2) :=
          div_le_div₀ (by positivity) h1 (Real.exp_pos _) h2
      _ = Real.exp (Λ + 3 + Real.log D / 2) := by
          rw [← Real.exp_sub]; congr 1; rw [hΛdef]; ring
  have ht0 : 0 ≤ (numDerangements d : ℝ) / (K - 1) ^ d := by
    have : 0 ≤ K - 1 := by linarith
    positivity
  have hth : ((numDerangements d : ℝ) / (K - 1) ^ d) ^ h ≤
      Real.exp (h * (Λ + 3 + Real.log D / 2)) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ ht0 ht h
  have hΛ0 : Λ ≤ 0 := by
    have : D * (Real.log D - L) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hDpos.le (by linarith)
    linarith
  have hΛK : -Λ ≤ K := by
    have hq : L - Real.log D ≤ K / D - 1 := by
      rw [← Real.log_div hKpos.ne' hDpos.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have : D * (L - Real.log D) ≤ D * (K / D - 1) := mul_le_mul_of_nonneg_left hq hDpos.le
    have e : D * (K / D - 1) = K - D := by field_simp
    linarith
  have key : (h : ℝ) * (Λ + 3 + Real.log D / 2) ≤ 9 / 10 * L * Λ + 2 * K := by
    have a1 : (h : ℝ) * Λ ≤ (9 / 10 * L - 1) * Λ := mul_le_mul_of_nonpos_right hh1 hΛ0
    have a2 : (h : ℝ) * (3 + Real.log D / 2) ≤ 9 / 10 * L * (3 + L / 2) :=
      mul_le_mul hh2 (by linarith) (by positivity) (by positivity)
    nlinarith
  unfold sd
  calc (k.choose d : ℝ) * numDerangements d * ((numDerangements d : ℝ) / ((k : ℝ) - 1) ^ d) ^ h
      ≤ K ^ d * Real.exp (h * (Λ + 3 + Real.log D / 2)) :=
        mul_le_mul hA hth (pow_nonneg ht0 _) (by positivity)
    _ ≤ Real.exp (D * L) * Real.exp (9 / 10 * L * Λ + 2 * K) := by
        rw [hKd]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 key) (Real.exp_pos _).le
    _ = Real.exp (K * L * gfun (D / K) + 2 * K) := by
        rw [← Real.exp_add]; congr 1
        simp only [gfun, hΛdef]
        rw [Real.log_div hDpos.ne' hKpos.ne']
        field_simp; ring

/-! ## Large `k` -/
lemma big_of_log (k : ℕ) (hL : 20000 ≤ Real.log k) :
    50 ≤ (k : ℝ) ∧ 9 / 10 * Real.log k * (3 + Real.log k / 2) ≤ k := by
  have hk0 : (0 : ℝ) < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hL; linarith
    · exact_mod_cast h
  have h3 := Real.pow_div_factorial_le_exp (Real.log k) (by linarith) 3
  rw [Real.exp_log hk0] at h3
  have e : ((3 ! : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [e] at h3
  set L := Real.log (k : ℝ)
  have h4 : (20000 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  constructor
  · nlinarith
  · nlinarith

lemma exists_big : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → 20000 ≤ Real.log k := by
  refine ⟨⌈Real.exp 20000⌉₊, fun k hk => ?_⟩
  have h1 : Real.exp 20000 ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  exact (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le h1)).2 h1

end GeneralizedUniformServer.Dev.LB.PartCB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset Real
open scoped Nat
variable {k h : ℕ} (hk : 50 ≤ (k : ℝ))
  (hh1 : 9 / 10 * Real.log k - 1 ≤ h) (hh2 : (h : ℝ) ≤ 9 / 10 * Real.log k)
  (hpoly : 9 / 10 * Real.log k * (3 + Real.log k / 2) ≤ k)
include hk hh1 hh2 hpoly
/-! ## The bounds used for Part CB -/
omit hh1 hh2 hpoly in
lemma k_ge_two : 2 ≤ k := by
  by_contra hc
  have : (k : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 (not_le.1 hc)
  linarith

lemma sd_le_all (d : ℕ) (hdk : d ≤ k) :
    sd k h d ≤ Real.exp (k * Real.log k / 10 + 2 * k) := by
  have hk2 := k_ge_two hk
  have hK : (0 : ℝ) < k := by linarith
  have hL0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hKL : 0 ≤ (k : ℝ) * Real.log k := mul_nonneg hK.le hL0
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d
    · unfold sd; simp [numDerangements_zero]
      positivity
    · unfold sd; simp [numDerangements_one]; positivity
  · refine (sd_le hk2 hd hdk hh1 hh2 hpoly).trans (Real.exp_le_exp.2 ?_)
    have hD : (0 : ℝ) < d := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                                linarith
    have hDK : (d : ℝ) ≤ k := by exact_mod_cast hdk
    have hu0 : 0 < (d : ℝ) / k := div_pos hD hK
    have hu1 : (d : ℝ) / k ≤ 1 := (div_le_one hK).2 hDK
    have hlog : Real.log ((d : ℝ) / k) ≤ 0 := Real.log_nonpos hu0.le hu1
    have hg : gfun ((d : ℝ) / k) ≤ 1 / 10 := by
      unfold gfun
      have : (d : ℝ) / k * Real.log ((d : ℝ) / k) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0.le hlog
      linarith
    have := mul_le_mul_of_nonneg_left hg hKL
    linarith

lemma S2_le :
    (∑ d ∈ range (k + 1), sd k h d) ≤ Real.exp (k * Real.log k / 10 + 3 * k) := by
  have h1 : (∑ d ∈ range (k + 1), sd k h d) ≤
      (range (k + 1)).card • Real.exp (k * Real.log k / 10 + 2 * k) :=
    Finset.sum_le_card_nsmul _ _ _ fun d hd =>
      sd_le_all hk hh1 hh2 hpoly d (Nat.lt_succ_iff.1 (Finset.mem_range.1 hd))
  rw [card_range, nsmul_eq_mul] at h1
  have h2 : ((k + 1 : ℕ) : ℝ) ≤ Real.exp k := by
    have := Real.add_one_le_exp (k : ℝ); push_cast; linarith
  have e : Real.exp (k * Real.log k / 10 + 3 * k) =
      Real.exp k * Real.exp (k * Real.log k / 10 + 2 * k) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)

lemma W1_le :
    (∑ d ∈ (range (k + 1)).filter
        (fun d : ℕ => (1 / 25 : ℝ) * k ≤ d ∧ (d : ℝ) ≤ (77 / 100 : ℝ) * k), sd k h d) ≤
      Real.exp (-(0.1031 : ℝ) * (k * Real.log k) + 3 * k) := by
  have hk2 := k_ge_two hk
  have hK : (0 : ℝ) < k := by linarith
  have hL0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hKL : 0 ≤ (k : ℝ) * Real.log k := mul_nonneg hK.le hL0
  have h1 : (∑ d ∈ (range (k + 1)).filter
        (fun d : ℕ => (1 / 25 : ℝ) * k ≤ d ∧ (d : ℝ) ≤ (77 / 100 : ℝ) * k), sd k h d) ≤
      ((range (k + 1)).filter
        (fun d : ℕ => (1 / 25 : ℝ) * k ≤ d ∧ (d : ℝ) ≤ (77 / 100 : ℝ) * k)).card •
        Real.exp (-(0.1031 : ℝ) * (k * Real.log k) + 2 * k) := by
    refine Finset.sum_le_card_nsmul _ _ _ fun d hd => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨hdk, hd1, hd2⟩ := hd
    have hdk' : d ≤ k := Nat.lt_succ_iff.1 hdk
    have hd2' : 2 ≤ d := by
      have : (2 : ℝ) ≤ d := by linarith
      exact_mod_cast this
    refine (sd_le hk2 hd2' hdk' hh1 hh2 hpoly).trans (Real.exp_le_exp.2 ?_)
    have hu : (d : ℝ) / k ∈ Set.Icc (1 / 25 : ℝ) (77 / 100) := by
      constructor
      · rw [le_div_iff₀ hK]; linarith
      · rw [div_le_iff₀ hK]; linarith
    have := mul_le_mul_of_nonneg_left (gfun_G1 _ hu) hKL
    linarith
  have hc : (((range (k + 1)).filter
        (fun d : ℕ => (1 / 25 : ℝ) * k ≤ d ∧ (d : ℝ) ≤ (77 / 100 : ℝ) * k)).card : ℝ) ≤
      Real.exp k := by
    have h3 := Finset.card_filter_le (range (k + 1))
      (fun d : ℕ => (1 / 25 : ℝ) * k ≤ d ∧ (d : ℝ) ≤ (77 / 100 : ℝ) * k)
    rw [card_range] at h3
    have h4 : (((range (k + 1)).filter
        (fun d : ℕ => (1 / 25 : ℝ) * k ≤ d ∧ (d : ℝ) ≤ (77 / 100 : ℝ) * k)).card : ℝ) ≤
        (k : ℝ) + 1 := by exact_mod_cast h3
    have := Real.add_one_le_exp (k : ℝ); linarith
  rw [nsmul_eq_mul] at h1
  have e : Real.exp (-(0.1031 : ℝ) * (k * Real.log k) + 3 * k) =
      Real.exp k * Real.exp (-(0.1031 : ℝ) * (k * Real.log k) + 2 * k) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  exact h1.trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le)

omit hh2 hpoly in
lemma b2_le (c : ℕ) (hc1 : (2 / 25 : ℝ) * k ≤ c) (hc2 : (c : ℝ) < (2 / 25 + 1 / 25 : ℝ) * k) :
    (((c : ℝ) - 1) * ((((c : ℝ) - 1) / ((k : ℝ) - 1)) ^ h)) ^ c ≤
      Real.exp (-(0.1018 : ℝ) * (k * Real.log k) + 12 * k) := by
  have hK : (0 : ℝ) < k := by linarith
  have hL0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hKL : 0 ≤ (k : ℝ) * Real.log k := mul_nonneg hK.le hL0
  set K : ℝ := (k : ℝ) with hKdef
  set L : ℝ := Real.log K with hLdef
  set C : ℝ := (c : ℝ) with hCdef
  have hC4 : 4 ≤ C := by linarith
  have hCK : C ≤ K := by linarith
  set u : ℝ := C / K with hudef
  have hu0 : 0 < u := div_pos (by linarith) hK
  have hu : u ∈ Set.Icc (2 / 25 : ℝ) (3 / 25) := by
    constructor
    · rw [hudef, le_div_iff₀ hK]; linarith
    · rw [hudef, div_le_iff₀ hK]; linarith
  have hu1 : u ≤ 1 := by linarith [hu.2]
  have hr0 : 0 ≤ (C - 1) / (K - 1) := div_nonneg (by linarith) (by linarith)
  have hru : (C - 1) / (K - 1) ≤ u := by
    rw [hudef, div_le_div_iff₀ (by linarith) hK]; nlinarith
  have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
  have hlogu2 : -Real.log u ≤ 23 / 2 := by
    have h1 := Real.one_sub_inv_le_log_of_pos hu0
    have h2 : u⁻¹ ≤ 25 / 2 := by
      rw [inv_le_comm₀ hu0 (by norm_num)]; linarith [hu.1]
    linarith
  have hhu : (h : ℝ) * Real.log u ≤ 9 / 10 * L * Real.log u + 23 / 2 := by
    have := mul_le_mul_of_nonpos_right hh1 hlogu
    nlinarith
  have hpow : ((C - 1) / (K - 1)) ^ h ≤ Real.exp (9 / 10 * L * Real.log u + 23 / 2) := by
    calc ((C - 1) / (K - 1)) ^ h ≤ u ^ h := pow_le_pow_left₀ hr0 hru h
      _ = Real.exp (h * Real.log u) := by rw [Real.exp_nat_mul, Real.exp_log hu0]
      _ ≤ _ := Real.exp_le_exp.2 hhu
  have hbase0 : 0 ≤ (C - 1) * ((C - 1) / (K - 1)) ^ h :=
    mul_nonneg (by linarith) (pow_nonneg hr0 _)
  have hbase : (C - 1) * ((C - 1) / (K - 1)) ^ h ≤
      Real.exp (L + 9 / 10 * L * Real.log u + 23 / 2) := by
    calc (C - 1) * ((C - 1) / (K - 1)) ^ h
        ≤ K * Real.exp (9 / 10 * L * Real.log u + 23 / 2) :=
          mul_le_mul (by linarith) hpow (pow_nonneg hr0 _) hK.le
      _ = _ := by rw [hLdef]; simp only [Real.exp_add, Real.exp_log hK]; ring
  have hf := mul_le_mul_of_nonneg_left (ffun_G2 u hu) hKL
  calc ((C - 1) * ((C - 1) / (K - 1)) ^ h) ^ c
      ≤ Real.exp (L + 9 / 10 * L * Real.log u + 23 / 2) ^ c := pow_le_pow_left₀ hbase0 hbase c
    _ = Real.exp (C * (L + 9 / 10 * L * Real.log u + 23 / 2)) := by rw [← Real.exp_nat_mul]
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        have e : C * (L + 9 / 10 * L * Real.log u + 23 / 2) =
            K * L * ffun u + 23 / 2 * C := by
          simp only [ffun, hudef]; field_simp; try ring
        rw [e]; nlinarith

omit hh2 hpoly in
lemma W3_le :
    (2 : ℝ) ^ k * ((k * k).choose k : ℝ) * (2 / 25 : ℝ) ^ (h * k) ≤
      Real.exp (-(0.1018 : ℝ) * (k * Real.log k) + 13 * k) := by
  have hK : (0 : ℝ) < k := by linarith
  have hL0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hKL : 0 ≤ (k : ℝ) * Real.log k := mul_nonneg hK.le hL0
  have h2 : (2 : ℝ) ^ k ≤ Real.exp k := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) k
  have hc : ((k * k).choose k : ℝ) ≤ Real.exp (2 * (k * Real.log k)) := by
    have : (k * k).choose k ≤ (k * k) ^ k := Nat.choose_le_pow _ _
    have h' : ((k * k).choose k : ℝ) ≤ ((k : ℝ) * k) ^ k := by exact_mod_cast this
    refine h'.trans (le_of_eq ?_)
    rw [← Real.exp_log (show (0 : ℝ) < k * k by positivity), ← Real.exp_nat_mul,
      Real.log_mul hK.ne' hK.ne']; ring_nf
  have l2 := Real.log_two_gt_d9
  have l12 := log_12_5_ge
  have e1 : Real.log (2 / 25 : ℝ) = - Real.log (25 / 2) := by
    rw [← Real.log_inv]; norm_num
  have l12u : Real.log (25 / 2 : ℝ) ≤ 23 / 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 25 / 2 by norm_num); linarith
  have hlg : Real.log (2 / 25 : ℝ) ≤ -2.525 := by rw [e1]; linarith
  have hlg0 : Real.log (2 / 25 : ℝ) ≤ 0 := by linarith
  have hη : (2 / 25 : ℝ) ^ (h * k) ≤
      Real.exp (k * (9 / 10 * Real.log k * Real.log (2 / 25) + 23 / 2)) := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 / 25 by norm_num), ← Real.exp_nat_mul,
      Real.exp_log (show (0 : ℝ) < 2 / 25 by norm_num)]
    apply Real.exp_le_exp.2
    have a := mul_le_mul_of_nonpos_right hh1 hlg0
    have b : (h : ℝ) * Real.log (2 / 25) ≤ 9 / 10 * Real.log k * Real.log (2 / 25) + 23 / 2 := by
      rw [e1] at a ⊢; nlinarith
    push_cast
    have := mul_le_mul_of_nonneg_left b hK.le
    nlinarith
  calc (2 : ℝ) ^ k * ((k * k).choose k : ℝ) * (2 / 25 : ℝ) ^ (h * k)
      ≤ Real.exp k * Real.exp (2 * (k * Real.log k)) *
          Real.exp (k * (9 / 10 * Real.log k * Real.log (2 / 25) + 23 / 2)) := by
        gcongr
    _ = Real.exp (k + 2 * (k * Real.log k) +
          k * (9 / 10 * Real.log k * Real.log (2 / 25) + 23 / 2)) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hlg hKL
        nlinarith

end GeneralizedUniformServer.Dev.LB.PartCB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset Real
open scoped Nat
lemma E_ge (k h : ℕ) (hk : 1 ≤ k) (hh2 : (h : ℝ) ≤ 9 / 10 * Real.log k) :
    Real.exp ((k : ℝ) * Real.log k / 10 - k) ≤
      (k ! : ℝ) * ((k ! : ℝ) / (k : ℝ) ^ k) ^ h := by
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  have hf := fact_ge_exp k
  have hKk : (k : ℝ) ^ k = Real.exp (k * Real.log k) := by
    rw [Real.exp_nat_mul, Real.exp_log hK]
  have hp : Real.exp (-k) ≤ (k ! : ℝ) / (k : ℝ) ^ k := by
    rw [hKk, le_div_iff₀ (Real.exp_pos _), ← Real.exp_add]
    refine le_of_eq_of_le ?_ hf; ring_nf
  have hph : Real.exp (-(h * k)) ≤ ((k ! : ℝ) / (k : ℝ) ^ k) ^ h := by
    have := pow_le_pow_left₀ (Real.exp_pos _).le hp h
    rw [← Real.exp_nat_mul] at this
    refine le_trans (le_of_eq ?_) this; ring_nf
  have hL0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  calc Real.exp ((k : ℝ) * Real.log k / 10 - k)
      ≤ Real.exp (k * Real.log k - k) * Real.exp (-(h * k)) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_right hh2 hK.le
        nlinarith
    _ ≤ _ := mul_le_mul hf hph (Real.exp_pos _).le (by positivity)

lemma final_ineq (k : ℕ) (hL : 20000 ≤ Real.log k) (S2 W1 W2 W3 : ℝ) (hS0 : 0 ≤ S2)
    (hW1 : W1 ≤ Real.exp (-(0.1031 : ℝ) * (k * Real.log k) + 3 * k))
    (hW2 : W2 ≤ 2 ^ k * Real.exp (-(0.1018 : ℝ) * (k * Real.log k) + 12 * k))
    (hW3 : W3 ≤ Real.exp (-(0.1018 : ℝ) * (k * Real.log k) + 13 * k))
    (hS : S2 ≤ Real.exp (k * Real.log k / 10 + 3 * k)) :
    4 * S2 * (W1 + W2 + W3) < 1 := by
  obtain ⟨hk, -⟩ := big_of_log k hL
  have hK : (0 : ℝ) < k := by linarith
  have hKL : 20000 * (k : ℝ) ≤ k * Real.log k := by nlinarith
  set A := Real.exp (-(0.1018 : ℝ) * (k * Real.log k) + 13 * k) with hAdef
  have h1 : W1 ≤ A := hW1.trans (Real.exp_le_exp.2 (by nlinarith))
  have h2 : W2 ≤ A := by
    have e2 : (2 : ℝ) ^ k ≤ Real.exp k := by
      rw [← Real.exp_one_pow]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) k
    refine hW2.trans ((mul_le_mul_of_nonneg_right e2 (Real.exp_pos _).le).trans (le_of_eq ?_))
    rw [← Real.exp_add, hAdef]; ring_nf
  have hW : W1 + W2 + W3 ≤ 3 * A := by linarith
  by_cases hW0 : 0 ≤ W1 + W2 + W3
  · have hprod : 4 * S2 * (W1 + W2 + W3) ≤
        4 * Real.exp (k * Real.log k / 10 + 3 * k) * (3 * A) :=
      mul_le_mul (by linarith) hW hW0 (by positivity)
    have e : 4 * Real.exp (k * Real.log k / 10 + 3 * k) * (3 * A) =
        12 * Real.exp (-(0.0018 : ℝ) * (k * Real.log k) + 16 * k) := by
      rw [hAdef, show ∀ a b : ℝ, (4 : ℝ) * a * (3 * b) = 12 * (a * b) by intros; ring,
        ← Real.exp_add]
      ring_nf
    have h3 : Real.exp (-(0.0018 : ℝ) * (k * Real.log k) + 16 * k) ≤ Real.exp (-20) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h4 : Real.exp (-20) ≤ 1 / 21 := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp (20 : ℝ)])
    linarith
  · have : 4 * S2 * (W1 + W2 + W3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith

end GeneralizedUniformServer.Dev.LB.PartCB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartCB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
open scoped Nat
variable {k : ℕ}
/-! ## The theorem -/
theorem exists_good : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ F : Sys k (hh k), Good F ∧
      Real.exp ((k : ℝ) * Real.log k / 10 - k) / 2 ≤ (Z F : ℝ) := by
  classical
  obtain ⟨k₀, hk₀⟩ := exists_big
  refine ⟨k₀, fun k hk => ?_⟩
  have hL := hk₀ k hk
  obtain ⟨hk50, hpoly⟩ := big_of_log k hL
  set h := hh k with hhdef
  have hh1 : 9 / 10 * Real.log k - 1 ≤ (h : ℝ) := (hh_gt k).le
  have hh2 : (h : ℝ) ≤ 9 / 10 * Real.log k := hh_le k
  have hk2 : 2 ≤ k := k_ge_two hk50
  have hk1 : 1 ≤ k := by omega
  set SZ : ℝ := ∑ F : Sys k h, (Z F : ℝ) with hSZ
  set M : ℝ := (Fintype.card (Sys k h) : ℝ) with hM
  set E : ℝ := (k.factorial : ℝ) * ((k.factorial : ℝ) / (k : ℝ) ^ k) ^ h with hE
  have hSZE : SZ = M * E := by rw [hSZ, sum_Z, hE]; ring
  have hEge := E_ge k h hk1 hh2
  have hE0 : 0 < E := (Real.exp_pos _).trans_le hEge
  have hM0 : 0 < M := by rw [hM]; exact_mod_cast Fintype.card_pos
  have hSZ0 : 0 < SZ := by rw [hSZE]; positivity
  -- Paley–Zygmund
  set S2 : ℝ := ∑ d ∈ range (k + 1), sd k h d with hS2
  have hpz := pz_count (fun F : Sys k h => (Z F : ℝ)) (fun _ => Nat.cast_nonneg _) (E / 2)
    (by positivity) (by rw [← hSZ, hSZE, ← hM]; linarith)
  rw [← hSZ, sum_Z_sq hk2, ← hS2, ← hSZ] at hpz
  set T := univ.filter fun F : Sys k h => E / 2 ≤ (Z F : ℝ) with hT
  -- bad systems
  set W1 : ℝ := ∑ d ∈ (range (k + 1)).filter
          (fun d : ℕ => (1 / 25 : ℝ) * k ≤ d ∧ (d : ℝ) ≤ (77 / 100 : ℝ) * k), sd k h d with hW1
  set A2 : ℝ := Real.exp (-(0.1018 : ℝ) * (k * Real.log k) + 12 * k) with hA2
  set W3 : ℝ := (2 : ℝ) ^ k * ((k * k).choose k : ℝ) * (2 / 25 : ℝ) ^ (h * k) with hW3
  have hU1 := card_U1 hk2 h
  have hU2 := card_U2 hk2 h A2 (Real.exp_pos _).le
    (fun c hc1 hc2 => b2_le hk50 hh1 c hc1 hc2)
  have hU3 := card_U3 hk2 h
  set U := U1 k h ∪ U2 k h ∪ U3 k h with hU
  have hUc : (U.card : ℝ) ≤ SZ * (W1 + 2 ^ k * A2 + W3) := by
    have : U.card ≤ (U1 k h).card + (U2 k h).card + (U3 k h).card :=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    have : (U.card : ℝ) ≤ (U1 k h).card + (U2 k h).card + (U3 k h).card := by
      exact_mod_cast this
    rw [← hW1] at hU1
    rw [← hW3] at hU3
    nlinarith
  have hfin := final_ineq k hL S2 W1 (2 ^ k * A2) W3
    (Finset.sum_nonneg fun d _ => sd_nonneg hk1 h d) (W1_le hk50 hh1 hh2 hpoly) le_rfl
    (W3_le hk50 hh1) (S2_le hk50 hh1 hh2 hpoly)
  -- `|U| < |T|`
  have hS2pos : 0 < S2 := by
    by_contra hneg
    have : (T.card : ℝ) * (S2 * SZ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
        (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hSZ0.le)
    nlinarith
  have hTlow : SZ ≤ 4 * S2 * T.card := by
    have : SZ * SZ ≤ (4 * S2 * T.card) * SZ := by nlinarith
    exact le_of_mul_le_mul_right this hSZ0
  have hlt : (U.card : ℝ) < T.card := by
    have h1 : 4 * S2 * U.card ≤ 4 * S2 * (SZ * (W1 + 2 ^ k * A2 + W3)) :=
      mul_le_mul_of_nonneg_left hUc (by positivity)
    have h2 : 4 * S2 * (SZ * (W1 + 2 ^ k * A2 + W3)) < SZ := by
      have : 4 * S2 * (SZ * (W1 + 2 ^ k * A2 + W3)) =
          SZ * (4 * S2 * (W1 + 2 ^ k * A2 + W3)) := by ring
      rw [this]; nlinarith
    have h3 : 4 * S2 * U.card < 4 * S2 * T.card := by linarith
    exact lt_of_mul_lt_mul_left h3 (by positivity)
  obtain ⟨F, hFT, hFU⟩ := Finset.exists_mem_notMem_of_card_lt_card (by exact_mod_cast hlt)
  refine ⟨F, ?_, ?_⟩
  · rw [hU, mem_union, mem_union, not_or, not_or] at hFU
    exact good_of_not_mem hk1 F hFU.1.1 hFU.1.2 hFU.2
  · rw [hT, mem_filter] at hFT
    linarith [hFT.2]

end GeneralizedUniformServer.Dev.LB.PartCB
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias exists_good := GeneralizedUniformServer.Dev.LB.PartCB.exists_good

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section
namespace GeneralizedUniformServer.Dev.LB.PartA4
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.LB Finset
theorem lower_main :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ (a : Config (fun _ : Fin k => Fin k))
        (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Config (fun _ : Fin k => Fin k))),
        IsServing Serves A →
        ∀ γ c : ℝ,
          (∀ ρ : List (Config (fun _ : Fin k => Fin k)),
            (genExpectedCost A a ρ).toReal ≤ γ * (optCost a ρ : ℝ) + c) →
          (1 / 20 : ℝ) * (k : ℝ) * Real.log (k : ℝ) ≤ γ := by
  obtain ⟨k1, hk1⟩ := one_phase
  obtain ⟨k2, hk2⟩ := exists_good
  refine ⟨max (max k1 k2) 2, ?_⟩
  intro k hk a A hA γ c hc
  have hk1' : k1 ≤ k := by omega
  have hk2' : k2 ≤ k := by omega
  have hk2le : 2 ≤ k := by omega
  obtain ⟨F, hF, hZ⟩ := hk2 k hk2'
  obtain ⟨G⟩ := goodSet_of_good hk2le F hF hZ
  have hC : Compet A a γ c := hc
  set K : ℝ := (k : ℝ) ^ 2 * Real.log k / 20 with hK
  have avg : ∀ ρ0 : List (Cfg k), ∃ ρ' : List (Cfg k), (∃ q, ∀ r ∈ ρ', Serves q r) ∧
      ecost A a ρ0 + K ≤ ecost A a (ρ0 ++ ρ') := by
    intro ρ0
    obtain ⟨P, hP0, hP1, hPs, hPe⟩ := hk1 k hk1' G a A hA γ c hC ρ0
    obtain ⟨ρ', hρ', hge⟩ := exists_ge_of_avg P hP0 hP1 (fun ρ' => ecost A a (ρ0 ++ ρ'))
      (ecost A a ρ0 + K) hPe
    exact ⟨ρ', hPs ρ' hρ', hge⟩
  have main : ∀ L : ℕ, ∃ ρ : List (Cfg k), (L : ℝ) * K ≤ ecost A a ρ ∧
      (optCost a ρ : ℝ) ≤ (L : ℝ) * k := by
    intro L
    induction L with
    | zero =>
      refine ⟨[], ?_, ?_⟩
      · simp only [Nat.cast_zero, zero_mul]
        exact ENNReal.toReal_nonneg
      · rw [opt_nil]; simp
    | succ L ih =>
      obtain ⟨ρ, h1, h2⟩ := ih
      obtain ⟨ρ', ⟨q, hq⟩, he⟩ := avg ρ
      refine ⟨ρ ++ ρ', ?_, ?_⟩
      · push_cast; linarith
      · have h3 : (optCost a (ρ ++ ρ') : ℝ) ≤ (optCost a ρ : ℝ) + k := by
          exact_mod_cast opt_append (by omega) a ρ ρ' q hq
        push_cast; linarith
  by_contra hlt
  push Not at hlt
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  set g := max γ 0 with hg
  have hgl : g < 1 / 20 * (k : ℝ) * Real.log k := max_lt hlt (by positivity)
  set D := K - g * k with hD
  have hDe : D = k * (1 / 20 * (k : ℝ) * Real.log k - g) := by rw [hD, hK]; ring
  have hDpos : 0 < D := by rw [hDe]; exact mul_pos hkpos (by linarith)
  obtain ⟨L, hL⟩ := exists_nat_gt (c / D)
  rw [div_lt_iff₀ hDpos] at hL
  obtain ⟨ρ, h1, h2⟩ := main L
  have h3 := hC ρ
  have h4 : γ * (optCost a ρ : ℝ) ≤ g * ((L : ℝ) * k) :=
    calc γ * (optCost a ρ : ℝ) ≤ g * (optCost a ρ : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ g * ((L : ℝ) * k) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
  have h5 : (L : ℝ) * D = L * K - g * (L * k) := by rw [hD]; ring
  linarith

end GeneralizedUniformServer.Dev.LB.PartA4
end
end

section
noncomputable section
namespace GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
alias lower_main := GeneralizedUniformServer.Dev.LB.PartA4.lower_main

end GeneralizedUniformServer.Dev.LB
end
end

section
set_option autoImplicit false
noncomputable section

end
end

section
noncomputable section
open GeneralizedUniformServer
open GeneralizedUniformServer.Dev
open GeneralizedUniformServer.Dev.LB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open Finset
variable {k : ℕ}
theorem solution :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ (a : Config (fun _ : Fin k => Fin k))
        (A : GenOnlineAlg (fun _ : Fin k => Fin k) (Config (fun _ : Fin k => Fin k))),
        IsServing Serves A →
        ∀ γ c : ℝ,
          (∀ ρ : List (Config (fun _ : Fin k => Fin k)),
            (genExpectedCost A a ρ).toReal ≤ γ * (optCost a ρ : ℝ) + c) →
          (1 / 20 : ℝ) * (k : ℝ) * Real.log (k : ℝ) ≤ γ := by
  exact GeneralizedUniformServer.Dev.LB.lower_main
end
end
