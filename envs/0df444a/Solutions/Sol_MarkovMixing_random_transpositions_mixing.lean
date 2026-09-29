-- Prove2me | solution 1 for MarkovMixing.random_transpositions_mixing
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T20:59:33.894584+00:00
-- url     : https://prove2.me/submissions/569b62c3-7e69-4ae9-b101-55b62f376f5d

import Definitions.Def_mm_shuffle
import Definitions.Def_mm_stopping
import Theorems.Thm_MarkovMixing_strong_stationary_bound
import Theorems.Thm_MarkovMixing_group_walk_uniform_stationary
import Theorems.Thm_MarkovMixing_group_walk_irreducible_iff
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MarkovMixing
noncomputable section
open scoped BigOperators
open Finset

variable {n : ℕ}

def markUpd (M : Finset (Fin n)) (L R : Fin n) : Finset (Fin n) :=
  if R ∉ M ∧ (L = R ∨ L ∈ M) then insert R M else M

def swapCnt (n : ℕ) (g : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => Equiv.swap p.1 p.2 = g).card

def markCnt (M M' : Finset (Fin n)) (g : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
    Equiv.swap p.1 p.2 = g ∧ markUpd M p.1 p.2 = M').card

def markKer (M M' : Finset (Fin n)) (g : Equiv.Perm (Fin n)) : ℝ :=
  (markCnt M M' g : ℝ) / (swapCnt n g : ℝ)

lemma swap_eq_swap_of_ne {i j L R : Fin n} (hij : i ≠ j)
    (h : Equiv.swap L R = Equiv.swap i j) :
    (L = i ∧ R = j) ∨ (L = j ∧ R = i) := by
  have h1 : Equiv.swap L R i = j := by rw [h]; exact Equiv.swap_apply_left i j
  rcases eq_or_ne i L with rfl | hiL
  · left
    refine ⟨rfl, ?_⟩
    rw [Equiv.swap_apply_left] at h1; exact h1
  · rcases eq_or_ne i R with rfl | hiR
    · right
      rw [Equiv.swap_apply_right] at h1
      exact ⟨h1, rfl⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hiL hiR] at h1
      exact absurd h1 hij

lemma swapCnt_one : swapCnt n 1 = n := by
  classical
  have hinj : Function.Injective (fun i : Fin n => (i, i)) := fun a b h => (Prod.mk.injEq .. ▸ h).1
  have : (Finset.univ.filter fun p : Fin n × Fin n => Equiv.swap p.1 p.2 = 1)
      = Finset.univ.map ⟨fun i : Fin n => (i, i), hinj⟩ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro h
      have : p.1 = p.2 := by
        by_contra hne
        have h2 := Equiv.swap_apply_left p.1 p.2
        rw [h] at h2
        simp only [Equiv.Perm.coe_one, id_eq] at h2
        exact hne h2
      exact ⟨p.1, Prod.ext rfl this⟩
    · rintro ⟨i, -, rfl⟩
      show Equiv.swap i i = 1
      simp only [Equiv.swap_self]
      rfl
  rw [swapCnt, this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma swapCnt_swap {i j : Fin n} (hij : i ≠ j) : swapCnt n (Equiv.swap i j) = 2 := by
  classical
  have : (Finset.univ.filter fun p : Fin n × Fin n => Equiv.swap p.1 p.2 = Equiv.swap i j)
      = {(i, j), (j, i)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      rcases swap_eq_swap_of_ne hij h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact Prod.ext h1 h2
      · right; exact Prod.ext h1 h2
    · rintro (rfl | rfl)
      · rfl
      · exact Equiv.swap_comm j i
  rw [swapCnt, this, Finset.card_insert_of_notMem (by simp [Prod.ext_iff, hij, Ne.symm hij]),
    Finset.card_singleton]

lemma transpositionDist_eq (n : ℕ) (g : Equiv.Perm (Fin n)) :
    transpositionDist n g = (swapCnt n g : ℝ) / (n : ℝ) ^ 2 := by
  classical
  unfold transpositionDist
  by_cases h1 : g = 1
  · subst h1
    rw [if_pos rfl, swapCnt_one]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp; try ring
  · rw [if_neg h1]
    by_cases h2 : ∃ i j : Fin n, i ≠ j ∧ g = Equiv.swap i j
    · rw [if_pos h2]
      obtain ⟨i, j, hij, rfl⟩ := h2
      rw [swapCnt_swap hij]; norm_num
    · rw [if_neg h2]
      have : swapCnt n g = 0 := by
        rw [swapCnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨L, R⟩ -
        simp only
        intro h
        rcases eq_or_ne L R with rfl | hLR
        · exact h1 (by rw [← h, Equiv.swap_self]; rfl)
        · exact h2 ⟨L, R, hLR, h.symm⟩
      rw [this]; norm_num


/-- `markUpd` never removes marks. -/
lemma subset_markUpd (M : Finset (Fin n)) (L R : Fin n) : M ⊆ markUpd M L R := by
  unfold markUpd; split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

/-- Once every card is marked, the mark set no longer changes. -/
lemma markUpd_univ (L R : Fin n) : markUpd (Finset.univ) L R = Finset.univ := by
  unfold markUpd; simp

lemma markCnt_le_swapCnt (M M' : Finset (Fin n)) (g : Equiv.Perm (Fin n)) :
    markCnt M M' g ≤ swapCnt n g := by
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact hp.1

lemma sum_markCnt (M : Finset (Fin n)) (g : Equiv.Perm (Fin n)) :
    ∑ M' : Finset (Fin n), markCnt M M' g = swapCnt n g := by
  classical
  unfold markCnt swapCnt
  rw [← Finset.card_biUnion]
  · congr 1
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨M', h1⟩; exact h1.1
    · intro h; exact ⟨markUpd M p.1 p.2, h, rfl⟩
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro p ⟨-, h1⟩ ⟨-, h2⟩
    exact hab (h1 ▸ h2 ▸ rfl)

lemma markKer_nonneg (M M' : Finset (Fin n)) (g : Equiv.Perm (Fin n)) :
    0 ≤ markKer M M' g := by
  unfold markKer; positivity

lemma sum_markKer_le_one (M : Finset (Fin n)) (g : Equiv.Perm (Fin n)) :
    ∑ M' : Finset (Fin n), markKer M M' g ≤ 1 := by
  unfold markKer
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← div_eq_mul_inv]
  rcases Nat.eq_zero_or_pos (swapCnt n g) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast le_of_eq (by exact_mod_cast congrArg (Nat.cast (R := ℝ)) (sum_markCnt M g))

lemma markKer_univ_univ (g : Equiv.Perm (Fin n)) (hg : 0 < swapCnt n g) :
    markKer (Finset.univ) (Finset.univ) g = 1 := by
  unfold markKer
  have : markCnt (Finset.univ : Finset (Fin n)) Finset.univ g = swapCnt n g := by
    unfold markCnt swapCnt
    congr 1
    apply Finset.filter_congr
    intro p _
    simp [markUpd_univ]
  rw [this, div_self (by exact_mod_cast hg.ne')]

/-- The product identity relating the increment law and the conditional mark law. -/
lemma transpositionDist_mul_markKer (M M' : Finset (Fin n)) (g : Equiv.Perm (Fin n)) :
    transpositionDist n g * markKer M M' g = (markCnt M M' g : ℝ) / (n : ℝ) ^ 2 := by
  rw [transpositionDist_eq, markKer]
  rcases Nat.eq_zero_or_pos (swapCnt n g) with h | h
  · have h0 : markCnt M M' g = 0 := Nat.le_zero.mp (h ▸ markCnt_le_swapCnt M M' g)
    simp [h, h0]
  · have hs : (swapCnt n g : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp
    try ring

/-! ### The augmented chain on (deck, marks) -/

section Augmented

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma pathWeight_snoc (P : Matrix V V ℝ) (m : ℕ) (p : Fin (m+1) → V) (v : V) :
    pathWeight P (Fin.snoc p v : Fin (m+2) → V)
      = pathWeight P p * P (p (Fin.last m)) v := by
  rw [pathWeight, pathWeight, Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [Fin.snoc_castSucc, Fin.succ_castSucc]
  · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

private lemma sum_comm3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := by
  have h1 : (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
  rw [h1, Finset.sum_comm]

private lemma snoc_split (m : ℕ) (F : (Fin (m+2) → V) → ℝ) :
    ∑ ω : Fin (m+2) → V, F ω = ∑ p : Fin (m+1) → V, ∑ v : V, F (Fin.snoc p v) := by
  classical
  have hEq := Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (m+2) => V))
    (fun q : V × (Fin (m+1) → V) => F (Fin.snoc q.2 q.1 : Fin (m+2) → V))
    (fun ω : Fin (m+2) → V => F ω) (fun q => rfl)
  rw [← hEq, Fintype.sum_prod_type, Finset.sum_comm]

end Augmented

/-- One step of the augmented chain on (deck, mark set). -/
def augKer (n : ℕ) (a b : Equiv.Perm (Fin n) × Finset (Fin n)) : ℝ :=
  (markCnt a.2 b.2 (b.1 * a.1⁻¹) : ℝ) / (n : ℝ) ^ 2

/-- The law of the augmented chain at time `t`, started from `(x, ∅)`. -/
def augLaw (n : ℕ) (x : Equiv.Perm (Fin n)) :
    ℕ → (Equiv.Perm (Fin n) × Finset (Fin n)) → ℝ
  | 0, b => if b = (x, ∅) then 1 else 0
  | (t+1), b => ∑ a : Equiv.Perm (Fin n) × Finset (Fin n), augLaw n x t a * augKer n a b

/-- The conditional law of the mark set at time `t` given the deck trajectory `ω`. -/
def mp (n : ℕ) : ∀ t : ℕ, (Fin (t+1) → Equiv.Perm (Fin n)) → Finset (Fin n) → ℝ
  | 0, _, M => if M = ∅ then 1 else 0
  | (t+1), ω, M' => ∑ M : Finset (Fin n), mp n t (Fin.init ω) M *
      markKer M M' (ω (Fin.last (t+1)) * (ω ((Fin.last t).castSucc))⁻¹)

lemma mp_succ (n t : ℕ) (ω : Fin (t+2) → Equiv.Perm (Fin n)) (M' : Finset (Fin n)) :
    mp n (t+1) ω M' = ∑ M : Finset (Fin n), mp n t (Fin.init ω) M *
      markKer M M' (ω (Fin.last (t+1)) * (ω ((Fin.last t).castSucc))⁻¹) := rfl

lemma mp_snoc (n t : ℕ) (p : Fin (t+1) → Equiv.Perm (Fin n)) (v : Equiv.Perm (Fin n))
    (M' : Finset (Fin n)) :
    mp n (t+1) (Fin.snoc p v : Fin (t+2) → Equiv.Perm (Fin n)) M'
      = ∑ M : Finset (Fin n), mp n t p M * markKer M M' (v * (p (Fin.last t))⁻¹) := by
  rw [mp_succ]
  have h1 : (Fin.snoc p v : Fin (t+2) → Equiv.Perm (Fin n)) (Fin.last (t+1)) = v :=
    Fin.snoc_last _ _
  have h2 : (Fin.snoc p v : Fin (t+2) → Equiv.Perm (Fin n)) ((Fin.last t).castSucc)
      = p (Fin.last t) := Fin.snoc_castSucc _ _ _
  rw [h1, h2]
  refine Finset.sum_congr rfl (fun M _ => ?_)
  congr 2
  simp

/-- The joint law of the deck at time `t` and the mark set, as a sum over trajectories. -/
def pathMark (n : ℕ) (x y : Equiv.Perm (Fin n)) (M : Finset (Fin n)) (t : ℕ) : ℝ :=
  ∑ ω : Fin (t+1) → Equiv.Perm (Fin n),
    if ω 0 = x ∧ ω (Fin.last t) = y then
      pathWeight (randomTranspositions n) ω * mp n t ω M else 0

lemma pathMark_eq_augLaw (n : ℕ) (x : Equiv.Perm (Fin n)) :
    ∀ (t : ℕ) (y : Equiv.Perm (Fin n)) (M : Finset (Fin n)),
      pathMark n x y M t = augLaw n x t (y, M) := by
  intro t
  induction t with
  | zero =>
    intro y M
    unfold pathMark augLaw
    have : ∀ ω : Fin 1 → Equiv.Perm (Fin n),
        (if ω 0 = x ∧ ω (Fin.last 0) = y then
          pathWeight (randomTranspositions n) ω * mp n 0 ω M else 0)
        = (if ω 0 = x ∧ ω 0 = y then (if M = ∅ then (1:ℝ) else 0) else 0) := by
      intro ω
      have hl : (Fin.last 0 : Fin 1) = 0 := rfl
      rw [hl, pathWeight]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      rfl
    rw [Finset.sum_congr rfl (fun ω _ => this ω)]
    have hev := Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Equiv.Perm (Fin n)))
      (fun ω : Fin 1 → Equiv.Perm (Fin n) =>
        (if ω 0 = x ∧ ω 0 = y then (if M = ∅ then (1:ℝ) else 0) else 0))
      (fun u : Equiv.Perm (Fin n) => (if u = x ∧ u = y then (if M = ∅ then (1:ℝ) else 0) else 0))
      (fun ω => rfl)
    rw [hev]
    by_cases hM : M = ∅
    · subst hM
      by_cases hxy : y = x
      · subst hxy
        simp only [Prod.mk.injEq, and_true, if_pos rfl]
        rw [Finset.sum_eq_single y]
        · simp
        · intro b _ hb; simp [hb]
        · intro hb; exact absurd (Finset.mem_univ y) hb
      · simp only [Prod.mk.injEq, and_true, if_pos rfl, if_neg hxy]
        refine Finset.sum_eq_zero (fun u _ => ?_)
        rw [if_neg]
        rintro ⟨rfl, rfl⟩; exact hxy rfl
    · simp [hM]
  | succ t ih =>
    intro y M'
    unfold pathMark
    rw [snoc_split]
    have hterm : ∀ (p : Fin (t+1) → Equiv.Perm (Fin n)) (v : Equiv.Perm (Fin n)),
        (if (Fin.snoc p v : Fin (t+2) → _) 0 = x ∧
            (Fin.snoc p v : Fin (t+2) → _) (Fin.last (t+1)) = y then
          pathWeight (randomTranspositions n) (Fin.snoc p v : Fin (t+2) → _)
            * mp n (t+1) (Fin.snoc p v) M' else 0)
        = (if p 0 = x ∧ v = y then
            pathWeight (randomTranspositions n) p *
              ∑ M : Finset (Fin n), mp n t p M *
                ((randomTranspositions n) (p (Fin.last t)) v *
                  markKer M M' (v * (p (Fin.last t))⁻¹)) else 0) := by
      intro p v
      have h0 : (Fin.snoc p v : Fin (t+2) → Equiv.Perm (Fin n)) 0 = p 0 := by
        have : (0 : Fin (t+2)) = ((0 : Fin (t+1)).castSucc) := rfl
        rw [this, Fin.snoc_castSucc]
      have h1 : (Fin.snoc p v : Fin (t+2) → Equiv.Perm (Fin n)) (Fin.last (t+1)) = v :=
        Fin.snoc_last _ _
      have h2 : (Fin.snoc p v : Fin (t+2) → Equiv.Perm (Fin n)) ((Fin.last t).castSucc)
          = p (Fin.last t) := Fin.snoc_castSucc _ _ _
      rw [h0, h1]
      by_cases hc : p 0 = x ∧ v = y
      · rw [if_pos hc, if_pos hc, pathWeight_snoc, mp_snoc, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun M _ => ?_)
        ring
      · rw [if_neg hc, if_neg hc]
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun v _ => hterm p v))]
    have hker : ∀ (u : Equiv.Perm (Fin n)) (M : Finset (Fin n)),
        (randomTranspositions n) u y * markKer M M' (y * u⁻¹) = augKer n (u, M) (y, M') := by
      intro u M
      show transpositionDist n (y * u⁻¹) * markKer M M' (y * u⁻¹) = _
      rw [transpositionDist_mul_markKer]
      rfl
    have hv : ∀ p : Fin (t+1) → Equiv.Perm (Fin n),
        (∑ v : Equiv.Perm (Fin n), if p 0 = x ∧ v = y then
          pathWeight (randomTranspositions n) p * ∑ M : Finset (Fin n), mp n t p M *
            ((randomTranspositions n) (p (Fin.last t)) v * markKer M M' (v * (p (Fin.last t))⁻¹))
          else 0)
        = if p 0 = x then pathWeight (randomTranspositions n) p *
            ∑ M : Finset (Fin n), mp n t p M * augKer n (p (Fin.last t), M) (y, M') else 0 := by
      intro p
      by_cases hp : p 0 = x
      · rw [if_pos hp, Finset.sum_eq_single y]
        · rw [if_pos ⟨hp, rfl⟩]
          congr 1
          exact Finset.sum_congr rfl (fun M _ => by rw [hker])
        · intro b _ hb; rw [if_neg (by tauto)]
        · intro hb; exact absurd (Finset.mem_univ y) hb
      · rw [if_neg hp]
        exact Finset.sum_eq_zero (fun v _ => by rw [if_neg (by tauto)])
    rw [Finset.sum_congr rfl (fun p _ => hv p)]
    rw [augLaw, Fintype.sum_prod_type]
    have hrw : ∀ (u : Equiv.Perm (Fin n)) (M : Finset (Fin n)),
        augLaw n x t (u, M) * augKer n (u, M) (y, M')
        = (∑ p : Fin (t+1) → Equiv.Perm (Fin n),
            if p 0 = x ∧ p (Fin.last t) = u then
              pathWeight (randomTranspositions n) p * mp n t p M else 0)
          * augKer n (u, M) (y, M') := by
      intro u M; rw [← ih u M]; rfl
    rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun M _ => hrw u M))]
    simp only [Finset.sum_mul]
    rw [sum_comm3 (fun (u : Equiv.Perm (Fin n)) (M : Finset (Fin n))
      (p : Fin (t+1) → Equiv.Perm (Fin n)) =>
        (if p 0 = x ∧ p (Fin.last t) = u then
          pathWeight (randomTranspositions n) p * mp n t p M else 0) * augKer n (u, M) (y, M'))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    symm
    by_cases hp : p 0 = x
    · rw [if_pos hp, Finset.mul_sum]
      rw [Finset.sum_eq_single (p (Fin.last t))]
      · refine Finset.sum_congr rfl (fun M _ => ?_)
        rw [if_pos ⟨hp, rfl⟩]; ring
      · intro b _ hb
        exact Finset.sum_eq_zero (fun M _ => by rw [if_neg (by tauto), zero_mul])
      · intro hb; exact absurd (Finset.mem_univ (p (Fin.last t))) hb
    · rw [if_neg hp]
      exact Finset.sum_eq_zero (fun u _ =>
        Finset.sum_eq_zero (fun M _ => by rw [if_neg (by tauto), zero_mul]))


/-! ### The one-step decomposition of the augmented law -/

lemma markCnt_eq_sum (M M' : Finset (Fin n)) (g : Equiv.Perm (Fin n)) :
    (markCnt M M' g : ℝ)
      = ∑ q : Fin n × Fin n,
          if Equiv.swap q.1 q.2 = g ∧ markUpd M q.1 q.2 = M' then (1:ℝ) else 0 := by
  classical
  rw [markCnt, ← Finset.sum_boole]

lemma swap_eq_mul_inv_iff (a b : Fin n) (w u : Equiv.Perm (Fin n)) :
    Equiv.swap a b = w * u⁻¹ ↔ u = Equiv.swap a b * w := by
  constructor
  · intro h
    have : Equiv.swap a b * u = w := by
      rw [h]; group
    rw [← this, ← mul_assoc, Equiv.swap_mul_self, one_mul]
  · intro h
    subst h
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, Equiv.swap_inv]

lemma augLaw_succ (n : ℕ) (x w : Equiv.Perm (Fin n)) (t : ℕ) (M' : Finset (Fin n)) :
    augLaw n x (t+1) (w, M')
      = (∑ M : Finset (Fin n), ∑ q : Fin n × Fin n,
          (if markUpd M q.1 q.2 = M' then
            augLaw n x t (Equiv.swap q.1 q.2 * w, M) else 0)) / (n:ℝ)^2 := by
  classical
  have key : ∀ M : Finset (Fin n),
      (∑ u : Equiv.Perm (Fin n), augLaw n x t (u, M) * augKer n (u, M) (w, M'))
        = (∑ q : Fin n × Fin n,
            if markUpd M q.1 q.2 = M' then
              augLaw n x t (Equiv.swap q.1 q.2 * w, M) else 0) / (n:ℝ)^2 := by
    intro M
    have h1 : (∑ u : Equiv.Perm (Fin n), augLaw n x t (u, M) * augKer n (u, M) (w, M'))
        = (∑ u : Equiv.Perm (Fin n), ∑ q : Fin n × Fin n,
            augLaw n x t (u, M) *
              (if Equiv.swap q.1 q.2 = w * u⁻¹ ∧ markUpd M q.1 q.2 = M' then (1:ℝ) else 0))
          / (n:ℝ)^2 := by
      simp only [augKer, markCnt_eq_sum, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun q _ => by ring))
    rw [h1]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hm : markUpd M q.1 q.2 = M'
    · rw [if_pos hm]
      rw [Finset.sum_eq_single (Equiv.swap q.1 q.2 * w)]
      · rw [if_pos ⟨(swap_eq_mul_inv_iff q.1 q.2 w _).mpr rfl, hm⟩, mul_one]
      · intro b _ hb
        rw [if_neg (by rintro ⟨h1, -⟩; exact hb ((swap_eq_mul_inv_iff q.1 q.2 w b).mp h1)),
          mul_zero]
      · intro hb; exact absurd (Finset.mem_univ _) hb
    · rw [if_neg hm]
      refine Finset.sum_eq_zero (fun u _ => ?_)
      rw [if_neg (by rintro ⟨-, h2⟩; exact hm h2), mul_zero]
  rw [augLaw, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun M _ => key M)]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]

/-! ### Permutations supported on the marked set -/

/-- `ρ` moves only cards in `M`. -/
def SuppIn (ρ : Equiv.Perm (Fin n)) (M : Finset (Fin n)) : Prop := ∀ c, c ∉ M → ρ c = c

lemma SuppIn.mem_iff {ρ : Equiv.Perm (Fin n)} {M : Finset (Fin n)} (h : SuppIn ρ M)
    (c : Fin n) : ρ c ∈ M ↔ c ∈ M := by
  constructor
  · intro hc
    by_contra hcM
    rw [h c hcM] at hc; exact hcM hc
  · intro hc
    by_contra hd
    have := h (ρ c) hd
    exact hd (by rw [ρ.injective this]; exact hc)

lemma SuppIn.one (M : Finset (Fin n)) : SuppIn (1 : Equiv.Perm (Fin n)) M := fun _ _ => rfl

lemma SuppIn.mul {ρ σ : Equiv.Perm (Fin n)} {M : Finset (Fin n)}
    (hρ : SuppIn ρ M) (hσ : SuppIn σ M) : SuppIn (ρ * σ) M := by
  intro c hc
  show ρ (σ c) = c
  rw [hσ c hc, hρ c hc]

lemma SuppIn.swap {a b : Fin n} {M : Finset (Fin n)} (ha : a ∈ M) (hb : b ∈ M) :
    SuppIn (Equiv.swap a b) M := by
  intro c hc
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hc (h ▸ ha)) (fun h => hc (h ▸ hb))

lemma SuppIn.mono {ρ : Equiv.Perm (Fin n)} {M N : Finset (Fin n)} (hMN : M ⊆ N)
    (h : SuppIn ρ M) : SuppIn ρ N := fun c hc => h c (fun hcM => hc (hMN hcM))

lemma SuppIn.erase {ρ : Equiv.Perm (Fin n)} {M : Finset (Fin n)} {R : Fin n}
    (h : SuppIn ρ M) (hR : ρ R = R) : SuppIn ρ (M.erase R) := by
  intro c hc
  rcases eq_or_ne c R with rfl | hcR
  · exact hR
  · exact h c (fun hcM => hc (Finset.mem_erase.mpr ⟨hcR, hcM⟩))

/-- The `M`'s that `markUpd` sends to a prescribed `M'`. -/
lemma markUpd_eq_iff (M M' : Finset (Fin n)) (L R : Fin n) :
    markUpd M L R = M' ↔
      (M = M' ∧ markUpd M' L R = M') ∨ (R ∈ M' ∧ L ∈ M' ∧ M = M'.erase R) := by
  classical
  unfold markUpd
  constructor
  · intro h
    by_cases hc : R ∉ M ∧ (L = R ∨ L ∈ M)
    · rw [if_pos hc] at h
      subst h
      right
      refine ⟨Finset.mem_insert_self _ _, ?_, ?_⟩
      · rcases hc.2 with rfl | hL
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem hL
      · rw [Finset.erase_insert hc.1]
    · rw [if_neg hc] at h
      subst h
      exact Or.inl ⟨rfl, by rw [if_neg hc]⟩
  · rintro (⟨rfl, h⟩ | ⟨hR, hL, rfl⟩)
    · exact h
    · have h1 : R ∉ M'.erase R := Finset.notMem_erase _ _
      have h2 : L = R ∨ L ∈ M'.erase R := by
        rcases eq_or_ne L R with rfl | hLR
        · exact Or.inl rfl
        · exact Or.inr (Finset.mem_erase.mpr ⟨hLR, hL⟩)
      rw [if_pos ⟨h1, h2⟩, Finset.insert_erase hR]

/-! ### Splitting the one-step sum into "no new mark" and "new mark" parts -/

lemma markUpd_self_iff (M : Finset (Fin n)) (L R : Fin n) :
    markUpd M L R = M ↔ ¬(R ∉ M ∧ (L = R ∨ L ∈ M)) := by
  classical
  unfold markUpd
  constructor
  · intro h hc
    rw [if_pos hc] at h
    exact hc.1 (h ▸ Finset.mem_insert_self R M)
  · intro hc; rw [if_neg hc]

lemma sum_markUpd_split (M' : Finset (Fin n)) (L R : Fin n) (g : Finset (Fin n) → ℝ) :
    (∑ M : Finset (Fin n), if markUpd M L R = M' then g M else 0)
    = (if markUpd M' L R = M' then g M' else 0)
      + (if R ∈ M' ∧ L ∈ M' then g (M'.erase R) else 0) := by
  classical
  by_cases hR : R ∈ M'
  · have hne : M'.erase R ≠ M' := by
      intro h
      exact Finset.notMem_erase R M' (by rw [h]; exact hR)
    have hself : markUpd M' L R = M' := by
      rw [markUpd_self_iff]; tauto
    have hzero : ∀ M ∈ (Finset.univ : Finset (Finset (Fin n))),
        M ∉ ({M', M'.erase R} : Finset (Finset (Fin n))) →
        (if markUpd M L R = M' then g M else 0) = 0 := by
      intro M _ hM
      rw [if_neg]
      intro h
      rcases (markUpd_eq_iff M M' L R).mp h with ⟨h1, -⟩ | ⟨-, -, h3⟩
      · exact hM (by simp [h1])
      · exact hM (by simp [h3])
    rw [← Finset.sum_subset (Finset.subset_univ ({M', M'.erase R} : Finset (Finset (Fin n)))) hzero]
    rw [Finset.sum_pair (Ne.symm hne), if_pos hself]
    have herase : markUpd (M'.erase R) L R = M' ↔ L ∈ M' := by
      rw [markUpd_eq_iff]
      constructor
      · rintro (⟨h1, -⟩ | ⟨-, h2, -⟩)
        · exact absurd h1 hne
        · exact h2
      · intro hL; exact Or.inr ⟨hR, hL, rfl⟩
    by_cases hL : L ∈ M'
    · rw [if_pos (herase.mpr hL), if_pos ⟨hR, hL⟩]
    · rw [if_neg (fun h => hL (herase.mp h)), if_neg (by tauto), add_zero]
  · have herase : M'.erase R = M' := Finset.erase_eq_of_notMem hR
    have hzero : ∀ M ∈ (Finset.univ : Finset (Finset (Fin n))),
        M ∉ ({M'} : Finset (Finset (Fin n))) →
        (if markUpd M L R = M' then g M else 0) = 0 := by
      intro M _ hM
      rw [if_neg]
      intro h
      rcases (markUpd_eq_iff M M' L R).mp h with ⟨h1, -⟩ | ⟨h2, -, -⟩
      · exact hM (by simp [h1])
      · exact hR h2
    rw [← Finset.sum_subset (Finset.subset_univ ({M'} : Finset (Finset (Fin n)))) hzero]
    rw [Finset.sum_singleton, if_neg (fun h : R ∈ M' ∧ L ∈ M' => hR h.1), add_zero]

/-! ### Invariance of the "new mark" sum -/

lemma newMark_invariant (n : ℕ) (x : Equiv.Perm (Fin n)) (t : ℕ) (M' : Finset (Fin n))
    (R : Fin n) (hR : R ∈ M')
    (IH : ∀ (σ z : Equiv.Perm (Fin n)), SuppIn σ (M'.erase R) →
      augLaw n x t (σ * z, M'.erase R) = augLaw n x t (z, M'.erase R))
    (ρ w : Equiv.Perm (Fin n)) (hρ : SuppIn ρ M') :
    ∑ L ∈ M', augLaw n x t (Equiv.swap L R * (ρ * w), M'.erase R)
      = ∑ L ∈ M', augLaw n x t (Equiv.swap L R * w, M'.erase R) := by
  classical
  -- `π` fixes `R` and `ρ = swap R (ρ R) * π`
  set c : Fin n := ρ R with hc
  have hcM : c ∈ M' := (hρ.mem_iff R).mpr hR
  set π : Equiv.Perm (Fin n) := Equiv.swap R c * ρ with hπ
  have hπR : π R = R := by
    show Equiv.swap R c (ρ R) = R
    rw [← hc, Equiv.swap_apply_right]
  have hπsupp : SuppIn π M' := SuppIn.mul (SuppIn.swap hR hcM) hρ
  have hπe : SuppIn π (M'.erase R) := hπsupp.erase hπR
  have hρeq : ρ = Equiv.swap R c * π := by
    rw [hπ, ← mul_assoc, Equiv.swap_mul_self, one_mul]
  -- Step 1: invariance under `π`
  have step1 : ∀ v : Equiv.Perm (Fin n),
      ∑ L ∈ M', augLaw n x t (Equiv.swap L R * (π * v), M'.erase R)
        = ∑ L ∈ M', augLaw n x t (Equiv.swap L R * v, M'.erase R) := by
    intro v
    have hterm : ∀ L : Fin n, augLaw n x t (Equiv.swap L R * (π * v), M'.erase R)
        = augLaw n x t (Equiv.swap (π⁻¹ L) R * v, M'.erase R) := by
      intro L
      have hπinvR : π⁻¹ R = R := by
        rw [Equiv.Perm.inv_eq_iff_eq]; exact hπR.symm
      have : Equiv.swap L R * (π * v) = π * (Equiv.swap (π⁻¹ L) R * v) := by
        rw [← mul_assoc, Equiv.swap_mul_eq_mul_swap, hπinvR, mul_assoc]
      rw [this, IH π _ hπe]
    rw [Finset.sum_congr rfl (fun L _ => hterm L)]
    refine Finset.sum_nbij' (fun L => π⁻¹ L) (fun L => π L) ?_ ?_ ?_ ?_ ?_
    · intro L hL
      have h := hπsupp.mem_iff (π⁻¹ L)
      rw [show π (π⁻¹ L) = L by simp] at h
      exact h.mp hL
    · intro L hL; exact (hπsupp.mem_iff L).mpr hL
    · intro L _; simp
    · intro L _; simp
    · intro L _; rfl
  -- Step 2: invariance under `swap R c`
  have step2 : ∀ v : Equiv.Perm (Fin n),
      ∑ L ∈ M', augLaw n x t (Equiv.swap L R * (Equiv.swap R c * v), M'.erase R)
        = ∑ L ∈ M', augLaw n x t (Equiv.swap L R * v, M'.erase R) := by
    intro v
    have hterm : ∀ L ∈ M', augLaw n x t (Equiv.swap L R * (Equiv.swap R c * v), M'.erase R)
        = augLaw n x t (Equiv.swap (Equiv.swap R c L) R * v, M'.erase R) := by
      intro L hL
      set L' : Fin n := Equiv.swap R c L with hL'
      set pL : Equiv.Perm (Fin n) :=
        Equiv.swap L R * Equiv.swap R c * Equiv.swap L' R with hpL
      have hLM : L' ∈ M' := by
        rw [hL']
        exact (SuppIn.swap hR hcM).mem_iff L |>.mpr hL
      have hsupp : SuppIn pL M' :=
        SuppIn.mul (SuppIn.mul (SuppIn.swap hL hR) (SuppIn.swap hR hcM)) (SuppIn.swap hLM hR)
      have hfix : pL R = R := by
        show Equiv.swap L R (Equiv.swap R c (Equiv.swap L' R R)) = R
        rw [Equiv.swap_apply_right]
        rw [hL']
        rw [Equiv.swap_apply_self]
        exact Equiv.swap_apply_left L R
      have hfac : Equiv.swap L R * Equiv.swap R c = pL * Equiv.swap L' R := by
        rw [hpL, mul_assoc, Equiv.swap_mul_self, mul_one]
      have : Equiv.swap L R * (Equiv.swap R c * v) = pL * (Equiv.swap L' R * v) := by
        rw [← mul_assoc, hfac, mul_assoc]
      rw [this, IH pL _ (hsupp.erase hfix)]
    rw [Finset.sum_congr rfl hterm]
    refine Finset.sum_nbij' (fun L => Equiv.swap R c L) (fun L => Equiv.swap R c L) ?_ ?_ ?_ ?_ ?_
    · intro L hL; exact (SuppIn.swap hR hcM).mem_iff L |>.mpr hL
    · intro L hL; exact (SuppIn.swap hR hcM).mem_iff L |>.mpr hL
    · intro L _; exact Equiv.swap_apply_self R c L
    · intro L _; exact Equiv.swap_apply_self R c L
    · intro L _; rfl
  calc ∑ L ∈ M', augLaw n x t (Equiv.swap L R * (ρ * w), M'.erase R)
      = ∑ L ∈ M', augLaw n x t (Equiv.swap L R * (Equiv.swap R c * (π * w)), M'.erase R) := by
        rw [hρeq]
        exact Finset.sum_congr rfl (fun L _ => by rw [mul_assoc])
    _ = ∑ L ∈ M', augLaw n x t (Equiv.swap L R * (π * w), M'.erase R) := step2 _
    _ = ∑ L ∈ M', augLaw n x t (Equiv.swap L R * w, M'.erase R) := step1 _

/-! ### The uniformity invariant -/

lemma SuppIn.inv {ρ : Equiv.Perm (Fin n)} {M : Finset (Fin n)} (h : SuppIn ρ M) :
    SuppIn ρ⁻¹ M := by
  intro c hc
  have := h c hc
  rw [Equiv.Perm.inv_eq_iff_eq, this]

lemma markUpd_self_congr {ρ : Equiv.Perm (Fin n)} {M : Finset (Fin n)} (h : SuppIn ρ M)
    (L R : Fin n) : markUpd M (ρ L) (ρ R) = M ↔ markUpd M L R = M := by
  rw [markUpd_self_iff, markUpd_self_iff]
  constructor
  · intro hc hd
    exact hc ⟨fun hm => hd.1 ((h.mem_iff R).mp hm),
      hd.2.imp (fun he => by rw [he]) (fun hm => (h.mem_iff L).mpr hm)⟩
  · intro hc hd
    exact hc ⟨fun hm => hd.1 ((h.mem_iff R).mpr hm),
      hd.2.imp (fun he => ρ.injective he) (fun hm => (h.mem_iff L).mp hm)⟩

/-- **The key invariance:** the joint law of the deck and the mark set is unchanged
when the marked cards are permuted among themselves. -/
theorem augLaw_perm_invariant (n : ℕ) (x : Equiv.Perm (Fin n)) :
    ∀ (t : ℕ) (M : Finset (Fin n)) (ρ w : Equiv.Perm (Fin n)), SuppIn ρ M →
      augLaw n x t (ρ * w, M) = augLaw n x t (w, M) := by
  intro t
  induction t with
  | zero =>
    intro M ρ w hρ
    by_cases hM : M = ∅
    · subst hM
      have : ρ = 1 := Equiv.ext (fun c => hρ c (Finset.notMem_empty c))
      rw [this, one_mul]
    · show (if _ then _ else _) = (if _ then _ else _)
      rw [if_neg (by rintro h; exact hM (congrArg Prod.snd h)),
        if_neg (by rintro h; exact hM (congrArg Prod.snd h))]
  | succ t ih =>
    intro M' ρ w hρ
    rw [augLaw_succ, augLaw_succ]
    congr 1
    have hsplit : ∀ (v : Equiv.Perm (Fin n)),
        (∑ M : Finset (Fin n), ∑ q : Fin n × Fin n,
          (if markUpd M q.1 q.2 = M' then augLaw n x t (Equiv.swap q.1 q.2 * v, M) else 0))
        = (∑ q : Fin n × Fin n,
            if markUpd M' q.1 q.2 = M' then augLaw n x t (Equiv.swap q.1 q.2 * v, M') else 0)
          + (∑ q : Fin n × Fin n,
            if q.2 ∈ M' ∧ q.1 ∈ M' then
              augLaw n x t (Equiv.swap q.1 q.2 * v, M'.erase q.2) else 0) := by
      intro v
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun q _ => sum_markUpd_split M' q.1 q.2
        (fun M => augLaw n x t (Equiv.swap q.1 q.2 * v, M)))]
      exact Finset.sum_add_distrib
    rw [hsplit, hsplit]
    congr 1
    · -- no new mark: reindex the hands by `ρ⁻¹`
      refine Fintype.sum_equiv
        (Equiv.prodCongr (ρ⁻¹ : Equiv.Perm (Fin n)) (ρ⁻¹ : Equiv.Perm (Fin n)))
        (fun q : Fin n × Fin n => if markUpd M' q.1 q.2 = M' then
            augLaw n x t (Equiv.swap q.1 q.2 * (ρ * w), M') else 0)
        (fun q : Fin n × Fin n => if markUpd M' q.1 q.2 = M' then
            augLaw n x t (Equiv.swap q.1 q.2 * w, M') else 0) (fun q => ?_)
      obtain ⟨L, R⟩ := q
      show (if markUpd M' L R = M' then augLaw n x t (Equiv.swap L R * (ρ * w), M') else 0)
        = (if markUpd M' (ρ⁻¹ L) (ρ⁻¹ R) = M' then
            augLaw n x t (Equiv.swap (ρ⁻¹ L) (ρ⁻¹ R) * w, M') else 0)
      by_cases hc : markUpd M' L R = M'
      · rw [if_pos hc, if_pos ((markUpd_self_congr hρ.inv L R).mpr hc),
          ← mul_assoc, Equiv.swap_mul_eq_mul_swap, mul_assoc, ih M' ρ _ hρ]
      · rw [if_neg hc, if_neg (fun h => hc ((markUpd_self_congr hρ.inv L R).mp h))]
    · -- a new mark: sum over the newly marked card
      have hconv : ∀ v : Equiv.Perm (Fin n),
          (∑ q : Fin n × Fin n, if q.2 ∈ M' ∧ q.1 ∈ M' then
              augLaw n x t (Equiv.swap q.1 q.2 * v, M'.erase q.2) else 0)
          = ∑ R ∈ M', ∑ L ∈ M', augLaw n x t (Equiv.swap L R * v, M'.erase R) := by
        intro v
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        have hin : ∀ R : Fin n,
            (∑ L : Fin n, if R ∈ M' ∧ L ∈ M' then
              augLaw n x t (Equiv.swap L R * v, M'.erase R) else 0)
            = if R ∈ M' then ∑ L ∈ M', augLaw n x t (Equiv.swap L R * v, M'.erase R) else 0 := by
          intro R
          by_cases hR : R ∈ M'
          · rw [if_pos hR]
            have hL2 : ∀ L : Fin n,
                (if R ∈ M' ∧ L ∈ M' then augLaw n x t (Equiv.swap L R * v, M'.erase R) else 0)
                = (if L ∈ M' then augLaw n x t (Equiv.swap L R * v, M'.erase R) else 0) := by
              intro L
              by_cases hL : L ∈ M'
              · rw [if_pos ⟨hR, hL⟩, if_pos hL]
              · rw [if_neg (by tauto), if_neg hL]
            rw [Finset.sum_congr rfl (fun L _ => hL2 L), Finset.sum_ite_mem, Finset.univ_inter]
          · rw [if_neg hR]
            exact Finset.sum_eq_zero (fun L _ => by rw [if_neg (by tauto)])
        rw [Finset.sum_congr rfl (fun R _ => hin R), Finset.sum_ite_mem, Finset.univ_inter]
      rw [hconv, hconv]
      refine Finset.sum_congr rfl (fun R hR => ?_)
      exact newMark_invariant n x t M' R hR (fun σ z hσ => ih (M'.erase R) σ z hσ) ρ w hρ

/-! ### Basic properties of the conditional mark law -/

lemma augLaw_univ_const (n : ℕ) (x y y' : Equiv.Perm (Fin n)) (t : ℕ) :
    augLaw n x t (y, Finset.univ) = augLaw n x t (y', Finset.univ) := by
  have h := augLaw_perm_invariant n x t Finset.univ (y * y'⁻¹) y'
    (fun c hc => absurd (Finset.mem_univ c) hc)
  rw [← h]
  congr 2
  rw [mul_assoc, inv_mul_cancel, mul_one]

lemma mp_nonneg (n : ℕ) : ∀ (t : ℕ) (ω : Fin (t+1) → Equiv.Perm (Fin n))
    (M : Finset (Fin n)), 0 ≤ mp n t ω M := by
  intro t
  induction t with
  | zero => intro ω M; unfold mp; split <;> norm_num
  | succ t ih =>
    intro ω M
    rw [mp_succ]
    exact Finset.sum_nonneg (fun M' _ => mul_nonneg (ih _ _) (markKer_nonneg _ _ _))

lemma mp_sum_le_one (n : ℕ) : ∀ (t : ℕ) (ω : Fin (t+1) → Equiv.Perm (Fin n)),
    ∑ M : Finset (Fin n), mp n t ω M ≤ 1 := by
  intro t
  induction t with
  | zero =>
    intro ω
    have : ∀ M : Finset (Fin n), mp n 0 ω M = if M = ∅ then (1:ℝ) else 0 := fun M => rfl
    rw [Finset.sum_congr rfl (fun M _ => this M)]
    rw [Finset.sum_ite_eq' Finset.univ (∅ : Finset (Fin n)) (fun _ => (1:ℝ))]
    simp
  | succ t ih =>
    intro ω
    rw [Finset.sum_congr rfl (fun M' _ => mp_succ n t ω M')]
    rw [Finset.sum_comm]
    have hle : ∀ M : Finset (Fin n),
        (∑ M' : Finset (Fin n), mp n t (Fin.init ω) M *
          markKer M M' (ω (Fin.last (t+1)) * (ω ((Fin.last t).castSucc))⁻¹))
        ≤ mp n t (Fin.init ω) M := by
      intro M
      rw [← Finset.mul_sum]
      calc mp n t (Fin.init ω) M * ∑ M' : Finset (Fin n), markKer M M' _
          ≤ mp n t (Fin.init ω) M * 1 :=
            mul_le_mul_of_nonneg_left (sum_markKer_le_one M _) (mp_nonneg n t _ M)
        _ = mp n t (Fin.init ω) M := mul_one _
    exact le_trans (Finset.sum_le_sum (fun M _ => hle M)) (ih (Fin.init ω))

lemma mp_le_one (n : ℕ) (t : ℕ) (ω : Fin (t+1) → Equiv.Perm (Fin n))
    (M : Finset (Fin n)) : mp n t ω M ≤ 1 := by
  refine le_trans ?_ (mp_sum_le_one n t ω)
  exact Finset.single_le_sum (fun M' _ => mp_nonneg n t ω M') (Finset.mem_univ M)

/-- Paths all of whose steps have positive probability. -/
def GoodPath (n : ℕ) {t : ℕ} (ω : Fin (t+1) → Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin t, 0 < swapCnt n (ω i.succ * (ω i.castSucc)⁻¹)

lemma goodPath_of_pathWeight (n : ℕ) {t : ℕ} (ω : Fin (t+1) → Equiv.Perm (Fin n))
    (h : pathWeight (randomTranspositions n) ω ≠ 0) : GoodPath n ω := by
  intro i
  have hne : (randomTranspositions n) (ω i.castSucc) (ω i.succ) ≠ 0 :=
    fun h0 => h (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have : transpositionDist n (ω i.succ * (ω i.castSucc)⁻¹) ≠ 0 := hne
  rw [transpositionDist_eq] at this
  by_contra hc
  push_neg at hc
  rw [Nat.le_zero.mp hc] at this
  simp at this

lemma goodPath_init (n : ℕ) {t : ℕ} (ω : Fin (t+2) → Equiv.Perm (Fin n))
    (h : GoodPath n ω) : GoodPath n (Fin.init ω) := by
  intro i
  have := h i.castSucc
  have e1 : (Fin.init ω) i.succ = ω i.succ.castSucc := rfl
  have e2 : (Fin.init ω) i.castSucc = ω i.castSucc.castSucc := rfl
  rw [e1, e2]
  have e3 : (i.castSucc : Fin (t+1)).succ = (i.succ : Fin (t+1)).castSucc :=
    (Fin.succ_castSucc i).symm
  rw [← e3]
  exact this

lemma mp_univ_mono (n : ℕ) (t : ℕ) (ω : Fin (t+2) → Equiv.Perm (Fin n))
    (h : GoodPath n ω) :
    mp n t (Fin.init ω) Finset.univ ≤ mp n (t+1) ω Finset.univ := by
  rw [mp_succ]
  have hg : 0 < swapCnt n (ω (Fin.last (t+1)) * (ω ((Fin.last t).castSucc))⁻¹) := by
    have := h (Fin.last t)
    have e1 : (Fin.last t : Fin (t+1)).succ = Fin.last (t+1) := Fin.succ_last t
    rwa [e1] at this
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum
    (f := fun M => mp n t (Fin.init ω) M * markKer M Finset.univ
      (ω (Fin.last (t+1)) * (ω ((Fin.last t).castSucc))⁻¹))
    (fun M _ => mul_nonneg (mp_nonneg n t _ M) (markKer_nonneg _ _ _))
    (Finset.mem_univ (Finset.univ : Finset (Fin n))))
  try dsimp only
  rw [markKer_univ_univ _ hg, mul_one]

/-! ### Broder's stopping rule -/

/-- `P{τ > t | ω}`: given the deck trajectory `ω`, the marking is not yet complete. -/
def surv (n : ℕ) (t : ℕ) (ω : Fin (t+1) → Equiv.Perm (Fin n)) : ℝ :=
  1 - mp n t ω Finset.univ

/-- Broder's marking rule, presented as a conditional stopping probability
given the deck trajectory. -/
def rtRule (n : ℕ) : ∀ t : ℕ, (Fin (t+1) → Equiv.Perm (Fin n)) → ℝ
  | 0, _ => 0
  | (t+1), ω =>
      if surv n t (Fin.init ω) ≤ 0 then 0
      else max 0 (min 1 ((surv n t (Fin.init ω) - surv n (t+1) ω) / surv n t (Fin.init ω)))

lemma rtRule_zero (n : ℕ) (ω : Fin 1 → Equiv.Perm (Fin n)) : rtRule n 0 ω = 0 := rfl

lemma rtRule_isStoppingRule (n : ℕ) : IsStoppingRule (rtRule n) := by
  intro t ω
  match t with
  | 0 => exact ⟨le_refl 0, zero_le_one⟩
  | (t+1) =>
    have h : rtRule n (t+1) ω
        = if surv n t (Fin.init ω) ≤ 0 then 0
          else max 0 (min 1
            ((surv n t (Fin.init ω) - surv n (t+1) ω) / surv n t (Fin.init ω))) := rfl
    rw [h]
    split
    · exact ⟨le_refl 0, zero_le_one⟩
    · exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma surv_nonneg (n t : ℕ) (ω : Fin (t+1) → Equiv.Perm (Fin n)) : 0 ≤ surv n t ω := by
  have := mp_le_one n t ω Finset.univ
  unfold surv; linarith

lemma surv_le_one (n t : ℕ) (ω : Fin (t+1) → Equiv.Perm (Fin n)) : surv n t ω ≤ 1 := by
  have := mp_nonneg n t ω Finset.univ
  unfold surv; linarith

lemma surv_mono (n t : ℕ) (ω : Fin (t+2) → Equiv.Perm (Fin n)) (h : GoodPath n ω) :
    surv n (t+1) ω ≤ surv n t (Fin.init ω) := by
  have := mp_univ_mono n t ω h
  unfold surv; linarith

lemma surv_zero_eq_one (n : ℕ) (hn : 1 ≤ n) (ω : Fin 1 → Equiv.Perm (Fin n)) :
    surv n 0 ω = 1 := by
  have hne : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
    have : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    exact fun h => by simp [h] at this
  show 1 - (if (Finset.univ : Finset (Fin n)) = ∅ then (1:ℝ) else 0) = 1
  rw [if_neg hne, sub_zero]

/-- The survival factor accumulated over times `0, …, t-1`. -/
def survProd (n : ℕ) (t : ℕ) (ω : Fin (t+1) → Equiv.Perm (Fin n)) : ℝ :=
  ∏ u : Fin t, (1 - rtRule n u.val (pathPrefix ω u))

lemma survProd_succ (n t : ℕ) (ω : Fin (t+2) → Equiv.Perm (Fin n)) :
    survProd n (t+1) ω = survProd n t (Fin.init ω) * (1 - rtRule n t (Fin.init ω)) := by
  rw [survProd, survProd, Fin.prod_univ_castSucc]
  rfl

lemma survProd_eq (n : ℕ) (hn : 1 ≤ n) : ∀ (t : ℕ) (ω : Fin (t+2) → Equiv.Perm (Fin n)),
    GoodPath n ω → survProd n (t+1) ω = surv n t (Fin.init ω) := by
  intro t
  induction t with
  | zero =>
    intro ω _
    rw [survProd_succ, surv_zero_eq_one n hn]
    simp [survProd, rtRule_zero]
  | succ t ih =>
    intro ω hgood
    rw [survProd_succ, ih (Fin.init ω) (goodPath_init n ω hgood)]
    set b := surv n t (Fin.init (Fin.init ω)) with hb
    set c := surv n (t+1) (Fin.init ω) with hc
    have hcb : c ≤ b := surv_mono n t (Fin.init ω) (goodPath_init n ω hgood)
    have hc0 : 0 ≤ c := surv_nonneg n (t+1) (Fin.init ω)
    have hrule : rtRule n (t+1) (Fin.init ω)
        = if b ≤ 0 then 0 else max 0 (min 1 ((b - c) / b)) := rfl
    rw [hrule]
    by_cases hb0 : b ≤ 0
    · rw [if_pos hb0]
      have : c = 0 := le_antisymm (le_trans hcb hb0) hc0
      rw [this]
      have : b = 0 := le_antisymm hb0 (le_trans hc0 hcb)
      rw [this]; ring
    · rw [if_neg hb0]
      push_neg at hb0
      have h1 : 0 ≤ (b - c) / b := div_nonneg (by linarith) hb0.le
      have h2 : (b - c) / b ≤ 1 := by
        rw [div_le_one hb0]; linarith
      rw [min_eq_right h2, max_eq_right h1]
      field_simp
      try ring

/-! ### The joint law of the stopping time and the deck -/

lemma survProd_mul_rule (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (ω : Fin (t+2) → Equiv.Perm (Fin n))
    (hgood : GoodPath n ω) :
    survProd n (t+1) ω * rtRule n (t+1) ω = surv n t (Fin.init ω) - surv n (t+1) ω := by
  rw [survProd_eq n hn t ω hgood]
  set b := surv n t (Fin.init ω) with hb
  set c := surv n (t+1) ω with hc
  have hcb : c ≤ b := surv_mono n t ω hgood
  have hc0 : 0 ≤ c := surv_nonneg n (t+1) ω
  have hrule : rtRule n (t+1) ω = if b ≤ 0 then 0 else max 0 (min 1 ((b - c) / b)) := rfl
  rw [hrule]
  by_cases hb0 : b ≤ 0
  · rw [if_pos hb0]
    have h1 : c = 0 := le_antisymm (le_trans hcb hb0) hc0
    have h2 : b = 0 := le_antisymm hb0 (le_trans hc0 hcb)
    rw [h1, h2]; ring
  · rw [if_neg hb0]
    push_neg at hb0
    have h1 : 0 ≤ (b - c) / b := div_nonneg (by linarith) hb0.le
    have h2 : (b - c) / b ≤ 1 := by rw [div_le_one hb0]; linarith
    rw [min_eq_right h2, max_eq_right h1]
    field_simp

lemma sum_init_marg (n : ℕ) (x y : Equiv.Perm (Fin n)) (t : ℕ) :
    (∑ ω : Fin (t+2) → Equiv.Perm (Fin n),
      if ω 0 = x ∧ ω (Fin.last (t+1)) = y then
        pathWeight (randomTranspositions n) ω * mp n t (Fin.init ω) Finset.univ else 0)
    = ∑ u : Equiv.Perm (Fin n),
        augLaw n x t (u, Finset.univ) * randomTranspositions n u y := by
  classical
  rw [snoc_split]
  have hterm : ∀ (p : Fin (t+1) → Equiv.Perm (Fin n)) (v : Equiv.Perm (Fin n)),
      (if (Fin.snoc p v : Fin (t+2) → _) 0 = x ∧
          (Fin.snoc p v : Fin (t+2) → _) (Fin.last (t+1)) = y then
        pathWeight (randomTranspositions n) (Fin.snoc p v : Fin (t+2) → _)
          * mp n t (Fin.init (Fin.snoc p v : Fin (t+2) → _)) Finset.univ else 0)
      = (if p 0 = x ∧ v = y then
          pathWeight (randomTranspositions n) p * mp n t p Finset.univ
            * (randomTranspositions n) (p (Fin.last t)) v else 0) := by
    intro p v
    have h0 : (Fin.snoc p v : Fin (t+2) → Equiv.Perm (Fin n)) 0 = p 0 := by
      have h : (0 : Fin (t+2)) = ((0 : Fin (t+1)).castSucc) := rfl
      rw [h, Fin.snoc_castSucc]
    have h1 : (Fin.snoc p v : Fin (t+2) → Equiv.Perm (Fin n)) (Fin.last (t+1)) = v :=
      Fin.snoc_last _ _
    rw [h0, h1]
    by_cases hc : p 0 = x ∧ v = y
    · rw [if_pos hc, if_pos hc, pathWeight_snoc]
      have hi : Fin.init (Fin.snoc p v : Fin (t+2) → Equiv.Perm (Fin n)) = p := by simp
      rw [hi]
      ring
    · rw [if_neg hc, if_neg hc]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun v _ => hterm p v))]
  have hv : ∀ p : Fin (t+1) → Equiv.Perm (Fin n),
      (∑ v : Equiv.Perm (Fin n), if p 0 = x ∧ v = y then
        pathWeight (randomTranspositions n) p * mp n t p Finset.univ
          * (randomTranspositions n) (p (Fin.last t)) v else 0)
      = if p 0 = x then pathWeight (randomTranspositions n) p * mp n t p Finset.univ
          * (randomTranspositions n) (p (Fin.last t)) y else 0 := by
    intro p
    by_cases hp : p 0 = x
    · rw [if_pos hp, Finset.sum_eq_single y]
      · rw [if_pos ⟨hp, rfl⟩]
      · intro b _ hb; rw [if_neg (by tauto)]
      · intro hb; exact absurd (Finset.mem_univ y) hb
    · rw [if_neg hp]
      exact Finset.sum_eq_zero (fun v _ => by rw [if_neg (by tauto)])
  rw [Finset.sum_congr rfl (fun p _ => hv p)]
  have hrw : ∀ u : Equiv.Perm (Fin n),
      augLaw n x t (u, Finset.univ) * (randomTranspositions n) u y
      = (∑ p : Fin (t+1) → Equiv.Perm (Fin n),
          if p 0 = x ∧ p (Fin.last t) = u then
            pathWeight (randomTranspositions n) p * mp n t p Finset.univ else 0)
        * (randomTranspositions n) u y := by
    intro u
    rw [← pathMark_eq_augLaw n x t u Finset.univ]
    rfl
  rw [Finset.sum_congr rfl (fun u _ => hrw u)]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  symm
  by_cases hp : p 0 = x
  · rw [if_pos hp, Finset.sum_eq_single (p (Fin.last t))]
    · rw [if_pos ⟨hp, rfl⟩]
    · intro b _ hb; rw [if_neg (by tauto), zero_mul]
    · intro hb; exact absurd (Finset.mem_univ (p (Fin.last t))) hb
  · rw [if_neg hp]
    exact Finset.sum_eq_zero (fun u _ => by rw [if_neg (by tauto), zero_mul])

lemma stopAtProb_succ (n : ℕ) (hn : 1 ≤ n) (x y : Equiv.Perm (Fin n)) (t : ℕ) :
    stopAtProb (randomTranspositions n) x (rtRule n) (t+1) y
      = augLaw n x (t+1) (y, Finset.univ)
        - ∑ u : Equiv.Perm (Fin n),
            augLaw n x t (u, Finset.univ) * randomTranspositions n u y := by
  classical
  have hterm : ∀ ω : Fin (t+2) → Equiv.Perm (Fin n),
      (if ω 0 = x ∧ ω (Fin.last (t+1)) = y then
        pathWeight (randomTranspositions n) ω
          * (∏ u : Fin (t+1), (1 - rtRule n u.val (pathPrefix ω u)))
          * rtRule n (t+1) ω else 0)
      = (if ω 0 = x ∧ ω (Fin.last (t+1)) = y then
          pathWeight (randomTranspositions n) ω * mp n (t+1) ω Finset.univ else 0)
        - (if ω 0 = x ∧ ω (Fin.last (t+1)) = y then
          pathWeight (randomTranspositions n) ω * mp n t (Fin.init ω) Finset.univ else 0) := by
    intro ω
    by_cases hc : ω 0 = x ∧ ω (Fin.last (t+1)) = y
    · rw [if_pos hc, if_pos hc, if_pos hc]
      by_cases hw : pathWeight (randomTranspositions n) ω = 0
      · rw [hw]; ring
      · rw [mul_assoc, show (∏ u : Fin (t+1), (1 - rtRule n u.val (pathPrefix ω u)))
            * rtRule n (t+1) ω = surv n t (Fin.init ω) - surv n (t+1) ω from
          survProd_mul_rule n hn t ω (goodPath_of_pathWeight n ω hw)]
        unfold surv; ring
    · rw [if_neg hc, if_neg hc, if_neg hc]; ring
  show (∑ ω : Fin (t+2) → Equiv.Perm (Fin n), _) = _
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω), Finset.sum_sub_distrib,
    sum_init_marg n x y t]
  congr 1
  exact pathMark_eq_augLaw n x (t+1) y Finset.univ

lemma stopAtProb_zero (n : ℕ) (x y : Equiv.Perm (Fin n)) :
    stopAtProb (randomTranspositions n) x (rtRule n) 0 y = 0 := by
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  by_cases hc : ω 0 = x ∧ ω (Fin.last 0) = y
  · rw [if_pos hc]
    show _ * _ * rtRule n 0 ω = 0
    rw [rtRule_zero, mul_zero]
  · rw [if_neg hc]

/-! ### Total mass -/

lemma sum_swapCnt (n : ℕ) : ∑ g : Equiv.Perm (Fin n), swapCnt n g = n ^ 2 := by
  classical
  unfold swapCnt
  rw [← Finset.card_biUnion]
  · have : ((Finset.univ : Finset (Equiv.Perm (Fin n))).biUnion
        fun g => Finset.univ.filter fun p : Fin n × Fin n => Equiv.swap p.1 p.2 = g)
        = Finset.univ := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact ⟨Equiv.swap p.1 p.2, rfl⟩
    rw [this, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    intro p h1 h2
    exact hab (h1 ▸ h2 ▸ rfl)

lemma sum_transpositionDist (n : ℕ) (hn : 1 ≤ n) :
    ∑ g : Equiv.Perm (Fin n), transpositionDist n g = 1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Finset.sum_congr rfl (fun g _ => transpositionDist_eq n g)]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← Nat.cast_sum, sum_swapCnt]
  push_cast
  field_simp

lemma transpositionDist_nonneg (n : ℕ) (g : Equiv.Perm (Fin n)) :
    0 ≤ transpositionDist n g := by
  rw [transpositionDist_eq]; positivity

lemma transpositionDist_isDist (n : ℕ) (hn : 1 ≤ n) : IsDist (transpositionDist n) :=
  ⟨transpositionDist_nonneg n, sum_transpositionDist n hn⟩

lemma rt_row_sum (n : ℕ) (hn : 1 ≤ n) (u : Equiv.Perm (Fin n)) :
    ∑ y : Equiv.Perm (Fin n), randomTranspositions n u y = 1 := by
  have h := Fintype.sum_equiv (Equiv.mulRight u)
    (fun g : Equiv.Perm (Fin n) => transpositionDist n g)
    (fun y : Equiv.Perm (Fin n) => randomTranspositions n u y)
    (fun g => by
      show transpositionDist n g = transpositionDist n (g * u * u⁻¹)
      rw [mul_assoc, mul_inv_cancel, mul_one])
  rw [← h, sum_transpositionDist n hn]

lemma rt_col_sum (n : ℕ) (hn : 1 ≤ n) (y : Equiv.Perm (Fin n)) :
    ∑ u : Equiv.Perm (Fin n), randomTranspositions n u y = 1 := by
  have h := Fintype.sum_equiv ((Equiv.inv (Equiv.Perm (Fin n))).trans (Equiv.mulRight y))
    (fun g : Equiv.Perm (Fin n) => transpositionDist n g)
    (fun u : Equiv.Perm (Fin n) => randomTranspositions n u y)
    (fun g => by
      show transpositionDist n g = transpositionDist n (y * (g⁻¹ * y)⁻¹)
      rw [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul])
  rw [← h, sum_transpositionDist n hn]

lemma sum_augKer (n : ℕ) (hn : 1 ≤ n) (a : Equiv.Perm (Fin n) × Finset (Fin n)) :
    ∑ b : Equiv.Perm (Fin n) × Finset (Fin n), augKer n a b = 1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Fintype.sum_prod_type]
  have hy : ∀ y : Equiv.Perm (Fin n),
      (∑ M' : Finset (Fin n), augKer n a (y, M'))
      = (swapCnt n (y * a.1⁻¹) : ℝ) / (n:ℝ)^2 := by
    intro y
    show (∑ M' : Finset (Fin n), (markCnt a.2 M' (y * a.1⁻¹) : ℝ) / (n:ℝ)^2) = _
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    rw [← Nat.cast_sum, sum_markCnt]
  rw [Finset.sum_congr rfl (fun y _ => hy y)]
  have hsum : ∑ y : Equiv.Perm (Fin n), (swapCnt n (y * a.1⁻¹) : ℝ)
      = ((n:ℝ))^2 := by
    have h := Fintype.sum_equiv (Equiv.mulRight a.1)
      (fun g : Equiv.Perm (Fin n) => (swapCnt n g : ℝ))
      (fun y : Equiv.Perm (Fin n) => (swapCnt n (y * a.1⁻¹) : ℝ))
      (fun g => by
        show (swapCnt n g : ℝ) = (swapCnt n (g * a.1 * a.1⁻¹) : ℝ)
        rw [mul_assoc, mul_inv_cancel, mul_one])
    rw [← h, ← Nat.cast_sum, sum_swapCnt]
    push_cast; ring
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [hsum]
  field_simp

lemma augLaw_total (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) :
    ∀ t : ℕ, ∑ b : Equiv.Perm (Fin n) × Finset (Fin n), augLaw n x t b = 1 := by
  intro t
  induction t with
  | zero =>
    show (∑ b : Equiv.Perm (Fin n) × Finset (Fin n), if b = (x, ∅) then (1:ℝ) else 0) = 1
    rw [Finset.sum_ite_eq' Finset.univ (x, (∅ : Finset (Fin n))) (fun _ => (1:ℝ))]
    simp
  | succ t ih =>
    have hstep : ∀ b : Equiv.Perm (Fin n) × Finset (Fin n),
        augLaw n x (t+1) b
          = ∑ a : Equiv.Perm (Fin n) × Finset (Fin n), augLaw n x t a * augKer n a b :=
      fun b => rfl
    rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => by
      rw [← Finset.mul_sum, sum_augKer n hn a, mul_one])]
    exact ih

lemma augLaw_nonneg (n : ℕ) (x : Equiv.Perm (Fin n)) :
    ∀ (t : ℕ) (b : Equiv.Perm (Fin n) × Finset (Fin n)), 0 ≤ augLaw n x t b := by
  intro t
  induction t with
  | zero => intro b; show (0:ℝ) ≤ if b = (x, ∅) then 1 else 0; split <;> norm_num
  | succ t ih =>
    intro b
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (ih a)
      (by unfold augKer; positivity))

/-! ### The tail of the stopping time -/

/-- `P{marking complete by time t}`. -/
def markDone (n : ℕ) (x : Equiv.Perm (Fin n)) (t : ℕ) : ℝ :=
  ∑ y : Equiv.Perm (Fin n), augLaw n x t (y, Finset.univ)

lemma sum_stopAtProb_succ (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) (t : ℕ) :
    (∑ y : Equiv.Perm (Fin n), stopAtProb (randomTranspositions n) x (rtRule n) (t+1) y)
      = markDone n x (t+1) - markDone n x t := by
  rw [Finset.sum_congr rfl (fun y _ => stopAtProb_succ n hn x y t)]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun u _ => by
    rw [← Finset.mul_sum, rt_row_sum n hn u, mul_one])]
  rfl

lemma markDone_zero (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) : markDone n x 0 = 0 := by
  refine Finset.sum_eq_zero (fun y _ => ?_)
  show (if (y, (Finset.univ : Finset (Fin n))) = (x, ∅) then (1:ℝ) else 0) = 0
  rw [if_neg]
  rintro h
  have h2 : (Finset.univ : Finset (Fin n)) = ∅ := congrArg Prod.snd h
  have : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  rw [h2] at this
  exact absurd this (Finset.notMem_empty _)

lemma partial_sum_stopAtProb (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) :
    ∀ t : ℕ, (∑ u ∈ Finset.range (t+1),
      ∑ y : Equiv.Perm (Fin n), stopAtProb (randomTranspositions n) x (rtRule n) u y)
      = markDone n x t := by
  intro t
  induction t with
  | zero =>
    rw [Finset.sum_range_one, markDone_zero n hn x]
    exact Finset.sum_eq_zero (fun y _ => stopAtProb_zero n x y)
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, sum_stopAtProb_succ n hn x t]
    ring

lemma stopTailProb_eq (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) (t : ℕ) :
    stopTailProb (randomTranspositions n) x (rtRule n) t = 1 - markDone n x t := by
  rw [stopTailProb, partial_sum_stopAtProb n hn x t]

lemma one_sub_markDone (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) (t : ℕ) :
    1 - markDone n x t
      = ∑ b ∈ Finset.univ.filter (fun b : Equiv.Perm (Fin n) × Finset (Fin n) =>
          b.2 ≠ Finset.univ), augLaw n x t b := by
  classical
  have htot := augLaw_total n hn x t
  have hsplit : (∑ b : Equiv.Perm (Fin n) × Finset (Fin n), augLaw n x t b)
      = (∑ b ∈ Finset.univ.filter (fun b : Equiv.Perm (Fin n) × Finset (Fin n) =>
            b.2 ≠ Finset.univ), augLaw n x t b)
        + ∑ b ∈ Finset.univ.filter (fun b : Equiv.Perm (Fin n) × Finset (Fin n) =>
            ¬ (b.2 ≠ Finset.univ)), augLaw n x t b :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hdone : (∑ b ∈ Finset.univ.filter (fun b : Equiv.Perm (Fin n) × Finset (Fin n) =>
      ¬ (b.2 ≠ Finset.univ)), augLaw n x t b) = markDone n x t := by
    rw [markDone]
    refine Finset.sum_nbij' (fun b => b.1) (fun y => (y, Finset.univ)) ?_ ?_ ?_ ?_ ?_
    · intro b _; exact Finset.mem_univ _
    · intro y _; simp
    · rintro ⟨y, M⟩ hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hb
      subst hb
      rfl
    · intro y _; rfl
    · rintro ⟨y, M⟩ hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hb
      subst hb
      rfl
  rw [hsplit, hdone] at htot
  linarith

lemma stopAtProb_const (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) (t : ℕ)
    (y y' : Equiv.Perm (Fin n)) :
    stopAtProb (randomTranspositions n) x (rtRule n) t y
      = stopAtProb (randomTranspositions n) x (rtRule n) t y' := by
  match t with
  | 0 => rw [stopAtProb_zero, stopAtProb_zero]
  | (t+1) =>
    rw [stopAtProb_succ n hn x y t, stopAtProb_succ n hn x y' t]
    congr 1
    · exact augLaw_univ_const n x y y' (t+1)
    · have e1 : ∀ z : Equiv.Perm (Fin n),
          (∑ u : Equiv.Perm (Fin n),
            augLaw n x t (u, Finset.univ) * randomTranspositions n u z)
          = augLaw n x t (1, Finset.univ) := by
        intro z
        rw [Finset.sum_congr rfl (fun u _ =>
          congrArg (fun w => w * randomTranspositions n u z) (augLaw_univ_const n x u 1 t))]
        rw [← Finset.mul_sum, rt_col_sum n hn z, mul_one]
      rw [e1 y, e1 y']

lemma stopAtProb_eq_uniform (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) (t : ℕ)
    (y : Equiv.Perm (Fin n)) :
    stopAtProb (randomTranspositions n) x (rtRule n) t y
      = (∑ z : Equiv.Perm (Fin n), stopAtProb (randomTranspositions n) x (rtRule n) t z)
        * uniformDist (Equiv.Perm (Fin n)) y := by
  have hcard : (0:ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [Finset.sum_congr rfl (fun z _ => stopAtProb_const n hn x t z y)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  show _ = _ * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ))⁻¹
  field_simp

/-! ### An exponential supermartingale for the marking process -/

/-- The chance of marking a new card when `j` cards are already marked. -/
def pp (n j : ℕ) : ℝ := ((j : ℝ) + 1) * ((n : ℝ) - j) / (n : ℝ) ^ 2

/-- The one-stage factor of the exponential supermartingale. -/
def aa (n : ℕ) (z : ℝ) (j : ℕ) : ℝ := z * pp n j / (1 - z * (1 - pp n j))

/-- The potential attached to a mark set of size `j`. -/
def AA (n : ℕ) (z : ℝ) (j : ℕ) : ℝ := ∏ i ∈ Finset.Ico j n, aa n z i

/-- The potential attached to a mark set, vanishing once all cards are marked. -/
def Phi (n : ℕ) (z : ℝ) (M : Finset (Fin n)) : ℝ :=
  if M = Finset.univ then 0 else AA n z M.card

lemma pp_pos {n j : ℕ} (hj : j < n) : 0 < pp n j := by
  have h1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
  have h2 : (0:ℝ) < (n:ℝ) - j := by
    have : (j:ℝ) < n := by exact_mod_cast hj
    linarith
  have h3 : (0:ℝ) < (n:ℝ)^2 := by
    have : (0:ℝ) < (n:ℝ) := by
      have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith
    positivity
  unfold pp; positivity

lemma pp_le_one {n j : ℕ} (hj : j < n) : pp n j ≤ 1 := by
  have hjn : (j:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  rw [pp, div_le_one (by positivity)]
  nlinarith [sq_nonneg ((j:ℝ) + 1 - ((n:ℝ) - j))]

lemma aa_pos {n j : ℕ} {z : ℝ} (hj : j < n) (hz : 0 < z)
    (hD : 0 < 1 - z * (1 - pp n j)) : 0 < aa n z j := by
  unfold aa
  exact div_pos (mul_pos hz (pp_pos hj)) hD

lemma one_le_aa {n j : ℕ} {z : ℝ} (hj : j < n) (hz : 1 ≤ z)
    (hD : 0 < 1 - z * (1 - pp n j)) : 1 ≤ aa n z j := by
  rw [aa, le_div_iff₀ hD]
  nlinarith [pp_pos hj]

lemma AA_pos {n : ℕ} {z : ℝ} (hz : 0 < z)
    (hD : ∀ j, j < n → 0 < 1 - z * (1 - pp n j)) (j : ℕ) : 0 < AA n z j := by
  refine Finset.prod_pos (fun i hi => ?_)
  exact aa_pos (Finset.mem_Ico.mp hi).2 hz (hD i (Finset.mem_Ico.mp hi).2)

lemma one_le_AA {n : ℕ} {z : ℝ} (hz : 1 ≤ z)
    (hD : ∀ j, j < n → 0 < 1 - z * (1 - pp n j)) (j : ℕ) : 1 ≤ AA n z j := by
  calc (1:ℝ) = ∏ _i ∈ Finset.Ico j n, (1:ℝ) := by simp
    _ ≤ ∏ i ∈ Finset.Ico j n, aa n z i :=
        Finset.prod_le_prod (fun i _ => zero_le_one)
          (fun i hi => one_le_aa (Finset.mem_Ico.mp hi).2 hz (hD i (Finset.mem_Ico.mp hi).2))

lemma AA_succ {n j : ℕ} {z : ℝ} (hj : j < n) : AA n z j = aa n z j * AA n z (j+1) := by
  rw [AA, AA, Finset.prod_eq_prod_Ico_succ_bot hj]

lemma sum_markable (n : ℕ) (M : Finset (Fin n)) :
    (∑ q : Fin n × Fin n, if q.2 ∉ M ∧ (q.1 = q.2 ∨ q.1 ∈ M) then (1:ℝ) else 0)
      = ((n : ℝ) - M.card) * (M.card + 1) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hinner : ∀ R : Fin n,
      (∑ L : Fin n, if R ∉ M ∧ (L = R ∨ L ∈ M) then (1:ℝ) else 0)
      = if R ∉ M then ((M.card : ℝ) + 1) else 0 := by
    intro R
    by_cases hR : R ∉ M
    · rw [if_pos hR]
      have hset : (Finset.univ.filter fun L : Fin n => L = R ∨ L ∈ M) = insert R M := by
        ext L; simp [or_comm]
      rw [Finset.sum_congr rfl (fun L _ => by
        rw [if_congr (by tauto : (R ∉ M ∧ (L = R ∨ L ∈ M)) ↔ (L = R ∨ L ∈ M)) rfl rfl])]
      rw [Finset.sum_boole, hset, Finset.card_insert_of_notMem hR]
      push_cast; ring
    · rw [if_neg hR]
      exact Finset.sum_eq_zero (fun L _ => by rw [if_neg (by tauto)])
  rw [Finset.sum_congr rfl (fun R _ => hinner R)]
  rw [← Finset.sum_filter]
  have hcompl : (Finset.univ.filter fun R : Fin n => R ∉ M) = Mᶜ := by
    ext R; simp
  rw [hcompl, Finset.sum_const, nsmul_eq_mul, Finset.card_compl, Fintype.card_fin]
  congr 1
  have : M.card ≤ n := le_trans (Finset.card_le_univ M) (by simp)
  push_cast [Nat.cast_sub this]
  ring

lemma sum_ite_const (n : ℕ) (C : Fin n × Fin n → Prop) [DecidablePred C] (A B : ℝ) :
    (∑ q : Fin n × Fin n, if C q then A else B)
      = (∑ q : Fin n × Fin n, if C q then (1:ℝ) else 0) * A
        + ((n:ℝ)^2 - ∑ q : Fin n × Fin n, if C q then (1:ℝ) else 0) * B := by
  classical
  have hcard : (∑ _q : Fin n × Fin n, (1:ℝ)) = (n:ℝ)^2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hterm : ∀ q : Fin n × Fin n,
      (if C q then A else B)
        = (if C q then (1:ℝ) else 0) * A + (1 - (if C q then (1:ℝ) else 0)) * B := by
    intro q; by_cases h : C q
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [Finset.sum_congr rfl (fun q _ => hterm q)]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib, hcard]

lemma phi_step (n : ℕ) (z : ℝ) (hz : 1 ≤ z) (hn : 1 ≤ n)
    (hD : ∀ j, j < n → 0 < 1 - z * (1 - pp n j)) (M : Finset (Fin n)) :
    (∑ q : Fin n × Fin n, Phi n z (markUpd M q.1 q.2)) ≤ (n:ℝ)^2 / z * Phi n z M := by
  classical
  have hz0 : (0:ℝ) < z := lt_of_lt_of_le zero_lt_one hz
  by_cases hM : M = Finset.univ
  · subst hM
    have h0 : ∀ q : Fin n × Fin n, Phi n z (markUpd (Finset.univ : Finset (Fin n)) q.1 q.2) = 0 := by
      intro q; rw [markUpd_univ]; unfold Phi; rw [if_pos rfl]
    rw [Finset.sum_congr rfl (fun q _ => h0 q), Finset.sum_const, smul_zero]
    have : Phi n z (Finset.univ : Finset (Fin n)) = 0 := by unfold Phi; rw [if_pos rfl]
    rw [this, mul_zero]
  · set j := M.card with hj
    have hjn : j < n := by
      have h1 : M ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hM
      have := Finset.card_lt_card h1
      simpa [Finset.card_univ] using this
    have hA1 : 0 < AA n z (j+1) := AA_pos hz0 hD (j+1)
    have hPhiM : Phi n z M = AA n z j := by unfold Phi; rw [if_neg hM]
    have hbound : ∀ q : Fin n × Fin n,
        Phi n z (markUpd M q.1 q.2)
          ≤ if q.2 ∉ M ∧ (q.1 = q.2 ∨ q.1 ∈ M) then AA n z (j+1) else AA n z j := by
      intro q
      unfold markUpd
      by_cases hc : q.2 ∉ M ∧ (q.1 = q.2 ∨ q.1 ∈ M)
      · rw [if_pos hc, if_pos hc]
        unfold Phi
        split
        · exact le_of_lt hA1
        · rw [Finset.card_insert_of_notMem hc.1]
      · rw [if_neg hc, if_neg hc, hPhiM]
    refine le_trans (Finset.sum_le_sum (fun q _ => hbound q)) ?_
    rw [sum_ite_const, sum_markable]
    set P : ℝ := pp n j with hP
    have hDj : 0 < 1 - z * (1 - P) := hD j hjn
    have hn0 : (0:ℝ) < (n:ℝ) := by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    have hcn : ((n : ℝ) - j) * (j + 1) = (n:ℝ)^2 * P := by
      rw [hP, pp]
      field_simp
      try ring
    have haa : AA n z j = aa n z j * AA n z (j+1) := AA_succ hjn
    have hkey : z * (P + (1 - P) * aa n z j) = aa n z j := by
      rw [aa, ← hP]
      field_simp
      ring
    rw [hcn, haa, hPhiM, haa]
    have hexp : (n:ℝ)^2 * P * AA n z (j+1)
        + ((n:ℝ)^2 - (n:ℝ)^2 * P) * (aa n z j * AA n z (j+1))
        = (n:ℝ)^2 * (P + (1 - P) * aa n z j) * AA n z (j+1) := by ring
    rw [hexp]
    have hrhs : (n:ℝ)^2 / z * (aa n z j * AA n z (j+1))
        = (n:ℝ)^2 * (z * (P + (1 - P) * aa n z j) / z) * AA n z (j+1) := by
      rw [hkey]; try field_simp
    rw [hrhs]
    rw [mul_div_cancel_left₀ _ (ne_of_gt hz0)]

/-- The mark-set marginal of the augmented law. -/
lemma augLaw_zero_eq (n : ℕ) (x : Equiv.Perm (Fin n))
    (b : Equiv.Perm (Fin n) × Finset (Fin n)) :
    augLaw n x 0 b = if b = (x, ∅) then 1 else 0 := rfl

def Ay (n : ℕ) (x : Equiv.Perm (Fin n)) (t : ℕ) (M : Finset (Fin n)) : ℝ :=
  ∑ y : Equiv.Perm (Fin n), augLaw n x t (y, M)

lemma Ay_nonneg (n : ℕ) (x : Equiv.Perm (Fin n)) (t : ℕ) (M : Finset (Fin n)) :
    0 ≤ Ay n x t M :=
  Finset.sum_nonneg (fun y _ => augLaw_nonneg n x t (y, M))

lemma Ay_reindex (n : ℕ) (x : Equiv.Perm (Fin n)) (t : ℕ) (M : Finset (Fin n))
    (g : Equiv.Perm (Fin n)) :
    (∑ y : Equiv.Perm (Fin n), augLaw n x t (g * y, M)) = Ay n x t M := by
  exact Fintype.sum_equiv (Equiv.mulLeft g)
    (fun y => augLaw n x t (g * y, M)) (fun y => augLaw n x t (y, M)) (fun y => rfl)

lemma Ay_succ (n : ℕ) (x : Equiv.Perm (Fin n)) (t : ℕ) (M' : Finset (Fin n)) :
    Ay n x (t+1) M'
      = (∑ M : Finset (Fin n), ∑ q : Fin n × Fin n,
          (if markUpd M q.1 q.2 = M' then Ay n x t M else 0)) / (n:ℝ)^2 := by
  classical
  rw [Ay, Finset.sum_congr rfl (fun y _ => augLaw_succ n x y t M')]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  congr 1
  rw [sum_comm3 (fun (y : Equiv.Perm (Fin n)) (M : Finset (Fin n)) (q : Fin n × Fin n) =>
    if markUpd M q.1 q.2 = M' then augLaw n x t (Equiv.swap q.1 q.2 * y, M) else 0)]
  rw [sum_comm3 (fun (q : Fin n × Fin n) (y : Equiv.Perm (Fin n)) (M : Finset (Fin n)) =>
    if markUpd M q.1 q.2 = M' then augLaw n x t (Equiv.swap q.1 q.2 * y, M) else 0)]
  refine Finset.sum_congr rfl (fun M _ => Finset.sum_congr rfl (fun q _ => ?_))
  by_cases hc : markUpd M q.1 q.2 = M'
  · rw [if_pos hc]
    rw [Finset.sum_congr rfl (fun y _ => if_pos hc)]
    exact Ay_reindex n x t M (Equiv.swap q.1 q.2)
  · rw [if_neg hc]
    exact Finset.sum_eq_zero (fun y _ => if_neg hc)

/-- The exponential potential of the augmented law. -/
def Psi (n : ℕ) (z : ℝ) (x : Equiv.Perm (Fin n)) (t : ℕ) : ℝ :=
  ∑ M : Finset (Fin n), Ay n x t M * Phi n z M

lemma Psi_succ_le (n : ℕ) (z : ℝ) (hz : 1 ≤ z) (hn : 1 ≤ n)
    (hD : ∀ j, j < n → 0 < 1 - z * (1 - pp n j)) (x : Equiv.Perm (Fin n)) (t : ℕ) :
    Psi n z x (t+1) ≤ Psi n z x t / z := by
  classical
  have hz0 : (0:ℝ) < z := lt_of_lt_of_le zero_lt_one hz
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hn2 : (0:ℝ) < (n:ℝ)^2 := by positivity
  have hstep : (n:ℝ)^2 * Psi n z x (t+1)
      = ∑ M : Finset (Fin n), Ay n x t M *
          ∑ q : Fin n × Fin n, Phi n z (markUpd M q.1 q.2) := by
    rw [Psi, Finset.mul_sum]
    have hterm : ∀ M' : Finset (Fin n),
        (n:ℝ)^2 * (Ay n x (t+1) M' * Phi n z M')
          = ∑ M : Finset (Fin n), ∑ q : Fin n × Fin n,
              (if markUpd M q.1 q.2 = M' then Ay n x t M else 0) * Phi n z M' := by
      intro M'
      rw [Ay_succ n x t M']
      rw [show (n:ℝ)^2 * ((∑ M : Finset (Fin n), ∑ q : Fin n × Fin n,
            (if markUpd M q.1 q.2 = M' then Ay n x t M else 0)) / (n:ℝ)^2 * Phi n z M')
          = (∑ M : Finset (Fin n), ∑ q : Fin n × Fin n,
            (if markUpd M q.1 q.2 = M' then Ay n x t M else 0)) * Phi n z M' from by
        field_simp]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun M _ => Finset.sum_mul _ _ _)
    rw [Finset.sum_congr rfl (fun M' _ => hterm M')]
    rw [sum_comm3 (fun (M' : Finset (Fin n)) (M : Finset (Fin n)) (q : Fin n × Fin n) =>
      (if markUpd M q.1 q.2 = M' then Ay n x t M else 0) * Phi n z M')]
    rw [sum_comm3 (fun (q : Fin n × Fin n) (M' : Finset (Fin n)) (M : Finset (Fin n)) =>
      (if markUpd M q.1 q.2 = M' then Ay n x t M else 0) * Phi n z M')]
    refine Finset.sum_congr rfl (fun M _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_eq_single (markUpd M q.1 q.2)]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg (fun h => hb h.symm), zero_mul]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  have hb : ∀ M : Finset (Fin n),
      Ay n x t M * (∑ q : Fin n × Fin n, Phi n z (markUpd M q.1 q.2)) * z
        ≤ Ay n x t M * Phi n z M * (n:ℝ)^2 := by
    intro M
    have h1 := phi_step n z hz hn hD M
    have h2 : Ay n x t M * (∑ q : Fin n × Fin n, Phi n z (markUpd M q.1 q.2))
        ≤ Ay n x t M * ((n:ℝ)^2 / z * Phi n z M) :=
      mul_le_mul_of_nonneg_left h1 (Ay_nonneg n x t M)
    have h3 : Ay n x t M * ((n:ℝ)^2 / z * Phi n z M) * z
        = Ay n x t M * Phi n z M * (n:ℝ)^2 := by field_simp; try ring
    calc Ay n x t M * (∑ q : Fin n × Fin n, Phi n z (markUpd M q.1 q.2)) * z
        ≤ Ay n x t M * ((n:ℝ)^2 / z * Phi n z M) * z :=
          mul_le_mul_of_nonneg_right h2 hz0.le
      _ = _ := h3
  rw [le_div_iff₀ hz0]
  refine le_of_mul_le_mul_right ?_ hn2
  have he : Psi n z x (t+1) * z * (n:ℝ)^2
      = (∑ M : Finset (Fin n), Ay n x t M *
          ∑ q : Fin n × Fin n, Phi n z (markUpd M q.1 q.2)) * z := by
    rw [← hstep]; ring
  rw [he, Psi]
  simp only [Finset.sum_mul]
  exact Finset.sum_le_sum (fun M _ => hb M)

lemma Psi_le (n : ℕ) (z : ℝ) (hz : 1 ≤ z) (hn : 1 ≤ n)
    (hD : ∀ j, j < n → 0 < 1 - z * (1 - pp n j)) (x : Equiv.Perm (Fin n)) :
    ∀ t : ℕ, Psi n z x t ≤ AA n z 0 / z ^ t := by
  have hz0 : (0:ℝ) < z := lt_of_lt_of_le zero_lt_one hz
  intro t
  induction t with
  | zero =>
    have hAy0 : Ay n x 0 (∅ : Finset (Fin n)) = 1 := by
      rw [Ay, Finset.sum_eq_single x]
      · rw [augLaw_zero_eq, if_pos rfl]
      · intro b _ hb
        rw [augLaw_zero_eq, if_neg (fun h => hb (congrArg Prod.fst h))]
      · intro hb; exact absurd (Finset.mem_univ x) hb
    have h0 : Psi n z x 0 = Phi n z (∅ : Finset (Fin n)) := by
      rw [Psi, Finset.sum_eq_single (∅ : Finset (Fin n))]
      · rw [hAy0, one_mul]
      · intro M _ hM
        have : Ay n x 0 M = 0 := by
          rw [Ay]
          refine Finset.sum_eq_zero (fun y _ => ?_)
          rw [augLaw_zero_eq, if_neg (fun h => hM (congrArg Prod.snd h))]
        rw [this, zero_mul]
      · intro hb; exact absurd (Finset.mem_univ _) hb
    have hne : (∅ : Finset (Fin n)) ≠ Finset.univ := by
      intro h
      have : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
      rw [← h] at this
      exact absurd this (Finset.notMem_empty _)
    rw [h0, Phi, if_neg hne, Finset.card_empty, pow_zero, div_one]
  | succ t ih =>
    refine le_trans (Psi_succ_le n z hz hn hD x t) ?_
    rw [div_le_div_iff₀ hz0 (by positivity)]
    have h1 : Psi n z x t * z ^ (t+1) ≤ AA n z 0 / z ^ t * z ^ (t+1) :=
      mul_le_mul_of_nonneg_right ih (by positivity)
    refine le_trans h1 (le_of_eq ?_)
    field_simp
    try ring

/-! ### Estimating the potential -/

lemma pp_ge_inv (n j : ℕ) (hj : j < n) : (1:ℝ) / n ≤ pp n j := by
  have hj' : (j:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  rw [pp, div_le_div_iff₀ hn0 (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hj0 (show (0:ℝ) ≤ (n:ℝ) - j - 1 by linarith)) hn0.le]

lemma pos_denom (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (j : ℕ) (hj : j < n) :
    0 < 1 - (1 + c / n) * (1 - pp n j) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h1 : (1:ℝ)/n ≤ pp n j := pp_ge_inv n j hj
  have h2 : 1 - (1 + c / n) * (1 - pp n j) = (1 + c/n) * pp n j - c/n := by ring
  rw [h2]
  have h3 : (1:ℝ) * pp n j ≤ (1 + c/n) * pp n j := by
    have : (0:ℝ) < pp n j := pp_pos hj
    nlinarith [le_of_lt (div_pos hc0 hn0)]
  have h4 : c / n < 1 / n := by
    rw [div_lt_div_iff_of_pos_right hn0]; exact hc1
  linarith

lemma aa_le (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (j : ℕ) (hj : j < n) :
    aa n (1 + c / n) j ≤ 1 + (c / n) / ((1 - c) * pp n j) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hP : (0:ℝ) < pp n j := pp_pos hj
  have h1 : (1:ℝ)/n ≤ pp n j := pp_ge_inv n j hj
  have hD : 0 < 1 - (1 + c / n) * (1 - pp n j) := pos_denom n hn c hc0 hc1 j hj
  have hDeq : 1 - (1 + c / n) * (1 - pp n j) = (1 + c/n) * pp n j - c/n := by ring
  have hlow : (1 - c) * pp n j ≤ (1 + c/n) * pp n j - c/n := by
    have hcp : c / n ≤ c * pp n j := by
      rw [div_le_iff₀ hn0] at *
      nlinarith
    nlinarith [div_pos hc0 hn0]
  have hlow0 : 0 < (1 - c) * pp n j := by
    have : (0:ℝ) < 1 - c := by linarith
    positivity
  rw [aa, hDeq]
  have hne : (1 + c/n) * pp n j - c/n ≠ 0 := by rw [← hDeq]; exact hD.ne'
  have hne2 : ((n:ℝ) + c) * pp n j - c ≠ 0 := by
    have he : ((n:ℝ) + c) * pp n j - c = (n:ℝ) * ((1 + c/(n:ℝ)) * pp n j - c/(n:ℝ)) := by
      field_simp
      try ring
    rw [he]
    exact mul_ne_zero hn0.ne' hne
  have hsplit : (1 + c/n) * pp n j / ((1 + c/n) * pp n j - c/n)
      = 1 + (c/n) / ((1 + c/n) * pp n j - c/n) := by
    field_simp
    try ring
  rw [hsplit]
  have := div_le_div_of_nonneg_left (le_of_lt (div_pos hc0 hn0)) hlow0 hlow
  linarith

lemma sum_inv_pp (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n, (pp n i)⁻¹
      = (n:ℝ)^2 / ((n:ℝ) + 1) * (2 * ∑ i ∈ Finset.range n, ((i:ℝ) + 1)⁻¹) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hterm : ∀ i ∈ Finset.range n, (pp n i)⁻¹
      = (n:ℝ)^2 / ((n:ℝ)+1) * (((i:ℝ)+1)⁻¹ + ((n:ℝ) - i)⁻¹) := by
    intro i hi
    have hi' : (i:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast Finset.mem_range.mp hi
    have h1 : (0:ℝ) < (i:ℝ) + 1 := by positivity
    have h2 : (0:ℝ) < (n:ℝ) - i := by linarith
    rw [pp]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  have hrefl : ∑ i ∈ Finset.range n, ((n:ℝ) - i)⁻¹ = ∑ i ∈ Finset.range n, ((i:ℝ) + 1)⁻¹ := by
    rw [← Finset.sum_range_reflect (fun i => ((i:ℝ) + 1)⁻¹) n]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < n := Finset.mem_range.mp hi
    congr 1
    have : ((n - 1 - i : ℕ) : ℝ) = (n:ℝ) - 1 - i := by
      have h1 : i ≤ n - 1 := by omega
      have h2 : 1 ≤ n := hn
      push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
      ring
    rw [this]; ring
  rw [hrefl]; ring

lemma sum_inv_pp_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n, (pp n i)⁻¹ ≤ 2 * n * (1 + Real.log n) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [sum_inv_pp n hn]
  have hharm : ∑ i ∈ Finset.range n, ((i:ℝ) + 1)⁻¹ = (harmonic n : ℝ) := by
    rw [harmonic]
    push_cast
    rfl
  have hH : (harmonic n : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
  have hH0 : (0:ℝ) ≤ (harmonic n : ℝ) := by
    rw [← hharm]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have hfac : (n:ℝ)^2 / ((n:ℝ)+1) ≤ (n:ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  rw [hharm]
  calc (n:ℝ)^2 / ((n:ℝ)+1) * (2 * (harmonic n : ℝ))
      ≤ (n:ℝ) * (2 * (harmonic n : ℝ)) := by
        refine mul_le_mul_of_nonneg_right hfac (by linarith)
    _ ≤ (n:ℝ) * (2 * (1 + Real.log n)) := by
        refine mul_le_mul_of_nonneg_left (by linarith) hn0.le
    _ = 2 * n * (1 + Real.log n) := by ring

lemma tail_le_Psi (n : ℕ) (z : ℝ) (hz : 1 ≤ z) (hn : 1 ≤ n)
    (hD : ∀ j, j < n → 0 < 1 - z * (1 - pp n j)) (x : Equiv.Perm (Fin n)) (t : ℕ) :
    1 - markDone n x t ≤ Psi n z x t := by
  classical
  rw [one_sub_markDone n hn x t]
  have hPsi : Psi n z x t
      = ∑ b : Equiv.Perm (Fin n) × Finset (Fin n), augLaw n x t b * Phi n z b.2 := by
    rw [Psi, Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun M _ => by rw [Ay, Finset.sum_mul])
  rw [hPsi]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Equiv.Perm (Fin n) × Finset (Fin n)))
    (fun b => b.2 ≠ Finset.univ) (fun b => augLaw n x t b * Phi n z b.2)
  have hzero : (∑ b ∈ Finset.univ.filter
      (fun b : Equiv.Perm (Fin n) × Finset (Fin n) => ¬ (b.2 ≠ Finset.univ)),
      augLaw n x t b * Phi n z b.2) = 0 := by
    refine Finset.sum_eq_zero (fun b hb => ?_)
    simp only [Finset.mem_filter, not_not] at hb
    rw [show Phi n z b.2 = 0 from by rw [Phi, if_pos hb.2], mul_zero]
  have hge : (∑ b ∈ Finset.univ.filter
        (fun b : Equiv.Perm (Fin n) × Finset (Fin n) => b.2 ≠ Finset.univ), augLaw n x t b)
      ≤ ∑ b ∈ Finset.univ.filter
        (fun b : Equiv.Perm (Fin n) × Finset (Fin n) => b.2 ≠ Finset.univ),
        augLaw n x t b * Phi n z b.2 := by
    refine Finset.sum_le_sum (fun b hb => ?_)
    simp only [Finset.mem_filter] at hb
    have h1 : (1:ℝ) ≤ Phi n z b.2 := by
      rw [Phi, if_neg hb.2]; exact one_le_AA hz hD _
    nlinarith [augLaw_nonneg n x t b]
  linarith

lemma AA_zero_le (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    AA n (1 + c/n) 0 ≤ Real.exp (2 * c * (1 + Real.log n) / (1 - c)) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hc' : (0:ℝ) < 1 - c := by linarith
  have hz : (1:ℝ) ≤ 1 + c/n := by
    have : (0:ℝ) < c / n := div_pos hc0 hn0
    linarith
  have hz0 : (0:ℝ) < 1 + c/n := by linarith
  have hstep1 : AA n (1 + c/n) 0
      ≤ ∏ i ∈ Finset.range n, (1 + (c/n) / ((1 - c) * pp n i)) := by
    rw [AA, ← Finset.range_eq_Ico]
    refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
    · exact le_of_lt (aa_pos (Finset.mem_range.mp hi) hz0
        (pos_denom n hn c hc0 hc1 i (Finset.mem_range.mp hi)))
    · exact aa_le n hn c hc0 hc1 i (Finset.mem_range.mp hi)
  have hstep2 : (∏ i ∈ Finset.range n, (1 + (c/n) / ((1 - c) * pp n i)))
      ≤ ∏ i ∈ Finset.range n, Real.exp ((c/n) / ((1 - c) * pp n i)) := by
    refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
    · have : (0:ℝ) ≤ (c/n) / ((1 - c) * pp n i) := by
        have := pp_pos (Finset.mem_range.mp hi)
        positivity
      linarith
    · linarith [Real.add_one_le_exp ((c/(n:ℝ)) / ((1 - c) * pp n i))]
  have hstep3 : (∏ i ∈ Finset.range n, Real.exp ((c/n) / ((1 - c) * pp n i)))
      = Real.exp (∑ i ∈ Finset.range n, (c/n) / ((1 - c) * pp n i)) :=
    (Real.exp_sum _ _).symm
  have hsum : (∑ i ∈ Finset.range n, (c/n) / ((1 - c) * pp n i))
      ≤ 2 * c * (1 + Real.log n) / (1 - c) := by
    have hterm : ∀ i ∈ Finset.range n,
        (c/n) / ((1 - c) * pp n i) = (c / ((n:ℝ) * (1-c))) * (pp n i)⁻¹ := by
      intro i hi
      have := pp_pos (Finset.mem_range.mp hi)
      field_simp
      try ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have h1 := sum_inv_pp_le n hn
    have h2 : (0:ℝ) < c / ((n:ℝ) * (1-c)) := by positivity
    calc c / ((n:ℝ) * (1-c)) * ∑ i ∈ Finset.range n, (pp n i)⁻¹
        ≤ c / ((n:ℝ) * (1-c)) * (2 * n * (1 + Real.log n)) :=
          mul_le_mul_of_nonneg_left h1 h2.le
      _ = 2 * c * (1 + Real.log n) / (1 - c) := by field_simp; try ring
  calc AA n (1 + c/n) 0 ≤ _ := hstep1
    _ ≤ _ := hstep2
    _ = Real.exp (∑ i ∈ Finset.range n, (c/n) / ((1 - c) * pp n i)) := hstep3
    _ ≤ Real.exp (2 * c * (1 + Real.log n) / (1 - c)) := Real.exp_le_exp.mpr hsum

/-! ### The stopping time is almost surely finite -/

lemma stopTail_le (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (x : Equiv.Perm (Fin n)) (T : ℕ) :
    stopTailProb (randomTranspositions n) x (rtRule n) T
      ≤ Real.exp (2*c*(1+Real.log n)/(1-c)) / (1 + c/(n:ℝ))^T := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hcn : (0:ℝ) < c/(n:ℝ) := div_pos hc0 hn0
  have hz : (1:ℝ) ≤ 1 + c/(n:ℝ) := by linarith
  have hD : ∀ j, j < n → 0 < 1 - (1 + c/(n:ℝ)) * (1 - pp n j) := pos_denom n hn c hc0 hc1
  rw [stopTailProb_eq n hn x T]
  have h1 : 1 - markDone n x T ≤ Psi n (1+c/(n:ℝ)) x T := tail_le_Psi n _ hz hn hD x T
  have h2 : Psi n (1+c/(n:ℝ)) x T ≤ AA n (1+c/(n:ℝ)) 0 / (1+c/(n:ℝ))^T :=
    Psi_le n _ hz hn hD x T
  have h3 : AA n (1+c/(n:ℝ)) 0 / (1+c/(n:ℝ))^T
      ≤ Real.exp (2*c*(1+Real.log n)/(1-c)) / (1+c/(n:ℝ))^T := by
    have hpow : (0:ℝ) < (1+c/(n:ℝ))^T := by positivity
    gcongr
    exact AA_zero_le n hn c hc0 hc1
  linarith

lemma markDone_le_one (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) (t : ℕ) :
    markDone n x t ≤ 1 := by
  have h := one_sub_markDone n hn x t
  have h2 : (0:ℝ) ≤ ∑ b ∈ Finset.univ.filter
      (fun b : Equiv.Perm (Fin n) × Finset (Fin n) => b.2 ≠ Finset.univ), augLaw n x t b :=
    Finset.sum_nonneg (fun b _ => augLaw_nonneg n x t b)
  linarith

lemma markDone_tendsto (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) :
    Filter.Tendsto (fun t => markDone n x t) Filter.atTop (nhds 1) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set c : ℝ := 1/2 with hc
  have hc0 : (0:ℝ) < c := by norm_num
  have hc1 : c < 1 := by norm_num
  set z : ℝ := 1 + c/(n:ℝ) with hzdef
  have hz1 : (1:ℝ) < z := by
    have := div_pos hc0 hn0
    rw [hzdef]; linarith
  set C : ℝ := Real.exp (2*c*(1+Real.log n)/(1-c)) with hC
  have hlim : Filter.Tendsto (fun T : ℕ => C / z ^ T) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun T : ℕ => (z⁻¹) ^ T) Filter.atTop (nhds 0) := by
      refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
      rw [inv_lt_one_iff₀]
      right; exact hz1
    have h2 : Filter.Tendsto (fun T : ℕ => C * (z⁻¹) ^ T) Filter.atTop (nhds (C * 0)) :=
      h1.const_mul C
    rw [mul_zero] at h2
    refine h2.congr (fun T => ?_)
    rw [inv_pow, ← div_eq_mul_inv]
  have hsq : Filter.Tendsto (fun t : ℕ => 1 - markDone n x t) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun t => ?_) (fun t => ?_)
    · have := markDone_le_one n hn x t; linarith
    · have h := stopTail_le n hn c hc0 hc1 x t
      rw [stopTailProb_eq n hn x t] at h
      exact h
  have : Filter.Tendsto (fun t : ℕ => 1 - (1 - markDone n x t)) Filter.atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hsq
  rw [sub_zero] at this
  exact this.congr (fun t => by ring)

lemma stopAtProb_nonneg (n : ℕ) (x y : Equiv.Perm (Fin n)) (t : ℕ) :
    0 ≤ stopAtProb (randomTranspositions n) x (rtRule n) t y := by
  refine Finset.sum_nonneg (fun ω _ => ?_)
  by_cases hc : ω 0 = x ∧ ω (Fin.last t) = y
  · rw [if_pos hc]
    refine mul_nonneg (mul_nonneg ?_ ?_) (rtRule_isStoppingRule n t ω).1
    · exact Finset.prod_nonneg (fun i _ => transpositionDist_nonneg n _)
    · exact Finset.prod_nonneg (fun u _ => by
        have := (rtRule_isStoppingRule n u.val (pathPrefix ω u)).2
        linarith)
  · rw [if_neg hc]

lemma rtRule_hasSum (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) :
    (∑' t : ℕ, ∑ y : Equiv.Perm (Fin n),
      stopAtProb (randomTranspositions n) x (rtRule n) t y) = 1 := by
  set f : ℕ → ℝ := fun t => ∑ y : Equiv.Perm (Fin n),
    stopAtProb (randomTranspositions n) x (rtRule n) t y with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t =>
    Finset.sum_nonneg (fun y _ => stopAtProb_nonneg n x y t)
  have hpart : ∀ t : ℕ, ∑ u ∈ Finset.range (t+1), f u = markDone n x t :=
    partial_sum_stopAtProb n hn x
  have hsummable : Summable f := by
    refine summable_of_sum_range_le (c := 1) hf0 (fun m => ?_)
    match m with
    | 0 => simpa using markDone_le_one n hn x 0
    | (m+1) => rw [hpart m]; exact markDone_le_one n hn x m
  have htend : Filter.Tendsto (fun m : ℕ => ∑ u ∈ Finset.range m, f u)
      Filter.atTop (nhds 1) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    exact (markDone_tendsto n hn x).congr (fun m => (hpart m).symm)
  exact (hsummable.hasSum_iff_tendsto_nat.mpr htend).tsum_eq

theorem rtRule_isStrongStationaryTime (n : ℕ) (hn : 1 ≤ n) (x : Equiv.Perm (Fin n)) :
    IsStrongStationaryTime (randomTranspositions n)
      (uniformDist (Equiv.Perm (Fin n))) x (rtRule n) :=
  ⟨rtRule_isStoppingRule n, rtRule_hasSum n hn x,
    fun t y => stopAtProb_eq_uniform n hn x t y⟩

/-! ### Assembling the mixing bound -/

lemma rt_isStochastic (n : ℕ) (hn : 1 ≤ n) : IsStochastic (randomTranspositions n) :=
  (group_walk_uniform_stationary (transpositionDist n) (transpositionDist_isDist n hn)).1

lemma rt_isStationary (n : ℕ) (hn : 1 ≤ n) :
    IsStationary (randomTranspositions n) (uniformDist (Equiv.Perm (Fin n))) :=
  (group_walk_uniform_stationary (transpositionDist n) (transpositionDist_isDist n hn)).2.1

lemma rt_irreducible (n : ℕ) (hn : 2 ≤ n) : Irreducible (randomTranspositions n) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  rw [show randomTranspositions n = groupWalk (transpositionDist n) from rfl,
    group_walk_irreducible_iff (transpositionDist n) (transpositionDist_isDist n hn1)]
  refine le_antisymm le_top ?_
  rw [← Equiv.Perm.closure_isSwap]
  refine Subgroup.closure_mono ?_
  rintro σ ⟨a, b, hab, rfl⟩
  show 0 < transpositionDist n (Equiv.swap a b)
  rw [transpositionDist_eq, swapCnt_swap hab]
  positivity

lemma log_one_add_ge (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    c / ((n:ℝ) + 1) ≤ Real.log (1 + c / (n:ℝ)) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hx : (0:ℝ) < (n:ℝ) / ((n:ℝ) + c) := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  have he : (n:ℝ) / ((n:ℝ) + c) - 1 = -(c / ((n:ℝ) + c)) := by
    field_simp
    try ring
  have hz1 : (1:ℝ) + c / (n:ℝ) ≠ 0 := by positivity
  have hlog : Real.log ((n:ℝ) / ((n:ℝ) + c)) = - Real.log (1 + c / (n:ℝ)) := by
    rw [← Real.log_inv]
    congr 1
    rw [eq_comm, inv_eq_iff_eq_inv]
    field_simp
    try ring
  rw [hlog, he] at h
  have h2 : c / ((n:ℝ) + 1) ≤ c / ((n:ℝ) + c) := by
    apply div_le_div_of_nonneg_left hc0.le (by positivity)
    linarith
  linarith

lemma four_le_exp_two : (4:ℝ) ≤ Real.exp 2 := by
  have h : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1:ℝ)]

lemma key_tail_quarter (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hn2 : 2 ≤ n)
    (hcond1 : 2 + 3*δ/4 ≤ (2+δ) * (n:ℝ) / ((n:ℝ)+1))
    (hcond2 : 3 + δ/2 + 2 * (4+δ)/δ ≤ (δ/4) * Real.log n)
    (x : Equiv.Perm (Fin n)) :
    stopTailProb (randomTranspositions n) x (rtRule n) ⌊(2+δ) * (n:ℝ) * Real.log n⌋₊
      ≤ 1/4 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
  have hlogn : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
  set c : ℝ := δ / (4 + δ) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hc1 : c < 1 := by
    rw [hcdef, div_lt_one (by linarith)]; linarith
  have hcinv : 2 / (1 - c) = 2 + δ/2 := by
    have h1 : 1 - c = 4 / (4 + δ) := by rw [hcdef]; field_simp; try ring; try ring
    rw [h1]
    field_simp
    try ring
  have hc2 : 2 * (4+δ)/δ = 2/c := by rw [hcdef]; field_simp; try ring; try ring
  set T : ℕ := ⌊(2+δ) * (n:ℝ) * Real.log n⌋₊ with hT
  have hTge : (2+δ) * (n:ℝ) * Real.log n - 1 ≤ (T:ℝ) := by
    have := Nat.lt_floor_add_one ((2+δ) * (n:ℝ) * Real.log n)
    rw [← hT] at this
    linarith
  have hbound := stopTail_le n hn1 c hc0 hc1 x T
  -- lower bound on the denominator
  have hlogge : c / ((n:ℝ) + 1) ≤ Real.log (1 + c / (n:ℝ)) :=
    log_one_add_ge n hn1 c hc0 hc1.le
  have hzpos : (0:ℝ) < 1 + c / (n:ℝ) := by positivity
  have hpow : Real.exp ((T:ℝ) * (c / ((n:ℝ)+1))) ≤ (1 + c/(n:ℝ))^T := by
    have h1 : (1 + c/(n:ℝ))^T = Real.exp ((T:ℝ) * Real.log (1 + c/(n:ℝ))) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [h1]
    exact Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) T])
  have hexp : Real.exp (2*c*(1+Real.log n)/(1-c)) / (1 + c/(n:ℝ))^T
      ≤ Real.exp (2*c*(1+Real.log n)/(1-c) - (T:ℝ) * (c / ((n:ℝ)+1))) := by
    rw [Real.exp_sub]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hpow
  -- the exponent is at most -2
  have hE : 2*c*(1+Real.log n)/(1-c) - (T:ℝ) * (c / ((n:ℝ)+1)) ≤ -2 := by
    have hfirst : 2*c*(1+Real.log n)/(1-c) = c * (2 + δ/2) * (1 + Real.log n) := by
      rw [← hcinv]; field_simp; try ring
    have hcpos : (0:ℝ) < c / ((n:ℝ)+1) := by positivity
    have hTterm : ((2+δ) * (n:ℝ) * Real.log n - 1) * (c / ((n:ℝ)+1))
        ≤ (T:ℝ) * (c / ((n:ℝ)+1)) :=
      mul_le_mul_of_nonneg_right hTge hcpos.le
    have hsecond : c * (2 + 3*δ/4) * Real.log n - c / ((n:ℝ)+1)
        ≤ ((2+δ) * (n:ℝ) * Real.log n - 1) * (c / ((n:ℝ)+1)) := by
      have h1 : c * (2 + 3*δ/4) * Real.log n
          ≤ (2+δ) * (n:ℝ) * Real.log n * (c / ((n:ℝ)+1)) := by
        have h2 : (2 + 3*δ/4) * Real.log n
            ≤ (2+δ) * (n:ℝ) / ((n:ℝ)+1) * Real.log n :=
          mul_le_mul_of_nonneg_right hcond1 hlogn
        calc c * (2 + 3*δ/4) * Real.log n = c * ((2 + 3*δ/4) * Real.log n) := by ring
          _ ≤ c * ((2+δ) * (n:ℝ) / ((n:ℝ)+1) * Real.log n) :=
              mul_le_mul_of_nonneg_left h2 hc0.le
          _ = (2+δ) * (n:ℝ) * Real.log n * (c / ((n:ℝ)+1)) := by ring
      linarith [h1]
    have hsmall : c / ((n:ℝ)+1) ≤ c := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hkey : c * (2 + δ/2) * (1 + Real.log n) - (c * (2 + 3*δ/4) * Real.log n
        - c / ((n:ℝ)+1)) ≤ -2 := by
      have hexpand : c * (2 + δ/2) * (1 + Real.log n) - c * (2 + 3*δ/4) * Real.log n
          = c * (2 + δ/2) - c * (δ/4) * Real.log n := by ring
      have hc3 : 3 + δ/2 + 2/c ≤ (δ/4) * Real.log n := by rw [← hc2]; exact hcond2
      have hmul : c * (3 + δ/2 + 2/c) ≤ c * ((δ/4) * Real.log n) :=
        mul_le_mul_of_nonneg_left hc3 hc0.le
      have hcc : c * (3 + δ/2 + 2/c) = c * (3 + δ/2) + 2 := by
        field_simp; try ring
      have hgoal : c * (2 + δ/2) * (1 + Real.log n) - (c * (2 + 3*δ/4) * Real.log n
          - c / ((n:ℝ)+1))
          = (c * (2 + δ/2) - c * (δ/4) * Real.log n) + c / ((n:ℝ)+1) := by
        rw [← hexpand]; ring
      rw [hgoal]
      have e1 : c * ((δ/4) * Real.log n) = c * (δ/4) * Real.log n := by ring
      have hmul2 : c * (3 + δ/2) + 2 ≤ c * (δ/4) * Real.log n := by
        linarith [hmul, hcc, e1]
      have e2 : c * (2 + δ/2) - c * (3 + δ/2) = -c := by ring
      linarith [hmul2, hsmall, e2]
    linarith [hfirst ▸ hkey, hTterm, hsecond]
  have hfin : Real.exp (2*c*(1+Real.log n)/(1-c) - (T:ℝ) * (c / ((n:ℝ)+1))) ≤ 1/4 := by
    refine le_trans (Real.exp_le_exp.mpr hE) ?_
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have h4 : ((1:ℝ)/4)⁻¹ = 4 := by norm_num
    rw [h4]
    exact four_le_exp_two
  linarith

/-- **Corollary 8.10** (LPW), the capstone of Chapter 8: the random
transpositions shuffle on `n` cards mixes in at most `(2 + o(1)) n log n`
steps. -/
theorem rt_mixing (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (tMix (randomTranspositions n) (uniformDist (Equiv.Perm (Fin n))) : ℝ) ≤
        (2 + δ) * n * Real.log n := by
  classical
  set e : ℝ := min δ 1 with he
  have he0 : 0 < e := lt_min hδ zero_lt_one
  have he1 : e ≤ 1 := min_le_right _ _
  have heδ : e ≤ δ := min_le_left _ _
  set L : ℝ := (4/e) * (3 + e/2 + 2*(4+e)/e) with hL
  set N : ℕ := max 2 (max (⌈(8 + 3*e)/e⌉₊ + 1) (⌈Real.exp L⌉₊ + 1)) with hN
  refine ⟨N, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
  have hlogn : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
  -- the two largeness conditions
  have hstep1 : (8 + 3*e)/e ≤ (n:ℝ) := by
    have h1 : (⌈(8 + 3*e)/e⌉₊ : ℝ) ≤ (n:ℝ) := by
      have : ⌈(8 + 3*e)/e⌉₊ ≤ n := by
        have := le_trans (le_trans (le_max_left _ _) (le_max_right 2 _)) hn
        omega
      exact_mod_cast this
    exact le_trans (Nat.le_ceil _) h1
  have hcond1 : 2 + 3*e/4 ≤ (2+e) * (n:ℝ) / ((n:ℝ)+1) := by
    rw [le_div_iff₀ (by linarith)]
    rw [div_le_iff₀ he0] at hstep1
    nlinarith
  have hstep2 : Real.exp L ≤ (n:ℝ) := by
    have h1 : (⌈Real.exp L⌉₊ : ℝ) ≤ (n:ℝ) := by
      have : ⌈Real.exp L⌉₊ ≤ n := by
        have := le_trans (le_trans (le_max_right _ _) (le_max_right 2 _)) hn
        omega
      exact_mod_cast this
    exact le_trans (Nat.le_ceil _) h1
  have hcond2 : 3 + e/2 + 2*(4+e)/e ≤ (e/4) * Real.log n := by
    have hlogL : L ≤ Real.log n := by
      have := Real.log_le_log (Real.exp_pos L) hstep2
      rwa [Real.log_exp] at this
    have h2 : (e/4) * L = 3 + e/2 + 2*(4+e)/e := by
      rw [hL]; field_simp; try ring
    calc 3 + e/2 + 2*(4+e)/e = (e/4) * L := h2.symm
      _ ≤ (e/4) * Real.log n := by
          refine mul_le_mul_of_nonneg_left hlogL (by positivity)
  -- the mixing bound at time `T`
  set T : ℕ := ⌊(2+e) * (n:ℝ) * Real.log n⌋₊ with hT
  have hdist : distStationary (randomTranspositions n)
      (uniformDist (Equiv.Perm (Fin n))) T ≤ 1/4 := by
    refine le_trans (strong_stationary_bound (randomTranspositions n)
      (rt_isStochastic n hn1) (rt_irreducible n hn2) (uniformDist (Equiv.Perm (Fin n)))
      (rt_isStationary n hn1) (rtRule n)
      (fun x => rtRule_isStrongStationaryTime n hn1 x) T) ?_
    refine ciSup_le (fun x => ?_)
    exact key_tail_quarter n e he0 he1 hn2 hcond1 hcond2 x
  have hmix : tMix (randomTranspositions n) (uniformDist (Equiv.Perm (Fin n))) ≤ T :=
    Nat.sInf_le hdist
  have hTle : (T : ℝ) ≤ (2+e) * (n:ℝ) * Real.log n := by
    rw [hT]
    exact Nat.floor_le (by positivity)
  have hfinal : (2+e) * (n:ℝ) * Real.log n ≤ (2+δ) * (n:ℝ) * Real.log n := by
    have : (0:ℝ) ≤ (n:ℝ) * Real.log n := by positivity
    nlinarith
  have hcast : (tMix (randomTranspositions n) (uniformDist (Equiv.Perm (Fin n))) : ℝ)
      ≤ (T:ℝ) := by exact_mod_cast hmix
  linarith

end
end MarkovMixing

open MarkovMixing

/-- **Corollary 8.10** (LPW), the capstone of Chapter 8: the random
transpositions shuffle on `n` cards mixes in at most `(2 + o(1)) n log n`
steps. -/
theorem solution (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (tMix (randomTranspositions n) (uniformDist (Equiv.Perm (Fin n))) : ℝ) ≤
        (2 + δ) * n * Real.log n :=
  MarkovMixing.rt_mixing δ hδ
