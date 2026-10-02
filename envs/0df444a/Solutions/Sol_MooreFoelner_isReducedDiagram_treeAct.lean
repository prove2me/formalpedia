-- Prove2me | solution 1 for MooreFoelner.isReducedDiagram_treeAct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T04:11:04.910567+00:00
-- url     : https://prove2.me/submissions/e07e7483-2b36-40c5-aed9-4e0722b10145

import Theorems.Thm_MooreFoelner_bijOn_Lf_Rf_and_diagramMul
import Theorems.Thm_MooreFoelner_isTree_treeAct_and_isPartialAction
import Theorems.Thm_MooreFoelner_isReducedDiagram_iff
import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, §2: trees, the partial action of `F` on trees, reduced diagrams (TreesBasic)

Targets: `isTree_iff` (#1), `isTree_treeAct_and_isPartialAction` (#2),
`isReducedDiagram_treeAct` (#6).
-/

namespace MooreFoelner.Dev.TreesBasic

open Classical CannonFloydParry MooreFoelner

/-! ### Infinite sequences and prefixes -/

/-- `u⁀y`. -/
def app (u : Seq) (y : ℕ → Bool) : ℕ → Bool :=
  fun n => if h : n < u.length then u.get ⟨n, h⟩ else y (n - u.length)

/-- The tail of `x` after its first `k` digits. -/
def shift (x : ℕ → Bool) (k : ℕ) : ℕ → Bool := fun n => x (n + k)

/-- The first `n` digits of `x`. -/
def pre (x : ℕ → Bool) (n : ℕ) : Seq := List.ofFn (fun i : Fin n => x i)

@[simp] lemma length_pre (x : ℕ → Bool) (n : ℕ) : (pre x n).length = n := by simp [pre]

lemma isInitialPart_pre (x : ℕ → Bool) (n : ℕ) : IsInitialPart (pre x n) x := by
  intro i hi
  simp [pre]

lemma isInitialPart_app (u : Seq) (y : ℕ → Bool) : IsInitialPart u (app u y) := by
  intro i hi
  simp [app, hi]

lemma ip_mono {u v : Seq} {x : ℕ → Bool} (huv : u <+: v) (hv : IsInitialPart v x) :
    IsInitialPart u x := by
  intro i hi
  have hi' : i < v.length := lt_of_lt_of_le hi huv.length_le
  have := hv i hi'
  rw [← this]
  simp only [List.get_eq_getElem]
  exact huv.getElem hi

lemma ip_prefix {u v : Seq} {x : ℕ → Bool} (hu : IsInitialPart u x)
    (hv : IsInitialPart v x) (hl : u.length ≤ v.length) : u <+: v := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_get (by simp [hl])
  intro n h1 h2
  have h3 : n < v.length := by simp at h2; omega
  simp only [List.get_eq_getElem, List.getElem_take]
  have e1 := hu n h1
  have e2 := hv n h3
  simp only [List.get_eq_getElem] at e1 e2
  rw [e1, e2]

lemma ip_comparable {u v : Seq} {x : ℕ → Bool} (hu : IsInitialPart u x)
    (hv : IsInitialPart v x) : u <+: v ∨ v <+: u := by
  rcases le_total u.length v.length with h | h
  · exact Or.inl (ip_prefix hu hv h)
  · exact Or.inr (ip_prefix hv hu h)

lemma app_shift {u : Seq} {x : ℕ → Bool} (hu : IsInitialPart u x) :
    app u (shift x u.length) = x := by
  funext n
  simp only [app, shift]
  split_ifs with h
  · exact hu n h
  · congr 1; omega

@[simp] lemma shift_app (u : Seq) (y : ℕ → Bool) : shift (app u y) u.length = y := by
  funext n
  simp [shift, app]

lemma app_append (u v : Seq) (y : ℕ → Bool) : app (u ++ v) y = app u (app v y) := by
  funext n
  simp only [app, List.get_eq_getElem, List.length_append, List.getElem_append]
  by_cases h1 : n < u.length
  · simp [h1, show n < u.length + v.length by omega]
  · by_cases h2 : n < u.length + v.length
    · simp [h1, h2, show n - u.length < v.length by omega]
    · simp [h1, h2, show ¬ n - u.length < v.length by omega]
      congr 1; omega

/-! ### Trees -/

section Trees

variable {T : Finset Seq}

lemma tree_exists (hT : IsTree T) (x : ℕ → Bool) : ∃ t ∈ T, IsInitialPart t x := by
  obtain ⟨t, ⟨ht, hx⟩, -⟩ := hT x
  exact ⟨t, ht, hx⟩

lemma tree_unique (hT : IsTree T) {x : ℕ → Bool} {t t' : Seq} (ht : t ∈ T) (ht' : t' ∈ T)
    (hx : IsInitialPart t x) (hx' : IsInitialPart t' x) : t = t' :=
  (hT x).unique ⟨ht, hx⟩ ⟨ht', hx'⟩

lemma tree_eq_of_prefix (hT : IsTree T) {s s' : Seq} (hs : s ∈ T) (hs' : s' ∈ T)
    (h : s <+: s') : s = s' :=
  tree_unique hT hs hs' (ip_mono h (isInitialPart_app s' (fun _ => false)))
    (isInitialPart_app s' (fun _ => false))

/-- Every sequence either extends an element of the tree or is a proper prefix of one. -/
lemma tree_cases (hT : IsTree T) (u : Seq) :
    (∃ s ∈ T, s <+: u) ∨ ∃ s ∈ T, u <+: s ∧ u ≠ s := by
  obtain ⟨s, hs, hx⟩ := tree_exists hT (app u (fun _ => false))
  rcases ip_comparable hx (isInitialPart_app u (fun _ => false)) with h | h
  · exact Or.inl ⟨s, hs, h⟩
  · by_cases hus : u = s
    · exact Or.inl ⟨s, hs, hus ▸ List.prefix_refl u⟩
    · exact Or.inr ⟨s, hs, h, hus⟩

lemma prefix_antisymm {u v : Seq} (h1 : u <+: v) (h2 : v <+: u) : u = v :=
  h1.eq_of_length (le_antisymm h1.length_le h2.length_le)

/-- The two alternatives of `IsTree.cases` exclude each other. -/
lemma tree_not_both (hT : IsTree T) {u s s' : Seq} (hs : s ∈ T) (h1 : s <+: u) (hs' : s' ∈ T)
    (h2 : u <+: s') (hne : u ≠ s') : False := by
  have := tree_eq_of_prefix hT hs hs' (h1.trans h2)
  subst this
  exact hne (prefix_antisymm h2 h1)

end Trees

/-! ### `sorted` -/

section Sorted

theorem pairwise_merge' {α : Type*} (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true) :
    ∀ (l₁ l₂ : List α), (∀ a ∈ l₁, ∀ b ∈ l₂, le a b = true ∨ le b a = true) →
      l₁.Pairwise (fun a b => le a b = true) → l₂.Pairwise (fun a b => le a b = true) →
      (List.merge l₁ l₂ le).Pairwise (fun a b => le a b = true) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ _ h₂; simpa using h₂
  | cons x l₁ ih₁ =>
    intro l₂
    induction l₂ with
    | nil => intro _ h₁ _; simpa using h₁
    | cons y l₂ ih₂ =>
      intro htot h₁ h₂
      rw [List.cons_merge_cons]
      split <;> rename_i h
      · apply List.Pairwise.cons
        · intro z m
          rw [List.mem_merge, List.mem_cons] at m
          rcases m with (m | rfl | m)
          · exact List.rel_of_pairwise_cons h₁ m
          · exact h
          · exact trans _ _ _ h (List.rel_of_pairwise_cons h₂ m)
        · exact ih₁ _ (fun a ha b hb => htot a (List.mem_cons_of_mem _ ha) b hb) h₁.tail h₂
      · have hyx : le y x = true := by
          rcases htot x List.mem_cons_self y List.mem_cons_self with h' | h'
          · exact absurd h' h
          · exact h'
        apply List.Pairwise.cons
        · intro z m
          rw [List.mem_merge, List.mem_cons] at m
          rcases m with ((rfl | m) | m)
          · exact hyx
          · exact trans _ _ _ hyx (List.rel_of_pairwise_cons h₁ m)
          · exact List.rel_of_pairwise_cons h₂ m
        · exact ih₂ (fun a ha b hb => htot a ha b (List.mem_cons_of_mem _ hb)) h₁ h₂.tail

theorem pairwise_mergeSort' {α : Type*} (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true) :
    ∀ (l : List α), l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → le a b = true ∨ le b a = true) →
      (l.mergeSort le).Pairwise (fun a b => le a b = true)
  | [], _, _ => by simp
  | [a], _, _ => by simp
  | a :: b :: xs, hnd, htot => by
    simp only [List.mergeSort, List.MergeSort.Internal.splitInTwo_fst,
      List.MergeSort.Internal.splitInTwo_snd]
    have hlen1 : (List.take ((xs.length + 1 + 1 + 1) / 2) (a :: b :: xs)).length <
        xs.length + 1 + 1 := by simp; omega
    have hlen2 : (List.drop ((xs.length + 1 + 1 + 1) / 2) (a :: b :: xs)).length <
        xs.length + 1 + 1 := by simp; omega
    have hd := List.disjoint_take_drop hnd (le_refl ((xs.length + 1 + 1 + 1) / 2))
    apply pairwise_merge' le trans
    · intro u hu v hv
      rw [List.mem_mergeSort] at hu hv
      have hne : u ≠ v := by
        rintro rfl
        exact hd hu hv
      exact htot u (List.mem_of_mem_take hu) v (List.mem_of_mem_drop hv) hne
    · exact pairwise_mergeSort' le trans _ (hnd.sublist (List.take_sublist _ _))
        (fun u hu v hv => htot u (List.mem_of_mem_take hu) v (List.mem_of_mem_take hv))
    · exact pairwise_mergeSort' le trans _ (hnd.sublist (List.drop_sublist _ _))
        (fun u hu v hv => htot u (List.mem_of_mem_drop hu) v (List.mem_of_mem_drop hv))
termination_by l => l.length

lemma sorted_perm (T : Finset Seq) : (sorted T).Perm T.toList := List.mergeSort_perm _ _

lemma mem_sorted {T : Finset Seq} {u : Seq} : u ∈ sorted T ↔ u ∈ T := by
  rw [(sorted_perm T).mem_iff, Finset.mem_toList]

lemma length_sorted (T : Finset Seq) : (sorted T).length = T.card := by
  rw [(sorted_perm T).length_eq, Finset.length_toList]

lemma nodup_sorted (T : Finset Seq) : (sorted T).Nodup :=
  (sorted_perm T).nodup_iff.mpr T.nodup_toList

lemma lexLt_trans {u v w : Seq} (h1 : LexLt u v) (h2 : LexLt v w) : LexLt u w :=
  lt_trans (α := List Bool) h1 h2

lemma lexLt_irrefl (u : Seq) : ¬ LexLt u u := lt_irrefl (α := List Bool) u

lemma lexLt_asymm {u v : Seq} (h : LexLt u v) : ¬ LexLt v u := lt_asymm (α := List Bool) h

lemma lexLt_total {u v : Seq} (h : u ≠ v) : LexLt u v ∨ LexLt v u :=
  lt_or_gt_of_ne (α := List Bool) h

lemma sorted_pairwise (T : Finset Seq) : (sorted T).Pairwise LexLt := by
  have := pairwise_mergeSort' (fun u v : Seq => decide (LexLt u v))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; exact lexLt_trans h1 h2)
    T.toList T.nodup_toList
    (fun a _ b _ hab => by simp only [decide_eq_true_eq]; exact lexLt_total hab)
  exact this.imp (fun h => by simpa using h)

lemma nodup_of_pairwise_lexLt {l : List Seq} (hl : l.Pairwise LexLt) : l.Nodup :=
  hl.imp (fun {a b} (h : LexLt a b) (e : a = b) => lexLt_irrefl b (by rw [e] at h; exact h))

/-- A strictly `<_lex`-increasing enumeration of `T` is `sorted T`. -/
lemma sorted_eq_of {T : Finset Seq} {l : List Seq} (hl : l.Pairwise LexLt)
    (hmem : ∀ u, u ∈ l ↔ u ∈ T) : sorted T = l := by
  apply List.Perm.eq_of_pairwise (le := LexLt) _ (sorted_pairwise T) hl
  · rw [List.perm_ext_iff_of_nodup (nodup_sorted T) (nodup_of_pairwise_lexLt hl)]
    intro u; rw [mem_sorted, hmem]
  · intro a b _ _ h1 h2; exact absurd h2 (lexLt_asymm h1)

lemma sorted_get_mem (T : Finset Seq) (i : ℕ) (hi : i < (sorted T).length) :
    (sorted T).get ⟨i, hi⟩ ∈ T :=
  mem_sorted.mp (List.get_mem _ _)

lemma exists_get_of_mem {T : Finset Seq} {u : Seq} (hu : u ∈ T) :
    ∃ i, ∃ hi : i < (sorted T).length, (sorted T).get ⟨i, hi⟩ = u := by
  obtain ⟨⟨i, hi⟩, h⟩ := List.mem_iff_get.mp (mem_sorted.mpr hu)
  exact ⟨i, hi, h⟩

lemma sorted_get_inj (T : Finset Seq) {i j : ℕ} (hi : i < (sorted T).length)
    (hj : j < (sorted T).length) (h : (sorted T).get ⟨i, hi⟩ = (sorted T).get ⟨j, hj⟩) :
    i = j := by
  simpa using (nodup_sorted T).getElem_inj_iff.mp (by simpa using h)

end Sorted

/-! ### Dyadic intervals -/

section Real

lemma seqVal_nil : seqVal [] = 0 := by simp [seqVal]

lemma seqVal_cons (b : Bool) (u : Seq) :
    seqVal (b :: u) = (if b then 1/2 else 0) + seqVal u / 2 := by
  simp only [seqVal]
  have : ∀ (n : ℕ) (g : Fin (n+1) → Bool),
      (∑ i : Fin (n+1), if g i = true then (1/2 : ℝ) ^ (i.1 + 1) else 0) =
      (if g 0 then 1/2 else 0) +
        (∑ i : Fin n, if g i.succ = true then (1/2 : ℝ) ^ (i.1 + 1) else 0) / 2 := by
    intro n g
    rw [Fin.sum_univ_succ, Finset.sum_div]
    congr 1
    · split_ifs <;> norm_num
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ]
      split_ifs <;> ring
  exact this u.length (fun i => (b :: u).get i)

lemma seqVal_append (u v : Seq) : seqVal (u ++ v) = seqVal u + seqVal v * (1/2) ^ u.length := by
  induction u with
  | nil => simp [seqVal_nil]
  | cons b u ih =>
    rw [List.cons_append, seqVal_cons, seqVal_cons, ih, List.length_cons, pow_succ]
    ring

lemma seqVal_nonneg (u : Seq) : 0 ≤ seqVal u := by
  induction u with
  | nil => simp [seqVal_nil]
  | cons b u ih => rw [seqVal_cons]; split_ifs <;> positivity

lemma half_pow_pos (n : ℕ) : 0 < (1/2 : ℝ) ^ n := by positivity

lemma seqVal_add_le (u : Seq) : seqVal u + (1/2) ^ u.length ≤ 1 := by
  induction u with
  | nil => simp [seqVal_nil]
  | cons b u ih =>
    rw [seqVal_cons, List.length_cons, pow_succ]
    split_ifs <;> linarith

lemma seqVal_lt_one (u : Seq) : seqVal u < 1 := by
  linarith [seqVal_add_le u, half_pow_pos u.length]

lemma half_pow_inj {m n : ℕ} (h : (1/2 : ℝ) ^ m = (1/2) ^ n) : m = n :=
  pow_right_injective₀ (by norm_num) (by norm_num) h

lemma seqVal_inj : ∀ {u v : Seq}, u.length = v.length → seqVal u = seqVal v → u = v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: u, c :: v, h, h' => by
    rw [seqVal_cons, seqVal_cons] at h'
    have hl : u.length = v.length := by simpa using h
    have := seqVal_lt_one u; have := seqVal_lt_one v
    have := seqVal_nonneg u; have := seqVal_nonneg v
    cases b <;> cases c <;> simp at h'
    · rw [seqVal_inj hl (by linarith)]
    · linarith
    · linarith
    · rw [seqVal_inj hl (by linarith)]

/-- For sequences that are not prefixes of one another, `<_lex` puts the dyadic interval of the
first to the left of that of the second. -/
lemma lexLt_seqVal {u v : Seq} (h : LexLt u v) (hnp : ¬ u <+: v) :
    seqVal u + (1/2) ^ u.length ≤ seqVal v := by
  induction h with
  | nil => exact absurd (List.nil_prefix) hnp
  | @cons a l₁ l₂ _ ih =>
    rw [List.cons_prefix_cons] at hnp
    have := ih (fun h => hnp ⟨rfl, h⟩)
    rw [seqVal_cons, seqVal_cons, List.length_cons, pow_succ]
    linarith
  | @rel a₁ l₁ a₂ l₂ h =>
    have := seqVal_add_le l₁
    have := seqVal_nonneg l₂
    rw [seqVal_cons, seqVal_cons, List.length_cons, pow_succ]
    cases a₁ <;> cases a₂
    · exact absurd h (by decide)
    · simp only [Bool.false_eq_true, ↓reduceIte]; linarith
    · exact absurd h (by decide)
    · exact absurd h (by decide)

/-- `x` lies in the closed dyadic interval of `u`. -/
def inI (u : Seq) (x : ℝ) : Prop := seqVal u ≤ x ∧ x ≤ seqVal u + (1/2) ^ u.length

lemma inI_unit {u : Seq} {x : ℝ} (h : inI u x) : x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_trans (seqVal_nonneg u) h.1, le_trans h.2 (seqVal_add_le u)⟩

lemma inI_append {u w : Seq} {x : ℝ} (h : inI (u ++ w) x) : inI u x := by
  obtain ⟨h1, h2⟩ := h
  simp only [seqVal_append, List.length_append, pow_add] at h1 h2
  have := seqVal_nonneg w
  have := seqVal_add_le w
  have hp := half_pow_pos u.length
  constructor
  · nlinarith
  · nlinarith

lemma inI_left (u : Seq) : inI u (seqVal u) := ⟨le_rfl, by linarith [half_pow_pos u.length]⟩

lemma inI_right (u : Seq) : inI u (seqVal u + (1/2) ^ u.length) :=
  ⟨by linarith [half_pow_pos u.length], le_rfl⟩

/-! ### Affine maps between dyadic intervals -/

lemma two_zpow (a b : ℕ) : (2 : ℝ) ^ ((a : ℤ) - b) = (1/2) ^ b / (1/2) ^ a := by
  rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, one_div_pow, one_div_pow]
  field_simp

/-- The affine map from the dyadic interval of `s` onto that of `r`. -/
noncomputable def aff (s r : Seq) (x : ℝ) : ℝ :=
  seqVal r + (x - seqVal s) * (2 : ℝ) ^ (s.length - r.length : ℤ)

lemma aff_eq (s r : Seq) (x : ℝ) :
    aff s r x = seqVal r + (x - seqVal s) * ((1/2) ^ r.length / (1/2) ^ s.length) := by
  rw [aff, two_zpow]

lemma aff_append (s r w : Seq) (x : ℝ) : aff (s ++ w) (r ++ w) x = aff s r x := by
  rw [aff_eq, aff_eq, seqVal_append, seqVal_append, List.length_append, List.length_append,
    pow_add, pow_add]
  have := half_pow_pos s.length
  have := half_pow_pos r.length
  have := half_pow_pos w.length
  field_simp
  ring

lemma aff_left (s r : Seq) : aff s r (seqVal s) = seqVal r := by simp [aff]

lemma aff_right (s r : Seq) : aff s r (seqVal s + (1/2) ^ s.length) = seqVal r + (1/2) ^ r.length := by
  rw [aff_eq]
  have := half_pow_pos s.length
  field_simp
  ring

lemma aff_comp (s r q : Seq) (x : ℝ) : aff r q (aff s r x) = aff s q x := by
  rw [aff_eq, aff_eq, aff_eq]
  have := half_pow_pos s.length
  have := half_pow_pos r.length
  field_simp
  ring

lemma aff_self (s : Seq) (x : ℝ) : aff s s x = x := by
  rw [aff_eq]
  have := half_pow_pos s.length
  field_simp
  ring

lemma inI_aff {s r : Seq} {x : ℝ} (h : inI s x) : inI r (aff s r x) := by
  obtain ⟨h1, h2⟩ := h
  rw [aff_eq]
  have hs := half_pow_pos s.length
  have hr := half_pow_pos r.length
  have e : (x - seqVal s) * ((1/2) ^ r.length / (1/2) ^ s.length) =
      ((x - seqVal s) / (1/2) ^ s.length) * (1/2) ^ r.length := by ring
  have h3 : 0 ≤ (x - seqVal s) / (1/2) ^ s.length := div_nonneg (by linarith) hs.le
  have h4 : (x - seqVal s) / (1/2) ^ s.length ≤ 1 := by
    rw [div_le_one hs]; linarith
  rw [e]
  constructor
  · nlinarith
  · nlinarith

/-- `f` maps the dyadic interval of `s` affinely onto that of `r` (the clause of `Describes`). -/
def AffOn (f : UI ≃o UI) (s r : Seq) : Prop :=
  ∀ x : UI, seqVal s ≤ (x : ℝ) → (x : ℝ) ≤ seqVal s + (1 / 2 : ℝ) ^ s.length →
    ((f x : UI) : ℝ) = seqVal r + ((x : ℝ) - seqVal s) * (2 : ℝ) ^ (s.length - r.length : ℤ)

lemma affOn_apply {f : UI ≃o UI} {s r : Seq} (h : AffOn f s r) {x : UI} (hx : inI s x) :
    ((f x : UI) : ℝ) = aff s r x := h x hx.1 hx.2

lemma affOn_of_apply {f : UI ≃o UI} {s r : Seq}
    (h : ∀ x : UI, inI s x → ((f x : UI) : ℝ) = aff s r x) : AffOn f s r :=
  fun x h1 h2 => h x ⟨h1, h2⟩

/-- The point `x` of a dyadic interval, as a point of `[0,1]`. -/
def mkUI {u : Seq} {x : ℝ} (h : inI u x) : UI := ⟨x, inI_unit h⟩

lemma affOn_unique {f : UI ≃o UI} {s r r' : Seq} (h1 : AffOn f s r) (h2 : AffOn f s r') :
    r = r' := by
  have eL1 := affOn_apply h1 (x := mkUI (inI_left s)) (inI_left s)
  have eL2 := affOn_apply h2 (x := mkUI (inI_left s)) (inI_left s)
  have eR1 := affOn_apply h1 (x := mkUI (inI_right s)) (inI_right s)
  have eR2 := affOn_apply h2 (x := mkUI (inI_right s)) (inI_right s)
  simp only [mkUI, aff_left, aff_right] at eL1 eL2 eR1 eR2
  have hv : seqVal r = seqVal r' := by rw [← eL1, eL2]
  have hl : r.length = r'.length := by
    apply half_pow_inj
    linarith
  exact seqVal_inj hl hv

lemma affOn_append {f : UI ≃o UI} {s r : Seq} (h : AffOn f s r) (w : Seq) :
    AffOn f (s ++ w) (r ++ w) :=
  affOn_of_apply fun x hx => by rw [affOn_apply h (inI_append hx), aff_append]

lemma affOn_comp {f g : UI ≃o UI} {s r q : Seq} (hg : AffOn g s r) (hf : AffOn f r q) :
    AffOn (f * g) s q := by
  refine affOn_of_apply fun x hx => ?_
  have e1 := affOn_apply hg hx
  have hgx : inI r ((g x : UI) : ℝ) := by rw [e1]; exact inI_aff hx
  show ((f (g x) : UI) : ℝ) = _
  rw [affOn_apply hf hgx, e1, aff_comp]

lemma affOn_symm {f : UI ≃o UI} {s r : Seq} (h : AffOn f s r) : AffOn f⁻¹ r s := by
  refine affOn_of_apply fun y hy => ?_
  have hx : inI s (aff r s y) := inI_aff hy
  have e := affOn_apply h (x := mkUI hx) hx
  simp only [mkUI, aff_comp, aff_self] at e
  have h' : f (mkUI hx) = y := Subtype.ext e
  have h'' : f⁻¹ y = mkUI hx := by
    have := RelIso.inv_apply_self f (mkUI hx)
    rwa [h'] at this
  rw [h'']
  rfl

lemma affOn_eq_of_target {f : UI ≃o UI} {s s' r : Seq} (h1 : AffOn f s r) (h2 : AffOn f s' r) :
    s = s' :=
  affOn_unique (affOn_symm h1) (affOn_symm h2)

lemma affOn_lexLt {f : UI ≃o UI} {s s' r r' : Seq} (h1 : AffOn f s r) (h2 : AffOn f s' r')
    (hs : LexLt s s') (hsp : ¬ s <+: s') (hrp : ¬ r <+: r') (hrp' : ¬ r' <+: r) :
    LexLt r r' := by
  have hle := lexLt_seqVal hs hsp
  have eR := affOn_apply h1 (x := mkUI (inI_right s)) (inI_right s)
  have eL := affOn_apply h2 (x := mkUI (inI_left s')) (inI_left s')
  simp only [mkUI, aff_left, aff_right] at eR eL
  have hmono : f (mkUI (inI_right s)) ≤ f (mkUI (inI_left s')) := by
    apply f.monotone
    show seqVal s + (1/2) ^ s.length ≤ seqVal s'
    exact hle
  have hr : seqVal r + (1/2) ^ r.length ≤ seqVal r' := by
    have : ((f (mkUI (inI_right s)) : UI) : ℝ) ≤ ((f (mkUI (inI_left s')) : UI) : ℝ) := hmono
    simp only [mkUI] at this
    linarith
  have hne : r ≠ r' := by
    rintro rfl
    linarith [half_pow_pos r.length]
  rcases lexLt_total hne with h | h
  · exact h
  · have := lexLt_seqVal h hrp'
    linarith [half_pow_pos r.length, half_pow_pos r'.length]

end Real

/-! ### Tree diagrams: the maps they define -/

section Diagrams

variable {L R : Finset Seq}

lemma len_eq (hD : IsTreeDiagram L R) : (sorted L).length = (sorted R).length := by
  rw [length_sorted, length_sorted, hD.2.2]

lemma diagramAct_of_prefix (hD : IsTreeDiagram L R) {t : Seq} (i : ℕ)
    (hi : i < (sorted L).length) (hi' : i < (sorted R).length)
    (h : (sorted L).get ⟨i, hi⟩ <+: t) :
    diagramAct L R t = some ((sorted R).get ⟨i, hi'⟩ ++ t.drop ((sorted L).get ⟨i, hi⟩).length) := by
  unfold diagramAct
  dsimp only
  split
  · rename_i j hj
    have hpj : (sorted L).get j <+: t := by simpa using List.find?_some hj
    have hij : (sorted L).get ⟨i, hi⟩ = (sorted L).get j := by
      rcases List.prefix_or_prefix_of_prefix h hpj with h' | h'
      · exact tree_eq_of_prefix hD.1 (sorted_get_mem _ _ _) (sorted_get_mem _ _ _) h'
      · exact (tree_eq_of_prefix hD.1 (sorted_get_mem _ _ _) (sorted_get_mem _ _ _) h').symm
    have e := sorted_get_inj L hi j.2 hij
    obtain ⟨j, hj'⟩ := j
    simp only at e
    subst e
    rw [List.getElem?_eq_getElem hi']
    simp
  · rename_i hn
    exfalso
    have := List.find?_eq_none.mp hn ⟨i, hi⟩ (List.mem_finRange _)
    simp only [decide_eq_true_eq] at this
    exact this h

lemma diagramAct_eq_none' (_hD : IsTreeDiagram L R) {t : Seq}
    (h : ∀ i (hi : i < (sorted L).length), ¬ (sorted L).get ⟨i, hi⟩ <+: t) :
    diagramAct L R t = none := by
  unfold diagramAct
  dsimp only
  split
  · rename_i j hj
    have hpj : (sorted L).get j <+: t := by simpa using List.find?_some hj
    exact absurd hpj (h j.1 j.2)
  · rfl

lemma diagramAct_eq_some (hD : IsTreeDiagram L R) {t t' : Seq} (h : diagramAct L R t = some t') :
    ∃ i, ∃ (hi : i < (sorted L).length) (hi' : i < (sorted R).length),
      (sorted L).get ⟨i, hi⟩ <+: t ∧
        t' = (sorted R).get ⟨i, hi'⟩ ++ t.drop ((sorted L).get ⟨i, hi⟩).length := by
  by_cases hex : ∃ i, ∃ (hi : i < (sorted L).length), (sorted L).get ⟨i, hi⟩ <+: t
  · obtain ⟨i, hi, hp⟩ := hex
    have hi' : i < (sorted R).length := len_eq hD ▸ hi
    rw [diagramAct_of_prefix hD i hi hi' hp] at h
    exact ⟨i, hi, hi', hp, (Option.some.inj h).symm⟩
  · push Not at hex
    rw [diagramAct_eq_none' hD hex] at h
    exact absurd h (by simp)

lemma diagramMap_of_initial (hD : IsTreeDiagram L R) {x : ℕ → Bool} (i : ℕ)
    (hi : i < (sorted L).length) (hi' : i < (sorted R).length)
    (h : IsInitialPart ((sorted L).get ⟨i, hi⟩) x) :
    diagramMap L R x = app ((sorted R).get ⟨i, hi'⟩) (shift x ((sorted L).get ⟨i, hi⟩).length) := by
  unfold diagramMap
  dsimp only
  split
  · rename_i j hj
    have hpj : IsInitialPart ((sorted L).get j) x := by simpa using List.find?_some hj
    have hij : (sorted L).get ⟨i, hi⟩ = (sorted L).get j :=
      tree_unique hD.1 (sorted_get_mem _ _ _) (sorted_get_mem _ _ _) h hpj
    have e := sorted_get_inj L hi j.2 hij
    obtain ⟨j, hj'⟩ := j
    simp only at e
    subst e
    rw [List.getElem?_eq_getElem hi']
    rfl
  · rename_i hn
    exfalso
    have := List.find?_eq_none.mp hn ⟨i, hi⟩ (List.mem_finRange _)
    simp only [decide_eq_true_eq] at this
    exact this h

lemma exists_initial_index (hL : IsTree L) (x : ℕ → Bool) :
    ∃ i, ∃ hi : i < (sorted L).length, IsInitialPart ((sorted L).get ⟨i, hi⟩) x := by
  obtain ⟨s, hs, hx⟩ := tree_exists hL x
  obtain ⟨i, hi, rfl⟩ := exists_get_of_mem hs
  exact ⟨i, hi, hx⟩

/-- On the cylinder of `p`, the map of the diagram replaces the prefix `p` by `p · (L, R)`. -/
lemma diagramMap_app (hD : IsTreeDiagram L R) {p q : Seq} (h : diagramAct L R p = some q)
    (y : ℕ → Bool) : diagramMap L R (app p y) = app q y := by
  obtain ⟨i, hi, hi', hp, rfl⟩ := diagramAct_eq_some hD h
  obtain ⟨w, rfl⟩ := hp
  rw [diagramMap_of_initial hD i hi hi' (ip_mono (List.prefix_append _ w) (isInitialPart_app _ y)),
    app_append, shift_app, List.drop_left, app_append]

lemma affOn_of_diagramAct {f : UI ≃o UI} (h : Describes L R f) {p q : Seq}
    (hpq : diagramAct L R p = some q) : AffOn f p q := by
  obtain ⟨i, hi, hi', hp, rfl⟩ := diagramAct_eq_some h.1 hpq
  obtain ⟨w, rfl⟩ := hp
  rw [List.drop_left]
  exact affOn_append (h.2 i hi hi') w

/-- Two tree diagrams describing the same map define the same map on infinite sequences. -/
lemma diagramEquiv_of_describes {f : UI ≃o UI} {L' R' : Finset Seq} (h1 : Describes L R f)
    (h2 : Describes L' R' f) : DiagramEquiv L R L' R' := by
  intro x
  obtain ⟨i, hi, hx⟩ := exists_initial_index h1.1.1 x
  obtain ⟨j, hj, hx'⟩ := exists_initial_index h2.1.1 x
  set n := max ((sorted L).get ⟨i, hi⟩).length ((sorted L').get ⟨j, hj⟩).length
  have hp1 : (sorted L).get ⟨i, hi⟩ <+: pre x n :=
    ip_prefix hx (isInitialPart_pre x n) (by simp [n])
  have hp2 : (sorted L').get ⟨j, hj⟩ <+: pre x n :=
    ip_prefix hx' (isInitialPart_pre x n) (by simp [n])
  have e1 := diagramAct_of_prefix h1.1 i hi (len_eq h1.1 ▸ hi) hp1
  have e2 := diagramAct_of_prefix h2.1 j hj (len_eq h2.1 ▸ hj) hp2
  have hq := affOn_unique (affOn_of_diagramAct h1 e1) (affOn_of_diagramAct h2 e2)
  have hx0 : app (pre x n) (shift x n) = x := by
    have := app_shift (isInitialPart_pre x n)
    simpa using this
  rw [← hx0, diagramMap_app h1.1 e1, diagramMap_app h2.1 e2, hq]

end Diagrams

/-! ### Describing diagrams through a pairing of leaves -/

section Pairing

variable {L R : Finset Seq}

/-- A pair of trees with an `AffOn` pairing of their leaves describes `f`, and the pairing is the
one of `sorted`. -/
lemma describes_of_map {f : UI ≃o UI} (hL : IsTree L) (hR : IsTree R) (hc : L.card = R.card)
    (ψ : Seq → Seq) (hψ : ∀ s ∈ L, ψ s ∈ R ∧ AffOn f s (ψ s)) :
    sorted R = (sorted L).map ψ ∧ Describes L R f := by
  have hinj : ∀ s ∈ L, ∀ s' ∈ L, ψ s = ψ s' → s = s' := fun s hs s' hs' e =>
    affOn_eq_of_target (hψ s hs).2 (e ▸ (hψ s' hs').2)
  have hpw : ((sorted L).map ψ).Pairwise LexLt := by
    rw [List.pairwise_map]
    refine (sorted_pairwise L).imp_of_mem ?_
    intro a b ha hb hab
    rw [mem_sorted] at ha hb
    have hne : a ≠ b := by rintro rfl; exact lexLt_irrefl a hab
    have hψne : ψ a ≠ ψ b := fun e => hne (hinj a ha b hb e)
    apply affOn_lexLt (hψ a ha).2 (hψ b hb).2 hab
    · intro hp; exact hne (tree_eq_of_prefix hL ha hb hp)
    · intro hp; exact hψne (tree_eq_of_prefix hR (hψ a ha).1 (hψ b hb).1 hp)
    · intro hp; exact hψne (tree_eq_of_prefix hR (hψ b hb).1 (hψ a ha).1 hp).symm
  have hmem : ∀ u, u ∈ (sorted L).map ψ ↔ u ∈ R := by
    have hsub : ∀ u ∈ (sorted L).map ψ, u ∈ R := by
      intro u hu
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
      exact (hψ s (mem_sorted.mp hs)).1
    have hnd := nodup_of_pairwise_lexLt hpw
    have hcard : ((sorted L).map ψ).toFinset = R := by
      apply Finset.eq_of_subset_of_card_le
      · intro u hu; exact hsub u (List.mem_toFinset.mp hu)
      · rw [List.toFinset_card_of_nodup hnd, List.length_map, length_sorted, hc]
    intro u
    rw [← hcard, List.mem_toFinset]
  have hs : sorted R = (sorted L).map ψ := sorted_eq_of hpw hmem
  refine ⟨hs, ⟨hL, hR, hc⟩, ?_⟩
  intro i hiL hiR
  have : (sorted R).get ⟨i, hiR⟩ = ψ ((sorted L).get ⟨i, hiL⟩) := by
    simp only [List.get_eq_getElem]
    rw [List.getElem_of_eq hs]
    simp
  rw [this]
  exact (hψ _ (sorted_get_mem L i hiL)).2

/-- The leaf of `R` paired with the leaf `s` of `L`. -/
noncomputable def pairOf (L R : Finset Seq) (s : Seq) : Seq :=
  (sorted R).getD ((sorted L).idxOf s) []

lemma pairOf_get (i : ℕ) (hi : i < (sorted L).length) (hi' : i < (sorted R).length) :
    pairOf L R ((sorted L).get ⟨i, hi⟩) = (sorted R).get ⟨i, hi'⟩ := by
  simp only [pairOf, List.get_eq_getElem, (nodup_sorted L).idxOf_getElem i hi]
  rw [List.getD_eq_getElem]

lemma pairOf_mem_aff {f : UI ≃o UI} (h : Describes L R f) {s : Seq} (hs : s ∈ L) :
    pairOf L R s ∈ R ∧ AffOn f s (pairOf L R s) := by
  obtain ⟨i, hi, rfl⟩ := exists_get_of_mem hs
  have hi' : i < (sorted R).length := len_eq h.1 ▸ hi
  rw [pairOf_get i hi hi']
  exact ⟨sorted_get_mem R i hi', h.2 i hi hi'⟩

lemma pairOf_surj (hD : IsTreeDiagram L R) {r : Seq} (hr : r ∈ R) :
    ∃ s ∈ L, pairOf L R s = r := by
  obtain ⟨i, hi', rfl⟩ := exists_get_of_mem hr
  have hi : i < (sorted L).length := (len_eq hD).symm ▸ hi'
  exact ⟨_, sorted_get_mem L i hi, pairOf_get i hi hi'⟩

/-- Collapsing a node `t` of the domain tree whose interval `f` maps affinely onto a dyadic
interval gives a smaller tree diagram describing `f`. -/
lemma collapse {f : UI ≃o UI} (h : Describes L R f) {t t' : Seq}
    (ht : ∃ s ∈ L, t <+: s ∧ t ≠ s) (haff : AffOn f t t') :
    ∃ L'' R'' : Finset Seq, Describes L'' R'' f ∧ L''.card < L.card := by
  have hL := h.1.1
  have hR := h.1.2.1
  have hinj : ∀ s ∈ L, ∀ s' ∈ L, pairOf L R s = pairOf L R s' → s = s' := fun s hs s' hs' e =>
    affOn_eq_of_target (pairOf_mem_aff h hs).2 (e ▸ (pairOf_mem_aff h hs').2)
  -- leaves under `t` go under `t'`
  have ha : ∀ s ∈ L, t <+: s → t' <+: pairOf L R s := by
    intro s hs hts
    obtain ⟨w, rfl⟩ := hts
    rw [affOn_unique (pairOf_mem_aff h hs).2 (affOn_append haff w)]
    exact List.prefix_append _ _
  have hnb : ∀ s ∈ L, ¬ s <+: t := fun s hs hst => by
    obtain ⟨s0, hs0, h1, h2⟩ := ht
    exact tree_not_both hL hs hst hs0 h1 h2
  have hb1 : ∀ s ∈ L, t' <+: pairOf L R s → t <+: s := by
    intro s hs hp
    obtain ⟨c, hc⟩ := hp
    have h1 : AffOn f⁻¹ (pairOf L R s) s := affOn_symm (pairOf_mem_aff h hs).2
    have h2 : AffOn f⁻¹ (t' ++ c) (t ++ c) := affOn_append (affOn_symm haff) c
    rw [hc] at h2
    rw [affOn_unique h1 h2]
    exact List.prefix_append _ _
  have hb2 : ∀ r ∈ R, ¬ r <+: t' := by
    intro r hr hp
    obtain ⟨s, hs, rfl⟩ := pairOf_surj h.1 hr
    obtain ⟨c, hc⟩ := hp
    have h1 : AffOn f⁻¹ (pairOf L R s ++ c) (s ++ c) :=
      affOn_append (affOn_symm (pairOf_mem_aff h hs).2) c
    rw [hc] at h1
    have e := affOn_unique (affOn_symm haff) h1
    exact hnb s hs (e ▸ List.prefix_append s c)
  set L'' := insert t (L.filter (fun s => ¬ t <+: s)) with hL''def
  set R'' := insert t' (R.filter (fun r => ¬ t' <+: r)) with hR''def
  have hL'' : IsTree L'' := by
    intro x
    by_cases hx : IsInitialPart t x
    · refine ⟨t, ⟨Finset.mem_insert_self _ _, hx⟩, ?_⟩
      rintro s ⟨hs, hsx⟩
      rcases Finset.mem_insert.mp hs with rfl | hs
      · rfl
      · rw [Finset.mem_filter] at hs
        rcases ip_comparable hsx hx with h' | h'
        · exact absurd h' (hnb s hs.1)
        · exact absurd h' hs.2
    · obtain ⟨s, hs, hsx⟩ := tree_exists hL x
      have hns : ¬ t <+: s := fun h' => hx (ip_mono h' hsx)
      refine ⟨s, ⟨Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hs, hns⟩), hsx⟩, ?_⟩
      rintro s' ⟨hs', hs'x⟩
      rcases Finset.mem_insert.mp hs' with rfl | hs'
      · exact absurd hs'x hx
      · exact tree_unique hL (Finset.mem_filter.mp hs').1 hs hs'x hsx
  have hR'' : IsTree R'' := by
    intro x
    by_cases hx : IsInitialPart t' x
    · refine ⟨t', ⟨Finset.mem_insert_self _ _, hx⟩, ?_⟩
      rintro r ⟨hr, hrx⟩
      rcases Finset.mem_insert.mp hr with rfl | hr
      · rfl
      · rw [Finset.mem_filter] at hr
        rcases ip_comparable hrx hx with h' | h'
        · exact absurd h' (hb2 r hr.1)
        · exact absurd h' hr.2
    · obtain ⟨r, hr, hrx⟩ := tree_exists hR x
      have hnr : ¬ t' <+: r := fun h' => hx (ip_mono h' hrx)
      refine ⟨r, ⟨Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hr, hnr⟩), hrx⟩, ?_⟩
      rintro r' ⟨hr', hr'x⟩
      rcases Finset.mem_insert.mp hr' with rfl | hr'
      · exact absurd hr'x hx
      · exact tree_unique hR (Finset.mem_filter.mp hr').1 hr hr'x hrx
  have hfilt : (L.filter (fun s => ¬ t <+: s)).card = (R.filter (fun r => ¬ t' <+: r)).card := by
    apply Finset.card_nbij (pairOf L R)
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs ⊢
      exact ⟨(pairOf_mem_aff h hs.1).1, fun h' => hs.2 (hb1 s hs.1 h')⟩
    · intro s hs s' hs' e
      exact hinj s (Finset.mem_filter.mp hs).1 s' (Finset.mem_filter.mp hs').1 e
    · intro r hr
      rw [Finset.mem_coe, Finset.mem_filter] at hr
      obtain ⟨s, hs, rfl⟩ := pairOf_surj h.1 hr.1
      exact ⟨s, Finset.mem_filter.mpr ⟨hs, fun h' => hr.2 (ha s hs h')⟩, rfl⟩
  have htL : t ∉ L.filter (fun s => ¬ t <+: s) := by
    rw [Finset.mem_filter]; exact fun h' => h'.2 (List.prefix_refl t)
  have htR : t' ∉ R.filter (fun r => ¬ t' <+: r) := by
    rw [Finset.mem_filter]; exact fun h' => h'.2 (List.prefix_refl t')
  have hcard : L''.card = R''.card := by
    rw [hL''def, hR''def, Finset.card_insert_of_notMem htL, Finset.card_insert_of_notMem htR, hfilt]
  -- two leaves below `t`
  have hbelow : ∀ b : Bool, ∃ s ∈ L, (t ++ [b]) <+: s := by
    intro b
    rcases tree_cases hL (t ++ [b]) with ⟨s, hs, hsu⟩ | ⟨s, hs, hus, -⟩
    · rcases List.prefix_concat_iff.mp hsu with e | e
      · exact ⟨s, hs, e ▸ List.prefix_refl _⟩
      · exact absurd e (hnb s hs)
    · exact ⟨s, hs, hus⟩
  have htwo : 1 < (L.filter (fun s => t <+: s)).card := by
    obtain ⟨s0, hs0, h0⟩ := hbelow false
    obtain ⟨s1, hs1, h1⟩ := hbelow true
    rw [Finset.one_lt_card]
    refine ⟨s0, Finset.mem_filter.mpr ⟨hs0, (List.prefix_append _ _).trans h0⟩,
      s1, Finset.mem_filter.mpr ⟨hs1, (List.prefix_append _ _).trans h1⟩, ?_⟩
    rintro rfl
    have hp : (t ++ [false]) <+: (t ++ [true]) :=
      List.prefix_of_prefix_length_le h0 h1 (by simp)
    have := hp.eq_of_length (by simp)
    simp at this
  have hsplit : (L.filter (fun s => t <+: s)).card + (L.filter (fun s => ¬ t <+: s)).card =
      L.card := by
    convert Finset.card_filter_add_card_filter_not (s := L) (fun s => t <+: s)
  refine ⟨L'', R'', (describes_of_map hL'' hR'' hcard
    (fun s => if s = t then t' else pairOf L R s) ?_).2, ?_⟩
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp only [↓reduceIte]
      exact ⟨Finset.mem_insert_self _ _, haff⟩
    · have hne : s ≠ t := by
        rintro rfl; exact htL hs
      simp only [hne, ↓reduceIte]
      rw [Finset.mem_filter] at hs
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨(pairOf_mem_aff h hs.1).1, fun h' => hs.2 (hb1 s hs.1 h')⟩), (pairOf_mem_aff h hs.1).2⟩
  · rw [hL''def, Finset.card_insert_of_notMem htL]
    omega

end Pairing

/-! ### The reduced diagram of an element of `F` -/

section Reduced

/-- From #5: `(L_g, R_g)` is a reduced tree diagram describing `g`. -/
lemma reducedDiagram_spec (g : MooreF) :
    IsReducedDiagram (Lf (toMap g)) (Rf (toMap g)) ∧
      Describes (Lf (toMap g)) (Rf (toMap g)) (toMap g) :=
  ⟨bijOn_Lf_Rf_and_diagramMul.2.2.2.2.2.1.mapsTo (Set.mem_univ g),
    bijOn_Lf_Rf_and_diagramMul.2.2.2.2.2.2.1 g⟩

/-- `t · g = t'` exactly when `g` maps the dyadic interval of `t` affinely onto that of `t'`. -/
lemma seqAct_eq_some_iff (g : MooreF) (t t' : Seq) :
    seqAct t g = some t' ↔ AffOn (toMap g) t t' := by
  obtain ⟨hred, hdesc⟩ := reducedDiagram_spec g
  constructor
  · intro h
    exact affOn_of_diagramAct hdesc h
  · intro haff
    rcases tree_cases hdesc.1.1 t with ⟨s, hs, hst⟩ | hprop
    · obtain ⟨i, hi, rfl⟩ := exists_get_of_mem hs
      have e := diagramAct_of_prefix hdesc.1 i hi (len_eq hdesc.1 ▸ hi) hst
      show diagramAct _ _ t = some t'
      rw [e, affOn_unique haff (affOn_of_diagramAct hdesc e)]
    · exfalso
      obtain ⟨L'', R'', hD'', hlt⟩ := collapse hdesc hprop haff
      have he := diagramEquiv_of_describes hdesc hD''
      have := hred.2 L'' R'' hD''.1 he
      omega

lemma seqAct_inv (g : MooreF) (x y : Seq) : seqAct x g = some y ↔ seqAct y g⁻¹ = some x := by
  rw [seqAct_eq_some_iff, seqAct_eq_some_iff]
  constructor
  · exact affOn_symm
  · intro h
    have := affOn_symm h
    rwa [show toMap g⁻¹ = (toMap g)⁻¹ from rfl, inv_inv] at this

lemma treeAct_eq_some_iff (T T' : Finset Seq) (g : MooreF) :
    treeAct T g = some T' ↔ (∀ t ∈ T, ∃ t' ∈ T', seqAct t g = some t') ∧
      (∀ t' ∈ T', ∃ t ∈ T, seqAct t g = some t') := by
  unfold treeAct
  split
  · rename_i hall
    rw [Option.some.injEq]
    constructor
    · rintro rfl
      constructor
      · intro t ht
        exact ⟨_, Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩,
          (Option.some_get _).symm⟩
      · intro t' ht'
        obtain ⟨⟨t, ht⟩, -, rfl⟩ := Finset.mem_image.mp ht'
        exact ⟨t, ht, (Option.some_get _).symm⟩
    · rintro ⟨h1, h2⟩
      ext u
      rw [Finset.mem_image]
      constructor
      · rintro ⟨⟨t, ht⟩, -, rfl⟩
        obtain ⟨t', ht', e⟩ := h1 t ht
        rw [Option.get_of_eq_some _ e]
        exact ht'
      · intro hu
        obtain ⟨t, ht, e⟩ := h2 u hu
        exact ⟨⟨t, ht⟩, Finset.mem_attach _ _, Option.get_of_eq_some _ e⟩
  · rename_i hn
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h1, -⟩
    apply hn
    intro t ht
    obtain ⟨t', -, e⟩ := h1 t ht
    rw [e]
    rfl

end Reduced

end MooreFoelner.Dev.TreesBasic

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry in
open Dev.TreesBasic in
theorem solution (f g : MooreF) (S T T' : Finset Seq)
    (h : IsReducedDiagram S T) (hg : Describes S T (toMap g)) (hf : ActsProperlyOn f T)
    (hT' : treeAct T f = some T') :
    IsReducedDiagram S T' ∧ Describes S T' (toMap (g * f)) := by
  have hTT' : IsTree T' := isTree_treeAct_and_isPartialAction.1 T T' f hg.1.2.1 hT'
  obtain ⟨h1, h2⟩ := (treeAct_eq_some_iff T T' f).mp hT'
  set ψ0 : Seq → Seq := fun t => (seqAct t f).getD [] with hψ0def
  have hψ0 : ∀ t ∈ T, seqAct t f = some (ψ0 t) ∧ ψ0 t ∈ T' := by
    intro t ht
    obtain ⟨t', ht', e⟩ := h1 t ht
    simp only [ψ0, e, Option.getD_some]
    exact ⟨trivial, ht'⟩
  have hcard : T.card = T'.card := by
    apply Finset.card_nbij ψ0
    · intro t ht; exact (hψ0 t ht).2
    · intro t ht t₂ ht₂ e
      have a1 := (seqAct_inv f t _).mp (hψ0 t ht).1
      have a2 := (seqAct_inv f t₂ _).mp (hψ0 t₂ ht₂).1
      rw [e, a2] at a1
      exact (Option.some.inj a1).symm
    · intro t' ht'
      obtain ⟨t, ht, e⟩ := h2 t' ht'
      refine ⟨t, ht, ?_⟩
      simp [ψ0, e]
  set ψ : Seq → Seq := fun s => ψ0 (pairOf S T s) with hψdef
  have hψ : ∀ s ∈ S, ψ s ∈ T' ∧ AffOn (toMap (g * f)) s (ψ s) := by
    intro s hs
    obtain ⟨hmem, haff⟩ := pairOf_mem_aff hg hs
    obtain ⟨e, hm⟩ := hψ0 _ hmem
    exact ⟨hm, affOn_comp haff ((seqAct_eq_some_iff f _ _).mp e)⟩
  obtain ⟨hsorted, hdesc⟩ := describes_of_map hg.1.1 hTT' (hg.1.2.2.trans hcard) ψ hψ
  refine ⟨?_, hdesc⟩
  have hlenT : (sorted T).length = (sorted T').length := by
    rw [length_sorted, length_sorted, hcard]
  have hlast : ∀ j (hj : j < (sorted T').length) (hj' : j < (sorted T).length),
      ((sorted T').get ⟨j, hj⟩).getLast? = ((sorted T).get ⟨j, hj'⟩).getLast? := by
    intro j hj hj'
    have hjS : j < (sorted S).length := (len_eq hg.1).symm ▸ hj'
    have e1 : (sorted T').get ⟨j, hj⟩ = ψ ((sorted S).get ⟨j, hjS⟩) := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_of_eq hsorted]
      simp
    rw [e1, hψdef]
    simp only
    rw [pairOf_get j hjS hj']
    obtain ⟨t', e, hl⟩ := hf _ (sorted_get_mem T j hj')
    obtain ⟨e', -⟩ := hψ0 _ (sorted_get_mem T j hj')
    rw [e] at e'
    rw [← Option.some.inj e', hl]
  rw [isReducedDiagram_iff S T' hdesc.1]
  have hred := (isReducedDiagram_iff S T hg.1).mp h
  rintro ⟨i, hi, hi', c1, c2, c3, c4⟩
  apply hred
  have hiT : i + 1 < (sorted T).length := hlenT ▸ hi'
  refine ⟨i, hi, hiT, c1, ?_, c3, ?_⟩
  · rw [← hlast i (by omega) (by omega)]; exact c2
  · rw [← hlast (i + 1) hi' hiT]; exact c4
