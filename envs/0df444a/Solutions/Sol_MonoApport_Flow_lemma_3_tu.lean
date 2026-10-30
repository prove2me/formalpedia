-- Prove2me | solution 1 for MonoApport.Flow.lemma_3_tu
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:00:30.262381+00:00
-- url     : https://prove2.me/submissions/e12ab75e-1543-48f7-9915-654d26e4daee

import Mathlib
import Definitions.Def_MonoApport_Flow_Setting

open MonoApport.Flow Finset Matrix

namespace MonoTU

lemma range_mul {a b : ℤ} (ha : a ∈ Set.range (SignType.cast : SignType → ℤ))
    (hb : b ∈ Set.range (SignType.cast : SignType → ℤ)) :
    a * b ∈ Set.range (SignType.cast : SignType → ℤ) := by
  obtain ⟨s, rfl⟩ := ha; obtain ⟨t, rfl⟩ := hb
  exact ⟨s * t, by simp⟩

lemma range_of_pm {a : ℤ} (h : a = -1 ∨ a = 0 ∨ a = 1) :
    a ∈ Set.range (SignType.cast : SignType → ℤ) := by
  rcases h with rfl | rfl | rfl
  · exact ⟨-1, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

/-- A square integer matrix whose columns contain at most one `1`, at most one `-1`, and
otherwise zeros, has determinant in `{0, ±1}`. -/
theorem inc_det : ∀ (k : ℕ) (X : Matrix (Fin k) (Fin k) ℤ),
    (∀ i j, X i j = -1 ∨ X i j = 0 ∨ X i j = 1) →
    (∀ j i i', X i j = 1 → X i' j = 1 → i = i') →
    (∀ j i i', X i j = -1 → X i' j = -1 → i = i') →
    X.det ∈ Set.range (SignType.cast : SignType → ℤ) := by
  intro k
  induction k with
  | zero => intro X _ _ _; exact ⟨1, by simp⟩
  | succ k ih =>
    intro X hX hp hm
    by_cases hcol : ∃ j, ∀ i i', X i j ≠ 0 → X i' j ≠ 0 → i = i'
    · obtain ⟨j, hj⟩ := hcol
      by_cases hz : ∃ i, X i j ≠ 0
      · obtain ⟨i0, hi0⟩ := hz
        rw [det_succ_column X j, Finset.sum_eq_single i0]
        · apply range_mul (range_mul ?_ (range_of_pm (hX i0 j)))
          · apply ih
            · intro a b; exact hX _ _
            · intro b a a' h1 h2; exact Fin.succAbove_right_injective (hp _ _ _ h1 h2)
            · intro b a a' h1 h2; exact Fin.succAbove_right_injective (hm _ _ _ h1 h2)
          · rcases neg_one_pow_eq_or ℤ ((i0 : ℕ) + (j : ℕ)) with h | h <;> rw [h]
            · exact ⟨1, by simp⟩
            · exact ⟨-1, by simp⟩
        · intro i _ hi
          have : X i j = 0 := by
            by_contra hc; exact hi (hj i i0 hc hi0)
          rw [this]; ring
        · intro h; exact absurd (mem_univ _) h
      · push Not at hz
        rw [det_eq_zero_of_column_eq_zero j hz]
        exact ⟨0, by simp⟩
    · push Not at hcol
      have hsum : ∀ j, ∑ i, X i j = 0 := by
        intro j
        obtain ⟨a, b, ha, hb, hab⟩ := hcol j
        have hpm : (X a j = 1 ∧ X b j = -1) ∨ (X a j = -1 ∧ X b j = 1) := by
          rcases hX a j with h1 | h1 | h1 <;> rcases hX b j with h2 | h2 | h2
          · exact absurd (hm j a b h1 h2) hab
          · exact absurd h2 hb
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd h1 ha
          · exact absurd h1 ha
          · exact absurd h1 ha
          · exact Or.inl ⟨h1, h2⟩
          · exact absurd h2 hb
          · exact absurd (hp j a b h1 h2) hab
        have key : ∀ (u v : Fin (k + 1)), u ≠ v → X u j = 1 → X v j = -1 →
            ∑ i, X i j = 0 := by
          intro u v huv hu hv
          have : ∀ i, X i j = (if i = u then 1 else 0) - (if i = v then 1 else 0) := by
            intro i
            by_cases hiu : i = u
            · subst hiu; simp [huv, hu]
            · by_cases hiv : i = v
              · subst hiv; simp [hiu, hv]
              · simp only [hiu, hiv, if_false, sub_zero]
                rcases hX i j with h | h | h
                · exact absurd (hm j i v h hv) hiv
                · exact h
                · exact absurd (hp j i u h hu) hiu
          rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib]
          simp
        rcases hpm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact key a b hab h1 h2
        · exact key b a (Ne.symm hab) h2 h1
      have : X.det = 0 := by
        rw [← exists_vecMul_eq_zero_iff]
        refine ⟨fun _ => 1, fun h => by simpa using congrFun h 0, ?_⟩
        funext j
        simp only [vecMul, dotProduct, one_mul, Pi.zero_apply]
        exact hsum j
      rw [this]; exact ⟨0, by simp⟩


/-! ### The underlying matrix with rows `e_{i,t}` and `e′_t` -/

variable {n L : ℕ}

def NN (n L : ℕ) : Matrix ((Fin n × Fin L) ⊕ Fin L) (Fin n × Fin L) ℤ :=
  fun r c => match r with
    | Sum.inl it => if c.1 = it.1 ∧ c.2 ≤ it.2 then 1 else 0
    | Sum.inr t => if c.2 = t then 1 else 0

section Rows

variable {k : ℕ} (f : Fin k → (Fin n × Fin L) ⊕ Fin L)

/-- `i'` is the immediate predecessor of `i` among the selected rows of the same state. -/
def IsPred (i' i : Fin k) : Prop :=
  ∃ (j : Fin n) (t t' : Fin L), f i = Sum.inl (j, t) ∧ f i' = Sum.inl (j, t') ∧ t' < t ∧
    ∀ (i'' : Fin k) (t'' : Fin L), f i'' = Sum.inl (j, t'') → t'' < t → t'' ≤ t'

def tm (r : (Fin n × Fin L) ⊕ Fin L) : ℕ := match r with
  | Sum.inl x => x.2.val
  | Sum.inr _ => 0

variable {f}

lemma IsPred.tm_lt {i' i : Fin k} (h : IsPred f i' i) : tm (f i') < tm (f i) := by
  obtain ⟨j, t, t', h1, h2, h3, _⟩ := h
  rw [h1, h2]; exact h3

lemma IsPred.unique (hf : Function.Injective f) {i1 i2 i : Fin k} (h1 : IsPred f i1 i)
    (h2 : IsPred f i2 i) : i1 = i2 := by
  obtain ⟨j, t, t1, e1, e1', lt1, max1⟩ := h1
  obtain ⟨j2, t2', t2, e2, e2', lt2, max2⟩ := h2
  rw [e1] at e2
  simp only [Sum.inl.injEq, Prod.mk.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  have a := max1 i2 t2 e2' lt2
  have b := max2 i1 t1 e1' lt1
  have : t1 = t2 := le_antisymm b a
  subst this
  exact hf (e1'.trans e2'.symm)

open Classical in
noncomputable def pr (f : Fin k → (Fin n × Fin L) ⊕ Fin L) (i : Fin k) : Option (Fin k) :=
  if h : ∃ i', IsPred f i' i then some h.choose else none

lemma pr_spec {i i' : Fin k} (h : pr f i = some i') : IsPred f i' i := by
  unfold pr at h
  split_ifs at h with hh
  · simp only [Option.some.injEq] at h; subst h; exact hh.choose_spec

lemma pr_none {i : Fin k} (h : pr f i = none) (i' : Fin k) : ¬ IsPred f i' i := by
  unfold pr at h
  split_ifs at h with hh
  · exact fun h' => hh ⟨i', h'⟩

lemma pr_exists {i : Fin k} {j : Fin n} {t : Fin L} (hi : f i = Sum.inl (j, t)) (i'' : Fin k)
    (t'' : Fin L) (h'' : f i'' = Sum.inl (j, t'')) (hlt : t'' < t) : ∃ i', IsPred f i' i := by
  classical
  set S := univ.filter (fun a : Fin k => ∃ t' : Fin L, f a = Sum.inl (j, t') ∧ t' < t)
  have hne : S.Nonempty := ⟨i'', by simp [S]; exact ⟨t'', h'', hlt⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image S (fun a => tm (f a)) hne
  simp only [S, mem_filter, mem_univ, true_and] at ha
  obtain ⟨ta, hfa, hta⟩ := ha
  refine ⟨a, j, t, ta, hi, hfa, hta, ?_⟩
  intro b tb hfb htb
  have := hmax b (by simp [S]; exact ⟨tb, hfb, htb⟩)
  rw [hfa, hfb] at this
  exact this

/-- The row-operation matrix: subtract from each `e_{j,t}` row its predecessor, and negate the
`e′_t` rows. -/
noncomputable def VV (f : Fin k → (Fin n × Fin L) ⊕ Fin L) : Matrix (Fin k) (Fin k) ℤ :=
  fun i i' => (if i' = i then (if (f i).isLeft then 1 else -1) else 0) -
    (if pr f i = some i' then 1 else 0)

lemma VV_mul (S : Matrix (Fin k) (Fin k) ℤ) (i c : Fin k) :
    (VV f * S) i c = (if (f i).isLeft then 1 else -1) * S i c -
      (match pr f i with | some i' => S i' c | none => 0) := by
  simp only [mul_apply, VV, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, one_mul]
  congr 1
  · rw [Finset.sum_ite_eq']; simp
  · cases h : pr f i with
    | none => simp
    | some i' => simp [Option.some.injEq]


lemma pr_some_of_exists {i : Fin k} (h : ∃ i', IsPred f i' i) : ∃ i', pr f i = some i' := by
  unfold pr; rw [dif_pos h]; exact ⟨_, rfl⟩

lemma pred_val {i i' : Fin k} {j : Fin n} {t : Fin L} (hi : f i = Sum.inl (j, t))
    (h : pr f i = some i') : ∃ t', f i' = Sum.inl (j, t') ∧ t' < t ∧
      ∀ (i'' : Fin k) (t'' : Fin L), f i'' = Sum.inl (j, t'') → t'' < t → t'' ≤ t' := by
  obtain ⟨j', t1, t', e1, e2, hlt, hmax⟩ := pr_spec h
  rw [hi] at e1
  simp only [Sum.inl.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  exact ⟨t', e2, hlt, hmax⟩

lemma pr_inr {i : Fin k} {t : Fin L} (hi : f i = Sum.inr t) : pr f i = none := by
  cases h : pr f i with
  | none => rfl
  | some i' =>
    obtain ⟨j, t1, t', e1, _, _, _⟩ := pr_spec h
    rw [hi] at e1; cases e1

lemma pr_ne_self (i : Fin k) : pr f i ≠ some i := by
  intro h
  have := (pr_spec h).tm_lt
  exact lt_irrefl _ this

lemma det_VV : (VV f).det = 1 ∨ (VV f).det = -1 := by
  classical
  have hbt : (VV f).BlockTriangular (fun i => OrderDual.toDual (tm (f i))) := by
    intro i i' hlt
    change tm (f i) < tm (f i') at hlt
    have hne : i' ≠ i := by rintro rfl; exact lt_irrefl _ hlt
    have hpr : pr f i ≠ some i' := by
      intro h; have := (pr_spec h).tm_lt; omega
    simp [VV, hne, hpr]
  rw [hbt.det]
  apply Finset.prod_induction _ (fun z => z = 1 ∨ z = -1)
  · intro a b ha hb; rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  · simp
  · intro a _
    have hdiag : (VV f).toSquareBlock (fun i => OrderDual.toDual (tm (f i))) a =
        Matrix.diagonal (fun x => VV f x.1 x.1) := by
      ext x y
      by_cases hxy : x = y
      · subst hxy; rw [toSquareBlock_def, of_apply, diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hxy, toSquareBlock_def, of_apply]
        have hne : (y : Fin k) ≠ x := fun h => hxy (Subtype.ext h.symm)
        have hpr : pr f x.1 ≠ some y.1 := by
          intro h
          have h1 := (pr_spec h).tm_lt
          have h2 : tm (f x) = tm (f y) := by
            have := x.2.trans y.2.symm
            exact OrderDual.toDual.injective this
          omega
        simp [VV, hne, hpr]
    rw [hdiag, det_diagonal]
    apply Finset.prod_induction _ (fun z => z = 1 ∨ z = -1)
    · intro a b ha hb; rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
    · simp
    · intro x _
      simp only [VV, if_true, pr_ne_self, if_false, sub_zero]
      split_ifs <;> simp


lemma X_cases (g : Fin k → Fin n × Fin L) (i c : Fin k) :
    (∃ j t, f i = Sum.inl (j, t) ∧
      ((VV f * (NN n L).submatrix f g) i c = 0 ∨
        ((VV f * (NN n L).submatrix f g) i c = 1 ∧ (g c).1 = j ∧ (g c).2 ≤ t ∧
          ∀ i' t', pr f i = some i' → f i' = Sum.inl (j, t') → ¬ (g c).2 ≤ t'))) ∨
    (∃ t, f i = Sum.inr t ∧
      ((VV f * (NN n L).submatrix f g) i c = 0 ∨
        ((VV f * (NN n L).submatrix f g) i c = -1 ∧ (g c).2 = t))) := by
  rw [VV_mul]
  rcases hfi : f i with ⟨j, t⟩ | t
  · left
    refine ⟨j, t, rfl, ?_⟩
    simp only [Sum.isLeft_inl, if_true, one_mul, submatrix_apply, hfi, NN]
    cases hp : pr f i with
    | none =>
      simp only [sub_zero]
      split_ifs with h
      · right; refine ⟨rfl, h.1, h.2, ?_⟩
        intro i' t' h'; simp at h'
      · left; rfl
    | some i' =>
      obtain ⟨t', e', hlt, _⟩ := pred_val hfi hp
      simp only [submatrix_apply, e', NN]
      by_cases h1 : (g c).1 = j ∧ (g c).2 ≤ t
      · by_cases h2 : (g c).1 = j ∧ (g c).2 ≤ t'
        · left; rw [if_pos h1, if_pos h2]; ring
        · right
          rw [if_pos h1, if_neg h2]
          refine ⟨by ring, h1.1, h1.2, ?_⟩
          intro i'' t'' h'' e''
          simp only [Option.some.injEq] at h''
          subst h''
          rw [e'] at e''
          simp only [Sum.inl.injEq, Prod.mk.injEq] at e''
          rw [← e''.2]
          exact fun h => h2 ⟨h1.1, h⟩
      · have h2 : ¬ ((g c).1 = j ∧ (g c).2 ≤ t') := by
          intro h; exact h1 ⟨h.1, le_trans h.2 hlt.le⟩
        left; rw [if_neg h1, if_neg h2]; ring
  · right
    refine ⟨t, rfl, ?_⟩
    rw [pr_inr hfi]
    simp only [Sum.isLeft_inr, Bool.false_eq_true, if_false, submatrix_apply, hfi, NN, sub_zero]
    split_ifs with h
    · right; exact ⟨by ring, h⟩
    · left; ring

lemma det_NN_inj (hf : Function.Injective f) (g : Fin k → Fin n × Fin L) :
    ((NN n L).submatrix f g).det ∈ Set.range (SignType.cast : SignType → ℤ) := by
  have hX : (VV f * (NN n L).submatrix f g).det ∈ Set.range (SignType.cast : SignType → ℤ) := by
    apply inc_det
    · intro i c
      rcases X_cases (f := f) g i c with ⟨j, t, _, h | h⟩ | ⟨t, _, h | h⟩
      · right; left; exact h
      · right; right; exact h.1
      · right; left; exact h
      · left; exact h.1
    · intro c i1 i2 h1 h2
      rcases X_cases (f := f) g i1 c with ⟨j1, t1, e1, h1' | h1'⟩ | ⟨t1, e1, h1' | h1'⟩
      · rw [h1'] at h1; norm_num at h1
      · rcases X_cases (f := f) g i2 c with ⟨j2, t2, e2, h2' | h2'⟩ | ⟨t2, e2, h2' | h2'⟩
        · rw [h2'] at h2; norm_num at h2
        · have hj : j1 = j2 := h1'.2.1.symm.trans h2'.2.1
          subst hj
          rcases lt_trichotomy t1 t2 with hlt | heq | hgt
          · exfalso
            obtain ⟨i', hi'⟩ := pr_some_of_exists (pr_exists e2 i1 t1 e1 hlt)
            obtain ⟨t', e', _, hmax⟩ := pred_val e2 hi'
            exact h2'.2.2.2 i' t' hi' e' (le_trans h1'.2.2.1 (hmax i1 t1 e1 hlt))
          · subst heq; exact hf (e1.trans e2.symm)
          · exfalso
            obtain ⟨i', hi'⟩ := pr_some_of_exists (pr_exists e1 i2 t2 e2 hgt)
            obtain ⟨t', e', _, hmax⟩ := pred_val e1 hi'
            exact h1'.2.2.2 i' t' hi' e' (le_trans h2'.2.2.1 (hmax i2 t2 e2 hgt))
        · rw [h2'] at h2; norm_num at h2
        · rw [h2'.1] at h2; norm_num at h2
      · rw [h1'] at h1; norm_num at h1
      · rw [h1'.1] at h1; norm_num at h1
    · intro c i1 i2 h1 h2
      rcases X_cases (f := f) g i1 c with ⟨j1, t1, e1, h1' | h1'⟩ | ⟨t1, e1, h1' | h1'⟩
      · rw [h1'] at h1; norm_num at h1
      · rw [h1'.1] at h1; norm_num at h1
      · rw [h1'] at h1; norm_num at h1
      · rcases X_cases (f := f) g i2 c with ⟨j2, t2, e2, h2' | h2'⟩ | ⟨t2, e2, h2' | h2'⟩
        · rw [h2'] at h2; norm_num at h2
        · rw [h2'.1] at h2; norm_num at h2
        · rw [h2'] at h2; norm_num at h2
        · have : t1 = t2 := h1'.2.symm.trans h2'.2
          subst this
          exact hf (e1.trans e2.symm)
  have hdet : (VV f * (NN n L).submatrix f g).det = (VV f).det * ((NN n L).submatrix f g).det := by
    rw [det_mul]
  have hV := det_VV (f := f)
  have : ((NN n L).submatrix f g).det = (VV f).det * (VV f * (NN n L).submatrix f g).det := by
    rw [hdet, ← mul_assoc]
    rcases hV with h | h <;> rw [h] <;> ring
  rw [this]
  apply range_mul _ hX
  rcases hV with h | h <;> rw [h]
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩

end Rows

lemma det_NN {k : ℕ} (f : Fin k → (Fin n × Fin L) ⊕ Fin L) (g : Fin k → Fin n × Fin L) :
    ((NN n L).submatrix f g).det ∈ Set.range (SignType.cast : SignType → ℤ) := by
  by_cases hf : Function.Injective f
  · exact det_NN_inj hf g
  · unfold Function.Injective at hf
    push Not at hf
    obtain ⟨a, b, hab, hne⟩ := hf
    rw [det_zero_of_row_eq hne (by funext c; simp [hab])]
    exact ⟨0, by simp⟩

def beta : (Fin n × Fin L) ⊕ (Fin n × Fin L) ⊕ Fin L ⊕ Fin L → (Fin n × Fin L) ⊕ Fin L
  | Sum.inl it => Sum.inl it
  | Sum.inr (Sum.inl it) => Sum.inl it
  | Sum.inr (Sum.inr (Sum.inl t)) => Sum.inr t
  | Sum.inr (Sum.inr (Sum.inr t)) => Sum.inr t

def sgn : (Fin n × Fin L) ⊕ (Fin n × Fin L) ⊕ Fin L ⊕ Fin L → ℤ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => -1
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr _)) => -1

lemma cm_eq (r : (Fin n × Fin L) ⊕ (Fin n × Fin L) ⊕ Fin L ⊕ Fin L) (c : Fin n × Fin L) :
    constraintMatrix n L r c = sgn r * NN n L (beta r) c := by
  rcases r with it | it | t | t
  · simp [constraintMatrix, sgn, beta, NN]
  · simp only [constraintMatrix, sgn, beta, NN]; split_ifs <;> simp
  · simp [constraintMatrix, sgn, beta, NN]
  · simp only [constraintMatrix, sgn, beta, NN]; split_ifs <;> simp

theorem tu : (constraintMatrix n L).IsTotallyUnimodular := by
  intro k f g _ _
  have hM : (constraintMatrix n L).submatrix f g =
      Matrix.diagonal (fun i => sgn (f i)) * (NN n L).submatrix (beta ∘ f) g := by
    ext i c
    rw [diagonal_mul, submatrix_apply, submatrix_apply, cm_eq]
    rfl
  rw [hM, det_mul, det_diagonal]
  apply range_mul _ (det_NN _ g)
  apply Finset.prod_induction _ (fun z => z ∈ Set.range (SignType.cast : SignType → ℤ))
  · intro a b ha hb; exact range_mul ha hb
  · exact ⟨1, by simp⟩
  · intro i _
    rcases f i with it | it | t | t
    · exact ⟨1, by simp [sgn]⟩
    · exact ⟨-1, by simp [sgn]⟩
    · exact ⟨1, by simp [sgn]⟩
    · exact ⟨-1, by simp [sgn]⟩

end MonoTU

theorem solution (n L : ℕ) : (constraintMatrix n L).IsTotallyUnimodular := MonoTU.tu
