-- Prove2me | solution 1 for LSWNewArcAudit.NewArc.lemma79_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T12:52:05.725403+00:00
-- url     : https://prove2.me/submissions/e37a92cb-ee75-4d09-b48a-75c34bc032af

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_RepresentedInput

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LSW79F

open Finset LSWCuttingPlane.SFMArcs

/-! ## Part 1: mathematics of the selection rule (no machine). -/

/-- Marginal of `j` over `B ∪ before σ j`: the BFS of `σ` frontloaded behind the base set `B`. -/
def marg {n : ℕ} (f : Finset (Fin n) → ℤ) (B : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (j : Fin n) : ℤ :=
  f (insert j (B ∪ before σ j)) - f (B ∪ before σ j)

theorem marg_empty {n : ℕ} (f : Finset (Fin n) → ℤ) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    bfs f σ j = (marg f ∅ σ j : ℝ) := by
  simp [bfs, marg]

theorem marg_mem {n : ℕ} (f : Finset (Fin n) → ℤ) (B : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (j : Fin n) (hj : j ∈ B) : marg f B σ j = 0 := by
  unfold marg
  rw [Finset.insert_eq_of_mem (Finset.mem_union_left _ hj)]
  simp

/-- Greedy bound: the frontloaded marginals over any `T` disjoint from `B` sum to at most
`f (B ∪ T) - f B`. -/
theorem GB {n : ℕ} (f : Finset (Fin n) → ℤ) (hf : Submodular f) (B : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n)) :
    Disjoint T B → ∑ j ∈ T, marg f B σ j ≤ f (B ∪ T) - f B := by
  classical
  refine Finset.induction_on_max_value (fun j => σ j) T ?_ ?_
  · intro _; simp
  · intro a s ha hmax ih hdis
    have hdis' : Disjoint s B := Finset.disjoint_of_subset_left (Finset.subset_insert a s) hdis
    have haB : a ∉ B := fun h => Finset.disjoint_left.mp hdis (Finset.mem_insert_self a s) h
    have hsub : B ∪ s ⊆ B ∪ before σ a := by
      apply Finset.union_subset_union (le_refl B)
      intro x hx
      simp only [before, Finset.mem_filter, Finset.mem_univ, true_and]
      refine lt_of_le_of_ne (hmax x hx) ?_
      intro h
      exact ha (σ.injective h ▸ hx)
    have hnot : a ∉ B ∪ before σ a := by
      simp [before, haB]
    have h1 := hf (B ∪ s) (B ∪ before σ a) a hsub hnot
    rw [Finset.sum_insert ha]
    have e : B ∪ insert a s = insert a (B ∪ s) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [e]
    have := ih hdis'
    have hm : marg f B σ a = f (insert a (B ∪ before σ a)) - f (B ∪ before σ a) := rfl
    linarith

/-- Telescoping: over the complement of `B` the frontloaded marginals sum to `f univ - f B`. -/
theorem TEL {n : ℕ} (f : Finset (Fin n) → ℤ) (B : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    ∑ j ∈ Bᶜ, marg f B σ j = f Finset.univ - f B := by
  classical
  have key : ∀ t : ℕ, t ≤ n →
      ∑ j ∈ Bᶜ.filter (fun j => (σ j).val < t), marg f B σ j
        = f (B ∪ Finset.univ.filter (fun j => (σ j).val < t)) - f B := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      set a : Fin n := σ.symm ⟨t, by omega⟩ with ha
      have hσa : σ a = ⟨t, by omega⟩ := by simp [ha]
      have hfil : ∀ C : Finset (Fin n), C.filter (fun j => (σ j).val < t + 1)
          = (if a ∈ C then insert a (C.filter (fun j => (σ j).val < t))
              else C.filter (fun j => (σ j).val < t)) := by
        intro C
        ext x
        have hx : x = a ↔ (σ x).val = t := by
          constructor
          · intro h; rw [h, hσa]
          · intro h
            have : σ x = σ a := by rw [hσa]; exact Fin.ext h
            exact σ.injective this
        split_ifs with haC
        · simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hxC, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
            · exact Or.inr ⟨hxC, h⟩
            · exact Or.inl (hx.mpr h)
          · rintro (h | ⟨hxC, h⟩)
            · subst h; exact ⟨haC, by rw [hσa]; simp⟩
            · exact ⟨hxC, by omega⟩
        · simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hxC, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
            · exact ⟨hxC, h⟩
            · exact absurd (hx.mpr h ▸ hxC) haC
          · rintro ⟨hxC, h⟩; exact ⟨hxC, by omega⟩
      have hbef : before σ a = Finset.univ.filter (fun j => (σ j).val < t) := by
        ext x; simp [before, hσa, Fin.lt_def]
      have hU := hfil Finset.univ
      simp only [Finset.mem_univ, if_true] at hU
      have ih' := ih (by omega)
      by_cases haB : a ∈ B
      · have hC := hfil Bᶜ
        have : a ∉ Bᶜ := by simpa using haB
        rw [if_neg this] at hC
        rw [hC, ih', hU, Finset.union_insert,
          Finset.insert_eq_of_mem (Finset.mem_union_left _ haB)]
      · have hC := hfil Bᶜ
        have : a ∈ Bᶜ := by simpa using haB
        rw [if_pos this] at hC
        have hnot : a ∉ Bᶜ.filter (fun j => (σ j).val < t) := by
          simp [hσa]
        rw [hC, Finset.sum_insert hnot, ih', hU]
        unfold marg
        rw [hbef]
        rw [Finset.union_insert]
        ring
  have h := key n le_rfl
  have e1 : Bᶜ.filter (fun j => (σ j).val < n) = Bᶜ := by
    ext x; simp
  have e2 : Finset.univ.filter (fun j : Fin n => (σ j).val < n) = Finset.univ := by
    ext x; simp
  rw [e1, e2, Finset.union_eq_right.mpr (Finset.subset_univ B)] at h
  exact h

/-- Diminishing returns: frontloading `R` lowers the marginal of any `j ∉ R`. -/
theorem marg_le {n : ℕ} (f : Finset (Fin n) → ℤ) (hf : Submodular f) (R : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (j : Fin n) (hj : j ∉ R) : marg f R σ j ≤ marg f ∅ σ j := by
  have hnot : j ∉ R ∪ before σ j := by simp [before, hj]
  have := hf (before σ j) (R ∪ before σ j) j Finset.subset_union_right hnot
  unfold marg
  simpa using this

/-- For `S ⊇ B`, the frontloaded marginals over `Sᶜ` sum to at least `f univ - f S`. -/
theorem compl_ge {n : ℕ} (f : Finset (Fin n) → ℤ) (hf : Submodular f) (B : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (hBS : B ⊆ S) :
    f Finset.univ - f S ≤ ∑ j ∈ Sᶜ, marg f B σ j := by
  classical
  have ht := TEL f B σ
  have hg := GB f hf B σ (S \ B) Finset.sdiff_disjoint
  have e1 : B ∪ (S \ B) = S := Finset.union_sdiff_of_subset hBS
  rw [e1] at hg
  have hsplit : Bᶜ = (S \ B) ∪ Sᶜ := by
    ext x; simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro h; by_cases hs : x ∈ S
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr hs
    · rintro (⟨_, h⟩ | h)
      · exact h
      · exact fun hb => h (hBS hb)
  have hdisj : Disjoint (S \ B) Sᶜ := by
    rw [Finset.disjoint_left]; intro x hx hx'
    simp only [Finset.mem_sdiff] at hx; simp only [Finset.mem_compl] at hx'; exact hx' hx.1
  rw [hsplit, Finset.sum_union hdisj] at ht
  linarith

theorem LSW79Aux_R_sub {n : ℕ} (A : Fin n → Fin n → Prop) (p : Fin n) (S : Finset (Fin n))
    (hS : S ∈ ringFamily A) (hp : p ∈ S) : R A p ⊆ S := by
  intro j hj
  classical
  have hj' : Relation.ReflTransGen A p j := by
    simpa [R] using hj
  induction hj' with
  | refl => exact hp
  | tail _ hbc ih => exact hS _ _ hbc (ih (by simp [R]; assumption))

theorem LSW79Aux_mem_R {n : ℕ} (A : Fin n → Fin n → Prop) (p j : Fin n) :
    j ∈ R A p ↔ Relation.ReflTransGen A p j := by
  classical
  simp [R]

/-- The frontloaded gap of one BFS: `∑_{Rᶜ} (y - x) ≥ upper - y_p`. -/
theorem gap_one {n : ℕ} (f : Finset (Fin n) → ℤ) (hf : Submodular f) (R : Finset (Fin n))
    (p : Fin n) (hp : p ∈ R) (σ : Equiv.Perm (Fin n)) :
    (f R - f (R.erase p)) - marg f ∅ σ p ≤ ∑ j ∈ Rᶜ, (marg f ∅ σ j - marg f R σ j) := by
  classical
  have t0 := TEL f ∅ σ
  have t1 := TEL f R σ
  have g0 := GB f hf ∅ σ (R.erase p) (Finset.disjoint_empty_right _)
  rw [Finset.compl_empty] at t0
  rw [Finset.empty_union] at g0
  have hs := Finset.sum_add_sum_compl R (fun j => marg f ∅ σ j)
  have he := Finset.add_sum_erase R (fun j => marg f ∅ σ j) hp
  rw [Finset.sum_sub_distrib]
  linarith

section crit
variable {n m : ℕ}

/-- The vector the machine computes: frontloaded behind `R` on `K`, plain BFS elsewhere. -/
noncomputable def Wv (f : Finset (Fin n) → ℤ) (R : Finset (Fin n)) (lam : Fin m → ℝ)
    (σs : Fin m → Equiv.Perm (Fin n)) (K : Finset (Fin m)) (j : Fin n) : ℝ :=
  ∑ k, lam k * (if k ∈ K then (marg f R (σs k) j : ℝ) else bfs f (σs k) j)

theorem Wv_eq (f : Finset (Fin n) → ℤ) (R : Finset (Fin n)) (lam : Fin m → ℝ)
    (σs : Fin m → Equiv.Perm (Fin n)) (K : Finset (Fin m)) (j : Fin n) :
    Wv f R lam σs K j = (∑ k, lam k * bfs f (σs k) j)
      + ∑ k ∈ K, lam k * ((marg f R (σs k) j : ℝ) - bfs f (σs k) j) := by
  classical
  have h : ∀ k, lam k * (if k ∈ K then (marg f R (σs k) j : ℝ) else bfs f (σs k) j)
      = lam k * bfs f (σs k) j
        + (if k ∈ K then lam k * ((marg f R (σs k) j : ℝ) - bfs f (σs k) j) else 0) := by
    intro k; split_ifs <;> ring
  unfold Wv
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.univ_inter]

/-- Selection criterion: a minimiser of `Wv` outside `R(p)` lies in every minimiser through `p`,
once the frontloading gain exceeds `(n-1) n ymax`. -/
theorem crit [NeZero n] (f : Finset (Fin n) → ℤ) (hf : Submodular f)
    (A : Fin n → Fin n → Prop) (p : Fin n)
    (lam : Fin m → ℝ) (σs : Fin m → Equiv.Perm (Fin n)) (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∑ k, lam k = 1) (K : Finset (Fin m))
    (hy : 0 < ymax (fun j => ∑ k, lam k * bfs f (σs k) j))
    (hG : ((n : ℝ) - 1) * n * ymax (fun j => ∑ k, lam k * bfs f (σs k) j)
      < ∑ k ∈ K, lam k * ((upper f A p : ℝ) - bfs f (σs k) p))
    (q : Fin n) (hq : q ∉ R A p)
    (hmin : ∀ j ∉ R A p, Wv f (R A p) lam σs K q ≤ Wv f (R A p) lam σs K j) :
    ∀ S, IsMinimizer A f S → p ∈ S → q ∈ S := by
  classical
  set Rp := R A p with hRp
  set Y : Fin n → ℝ := fun j => ∑ k, lam k * bfs f (σs k) j with hY
  set M := ymax Y with hM
  set W := Wv f Rp lam σs K with hW
  set G := ∑ k ∈ K, lam k * ((upper f A p : ℝ) - bfs f (σs k) p) with hGdef
  have hpR : p ∈ Rp := by
    rw [hRp]; exact (LSW79Aux_mem_R A p p).mpr Relation.ReflTransGen.refl
  have hYM : ∀ j, Y j ≤ M := fun j => Finset.le_sup' Y (Finset.mem_univ j)
  have hWY : ∀ j ∉ Rp, W j ≤ Y j := by
    intro j hj
    rw [hW, Wv_eq]
    have : ∑ k ∈ K, lam k * ((marg f Rp (σs k) j : ℝ) - bfs f (σs k) j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro k _
      have h1 := marg_le f hf Rp (σs k) j hj
      have h2 : ((marg f Rp (σs k) j : ℤ) : ℝ) ≤ bfs f (σs k) j := by
        rw [marg_empty]; exact_mod_cast h1
      exact mul_nonpos_of_nonneg_of_nonpos (hlam0 k) (by linarith)
    simp only [hY]; linarith
  -- the total gain
  have hsum : G ≤ ∑ j ∈ Rpᶜ, (Y j - W j) := by
    have e : ∀ j, Y j - W j
        = ∑ k ∈ K, lam k * (bfs f (σs k) j - (marg f Rp (σs k) j : ℝ)) := by
      intro j
      rw [hW, Wv_eq]
      simp only [hY]
      rw [sub_add_cancel_left, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_comm]
    apply Finset.sum_le_sum
    intro k _
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hlam0 k)
    have g := gap_one f hf Rp p hpR (σs k)
    have g' : ((f Rp - f (Rp.erase p) - marg f ∅ (σs k) p : ℤ) : ℝ)
        ≤ ((∑ j ∈ Rpᶜ, (marg f ∅ (σs k) j - marg f Rp (σs k) j) : ℤ) : ℝ) := by
      exact_mod_cast g
    push_cast at g'
    have hu : (upper f A p : ℝ) = ((f Rp : ℤ) : ℝ) - ((f (Rp.erase p) : ℤ) : ℝ) := by
      simp [upper, hRp]
    rw [hu, marg_empty]
    have : ∀ j, bfs f (σs k) j = ((marg f ∅ (σs k) j : ℤ) : ℝ) := fun j => marg_empty f _ j
    simp only [this]
    linarith
  -- the minimum value is far below zero
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hd : (Rpᶜ.card : ℝ) ≤ (n : ℝ) - 1 := by
    have : Rpᶜ.card + 1 ≤ n := by
      have h1 : Rpᶜ.card = n - Rp.card := by rw [Finset.card_compl, Fintype.card_fin]
      have h2 : 1 ≤ Rp.card := Finset.card_pos.mpr ⟨p, hpR⟩
      have h3 : Rp.card ≤ n := by
        simpa using Finset.card_le_univ Rp
      omega
    have : ((Rpᶜ.card + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at this; linarith
  have hWq : W q + ((n : ℝ) - 1) * M < 0 := by
    have hlow : (Rpᶜ.card : ℝ) * W q ≤ ∑ j ∈ Rpᶜ, W j := by
      have := Finset.card_nsmul_le_sum Rpᶜ W (W q) (fun j hj => hmin j (by simpa using hj))
      simpa [nsmul_eq_mul] using this
    have hup : ∑ j ∈ Rpᶜ, Y j ≤ (Rpᶜ.card : ℝ) * M := by
      have := Finset.sum_le_card_nsmul Rpᶜ Y M (fun j _ => hYM j)
      simpa [nsmul_eq_mul] using this
    rw [Finset.sum_sub_distrib] at hsum
    have hc0 : (0 : ℝ) ≤ Rpᶜ.card := by positivity
    have hnM : 0 ≤ (n : ℝ) * M := by positivity
    have key : (Rpᶜ.card : ℝ) * (W q + ((n : ℝ) - 1) * M) < 0 := by
      have h1 : (Rpᶜ.card : ℝ) * ((n : ℝ) * M) ≤ ((n : ℝ) - 1) * ((n : ℝ) * M) :=
        mul_le_mul_of_nonneg_right hd hnM
      nlinarith
    by_contra hcon
    push Not at hcon
    have := mul_nonneg hc0 hcon
    linarith
  -- the criterion
  intro S hS hpS
  by_contra hqS
  have hRS : Rp ⊆ S := LSW79Aux_R_sub A p S hS.1 hpS
  have hUR : ∀ j ∈ Sᶜ, j ∉ Rp := by
    intro j hj hjR; exact (Finset.mem_compl.mp hj) (hRS hjR)
  have hqU : q ∈ Sᶜ := Finset.mem_compl.mpr hqS
  -- lower bound
  have hlow : ((f Finset.univ : ℤ) : ℝ) - ((f S : ℤ) : ℝ) ≤ ∑ j ∈ Sᶜ, W j := by
    have e : ∑ j ∈ Sᶜ, W j = ∑ k, lam k * ∑ j ∈ Sᶜ,
        (if k ∈ K then (marg f Rp (σs k) j : ℝ) else bfs f (σs k) j) := by
      rw [hW]; unfold Wv
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
    rw [e]
    have hk : ∀ k, ((f Finset.univ : ℤ) : ℝ) - ((f S : ℤ) : ℝ) ≤ ∑ j ∈ Sᶜ,
        (if k ∈ K then (marg f Rp (σs k) j : ℝ) else bfs f (σs k) j) := by
      intro k
      by_cases hkK : k ∈ K
      · simp only [hkK, if_true]
        have := compl_ge f hf Rp (σs k) S hRS
        exact_mod_cast this
      · simp only [hkK, if_false]
        have := compl_ge f hf ∅ (σs k) S (Finset.empty_subset S)
        simp only [marg_empty]
        exact_mod_cast this
    calc ((f Finset.univ : ℤ) : ℝ) - ((f S : ℤ) : ℝ)
        = ∑ k, lam k * (((f Finset.univ : ℤ) : ℝ) - ((f S : ℤ) : ℝ)) := by
          rw [← Finset.sum_mul, hlam1, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hk k) (hlam0 k))
  -- upper bound
  have hupp : ∑ j ∈ Sᶜ, W j ≤ W q + ((n : ℝ) - 1) * M := by
    rw [← Finset.add_sum_erase _ _ hqU]
    have h1 : ∑ j ∈ Sᶜ.erase q, W j ≤ ((Sᶜ.erase q).card : ℝ) * M := by
      have := Finset.sum_le_card_nsmul (Sᶜ.erase q) W M
        (fun j hj => (hWY j (hUR j (Finset.mem_of_mem_erase hj))).trans (hYM j))
      simpa [nsmul_eq_mul] using this
    have h2 : ((Sᶜ.erase q).card : ℝ) ≤ (n : ℝ) - 1 := by
      have a1 := Finset.card_erase_of_mem hqU
      have a2 : Sᶜ.card ≤ n := by simpa using Finset.card_le_univ Sᶜ
      have a3 : 1 ≤ Sᶜ.card := Finset.card_pos.mpr ⟨q, hqU⟩
      have : (Sᶜ.erase q).card + 1 ≤ n := by omega
      have : (((Sᶜ.erase q).card + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast at this; linarith
    have h3 : ((Sᶜ.erase q).card : ℝ) * M ≤ ((n : ℝ) - 1) * M :=
      mul_le_mul_of_nonneg_right h2 hy.le
    linarith
  have hV : f S ≤ f Finset.univ := hS.2 Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
  have : ((f S : ℤ) : ℝ) ≤ ((f Finset.univ : ℤ) : ℝ) := by exact_mod_cast hV
  linarith

/-- Total frontloading gain `∑_k λ_k (upper - y^k_p) = upper - y_p`. -/
theorem gain_total {n m : ℕ} (f : Finset (Fin n) → ℤ) (lam : Fin m → ℝ)
    (σs : Fin m → Equiv.Perm (Fin n)) (hlam1 : ∑ k, lam k = 1) (u : ℝ) (p : Fin n) :
    ∑ k, lam k * (u - bfs f (σs k) p) = u - ∑ k, lam k * bfs f (σs k) p := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hlam1, one_mul]

/-- Small case (`K = univ`): the gain is large enough. -/
theorem G_all {n m : ℕ} [NeZero n] (f : Finset (Fin n) → ℤ) (lam : Fin m → ℝ)
    (σs : Fin m → Equiv.Perm (Fin n)) (hlam1 : ∑ k, lam k = 1) (u : ℝ) (p : Fin n)
    (hy : 0 < ymax (fun j => ∑ k, lam k * bfs f (σs k) j))
    (hu : (n : ℝ) ^ 4 * ymax (fun j => ∑ k, lam k * bfs f (σs k) j) < u) :
    ((n : ℝ) - 1) * n * ymax (fun j => ∑ k, lam k * bfs f (σs k) j)
      < ∑ k ∈ Finset.univ, lam k * (u - bfs f (σs k) p) := by
  set M := ymax (fun j => ∑ k, lam k * bfs f (σs k) j) with hM
  have hYp : (∑ k, lam k * bfs f (σs k) p) ≤ M :=
    Finset.le_sup' (fun j => ∑ k, lam k * bfs f (σs k) j) (Finset.mem_univ p)
  rw [gain_total f lam σs hlam1 u p]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hpoly : ((n : ℝ) - 1) * n ≤ (n : ℝ) ^ 4 - 1 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    have : (n : ℝ) ^ 4 - 1 - ((n : ℝ) - 1) * n = ((n : ℝ) - 1) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 2 + 1) := by
      ring
    have h2 : 0 ≤ ((n : ℝ) - 1) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 2 + 1) := by positivity
    linarith
  have := mul_le_mul_of_nonneg_right hpoly hy.le
  nlinarith

/-- Large case (`K = {k}` with `k` maximising the gain, `m ≤ c n`, `c < n`). -/
theorem G_one {n m : ℕ} [NeZero n] (f : Finset (Fin n) → ℤ) (lam : Fin m → ℝ)
    (σs : Fin m → Equiv.Perm (Fin n)) (hlam1 : ∑ k, lam k = 1) (u : ℝ) (p : Fin n)
    (hy : 0 < ymax (fun j => ∑ k, lam k * bfs f (σs k) j))
    (hu : (n : ℝ) ^ 4 * ymax (fun j => ∑ k, lam k * bfs f (σs k) j) < u)
    (c : ℕ) (hm : m ≤ c * n) (hc : c + 1 ≤ n) (k : Fin m)
    (hk : ∀ l, lam l * (u - bfs f (σs l) p) ≤ lam k * (u - bfs f (σs k) p)) :
    ((n : ℝ) - 1) * n * ymax (fun j => ∑ k, lam k * bfs f (σs k) j)
      < ∑ l ∈ ({k} : Finset (Fin m)), lam l * (u - bfs f (σs l) p) := by
  set M := ymax (fun j => ∑ k, lam k * bfs f (σs k) j) with hM
  rw [Finset.sum_singleton]
  set g := lam k * (u - bfs f (σs k) p) with hg
  have hYp : (∑ k, lam k * bfs f (σs k) p) ≤ M :=
    Finset.le_sup' (fun j => ∑ k, lam k * bfs f (σs k) j) (Finset.mem_univ p)
  have hsum := gain_total f lam σs hlam1 u p
  have hle : ∑ l, lam l * (u - bfs f (σs l) p) ≤ (m : ℝ) * g := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun l => lam l * (u - bfs f (σs l) p)) g
      (fun l _ => hk l)
    simpa [nsmul_eq_mul] using this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hmr : (m : ℝ) ≤ ((n : ℝ) - 1) * n := by
    have h1 : (m : ℝ) ≤ (c : ℝ) * n := by exact_mod_cast hm
    have h2 : (c : ℝ) ≤ (n : ℝ) - 1 := by
      have : ((c + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hc
      push_cast at this; linarith
    have h3 : (c : ℝ) * n ≤ ((n : ℝ) - 1) * n := mul_le_mul_of_nonneg_right h2 (by linarith)
    linarith
  have hpoly : (((n : ℝ) - 1) * n) * (((n : ℝ) - 1) * n) ≤ (n : ℝ) ^ 4 - 1 := by
    have : (n : ℝ) ^ 4 - 1 - (((n : ℝ) - 1) * n) * (((n : ℝ) - 1) * n)
        = ((n : ℝ) - 1) * (2 * (n : ℝ) ^ 2 + n + 1) := by ring
    have h0 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    have h2 : 0 ≤ ((n : ℝ) - 1) * (2 * (n : ℝ) ^ 2 + n + 1) := by positivity
    linarith
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := Fin.pos k
    exact_mod_cast this
  have hA : (m : ℝ) * (((n : ℝ) - 1) * n * M) ≤ ((n : ℝ) ^ 4 - 1) * M := by
    have h1 : (m : ℝ) * (((n : ℝ) - 1) * n) ≤ (((n : ℝ) - 1) * n) * (((n : ℝ) - 1) * n) :=
      mul_le_mul_of_nonneg_right hmr (by nlinarith)
    have h2 := mul_le_mul_of_nonneg_right (h1.trans hpoly) hy.le
    nlinarith
  have hB : ((n : ℝ) ^ 4 - 1) * M < (m : ℝ) * g := by
    rw [hsum] at hle; nlinarith
  by_contra hcon
  push Not at hcon
  have := mul_le_mul_of_nonneg_left hcon hm0.le
  linarith

end crit

end LSW79F

namespace LSW79M

open LSWNewArcAudit.NewArc SmaleNinth LSWCuttingPlane.SFMArcs

variable {n : ℕ} (prog : OracleProgram) (f : Finset (Fin n) → ℤ) (s : OracleState n)

theorem step_halted (ho : s.output.isSome) : oracleStep prog f s = s := by
  simp [oracleStep, ho]

theorem core_fetch (i : RAMInstr) (h : prog[s.core.pc]? = some (.core i)) :
    (coreProgram prog)[s.core.pc]? = some i := by
  simp [coreProgram, List.getElem?_map, h]

theorem step_core (i : RAMInstr) (h : prog[s.core.pc]? = some (.core i)) (ho : s.output = none) :
    oracleStep prog f s = (⟨RAMStep (coreProgram prog) s.core, s.integerMemory, s.bitmap, s.output, s.queries, s.work + 1⟩ : OracleState n) := by
  simp [oracleStep, ho, h]

theorem step_const (d : ℕ) (c : ℝ) (h : prog[s.core.pc]? = some (.core (.const d c)))
    (ho : s.output = none) :
    oracleStep prog f s = (⟨⟨s.core.pc + 1, Function.update s.core.regs d c, s.core.ptrs, s.core.mem⟩, s.integerMemory, s.bitmap, s.output, s.queries, s.work + 1⟩ : OracleState n) := by
  rw [step_core prog f s _ h ho]
  simp [RAMStep, core_fetch prog s _ h]

theorem step_jle (i t : ℕ) (h : prog[s.core.pc]? = some (.core (.jle i t)))
    (ho : s.output = none) :
    oracleStep prog f s = (⟨⟨if s.core.regs i ≤ 0 then t else s.core.pc + 1, s.core.regs, s.core.ptrs, s.core.mem⟩, s.integerMemory, s.bitmap, s.output, s.queries, s.work + 1⟩ : OracleState n) := by
  rw [step_core prog f s _ h ho]
  simp only [RAMStep, core_fetch prog s _ h]
  split_ifs <;> rfl

theorem step_pjle (a b t : ℕ) (h : prog[s.core.pc]? = some (.core (.pjle a b t)))
    (ho : s.output = none) :
    oracleStep prog f s = (⟨⟨if s.core.ptrs a ≤ s.core.ptrs b then t else s.core.pc + 1, s.core.regs, s.core.ptrs, s.core.mem⟩, s.integerMemory, s.bitmap, s.output, s.queries, s.work + 1⟩ : OracleState n) := by
  rw [step_core prog f s _ h ho]
  simp only [RAMStep, core_fetch prog s _ h]
  split_ifs <;> rfl

theorem step_pointerAdd (d a b : ℕ) (h : prog[s.core.pc]? = some (.pointerAdd d a b))
    (ho : s.output = none) :
    oracleStep prog f s = (⟨⟨s.core.pc + 1, s.core.regs, Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b), s.core.mem⟩, s.integerMemory, s.bitmap, s.output, s.queries, s.work + 1⟩ : OracleState n) := by
  simp [oracleStep, ho, h]

theorem step_integerLoad (d a : ℕ) (h : prog[s.core.pc]? = some (.integerLoad d a))
    (ho : s.output = none) :
    oracleStep prog f s = (⟨⟨s.core.pc + 1, s.core.regs, Function.update s.core.ptrs d (s.integerMemory (s.core.ptrs a)), s.core.mem⟩, s.integerMemory, s.bitmap, s.output, s.queries, s.work + 1⟩ : OracleState n) := by
  simp [oracleStep, ho, h]

theorem step_query (d b : ℕ) (h : prog[s.core.pc]? = some (.query d b))
    (ho : s.output = none) :
    oracleStep prog f s = (⟨⟨s.core.pc + 1, Function.update s.core.regs d (f (s.bitmap (s.core.ptrs b)) : ℝ), s.core.ptrs, s.core.mem⟩, s.integerMemory, s.bitmap, s.output, s.queries + 1, s.work + 1⟩ : OracleState n) := by
  simp [oracleStep, ho, h]

theorem step_halt (a : ℕ) (h : prog[s.core.pc]? = some (.halt a))
    (ho : s.output = none) :
    oracleStep prog f s = (⟨⟨s.core.pc + 1, s.core.regs, s.core.ptrs, s.core.mem⟩, s.integerMemory, s.bitmap, some (s.core.ptrs a), s.queries, s.work + 1⟩ : OracleState n) := by
  simp [oracleStep, ho, h]

theorem run_add (input : RAMInput) (a b : ℕ) :
    oracleRun prog f input (a + b) = (oracleStep prog f)^[b] (oracleRun prog f input a) := by
  unfold oracleRun
  rw [Nat.add_comm, Function.iterate_add_apply]

/-! ## Explicit-state stepping (relay 2). -/

/-- A running (not yet halted) state with explicit components. -/
def st (pc : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ) (bm : ℤ → Finset (Fin n))
    (q w : ℕ) : OracleState n :=
  ⟨⟨pc, r, p, M⟩, im, bm, none, q, w⟩

section G
variable (P : OracleProgram) (f : Finset (Fin n) → ℤ) (pc : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ)
  (M : ℤ → ℝ) (im : ℤ → ℤ) (bm : ℤ → Finset (Fin n)) (q w : ℕ)

theorem G_core (i : RAMInstr) (h : P[pc]? = some (.core i)) :
    oracleStep P f (st pc r p M im bm q w)
      = ⟨RAMStep (coreProgram P) ⟨pc, r, p, M⟩, im, bm, none, q, w + 1⟩ := by
  simp [st, oracleStep, h]

theorem cfetch (i : RAMInstr) (h : P[pc]? = some (.core i)) : (coreProgram P)[pc]? = some i := by
  simp [coreProgram, List.getElem?_map, h]

theorem G_const (d : ℕ) (v : ℝ) (h : P[pc]? = some (.core (.const d v))) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) (Function.update r d v) p M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp [st, RAMStep, cfetch P pc _ h]

theorem G_add (d a b : ℕ) (h : P[pc]? = some (.core (.add d a b))) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) (Function.update r d (r a + r b)) p M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp [st, RAMStep, cfetch P pc _ h]

theorem G_sub (d a b : ℕ) (h : P[pc]? = some (.core (.sub d a b))) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) (Function.update r d (r a - r b)) p M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp [st, RAMStep, cfetch P pc _ h]

theorem G_mul (d a b : ℕ) (h : P[pc]? = some (.core (.mul d a b))) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) (Function.update r d (r a * r b)) p M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp [st, RAMStep, cfetch P pc _ h]

theorem G_load (d a : ℕ) (h : P[pc]? = some (.core (.load d a))) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) (Function.update r d (M (p a))) p M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp [st, RAMStep, cfetch P pc _ h]

theorem G_store (a b : ℕ) (h : P[pc]? = some (.core (.store a b))) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r p (Function.update M (p a) (r b)) im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp [st, RAMStep, cfetch P pc _ h]

theorem G_pset (d : ℕ) (v : ℤ) (h : P[pc]? = some (.core (.pset d v))) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r (Function.update p d v) M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp [st, RAMStep, cfetch P pc _ h]

theorem G_pcopy (d a : ℕ) (h : P[pc]? = some (.core (.pcopy d a))) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r (Function.update p d (p a)) M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp [st, RAMStep, cfetch P pc _ h]

theorem G_pinc (d : ℕ) (h : P[pc]? = some (.core (.pinc d))) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r (Function.update p d (p d + 1)) M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp [st, RAMStep, cfetch P pc _ h]

theorem G_pdec (d : ℕ) (h : P[pc]? = some (.core (.pdec d))) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r (Function.update p d (p d - 1)) M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp [st, RAMStep, cfetch P pc _ h]

theorem G_jle (a t : ℕ) (h : P[pc]? = some (.core (.jle a t))) :
    oracleStep P f (st pc r p M im bm q w) = st (if r a ≤ 0 then t else pc + 1) r p M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp only [st, RAMStep, cfetch P pc _ h]; split_ifs <;> rfl

theorem G_pjle (a b t : ℕ) (h : P[pc]? = some (.core (.pjle a b t))) :
    oracleStep P f (st pc r p M im bm q w) = st (if p a ≤ p b then t else pc + 1) r p M im bm q (w + 1) := by
  rw [G_core P f pc r p M im bm q w _ h]; simp only [st, RAMStep, cfetch P pc _ h]; split_ifs <;> rfl

theorem G_pointerAdd (d a b : ℕ) (h : P[pc]? = some (.pointerAdd d a b)) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r (Function.update p d (p a + p b)) M im bm q (w + 1) := by
  simp [st, oracleStep, h]

theorem G_pointerSub (d a b : ℕ) (h : P[pc]? = some (.pointerSub d a b)) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r (Function.update p d (p a - p b)) M im bm q (w + 1) := by
  simp [st, oracleStep, h]

theorem G_pointerMul (d a b : ℕ) (h : P[pc]? = some (.pointerMul d a b)) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r (Function.update p d (p a * p b)) M im bm q (w + 1) := by
  simp [st, oracleStep, h]

theorem G_iload (d a : ℕ) (h : P[pc]? = some (.integerLoad d a)) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r (Function.update p d (im (p a))) M im bm q (w + 1) := by
  simp [st, oracleStep, h]

theorem G_istore (a b : ℕ) (h : P[pc]? = some (.integerStore a b)) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r p M (Function.update im (p a) (p b)) bm q (w + 1) := by
  simp [st, oracleStep, h]

theorem G_query (d b : ℕ) (h : P[pc]? = some (.query d b)) :
    oracleStep P f (st pc r p M im bm q w)
      = st (pc + 1) (Function.update r d (f (bm (p b)) : ℝ)) p M im bm (q + 1) (w + 1) := by
  simp [st, oracleStep, h]

theorem G_bw (b e v : ℕ) (j : Fin n) (h : P[pc]? = some (.bitWrite b e v)) (hj : p e = (j : ℤ)) :
    oracleStep P f (st pc r p M im bm q w) = st (pc + 1) r p M im
      (Function.update bm (p b) (if r v = 0 then (bm (p b)).erase j else insert j (bm (p b)))) q (w + 1) := by
  have h1 : 0 ≤ p e ∧ (p e).toNat < n := by rw [hj]; exact ⟨by positivity, by simp⟩
  have h2 : (⟨(p e).toNat, h1.2⟩ : Fin n) = j := by ext; simp [hj]
  simp only [st, oracleStep, h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, dif_pos h1, h2]

theorem G_br (d b e : ℕ) (j : Fin n) (h : P[pc]? = some (.bitRead d b e)) (hj : p e = (j : ℤ)) :
    oracleStep P f (st pc r p M im bm q w)
      = st (pc + 1) (Function.update r d (if j ∈ bm (p b) then 1 else 0)) p M im bm q (w + 1) := by
  have h1 : 0 ≤ p e ∧ (p e).toNat < n := by rw [hj]; exact ⟨by positivity, by simp⟩
  have h2 : (⟨(p e).toNat, h1.2⟩ : Fin n) = j := by ext; simp [hj]
  simp only [st, oracleStep, h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, dif_pos h1, h2]

theorem G_halt (a : ℕ) (h : P[pc]? = some (.halt a)) :
    oracleStep P f (st pc r p M im bm q w)
      = (⟨⟨pc + 1, r, p, M⟩, im, bm, some (p a), q, w + 1⟩ : OracleState n) := by
  simp [st, oracleStep, h]

end G

/-- The oracle program (generated by scratch/probe/0c67edc8_lib/asm.py; do not hand-edit). -/
def lswProg (c : ℕ) : OracleProgram := [
  .core (.pset 4 0),  -- 0
  .core (.pset 5 1),  -- 1
  .core (.pset 18 (-1)),  -- 2
  .core (.pset 19 3),  -- 3
  .integerLoad 0 4,  -- 4
  .integerLoad 1 5,  -- 5
  .core (.pset 8 2),  -- 6
  .integerLoad 2 8,  -- 7
  .core (.pset 3 (c : ℤ)),  -- 8
  .pointerMul 14 0 0,  -- 9
  .core (.const 1 1),  -- 10
  .core (.pset 11 0),  -- 11
  .core (.pset 7 0),  -- 12
  .core (.pjle 0 7 23),  -- 13
  .pointerMul 8 11 0,  -- 14
  .pointerAdd 8 8 14,  -- 15
  .pointerAdd 8 8 19,  -- 16
  .pointerAdd 8 8 7,  -- 17
  .integerLoad 10 8,  -- 18
  .pointerSub 9 18 10,  -- 19
  .integerStore 9 7,  -- 20
  .core (.pinc 7),  -- 21
  .core (.pjle 4 4 13),  -- 22
  .core (.pcopy 6 0),  -- 23
  .core (.pdec 6),  -- 24
  .core (.pjle 4 6 27),  -- 25
  .core (.pjle 4 4 51),  -- 26
  .pointerSub 9 18 6,  -- 27
  .integerLoad 7 9,  -- 28
  .core (.const 11 0),  -- 29
  .core (.pjle 7 2 32),  -- 30
  .core (.pjle 4 4 35),  -- 31
  .core (.pjle 2 7 34),  -- 32
  .core (.pjle 4 4 35),  -- 33
  .core (.const 11 1),  -- 34
  .core (.pset 20 0),  -- 35
  .core (.pjle 0 20 47),  -- 36
  .bitRead 6 4 20,  -- 37
  .core (.jle 6 45),  -- 38
  .pointerMul 8 20 0,  -- 39
  .pointerAdd 8 8 7,  -- 40
  .pointerAdd 8 8 19,  -- 41
  .integerLoad 10 8,  -- 42
  .core (.pjle 10 4 45),  -- 43
  .core (.const 11 1),  -- 44
  .core (.pinc 20),  -- 45
  .core (.pjle 4 4 36),  -- 46
  .core (.jle 11 49),  -- 47
  .bitWrite 4 7 1,  -- 48
  .core (.pdec 6),  -- 49
  .core (.pjle 4 4 25),  -- 50
  .query 2 4,  -- 51
  .bitWrite 4 2 0,  -- 52
  .query 3 4,  -- 53
  .bitWrite 4 2 1,  -- 54
  .core (.sub 4 2 3),  -- 55
  .core (.pset 11 0),  -- 56
  .core (.pjle 1 11 75),  -- 57
  .core (.pcopy 8 11),  -- 58
  .core (.load 10 8),  -- 59
  .core (.pset 7 0),  -- 60
  .core (.pjle 0 7 73),  -- 61
  .pointerMul 8 11 0,  -- 62
  .pointerAdd 8 8 1,  -- 63
  .pointerAdd 8 8 7,  -- 64
  .core (.load 6 8),  -- 65
  .core (.mul 6 6 10),  -- 66
  .pointerSub 9 18 7,  -- 67
  .core (.load 7 9),  -- 68
  .core (.add 7 7 6),  -- 69
  .core (.store 9 7),  -- 70
  .core (.pinc 7),  -- 71
  .core (.pjle 4 4 61),  -- 72
  .core (.pinc 11),  -- 73
  .core (.pjle 4 4 57),  -- 74
  .core (.pset 11 0),  -- 75
  .core (.pcopy 8 11),  -- 76
  .core (.load 10 8),  -- 77
  .pointerMul 8 11 0,  -- 78
  .pointerAdd 8 8 1,  -- 79
  .pointerAdd 8 8 2,  -- 80
  .core (.load 6 8),  -- 81
  .core (.sub 6 4 6),  -- 82
  .core (.mul 5 6 10),  -- 83
  .core (.pset 13 0),  -- 84
  .core (.pjle 1 11 100),  -- 85
  .core (.pcopy 8 11),  -- 86
  .core (.load 10 8),  -- 87
  .pointerMul 8 11 0,  -- 88
  .pointerAdd 8 8 1,  -- 89
  .pointerAdd 8 8 2,  -- 90
  .core (.load 6 8),  -- 91
  .core (.sub 6 4 6),  -- 92
  .core (.mul 7 6 10),  -- 93
  .core (.sub 6 7 5),  -- 94
  .core (.jle 6 98),  -- 95
  .core (.add 5 7 0),  -- 96
  .core (.pcopy 13 11),  -- 97
  .core (.pinc 11),  -- 98
  .core (.pjle 4 4 85),  -- 99
  .core (.pjle 0 3 104),  -- 100
  .core (.pcopy 11 13),  -- 101
  .core (.pcopy 12 13),  -- 102
  .core (.pjle 4 4 107),  -- 103
  .core (.pset 11 0),  -- 104
  .core (.pcopy 12 1),  -- 105
  .core (.pdec 12),  -- 106
  .core (.pjle 11 12 109),  -- 107
  .core (.pjle 4 4 151),  -- 108
  .pointerAdd 17 11 5,  -- 109
  .core (.pset 7 0),  -- 110
  .core (.pjle 0 7 123),  -- 111
  .pointerMul 8 11 0,  -- 112
  .pointerAdd 8 8 14,  -- 113
  .pointerAdd 8 8 19,  -- 114
  .pointerAdd 8 8 7,  -- 115
  .integerLoad 10 8,  -- 116
  .pointerSub 9 18 10,  -- 117
  .integerStore 9 7,  -- 118
  .bitRead 6 4 7,  -- 119
  .bitWrite 17 7 6,  -- 120
  .core (.pinc 7),  -- 121
  .core (.pjle 4 4 111),  -- 122
  .core (.add 8 2 0),  -- 123
  .core (.pcopy 9 11),  -- 124
  .core (.load 10 9),  -- 125
  .core (.pset 6 0),  -- 126
  .core (.pjle 0 6 149),  -- 127
  .pointerSub 9 18 6,  -- 128
  .integerLoad 7 9,  -- 129
  .bitRead 6 4 7,  -- 130
  .core (.jle 6 133),  -- 131
  .core (.pjle 4 4 147),  -- 132
  .bitWrite 17 7 1,  -- 133
  .query 9 17,  -- 134
  .core (.sub 13 9 8),  -- 135
  .core (.add 8 9 0),  -- 136
  .pointerMul 8 11 0,  -- 137
  .pointerAdd 8 8 1,  -- 138
  .pointerAdd 8 8 7,  -- 139
  .core (.load 7 8),  -- 140
  .core (.sub 13 13 7),  -- 141
  .core (.mul 13 13 10),  -- 142
  .pointerSub 9 18 7,  -- 143
  .core (.load 7 9),  -- 144
  .core (.add 7 7 13),  -- 145
  .core (.store 9 7),  -- 146
  .core (.pinc 6),  -- 147
  .core (.pjle 4 4 127),  -- 148
  .core (.pinc 11),  -- 149
  .core (.pjle 4 4 107),  -- 150
  .core (.pset 16 0),  -- 151
  .core (.pset 7 0),  -- 152
  .core (.pjle 0 7 168),  -- 153
  .bitRead 6 4 7,  -- 154
  .core (.jle 6 157),  -- 155
  .core (.pjle 4 4 166),  -- 156
  .pointerSub 9 18 7,  -- 157
  .core (.load 7 9),  -- 158
  .core (.pjle 16 4 163),  -- 159
  .core (.sub 6 7 12),  -- 160
  .core (.jle 6 163),  -- 161
  .core (.pjle 4 4 166),  -- 162
  .core (.add 12 7 0),  -- 163
  .core (.pcopy 15 7),  -- 164
  .core (.pset 16 1),  -- 165
  .core (.pinc 7),  -- 166
  .core (.pjle 4 4 153),  -- 167
  .halt 15  -- 168
]



set_option maxRecDepth 20000 in
theorem lswProg_length (c : ℕ) : (lswProg c).length = 169 := rfl

theorem lit0 : ∃ r : ℚ, (0 : ℝ) = (r : ℝ) := ⟨0, by simp⟩
theorem lit1 : ∃ r : ℚ, (1 : ℝ) = (r : ℝ) := ⟨1, by simp⟩

set_option maxRecDepth 20000 in
theorem lswProg_literal (c : ℕ) : LiteralProgram (lswProg c) := by
  unfold LiteralProgram
  simp only [lswProg, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, and_true, lit0,
    lit1, implies_true]

/-! ## Per-index step lemmas (generated by 0c67edc8_lib/gen_steps.py). -/

theorem S0 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 0 r p M im bm q w) = st 1 r (Function.update p 4 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 0 r p M im bm q w 4 0 rfl

theorem S1 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 1 r p M im bm q w) = st 2 r (Function.update p 5 1) M im bm q (w + 1) :=
  G_pset (lswProg c) f 1 r p M im bm q w 5 1 rfl

theorem S2 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 2 r p M im bm q w) = st 3 r (Function.update p 18 (-1)) M im bm q (w + 1) :=
  G_pset (lswProg c) f 2 r p M im bm q w 18 (-1) rfl

theorem S3 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 3 r p M im bm q w) = st 4 r (Function.update p 19 3) M im bm q (w + 1) :=
  G_pset (lswProg c) f 3 r p M im bm q w 19 3 rfl

theorem S4 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 4 r p M im bm q w) = st 5 r (Function.update p 0 (im (p 4))) M im bm q (w + 1) :=
  G_iload (lswProg c) f 4 r p M im bm q w 0 4 rfl

theorem S5 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 5 r p M im bm q w) = st 6 r (Function.update p 1 (im (p 5))) M im bm q (w + 1) :=
  G_iload (lswProg c) f 5 r p M im bm q w 1 5 rfl

theorem S6 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 6 r p M im bm q w) = st 7 r (Function.update p 8 2) M im bm q (w + 1) :=
  G_pset (lswProg c) f 6 r p M im bm q w 8 2 rfl

theorem S7 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 7 r p M im bm q w) = st 8 r (Function.update p 2 (im (p 8))) M im bm q (w + 1) :=
  G_iload (lswProg c) f 7 r p M im bm q w 2 8 rfl

theorem S8 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 8 r p M im bm q w) = st 9 r (Function.update p 3 (c : ℤ)) M im bm q (w + 1) :=
  G_pset (lswProg c) f 8 r p M im bm q w 3 (c : ℤ) rfl

theorem S9 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 9 r p M im bm q w) = st 10 r (Function.update p 14 (p 0 * p 0)) M im bm q (w + 1) :=
  G_pointerMul (lswProg c) f 9 r p M im bm q w 14 0 0 rfl

theorem S10 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 10 r p M im bm q w) = st 11 (Function.update r 1 1) p M im bm q (w + 1) :=
  G_const (lswProg c) f 10 r p M im bm q w 1 1 rfl

theorem S11 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 11 r p M im bm q w) = st 12 r (Function.update p 11 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 11 r p M im bm q w 11 0 rfl

theorem S12 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 12 r p M im bm q w) = st 13 r (Function.update p 7 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 12 r p M im bm q w 7 0 rfl

theorem S13 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 13 r p M im bm q w) = st (if p 0 ≤ p 7 then 23 else 14) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 13 r p M im bm q w 0 7 23 rfl

theorem S14 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 14 r p M im bm q w) = st 15 r (Function.update p 8 (p 11 * p 0)) M im bm q (w + 1) :=
  G_pointerMul (lswProg c) f 14 r p M im bm q w 8 11 0 rfl

theorem S15 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 15 r p M im bm q w) = st 16 r (Function.update p 8 (p 8 + p 14)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 15 r p M im bm q w 8 8 14 rfl

theorem S16 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 16 r p M im bm q w) = st 17 r (Function.update p 8 (p 8 + p 19)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 16 r p M im bm q w 8 8 19 rfl

theorem S17 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 17 r p M im bm q w) = st 18 r (Function.update p 8 (p 8 + p 7)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 17 r p M im bm q w 8 8 7 rfl

theorem S18 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 18 r p M im bm q w) = st 19 r (Function.update p 10 (im (p 8))) M im bm q (w + 1) :=
  G_iload (lswProg c) f 18 r p M im bm q w 10 8 rfl

theorem S19 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 19 r p M im bm q w) = st 20 r (Function.update p 9 (p 18 - p 10)) M im bm q (w + 1) :=
  G_pointerSub (lswProg c) f 19 r p M im bm q w 9 18 10 rfl

theorem S20 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 20 r p M im bm q w) = st 21 r p M (Function.update im (p 9) (p 7)) bm q (w + 1) :=
  G_istore (lswProg c) f 20 r p M im bm q w 9 7 rfl

theorem S21 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 21 r p M im bm q w) = st 22 r (Function.update p 7 (p 7 + 1)) M im bm q (w + 1) :=
  G_pinc (lswProg c) f 21 r p M im bm q w 7 rfl

theorem S22 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 22 r p M im bm q w) = st (if p 4 ≤ p 4 then 13 else 23) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 22 r p M im bm q w 4 4 13 rfl

theorem S23 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 23 r p M im bm q w) = st 24 r (Function.update p 6 (p 0)) M im bm q (w + 1) :=
  G_pcopy (lswProg c) f 23 r p M im bm q w 6 0 rfl

theorem S24 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 24 r p M im bm q w) = st 25 r (Function.update p 6 (p 6 - 1)) M im bm q (w + 1) :=
  G_pdec (lswProg c) f 24 r p M im bm q w 6 rfl

theorem S25 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 25 r p M im bm q w) = st (if p 4 ≤ p 6 then 27 else 26) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 25 r p M im bm q w 4 6 27 rfl

theorem S26 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 26 r p M im bm q w) = st (if p 4 ≤ p 4 then 51 else 27) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 26 r p M im bm q w 4 4 51 rfl

theorem S27 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 27 r p M im bm q w) = st 28 r (Function.update p 9 (p 18 - p 6)) M im bm q (w + 1) :=
  G_pointerSub (lswProg c) f 27 r p M im bm q w 9 18 6 rfl

theorem S28 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 28 r p M im bm q w) = st 29 r (Function.update p 7 (im (p 9))) M im bm q (w + 1) :=
  G_iload (lswProg c) f 28 r p M im bm q w 7 9 rfl

theorem S29 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 29 r p M im bm q w) = st 30 (Function.update r 11 0) p M im bm q (w + 1) :=
  G_const (lswProg c) f 29 r p M im bm q w 11 0 rfl

theorem S30 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 30 r p M im bm q w) = st (if p 7 ≤ p 2 then 32 else 31) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 30 r p M im bm q w 7 2 32 rfl

theorem S31 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 31 r p M im bm q w) = st (if p 4 ≤ p 4 then 35 else 32) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 31 r p M im bm q w 4 4 35 rfl

theorem S32 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 32 r p M im bm q w) = st (if p 2 ≤ p 7 then 34 else 33) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 32 r p M im bm q w 2 7 34 rfl

theorem S33 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 33 r p M im bm q w) = st (if p 4 ≤ p 4 then 35 else 34) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 33 r p M im bm q w 4 4 35 rfl

theorem S34 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 34 r p M im bm q w) = st 35 (Function.update r 11 1) p M im bm q (w + 1) :=
  G_const (lswProg c) f 34 r p M im bm q w 11 1 rfl

theorem S35 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 35 r p M im bm q w) = st 36 r (Function.update p 20 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 35 r p M im bm q w 20 0 rfl

theorem S36 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 36 r p M im bm q w) = st (if p 0 ≤ p 20 then 47 else 37) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 36 r p M im bm q w 0 20 47 rfl

theorem S37 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) (j : Fin n) (hj : p 20 = (j : ℤ)) :
    oracleStep (lswProg c) f (st 37 r p M im bm q w) = st 38 (Function.update r 6 (if j ∈ bm (p 4) then 1 else 0)) p M im bm q (w + 1) :=
  G_br (lswProg c) f 37 r p M im bm q w 6 4 20 j rfl hj

theorem S38 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 38 r p M im bm q w) = st (if r 6 ≤ 0 then 45 else 39) r p M im bm q (w + 1) :=
  G_jle (lswProg c) f 38 r p M im bm q w 6 45 rfl

theorem S39 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 39 r p M im bm q w) = st 40 r (Function.update p 8 (p 20 * p 0)) M im bm q (w + 1) :=
  G_pointerMul (lswProg c) f 39 r p M im bm q w 8 20 0 rfl

theorem S40 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 40 r p M im bm q w) = st 41 r (Function.update p 8 (p 8 + p 7)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 40 r p M im bm q w 8 8 7 rfl

theorem S41 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 41 r p M im bm q w) = st 42 r (Function.update p 8 (p 8 + p 19)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 41 r p M im bm q w 8 8 19 rfl

theorem S42 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 42 r p M im bm q w) = st 43 r (Function.update p 10 (im (p 8))) M im bm q (w + 1) :=
  G_iload (lswProg c) f 42 r p M im bm q w 10 8 rfl

theorem S43 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 43 r p M im bm q w) = st (if p 10 ≤ p 4 then 45 else 44) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 43 r p M im bm q w 10 4 45 rfl

theorem S44 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 44 r p M im bm q w) = st 45 (Function.update r 11 1) p M im bm q (w + 1) :=
  G_const (lswProg c) f 44 r p M im bm q w 11 1 rfl

theorem S45 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 45 r p M im bm q w) = st 46 r (Function.update p 20 (p 20 + 1)) M im bm q (w + 1) :=
  G_pinc (lswProg c) f 45 r p M im bm q w 20 rfl

theorem S46 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 46 r p M im bm q w) = st (if p 4 ≤ p 4 then 36 else 47) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 46 r p M im bm q w 4 4 36 rfl

theorem S47 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 47 r p M im bm q w) = st (if r 11 ≤ 0 then 49 else 48) r p M im bm q (w + 1) :=
  G_jle (lswProg c) f 47 r p M im bm q w 11 49 rfl

theorem S48 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) (j : Fin n) (hj : p 7 = (j : ℤ)) :
    oracleStep (lswProg c) f (st 48 r p M im bm q w) = st 49 r p M im (Function.update bm (p 4) (if r 1 = 0 then (bm (p 4)).erase j else insert j (bm (p 4)))) q (w + 1) :=
  G_bw (lswProg c) f 48 r p M im bm q w 4 7 1 j rfl hj

theorem S49 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 49 r p M im bm q w) = st 50 r (Function.update p 6 (p 6 - 1)) M im bm q (w + 1) :=
  G_pdec (lswProg c) f 49 r p M im bm q w 6 rfl

theorem S50 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 50 r p M im bm q w) = st (if p 4 ≤ p 4 then 25 else 51) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 50 r p M im bm q w 4 4 25 rfl

theorem S51 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 51 r p M im bm q w) = st 52 (Function.update r 2 (f (bm (p 4)) : ℝ)) p M im bm (q + 1) (w + 1) :=
  G_query (lswProg c) f 51 r p M im bm q w 2 4 rfl

theorem S52 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) (j : Fin n) (hj : p 2 = (j : ℤ)) :
    oracleStep (lswProg c) f (st 52 r p M im bm q w) = st 53 r p M im (Function.update bm (p 4) (if r 0 = 0 then (bm (p 4)).erase j else insert j (bm (p 4)))) q (w + 1) :=
  G_bw (lswProg c) f 52 r p M im bm q w 4 2 0 j rfl hj

theorem S53 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 53 r p M im bm q w) = st 54 (Function.update r 3 (f (bm (p 4)) : ℝ)) p M im bm (q + 1) (w + 1) :=
  G_query (lswProg c) f 53 r p M im bm q w 3 4 rfl

theorem S54 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) (j : Fin n) (hj : p 2 = (j : ℤ)) :
    oracleStep (lswProg c) f (st 54 r p M im bm q w) = st 55 r p M im (Function.update bm (p 4) (if r 1 = 0 then (bm (p 4)).erase j else insert j (bm (p 4)))) q (w + 1) :=
  G_bw (lswProg c) f 54 r p M im bm q w 4 2 1 j rfl hj

theorem S55 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 55 r p M im bm q w) = st 56 (Function.update r 4 (r 2 - r 3)) p M im bm q (w + 1) :=
  G_sub (lswProg c) f 55 r p M im bm q w 4 2 3 rfl

theorem S56 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 56 r p M im bm q w) = st 57 r (Function.update p 11 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 56 r p M im bm q w 11 0 rfl

theorem S57 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 57 r p M im bm q w) = st (if p 1 ≤ p 11 then 75 else 58) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 57 r p M im bm q w 1 11 75 rfl

theorem S58 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 58 r p M im bm q w) = st 59 r (Function.update p 8 (p 11)) M im bm q (w + 1) :=
  G_pcopy (lswProg c) f 58 r p M im bm q w 8 11 rfl

theorem S59 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 59 r p M im bm q w) = st 60 (Function.update r 10 (M (p 8))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 59 r p M im bm q w 10 8 rfl

theorem S60 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 60 r p M im bm q w) = st 61 r (Function.update p 7 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 60 r p M im bm q w 7 0 rfl

theorem S61 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 61 r p M im bm q w) = st (if p 0 ≤ p 7 then 73 else 62) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 61 r p M im bm q w 0 7 73 rfl

theorem S62 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 62 r p M im bm q w) = st 63 r (Function.update p 8 (p 11 * p 0)) M im bm q (w + 1) :=
  G_pointerMul (lswProg c) f 62 r p M im bm q w 8 11 0 rfl

theorem S63 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 63 r p M im bm q w) = st 64 r (Function.update p 8 (p 8 + p 1)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 63 r p M im bm q w 8 8 1 rfl

theorem S64 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 64 r p M im bm q w) = st 65 r (Function.update p 8 (p 8 + p 7)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 64 r p M im bm q w 8 8 7 rfl

theorem S65 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 65 r p M im bm q w) = st 66 (Function.update r 6 (M (p 8))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 65 r p M im bm q w 6 8 rfl

theorem S66 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 66 r p M im bm q w) = st 67 (Function.update r 6 (r 6 * r 10)) p M im bm q (w + 1) :=
  G_mul (lswProg c) f 66 r p M im bm q w 6 6 10 rfl

theorem S67 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 67 r p M im bm q w) = st 68 r (Function.update p 9 (p 18 - p 7)) M im bm q (w + 1) :=
  G_pointerSub (lswProg c) f 67 r p M im bm q w 9 18 7 rfl

theorem S68 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 68 r p M im bm q w) = st 69 (Function.update r 7 (M (p 9))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 68 r p M im bm q w 7 9 rfl

theorem S69 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 69 r p M im bm q w) = st 70 (Function.update r 7 (r 7 + r 6)) p M im bm q (w + 1) :=
  G_add (lswProg c) f 69 r p M im bm q w 7 7 6 rfl

theorem S70 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 70 r p M im bm q w) = st 71 r p (Function.update M (p 9) (r 7)) im bm q (w + 1) :=
  G_store (lswProg c) f 70 r p M im bm q w 9 7 rfl

theorem S71 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 71 r p M im bm q w) = st 72 r (Function.update p 7 (p 7 + 1)) M im bm q (w + 1) :=
  G_pinc (lswProg c) f 71 r p M im bm q w 7 rfl

theorem S72 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 72 r p M im bm q w) = st (if p 4 ≤ p 4 then 61 else 73) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 72 r p M im bm q w 4 4 61 rfl

theorem S73 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 73 r p M im bm q w) = st 74 r (Function.update p 11 (p 11 + 1)) M im bm q (w + 1) :=
  G_pinc (lswProg c) f 73 r p M im bm q w 11 rfl

theorem S74 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 74 r p M im bm q w) = st (if p 4 ≤ p 4 then 57 else 75) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 74 r p M im bm q w 4 4 57 rfl

theorem S75 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 75 r p M im bm q w) = st 76 r (Function.update p 11 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 75 r p M im bm q w 11 0 rfl

theorem S76 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 76 r p M im bm q w) = st 77 r (Function.update p 8 (p 11)) M im bm q (w + 1) :=
  G_pcopy (lswProg c) f 76 r p M im bm q w 8 11 rfl

theorem S77 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 77 r p M im bm q w) = st 78 (Function.update r 10 (M (p 8))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 77 r p M im bm q w 10 8 rfl

theorem S78 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 78 r p M im bm q w) = st 79 r (Function.update p 8 (p 11 * p 0)) M im bm q (w + 1) :=
  G_pointerMul (lswProg c) f 78 r p M im bm q w 8 11 0 rfl

theorem S79 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 79 r p M im bm q w) = st 80 r (Function.update p 8 (p 8 + p 1)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 79 r p M im bm q w 8 8 1 rfl

theorem S80 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 80 r p M im bm q w) = st 81 r (Function.update p 8 (p 8 + p 2)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 80 r p M im bm q w 8 8 2 rfl

theorem S81 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 81 r p M im bm q w) = st 82 (Function.update r 6 (M (p 8))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 81 r p M im bm q w 6 8 rfl

theorem S82 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 82 r p M im bm q w) = st 83 (Function.update r 6 (r 4 - r 6)) p M im bm q (w + 1) :=
  G_sub (lswProg c) f 82 r p M im bm q w 6 4 6 rfl

theorem S83 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 83 r p M im bm q w) = st 84 (Function.update r 5 (r 6 * r 10)) p M im bm q (w + 1) :=
  G_mul (lswProg c) f 83 r p M im bm q w 5 6 10 rfl

theorem S84 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 84 r p M im bm q w) = st 85 r (Function.update p 13 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 84 r p M im bm q w 13 0 rfl

theorem S85 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 85 r p M im bm q w) = st (if p 1 ≤ p 11 then 100 else 86) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 85 r p M im bm q w 1 11 100 rfl

theorem S86 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 86 r p M im bm q w) = st 87 r (Function.update p 8 (p 11)) M im bm q (w + 1) :=
  G_pcopy (lswProg c) f 86 r p M im bm q w 8 11 rfl

theorem S87 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 87 r p M im bm q w) = st 88 (Function.update r 10 (M (p 8))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 87 r p M im bm q w 10 8 rfl

theorem S88 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 88 r p M im bm q w) = st 89 r (Function.update p 8 (p 11 * p 0)) M im bm q (w + 1) :=
  G_pointerMul (lswProg c) f 88 r p M im bm q w 8 11 0 rfl

theorem S89 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 89 r p M im bm q w) = st 90 r (Function.update p 8 (p 8 + p 1)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 89 r p M im bm q w 8 8 1 rfl

theorem S90 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 90 r p M im bm q w) = st 91 r (Function.update p 8 (p 8 + p 2)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 90 r p M im bm q w 8 8 2 rfl

theorem S91 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 91 r p M im bm q w) = st 92 (Function.update r 6 (M (p 8))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 91 r p M im bm q w 6 8 rfl

theorem S92 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 92 r p M im bm q w) = st 93 (Function.update r 6 (r 4 - r 6)) p M im bm q (w + 1) :=
  G_sub (lswProg c) f 92 r p M im bm q w 6 4 6 rfl

theorem S93 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 93 r p M im bm q w) = st 94 (Function.update r 7 (r 6 * r 10)) p M im bm q (w + 1) :=
  G_mul (lswProg c) f 93 r p M im bm q w 7 6 10 rfl

theorem S94 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 94 r p M im bm q w) = st 95 (Function.update r 6 (r 7 - r 5)) p M im bm q (w + 1) :=
  G_sub (lswProg c) f 94 r p M im bm q w 6 7 5 rfl

theorem S95 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 95 r p M im bm q w) = st (if r 6 ≤ 0 then 98 else 96) r p M im bm q (w + 1) :=
  G_jle (lswProg c) f 95 r p M im bm q w 6 98 rfl

theorem S96 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 96 r p M im bm q w) = st 97 (Function.update r 5 (r 7 + r 0)) p M im bm q (w + 1) :=
  G_add (lswProg c) f 96 r p M im bm q w 5 7 0 rfl

theorem S97 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 97 r p M im bm q w) = st 98 r (Function.update p 13 (p 11)) M im bm q (w + 1) :=
  G_pcopy (lswProg c) f 97 r p M im bm q w 13 11 rfl

theorem S98 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 98 r p M im bm q w) = st 99 r (Function.update p 11 (p 11 + 1)) M im bm q (w + 1) :=
  G_pinc (lswProg c) f 98 r p M im bm q w 11 rfl

theorem S99 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 99 r p M im bm q w) = st (if p 4 ≤ p 4 then 85 else 100) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 99 r p M im bm q w 4 4 85 rfl

theorem S100 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 100 r p M im bm q w) = st (if p 0 ≤ p 3 then 104 else 101) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 100 r p M im bm q w 0 3 104 rfl

theorem S101 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 101 r p M im bm q w) = st 102 r (Function.update p 11 (p 13)) M im bm q (w + 1) :=
  G_pcopy (lswProg c) f 101 r p M im bm q w 11 13 rfl

theorem S102 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 102 r p M im bm q w) = st 103 r (Function.update p 12 (p 13)) M im bm q (w + 1) :=
  G_pcopy (lswProg c) f 102 r p M im bm q w 12 13 rfl

theorem S103 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 103 r p M im bm q w) = st (if p 4 ≤ p 4 then 107 else 104) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 103 r p M im bm q w 4 4 107 rfl

theorem S104 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 104 r p M im bm q w) = st 105 r (Function.update p 11 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 104 r p M im bm q w 11 0 rfl

theorem S105 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 105 r p M im bm q w) = st 106 r (Function.update p 12 (p 1)) M im bm q (w + 1) :=
  G_pcopy (lswProg c) f 105 r p M im bm q w 12 1 rfl

theorem S106 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 106 r p M im bm q w) = st 107 r (Function.update p 12 (p 12 - 1)) M im bm q (w + 1) :=
  G_pdec (lswProg c) f 106 r p M im bm q w 12 rfl

theorem S107 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 107 r p M im bm q w) = st (if p 11 ≤ p 12 then 109 else 108) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 107 r p M im bm q w 11 12 109 rfl

theorem S108 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 108 r p M im bm q w) = st (if p 4 ≤ p 4 then 151 else 109) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 108 r p M im bm q w 4 4 151 rfl

theorem S109 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 109 r p M im bm q w) = st 110 r (Function.update p 17 (p 11 + p 5)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 109 r p M im bm q w 17 11 5 rfl

theorem S110 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 110 r p M im bm q w) = st 111 r (Function.update p 7 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 110 r p M im bm q w 7 0 rfl

theorem S111 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 111 r p M im bm q w) = st (if p 0 ≤ p 7 then 123 else 112) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 111 r p M im bm q w 0 7 123 rfl

theorem S112 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 112 r p M im bm q w) = st 113 r (Function.update p 8 (p 11 * p 0)) M im bm q (w + 1) :=
  G_pointerMul (lswProg c) f 112 r p M im bm q w 8 11 0 rfl

theorem S113 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 113 r p M im bm q w) = st 114 r (Function.update p 8 (p 8 + p 14)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 113 r p M im bm q w 8 8 14 rfl

theorem S114 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 114 r p M im bm q w) = st 115 r (Function.update p 8 (p 8 + p 19)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 114 r p M im bm q w 8 8 19 rfl

theorem S115 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 115 r p M im bm q w) = st 116 r (Function.update p 8 (p 8 + p 7)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 115 r p M im bm q w 8 8 7 rfl

theorem S116 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 116 r p M im bm q w) = st 117 r (Function.update p 10 (im (p 8))) M im bm q (w + 1) :=
  G_iload (lswProg c) f 116 r p M im bm q w 10 8 rfl

theorem S117 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 117 r p M im bm q w) = st 118 r (Function.update p 9 (p 18 - p 10)) M im bm q (w + 1) :=
  G_pointerSub (lswProg c) f 117 r p M im bm q w 9 18 10 rfl

theorem S118 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 118 r p M im bm q w) = st 119 r p M (Function.update im (p 9) (p 7)) bm q (w + 1) :=
  G_istore (lswProg c) f 118 r p M im bm q w 9 7 rfl

theorem S119 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) (j : Fin n) (hj : p 7 = (j : ℤ)) :
    oracleStep (lswProg c) f (st 119 r p M im bm q w) = st 120 (Function.update r 6 (if j ∈ bm (p 4) then 1 else 0)) p M im bm q (w + 1) :=
  G_br (lswProg c) f 119 r p M im bm q w 6 4 7 j rfl hj

theorem S120 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) (j : Fin n) (hj : p 7 = (j : ℤ)) :
    oracleStep (lswProg c) f (st 120 r p M im bm q w) = st 121 r p M im (Function.update bm (p 17) (if r 6 = 0 then (bm (p 17)).erase j else insert j (bm (p 17)))) q (w + 1) :=
  G_bw (lswProg c) f 120 r p M im bm q w 17 7 6 j rfl hj

theorem S121 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 121 r p M im bm q w) = st 122 r (Function.update p 7 (p 7 + 1)) M im bm q (w + 1) :=
  G_pinc (lswProg c) f 121 r p M im bm q w 7 rfl

theorem S122 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 122 r p M im bm q w) = st (if p 4 ≤ p 4 then 111 else 123) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 122 r p M im bm q w 4 4 111 rfl

theorem S123 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 123 r p M im bm q w) = st 124 (Function.update r 8 (r 2 + r 0)) p M im bm q (w + 1) :=
  G_add (lswProg c) f 123 r p M im bm q w 8 2 0 rfl

theorem S124 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 124 r p M im bm q w) = st 125 r (Function.update p 9 (p 11)) M im bm q (w + 1) :=
  G_pcopy (lswProg c) f 124 r p M im bm q w 9 11 rfl

theorem S125 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 125 r p M im bm q w) = st 126 (Function.update r 10 (M (p 9))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 125 r p M im bm q w 10 9 rfl

theorem S126 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 126 r p M im bm q w) = st 127 r (Function.update p 6 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 126 r p M im bm q w 6 0 rfl

theorem S127 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 127 r p M im bm q w) = st (if p 0 ≤ p 6 then 149 else 128) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 127 r p M im bm q w 0 6 149 rfl

theorem S128 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 128 r p M im bm q w) = st 129 r (Function.update p 9 (p 18 - p 6)) M im bm q (w + 1) :=
  G_pointerSub (lswProg c) f 128 r p M im bm q w 9 18 6 rfl

theorem S129 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 129 r p M im bm q w) = st 130 r (Function.update p 7 (im (p 9))) M im bm q (w + 1) :=
  G_iload (lswProg c) f 129 r p M im bm q w 7 9 rfl

theorem S130 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) (j : Fin n) (hj : p 7 = (j : ℤ)) :
    oracleStep (lswProg c) f (st 130 r p M im bm q w) = st 131 (Function.update r 6 (if j ∈ bm (p 4) then 1 else 0)) p M im bm q (w + 1) :=
  G_br (lswProg c) f 130 r p M im bm q w 6 4 7 j rfl hj

theorem S131 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 131 r p M im bm q w) = st (if r 6 ≤ 0 then 133 else 132) r p M im bm q (w + 1) :=
  G_jle (lswProg c) f 131 r p M im bm q w 6 133 rfl

theorem S132 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 132 r p M im bm q w) = st (if p 4 ≤ p 4 then 147 else 133) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 132 r p M im bm q w 4 4 147 rfl

theorem S133 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) (j : Fin n) (hj : p 7 = (j : ℤ)) :
    oracleStep (lswProg c) f (st 133 r p M im bm q w) = st 134 r p M im (Function.update bm (p 17) (if r 1 = 0 then (bm (p 17)).erase j else insert j (bm (p 17)))) q (w + 1) :=
  G_bw (lswProg c) f 133 r p M im bm q w 17 7 1 j rfl hj

theorem S134 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 134 r p M im bm q w) = st 135 (Function.update r 9 (f (bm (p 17)) : ℝ)) p M im bm (q + 1) (w + 1) :=
  G_query (lswProg c) f 134 r p M im bm q w 9 17 rfl

theorem S135 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 135 r p M im bm q w) = st 136 (Function.update r 13 (r 9 - r 8)) p M im bm q (w + 1) :=
  G_sub (lswProg c) f 135 r p M im bm q w 13 9 8 rfl

theorem S136 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 136 r p M im bm q w) = st 137 (Function.update r 8 (r 9 + r 0)) p M im bm q (w + 1) :=
  G_add (lswProg c) f 136 r p M im bm q w 8 9 0 rfl

theorem S137 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 137 r p M im bm q w) = st 138 r (Function.update p 8 (p 11 * p 0)) M im bm q (w + 1) :=
  G_pointerMul (lswProg c) f 137 r p M im bm q w 8 11 0 rfl

theorem S138 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 138 r p M im bm q w) = st 139 r (Function.update p 8 (p 8 + p 1)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 138 r p M im bm q w 8 8 1 rfl

theorem S139 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 139 r p M im bm q w) = st 140 r (Function.update p 8 (p 8 + p 7)) M im bm q (w + 1) :=
  G_pointerAdd (lswProg c) f 139 r p M im bm q w 8 8 7 rfl

theorem S140 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 140 r p M im bm q w) = st 141 (Function.update r 7 (M (p 8))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 140 r p M im bm q w 7 8 rfl

theorem S141 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 141 r p M im bm q w) = st 142 (Function.update r 13 (r 13 - r 7)) p M im bm q (w + 1) :=
  G_sub (lswProg c) f 141 r p M im bm q w 13 13 7 rfl

theorem S142 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 142 r p M im bm q w) = st 143 (Function.update r 13 (r 13 * r 10)) p M im bm q (w + 1) :=
  G_mul (lswProg c) f 142 r p M im bm q w 13 13 10 rfl

theorem S143 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 143 r p M im bm q w) = st 144 r (Function.update p 9 (p 18 - p 7)) M im bm q (w + 1) :=
  G_pointerSub (lswProg c) f 143 r p M im bm q w 9 18 7 rfl

theorem S144 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 144 r p M im bm q w) = st 145 (Function.update r 7 (M (p 9))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 144 r p M im bm q w 7 9 rfl

theorem S145 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 145 r p M im bm q w) = st 146 (Function.update r 7 (r 7 + r 13)) p M im bm q (w + 1) :=
  G_add (lswProg c) f 145 r p M im bm q w 7 7 13 rfl

theorem S146 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 146 r p M im bm q w) = st 147 r p (Function.update M (p 9) (r 7)) im bm q (w + 1) :=
  G_store (lswProg c) f 146 r p M im bm q w 9 7 rfl

theorem S147 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 147 r p M im bm q w) = st 148 r (Function.update p 6 (p 6 + 1)) M im bm q (w + 1) :=
  G_pinc (lswProg c) f 147 r p M im bm q w 6 rfl

theorem S148 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 148 r p M im bm q w) = st (if p 4 ≤ p 4 then 127 else 149) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 148 r p M im bm q w 4 4 127 rfl

theorem S149 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 149 r p M im bm q w) = st 150 r (Function.update p 11 (p 11 + 1)) M im bm q (w + 1) :=
  G_pinc (lswProg c) f 149 r p M im bm q w 11 rfl

theorem S150 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 150 r p M im bm q w) = st (if p 4 ≤ p 4 then 107 else 151) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 150 r p M im bm q w 4 4 107 rfl

theorem S151 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 151 r p M im bm q w) = st 152 r (Function.update p 16 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 151 r p M im bm q w 16 0 rfl

theorem S152 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 152 r p M im bm q w) = st 153 r (Function.update p 7 0) M im bm q (w + 1) :=
  G_pset (lswProg c) f 152 r p M im bm q w 7 0 rfl

theorem S153 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 153 r p M im bm q w) = st (if p 0 ≤ p 7 then 168 else 154) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 153 r p M im bm q w 0 7 168 rfl

theorem S154 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) (j : Fin n) (hj : p 7 = (j : ℤ)) :
    oracleStep (lswProg c) f (st 154 r p M im bm q w) = st 155 (Function.update r 6 (if j ∈ bm (p 4) then 1 else 0)) p M im bm q (w + 1) :=
  G_br (lswProg c) f 154 r p M im bm q w 6 4 7 j rfl hj

theorem S155 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 155 r p M im bm q w) = st (if r 6 ≤ 0 then 157 else 156) r p M im bm q (w + 1) :=
  G_jle (lswProg c) f 155 r p M im bm q w 6 157 rfl

theorem S156 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 156 r p M im bm q w) = st (if p 4 ≤ p 4 then 166 else 157) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 156 r p M im bm q w 4 4 166 rfl

theorem S157 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 157 r p M im bm q w) = st 158 r (Function.update p 9 (p 18 - p 7)) M im bm q (w + 1) :=
  G_pointerSub (lswProg c) f 157 r p M im bm q w 9 18 7 rfl

theorem S158 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 158 r p M im bm q w) = st 159 (Function.update r 7 (M (p 9))) p M im bm q (w + 1) :=
  G_load (lswProg c) f 158 r p M im bm q w 7 9 rfl

theorem S159 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 159 r p M im bm q w) = st (if p 16 ≤ p 4 then 163 else 160) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 159 r p M im bm q w 16 4 163 rfl

theorem S160 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 160 r p M im bm q w) = st 161 (Function.update r 6 (r 7 - r 12)) p M im bm q (w + 1) :=
  G_sub (lswProg c) f 160 r p M im bm q w 6 7 12 rfl

theorem S161 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 161 r p M im bm q w) = st (if r 6 ≤ 0 then 163 else 162) r p M im bm q (w + 1) :=
  G_jle (lswProg c) f 161 r p M im bm q w 6 163 rfl

theorem S162 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 162 r p M im bm q w) = st (if p 4 ≤ p 4 then 166 else 163) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 162 r p M im bm q w 4 4 166 rfl

theorem S163 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 163 r p M im bm q w) = st 164 (Function.update r 12 (r 7 + r 0)) p M im bm q (w + 1) :=
  G_add (lswProg c) f 163 r p M im bm q w 12 7 0 rfl

theorem S164 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 164 r p M im bm q w) = st 165 r (Function.update p 15 (p 7)) M im bm q (w + 1) :=
  G_pcopy (lswProg c) f 164 r p M im bm q w 15 7 rfl

theorem S165 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 165 r p M im bm q w) = st 166 r (Function.update p 16 1) M im bm q (w + 1) :=
  G_pset (lswProg c) f 165 r p M im bm q w 16 1 rfl

theorem S166 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 166 r p M im bm q w) = st 167 r (Function.update p 7 (p 7 + 1)) M im bm q (w + 1) :=
  G_pinc (lswProg c) f 166 r p M im bm q w 7 rfl

theorem S167 (c : ℕ) (f : Finset (Fin n) → ℤ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q w : ℕ) :
    oracleStep (lswProg c) f (st 167 r p M im bm q w) = st (if p 4 ≤ p 4 then 153 else 168) r p M im bm q (w + 1) :=
  G_pjle (lswProg c) f 167 r p M im bm q w 4 4 153 rfl


/-! ## Reachability in continuation style, the frame invariant, input cells. -/

section Run
variable {m : ℕ}

def RP (c : ℕ) (f : Finset (Fin n) → ℤ) (s : OracleState n) (G : OracleState n → Prop) : Prop :=
  ∃ t, G ((oracleStep (lswProg c) f)^[t] s)

theorem RP.step {c : ℕ} {f : Finset (Fin n) → ℤ} {s : OracleState n} {G : OracleState n → Prop}
    (h : RP c f (oracleStep (lswProg c) f s) G) : RP c f s G := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t + 1, by rw [Function.iterate_succ_apply]; exact ht⟩

theorem RP.done {c : ℕ} {f : Finset (Fin n) → ℤ} {s : OracleState n} {G : OracleState n → Prop}
    (h : G s) : RP c f s G := ⟨0, h⟩

structure Frame (c : ℕ) (I : ArcInput n m) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ) :
    Prop where
  p0 : p 0 = n
  p1 : p 1 = m
  p2 : p 2 = (I.point : ℕ)
  p3 : p 3 = c
  p4 : p 4 = 0
  p5 : p 5 = 1
  p14 : p 14 = n * n
  p18 : p 18 = -1
  p19 : p 19 = 3
  r0 : r 0 = 0
  r1 : r 1 = 1
  im_in : ∀ a, 0 ≤ a → im a = inputIntegerCell I a
  M_in : ∀ a, 0 ≤ a → M a = inputRealCell I a

theorem Frame.upd_p {c : ℕ} {I : ArcInput n m} {r : ℕ → ℝ} {p : ℕ → ℤ} {M : ℤ → ℝ} {im : ℤ → ℤ}
    (F : Frame c I r p M im) (d : ℕ) (v : ℤ)
    (hd : d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 2 ∧ d ≠ 3 ∧ d ≠ 4 ∧ d ≠ 5 ∧ d ≠ 14 ∧ d ≠ 18 ∧ d ≠ 19) :
    Frame c I r (Function.update p d v) M im := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h14, h18, h19⟩ := hd
  exact ⟨by rw [Function.update_of_ne (Ne.symm h0)]; exact F.p0,
    by rw [Function.update_of_ne (Ne.symm h1)]; exact F.p1,
    by rw [Function.update_of_ne (Ne.symm h2)]; exact F.p2,
    by rw [Function.update_of_ne (Ne.symm h3)]; exact F.p3,
    by rw [Function.update_of_ne (Ne.symm h4)]; exact F.p4,
    by rw [Function.update_of_ne (Ne.symm h5)]; exact F.p5,
    by rw [Function.update_of_ne (Ne.symm h14)]; exact F.p14,
    by rw [Function.update_of_ne (Ne.symm h18)]; exact F.p18,
    by rw [Function.update_of_ne (Ne.symm h19)]; exact F.p19, F.r0, F.r1, F.im_in, F.M_in⟩

theorem Frame.upd_r {c : ℕ} {I : ArcInput n m} {r : ℕ → ℝ} {p : ℕ → ℤ} {M : ℤ → ℝ} {im : ℤ → ℤ}
    (F : Frame c I r p M im) (d : ℕ) (v : ℝ) (hd : d ≠ 0 ∧ d ≠ 1) :
    Frame c I (Function.update r d v) p M im :=
  ⟨F.p0, F.p1, F.p2, F.p3, F.p4, F.p5, F.p14, F.p18, F.p19,
    by rw [Function.update_of_ne (Ne.symm hd.1)]; exact F.r0,
    by rw [Function.update_of_ne (Ne.symm hd.2)]; exact F.r1, F.im_in, F.M_in⟩

theorem Frame.upd_im {c : ℕ} {I : ArcInput n m} {r : ℕ → ℝ} {p : ℕ → ℤ} {M : ℤ → ℝ} {im : ℤ → ℤ}
    (F : Frame c I r p M im) (a v : ℤ) (ha : a < 0) :
    Frame c I r p M (Function.update im a v) :=
  ⟨F.p0, F.p1, F.p2, F.p3, F.p4, F.p5, F.p14, F.p18, F.p19, F.r0, F.r1,
    fun b hb => by rw [Function.update_of_ne (by omega)]; exact F.im_in b hb, F.M_in⟩

theorem Frame.upd_M {c : ℕ} {I : ArcInput n m} {r : ℕ → ℝ} {p : ℕ → ℤ} {M : ℤ → ℝ} {im : ℤ → ℤ}
    (F : Frame c I r p M im) (a : ℤ) (v : ℝ) (ha : a < 0) :
    Frame c I r p (Function.update M a v) im :=
  ⟨F.p0, F.p1, F.p2, F.p3, F.p4, F.p5, F.p14, F.p18, F.p19, F.r0, F.r1, F.im_in,
    fun b hb => by rw [Function.update_of_ne (by omega)]; exact F.M_in b hb⟩

theorem cell_order (I : ArcInput n m) (k : Fin m) (j : Fin n) :
    inputIntegerCell I ((k : ℤ) * n + n * n + 3 + j) = ((I.order k j : ℕ) : ℤ) := by
  have hk := k.isLt
  have hj := j.isLt
  have hn : 0 < n := by omega
  have e1 : ((k : ℤ) * n + n * n + 3 + j - 3).toNat = n * n + (k * n + j) := by
    have : (k : ℤ) * n + n * n + 3 + j - 3 = ((n * n + (k * n + j) : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have hlt : k * n + j < m * n := by nlinarith
  have hdiv : (k * n + j) / n = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, zero_add]
  have hmod : (k * n + j) % n = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hpos : (0 : ℤ) ≤ (k : ℤ) * n + n * n := by positivity
  unfold inputIntegerCell
  simp only [e1]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    dif_neg (by omega)]
  simp only [Nat.add_sub_cancel_left, hdiv, hmod]
  rw [dif_pos hlt, dif_pos ⟨hk, hj⟩]

theorem cell_graph (I : ArcInput n m) (i j : Fin n) :
    inputIntegerCell I ((i : ℤ) * n + j + 3) = if I.graph i j then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hn : 0 < n := by omega
  have e1 : ((i : ℤ) * n + j + 3 - 3).toNat = i * n + j := by
    have : (i : ℤ) * n + j + 3 - 3 = ((i * n + j : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have hlt : i * n + j < n * n := by nlinarith
  have hdiv : (i * n + j) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, zero_add]
  have hmod : (i * n + j) % n = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hpos : (0 : ℤ) ≤ (i : ℤ) * n + j := by positivity
  unfold inputIntegerCell
  simp only [e1]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos hlt]
  simp only [hdiv, hmod]
  rw [dif_pos ⟨hi, hj⟩]

theorem cell_weight (I : ArcInput n m) (k : Fin m) :
    inputRealCell I (k : ℤ) = I.weight k := by
  unfold inputRealCell
  rw [if_neg (by omega)]
  simp only [Int.toNat_natCast]
  rw [dif_pos k.isLt]

theorem cell_basis (I : ArcInput n m) (k : Fin m) (j : Fin n) :
    inputRealCell I ((k : ℤ) * n + m + j) = I.basis k j := by
  have hk := k.isLt
  have hj := j.isLt
  have hn : 0 < n := by omega
  have e1 : ((k : ℤ) * n + m + j).toNat = m + (k * n + j) := by
    have : (k : ℤ) * n + m + j = ((m + (k * n + j) : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have hlt : k * n + j < m * n := by nlinarith
  have hdiv : (k * n + j) / n = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, zero_add]
  have hmod : (k * n + j) % n = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hpos : (0 : ℤ) ≤ (k : ℤ) * n + m + j := by positivity
  unfold inputRealCell
  rw [if_neg (by omega)]
  simp only [e1]
  rw [dif_neg (by omega)]
  simp only [Nat.add_sub_cancel_left, hdiv, hmod]
  rw [dif_pos hlt, dif_pos ⟨hk, hj⟩]

/-! ### Block A: initialisation (pc 0 → 13). -/

theorem blockA (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (G : OracleState n → Prop)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ), Frame c I r p (inputRealCell I) (inputIntegerCell I) →
      p 7 = 0 → p 11 = 0 →
      RP c f (st 13 r p (inputRealCell I) (inputIntegerCell I) (fun _ => ∅) 0 13) G) :
    RP c f (st 0 (fun _ => 0) (fun _ => 0) (inputRealCell I) (inputIntegerCell I) (fun _ => ∅) 0 0) G := by
  iterate 13 (refine RP.step ?_; simp only [S0, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12,
    Function.update_apply, ↓reduceIte, Nat.reduceEqDiff])
  refine K _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩ ?_ ?_ <;>
    simp [inputIntegerCell]

/-! ### Block B: inverse table of σ₀ (pc 13 → 23). -/

/-- Inverse table: every vertex `i` below `j` is stored at INV address `-1 - σ i`. -/
def InvTab (σ : Equiv.Perm (Fin n)) (im : ℤ → ℤ) (j : ℕ) : Prop :=
  ∀ i : Fin n, (i : ℕ) < j → im (-1 - ((σ i : ℕ) : ℤ)) = (i : ℕ)

theorem InvTab.step (σ : Equiv.Perm (Fin n)) (im : ℤ → ℤ) (j : Fin n) (h : InvTab σ im j) :
    InvTab σ (Function.update im (-1 - ((σ j : ℕ) : ℤ)) (j : ℕ)) ((j : ℕ) + 1) := by
  intro i hi
  by_cases hij : i = j
  · subst hij; simp
  · have hne : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have hσ : ((σ i : ℕ) : ℤ) ≠ ((σ j : ℕ) : ℤ) := by
      intro e
      exact hij (σ.injective (Fin.ext (by exact_mod_cast e)))
    rw [Function.update_of_ne (by omega)]
    exact h i (by omega)

theorem loopB (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (hm : 0 < m)
    (G : OracleState n → Prop)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (im : ℤ → ℤ) (w : ℕ), Frame c I r p (inputRealCell I) im →
      InvTab (I.order ⟨0, hm⟩) im n → p 11 = 0 → w = 14 + 10 * n →
      RP c f (st 23 r p (inputRealCell I) im (fun _ => ∅) 0 w) G) :
    ∀ (d j : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (im : ℤ → ℤ) (w : ℕ), j + d = n →
      Frame c I r p (inputRealCell I) im → InvTab (I.order ⟨0, hm⟩) im j → p 7 = j →
      p 11 = 0 → w = 13 + 10 * j →
      RP c f (st 13 r p (inputRealCell I) im (fun _ => ∅) 0 w) G := by
  intro d
  induction d with
  | zero =>
    intro j r p im w hjd F hinv hp7 hp11 hw
    simp only [Nat.add_zero] at hjd
    subst hjd
    refine RP.step ?_
    rw [S13, if_pos (by rw [F.p0, hp7])]
    exact K r p im _ F hinv hp11 (by omega)
  | succ d ih =>
    intro j r p im w hjd F hinv hp7 hp11 hw
    have hj : j < n := by omega
    refine RP.step ?_
    rw [S13, if_neg (by rw [F.p0, hp7]; exact_mod_cast (Nat.not_le.mpr hj))]
    have hcell : im (↑n * ↑n + 3 + ↑j) = ((I.order ⟨0, hm⟩ ⟨j, hj⟩ : ℕ) : ℤ) := by
      rw [F.im_in _ (by positivity)]; simpa using cell_order I ⟨0, hm⟩ ⟨j, hj⟩
    iterate 9 (refine RP.step ?_; simp only [S14, S15, S16, S17, S18, S19, S20, S21, S22,
      Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p0, F.p14, F.p18, F.p19, F.p4, hp7, hp11,
      zero_mul, zero_add, hcell, le_refl])
    refine ih (j + 1) _ _ _ _ (by omega)
      ((((((((F.upd_im _ _ (by omega)).upd_p 8 _ (by decide)).upd_p 8 _ (by decide)).upd_p 8 _
        (by decide)).upd_p 8 _ (by decide)).upd_p 10 _ (by decide)).upd_p 9 _ (by decide)).upd_p 7 _
        (by decide))
      (InvTab.step _ im ⟨j, hj⟩ hinv) (by simp) (by simp [hp11]) (by omega)

/-! ### Block C: descendant set R(p) into bank 0 (pc 23 → 51). -/

/-- Real indicator of a proposition. -/
noncomputable def ind (P : Prop) : ℝ := by classical exact if P then 1 else 0

theorem ind_of {P : Prop} (h : P) : ind P = 1 := by simp [ind, h]

theorem ind_of_not {P : Prop} (h : ¬ P) : ind P = 0 := by simp [ind, h]

theorem ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by rw [propext h]

/-- Flag of the R-scan inner loop after inspecting parents `i' < i`. -/
def flagC (I : ArcInput n m) (b : Finset (Fin n)) (j : Fin n) (i : ℕ) : Prop :=
  j = I.point ∨ ∃ i' : Fin n, (i' : ℕ) < i ∧ i' ∈ b ∧ I.graph i' j = true

theorem flagC_zero (I : ArcInput n m) (b : Finset (Fin n)) (j : Fin n) :
    flagC I b j 0 ↔ j = I.point := by
  simp [flagC]

theorem flagC_succ (I : ArcInput n m) (b : Finset (Fin n)) (j : Fin n) (i : ℕ) (hi : i < n) :
    flagC I b j (i + 1) ↔ flagC I b j i ∨ ((⟨i, hi⟩ : Fin n) ∈ b ∧ I.graph ⟨i, hi⟩ j = true) := by
  unfold flagC
  constructor
  · rintro (h | ⟨i', hi', hb, hg⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | h
      · exact Or.inl (Or.inr ⟨i', h, hb, hg⟩)
      · right
        have : i' = ⟨i, hi⟩ := Fin.ext h
        subst this; exact ⟨hb, hg⟩
  · rintro ((h | ⟨i', hi', hb, hg⟩) | ⟨hb, hg⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i', by omega, hb, hg⟩
    · exact Or.inr ⟨⟨i, hi⟩, by simp, hb, hg⟩

theorem h10r : ¬ ((1 : ℝ) ≤ 0) := by norm_num
theorem h10z : ¬ ((1 : ℤ) ≤ 0) := by norm_num
theorem h1ne0 : ((1 : ℝ) = 0) = False := by norm_num

theorem loopCi (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (t : ℤ) (j : Fin n) (Wi : ℕ) (G : OracleState n → Prop)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ), Frame c I r p M im → p 6 = t → p 7 = (j : ℕ) →
      r 11 = ind (flagC I (bm 0) j n) → w ≤ Wi + 1 → RP c f (st 47 r p M im bm 0 w) G) :
    ∀ (d i : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ), i + d = n → Frame c I r p M im → p 6 = t →
      p 7 = (j : ℕ) → p 20 = i → r 11 = ind (flagC I (bm 0) j i) → w + 11 * d ≤ Wi →
      RP c f (st 36 r p M im bm 0 w) G := by
  intro d
  induction d with
  | zero =>
    intro i r p w hid F hp6 hp7 hp20 hr11 hw
    simp only [Nat.add_zero] at hid
    subst hid
    refine RP.step ?_
    rw [S36, if_pos (by rw [F.p0, hp20])]
    exact K r p _ F hp6 hp7 hr11 (by omega)
  | succ d ih =>
    intro i r p w hid F hp6 hp7 hp20 hr11 hw
    have hi : i < n := by omega
    refine RP.step ?_
    rw [S36, if_neg (by rw [F.p0, hp20]; exact_mod_cast (Nat.not_le.mpr hi))]
    refine RP.step ?_
    rw [S37 c f _ _ _ _ _ _ _ ⟨i, hi⟩ (by simpa using hp20)]
    have hcell : im (↑i * ↑n + ↑↑j + 3) = if I.graph ⟨i, hi⟩ j then 1 else 0 := by
      rw [F.im_in _ (by positivity)]; exact cell_graph I ⟨i, hi⟩ j
    by_cases hmem : (⟨i, hi⟩ : Fin n) ∈ bm 0
    · by_cases hg : I.graph ⟨i, hi⟩ j = true
      · iterate 9 (refine RP.step ?_; simp only [S38, S39, S40, S41, S42, S43, S44, S45, S46,
          Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p0, F.p4, F.p19, hp7, hp20, hmem,
          hcell, hg, le_refl, h10r, h10z])
        refine ih (i + 1) _ _ _ (by omega)
          (((((((F.upd_r 6 _ ⟨by decide, by decide⟩).upd_r 11 _ ⟨by decide, by decide⟩).upd_p 8 _
            (by decide)).upd_p 8 _ (by decide)).upd_p 8 _ (by decide)).upd_p 10 _ (by decide)).upd_p
            20 _ (by decide))
          (by simp [hp6]) (by simp [hp7]) (by simp [hp20]) ?_ (by omega)
        simp only [Function.update_apply, ↓reduceIte]
        rw [ind_of ((flagC_succ I (bm 0) j i hi).mpr (Or.inr ⟨hmem, hg⟩))]
      · iterate 8 (refine RP.step ?_; simp only [S38, S39, S40, S41, S42, S43, S44, S45, S46,
          Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p0, F.p4, F.p19, hp7, hp20, hmem,
          hcell, hg, le_refl, h10r, h10z, Bool.false_eq_true])
        refine ih (i + 1) _ _ _ (by omega)
          ((((((F.upd_r 6 _ ⟨by decide, by decide⟩).upd_p 8 _
            (by decide)).upd_p 8 _ (by decide)).upd_p 8 _ (by decide)).upd_p 10 _ (by decide)).upd_p
            20 _ (by decide))
          (by simp [hp6]) (by simp [hp7]) (by simp [hp20]) ?_ (by omega)
        simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]
        rw [hr11]
        exact ind_congr (by rw [flagC_succ I (bm 0) j i hi]; simp [hg])
    · iterate 3 (refine RP.step ?_; simp only [S38, S39, S40, S41, S42, S43, S44, S45, S46,
        Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p0, F.p4, F.p19, hp7, hp20, hmem,
        le_refl, h10r, h10z])
      refine ih (i + 1) _ _ _ (by omega)
        ((F.upd_r 6 _ ⟨by decide, by decide⟩).upd_p 20 _ (by decide))
        (by simp [hp6]) (by simp [hp7]) (by simp [hp20]) ?_ (by omega)
      simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]
      rw [hr11]
      exact ind_congr (by rw [flagC_succ I (bm 0) j i hi]; simp [hmem])

/-- Segment 29 → 36: the flag starts as `[j = p]`, the inner index at 0. -/
theorem segC29 (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (t : ℤ) (j : Fin n) (G : OracleState n → Prop)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ) (F : Frame c I r p M im) (hp6 : p 6 = t)
    (hp7 : p 7 = (j : ℕ))
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (w' : ℕ), Frame c I r p M im → p 6 = t → p 7 = (j : ℕ) →
      p 20 = 0 → r 11 = ind (j = I.point) → w' ≤ w + 5 → RP c f (st 36 r p M im bm 0 w') G) :
    RP c f (st 29 r p M im bm 0 w) G := by
  rcases lt_trichotomy (j : ℕ) (I.point : ℕ) with h | h | h
  · have hle : ((j : ℕ) : ℤ) ≤ ((I.point : ℕ) : ℤ) := by exact_mod_cast h.le
    have hnle : ¬ ((I.point : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast Nat.not_le.mpr h
    have hne : j ≠ I.point := fun e => by rw [e] at h; exact lt_irrefl _ h
    iterate 5 (refine RP.step ?_; simp only [S29, S30, S31, S32, S33, S34, S35,
      Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p2, F.p4, hp7, hle, hnle, le_refl])
    refine K _ _ _ ((F.upd_r 11 _ ⟨by decide, by decide⟩).upd_p 20 _ (by decide))
      (by simp [hp6]) (by simp [hp7]) (by simp) ?_ (by omega)
    simp only [Function.update_apply, ↓reduceIte]
    rw [ind_of_not hne]
  · have hj : j = I.point := Fin.ext h
    iterate 5 (refine RP.step ?_; simp only [S29, S30, S31, S32, S33, S34, S35,
      Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p2, F.p4, hp7, h, le_refl])
    refine K _ _ _ (((F.upd_r 11 _ ⟨by decide, by decide⟩).upd_r 11 _ ⟨by decide, by decide⟩).upd_p
      20 _ (by decide)) (by simp [hp6]) (by simp [hp7]) (by simp) ?_ (by omega)
    simp only [Function.update_apply, ↓reduceIte]
    rw [ind_of hj]
  · have hnle : ¬ ((j : ℕ) : ℤ) ≤ ((I.point : ℕ) : ℤ) := by exact_mod_cast Nat.not_le.mpr h
    have hne : j ≠ I.point := fun e => by rw [e] at h; exact lt_irrefl _ h
    iterate 4 (refine RP.step ?_; simp only [S29, S30, S31, S32, S33, S34, S35,
      Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p2, F.p4, hp7, hnle, le_refl])
    refine K _ _ _ ((F.upd_r 11 _ ⟨by decide, by decide⟩).upd_p 20 _ (by decide))
      (by simp [hp6]) (by simp [hp7]) (by simp) ?_ (by omega)
    simp only [Function.update_apply, ↓reduceIte]
    rw [ind_of_not hne]

/-- R-members at σ-positions above `t`. -/
noncomputable def bankR (I : ArcInput n m) (σ : Equiv.Perm (Fin n)) (t : ℤ) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun j => t < ((σ j : ℕ) : ℤ) ∧ j ∈ R (inputArcs I) I.point)

theorem mem_bankR (I : ArcInput n m) (σ : Equiv.Perm (Fin n)) (t : ℤ) (x : Fin n) :
    x ∈ bankR I σ t ↔ t < ((σ x : ℕ) : ℤ) ∧ x ∈ R (inputArcs I) I.point := by
  unfold bankR; simp

theorem bankR_neg1 (I : ArcInput n m) (σ : Equiv.Perm (Fin n)) :
    bankR I σ (-1) = R (inputArcs I) I.point := by
  ext x; rw [mem_bankR]; constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

theorem bankR_top (I : ArcInput n m) (σ : Equiv.Perm (Fin n)) :
    bankR I σ ((n : ℤ) - 1) = ∅ := by
  ext x; rw [mem_bankR]; simp only [Finset.notMem_empty, iff_false, not_and]
  intro h; have := (σ x).isLt; omega

theorem bankR_step (I : ArcInput n m) (σ : Equiv.Perm (Fin n)) (j : Fin n) (d : ℕ)
    (hj : ((σ j : Fin n) : ℕ) = d) :
    bankR I σ ((d : ℤ) - 1)
      = if j ∈ R (inputArcs I) I.point then insert j (bankR I σ d) else bankR I σ d := by
  have key : ∀ x : Fin n, ((d : ℤ) - 1 < ((σ x : ℕ) : ℤ)) ↔ ((d : ℤ) < ((σ x : ℕ) : ℤ) ∨ x = j) := by
    intro x
    constructor
    · intro h
      rcases lt_or_eq_of_le (show (d : ℤ) ≤ ((σ x : ℕ) : ℤ) by omega) with h' | h'
      · exact Or.inl h'
      · right; apply σ.injective; apply Fin.ext; omega
    · rintro (h | rfl) <;> omega
  ext x
  split_ifs with hR
  · rw [Finset.mem_insert, mem_bankR, mem_bankR, key]
    constructor
    · rintro ⟨h | rfl, hx⟩
      · exact Or.inr ⟨h, hx⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨h, hx⟩)
      · exact ⟨Or.inr rfl, hR⟩
      · exact ⟨Or.inl h, hx⟩
  · rw [mem_bankR, mem_bankR, key]
    constructor
    · rintro ⟨h | rfl, hx⟩
      · exact ⟨h, hx⟩
      · exact absurd hx hR
    · rintro ⟨h, hx⟩; exact ⟨Or.inl h, hx⟩

theorem flag_iff (I : ArcInput n m) (σ : Equiv.Perm (Fin n)) (hcons : Consistent (inputArcs I) σ)
    (j : Fin n) (d : ℕ) (hj : ((σ j : Fin n) : ℕ) = d) :
    flagC I (bankR I σ d) j n ↔ j ∈ R (inputArcs I) I.point := by
  unfold flagC
  constructor
  · rintro (h | ⟨i', -, hb, hg⟩)
    · subst h
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.ReflTransGen.refl
    · rw [mem_bankR] at hb
      have h2 := hb.2
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at h2 ⊢
      exact Relation.ReflTransGen.tail h2 hg
  · intro h
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨i', hpi, hA⟩
    · exact Or.inl h
    · right
      refine ⟨i', i'.isLt, ?_, hA⟩
      rw [mem_bankR]
      refine ⟨?_, by simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]; exact hpi⟩
      have h2 : ((σ j : Fin n) : ℕ) < ((σ i' : Fin n) : ℕ) := hcons i' j hA
      omega

theorem loopCo (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (hm : 0 < m)
    (hcons : Consistent (inputArcs I) (I.order ⟨0, hm⟩)) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (hinv : InvTab (I.order ⟨0, hm⟩) im n) (WC : ℕ) (G : OracleState n → Prop)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (bm : ℤ → Finset (Fin n)) (w : ℕ), Frame c I r p M im →
      bm 0 = R (inputArcs I) I.point → w ≤ WC + 2 → RP c f (st 51 r p M im bm 0 w) G) :
    ∀ (d : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (bm : ℤ → Finset (Fin n)) (w : ℕ), d ≤ n →
      Frame c I r p M im → p 6 = (d : ℤ) - 1 →
      bm 0 = bankR I (I.order ⟨0, hm⟩) ((d : ℤ) - 1) → w + d * (11 * n + 13) ≤ WC →
      RP c f (st 25 r p M im bm 0 w) G := by
  intro d
  induction d with
  | zero =>
    intro r p bm w _ F hp6 hb hw
    refine RP.step ?_
    rw [S25, if_neg (by rw [F.p4, hp6]; norm_num)]
    refine RP.step ?_
    rw [S26, if_pos le_rfl]
    refine K r p bm _ F ?_ (by omega)
    rw [hb]; simpa using bankR_neg1 I (I.order ⟨0, hm⟩)
  | succ d ih =>
    intro r p bm w hd F hp6 hb hw
    have hdn : d < n := by omega
    have hp6' : p 6 = d := by rw [hp6]; push_cast; ring
    obtain ⟨j, hjdef⟩ : ∃ j, j = (I.order ⟨0, hm⟩).symm ⟨d, hdn⟩ := ⟨_, rfl⟩
    have hσj : (((I.order ⟨0, hm⟩) j : Fin n) : ℕ) = d := by rw [hjdef]; simp
    have hinvc : im (-1 - ↑d) = ((j : ℕ) : ℤ) := by
      have := hinv j j.isLt; rw [hσj] at this; exact this
    have hb' : bm 0 = bankR I (I.order ⟨0, hm⟩) d := by rw [hb]; congr 1; push_cast; ring
    refine RP.step ?_
    rw [S25, if_pos (by rw [F.p4, hp6']; positivity)]
    iterate 2 (refine RP.step ?_; simp only [S27, S28, Function.update_apply, ↓reduceIte,
      Nat.reduceEqDiff, F.p18, hp6', hinvc])
    refine segC29 c f I M im bm d j G _ _ _ ((F.upd_p 9 _ (by decide)).upd_p 7 _ (by decide))
      (by simp [hp6']) (by simp) ?_
    intro r1 p1 w1 F1 h6 h7 h20 h11 hw1
    refine loopCi c f I M im bm d j (w1 + 11 * n) G ?_ n 0 r1 p1 w1 (by omega) F1 h6 h7
      (by simpa using h20) (by rw [h11]; exact ind_congr (flagC_zero I (bm 0) j).symm) le_rfl
    intro r2 p2 w2 F2 h6' h7' h11' hw2
    rw [hb', flag_iff I _ hcons j d hσj] at h11'
    by_cases hR : j ∈ R (inputArcs I) I.point
    · rw [ind_of hR] at h11'
      refine RP.step ?_
      rw [S47, h11', if_neg h10r]
      refine RP.step ?_
      rw [S48 c f _ _ _ _ _ _ _ j h7']
      iterate 2 (refine RP.step ?_; simp only [S49, S50, Function.update_apply, ↓reduceIte,
        Nat.reduceEqDiff, F2.p4, F2.r1, h1ne0, le_refl])
      refine ih _ _ _ _ (by omega) (F2.upd_p 6 _ (by decide)) (by simp [h6']) ?_ ?_
      · simp only [Function.update_self]
        rw [bankR_step I _ j d hσj, if_pos hR, hb']
      · rw [Nat.succ_mul] at hw; omega
    · rw [ind_of_not hR] at h11'
      refine RP.step ?_
      rw [S47, h11', if_pos le_rfl]
      iterate 2 (refine RP.step ?_; simp only [S49, S50, Function.update_apply, ↓reduceIte,
        Nat.reduceEqDiff, le_refl])
      refine ih _ _ _ _ (by omega) (F2.upd_p 6 _ (by decide)) (by simp [h6']) ?_ ?_
      · rw [bankR_step I _ j d hσj, if_neg hR, hb']
      · rw [Nat.succ_mul] at hw; omega

/-- Block C from pc 23 (fresh bitmaps) to pc 51 with bank 0 = R(p). -/
theorem blockC (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (hm : 0 < m)
    (hcons : Consistent (inputArcs I) (I.order ⟨0, hm⟩)) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (hinv : InvTab (I.order ⟨0, hm⟩) im n) (G : OracleState n → Prop)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ) (F : Frame c I r p M im)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (bm : ℤ → Finset (Fin n)) (w' : ℕ), Frame c I r p M im →
      bm 0 = R (inputArcs I) I.point → w' ≤ w + 4 + n * (11 * n + 13) →
      RP c f (st 51 r p M im bm 0 w') G) :
    RP c f (st 23 r p M im (fun _ => ∅) 0 w) G := by
  iterate 2 (refine RP.step ?_; simp only [S23, S24, Function.update_apply, ↓reduceIte,
    Nat.reduceEqDiff])
  refine loopCo c f I hm hcons M im hinv (w + 2 + n * (11 * n + 13)) G
    (fun r p bm w' F h0 hw => K r p bm w' F h0 (by omega)) n _ _ _ _ le_rfl
    ((F.upd_p 6 _ (by decide)).upd_p 6 _ (by decide)) (by simp [F.p0]) ?_ le_rfl
  rw [bankR_top]

/-! ### Block D: f(R), f(R - p), upper (pc 51 → 56). -/

theorem point_mem_R (I : ArcInput n m) : I.point ∈ R (inputArcs I) I.point := by
  simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Relation.ReflTransGen.refl

theorem blockD (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (G : OracleState n → Prop) (r : ℕ → ℝ) (p : ℕ → ℤ) (q w : ℕ)
    (F : Frame c I r p M im) (hb : bm 0 = R (inputArcs I) I.point)
    (K : ∀ (r' : ℕ → ℝ) (bm' : ℤ → Finset (Fin n)) (q' w' : ℕ), Frame c I r' p M im →
      bm' 0 = R (inputArcs I) I.point → r' 2 = (f (R (inputArcs I) I.point) : ℝ) →
      r' 4 = (upper f (inputArcs I) I.point : ℝ) → q' = q + 2 → w' = w + 5 →
      RP c f (st 56 r' p M im bm' q' w') G) :
    RP c f (st 51 r p M im bm q w) G := by
  refine RP.step ?_; rw [S51]
  refine RP.step ?_; rw [S52 c f _ _ _ _ _ _ _ I.point F.p2]
  refine RP.step ?_; rw [S53]
  refine RP.step ?_; rw [S54 c f _ _ _ _ _ _ _ I.point F.p2]
  refine RP.step ?_; rw [S55]
  refine K _ _ _ _ (((F.upd_r 2 _ ⟨by decide, by decide⟩).upd_r 3 _ ⟨by decide, by decide⟩).upd_r 4 _
    ⟨by decide, by decide⟩) ?_ ?_ ?_ rfl rfl
  · simp only [F.p4, Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.r0, F.r1, h1ne0, hb]
    exact Finset.insert_erase (point_mem_R I)
  · simp only [F.p4, Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, hb]
  · simp only [F.p4, Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.r0, F.r1, h1ne0, hb, upper]
    push_cast; ring

/-! ### Block E: the weighted vector y into W (pc 56 → 75). -/

/-- Partial weighted vector over the bases `k' < k`. -/
noncomputable def ysum (I : ArcInput n m) (k : ℕ) (j : Fin n) : ℝ :=
  ∑ k' : Fin m, if (k' : ℕ) < k then I.basis k' j * I.weight k' else 0

theorem ysum_zero (I : ArcInput n m) (j : Fin n) : ysum I 0 j = 0 := by simp [ysum]

theorem ysum_succ (I : ArcInput n m) (k : Fin m) (j : Fin n) :
    ysum I ((k : ℕ) + 1) j = ysum I k j + I.basis k j * I.weight k := by
  unfold ysum
  have h : ∀ k' : Fin m, (if (k' : ℕ) < k + 1 then I.basis k' j * I.weight k' else 0)
      = (if (k' : ℕ) < k then I.basis k' j * I.weight k' else 0)
        + (if k' = k then I.basis k' j * I.weight k' else 0) := by
    intro k'
    by_cases h1 : (k' : ℕ) < k
    · have : k' ≠ k := fun e => by rw [e] at h1; exact lt_irrefl _ h1
      simp [h1, this, show (k' : ℕ) < k + 1 by omega]
    · by_cases h2 : k' = k
      · subst h2; simp
      · have : ¬ (k' : ℕ) < k + 1 := fun h3 => h2 (Fin.ext (by omega))
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun k' _ => h k'), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem loopEi (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (k : Fin m) (q We : ℕ) (v2 v4 : ℝ) (G : OracleState n → Prop)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (w : ℕ), Frame c I r p M im → p 11 = (k : ℕ) →
      (∀ j : Fin n, M (-1 - ((j : ℕ) : ℤ)) = ysum I ((k : ℕ) + 1) j) → w ≤ We + 1 →
      r 2 = v2 → r 4 = v4 → RP c f (st 73 r p M im bm q w) G) :
    ∀ (d j : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (w : ℕ), j + d = n → Frame c I r p M im →
      p 7 = j → p 11 = (k : ℕ) → r 10 = I.weight k →
      (∀ j' : Fin n, M (-1 - ((j' : ℕ) : ℤ))
        = if (j' : ℕ) < j then ysum I ((k : ℕ) + 1) j' else ysum I k j') →
      w + 12 * d ≤ We → r 2 = v2 → r 4 = v4 → RP c f (st 61 r p M im bm q w) G := by
  intro d
  induction d with
  | zero =>
    intro j r p M w hjd F hp7 hp11 hr10 hM hw hr2 hr4
    simp only [Nat.add_zero] at hjd
    subst hjd
    refine RP.step ?_
    rw [S61, if_pos (by rw [F.p0, hp7])]
    refine K r p M _ F hp11 (fun j' => by rw [hM j', if_pos j'.isLt]) (by omega) hr2 hr4
  | succ d ih =>
    intro j r p M w hjd F hp7 hp11 hr10 hM hw hr2 hr4
    have hj : j < n := by omega
    refine RP.step ?_
    rw [S61, if_neg (by rw [F.p0, hp7]; exact_mod_cast (Nat.not_le.mpr hj))]
    have hcellb : M (↑↑k * ↑n + ↑m + ↑j) = I.basis k ⟨j, hj⟩ := by
      rw [F.M_in _ (by positivity)]; exact cell_basis I k ⟨j, hj⟩
    have hMj : M (-1 - ↑j) = ysum I k ⟨j, hj⟩ := by
      have := hM ⟨j, hj⟩; rw [if_neg (lt_irrefl _)] at this; exact this
    iterate 11 (refine RP.step ?_; simp only [S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, S72,
      Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p0, F.p1, F.p18, F.p4, hp7, hp11,
      hcellb, hr10, hMj, le_refl])
    refine ih (j + 1) _ _ _ _ (by omega)
      (((((((((F.upd_M _ _ (by omega)).upd_p 8 _ (by decide)).upd_p 8 _ (by decide)).upd_p 8 _
        (by decide)).upd_r 6 _ ⟨by decide, by decide⟩).upd_r 6 _ ⟨by decide, by decide⟩).upd_p 9 _
        (by decide)).upd_r 7 _ ⟨by decide, by decide⟩).upd_r 7 _ ⟨by decide, by decide⟩ |>.upd_p 7 _
        (by decide))
      (by simp) (by simp [hp11]) (by simp [hr10]) ?_ (by omega) (by simp [hr2]) (by simp [hr4])
    intro j'
    by_cases hjj : (j' : ℕ) = j
    · have hj'e : j' = ⟨j, hj⟩ := Fin.ext hjj
      subst hj'e
      simp only [Function.update_self]
      rw [if_pos (by simp), ysum_succ]
    · rw [Function.update_of_ne (by omega), hM j']
      have : (j' : ℕ) < j + 1 ↔ (j' : ℕ) < j := by omega
      simp only [this]

theorem loopEo (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q : ℕ) (v2 v4 : ℝ) (WE : ℕ) (G : OracleState n → Prop)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (w : ℕ), Frame c I r p M im →
      (∀ j : Fin n, M (-1 - ((j : ℕ) : ℤ)) = ysum I m j) → r 2 = v2 → r 4 = v4 → w ≤ WE + 1 →
      RP c f (st 75 r p M im bm q w) G) :
    ∀ (d k : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (w : ℕ), k + d = m → Frame c I r p M im →
      p 11 = k → (∀ j : Fin n, M (-1 - ((j : ℕ) : ℤ)) = ysum I k j) → r 2 = v2 → r 4 = v4 →
      w + d * (12 * n + 7) ≤ WE → RP c f (st 57 r p M im bm q w) G := by
  intro d
  induction d with
  | zero =>
    intro k r p M w hkd F hp11 hM hr2 hr4 hw
    simp only [Nat.add_zero] at hkd
    subst hkd
    refine RP.step ?_
    rw [S57, if_pos (by rw [F.p1, hp11])]
    exact K r p M _ F hM hr2 hr4 (by omega)
  | succ d ih =>
    intro k r p M w hkd F hp11 hM hr2 hr4 hw
    have hk : k < m := by omega
    refine RP.step ?_
    rw [S57, if_neg (by rw [F.p1, hp11]; exact_mod_cast (Nat.not_le.mpr hk))]
    have hcellw : M (k : ℤ) = I.weight ⟨k, hk⟩ := by
      rw [F.M_in _ (by positivity)]; exact cell_weight I ⟨k, hk⟩
    iterate 3 (refine RP.step ?_; simp only [S58, S59, S60, Function.update_apply, ↓reduceIte,
      Nat.reduceEqDiff, hp11, hcellw])
    refine loopEi c f I im bm ⟨k, hk⟩ q (w + 4 + 12 * n) v2 v4 G ?_ n 0 _ _ M _ (by omega)
      (((F.upd_p 8 _ (by decide)).upd_r 10 _ ⟨by decide, by decide⟩).upd_p 7 _ (by decide))
      (by simp) (by simp [hp11]) (by simp) (fun j' => by simp [hM]) (by omega)
      (by simp [hr2]) (by simp [hr4])
    intro r1 p1 M1 w1 F1 h11 hM1 hw1 hr2' hr4'
    iterate 2 (refine RP.step ?_; simp only [S73, S74, Function.update_apply, ↓reduceIte,
      Nat.reduceEqDiff, le_refl])
    refine ih (k + 1) _ _ _ _ (by omega) (F1.upd_p 11 _ (by decide)) (by simp [h11]) hM1 hr2' hr4' ?_
    rw [Nat.succ_mul] at hw; omega

theorem blockE (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q : ℕ) (G : OracleState n → Prop) (r : ℕ → ℝ) (p : ℕ → ℤ)
    (M : ℤ → ℝ) (w : ℕ) (F : Frame c I r p M im) (hM0 : ∀ j : Fin n, M (-1 - ((j : ℕ) : ℤ)) = 0)
    (K : ∀ (r' : ℕ → ℝ) (p' : ℕ → ℤ) (M' : ℤ → ℝ) (w' : ℕ), Frame c I r' p' M' im →
      (∀ j : Fin n, M' (-1 - ((j : ℕ) : ℤ)) = ysum I m j) → r' 2 = r 2 → r' 4 = r 4 →
      w' ≤ w + 2 + m * (12 * n + 7) → RP c f (st 75 r' p' M' im bm q w') G) :
    RP c f (st 56 r p M im bm q w) G := by
  refine RP.step ?_
  rw [S56]
  exact loopEo c f I im bm q (r 2) (r 4) (w + 1 + m * (12 * n + 7)) G
    (fun r' p' M' w' F' hM' h2 h4 hw' => K r' p' M' w' F' hM' h2 h4 (by omega)) m 0 _ _ M _
    (by omega) (F.upd_p 11 _ (by decide)) (by simp) (fun j => by rw [hM0, ysum_zero]) rfl rfl
    (by omega)

/-! ### Block F: k* maximising λ_k (upper - y^k_p) (pc 75 → 100). -/

/-- The gain of basis `k` as the machine computes it. -/
noncomputable def gainF (I : ArcInput n m) (u : ℝ) (k : Fin m) : ℝ :=
  (u - I.basis k I.point) * I.weight k

theorem loopF (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q : ℕ) (u v2 : ℝ) (WF : ℕ) (G : OracleState n → Prop)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ) (ks : Fin m), Frame c I r p M im → p 13 = (ks : ℕ) →
      (∀ k' : Fin m, gainF I u k' ≤ gainF I u ks) → r 2 = v2 → w ≤ WF + 1 →
      RP c f (st 100 r p M im bm q w) G) :
    ∀ (d k : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ) (ks : Fin m), k + d = m → Frame c I r p M im →
      p 11 = k → p 13 = (ks : ℕ) → r 5 = gainF I u ks → r 4 = u → r 2 = v2 →
      (∀ k' : Fin m, (k' : ℕ) < k → gainF I u k' ≤ gainF I u ks) → w + 15 * d ≤ WF →
      RP c f (st 85 r p M im bm q w) G := by
  intro d
  induction d with
  | zero =>
    intro k r p w ks hkd F hp11 hp13 hr5 hr4 hr2 hmax hw
    simp only [Nat.add_zero] at hkd
    subst hkd
    refine RP.step ?_
    rw [S85, if_pos (by rw [F.p1, hp11])]
    exact K r p _ ks F hp13 (fun k' => hmax k' k'.isLt) hr2 (by omega)
  | succ d ih =>
    intro k r p w ks hkd F hp11 hp13 hr5 hr4 hr2 hmax hw
    have hk : k < m := by omega
    refine RP.step ?_
    rw [S85, if_neg (by rw [F.p1, hp11]; exact_mod_cast (Nat.not_le.mpr hk))]
    have hcellw : M (k : ℤ) = I.weight ⟨k, hk⟩ := by
      rw [F.M_in _ (by positivity)]; exact cell_weight I ⟨k, hk⟩
    have hcellb : M (↑k * ↑n + ↑m + ↑↑I.point) = I.basis ⟨k, hk⟩ I.point := by
      rw [F.M_in _ (by positivity)]; exact cell_basis I ⟨k, hk⟩ I.point
    iterate 9 (refine RP.step ?_; simp only [S86, S87, S88, S89, S90, S91, S92, S93, S94,
      Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, hp11, F.p0, F.p1, F.p2, hcellw, hcellb,
      hr4, hr5])
    by_cases hg : gainF I u ⟨k, hk⟩ ≤ gainF I u ks
    · have hle : (u - I.basis ⟨k, hk⟩ I.point) * I.weight ⟨k, hk⟩ - gainF I u ks ≤ 0 := by
        unfold gainF at hg ⊢; linarith
      iterate 3 (refine RP.step ?_; simp only [S95, S98, S99, Function.update_apply, ↓reduceIte,
        Nat.reduceEqDiff, hle, le_refl])
      refine ih (k + 1) _ _ _ ks (by omega)
        (((((((((F.upd_p 8 _ (by decide)).upd_r 10 _ ⟨by decide, by decide⟩).upd_p 8 _
          (by decide)).upd_p 8 _ (by decide)).upd_p 8 _ (by decide)).upd_r 6 _
          ⟨by decide, by decide⟩).upd_r 6 _ ⟨by decide, by decide⟩).upd_r 7 _
          ⟨by decide, by decide⟩).upd_r 6 _ ⟨by decide, by decide⟩ |>.upd_p 11 _ (by decide))
        (by simp [hp11]) (by simp [hp13]) (by simp [hr5]) (by simp [hr4]) (by simp [hr2]) ?_ (by omega)
      intro k' hk'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h | h
      · exact hmax k' h
      · have : k' = ⟨k, hk⟩ := Fin.ext h
        rw [this]; exact hg
    · have hlt : ¬ ((u - I.basis ⟨k, hk⟩ I.point) * I.weight ⟨k, hk⟩ - gainF I u ks ≤ 0) := by
        unfold gainF at hg ⊢; intro h; exact hg (by linarith)
      iterate 5 (refine RP.step ?_; simp only [S95, S96, S97, S98, S99, Function.update_apply,
        ↓reduceIte, Nat.reduceEqDiff, hlt, le_refl, F.r0, add_zero])
      refine ih (k + 1) _ _ _ ⟨k, hk⟩ (by omega)
        ((((((((((F.upd_p 8 _ (by decide)).upd_r 10 _ ⟨by decide, by decide⟩).upd_p 8 _
          (by decide)).upd_p 8 _ (by decide)).upd_p 8 _ (by decide)).upd_r 6 _
          ⟨by decide, by decide⟩).upd_r 6 _ ⟨by decide, by decide⟩).upd_r 7 _
          ⟨by decide, by decide⟩).upd_r 6 _ ⟨by decide, by decide⟩).upd_r 5 _ ⟨by decide, by decide⟩
          |>.upd_p 13 _ (by decide) |>.upd_p 11 _ (by decide))
        (by simp [hp11]) (by simp [hp11]) (by simp [gainF]) (by simp [hr4]) (by simp [hr2]) ?_
        (by omega)
      intro k' hk'
      have hg' : gainF I u ks ≤ gainF I u ⟨k, hk⟩ := le_of_lt (not_le.mp hg)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h | h
      · exact le_trans (hmax k' h) hg'
      · have : k' = ⟨k, hk⟩ := Fin.ext h
        rw [this]

theorem blockF (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (hm : 0 < m) (M : ℤ → ℝ)
    (im : ℤ → ℤ) (bm : ℤ → Finset (Fin n)) (q : ℕ) (G : OracleState n → Prop) (r : ℕ → ℝ)
    (p : ℕ → ℤ) (w : ℕ) (F : Frame c I r p M im) (u v2 : ℝ) (hr4 : r 4 = u) (hr2 : r 2 = v2)
    (K : ∀ (r' : ℕ → ℝ) (p' : ℕ → ℤ) (w' : ℕ) (ks : Fin m), Frame c I r' p' M im →
      p' 13 = (ks : ℕ) → (∀ k' : Fin m, gainF I u k' ≤ gainF I u ks) → r' 2 = v2 →
      w' ≤ w + 11 + 15 * m → RP c f (st 100 r' p' M im bm q w') G) :
    RP c f (st 75 r p M im bm q w) G := by
  have hcellw : M 0 = I.weight ⟨0, hm⟩ := by
    rw [F.M_in 0 le_rfl]; simpa using cell_weight I ⟨0, hm⟩
  have hcellb : M (↑m + ↑↑I.point) = I.basis ⟨0, hm⟩ I.point := by
    rw [F.M_in _ (by positivity)]; simpa using cell_basis I ⟨0, hm⟩ I.point
  iterate 10 (refine RP.step ?_; simp only [S75, S76, S77, S78, S79, S80, S81, S82, S83, S84,
    Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p0, F.p1, F.p2, hcellw, hcellb, hr4,
    zero_mul, zero_add])
  refine loopF c f I M im bm q u v2 (w + 10 + 15 * m) G
    (fun r' p' w' ks F' h13 hmax h2 hw' => K r' p' w' ks F' h13 hmax h2 (by omega)) m 0 _ _ _ ⟨0, hm⟩
    (by omega)
    ((((((((((F.upd_p 11 _ (by decide)).upd_p 8 _ (by decide)).upd_p 8 _ (by decide)).upd_p 8 _
      (by decide)).upd_p 8 _ (by decide)).upd_p 13 _ (by decide)).upd_r 10 _
      ⟨by decide, by decide⟩).upd_r 6 _ ⟨by decide, by decide⟩).upd_r 6 _ ⟨by decide, by decide⟩).upd_r 5 _
      ⟨by decide, by decide⟩)
    (by simp) (by simp) (by simp [gainF]) (by simp [hr4]) (by simp [hr2])
    (fun k' hk' => absurd hk' (Nat.not_lt_zero _)) (by omega)

/-! ### Block G: the frontload range (pc 100 → 107). -/

theorem blockG (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (q : ℕ) (ks : Fin m) (G : OracleState n → Prop) (r : ℕ → ℝ)
    (p : ℕ → ℤ) (w : ℕ) (F : Frame c I r p M im) (hp13 : p 13 = (ks : ℕ))
    (K : ∀ (p' : ℕ → ℤ) (k0 e w' : ℕ), Frame c I r p' M im → p' 11 = k0 → p' 12 = (e : ℤ) - 1 →
      ((n ≤ c ∧ k0 = 0 ∧ e = m) ∨ (c < n ∧ k0 = ks ∧ e = (ks : ℕ) + 1)) → w' = w + 4 →
      RP c f (st 107 r p' M im bm q w') G) :
    RP c f (st 100 r p M im bm q w) G := by
  by_cases hnc : n ≤ c
  · have hz : (n : ℤ) ≤ c := by exact_mod_cast hnc
    iterate 4 (refine RP.step ?_; simp only [S100, S104, S105, S106, Function.update_apply,
      ↓reduceIte, Nat.reduceEqDiff, F.p0, F.p3, F.p1, hz])
    exact K _ 0 m _ (((F.upd_p 11 _ (by decide)).upd_p 12 _ (by decide)).upd_p 12 _ (by decide))
      (by simp) (by simp) (Or.inl ⟨hnc, rfl, rfl⟩) (by omega)
  · have hz : ¬ (n : ℤ) ≤ c := by exact_mod_cast hnc
    iterate 4 (refine RP.step ?_; simp only [S100, S101, S102, S103, Function.update_apply,
      ↓reduceIte, Nat.reduceEqDiff, F.p0, F.p3, hz, hp13, le_refl])
    exact K _ ks ((ks : ℕ) + 1) _ ((F.upd_p 11 _ (by decide)).upd_p 12 _ (by decide))
      (by simp) (by simp) (Or.inr ⟨by omega, rfl, rfl⟩) (by omega)

/-! ### Block H1: inverse table of σ_k and bank k+1 := bank 0 (pc 111 → 123). -/

theorem bank_copy_step (B Rs : Finset (Fin n)) (j : Fin n)
    (hB : ∀ i : Fin n, (i : ℕ) < j → (i ∈ B ↔ i ∈ Rs)) :
    ∀ i : Fin n, (i : ℕ) < (j : ℕ) + 1 →
      (i ∈ (if (if j ∈ Rs then (1 : ℝ) else 0) = 0 then B.erase j else insert j B) ↔ i ∈ Rs) := by
  intro i hi
  by_cases hij : i = j
  · subst hij
    by_cases h : i ∈ Rs <;> simp [h]
  · have hlt : (i : ℕ) < j := by
      have : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
      omega
    by_cases h : j ∈ Rs
    · simp [h, Finset.mem_insert, hij, hB i hlt]
    · simp [h, Finset.mem_erase, hij, hB i hlt]

theorem loopH1 (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (M : ℤ → ℝ) (q : ℕ)
    (k : Fin m) (e : ℕ) (v2 : ℝ) (W1 : ℕ) (G : OracleState n → Prop)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (im : ℤ → ℤ) (bm : ℤ → Finset (Fin n)) (w : ℕ),
      Frame c I r p M im → p 11 = (k : ℕ) → p 12 = (e : ℤ) - 1 → p 17 = (k : ℤ) + 1 →
      InvTab (I.order k) im n → bm 0 = R (inputArcs I) I.point →
      bm ((k : ℤ) + 1) = R (inputArcs I) I.point → r 2 = v2 → w ≤ W1 + 1 →
      RP c f (st 123 r p M im bm q w) G) :
    ∀ (d j : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (im : ℤ → ℤ) (bm : ℤ → Finset (Fin n)) (w : ℕ),
      j + d = n → Frame c I r p M im → p 7 = j → p 11 = (k : ℕ) → p 12 = (e : ℤ) - 1 →
      p 17 = (k : ℤ) + 1 → InvTab (I.order k) im j → bm 0 = R (inputArcs I) I.point →
      (∀ i : Fin n, (i : ℕ) < j → (i ∈ bm ((k : ℤ) + 1) ↔ i ∈ R (inputArcs I) I.point)) →
      r 2 = v2 → w + 12 * d ≤ W1 → RP c f (st 111 r p M im bm q w) G := by
  intro d
  induction d with
  | zero =>
    intro j r p im bm w hjd F hp7 hp11 hp12 hp17 hinv hb0 hbk hr2 hw
    simp only [Nat.add_zero] at hjd
    subst hjd
    refine RP.step ?_
    rw [S111, if_pos (by rw [F.p0, hp7])]
    refine K r p im bm _ F hp11 hp12 hp17 hinv hb0 ?_ hr2 (by omega)
    ext i; exact hbk i i.isLt
  | succ d ih =>
    intro j r p im bm w hjd F hp7 hp11 hp12 hp17 hinv hb0 hbk hr2 hw
    have hj : j < n := by omega
    refine RP.step ?_
    rw [S111, if_neg (by rw [F.p0, hp7]; exact_mod_cast (Nat.not_le.mpr hj))]
    have hcell : im (↑↑k * ↑n + ↑n * ↑n + 3 + ↑j) = ((I.order k ⟨j, hj⟩ : ℕ) : ℤ) := by
      rw [F.im_in _ (by positivity)]; exact cell_order I k ⟨j, hj⟩
    iterate 7 (refine RP.step ?_; simp only [S112, S113, S114, S115, S116, S117, S118,
      Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p0, F.p14, F.p18, F.p19, hp7, hp11,
      hcell])
    refine RP.step ?_
    rw [S119 c f _ _ _ _ _ _ _ ⟨j, hj⟩ (by simp [hp7])]
    refine RP.step ?_
    rw [S120 c f _ _ _ _ _ _ _ ⟨j, hj⟩ (by simp [hp7])]
    iterate 2 (refine RP.step ?_; simp only [S121, S122, Function.update_apply, ↓reduceIte,
      Nat.reduceEqDiff, F.p4, hp17, hb0, le_refl])
    have hk0 : ((k : ℕ) : ℤ) + 1 ≠ 0 := by omega
    refine ih (j + 1) _ _ _ _ _ (by omega)
      (((((((((F.upd_im _ _ (by omega)).upd_p 8 _ (by decide)).upd_p 8 _ (by decide)).upd_p 8 _
        (by decide)).upd_p 8 _ (by decide)).upd_p 10 _ (by decide)).upd_p 9 _ (by decide)).upd_r 6 _
        ⟨by decide, by decide⟩).upd_p 7 _ (by decide))
      (by simp [hp7]) (by simp [hp11]) (by simp [hp12]) (by simp [hp17])
      (InvTab.step _ im ⟨j, hj⟩ hinv) (by rw [Function.update_of_ne (Ne.symm hk0)]; exact hb0) ?_
      (by simp [hr2]) (by omega)
    simp only [Function.update_self]
    exact bank_copy_step _ _ ⟨j, hj⟩ hbk

/-! ### Block H2: frontload R(p)ᶜ in σ_k order behind bank k+1, update W (pc 127 → 149). -/

/-- Marginal of `j` behind `B ∪ before σ j` (same body as `LSW79F.marg`). -/
def margM (f : Finset (Fin n) → ℤ) (B : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (j : Fin n) : ℤ :=
  f (insert j (B ∪ before σ j)) - f (B ∪ before σ j)

/-- Bank k+1 after the positions below `t` were added. -/
noncomputable def Bk (Rs : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (t : ℕ) : Finset (Fin n) := by
  classical exact Rs ∪ Finset.univ.filter (fun i => ((σ i : Fin n) : ℕ) < t)

theorem mem_Bk (Rs : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (t : ℕ) (x : Fin n) :
    x ∈ Bk Rs σ t ↔ x ∈ Rs ∨ ((σ x : Fin n) : ℕ) < t := by
  unfold Bk; simp

theorem Bk_zero (Rs : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) : Bk Rs σ 0 = Rs := by
  ext x; simp [mem_Bk]

theorem Bk_eq_before (Rs : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (j : Fin n) (t : ℕ)
    (hj : ((σ j : Fin n) : ℕ) = t) : Bk Rs σ t = Rs ∪ before σ j := by
  ext x
  simp only [mem_Bk, Finset.mem_union, before, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.lt_def, hj]

theorem Bk_succ (Rs : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (j : Fin n) (t : ℕ)
    (hj : ((σ j : Fin n) : ℕ) = t) : Bk Rs σ (t + 1) = insert j (Bk Rs σ t) := by
  have key : ∀ x : Fin n, (((σ x : Fin n) : ℕ) < t + 1) ↔ (((σ x : Fin n) : ℕ) < t ∨ x = j) := by
    intro x; constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact Or.inl h
      · right; apply σ.injective; apply Fin.ext; omega
    · rintro (h | rfl) <;> omega
  ext x
  simp only [mem_Bk, Finset.mem_insert, key]
  tauto

theorem loopH2 (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (im : ℤ → ℤ) (k : Fin m)
    (e : ℕ) (v2 : ℝ) (base : Fin n → ℝ) (Q2 W2 : ℕ) (G : OracleState n → Prop)
    (hinv : InvTab (I.order k) im n)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (bm : ℤ → Finset (Fin n)) (q w : ℕ),
      Frame c I r p M im → p 11 = (k : ℕ) → p 12 = (e : ℤ) - 1 → bm 0 = R (inputArcs I) I.point →
      r 2 = v2 →
      (∀ j : Fin n, j ∉ R (inputArcs I) I.point → M (-1 - ((j : ℕ) : ℤ)) = base j
        + (((margM f (R (inputArcs I) I.point) (I.order k) j : ℤ) : ℝ) - I.basis k j) * I.weight k) →
      q ≤ Q2 → w ≤ W2 + 1 → RP c f (st 149 r p M im bm q w) G) :
    ∀ (d t : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (bm : ℤ → Finset (Fin n)) (q w : ℕ),
      t + d = n → Frame c I r p M im → p 6 = t → p 11 = (k : ℕ) → p 12 = (e : ℤ) - 1 →
      p 17 = (k : ℤ) + 1 → bm 0 = R (inputArcs I) I.point →
      bm ((k : ℤ) + 1) = Bk (R (inputArcs I) I.point) (I.order k) t →
      r 8 = (f (Bk (R (inputArcs I) I.point) (I.order k) t) : ℝ) → r 10 = I.weight k → r 2 = v2 →
      (∀ j : Fin n, j ∉ R (inputArcs I) I.point → M (-1 - ((j : ℕ) : ℤ)) = base j
        + (if (((I.order k) j : Fin n) : ℕ) < t then
            (((margM f (R (inputArcs I) I.point) (I.order k) j : ℤ) : ℝ) - I.basis k j) * I.weight k
          else 0)) →
      q + d ≤ Q2 → w + 21 * d ≤ W2 → RP c f (st 127 r p M im bm q w) G := by
  intro d
  induction d with
  | zero =>
    intro t r p M bm q w htd F hp6 hp11 hp12 hp17 hb0 hbk hr8 hr10 hr2 hW hq hw
    simp only [Nat.add_zero] at htd
    subst htd
    refine RP.step ?_
    rw [S127, if_pos (by rw [F.p0, hp6])]
    refine K r p M bm q _ F hp11 hp12 hb0 hr2 (fun j hj => ?_) (by omega) (by omega)
    rw [hW j hj, if_pos ((I.order k) j).isLt]
  | succ d ih =>
    intro t r p M bm q w htd F hp6 hp11 hp12 hp17 hb0 hbk hr8 hr10 hr2 hW hq hw
    have ht : t < n := by omega
    obtain ⟨j, hjdef⟩ : ∃ j, j = (I.order k).symm ⟨t, ht⟩ := ⟨_, rfl⟩
    have hσj : (((I.order k) j : Fin n) : ℕ) = t := by rw [hjdef]; simp
    have hinvc : im (-1 - ↑t) = ((j : ℕ) : ℤ) := by
      have := hinv j j.isLt; rw [hσj] at this; exact this
    have hk0 : ((k : ℕ) : ℤ) + 1 ≠ 0 := by omega
    refine RP.step ?_
    rw [S127, if_neg (by rw [F.p0, hp6]; exact_mod_cast (Nat.not_le.mpr ht))]
    iterate 2 (refine RP.step ?_; simp only [S128, S129, Function.update_apply, ↓reduceIte,
      Nat.reduceEqDiff, F.p18, hp6, hinvc])
    refine RP.step ?_
    rw [S130 c f _ _ _ _ _ _ _ j (by simp)]
    by_cases hjR : j ∈ R (inputArcs I) I.point
    · iterate 4 (refine RP.step ?_; simp only [S131, S132, S147, S148, Function.update_apply,
        ↓reduceIte, Nat.reduceEqDiff, F.p4, hb0, hjR, h10r, le_refl, hp6])
      refine ih (t + 1) _ _ _ _ _ _ (by omega)
        (((F.upd_p 9 _ (by decide)).upd_p 7 _ (by decide)).upd_r 6 _ ⟨by decide, by decide⟩ |>.upd_p 6 _
          (by decide))
        (by simp [hp6]) (by simp [hp11]) (by simp [hp12]) (by simp [hp17]) hb0 ?_ ?_ (by simp [hr10])
        (by simp [hr2]) ?_ (by omega) (by omega)
      · rw [hbk, Bk_succ _ _ j t hσj, Finset.insert_eq_of_mem]
        rw [mem_Bk]; exact Or.inl hjR
      · simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]
        rw [hr8, Bk_succ _ _ j t hσj, Finset.insert_eq_of_mem ((mem_Bk _ _ _ _).mpr (Or.inl hjR))]
      · intro j' hj'
        have hne : j' ≠ j := fun h => hj' (h ▸ hjR)
        have hiff : (((I.order k) j' : Fin n) : ℕ) < t + 1 ↔ (((I.order k) j' : Fin n) : ℕ) < t := by
          have : (((I.order k) j' : Fin n) : ℕ) ≠ t := by
            intro h; apply hne; apply (I.order k).injective; apply Fin.ext; omega
          omega
        rw [hW j' hj']
        simp only [hiff]
    · have hRne : (if j ∈ R (inputArcs I) I.point then (1 : ℝ) else 0) = 0 := by simp [hjR]
      refine RP.step ?_
      simp only [S131, Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, F.p4, hb0, hjR, le_refl]
      refine RP.step ?_
      rw [S133 c f _ _ _ _ _ _ _ j (by simp)]
      have hcellb : M (↑↑k * ↑n + ↑m + ↑↑j) = I.basis k j := by
        rw [F.M_in _ (by positivity)]; exact cell_basis I k j
      have hMj : M (-1 - ↑↑j) = base j := by
        rw [hW j hjR, if_neg (by omega), add_zero]
      iterate 15 (refine RP.step ?_; simp only [S134, S135, S136, S137, S138, S139, S140, S141, S142,
        S143, S144, S145, S146, S147, S148, Function.update_apply, ↓reduceIte, Nat.reduceEqDiff,
        F.p0, F.p1, F.p4, F.p18, F.r0, F.r1, h1ne0, hp11, hp17, hbk, hr8, hr10, hcellb, hMj, add_zero,
        le_refl, hp6])
      refine ih (t + 1) _ _ _ _ _ _ (by omega)
        (F.upd_p 9 _ (by decide) |>.upd_p 7 _ (by decide) |>.upd_r 6 _ ⟨by decide, by decide⟩
          |>.upd_r 9 _ ⟨by decide, by decide⟩ |>.upd_r 13 _ ⟨by decide, by decide⟩
          |>.upd_r 8 _ ⟨by decide, by decide⟩ |>.upd_p 8 _ (by decide) |>.upd_p 8 _ (by decide)
          |>.upd_p 8 _ (by decide) |>.upd_r 7 _ ⟨by decide, by decide⟩
          |>.upd_r 13 _ ⟨by decide, by decide⟩ |>.upd_r 13 _ ⟨by decide, by decide⟩
          |>.upd_p 9 _ (by decide) |>.upd_r 7 _ ⟨by decide, by decide⟩
          |>.upd_r 7 _ ⟨by decide, by decide⟩ |>.upd_M _ _ (by omega) |>.upd_p 6 _ (by decide))
        (by simp [hp6]) (by simp [hp11]) (by simp [hp12]) (by simp [hp17]) ?_ ?_ ?_
        (by simp [hr10]) (by simp [hr2]) ?_ (by omega) (by omega)
      · rw [Function.update_of_ne (Ne.symm hk0)]; exact hb0
      · rw [Function.update_self, Bk_succ _ _ j t hσj]
      · simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]
        rw [Bk_succ _ _ j t hσj]
      · intro j' hj'
        by_cases hjj : j' = j
        · subst hjj
          rw [Function.update_self, if_pos (by omega), margM, ← Bk_eq_before _ _ j' t hσj]
          push_cast; ring
        · have hne : (-1 - ((j' : ℕ) : ℤ)) ≠ -1 - ((j : ℕ) : ℤ) := by
            intro h; apply hjj; apply Fin.ext; omega
          have hiff : (((I.order k) j' : Fin n) : ℕ) < t + 1 ↔ (((I.order k) j' : Fin n) : ℕ) < t := by
            have : (((I.order k) j' : Fin n) : ℕ) ≠ t := by
              intro h; apply hjj; apply (I.order k).injective; apply Fin.ext; omega
            omega
          rw [Function.update_of_ne hne, hW j' hj']
          simp only [hiff]

/-! ### Block H outer: k from k0 to e-1 (pc 107 → 151). -/

/-- Frontloading correction summed over the processed bases `k0 ≤ k' < k`. -/
noncomputable def Hs (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (k0 k : ℕ) (j : Fin n) : ℝ :=
  ∑ k' : Fin m, if k0 ≤ (k' : ℕ) ∧ (k' : ℕ) < k then
    (((margM f (R (inputArcs I) I.point) (I.order k') j : ℤ) : ℝ) - I.basis k' j) * I.weight k'
    else 0

theorem Hs_self (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (k0 : ℕ) (j : Fin n) :
    Hs f I k0 k0 j = 0 :=
  Finset.sum_eq_zero (fun k' _ => if_neg (by omega))

theorem Hs_succ (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (k0 : ℕ) (k : Fin m) (hk : k0 ≤ k)
    (j : Fin n) : Hs f I k0 ((k : ℕ) + 1) j = Hs f I k0 k j
      + (((margM f (R (inputArcs I) I.point) (I.order k) j : ℤ) : ℝ) - I.basis k j) * I.weight k := by
  unfold Hs
  set a : Fin m → ℝ := fun k' =>
    (((margM f (R (inputArcs I) I.point) (I.order k') j : ℤ) : ℝ) - I.basis k' j) * I.weight k'
    with ha
  have h : ∀ k' : Fin m, (if k0 ≤ (k' : ℕ) ∧ (k' : ℕ) < k + 1 then a k' else 0)
      = (if k0 ≤ (k' : ℕ) ∧ (k' : ℕ) < k then a k' else 0) + (if k' = k then a k' else 0) := by
    intro k'
    by_cases h1 : k0 ≤ (k' : ℕ) ∧ (k' : ℕ) < k
    · have : k' ≠ k := fun e => by rw [e] at h1; exact lt_irrefl _ h1.2
      rw [if_pos ⟨h1.1, by omega⟩, if_pos h1, if_neg this, add_zero]
    · by_cases h2 : k' = k
      · subst h2; rw [if_pos ⟨hk, by omega⟩, if_neg h1, if_pos rfl, zero_add]
      · have : ¬ (k0 ≤ (k' : ℕ) ∧ (k' : ℕ) < k + 1) := fun h3 =>
          h1 ⟨h3.1, by
            have : (k' : ℕ) ≠ k := fun e => h2 (Fin.ext e)
            omega⟩
        rw [if_neg this, if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl (fun k' _ => h k'), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte, ha]

theorem loopHo (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (k0 e : ℕ) (he : e ≤ m)
    (QH WH : ℕ) (G : OracleState n → Prop)
    (K : ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ) (bm : ℤ → Finset (Fin n)) (q w : ℕ),
      Frame c I r p M im → bm 0 = R (inputArcs I) I.point →
      (∀ j : Fin n, j ∉ R (inputArcs I) I.point →
        M (-1 - ((j : ℕ) : ℤ)) = ysum I m j + Hs f I k0 e j) →
      q ≤ QH → w ≤ WH + 2 → RP c f (st 151 r p M im bm q w) G) :
    ∀ (d k : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (im : ℤ → ℤ) (bm : ℤ → Finset (Fin n))
      (q w : ℕ), k + d = e → k0 ≤ k → Frame c I r p M im → p 11 = k → p 12 = (e : ℤ) - 1 →
      bm 0 = R (inputArcs I) I.point → r 2 = (f (R (inputArcs I) I.point) : ℝ) →
      (∀ j : Fin n, j ∉ R (inputArcs I) I.point →
        M (-1 - ((j : ℕ) : ℤ)) = ysum I m j + Hs f I k0 k j) →
      q + d * n ≤ QH → w + d * (33 * n + 11) ≤ WH → RP c f (st 107 r p M im bm q w) G := by
  intro d
  induction d with
  | zero =>
    intro k r p M im bm q w hkd _ F hp11 hp12 hb0 hr2 hW hq hw
    simp only [Nat.add_zero] at hkd
    subst hkd
    refine RP.step ?_
    rw [S107, if_neg (by rw [hp11, hp12]; omega)]
    refine RP.step ?_
    rw [S108, if_pos le_rfl]
    exact K r p M im bm q _ F hb0 hW (by omega) (by omega)
  | succ d ih =>
    intro k r p M im bm q w hkd hk0 F hp11 hp12 hb0 hr2 hW hq hw
    have hk : k < m := by omega
    refine RP.step ?_
    rw [S107, if_pos (by rw [hp11, hp12]; omega)]
    iterate 2 (refine RP.step ?_; simp only [S109, S110, Function.update_apply, ↓reduceIte,
      Nat.reduceEqDiff, hp11, F.p5])
    refine loopH1 c f I M q ⟨k, hk⟩ e (f (R (inputArcs I) I.point) : ℝ) (w + 3 + 12 * n) G ?_ n 0 _ _ im
      bm _ (by omega) ((F.upd_p 17 _ (by decide)).upd_p 7 _ (by decide)) (by simp) (by simp [hp11])
      (by simp [hp12]) (by simp) (fun i hi => absurd hi (Nat.not_lt_zero _)) hb0
      (fun i hi => absurd hi (Nat.not_lt_zero _)) hr2 (by omega)
    intro r1 p1 im1 bm1 w1 F1 h11 h12 h17 hinv1 hb01 hbk1 hr21 hw1
    have hcellw : M (k : ℤ) = I.weight ⟨k, hk⟩ := by
      rw [F1.M_in _ (by positivity)]; exact cell_weight I ⟨k, hk⟩
    iterate 4 (refine RP.step ?_; simp only [S123, S124, S125, S126, Function.update_apply,
      ↓reduceIte, Nat.reduceEqDiff, h11, hcellw, hr21, F1.r0, add_zero])
    refine loopH2 c f I im1 ⟨k, hk⟩ e (f (R (inputArcs I) I.point) : ℝ)
      (fun j => ysum I m j + Hs f I k0 k j) (q + n) (w1 + 4 + 21 * n) G hinv1 ?_ n 0 _ _ M bm1 q _
      (by omega)
      ((((F1.upd_r 8 _ ⟨by decide, by decide⟩).upd_p 9 _ (by decide)).upd_r 10 _
        ⟨by decide, by decide⟩).upd_p 6 _ (by decide))
      (by simp) (by simp [h11]) (by simp [h12]) (by simp [h17]) hb01 (by rw [hbk1, Bk_zero])
      (by simp [Bk_zero]) (by simp) (by simp [hr21])
      (fun j hj => by rw [hW j hj]; simp) (by omega) (by omega)
    intro r2 p2 M2 bm2 q2 w2 F2 h11' h12' hb02 hr22 hW2 hq2 hw2
    iterate 2 (refine RP.step ?_; simp only [S149, S150, Function.update_apply, ↓reduceIte,
      Nat.reduceEqDiff, h11', le_refl])
    refine ih (k + 1) _ _ M2 im1 bm2 q2 _ (by omega) (by omega) (F2.upd_p 11 _ (by decide))
      (by simp [h11']) (by simp [h12']) hb02 hr22 ?_ ?_ ?_
    · intro j hj
      rw [hW2 j hj, Hs_succ f I k0 ⟨k, hk⟩ hk0 j]
      ring
    · rw [Nat.succ_mul] at hq; omega
    · rw [Nat.succ_mul] at hw; omega

/-! ### Block I: argmin of W over Rᶜ, then halt (pc 151 → 168). -/

/-- Loop invariant of block I after scanning indices `< j`: either nothing outside `Rs` was seen
(flag 0), or `q15` is an argmin so far with value `r12` (flag 1). -/
def InvI (Rs : Finset (Fin n)) (M : ℤ → ℝ) (r12 : ℝ) (q15 q16 : ℤ) (j : ℕ) : Prop :=
  (q16 = 0 ∧ ∀ j' : Fin n, (j' : ℕ) < j → j' ∈ Rs) ∨
  (q16 = 1 ∧ ∃ qq : Fin n, q15 = ((qq : ℕ) : ℤ) ∧ qq ∉ Rs ∧ r12 = M (-1 - ((qq : ℕ) : ℤ)) ∧
    ∀ j' : Fin n, (j' : ℕ) < j → j' ∉ Rs → M (-1 - ((qq : ℕ) : ℤ)) ≤ M (-1 - ((j' : ℕ) : ℤ)))

theorem InvI_skip (Rs : Finset (Fin n)) (M : ℤ → ℝ) (a : ℝ) (b e : ℤ) (j : ℕ) (hj : j < n)
    (hjR : (⟨j, hj⟩ : Fin n) ∈ Rs) (h : InvI Rs M a b e j) : InvI Rs M a b e (j + 1) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, qq, h3, h4, h5, h6⟩
  · refine Or.inl ⟨h1, fun j' hj' => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
    · exact h2 j' h
    · have : j' = ⟨j, hj⟩ := Fin.ext h
      rw [this]; exact hjR
  · refine Or.inr ⟨h1, qq, h3, h4, h5, fun j' hj' hj'R => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
    · exact h6 j' h hj'R
    · have : j' = ⟨j, hj⟩ := Fin.ext h
      exact absurd (this ▸ hjR) hj'R

theorem InvI_take (Rs : Finset (Fin n)) (M : ℤ → ℝ) (j : ℕ) (hj : j < n)
    (hjR : (⟨j, hj⟩ : Fin n) ∉ Rs)
    (hle : ∀ j' : Fin n, (j' : ℕ) < j → j' ∉ Rs → M (-1 - (j : ℤ)) ≤ M (-1 - ((j' : ℕ) : ℤ))) :
    InvI Rs M (M (-1 - (j : ℤ))) (j : ℤ) 1 (j + 1) := by
  refine Or.inr ⟨rfl, ⟨j, hj⟩, rfl, hjR, rfl, fun j' hj' hj'R => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
  · exact hle j' h hj'R
  · rw [h]

theorem InvI_keep (Rs : Finset (Fin n)) (M : ℤ → ℝ) (a : ℝ) (b : ℤ) (j : ℕ) (hj : j < n)
    (h : InvI Rs M a b 1 j) (hgt : a < M (-1 - (j : ℤ))) : InvI Rs M a b 1 (j + 1) := by
  rcases h with ⟨h1, _⟩ | ⟨_, qq, h3, h4, h5, h6⟩
  · exact absurd h1 one_ne_zero
  · refine Or.inr ⟨rfl, qq, h3, h4, h5, fun j' hj' hj'R => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
    · exact h6 j' h hj'R
    · rw [← h5, h]; exact hgt.le

theorem loopI (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (Rs : Finset (Fin n)) (hb0 : bm 0 = Rs) (q WI : ℕ)
    (hne : ∃ j0 : Fin n, j0 ∉ Rs) (G : OracleState n → Prop)
    (K : ∀ (s : OracleState n) (qq : Fin n), s.output = some ((qq : ℕ) : ℤ) → s.queries = q →
      s.work ≤ WI → qq ∉ Rs →
      (∀ j' : Fin n, j' ∉ Rs → M (-1 - ((qq : ℕ) : ℤ)) ≤ M (-1 - ((j' : ℕ) : ℤ))) → G s) :
    ∀ (d j : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ), j + d = n → Frame c I r p M im →
      p 7 = j → InvI Rs M (r 12) (p 15) (p 16) j → w + 13 * d + 2 ≤ WI →
      RP c f (st 153 r p M im bm q w) G := by
  intro d
  induction d with
  | zero =>
    intro j r p w hjd F hp7 hinv hw
    simp only [Nat.add_zero] at hjd
    subst hjd
    refine RP.step ?_
    rw [S153, if_pos (by rw [F.p0, hp7])]
    refine RP.step ?_
    rw [G_halt (lswProg c) f 168 r p M im bm q (w + 1) 15 rfl]
    refine RP.done ?_
    rcases hinv with ⟨_, hall⟩ | ⟨_, qq, h15, hqR, _, hmin⟩
    · obtain ⟨j0, hj0⟩ := hne
      exact absurd (hall j0 j0.isLt) hj0
    · exact K _ qq (by simp [h15]) rfl (by dsimp only; omega) hqR
        (fun j' hj' => hmin j' j'.isLt hj')
  | succ d ih =>
    intro j r p w hjd F hp7 hinv hw
    have hj : j < n := by omega
    refine RP.step ?_
    rw [S153, if_neg (by rw [F.p0, hp7]; exact_mod_cast (Nat.not_le.mpr hj))]
    refine RP.step ?_
    rw [S154 c f _ _ _ _ _ _ _ ⟨j, hj⟩ (by simp [hp7])]
    by_cases hjR : (⟨j, hj⟩ : Fin n) ∈ Rs
    · iterate 4 (refine RP.step ?_; simp only [S155, S156, S166, S167, Function.update_apply,
        ↓reduceIte, Nat.reduceEqDiff, F.p4, hb0, hjR, le_refl, h10r])
      refine ih (j + 1) _ _ _ (by omega) ((F.upd_r 6 _ ⟨by decide, by decide⟩).upd_p 7 _ (by decide))
        (by simp [hp7]) ?_ (by omega)
      simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]
      exact InvI_skip Rs M _ _ _ j hj hjR hinv
    · iterate 3 (refine RP.step ?_; simp only [S155, S157, S158, Function.update_apply,
        ↓reduceIte, Nat.reduceEqDiff, F.p4, hb0, hjR, le_refl, h10r, F.p18, hp7])
      rcases hinv with ⟨h16, hall⟩ | ⟨h16, qq, h15, hqR, h12, hmin⟩
      · iterate 6 (refine RP.step ?_; simp only [S159, S163, S164, S165, S166, S167,
          Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, h16, F.p4, le_refl, F.r0, add_zero, hp7])
        refine ih (j + 1) _ _ _ (by omega)
          ((((((F.upd_r 6 _ ⟨by decide, by decide⟩).upd_p 9 _ (by decide)).upd_r 7 _
            ⟨by decide, by decide⟩).upd_r 12 _ ⟨by decide, by decide⟩).upd_p 15 _
            (by decide)).upd_p 16 _ (by decide) |>.upd_p 7 _ (by decide))
          (by simp [hp7]) ?_ (by omega)
        simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, hp7, F.r0, add_zero]
        exact InvI_take Rs M j hj hjR (fun j' hj' hj'R => absurd (hall j' hj') hj'R)
      · by_cases hle : M (-1 - (j : ℤ)) - r 12 ≤ 0
        · iterate 8 (refine RP.step ?_; simp only [S159, S160, S161, S163, S164, S165, S166, S167,
            Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, h16, F.p4, h10z, le_refl, F.r0,
            add_zero, hp7, hle])
          refine ih (j + 1) _ _ _ (by omega)
            ((((((((F.upd_r 6 _ ⟨by decide, by decide⟩).upd_p 9 _ (by decide)).upd_r 7 _
              ⟨by decide, by decide⟩).upd_r 6 _ ⟨by decide, by decide⟩).upd_r 12 _
              ⟨by decide, by decide⟩).upd_p 15 _ (by decide)).upd_p 16 _ (by decide)
              |>.upd_p 7 _ (by decide)))
            (by simp [hp7]) ?_ (by omega)
          simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte, hp7, F.r0, add_zero]
          refine InvI_take Rs M j hj hjR (fun j' hj' hj'R => ?_)
          have := hmin j' hj' hj'R
          rw [← h12] at this
          linarith
        · iterate 6 (refine RP.step ?_; simp only [S159, S160, S161, S162, S166, S167,
            Function.update_apply, ↓reduceIte, Nat.reduceEqDiff, h16, F.p4, h10z, le_refl, hle])
          refine ih (j + 1) _ _ _ (by omega)
            ((((F.upd_r 6 _ ⟨by decide, by decide⟩).upd_p 9 _ (by decide)).upd_r 7 _
              ⟨by decide, by decide⟩).upd_r 6 _ ⟨by decide, by decide⟩ |>.upd_p 7 _ (by decide))
            (by simp [hp7]) ?_ (by omega)
          simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]
          rw [h16]
          exact InvI_keep Rs M _ _ j hj (Or.inr ⟨rfl, qq, h15, hqR, h12, hmin⟩)
            (by linarith [not_le.mp hle])

theorem blockI (c : ℕ) (f : Finset (Fin n) → ℤ) (I : ArcInput n m) (M : ℤ → ℝ) (im : ℤ → ℤ)
    (bm : ℤ → Finset (Fin n)) (Rs : Finset (Fin n)) (hb0 : bm 0 = Rs) (q WI : ℕ)
    (hne : ∃ j0 : Fin n, j0 ∉ Rs) (G : OracleState n → Prop)
    (K : ∀ (s : OracleState n) (qq : Fin n), s.output = some ((qq : ℕ) : ℤ) → s.queries = q →
      s.work ≤ WI → qq ∉ Rs →
      (∀ j' : Fin n, j' ∉ Rs → M (-1 - ((qq : ℕ) : ℤ)) ≤ M (-1 - ((j' : ℕ) : ℤ))) → G s)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ) (F : Frame c I r p M im) (hw : w + 13 * n + 4 ≤ WI) :
    RP c f (st 151 r p M im bm q w) G := by
  refine RP.step ?_
  rw [S151]
  refine RP.step ?_
  rw [S152]
  refine loopI c f I M im bm Rs hb0 q WI hne G K n 0 _ _ _ (by omega)
    ((F.upd_p 16 _ (by decide)).upd_p 7 _ (by decide)) (by simp) ?_ (by omega)
  simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte]
  exact Or.inl ⟨rfl, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩

end Run

end LSW79M

/-! ## Part 3: assembly (relay 3). -/

namespace LSW79Fin

open LSWNewArcAudit.NewArc SmaleNinth LSWCuttingPlane.SFMArcs

theorem sigma_le_of_R {n : ℕ} (A : Fin n → Fin n → Prop) (σ : Equiv.Perm (Fin n))
    (hc : Consistent A σ) (p j : Fin n) (h : Relation.ReflTransGen A p j) : σ j ≤ σ p := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_of_lt (lt_of_lt_of_le (hc _ _ hbc) ih)

theorem bfs_eq_upper {n : ℕ} (f : Finset (Fin n) → ℤ) (A : Fin n → Fin n → Prop)
    (σ : Equiv.Perm (Fin n)) (hc : Consistent A σ) (p : Fin n) (hall : ∀ j, j ∈ R A p) :
    bfs f σ p = (upper f A p : ℝ) := by
  classical
  have hRu : R A p = Finset.univ := Finset.eq_univ_of_forall hall
  have hb : before σ p = Finset.univ.erase p := by
    ext u
    simp only [before, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro h e; subst e; exact lt_irrefl _ h
    · intro hne
      have h1 := sigma_le_of_R A σ hc p u ((LSW79F.LSW79Aux_mem_R A p u).mp (hall u))
      exact lt_of_le_of_ne h1 (fun e => hne (σ.injective e))
  unfold bfs upper
  rw [hb, hRu, Finset.insert_erase (Finset.mem_univ p)]

theorem exists_not_mem_R {n m : ℕ} [NeZero n] (f : Finset (Fin n) → ℤ)
    (A : Fin n → Fin n → Prop) (p : Fin n) (lam : Fin m → ℝ) (σs : Fin m → Equiv.Perm (Fin n))
    (hc : ∀ k, Consistent A (σs k)) (K : Finset (Fin m))
    (hy : 0 < ymax (fun j => ∑ k, lam k * bfs f (σs k) j))
    (hG : ((n : ℝ) - 1) * n * ymax (fun j => ∑ k, lam k * bfs f (σs k) j)
      < ∑ k ∈ K, lam k * ((upper f A p : ℝ) - bfs f (σs k) p)) :
    ∃ j, j ∉ R A p := by
  by_contra h
  push_neg at h
  have h0 : ∑ k ∈ K, lam k * ((upper f A p : ℝ) - bfs f (σs k) p) = 0 :=
    Finset.sum_eq_zero (fun k _ => by rw [bfs_eq_upper f A (σs k) (hc k) p h, sub_self, mul_zero])
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have : 0 ≤ ((n : ℝ) - 1) * n * ymax (fun j => ∑ k, lam k * bfs f (σs k) j) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hy.le
  linarith

theorem W_eq {n m : ℕ} (f : Finset (Fin n) → ℤ) (I : ArcInput n m)
    (hrep : ∀ k j, I.basis k j = bfs f (I.order k) j) (k0 e : ℕ) (j : Fin n) :
    LSW79M.ysum I m j + LSW79M.Hs f I k0 e j
      = LSW79F.Wv f (R (inputArcs I) I.point) I.weight I.order
          (Finset.univ.filter (fun k : Fin m => k0 ≤ (k : ℕ) ∧ (k : ℕ) < e)) j := by
  rw [LSW79F.Wv_eq, Finset.sum_filter]
  unfold LSW79M.ysum LSW79M.Hs
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [if_pos k.isLt, hrep, mul_comm]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs
    · rw [hrep]; unfold LSW79M.margM LSW79F.marg; ring
    · rfl

theorem work_bound (n m c d x : ℕ) (hn : 1 ≤ n) (hm : m ≤ c * n) (hd : d ≤ c * n)
    (hx : x ≤ 14 + 10 * n + 4 + n * (11 * n + 13) + 5 + 2 + m * (12 * n + 7) + 11 + 15 * m + 4
      + d * (33 * n + 11) + 2 + 13 * n + 4) :
    x ≤ (100 * c + 100) * n ^ 2 := by
  have h1 : m * (12 * n + 7) ≤ c * n * (12 * n + 7) := Nat.mul_le_mul_right _ hm
  have h2 : d * (33 * n + 11) ≤ c * n * (33 * n + 11) := Nat.mul_le_mul_right _ hd
  have h3 : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  have h4 : c * n ≤ c * n * n := Nat.le_mul_of_pos_right _ hn
  have h6 : 1 ≤ n * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  nlinarith

theorem run_main (c : ℕ) (hc : 1 ≤ c) (n : ℕ) [NeZero n] (m : ℕ) (I : ArcInput n m)
    (f : Finset (Fin n) → ℤ) (hf : Submodular f) (hm : m ≤ c * n)
    (hrepr : RepresentedCombination f I) (hnd : NonDegenerate (inputVector I))
    (hup : (n : ℝ) ^ 4 * ymax (inputVector I) < (upper f (inputArcs I) I.point : ℝ)) :
    LSW79M.RP c f (oracleInitial (inputMemory I)) (fun s => ∃ q : Fin n,
      s.output = some (q.val : ℤ) ∧ q ∉ R (inputArcs I) I.point ∧
      (∀ S : Finset (Fin n), IsMinimizer (inputArcs I) f S → I.point ∈ S → q ∈ S) ∧
      s.queries ≤ (c * c + 2) * n ∧ s.work ≤ (100 * c + 100) * n ^ 2) := by
  obtain ⟨⟨hlam0, hlam1, hcons⟩, hbasis⟩ := hrepr
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hlam1
    · exact h
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hvec : inputVector I = fun j => ∑ k, I.weight k * bfs f (I.order k) j := by
    funext j; unfold inputVector; simp only [hbasis]
  have hy : 0 < ymax (fun j => ∑ k, I.weight k * bfs f (I.order k) j) := by
    obtain ⟨i, hi⟩ := hnd.1
    rw [hvec] at hi
    exact lt_of_lt_of_le hi
      (Finset.le_sup' (fun j => ∑ k, I.weight k * bfs f (I.order k) j) (Finset.mem_univ i))
  rw [hvec] at hup
  refine LSW79M.blockA c f I _ ?_
  intro r p F hp7 hp11
  refine LSW79M.loopB c f I hmpos _ ?_ n 0 r p _ 13 (by omega) F
    (fun i hi => absurd hi (Nat.not_lt_zero _)) (by simp [hp7]) hp11 (by omega)
  intro r p im w2 F hinv hp11 hw2
  refine LSW79M.blockC c f I hmpos (hcons _) _ im hinv _ r p w2 F ?_
  intro r p bm w3 F hb hw3
  refine LSW79M.blockD c f I _ im bm _ r p 0 w3 F hb ?_
  intro r bm q4 w4 F hb hr2 hr4 hq4 hw4
  refine LSW79M.blockE c f I im bm q4 _ r p _ w4 F ?_ ?_
  · intro j
    have h : (-1 - ((j : ℕ) : ℤ)) < 0 := by omega
    simp [inputRealCell, h]
  intro r5 p5 M5 w5 F hM5 hr25 hr45 hw5
  refine LSW79M.blockF c f I hmpos M5 im bm q4 _ r5 p5 w5 F _ _ (hr45.trans hr4)
    (hr25.trans hr2) ?_
  intro r6 p6 w6 ks F h13 hmax h26 hw6
  refine LSW79M.blockG c f I M5 im bm q4 ks _ r6 p6 w6 F h13 ?_
  intro p7 k0 e w7 F h11 h12 hcase hw7
  have hks := ks.isLt
  have he : e ≤ m := by rcases hcase with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> omega
  have hk0e : k0 ≤ e := by rcases hcase with ⟨_, h1, h⟩ | ⟨_, h1, h⟩ <;> omega
  have hd1 : e - k0 ≤ c * c := by
    rcases hcase with ⟨hnc, h1, h⟩ | ⟨_, h1, h⟩
    · have := Nat.mul_le_mul_left c hnc
      omega
    · have := Nat.mul_le_mul hc hc
      omega
  have hd2 : e - k0 ≤ c * n := by
    rcases hcase with ⟨_, h1, h⟩ | ⟨_, h1, h⟩
    · omega
    · have := Nat.mul_le_mul hc hn1
      omega
  obtain ⟨Kset, hKset⟩ : ∃ K : Finset (Fin m),
      K = Finset.univ.filter (fun k : Fin m => k0 ≤ (k : ℕ) ∧ (k : ℕ) < e) := ⟨_, rfl⟩
  have hG : ((n : ℝ) - 1) * n * ymax (fun j => ∑ k, I.weight k * bfs f (I.order k) j)
      < ∑ k ∈ Kset, I.weight k
          * ((upper f (inputArcs I) I.point : ℝ) - bfs f (I.order k) I.point) := by
    rcases hcase with ⟨hnc, h1, h2⟩ | ⟨hnc, h1, h2⟩
    · have : Kset = Finset.univ := by
        rw [hKset]; ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact ⟨by omega, by have := k.isLt; omega⟩
      rw [this]; exact LSW79F.G_all f I.weight I.order hlam1 _ I.point hy hup
    · have : Kset = {ks} := by
        rw [hKset]; ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h; exact Fin.ext (by omega)
        · intro h; subst h; omega
      rw [this]
      refine LSW79F.G_one f I.weight I.order hlam1 _ I.point hy hup c hm (by omega) ks
        (fun l => ?_)
      have := hmax l
      unfold LSW79M.gainF at this
      rw [hbasis, hbasis] at this
      rw [mul_comm (I.weight l), mul_comm (I.weight ks)]
      exact this
  have hne := exists_not_mem_R f (inputArcs I) I.point I.weight I.order hcons Kset hy hG
  refine LSW79M.loopHo c f I k0 e he (q4 + (e - k0) * n) (w7 + (e - k0) * (33 * n + 11)) _ ?_
    (e - k0) k0 r6 p7 M5 im bm q4 w7 (by omega) le_rfl F h11 h12 hb h26
    (fun j _ => by rw [hM5 j, LSW79M.Hs_self, add_zero]) le_rfl le_rfl
  intro r8 p8 M8 im8 bm8 q8 w8 F hb8 hW8 hq8 hw8
  refine LSW79M.blockI c f I M8 im8 bm8 (R (inputArcs I) I.point) hb8 q8 (w8 + 13 * n + 4) hne _ ?_
    r8 p8 w8 F le_rfl
  intro s qq hout hqs hws hqR hmin
  refine ⟨qq, hout, hqR, ?_, ?_, ?_⟩
  · refine LSW79F.crit f hf (inputArcs I) I.point I.weight I.order hlam0 hlam1 Kset hy hG qq hqR
      (fun j hj => ?_)
    have h1 := hmin j hj
    rw [hW8 qq hqR, hW8 j hj, W_eq f I hbasis, W_eq f I hbasis, ← hKset] at h1
    exact h1
  · rw [hqs]
    have h1 := Nat.mul_le_mul_right n hd1
    have h2 : (c * c + 2) * n = c * c * n + 2 * n := by ring
    omega
  · exact work_bound n m c (e - k0) s.work hn1 hm hd2 (by omega)

end LSW79Fin

open LSWNewArcAudit.NewArc LSWCuttingPlane.SFMArcs in
theorem solution :
    ∀ c : ℕ, 1 ≤ c →
    ∃ program : OracleProgram, LiteralProgram program ∧
    ∃ C_Q C_T : ℕ, 0 < C_Q ∧ 0 < C_T ∧
    ∀ (n : ℕ) [NeZero n] (m : ℕ) (I : ArcInput n m)
      (f : Finset (Fin n) → ℤ),
      Submodular f → f ∅ = 0 → Acyclic (inputArcs I) →
      m ≤ c * n → RepresentedCombination f I →
      NonDegenerate (inputVector I) →
      (n : ℝ) ^ 4 * ymax (inputVector I) < (upper f (inputArcs I) I.point : ℝ) →
      ∃ (steps : ℕ) (q : Fin n),
        let result := oracleRun program f (inputMemory I) steps
        result.output = some (q.val : ℤ) ∧
        q ∉ R (inputArcs I) I.point ∧
        (∀ S : Finset (Fin n), IsMinimizer (inputArcs I) f S →
          I.point ∈ S → q ∈ S) ∧
        result.queries ≤ C_Q * n ∧ result.work ≤ C_T * n ^ 2 := by
  intro c hc
  refine ⟨LSW79M.lswProg c, LSW79M.lswProg_literal c, c * c + 2, 100 * c + 100, by positivity,
    by positivity, ?_⟩
  intro n _ m I f hf _ _ hm hrep hnd hup
  obtain ⟨t, q, h1, h2, h3, h4, h5⟩ := LSW79Fin.run_main c hc n m I f hf hm hrep hnd hup
  exact ⟨t, q, h1, h2, h3, h4, h5⟩
