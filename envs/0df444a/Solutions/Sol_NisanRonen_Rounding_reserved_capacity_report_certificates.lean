-- Prove2me | solution 1 for NisanRonen.Rounding.reserved_capacity_report_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:04:35.771797+00:00
-- url     : https://prove2.me/submissions/964bbae3-bea6-46a7-9560-390d7454f44c

import Theorems.Thm_NisanRonen_Rounding_bundle_report_bound_with_reserved_machine

open NisanRonen.Rounding

set_option autoImplicit false

private noncomputable def jobLoad {n k : ℕ} (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) (l : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => x j = l), roundUp δ (d l j)

private noncomputable def span {n k : ℕ} [NeZero n] (δ : ℝ)
    (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) : ℝ :=
  roundedMakespan δ x (corrStar x d)

private theorem span_eq {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) :
    span δ x d = Finset.univ.sup' Finset.univ_nonempty (jobLoad δ x d) := by
  unfold span roundedMakespan makespan
  congr 1
  funext l
  unfold jobLoad load
  apply Finset.sum_congr rfl
  intro j hj
  simp [corrStar, (Finset.mem_filter.1 hj).2]

private theorem load_le_span {n k : ℕ} [NeZero n] {δ : ℝ}
    (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) (l : Fin n) :
    jobLoad δ x d l ≤ span δ x d := by
  rw [span_eq]
  exact Finset.le_sup' _ (Finset.mem_univ l)

private theorem ru_mono {δ : ℝ} (hδ : 0 < δ) {u v : ℝ} (h : u ≤ v) :
    roundUp δ u ≤ roundUp δ v := by
  unfold roundUp
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast Int.ceil_mono (div_le_div_of_nonneg_right h hδ.le)) hδ.le

private theorem pack_excluding_two {n k c : ℕ} (hn : 2 ≤ n) (hc : k - 1 ≤ (n - 2) * c) (i : Fin n)
    (S : Finset (Fin k)) (hS : S.Nonempty) {A : ℝ} (hA : 0 ≤ A) :
    ∃ spare : Fin n, spare ≠ i ∧ ∃ bg : Fin k → Fin n,
      (∀ j, j ∉ S → bg j ≠ i ∧ bg j ≠ spare) ∧
      ∀ l : Fin n, (∑ _j ∈ Finset.univ.filter (fun j => j ∉ S ∧ bg j = l), A) ≤ (c : ℝ) * A := by
  classical
  obtain _ | n := n
  · omega
  obtain _ | m := n
  · omega
  let spare := i.succAbove (0 : Fin (m + 1))
  let group (l : Fin m) := i.succAbove l.succ
  have hg : Function.Injective group := fun _ _ h =>
    Fin.succ_injective _ (Fin.succAbove_right_injective h)
  have hgi (l : Fin m) : group l ≠ i := i.succAbove_ne _
  have hgs (l : Fin m) : group l ≠ spare := fun h =>
    Fin.succ_ne_zero _ (Fin.succAbove_right_injective h)
  have hc : Fintype.card {j : Fin k // j ∉ S} ≤ Fintype.card (Fin m × Fin c) := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin]
    have hs := Finset.card_pos.mpr hS
    have hbound : k - 1 ≤ m * c := by simpa using hc
    exact (Nat.sub_le_sub_left (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs)) k).trans hbound
  obtain ⟨e⟩ := Function.Embedding.nonempty_iff_card_le.mpr hc
  let bg (j : Fin k) := if h : j ∉ S then group (e ⟨j, h⟩).1 else i
  refine ⟨spare, i.succAbove_ne _, bg, ?_, ?_⟩
  · intro j hj
    simpa [bg, hj] using And.intro (hgi (e ⟨j, hj⟩).1) (hgs (e ⟨j, hj⟩).1)
  · intro l
    let F := Finset.univ.filter (fun j : Fin k => j ∉ S ∧ bg j = l)
    have hf (j : F) : (j : Fin k) ∉ S ∧ bg j = l :=
      (Finset.mem_filter.1 j.property).2
    let g (j : F) := (e ⟨j, (hf j).1⟩).2
    have hi : Function.Injective g := by
      intro j j' h
      apply Subtype.ext
      have he : e ⟨(j : Fin k), (hf j).1⟩ =
          e ⟨(j' : Fin k), (hf j').1⟩ := by
        refine Prod.ext (hg ?_) h
        simpa only [bg, dif_pos (hf j).1, dif_pos (hf j').1] using
          (hf j).2.trans (hf j').2.symm
      exact congrArg (fun x : {j : Fin k // j ∉ S} => x.val) (e.injective he)
    have hcF : F.card ≤ c := by
      simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective g hi
    change (∑ _ ∈ F, A) ≤ (c : ℝ) * A
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcF) hA


theorem solution {n k : ℕ} [NeZero n] {a b δ M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hMa : a ≤ M) (hMb : M ≤ b)
    (hgrid : roundUp δ M = M) (hn : 2 ≤ n)
    (c : ℕ) (hcount : k - 1 ≤ (n - 2) * c)
    (hspace : (c : ℝ) * roundUp δ a < M)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ l, DeclarationOptimal f δ a b l (t l) (d l))
    (y : Fin k → Fin n) (hy : roundedMakespan δ y (corrStar y t) < M) :
    HasAllocationCertificates f δ a b t d M := by
  classical
  have hpos : 0 ≤ roundUp δ a := by
    unfold roundUp
    exact mul_nonneg hδ.le (by exact_mod_cast Int.ceil_nonneg (div_nonneg ha.le hδ.le))
  have hM0 := ha.le.trans hMa
  have rowBound (l : Fin n) (S : Finset (Fin k)) :
      S ⊆ Finset.univ.filter (fun j => y j = l) →
      (∑ j ∈ S, roundUp δ (d l j)) ≤ M := by
    induction S using Finset.strongInductionOn
    rename_i S ih
    intro hsub
    by_cases hempty : S = ∅
    · simp [hempty, hM0]
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨spare, hs, bg, hbg, hbgload⟩ := pack_excluding_two hn hcount l S ⟨j, hj⟩ hpos
    have htrue : (∑ j ∈ S, roundUp δ (t l j)) < M := by
      have hS := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun j => roundUp δ (t l j)) hsub (fun j _ _ =>
          hpos.trans (ru_mono hδ (ht l j).1))
      exact (hS.trans (load_le_span y t l)).trans_lt hy
    exact bundle_report_bound_with_reserved_machine ha hδ hMa hMb hgrid f hf l spare hs
      (t l) (d l) (ht l) (hd l) (hop l) S j hj bg hbg (fun u => (hbgload u).trans_lt hspace)
      htrue (ih _ (Finset.erase_ssubset hj) ((Finset.erase_subset _ _).trans hsub))
  intro i _
  refine ⟨d, hd, rfl, rfl, y, ?_⟩
  change span δ y (Function.update d i (t i)) ≤ M
  rw [span_eq]
  apply Finset.sup'_le
  intro l _
  by_cases hl : l = i
  · subst l
    simpa [jobLoad] using ((load_le_span y t i).trans hy.le)
  · simpa [jobLoad, hl] using rowBound l _ (Finset.Subset.refl _)

