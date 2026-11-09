-- Prove2me | solution 1 for KWSpectrum.Estimator.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T14:13:02.094566+00:00
-- url     : https://prove2.me/submissions/ab1b2bcb-e79b-428b-a5ef-bdb5083ec427

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

set_option autoImplicit false

namespace KW21

open QAlgorithms QAlgorithms.Schur Finset

theorem piKron_mul {d n : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    piKron n (A * B) = piKron n A * piKron n B := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

theorem piKron_one {d n : ℕ} : piKron n (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem tp_mul_piKron {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin d) (Fin d) ℂ) :
    tensorPermutation d n σ * piKron n A = piKron n A * tensorPermutation d n σ := by
  ext y x
  simp only [Matrix.mul_apply, tensorPermutation, piKron, Matrix.of_apply]
  rw [Fintype.sum_eq_single (y ∘ σ) (fun b hb => by
        have hne : ¬ (y = b ∘ ⇑σ.symm) := by
          rintro rfl; exact hb (by ext i; simp)
        simp [hne]),
      Fintype.sum_eq_single (x ∘ σ.symm) (fun b hb => by simp [hb])]
  have h1 : y = (y ∘ σ) ∘ ⇑σ.symm := by ext i; simp
  rw [if_pos h1, if_pos rfl, one_mul, mul_one]
  refine Eq.trans ?_ (Equiv.prod_comp σ (fun i => A (y i) ((x ∘ σ.symm) i)))
  simp

theorem young_comm {d n : ℕ} (Y : Partition d n) (A : Matrix (Fin d) (Fin d) ℂ) :
    tensorYoungOperator Y * piKron n A = piKron n A * tensorYoungOperator Y := by
  unfold tensorYoungOperator
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, tp_mul_piKron]

theorem piKron_mem {d n : ℕ} (Y : Partition d n) (A : Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin n → Fin d)) (hv : v ∈ schurModule Y) :
    Matrix.toEuclideanLin (piKron n A) v ∈ schurModule Y := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨Matrix.toEuclideanLin (piKron n A) w, ?_⟩
  have := congrArg (fun M => Matrix.toEuclideanLin M w) (young_comm Y A)
  simpa using this

theorem rep_apply {d n : ℕ} (Y : Partition d n) (A : Matrix (Fin d) (Fin d) ℂ)
    (v : schurModule Y) :
    ((polynomialRepresentation Y A v : schurModule Y) : EuclideanSpace ℂ (Fin n → Fin d)) =
      Matrix.toEuclideanLin (piKron n A) v := by
  have h := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := schurModule Y)
    ⟨_, piKron_mem Y A v v.2⟩
  exact congrArg Subtype.val h

theorem rep_mul {d n : ℕ} (Y : Partition d n) (A B : Matrix (Fin d) (Fin d) ℂ) :
    polynomialRepresentation Y (A * B) =
      polynomialRepresentation Y A ∘ₗ polynomialRepresentation Y B := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  simp only [rep_apply, LinearMap.comp_apply, piKron_mul, Matrix.toLpLin_mul_same]

theorem rep_one {d n : ℕ} (Y : Partition d n) :
    polynomialRepresentation Y (1 : Matrix (Fin d) (Fin d) ℂ) = LinearMap.id := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  simp only [rep_apply, piKron_one, Matrix.toLpLin_one, LinearMap.id_apply]


theorem piKron_diagonal {d n : ℕ} (r : Fin d → ℂ) :
    piKron n (Matrix.diagonal r) = Matrix.diagonal (fun w : Fin n → Fin d => ∏ k, r (w k)) := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)


variable {d n : ℕ}

noncomputable def rowOf (Y : Partition d n) (k : Fin n) : ℕ := ((cellNumbering Y).symm k).val.1
noncomputable def colOf (Y : Partition d n) (k : Fin n) : ℕ := ((cellNumbering Y).symm k).val.2

abbrev W (d n : ℕ) := (Fin n → Fin d) → ℂ

noncomputable def colVec (Y : Partition d n) (z : Fin n → Fin d) : W d n :=
  fun y => ∑ b ∈ columnPermutations Y,
    (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) * (if y = z ∘ b then (1 : ℂ) else 0)

lemma mem_col {Y : Partition d n} {b : Equiv.Perm (Fin n)} :
    b ∈ columnPermutations Y ↔ ∀ i, colOf Y (b i) = colOf Y i := by
  simp [columnPermutations, colOf]

lemma col_mul {Y : Partition d n} {a b : Equiv.Perm (Fin n)} (ha : a ∈ columnPermutations Y)
    (hb : b ∈ columnPermutations Y) : a * b ∈ columnPermutations Y := by
  rw [mem_col] at *
  intro i
  simp only [Equiv.Perm.mul_apply]
  rw [ha, hb]

lemma col_inv {Y : Partition d n} {a : Equiv.Perm (Fin n)} (ha : a ∈ columnPermutations Y) :
    a⁻¹ ∈ columnPermutations Y := by
  rw [mem_col] at *
  intro i
  simpa using (ha (a⁻¹ i)).symm

lemma colVec_comp_swap (Y : Partition d n) (z : Fin n → Fin d) (τ : Equiv.Perm (Fin n))
    (hτ : τ ∈ columnPermutations Y) (hsign : Equiv.Perm.sign τ = -1) :
    colVec Y (z ∘ τ) = - colVec Y z := by
  funext y
  simp only [colVec, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun b => τ * b) (fun b => τ⁻¹ * b) ?_ ?_ ?_ ?_ ?_
  · intro b hb; exact col_mul hτ hb
  · intro b hb; exact col_mul (col_inv hτ) hb
  · intro b _; simp
  · intro b _; simp
  · intro b _
    have hc : z ∘ ⇑(τ * b) = (z ∘ τ) ∘ b := by rw [Equiv.Perm.coe_mul]; rfl
    rw [hc, Equiv.Perm.sign_mul, hsign]
    push_cast
    ring
lemma hw_val (Y : Partition d n) (k : Fin n) : (highestWeightWord Y k).val = rowOf Y k := rfl
lemma mem_row {Y : Partition d n} {a : Equiv.Perm (Fin n)} :
    a ∈ rowPermutations Y ↔ ∀ i, rowOf Y (a i) = rowOf Y i := by
  simp [rowPermutations, rowOf]

lemma row_mul {Y : Partition d n} {a b : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations Y)
    (hb : b ∈ rowPermutations Y) : a * b ∈ rowPermutations Y := by
  rw [mem_row] at *
  intro i
  simp only [Equiv.Perm.mul_apply]
  rw [ha, hb]

lemma row_inv {Y : Partition d n} {a : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations Y) :
    a⁻¹ ∈ rowPermutations Y := by
  rw [mem_row] at *
  intro i
  simpa using (ha (a⁻¹ i)).symm

lemma hw_comp_row (Y : Partition d n) (a : Equiv.Perm (Fin n)) (ha : a ∈ rowPermutations Y)
    (k : Fin n) : highestWeightWord Y (a k) = highestWeightWord Y k :=
  Fin.ext ((mem_row.mp ha) k)

lemma perm_eq_iff (x y : Fin n → Fin d) (e : Equiv.Perm (Fin n)) :
    (x = y ∘ e.symm) ↔ (y = x ∘ e) := by
  constructor
  · rintro rfl; funext i; simp
  · rintro rfl; funext i; simp

lemma rowT_eq (Y : Partition d n) (x : Fin n → Fin d) :
    (fun y => tensorYoungOperator Y x y) = ∑ a ∈ rowPermutations Y, colVec Y (x ∘ a) := by
  funext y
  simp only [tensorYoungOperator, Matrix.sum_apply, Matrix.smul_apply, tensorPermutation,
    Matrix.of_apply, smul_eq_mul, Finset.sum_apply, colVec]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  apply if_congr _ rfl rfl
  rw [perm_eq_iff, Equiv.Perm.coe_mul]
  rfl

lemma colVec_eq_zero (Y : Partition d n) (z : Fin n → Fin d) (k k' : Fin n) (hne : k ≠ k')
    (hcol : colOf Y k = colOf Y k') (hz : z k = z k') : colVec Y z = 0 := by
  set τ := Equiv.swap k k' with hτdef
  have hτ : τ ∈ columnPermutations Y := by
    rw [mem_col]; intro i
    rcases eq_or_ne i k with rfl | h1
    · simp [τ, hcol]
    rcases eq_or_ne i k' with rfl | h2
    · simp [τ, hcol]
    · simp [τ, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hsign : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap hne
  have hzτ : z ∘ τ = z := by
    funext i
    rcases eq_or_ne i k with rfl | h1
    · simp [τ, hz]
    rcases eq_or_ne i k' with rfl | h2
    · simp [τ, hz]
    · simp [τ, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have key := colVec_comp_swap Y z τ hτ hsign
  rw [hzτ] at key
  funext y
  have hy := congrFun key y
  simp only [Pi.neg_apply] at hy
  show colVec Y z y = 0
  linear_combination (1 / 2 : ℂ) * hy

lemma colinj_of_colVec_ne (Y : Partition d n) (z : Fin n → Fin d) (h : colVec Y z ≠ 0) :
    ∀ k k', colOf Y k = colOf Y k' → z k = z k' → k = k' := by
  intro k k' hc hz
  by_contra hne
  exact h (colVec_eq_zero Y z k k' hne hc hz)

noncomputable def extR (r : Fin d → ℝ) : ℕ → ℝ := fun i => if h : i < d then r ⟨i, h⟩ else 0

lemma extR_fin (r : Fin d → ℝ) (i : Fin d) : extR r i.val = r i := by
  simp [extR, i.isLt]

lemma extR_nonneg {r : Fin d → ℝ} (hnn : ∀ j, 0 ≤ r j) (i : ℕ) : 0 ≤ extR r i := by
  unfold extR
  split_ifs
  · exact hnn _
  · exact le_rfl

lemma extR_anti {r : Fin d → ℝ} (hanti : Antitone r) (hnn : ∀ j, 0 ≤ r j) : Antitone (extR r) := by
  intro i j hij
  by_cases hj : j < d
  · have hi : i < d := lt_of_le_of_lt hij hj
    simp only [extR, dif_pos hi, dif_pos hj]
    exact hanti (Fin.mk_le_mk.mpr hij)
  · have : extR r j = 0 := by simp [extR, hj]
    rw [this]
    exact extR_nonneg hnn i

lemma prod_le_range (R : ℕ → ℝ) (hR : Antitone R) (h0 : ∀ i, 0 ≤ R i) (S : Finset ℕ) :
    ∏ v ∈ S, R v ≤ ∏ v ∈ range S.card, R v := by
  refine Finset.induction_on_max S (by simp) ?_
  intro a s ha ih
  have has : a ∉ s := fun h => lt_irrefl a (ha a h)
  rw [prod_insert has, card_insert_of_notMem has, prod_range_succ, mul_comm]
  have hcard : s.card ≤ a := by
    have hsub : s ⊆ range a := fun x hx => mem_range.mpr (ha x hx)
    simpa using card_le_card hsub
  exact mul_le_mul ih (hR hcard) (h0 a) (prod_nonneg fun i _ => h0 i)

lemma eq_range_of_down (S : Finset ℕ) (h : ∀ a ∈ S, ∀ b < a, b ∈ S) : S = range S.card := by
  have hsub : S ⊆ range S.card := by
    intro a ha
    rw [mem_range]
    have hs : range (a + 1) ⊆ S := by
      intro b hb
      have hb' := mem_range.mp hb
      by_cases hba : b = a
      · subst hba; exact ha
      · exact h a ha b (by omega)
    have := card_le_card hs
    simp at this
    omega
  exact eq_of_subset_of_card_le hsub (by simp)

lemma col_bound (Y : Partition d n) (r : Fin d → ℝ) (hanti : Antitone r) (hnn : ∀ j, 0 ≤ r j)
    (z : Fin n → Fin d) (hz : ∀ k k', colOf Y k = colOf Y k' → z k = z k' → k = k') :
    ∏ k, r (z k) ≤ ∏ k, r (highestWeightWord Y k) := by
  have hR := extR_anti hanti hnn
  have h0 := extR_nonneg hnn
  have hL : ∏ k, r (z k) = ∏ j ∈ univ.image (colOf Y),
      ∏ k ∈ univ.filter (fun k => colOf Y k = j), extR r (z k).val := by
    rw [prod_fiberwise_of_maps_to (fun k _ => mem_image_of_mem _ (mem_univ k))]
    exact prod_congr rfl fun k _ => (extR_fin r (z k)).symm
  have hRt : ∏ k, r (highestWeightWord Y k) = ∏ j ∈ univ.image (colOf Y),
      ∏ k ∈ univ.filter (fun k => colOf Y k = j), extR r (rowOf Y k) := by
    rw [prod_fiberwise_of_maps_to (fun k _ => mem_image_of_mem _ (mem_univ k))]
    exact prod_congr rfl fun k _ => (extR_fin r (highestWeightWord Y k)).symm
  rw [hL, hRt]
  refine prod_le_prod (fun j _ => prod_nonneg fun k _ => h0 _) (fun j _ => ?_)
  have hinjz : Set.InjOn (fun k => (z k).val) (univ.filter (fun k => colOf Y k = j) : Finset (Fin n)) := by
    intro k hk k' hk' h
    rw [Finset.mem_coe, mem_filter] at hk hk'
    exact hz k k' (hk.2.trans hk'.2.symm) (Fin.ext h)
  have hinjr : Set.InjOn (rowOf Y) (univ.filter (fun k => colOf Y k = j) : Finset (Fin n)) := by
    intro k hk k' hk' h
    rw [Finset.mem_coe, mem_filter] at hk hk'
    apply (cellNumbering Y).symm.injective
    apply Subtype.ext
    exact Prod.ext h (hk.2.trans hk'.2.symm)
  have hA : ∏ k ∈ univ.filter (fun k => colOf Y k = j), extR r (z k).val =
      ∏ v ∈ (univ.filter (fun k => colOf Y k = j)).image (fun k => (z k).val), extR r v :=
    (prod_image hinjz).symm
  have hB : ∏ k ∈ univ.filter (fun k => colOf Y k = j), extR r (rowOf Y k) =
      ∏ v ∈ (univ.filter (fun k => colOf Y k = j)).image (rowOf Y), extR r v :=
    (prod_image hinjr).symm
  have hdown : (univ.filter (fun k => colOf Y k = j)).image (rowOf Y) =
      range ((univ.filter (fun k => colOf Y k = j)).image (rowOf Y)).card := by
    apply eq_range_of_down
    intro a ha b hb
    obtain ⟨k, hk, rfl⟩ := mem_image.mp ha
    have hkF : colOf Y k = j := (mem_filter.mp hk).2
    have hcell : (rowOf Y k, colOf Y k) ∈ Y.val := ((cellNumbering Y).symm k).property
    have hmem : (b, colOf Y k) ∈ Y.val := Y.val.up_left_mem (le_of_lt hb) le_rfl hcell
    refine mem_image.mpr ⟨cellNumbering Y ⟨(b, colOf Y k), hmem⟩, ?_, ?_⟩
    · rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      simp only [colOf, Equiv.symm_apply_apply]
      exact hkF
    · simp only [rowOf, Equiv.symm_apply_apply]
  rw [hA, hB, hdown, card_image_of_injOn hinjr]
  calc ∏ v ∈ (univ.filter (fun k => colOf Y k = j)).image (fun k => (z k).val), extR r v
      ≤ ∏ v ∈ range ((univ.filter (fun k => colOf Y k = j)).image (fun k => (z k).val)).card,
          extR r v := prod_le_range _ hR h0 _
    _ = _ := by rw [card_image_of_injOn hinjz]

lemma card_row (Y : Partition d n) (i : ℕ) :
    (univ.filter (fun k : Fin n => rowOf Y k = i)).card = Y.val.rowLen i := by
  rw [YoungDiagram.rowLen_eq_card]
  refine card_bij (fun k _ => ((cellNumbering Y).symm k).val) ?_ ?_ ?_
  · intro k hk
    rw [mem_filter] at hk
    rw [YoungDiagram.mem_row_iff]
    exact ⟨((cellNumbering Y).symm k).property, hk.2⟩
  · intro k _ k' _ h
    exact (cellNumbering Y).symm.injective (Subtype.ext h)
  · intro c hc
    rw [YoungDiagram.mem_row_iff] at hc
    refine ⟨cellNumbering Y ⟨c, hc.1⟩, ?_, ?_⟩
    · rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      simp only [rowOf, Equiv.symm_apply_apply]
      exact hc.2
    · simp

lemma prod_hw (Y : Partition d n) (r : Fin d → ℝ) :
    ∏ k, r (highestWeightWord Y k) = ∏ i : Fin d, r i ^ Y.val.rowLen i.val := by
  rw [← prod_fiberwise univ (highestWeightWord Y)]
  refine prod_congr rfl fun i _ => ?_
  refine (prod_eq_pow_card (fun k hk => congrArg r (mem_filter.mp hk).2)).trans ?_
  have hf : (univ.filter fun k => highestWeightWord Y k = i) =
      univ.filter (fun k => rowOf Y k = i.val) :=
    filter_congr (fun k _ => ⟨fun h => by rw [← hw_val, h], fun h => Fin.ext (by rw [hw_val, h])⟩)
  rw [hf, card_row]

lemma apply_single (A : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (v w : Fin n → Fin d) :
    (Matrix.toEuclideanLin A (EuclideanSpace.single v (1 : ℂ))) w = A w v := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]

lemma supp_bound (Y : Partition d n) (r : Fin d → ℝ) (hanti : Antitone r) (hnn : ∀ j, 0 ≤ r j)
    (x : EuclideanSpace ℂ (Fin n → Fin d)) (hx : x ∈ schurModule Y) (w : Fin n → Fin d)
    (hw : x w ≠ 0) : ∏ k, r (w k) ≤ ∏ k, r (highestWeightWord Y k) := by
  obtain ⟨y, rfl⟩ := hx
  by_contra hcon
  apply hw
  have hall : ∀ a ∈ rowPermutations Y, colVec Y (w ∘ a) = 0 := by
    intro a _
    by_contra hne
    apply hcon
    calc ∏ k, r (w k) = ∏ k, r ((w ∘ a) k) := (Equiv.prod_comp a (fun k => r (w k))).symm
      _ ≤ _ := col_bound Y r hanti hnn _ (colinj_of_colVec_ne Y _ hne)
  have hrow : ∀ v, tensorYoungOperator Y w v = 0 := by
    intro v
    have := congrFun (rowT_eq Y w) v
    rw [this, sum_eq_zero hall]
    rfl
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, hrow]

lemma hw_ne (Y : Partition d n) :
    tensorYoungOperator Y (highestWeightWord Y) (highestWeightWord Y) ≠ 0 := by
  rw [show tensorYoungOperator Y (highestWeightWord Y) (highestWeightWord Y) =
      (∑ a ∈ rowPermutations Y, colVec Y (highestWeightWord Y ∘ a)) (highestWeightWord Y) from
      congrFun (rowT_eq Y _) _, Finset.sum_apply]
  have h1 : ∀ a ∈ rowPermutations Y, colVec Y (highestWeightWord Y ∘ a) (highestWeightWord Y) = 1 := by
    intro a ha
    have hc : highestWeightWord Y ∘ a = highestWeightWord Y := funext fun k => hw_comp_row Y a ha k
    rw [hc]
    simp only [colVec]
    rw [sum_eq_single 1]
    · simp
    · intro b hb hb1
      rw [if_neg, mul_zero]
      intro hh
      apply hb1
      refine Equiv.ext fun k => ?_
      have hr : rowOf Y (b k) = rowOf Y k := (congrArg Fin.val (congrFun hh k)).symm
      have hc : colOf Y (b k) = colOf Y k := mem_col.mp hb k
      have : (cellNumbering Y).symm (b k) = (cellNumbering Y).symm k := Subtype.ext (Prod.ext hr hc)
      rw [Equiv.Perm.one_apply]
      exact (cellNumbering Y).symm.injective this
    · intro h; exact absurd (mem_col.mpr fun i => rfl) h
  rw [sum_congr rfl h1, sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (card_pos.mpr ⟨1, mem_row.mpr fun i => rfl⟩).ne'

lemma hw_supp (Y : Partition d n) (w : Fin n → Fin d)
    (h : tensorYoungOperator Y w (highestWeightWord Y) ≠ 0) :
    ∃ σ : Equiv.Perm (Fin n), w = highestWeightWord Y ∘ σ := by
  by_contra hne
  simp only [not_exists] at hne
  apply h
  rw [show tensorYoungOperator Y w (highestWeightWord Y) =
      (∑ a ∈ rowPermutations Y, colVec Y (w ∘ a)) (highestWeightWord Y) from
      congrFun (rowT_eq Y _) _, Finset.sum_apply]
  refine sum_eq_zero fun a _ => ?_
  simp only [colVec]
  refine sum_eq_zero fun b _ => ?_
  rw [if_neg, mul_zero]
  intro hh
  apply hne (a * b)⁻¹
  funext k
  rw [hh]
  simp

lemma exists_hw_unit (Y : Partition d n) (r : Fin d → ℝ) :
    ∃ u : schurModule Y, ‖u‖ = 1 ∧ ∀ w, (u : EuclideanSpace ℂ (Fin n → Fin d)) w ≠ 0 →
      ∏ k, r (w k) = ∏ k, r (highestWeightWord Y k) := by
  obtain ⟨m, hmv⟩ : ∃ m : schurModule Y, (m : EuclideanSpace ℂ (Fin n → Fin d)) =
      Matrix.toEuclideanLin (tensorYoungOperator Y)
        (EuclideanSpace.single (highestWeightWord Y) (1 : ℂ)) := ⟨⟨_, ⟨_, rfl⟩⟩, rfl⟩
  have hm : m ≠ 0 := by
    intro h
    have h2 := congrArg (fun x : schurModule Y =>
      (x : EuclideanSpace ℂ (Fin n → Fin d)) (highestWeightWord Y)) h
    simp only [hmv, apply_single, Submodule.coe_zero] at h2
    exact hw_ne Y (by simpa using h2)
  refine ⟨((‖m‖⁻¹ : ℝ) : ℂ) • m, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hm)
  · intro w hw
    have h0 : tensorYoungOperator Y w (highestWeightWord Y) ≠ 0 := by
      intro h
      apply hw
      rw [Submodule.coe_smul, hmv]
      simp [apply_single, h]
    obtain ⟨σ, rfl⟩ := hw_supp Y w h0
    exact Equiv.prod_comp σ (fun k => r (highestWeightWord Y k))

lemma trace_eq (Y : Partition d n) (r : Fin d → ℝ) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (schurModule Y)) :
    LinearMap.trace ℂ (schurModule Y)
        (polynomialRepresentation Y (Matrix.diagonal (fun j => (r j : ℂ)))) =
      ∑ w : Fin n → Fin d, ((∏ k, r (w k) : ℝ) : ℂ) *
        ((∑ i, ‖(b i : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2 : ℝ) : ℂ) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  have key : ∀ i, inner ℂ (b i)
      (polynomialRepresentation Y (Matrix.diagonal (fun j => (r j : ℂ))) (b i)) =
      ∑ w : Fin n → Fin d, ((∏ k, r (w k) : ℝ) : ℂ) *
        ((‖(b i : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Submodule.coe_inner, rep_apply, piKron_diagonal, PiLp.inner_apply]
    refine sum_congr rfl fun w _ => ?_
    simp only [Matrix.toLpLin_apply, Matrix.mulVec_diagonal, PiLp.toLp_apply]
    rw [RCLike.inner_apply', mul_left_comm, Complex.conj_mul']
    push_cast
    ring
  simp only [key]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  push_cast
  rw [mul_sum]

theorem main (Y : Partition d n) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) (hanti : Antitone r)
    (hnn : ∀ j, 0 ≤ r j) :
    let χ : ℂ := LinearMap.trace ℂ (schurModule Y)
      (polynomialRepresentation Y (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U))
    χ.im = 0 ∧
    ∏ i : Fin d, r i ^ Y.val.rowLen i.val ≤ χ.re ∧
    χ.re ≤ (Module.finrank ℂ (schurModule Y) : ℝ) * ∏ i : Fin d, r i ^ Y.val.rowLen i.val := by
  classical
  intro χ
  obtain ⟨u, hu1, hsupp⟩ := exists_hw_unit Y r
  have hon : Orthonormal ℂ ((↑) : ({u} : Set (schurModule Y)) → schurModule Y) := by
    rw [orthonormal_subtype_iff_ite]
    intro v hv w hw
    rw [Set.mem_singleton_iff] at hv hw
    subst hv hw
    simp [inner_self_eq_norm_sq_to_K, hu1]
  obtain ⟨S, b, hsub, hb⟩ := hon.exists_orthonormalBasis_extension
  have hχ : χ = ((∑ w : Fin n → Fin d, (∏ k, r (w k)) *
      (∑ i, ‖(b i : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2) : ℝ) : ℂ) := by
    show LinearMap.trace ℂ (schurModule Y)
      (polynomialRepresentation Y (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U)) = _
    rw [rep_mul, rep_mul, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc, ← rep_mul,
      (Matrix.mem_unitaryGroup_iff').mp hU, rep_one, LinearMap.id_comp, trace_eq Y r b]
    push_cast
    rfl
  rw [hχ, Complex.ofReal_im, Complex.ofReal_re, ← prod_hw Y r]
  have hY0 : 0 ≤ ∏ k, r (highestWeightWord Y k) := prod_nonneg fun k _ => hnn _
  refine ⟨rfl, ?_, ?_⟩
  · have hu : u ∈ S := hsub (Set.mem_singleton u)
    have hbu : b ⟨u, hu⟩ = u := by rw [hb]
    have hc : ∀ w, ‖(u : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2 ≤
        ∑ i, ‖(b i : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2 := by
      intro w
      have := Finset.single_le_sum
        (f := fun i => ‖(b i : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2)
        (fun i _ => sq_nonneg _) (mem_univ ⟨u, hu⟩)
      simpa [hbu] using this
    have hnorm : ∑ w, ‖(u : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq,
        show ‖(u : EuclideanSpace ℂ (Fin n → Fin d))‖ = 1 from hu1]
      simp
    calc ∏ k, r (highestWeightWord Y k)
        = ∑ w, (∏ k, r (highestWeightWord Y k)) *
            ‖(u : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2 := by
          rw [← mul_sum, hnorm, mul_one]
      _ ≤ _ := by
          refine sum_le_sum fun w _ => ?_
          by_cases h0 : (u : EuclideanSpace ℂ (Fin n → Fin d)) w = 0
          · rw [h0, norm_zero]
            simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
            exact mul_nonneg (prod_nonneg fun k _ => hnn _) (sum_nonneg fun i _ => sq_nonneg _)
          · rw [hsupp w h0]
            exact mul_le_mul_of_nonneg_left (hc w) hY0
  · have hsum : ∑ w : Fin n → Fin d, ∑ i, ‖(b i : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2 =
        (Module.finrank ℂ (schurModule Y) : ℝ) := by
      rw [Finset.sum_comm, Module.finrank_eq_card_basis b.toBasis]
      have h1 : ∀ i, ∑ w, ‖(b i : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2 = 1 := by
        intro i
        rw [← EuclideanSpace.norm_sq_eq,
          show ‖((b i : schurModule Y) : EuclideanSpace ℂ (Fin n → Fin d))‖ = 1 from b.orthonormal.1 i]
        simp
      simp only [h1]
      simp
    rw [← hsum, sum_mul]
    refine sum_le_sum fun w _ => ?_
    rw [mul_comm (∑ i, _) _]
    by_cases hc0 : ∑ i, ‖(b i : EuclideanSpace ℂ (Fin n → Fin d)) w‖ ^ 2 = 0
    · rw [hc0]; simp
    · obtain ⟨i, _, hi⟩ := exists_ne_zero_of_sum_ne_zero hc0
      have hbi : (b i : EuclideanSpace ℂ (Fin n → Fin d)) w ≠ 0 := by
        intro h; apply hi; simp [h]
      exact mul_le_mul_of_nonneg_right (supp_bound Y r hanti hnn _ (b i).2 w hbi)
        (sum_nonneg fun i _ => sq_nonneg _)

end KW21

open QAlgorithms QAlgorithms.Schur in
theorem solution {d N : ℕ} (Y : Partition d N) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) (hanti : Antitone r)
    (hnn : ∀ j, 0 ≤ r j) :
    let χ : ℂ := LinearMap.trace ℂ (schurModule Y)
      (polynomialRepresentation Y (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U))
    χ.im = 0 ∧
    ∏ i : Fin d, r i ^ Y.val.rowLen i.val ≤ χ.re ∧
    χ.re ≤ (Module.finrank ℂ (schurModule Y) : ℝ) * ∏ i : Fin d, r i ^ Y.val.rowLen i.val := by
  exact KW21.main Y U hU r hanti hnn
