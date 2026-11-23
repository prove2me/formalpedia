-- Prove2me | solution 1 for GraphSimOT.Gaps.theorem_38
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:21:23.602578+00:00
-- url     : https://prove2.me/submissions/766f3b2f-ff15-484c-bcf3-50dd0ef28272

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_CutRounding
import Theorems.Thm_GraphSimOT_Gaps_lemma_36
import Theorems.Thm_GraphSimOT_Gaps_lemma_37

open Matrix GraphSimOT.Gaps

namespace Theorem38Aux

lemma cutNorm_nonneg {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (M : Matrix R C ℝ) : 0 ≤ FriezeKannan.CutDecomp.cutNorm M :=
  (abs_nonneg _).trans
    (Finset.le_sup' (fun p : Finset R × Finset C => |FriezeKannan.CutDecomp.blockSum M p.1 p.2|)
      (Finset.mem_univ (∅, ∅)))

lemma cutNorm_add_le {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (M1 M2 : Matrix R C ℝ) :
    FriezeKannan.CutDecomp.cutNorm (M1 + M2) ≤
      FriezeKannan.CutDecomp.cutNorm M1 + FriezeKannan.CutDecomp.cutNorm M2 := by
  apply Finset.sup'_le
  intro p _
  have hsum : FriezeKannan.CutDecomp.blockSum (M1 + M2) p.1 p.2 =
      FriezeKannan.CutDecomp.blockSum M1 p.1 p.2 +
      FriezeKannan.CutDecomp.blockSum M2 p.1 p.2 := by
    unfold FriezeKannan.CutDecomp.blockSum
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
  rw [hsum]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact Finset.le_sup'
      (fun q : Finset R × Finset C => |FriezeKannan.CutDecomp.blockSum M1 q.1 q.2|)
      (Finset.mem_univ p)
  · exact Finset.le_sup'
      (fun q : Finset R × Finset C => |FriezeKannan.CutDecomp.blockSum M2 q.1 q.2|)
      (Finset.mem_univ p)

lemma cutNorm_transpose_le {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) :
    FriezeKannan.CutDecomp.cutNorm Kᵀ ≤ FriezeKannan.CutDecomp.cutNorm K := by
  apply Finset.sup'_le
  intro p _
  have hswap : FriezeKannan.CutDecomp.blockSum Kᵀ p.1 p.2 =
      FriezeKannan.CutDecomp.blockSum K p.2 p.1 := by
    unfold FriezeKannan.CutDecomp.blockSum
    simp only [Matrix.transpose_apply]
    exact Finset.sum_comm
  rw [hswap]
  exact Finset.le_sup'
    (fun q : Finset (Fin n) × Finset (Fin n) => |FriezeKannan.CutDecomp.blockSum K q.1 q.2|)
    (Finset.mem_univ (p.2, p.1))

lemma cutNorm_ds_mul_le {n : ℕ} (R K : Matrix (Fin n) (Fin n) ℝ)
    (hR : R ∈ doublyStochastic ℝ (Fin n)) :
    FriezeKannan.CutDecomp.cutNorm (R * K) ≤ FriezeKannan.CutDecomp.cutNorm K := by
  classical
  rw [mem_doublyStochastic_iff_sum] at hR
  rcases hR with ⟨hRnn, -, hRcol⟩
  apply Finset.sup'_le
  intro p _
  let w : Fin n → ℝ := fun j => ∑ i ∈ p.1, R i j
  have hw0 : ∀ j : Fin n, 0 ≤ w j := fun j => Finset.sum_nonneg fun i _ => hRnn i j
  have hw1 : ∀ j : Fin n, w j ≤ 1 := by
    intro j
    calc
      w j ≤ ∑ i : Fin n, R i j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hRnn i j)
      _ = 1 := hRcol j
  let c : Fin n → ℝ := fun j => ∑ k ∈ p.2, K j k
  have hrew : FriezeKannan.CutDecomp.blockSum (R * K) p.1 p.2 = ∑ j : Fin n, w j * c j := by
    unfold FriezeKannan.CutDecomp.blockSum
    simp only [Matrix.mul_apply]
    calc
      ∑ i ∈ p.1, ∑ k ∈ p.2, ∑ j : Fin n, R i j * K j k
          = ∑ i ∈ p.1, ∑ j : Fin n, R i j * c j := by
              apply Finset.sum_congr rfl; intro i _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro j _
              simp only [c, Finset.mul_sum]
      _ = ∑ j : Fin n, w j * c j := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _
            simp only [w, Finset.sum_mul]
  rw [hrew]
  apply abs_le.mpr
  constructor
  · let Jneg : Finset (Fin n) := Finset.univ.filter (fun j => c j < 0)
    have h1 : -(∑ j : Fin n, w j * c j) ≤ -(∑ j ∈ Jneg, c j) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
          ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => c j < 0)]
      have hnp : ∑ j ∈ Finset.univ.filter (fun j => ¬ c j < 0), -(w j * c j) ≤ 0 := by
        apply Finset.sum_nonpos; intro j hj
        have hcj : 0 ≤ c j := not_lt.mp (Finset.mem_filter.mp hj).2
        have hwj : 0 ≤ w j := hw0 j
        nlinarith
      have hln : ∑ j ∈ Jneg, -(w j * c j) ≤ ∑ j ∈ Jneg, -(c j) := by
        apply Finset.sum_le_sum; intro j hj
        have hcj : c j < 0 := (Finset.mem_filter.mp hj).2
        have hwj : w j ≤ 1 := hw1 j
        nlinarith
      linarith
    have h2 : -(∑ j ∈ Jneg, c j) ≤ FriezeKannan.CutDecomp.cutNorm K := by
      change -FriezeKannan.CutDecomp.blockSum K Jneg p.2 ≤ _
      refine (neg_le_abs _).trans ?_
      exact Finset.le_sup'
        (fun q : Finset (Fin n) × Finset (Fin n) => |FriezeKannan.CutDecomp.blockSum K q.1 q.2|)
        (Finset.mem_univ (Jneg, p.2))
    linarith
  · let Jpos : Finset (Fin n) := Finset.univ.filter (fun j => 0 < c j)
    have h1 : ∑ j : Fin n, w j * c j ≤ ∑ j ∈ Jpos, c j := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => 0 < c j)]
      have hnp : ∑ j ∈ Finset.univ.filter (fun j => ¬ 0 < c j), w j * c j ≤ 0 := by
        apply Finset.sum_nonpos; intro j hj
        have hcj : c j ≤ 0 := not_lt.mp (Finset.mem_filter.mp hj).2
        have hwj : 0 ≤ w j := hw0 j
        nlinarith
      have hlp : ∑ j ∈ Jpos, w j * c j ≤ ∑ j ∈ Jpos, c j := by
        apply Finset.sum_le_sum; intro j hj
        have hcj : 0 < c j := (Finset.mem_filter.mp hj).2
        have hwj : w j ≤ 1 := hw1 j
        nlinarith
      linarith
    have h2 : ∑ j ∈ Jpos, c j ≤ FriezeKannan.CutDecomp.cutNorm K := by
      change FriezeKannan.CutDecomp.blockSum K Jpos p.2 ≤ _
      refine (le_abs_self _).trans ?_
      exact Finset.le_sup'
        (fun q : Finset (Fin n) × Finset (Fin n) => |FriezeKannan.CutDecomp.blockSum K q.1 q.2|)
        (Finset.mem_univ (Jpos, p.2))
    linarith

lemma perm_conj_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n))
    (i k : Fin n) :
    (π.permMatrix ℝ * M * (π.permMatrix ℝ)ᵀ) i k = M (π i) (π k) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  rw [Finset.sum_eq_single (π k)]
  · simp only [ ↓reduceIte, mul_one]
    rw [Finset.sum_eq_single (π i)]
    · simp
    · intro j _ hj; simp [hj.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro l _ hl; simp [hl.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma cutNorm_Bmat_perm_le {n : ℕ} (G H : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    FriezeKannan.CutDecomp.cutNorm (Bmat G H (π.permMatrix ℝ)) ≤
      FriezeKannan.CutDecomp.cutNorm
        (adj G - π.permMatrix ℝ * adj H * (π.permMatrix ℝ)ᵀ) := by
  classical
  set P := π.permMatrix ℝ
  apply Finset.sup'_le
  intro p _
  let X : Finset (Fin n) := Finset.univ.filter (fun i => (i, π i) ∈ p.1)
  let Y : Finset (Fin n) := Finset.univ.filter (fun k => (k, π k) ∈ p.2)
  have hsum : FriezeKannan.CutDecomp.blockSum (Bmat G H P) p.1 p.2 =
      FriezeKannan.CutDecomp.blockSum (adj G - P * adj H * Pᵀ) X Y := by
    unfold FriezeKannan.CutDecomp.blockSum Bmat disc
    have h1 : (∑ a ∈ p.1, ∑ b ∈ p.2,
        P a.1 a.2 * (adj G a.1 b.1 - adj H a.2 b.2) * P b.1 b.2) =
        ∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
          (if a ∈ p.1 then P a.1 a.2 else 0) * (adj G a.1 b.1 - adj H a.2 b.2) *
            (if b ∈ p.2 then P b.1 b.2 else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ p.1)]
      · apply Finset.sum_congr rfl; intro a ha
        simp only [ha, ite_true]
        rw [← Finset.sum_subset (Finset.subset_univ p.2)]
        · apply Finset.sum_congr rfl; intro b hb
          simp [hb]
        · intro b _ hb; simp [hb]
      · intro a _ ha; simp [ha]
    rw [h1, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have hP_val : ∀ (u v : Fin n), P u v = if π u = v then 1 else 0 := by
      intro u v
      simp [P, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp_rw [hP_val]
    have houter : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        (if (i, j) ∈ p.1 then if π i = j then (1 : ℝ) else 0 else 0) *
          (adj G i k - adj H j l) *
          (if (k, l) ∈ p.2 then if π k = l then (1 : ℝ) else 0 else 0) =
        ∑ i : Fin n, (if i ∈ X then (1 : ℝ) else 0) *
          (∑ k : Fin n, (if k ∈ Y then (1 : ℝ) else 0) * (adj G i k - adj H (π i) (π k))) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_eq_single (π i)]
      · have hiX : ((i, π i) ∈ p.1) ↔ i ∈ X := by simp [X]
        simp only [ite_true, hiX, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_eq_single (π k)]
        · have hkY : ((k, π k) ∈ p.2) ↔ k ∈ Y := by simp [Y]
          simp only [ite_true, hkY]; ring
        · intro l _ hl; simp [hl.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro j _ hj; simp [hj.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [houter]
    rw [← Finset.sum_subset (Finset.subset_univ X)]
    · apply Finset.sum_congr rfl; intro i hi
      simp only [hi, ite_true, one_mul]
      rw [← Finset.sum_subset (Finset.subset_univ Y)]
      · apply Finset.sum_congr rfl; intro k hk
        simp only [hk, ite_true, one_mul, Matrix.sub_apply]
        dsimp only [P]
        rw [perm_conj_apply]
      · intro k _ hk; simp [hk]
    · intro i _ hi; simp [hi]
  rw [hsum]
  exact Finset.le_sup'
    (fun q : Finset (Fin n) × Finset (Fin n) =>
      |FriezeKannan.CutDecomp.blockSum (adj G - P * adj H * Pᵀ) q.1 q.2|)
    (Finset.mem_univ (X, Y))

lemma cutNorm_conj_proj_le {n : ℕ} (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (π : Equiv.Perm (Fin n)) :
    FriezeKannan.CutDecomp.cutNorm
      (π.permMatrix ℝ * (Qᵀ * adj G * Q - adj H) * (π.permMatrix ℝ)ᵀ) ≤
      FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) := by
  classical
  rw [mem_doublyStochastic_iff_sum] at hQ
  rcases hQ with ⟨-, -, hQcol⟩
  apply Finset.sup'_le
  intro p _
  let X' : Finset (Fin n) := p.1.image π
  let Y' : Finset (Fin n) := p.2.image π
  have hsum : FriezeKannan.CutDecomp.blockSum
      (π.permMatrix ℝ * (Qᵀ * adj G * Q - adj H) * (π.permMatrix ℝ)ᵀ) p.1 p.2 =
      FriezeKannan.CutDecomp.blockSum (Bmat G H Q)
        (Finset.univ ×ˢ X') (Finset.univ ×ˢ Y') := by
    unfold FriezeKannan.CutDecomp.blockSum
    have hconj : ∑ i ∈ p.1, ∑ k ∈ p.2,
        (π.permMatrix ℝ * (Qᵀ * adj G * Q - adj H) * (π.permMatrix ℝ)ᵀ) i k =
        ∑ j ∈ X', ∑ l ∈ Y', ((Qᵀ * adj G * Q) j l - adj H j l) := by
      simp_rw [perm_conj_apply]
      simp only [X', Y', Finset.sum_image (fun _ _ _ _ h => π.injective h), Matrix.sub_apply]
    rw [hconj]
    simp_rw [Finset.sum_product]
    calc
      ∑ j ∈ X', ∑ l ∈ Y', ((Qᵀ * adj G * Q) j l - adj H j l)
          = ∑ j ∈ X', ∑ l ∈ Y', ∑ i : Fin n, ∑ k : Fin n, Bmat G H Q (i, j) (k, l) := by
              apply Finset.sum_congr rfl; intro j _
              apply Finset.sum_congr rfl; intro l _
              have hQAQ : (Qᵀ * adj G * Q) j l =
                  ∑ i : Fin n, ∑ k : Fin n, Q i j * adj G i k * Q k l := by
                simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
                rw [Finset.sum_comm]
              have hB : adj H j l = ∑ i : Fin n, ∑ k : Fin n, Q i j * adj H j l * Q k l := by
                symm
                calc
                  ∑ i : Fin n, ∑ k : Fin n, Q i j * adj H j l * Q k l
                      = ∑ i : Fin n, (adj H j l * Q i j) * (∑ k : Fin n, Q k l) := by
                          apply Finset.sum_congr rfl; intro i _
                          rw [Finset.mul_sum]
                          apply Finset.sum_congr rfl; intro k _; ring
                  _ = adj H j l * (∑ i : Fin n, Q i j) * (∑ k : Fin n, Q k l) := by
                        rw [← Finset.sum_mul, ← Finset.mul_sum]
                  _ = adj H j l := by rw [hQcol j, hQcol l, mul_one, mul_one]
              rw [hQAQ, hB, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl; intro i _
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl; intro k _
              unfold Bmat disc; ring
      _ = ∑ j ∈ X', ∑ i : Fin n, ∑ k : Fin n, ∑ l ∈ Y', Bmat G H Q (i, j) (k, l) := by
            apply Finset.sum_congr rfl; intro j _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro i _
            exact Finset.sum_comm
      _ = ∑ i : Fin n, ∑ j ∈ X', ∑ k : Fin n, ∑ l ∈ Y', Bmat G H Q (i, j) (k, l) :=
            Finset.sum_comm
  rw [hsum]
  exact Finset.le_sup'
    (fun q : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) =>
      |FriezeKannan.CutDecomp.blockSum (Bmat G H Q) q.1 q.2|)
    (Finset.mem_univ (Finset.univ ×ˢ X', Finset.univ ×ˢ Y'))

lemma perm_mul_transpose_ds {n : ℕ} (π : Equiv.Perm (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n)) :
    π.permMatrix ℝ * Qᵀ ∈ doublyStochastic ℝ (Fin n) := by
  apply Submonoid.mul_mem
  · change π.permMatrix ℝ ∈ (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ))
    rw [doublyStochastic_eq_convexHull_permMatrix]
    exact subset_convexHull ℝ _ ⟨π, rfl⟩
  · rw [mem_doublyStochastic_iff_sum] at hQ ⊢
    rcases hQ with ⟨hQnn, hQrow, hQcol⟩
    refine ⟨fun i j => hQnn j i, fun i => hQcol i, fun j => hQrow j⟩

end Theorem38Aux

theorem solution (Cthin : ℝ) (_hC : 0 < Cthin) (hthin : IsThinConstant Cthin)
    {n : ℕ} (hn : 2 ≤ n) (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n)) :
    ∃ π : Equiv.Perm (Fin n), zeta G H (π.permMatrix ℝ) ≤
      (1 + 4 * (Cthin * Real.log (2 * n) * Real.log (Real.log (4 * n)))) * zeta G H Q := by
  classical
  set α : ℝ := Cthin * Real.log (2 * n) * Real.log (Real.log (4 * n))
  rcases hthin n hn Q hQ with ⟨α', hα'le, π, hthin'⟩
  refine ⟨π, ?_⟩
  have hQ' := hQ
  rw [mem_doublyStochastic_iff_sum] at hQ'
  rcases hQ' with ⟨hQnn, hQrow, hQcol⟩
  have hα_pos : 0 < α := hthin'.1.trans_le hα'le
  have hthin_α : IsThin α (π.permMatrix ℝ) Q := by
    refine ⟨hα_pos, fun X Y => (hthin'.2 X Y).trans ?_⟩
    apply mul_le_mul_of_nonneg_right hα'le
    unfold crossWeight
    exact add_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hQnn i j)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hQnn i j)
  set P : Matrix (Fin n) (Fin n) ℝ := π.permMatrix ℝ
  set R : Matrix (Fin n) (Fin n) ℝ := P * Qᵀ
  set E : Matrix (Fin n) (Fin n) ℝ := 1 - R
  have hR_ds : R ∈ doublyStochastic ℝ (Fin n) := Theorem38Aux.perm_mul_transpose_ds π Q hQ
  have hA_transpose : (adj G)ᵀ = adj G := by
    ext i j
    simp only [Matrix.transpose_apply, adj]
    by_cases h : G.Adj j i
    · simp [h, h.symm]
    · have h' : ¬ G.Adj i j := fun hij => h hij.symm
      simp [h, h']
  have hsplit1 : adj G - P * adj H * Pᵀ =
      (adj G - R * adj G * Rᵀ) + P * (Qᵀ * adj G * Q - adj H) * Pᵀ := by
    have hRAR : R * adj G * Rᵀ = P * (Qᵀ * adj G * Q) * Pᵀ := by
      simp only [R, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hRAR]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hsplit2 : adj G - R * adj G * Rᵀ = E * adj G + R * (E * adj G)ᵀ := by
    simp only [E, Matrix.sub_mul, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_sub,
      hA_transpose, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have hEA_bound : (1 / (n : ℝ) ^ 2) * FriezeKannan.CutDecomp.cutNorm (E * adj G) ≤
      2 * α * zeta G H Q := by
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [one_div_mul_eq_div, div_le_iff₀ hn2]
    apply Finset.sup'_le
    intro p _
    let y : Fin n → ℝ := fun k => if k ∈ p.2 then 1 else 0
    have hy : ∀ k : Fin n, 0 ≤ y k ∧ y k ≤ 1 := by
      intro k; simp only [y]; split_ifs <;> constructor <;> norm_num
    set x : Fin n → ℝ := adj G *ᵥ y
    let f : Fin n → ℝ := fun i => x i - (Qᵀ *ᵥ x) (π i)
    have hRx : ∀ i : Fin n, (R *ᵥ x) i = (Qᵀ *ᵥ x) (π i) := by
      intro i
      rw [← Matrix.mulVec_mulVec]
      simp only [P, Matrix.mulVec, dotProduct, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
        Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_eq_single (π i)]
      · simp
      · intro j _ hj; simp [hj.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hEA_row : ∀ i : Fin n, ∑ k ∈ p.2, (E * adj G) i k = f i := by
      intro i
      have h1 : ∑ k ∈ p.2, (E * adj G) i k = ((E * adj G) *ᵥ y) i := by
        simp only [Matrix.mulVec, dotProduct, y, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext k; simp
      rw [h1, ← Matrix.mulVec_mulVec]
      change ((1 - R) *ᵥ x) i = f i
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, hRx i]
    have hblock_f : FriezeKannan.CutDecomp.blockSum (E * adj G) p.1 p.2 = ∑ i ∈ p.1, f i := by
      unfold FriezeKannan.CutDecomp.blockSum
      exact Finset.sum_congr rfl fun i _ => hEA_row i
    have hf_sum0 : ∑ i : Fin n, f i = 0 := by
      simp only [f, Finset.sum_sub_distrib]
      have h1 : ∑ i : Fin n, (Qᵀ *ᵥ x) (π i) = ∑ j : Fin n, (Qᵀ *ᵥ x) j :=
        Fintype.sum_equiv π _ _ (fun _ => rfl)
      have h2 : ∑ j : Fin n, (Qᵀ *ᵥ x) j = ∑ i : Fin n, x i := by
        calc
          ∑ j : Fin n, (Qᵀ *ᵥ x) j = ∑ j : Fin n, ∑ i : Fin n, Q i j * x i := by
              simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
          _ = ∑ i : Fin n, x i * (∑ j : Fin n, Q i j) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j _; ring
          _ = ∑ i : Fin n, x i := by
              apply Finset.sum_congr rfl; intro i _
              rw [hQrow i, mul_one]
      linarith
    have hhalf : 2 * |∑ i ∈ p.1, f i| ≤ ∑ i : Fin n, |f i| := by
      have hcompl : ∑ i ∈ p.1, f i + ∑ i ∈ p.1ᶜ, f i = 0 := by
        rw [Finset.sum_add_sum_compl, hf_sum0]
      have hneg : ∑ i ∈ p.1ᶜ, f i = -(∑ i ∈ p.1, f i) := by linarith
      have habs_eq : |∑ i ∈ p.1ᶜ, f i| = |∑ i ∈ p.1, f i| := by rw [hneg, abs_neg]
      calc
        2 * |∑ i ∈ p.1, f i| = |∑ i ∈ p.1, f i| + |∑ i ∈ p.1ᶜ, f i| := by linarith
        _ ≤ (∑ i ∈ p.1, |f i|) + (∑ i ∈ p.1ᶜ, |f i|) :=
              add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
        _ = ∑ i : Fin n, |f i| := Finset.sum_add_sum_compl _ _
    have h36 := lemma_36 hn α π Q hQ hthin_α x (Qᵀ *ᵥ x)
    have h37 := lemma_37 hn G H Q hQ y hy
    have h37' : ∑ i : Fin n, ∑ j : Fin n, Q i j * |x i - (Qᵀ *ᵥ x) j| ≤
        4 * zeta G H Q * (n : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right h37 hn2.le
      have hcancel : (1 / (n : ℝ) ^ 2) *
          (∑ i : Fin n, ∑ j : Fin n, Q i j * |x i - (Qᵀ *ᵥ x) j|) * (n : ℝ) ^ 2 =
          ∑ i : Fin n, ∑ j : Fin n, Q i j * |x i - (Qᵀ *ᵥ x) j| := by
        have hn2' : (n : ℝ) ^ 2 ≠ 0 := hn2.ne'
        field_simp
      linarith
    have hcomb : ∑ i : Fin n, |f i| ≤ α * (4 * zeta G H Q * (n : ℝ) ^ 2) :=
      h36.trans (mul_le_mul_of_nonneg_left h37' hα_pos.le)
    rw [hblock_f]
    linarith
  have hARAR : (1 / (n : ℝ) ^ 2) *
      FriezeKannan.CutDecomp.cutNorm (adj G - R * adj G * Rᵀ) ≤ 4 * α * zeta G H Q := by
    have h1 : FriezeKannan.CutDecomp.cutNorm (adj G - R * adj G * Rᵀ) ≤
        2 * FriezeKannan.CutDecomp.cutNorm (E * adj G) := by
      rw [hsplit2]
      have ha := Theorem38Aux.cutNorm_add_le (E * adj G) (R * (E * adj G)ᵀ)
      have hb := Theorem38Aux.cutNorm_ds_mul_le R (E * adj G)ᵀ hR_ds
      have hc := Theorem38Aux.cutNorm_transpose_le (E * adj G)
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2)
    linarith
  unfold zeta
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hP_le := Theorem38Aux.cutNorm_Bmat_perm_le G H π
  have hadd := Theorem38Aux.cutNorm_add_le (adj G - R * adj G * Rᵀ)
    (P * (Qᵀ * adj G * Q - adj H) * Pᵀ)
  rw [← hsplit1] at hadd
  have hQ_le := Theorem38Aux.cutNorm_conj_proj_le G H Q hQ π
  have htot : FriezeKannan.CutDecomp.cutNorm (Bmat G H P) / (n : ℝ) ^ 2 ≤
      (1 / (n : ℝ) ^ 2) * FriezeKannan.CutDecomp.cutNorm (adj G - R * adj G * Rᵀ) +
      FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) / (n : ℝ) ^ 2 := by
    have hsum_cut : FriezeKannan.CutDecomp.cutNorm (Bmat G H P) ≤
        FriezeKannan.CutDecomp.cutNorm (adj G - R * adj G * Rᵀ) +
        FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) := by linarith
    calc
      FriezeKannan.CutDecomp.cutNorm (Bmat G H P) / (n : ℝ) ^ 2
          ≤ (FriezeKannan.CutDecomp.cutNorm (adj G - R * adj G * Rᵀ) +
              FriezeKannan.CutDecomp.cutNorm (Bmat G H Q)) / (n : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hsum_cut hn2.le
      _ = _ := by rw [add_div, one_div_mul_eq_div]
  change FriezeKannan.CutDecomp.cutNorm (Bmat G H P) / (n : ℝ) ^ 2 ≤
    (1 + 4 * α) * (FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) / (n : ℝ) ^ 2)
  change (1 / (n : ℝ) ^ 2) * FriezeKannan.CutDecomp.cutNorm (adj G - R * adj G * Rᵀ) ≤
    4 * α * (FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) / (n : ℝ) ^ 2) at hARAR
  linarith
