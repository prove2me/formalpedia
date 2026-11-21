-- Prove2me | solution 1 for LinExchangeSP.ZPlus.lemma_7_4_iv
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:55:00.562205+00:00
-- url     : https://prove2.me/submissions/f3bef83c-6658-4dbc-b64f-66b0f386bd57

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace Aux_LinExchangeSP_ZPlus_lemma_7_4_iv

open LinExchangeSP.ZPlus

theorem offdiag_nonpos {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (h b : Fin t)
    (hhb : h ≠ b) : M h b ≤ 0 := by
  have hne : (h : ℕ) ≠ (b : ℕ) := fun heq => hhb (Fin.ext heq)
  exact hM.1 h b hne

theorem reach_of_mem_D {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i l : Fin t) (hl : l ∈ D M i) :
    Relation.ReflTransGen (arcH M) i l := by
  classical
  unfold D at hl
  rw [Finset.mem_filter] at hl
  exact hl.2

/-- Maximum principle for left vectors of a Z₊ matrix. -/
theorem maxp {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (i : Fin t)
    (P : Fin t → Prop) (hPi : ¬ P i) (hPD : ∀ l, P l → Relation.ReflTransGen (arcH M) i l)
    (y : Fin t → ℚ) (hsupp : ∀ l, ¬ P l → y l = 0)
    (hcol : ∀ j, P j → ∑ l, y l * M l j ≤ 0) : ∀ l, y l ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, hh0⟩ := hcon
  have hne : (Finset.univ : Finset (Fin t)).Nonempty := ⟨i, Finset.mem_univ _⟩
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = Finset.univ.sup' hne y := ⟨_, rfl⟩
  have hle : ∀ h, y h ≤ μ := fun h => by
    rw [hμdef]; exact Finset.le_sup' y (Finset.mem_univ h)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne y
  rw [← hμdef] at hj
  have hμpos : 0 < μ := lt_of_lt_of_le hh0 (hle h0)
  have hPof : ∀ x, y x = μ → P x := by
    intro x hx
    by_contra hPx
    have := hsupp x hPx
    linarith
  have hprop : ∀ a b, arcH M a b → y b = μ → y a = μ := by
    intro a b hab hb
    have hPb := hPof b hb
    have hT : ∀ h ∈ (Finset.univ : Finset (Fin t)), 0 ≤ (y h - μ) * M h b := by
      intro h _
      by_cases hhb : h = b
      · rw [hhb, hb, sub_self, zero_mul]
      · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hle h])
          (offdiag_nonpos M hM h b hhb)
    have hsumT : ∑ h, (y h - μ) * M h b = ∑ h, y h * M h b - μ * ∑ h, M h b := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro h _
      ring
    have hcs : 0 ≤ ∑ h, M h b := hM.2 b
    have hcb := hcol b hPb
    have hle0 : ∑ h, (y h - μ) * M h b ≤ 0 := by
      rw [hsumT]
      have := mul_nonneg hμpos.le hcs
      linarith
    have hzero : ∑ h, (y h - μ) * M h b = 0 :=
      le_antisymm hle0 (Finset.sum_nonneg hT)
    have hTa := (Finset.sum_eq_zero_iff_of_nonneg hT).mp hzero a (Finset.mem_univ _)
    have hab2 : M a b < 0 := hab.2
    rcases mul_eq_zero.mp hTa with h | h
    · linarith
    · linarith
  have hpath : ∀ x, Relation.ReflTransGen (arcH M) i x → y x = μ → y i = μ := by
    intro x hx
    induction hx with
    | refl => exact id
    | tail _ hbc ih =>
      intro hc
      exact ih (hprop _ _ hbc hc)
  have hyi := hpath j (hPD j (hPof j hj.symm)) hj.symm
  have := hsupp i hPi
  linarith

/-- Solvability with nonnegative solutions of the system reduced to `D \ {i}`. -/
theorem solve_S {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (i : Fin t)
    (b : Fin t → ℚ) (hb0 : ∀ l, 0 ≤ b l) :
    ∃ x : Fin t → ℚ, (∀ l, 0 ≤ x l) ∧ (∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → x l = b l) ∧
      (∀ l, (l ∈ D M i ∧ l ≠ i) →
        ∑ j, (if (j ∈ D M i ∧ j ≠ i) then M l j else 0) * x j = b l) := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Fin t → Prop, P = fun l => l ∈ D M i ∧ l ≠ i := ⟨_, rfl⟩
  have hPiff : ∀ l, P l ↔ (l ∈ D M i ∧ l ≠ i) := fun l => by rw [hP]
  have hPi : ¬ P i := fun h => ((hPiff i).mp h).2 rfl
  have hPD : ∀ l, P l → Relation.ReflTransGen (arcH M) i l :=
    fun l hl => reach_of_mem_D M i l ((hPiff l).mp hl).1
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin t) (Fin t) ℚ,
      A = fun l j => if P l ∧ P j then M l j else if l = j then 1 else 0 := ⟨_, rfl⟩
  have hAe : ∀ l j, A l j = if P l ∧ P j then M l j else if l = j then 1 else 0 :=
    fun l j => by rw [hA]
  have hvm_out : ∀ (y : Fin t → ℚ) j, ¬ P j → Matrix.vecMul y A j = y j := by
    intro y j hj
    simp only [Matrix.vecMul, dotProduct]
    have : ∀ l, y l * A l j = if l = j then y l else 0 := by
      intro l
      rw [hAe, if_neg (fun h => hj h.2)]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun l _ => this l), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hvm_in : ∀ (y : Fin t → ℚ) j, P j → (∀ l, ¬ P l → y l = 0) →
      Matrix.vecMul y A j = ∑ l, y l * M l j := by
    intro y j hj hy
    simp only [Matrix.vecMul, dotProduct]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : P l
    · rw [hAe, if_pos ⟨hl, hj⟩]
    · rw [hy l hl, zero_mul, zero_mul]
  have hmv_out : ∀ (q : Fin t → ℚ) l, ¬ P l → Matrix.mulVec A q l = q l := by
    intro q l hl
    simp only [Matrix.mulVec, dotProduct]
    have : ∀ j, A l j * q j = if l = j then q j else 0 := by
      intro j
      rw [hAe, if_neg (fun h => hl h.1)]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hmv_in : ∀ (q : Fin t → ℚ) l, P l →
      Matrix.mulVec A q l = ∑ j, (if (j ∈ D M i ∧ j ≠ i) then M l j else 0) * q j := by
    intro q l hl
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [hAe]
    by_cases hPj : P j
    · rw [if_pos ⟨hl, hPj⟩, if_pos ((hPiff j).mp hPj)]
    · have hlj : l ≠ j := fun h => hPj (by rw [← h]; exact hl)
      rw [if_neg (fun h => hPj h.2), if_neg hlj, if_neg (fun h => hPj ((hPiff j).mpr h))]
  have hneg_sum : ∀ (y : Fin t → ℚ) j, ∑ l, -y l * M l j = -∑ l, y l * M l j := by
    intro y j
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hinjv : Function.Injective A.vecMul := by
    intro y1 y2 h12
    have h12' : Matrix.vecMul y1 A = Matrix.vecMul y2 A := h12
    have hk : Matrix.vecMul (y1 - y2) A = 0 := by
      rw [Matrix.sub_vecMul, h12', sub_self]
    obtain ⟨y, hy⟩ : ∃ y, y = y1 - y2 := ⟨_, rfl⟩
    rw [← hy] at hk
    have hsupp : ∀ l, ¬ P l → y l = 0 := by
      intro l hl
      have := congrFun hk l
      rw [hvm_out y l hl] at this
      exact this
    have hcol0 : ∀ j, P j → ∑ l, y l * M l j = 0 := by
      intro j hj
      have := congrFun hk j
      rw [hvm_in y j hj hsupp] at this
      exact this
    have h1 := maxp M hM i P hPi hPD y hsupp (fun j hj => le_of_eq (hcol0 j hj))
    have h2 := maxp M hM i P hPi hPD (fun l => -y l)
      (fun l hl => by show -y l = 0; rw [hsupp l hl, neg_zero])
      (fun j hj => by
        show ∑ l, -y l * M l j ≤ 0
        rw [hneg_sum, hcol0 j hj, neg_zero])
    have hy0 : y = 0 := by
      funext l
      have a1 := h1 l
      have a2 : -y l ≤ 0 := h2 l
      simp only [Pi.zero_apply]
      linarith
    rw [hy] at hy0
    exact sub_eq_zero.mp hy0
  have hU : IsUnit A := Matrix.vecMul_injective_iff_isUnit.mp hinjv
  have hsurj := Matrix.mulVec_surjective_iff_isUnit.mpr hU
  have hsurjv := Matrix.vecMul_surjective_iff_isUnit.mpr hU
  obtain ⟨x, hx⟩ := hsurj b
  have hxe : ∀ l, Matrix.mulVec A x l = b l := fun l => congrFun hx l
  have hxnn : ∀ k, 0 ≤ x k := by
    intro k
    by_cases hPk : P k
    · obtain ⟨y, hy⟩ := hsurjv (Pi.single k 1)
      have hy' : Matrix.vecMul y A = (Pi.single k (1 : ℚ) : Fin t → ℚ) := hy
      have hye : ∀ j, Matrix.vecMul y A j = (Pi.single k (1 : ℚ) : Fin t → ℚ) j :=
        fun j => congrFun hy' j
      have hysupp : ∀ l, ¬ P l → y l = 0 := by
        intro l hl
        have hlk : l ≠ k := fun h => hl (by rw [h]; exact hPk)
        rw [← hvm_out y l hl, hye, Pi.single_eq_of_ne hlk]
      have hynn : ∀ l, 0 ≤ y l := by
        have h2 := maxp M hM i P hPi hPD (fun l => -y l)
          (fun l hl => by show -y l = 0; rw [hysupp l hl, neg_zero])
          (fun j hj => by
            show ∑ l, -y l * M l j ≤ 0
            have h3 := hye j
            rw [hvm_in y j hj hysupp] at h3
            rw [hneg_sum, h3]
            by_cases hjk : j = k
            · rw [hjk, Pi.single_eq_same]; norm_num
            · rw [Pi.single_eq_of_ne hjk]; norm_num)
        intro l
        have h4 : -y l ≤ 0 := h2 l
        linarith
      have hdot : x k = dotProduct y b := by
        have e1 : dotProduct (Pi.single k (1 : ℚ) : Fin t → ℚ) x = x k := by
          rw [single_dotProduct, one_mul]
        rw [← e1, ← hy', ← Matrix.dotProduct_mulVec, hx]
      rw [hdot]
      unfold dotProduct
      exact Finset.sum_nonneg (fun l _ => mul_nonneg (hynn l) (hb0 l))
    · rw [← hmv_out x k hPk, hxe]
      exact hb0 k
  refine ⟨x, hxnn, ?_, ?_⟩
  · intro l hl
    have hPl : ¬ P l := fun h => hl ((hPiff l).mp h)
    rw [← hmv_out x l hPl, hxe]
  · intro l hl
    have hPl : P l := (hPiff l).mpr hl
    rw [← hmv_in x l hPl, hxe]

end Aux_LinExchangeSP_ZPlus_lemma_7_4_iv

open LinExchangeSP.ZPlus Aux_LinExchangeSP_ZPlus_lemma_7_4_iv in
theorem solution {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (γ : Fin t → ℚ) (hγ : ∀ i, 0 < γ i) (i : Fin t) (hi : InT3 M i) :
    ∃ r : Fin t → ℝ, (∀ l, 0 ≤ r l) ∧ (∀ l, rowVal M r l ≤ (γ l : ℝ)) ∧
      ∀ l ∈ D M i, l ≠ i → rowVal M r l = (γ l : ℝ) := by
  classical
  obtain ⟨x, hx0, hxout, hxin⟩ := solve_S M hM i
    (fun l => if (l ∈ D M i ∧ l ≠ i) then γ l else 0)
    (fun l => by
      show 0 ≤ (if (l ∈ D M i ∧ l ≠ i) then γ l else 0)
      split_ifs
      · exact (hγ l).le
      · exact le_rfl)
  have hxz : ∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → x l = 0 := by
    intro l hl
    rw [hxout l hl]
    show (if (l ∈ D M i ∧ l ≠ i) then γ l else 0) = 0
    rw [if_neg hl]
  -- the full row sums equal the reduced ones
  have hfull : ∀ l, ∑ j, M l j * x j =
      ∑ j, (if (j ∈ D M i ∧ j ≠ i) then M l j else 0) * x j := by
    intro l
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : (j ∈ D M i ∧ j ≠ i)
    · rw [if_pos hj]
    · rw [if_neg hj, hxz j hj, mul_zero, zero_mul]
  have hrow : ∀ l, rowVal M (fun j => (x j : ℝ)) l = ((∑ j, M l j * x j : ℚ) : ℝ) := by
    intro l
    unfold rowVal
    simp only [Rat.cast_sum, Rat.cast_mul]
  have hin : ∀ l, (l ∈ D M i ∧ l ≠ i) → ∑ j, M l j * x j = γ l := by
    intro l hl
    rw [hfull, hxin l hl]
    show (if (l ∈ D M i ∧ l ≠ i) then γ l else 0) = γ l
    rw [if_pos hl]
  have hout : ∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → ∑ j, M l j * x j ≤ 0 := by
    intro l hl
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : (j ∈ D M i ∧ j ≠ i)
    · have hlj : l ≠ j := fun h => hl (by rw [h]; exact hj)
      exact mul_nonpos_of_nonpos_of_nonneg (offdiag_nonpos M hM l j hlj) (hx0 j)
    · rw [hxz j hj, mul_zero]
  refine ⟨fun j => (x j : ℝ), fun l => by show (0 : ℝ) ≤ (x l : ℝ); exact_mod_cast hx0 l, ?_, ?_⟩
  · intro l
    rw [hrow]
    by_cases hl : (l ∈ D M i ∧ l ≠ i)
    · exact le_of_eq (by rw [hin l hl])
    · have h1 := hout l hl
      have h2 := hγ l
      have h3 : (∑ j, M l j * x j) ≤ γ l := by linarith
      exact_mod_cast h3
  · intro l hl hli
    rw [hrow, hin l ⟨hl, hli⟩]
