-- Prove2me | solution 1 for LinExchangeSP.ZPlus.lemma_7_4_iii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:11:30.870288+00:00
-- url     : https://prove2.me/submissions/a8247159-d9fd-4417-be9a-dd9a03400bf9

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace Aux_LinExchangeSP_ZPlus_lemma_7_4_iii

open LinExchangeSP.ZPlus

theorem offdiag_nonpos {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (h b : Fin t)
    (hhb : h ≠ b) : (M h b : ℝ) ≤ 0 := by
  have hne : (h : ℕ) ≠ (b : ℕ) := fun heq => hhb (Fin.ext heq)
  exact_mod_cast hM.1 h b hne

theorem colsum_nonneg {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (b : Fin t) :
    0 ≤ ∑ h, (M h b : ℝ) := by
  have := hM.2 b
  exact_mod_cast this

/-- Maximum principle for left null-type vectors of a Z₊ matrix. -/
theorem maxp {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (i : Fin t)
    (P : Fin t → Prop) (hPi : ¬ P i) (hPD : ∀ l, P l → Relation.ReflTransGen (arcH M) i l)
    (y : Fin t → ℝ) (hsupp : ∀ l, ¬ P l → y l = 0)
    (hcol : ∀ j, P j → ∑ l, y l * (M l j : ℝ) ≤ 0) : ∀ l, y l ≤ 0 := by
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
  -- propagation along an arc
  have hprop : ∀ a b, arcH M a b → y b = μ → y a = μ := by
    intro a b hab hb
    have hPb := hPof b hb
    have hT : ∀ h ∈ (Finset.univ : Finset (Fin t)), 0 ≤ (y h - μ) * (M h b : ℝ) := by
      intro h _
      by_cases hhb : h = b
      · rw [hhb, hb, sub_self, zero_mul]
      · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hle h])
          (offdiag_nonpos M hM h b hhb)
    have hsumT : ∑ h, (y h - μ) * (M h b : ℝ) =
        ∑ h, y h * (M h b : ℝ) - μ * ∑ h, (M h b : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro h _
      ring
    have hcs := colsum_nonneg M hM b
    have hcb := hcol b hPb
    have hle0 : ∑ h, (y h - μ) * (M h b : ℝ) ≤ 0 := by
      rw [hsumT]
      have := mul_nonneg hμpos.le hcs
      linarith
    have hzero : ∑ h, (y h - μ) * (M h b : ℝ) = 0 :=
      le_antisymm hle0 (Finset.sum_nonneg hT)
    have hTa := (Finset.sum_eq_zero_iff_of_nonneg hT).mp hzero a (Finset.mem_univ _)
    have hab2 : (M a b : ℝ) < 0 := by exact_mod_cast hab.2
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

theorem reach_of_mem_D {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i l : Fin t) (hl : l ∈ D M i) :
    Relation.ReflTransGen (arcH M) i l := by
  classical
  unfold D at hl
  rw [Finset.mem_filter] at hl
  exact hl.2


/-- Solvability with nonnegative solutions of the system reduced to `D \ {i}`. -/
theorem solve_S {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (i : Fin t)
    (b : Fin t → ℝ) (hb0 : ∀ l, 0 ≤ b l) :
    ∃ x : Fin t → ℝ, (∀ l, 0 ≤ x l) ∧ (∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → x l = b l) ∧
      (∀ l, (l ∈ D M i ∧ l ≠ i) →
        ∑ j, (if (j ∈ D M i ∧ j ≠ i) then (M l j : ℝ) else 0) * x j = b l) ∧
      (∀ z : Fin t → ℝ, (∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → z l = b l) →
        (∀ l, (l ∈ D M i ∧ l ≠ i) →
          ∑ j, (if (j ∈ D M i ∧ j ≠ i) then (M l j : ℝ) else 0) * z j = b l) → z = x) := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Fin t → Prop, P = fun l => l ∈ D M i ∧ l ≠ i := ⟨_, rfl⟩
  have hPiff : ∀ l, P l ↔ (l ∈ D M i ∧ l ≠ i) := fun l => by rw [hP]
  have hPi : ¬ P i := fun h => ((hPiff i).mp h).2 rfl
  have hPD : ∀ l, P l → Relation.ReflTransGen (arcH M) i l :=
    fun l hl => reach_of_mem_D M i l ((hPiff l).mp hl).1
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin t) (Fin t) ℝ,
      A = fun l j => if P l ∧ P j then (M l j : ℝ) else if l = j then 1 else 0 := ⟨_, rfl⟩
  have hAe : ∀ l j, A l j = if P l ∧ P j then (M l j : ℝ) else if l = j then 1 else 0 :=
    fun l j => by rw [hA]
  have hvm_out : ∀ (y : Fin t → ℝ) j, ¬ P j → Matrix.vecMul y A j = y j := by
    intro y j hj
    simp only [Matrix.vecMul, dotProduct]
    have : ∀ l, y l * A l j = if l = j then y l else 0 := by
      intro l
      rw [hAe, if_neg (fun h => hj h.2)]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun l _ => this l), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hvm_in : ∀ (y : Fin t → ℝ) j, P j → (∀ l, ¬ P l → y l = 0) →
      Matrix.vecMul y A j = ∑ l, y l * (M l j : ℝ) := by
    intro y j hj hy
    simp only [Matrix.vecMul, dotProduct]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : P l
    · rw [hAe, if_pos ⟨hl, hj⟩]
    · rw [hy l hl, zero_mul, zero_mul]
  have hmv_out : ∀ (q : Fin t → ℝ) l, ¬ P l → Matrix.mulVec A q l = q l := by
    intro q l hl
    simp only [Matrix.mulVec, dotProduct]
    have : ∀ j, A l j * q j = if l = j then q j else 0 := by
      intro j
      rw [hAe, if_neg (fun h => hl h.1)]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hmv_in : ∀ (q : Fin t → ℝ) l, P l →
      Matrix.mulVec A q l = ∑ j, (if (j ∈ D M i ∧ j ≠ i) then (M l j : ℝ) else 0) * q j := by
    intro q l hl
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [hAe]
    by_cases hPj : P j
    · rw [if_pos ⟨hl, hPj⟩, if_pos ((hPiff j).mp hPj)]
    · have hlj : l ≠ j := fun h => hPj (by rw [← h]; exact hl)
      rw [if_neg (fun h => hPj h.2), if_neg hlj, if_neg (fun h => hPj ((hPiff j).mpr h))]
  have hneg_sum : ∀ (y : Fin t → ℝ) j, ∑ l, -y l * (M l j : ℝ) = -∑ l, y l * (M l j : ℝ) := by
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
    have hcol0 : ∀ j, P j → ∑ l, y l * (M l j : ℝ) = 0 := by
      intro j hj
      have := congrFun hk j
      rw [hvm_in y j hj hsupp] at this
      exact this
    have h1 := maxp M hM i P hPi hPD y hsupp (fun j hj => le_of_eq (hcol0 j hj))
    have h2 := maxp M hM i P hPi hPD (fun l => -y l)
      (fun l hl => by show -y l = 0; rw [hsupp l hl, neg_zero])
      (fun j hj => by
        show ∑ l, -y l * (M l j : ℝ) ≤ 0
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
      have hy' : Matrix.vecMul y A = (Pi.single k (1 : ℝ) : Fin t → ℝ) := hy
      have hye : ∀ j, Matrix.vecMul y A j = (Pi.single k (1 : ℝ) : Fin t → ℝ) j :=
        fun j => congrFun hy' j
      have hysupp : ∀ l, ¬ P l → y l = 0 := by
        intro l hl
        have hlk : l ≠ k := fun h => hl (by rw [h]; exact hPk)
        rw [← hvm_out y l hl, hye, Pi.single_eq_of_ne hlk]
      have hynn : ∀ l, 0 ≤ y l := by
        have h2 := maxp M hM i P hPi hPD (fun l => -y l)
          (fun l hl => by show -y l = 0; rw [hysupp l hl, neg_zero])
          (fun j hj => by
            show ∑ l, -y l * (M l j : ℝ) ≤ 0
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
        have e1 : dotProduct (Pi.single k (1 : ℝ) : Fin t → ℝ) x = x k := by
          rw [single_dotProduct, one_mul]
        rw [← e1, ← hy', ← Matrix.dotProduct_mulVec, hx]
      rw [hdot]
      unfold dotProduct
      exact Finset.sum_nonneg (fun l _ => mul_nonneg (hynn l) (hb0 l))
    · rw [← hmv_out x k hPk, hxe]
      exact hb0 k
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hU
  refine ⟨x, hxnn, ?_, ?_, ?_⟩
  · intro l hl
    have hPl : ¬ P l := fun h => hl ((hPiff l).mp h)
    rw [← hmv_out x l hPl, hxe]
  · intro l hl
    have hPl : P l := (hPiff l).mpr hl
    rw [← hmv_in x l hPl, hxe]
  · intro z hzout hzin
    apply hinj
    have hx' : Matrix.mulVec A x = b := hx
    show Matrix.mulVec A z = Matrix.mulVec A x
    rw [hx']
    funext l
    by_cases hPl : P l
    · rw [hmv_in z l hPl]
      exact hzin l ((hPiff l).mp hPl)
    · rw [hmv_out z l hPl]
      exact hzout l (fun h => hPl ((hPiff l).mpr h))



theorem exists_q {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (i : Fin t) :
    ∃ q : Fin t → ℝ, (∀ l, 0 ≤ q l) ∧ (∀ l ∈ D M i, l ≠ i → rowVal M q l = 0) ∧
      q i = 1 ∧ ∀ l, l ∉ D M i → q l = 0 := by
  classical
  have hiD : i ∈ D M i := self_mem_D M i
  obtain ⟨b, hb⟩ : ∃ b : Fin t → ℝ, b = fun l =>
      if (l ∈ D M i ∧ l ≠ i) then -(M l i : ℝ) else if l = i then 1 else 0 := ⟨_, rfl⟩
  have hbe : ∀ l, b l =
      if (l ∈ D M i ∧ l ≠ i) then -(M l i : ℝ) else if l = i then 1 else 0 :=
    fun l => by rw [hb]
  have hb0 : ∀ l, 0 ≤ b l := by
    intro l
    rw [hbe]
    split_ifs with h1 h2
    · have := offdiag_nonpos M hM l i h1.2
      linarith
    · exact zero_le_one
    · exact le_rfl
  obtain ⟨q, hq0, hqout', hqin, _⟩ := solve_S M hM i b hb0
  have hqi : q i = 1 := by
    rw [hqout' i (fun h => h.2 rfl), hbe, if_neg (fun h => h.2 rfl), if_pos rfl]
  have hqout : ∀ l, l ∉ D M i → q l = 0 := by
    intro l hl
    have hli : l ≠ i := fun h => hl (by rw [h]; exact hiD)
    rw [hqout' l (fun h => hl h.1), hbe, if_neg (fun h => hl h.1), if_neg hli]
  refine ⟨q, hq0, ?_, hqi, hqout⟩
  intro l hl hli
  have hS : (l ∈ D M i ∧ l ≠ i) := ⟨hl, hli⟩
  have hpt : ∀ j, (M l j : ℝ) * q j =
      (if (j ∈ D M i ∧ j ≠ i) then (M l j : ℝ) else 0) * q j +
        (if j = i then (M l j : ℝ) * q j else 0) := by
    intro j
    by_cases hji : j = i
    · rw [if_neg (fun h => h.2 hji), if_pos hji]
      ring
    · rw [if_neg hji]
      by_cases hj : (j ∈ D M i ∧ j ≠ i)
      · rw [if_pos hj]
        ring
      · have hjD : j ∉ D M i := fun hjD => hj ⟨hjD, hji⟩
        rw [if_neg hj, hqout j hjD]
        ring
  unfold rowVal
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, hqin l hS,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hqi, hbe, if_pos hS]
  ring

end Aux_LinExchangeSP_ZPlus_lemma_7_4_iii

open LinExchangeSP.ZPlus Aux_LinExchangeSP_ZPlus_lemma_7_4_iii in
theorem solution {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (γ : Fin t → ℚ) (hγ : ∀ i, 0 < γ i) (i : Fin t) (hi : InT2 M i) :
    ∃ r : Fin t → ℝ, (∀ l, 0 ≤ r l) ∧ (∀ l, rowVal M r l ≤ (γ l : ℝ)) ∧
      (∀ l ∈ D M i, rowVal M r l = (γ l : ℝ)) ∧ r i = kappa M γ i := by
  obtain ⟨q, hq0, hqD, hqi, hqout⟩ := exists_q M hM i
  classical
  obtain ⟨_, hrank⟩ := hi
  have hiD : i ∈ D M i := self_mem_D M i
  -- rows of D vanish outside D
  have hzeroM : ∀ l ∈ D M i, ∀ j, j ∉ D M i → M l j = 0 := by
    intro l hl j hj
    by_contra hne
    have hlj : l ≠ j := fun h => hj (by rw [← h]; exact hl)
    have hle : M l j ≤ 0 := hM.1 l j (fun heq => hlj (Fin.ext heq))
    have hneg : M l j < 0 := lt_of_le_of_ne hle hne
    apply hj
    unfold D
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (reach_of_mem_D M i l hl).tail (And.intro hlj hneg)⟩
  -- the principal submatrix on D is invertible
  obtain ⟨N, hN⟩ : ∃ N : Matrix {j // j ∈ D M i} {j // j ∈ D M i} ℚ,
      N = M.submatrix (fun r : {j // j ∈ D M i} => (r : Fin t))
        (fun r : {j // j ∈ D M i} => (r : Fin t)) :=
    ⟨_, rfl⟩
  have hli : LinearIndependent ℚ
      (M.submatrix (fun r : {j // j ∈ D M i} => (r : Fin t)) id).row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
      ← Matrix.rank_eq_finrank_span_row]
    unfold rowRank at hrank
    rw [hrank]
    simp
  have hNinj : Function.Injective N.vecMul := by
    intro y1 y2 h12
    have h12' : Matrix.vecMul y1 N = Matrix.vecMul y2 N := h12
    have hk : Matrix.vecMul (y1 - y2) N = 0 := by
      rw [Matrix.sub_vecMul, h12', sub_self]
    obtain ⟨y, hy⟩ : ∃ y, y = y1 - y2 := ⟨_, rfl⟩
    rw [← hy] at hk
    have hsum : ∑ l, y l • (M.submatrix (fun r : {j // j ∈ D M i} => (r : Fin t)) id).row l
        = 0 := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply,
        Matrix.submatrix_apply, id, Pi.zero_apply]
      by_cases hj : j ∈ D M i
      · have := congrFun hk ⟨j, hj⟩
        simp only [Matrix.vecMul, dotProduct, hN, Matrix.submatrix_apply, Pi.zero_apply] at this
        exact this
      · apply Finset.sum_eq_zero
        intro l _
        rw [hzeroM l l.2 j hj, mul_zero]
    have hy0 := Fintype.linearIndependent_iff.mp hli y hsum
    have hyz : y = 0 := funext hy0
    rw [hy] at hyz
    exact sub_eq_zero.mp hyz
  have hNU : IsUnit N := Matrix.vecMul_injective_iff_isUnit.mp hNinj
  have hNN : N * N⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (A := N) ((Matrix.isUnit_iff_isUnit_det (A := N)).mp hNU)
  obtain ⟨w, hw⟩ : ∃ w : {j // j ∈ D M i} → ℚ,
      w = Matrix.mulVec N⁻¹ (γ ∘ (fun r : {j // j ∈ D M i} => (r : Fin t))) := ⟨_, rfl⟩
  have hNw : Matrix.mulVec N w = γ ∘ (fun r : {j // j ∈ D M i} => (r : Fin t)) := by
    rw [hw, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec]
  have hkap : kappa M γ i = ((w ⟨i, hiD⟩ : ℚ) : ℝ) := by
    rw [hw, hN]
    rfl
  -- the solution of the D-system, extended by zero
  obtain ⟨x, hx⟩ : ∃ x : Fin t → ℚ, x = fun l => if hl : l ∈ D M i then w ⟨l, hl⟩ else 0 :=
    ⟨_, rfl⟩
  have hx_in : ∀ l (hl : l ∈ D M i), x l = w ⟨l, hl⟩ := fun l hl => by
    rw [hx]; exact dif_pos hl
  have hx_out : ∀ l, l ∉ D M i → x l = 0 := fun l hl => by
    rw [hx]; exact dif_neg hl
  have hxrow : ∀ l ∈ D M i, ∑ j, M l j * x j = γ l := by
    intro l hl
    have h1 : ∑ j, M l j * x j = ∑ j ∈ D M i, M l j * x j :=
      (Finset.sum_subset (Finset.subset_univ _)
        (fun j _ hj => by rw [hx_out j hj, mul_zero])).symm
    rw [h1, ← Finset.sum_coe_sort]
    have h2 := congrFun hNw ⟨l, hl⟩
    simp only [Matrix.mulVec, dotProduct, hN, Matrix.submatrix_apply, Function.comp_apply] at h2
    rw [← h2]
    apply Finset.sum_congr rfl
    intro j _
    rw [hx_in j.1 j.2]
  have hxi : ((x i : ℚ) : ℝ) = kappa M γ i := by rw [hkap, hx_in i hiD]
  -- z = x - κ q solves the system on D \ {i}
  obtain ⟨z, hz⟩ : ∃ z : Fin t → ℝ, z = fun l => (x l : ℝ) - kappa M γ i * q l := ⟨_, rfl⟩
  have hze : ∀ l, z l = (x l : ℝ) - kappa M γ i * q l := fun l => by rw [hz]
  have hrowz : ∀ l, rowVal M z l =
      ((∑ j, M l j * x j : ℚ) : ℝ) - kappa M γ i * rowVal M q l := by
    intro l
    unfold rowVal
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hze]
    ring
  have hz_out : ∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → z l = 0 := by
    intro l hl
    rw [hze]
    by_cases hlD : l ∈ D M i
    · have hli : l = i := by
        by_contra h
        exact hl ⟨hlD, h⟩
      rw [hli, hqi, hxi, mul_one, sub_self]
    · rw [hx_out l hlD, hqout l hlD]
      simp
  have hz_row : ∀ l, (l ∈ D M i ∧ l ≠ i) → rowVal M z l = (γ l : ℝ) := by
    intro l hl
    rw [hrowz, hxrow l hl.1, hqD l hl.1 hl.2, mul_zero, sub_zero]
  obtain ⟨b, hb⟩ : ∃ b : Fin t → ℝ,
      b = fun l => if (l ∈ D M i ∧ l ≠ i) then (γ l : ℝ) else 0 := ⟨_, rfl⟩
  have hbe : ∀ l, b l = if (l ∈ D M i ∧ l ≠ i) then (γ l : ℝ) else 0 := fun l => by rw [hb]
  have hb0 : ∀ l, 0 ≤ b l := by
    intro l
    rw [hbe]
    split_ifs
    · exact_mod_cast (hγ l).le
    · exact le_rfl
  obtain ⟨xs, hxs0, _, _, huniq⟩ := solve_S M hM i b hb0
  have hzx : z = xs := by
    apply huniq
    · intro l hl
      rw [hbe, if_neg hl, hz_out l hl]
    · intro l hl
      rw [hbe, if_pos hl, ← hz_row l hl]
      unfold rowVal
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : (j ∈ D M i ∧ j ≠ i)
      · rw [if_pos hj]
      · rw [if_neg hj, hz_out j hj]; simp
  have hz_nn : ∀ l, 0 ≤ z l := by
    rw [hzx]
    exact hxs0
  -- column sums over D are nonnegative
  have hcolD : ∀ j ∈ D M i, 0 ≤ ∑ l ∈ D M i, (M l j : ℝ) := by
    intro j hj
    have hall := colsum_nonneg M hM j
    have hsplit := Finset.sum_sdiff (Finset.subset_univ (D M i)) (f := fun l => (M l j : ℝ))
    have hneg : ∑ l ∈ Finset.univ \ D M i, (M l j : ℝ) ≤ 0 := by
      apply Finset.sum_nonpos
      intro l hl
      have hlj : l ≠ j := fun h => (Finset.mem_sdiff.mp hl).2 (by rw [h]; exact hj)
      exact offdiag_nonpos M hM l j hlj
    linarith
  -- M_i q ≥ 0
  have hsumq : 0 ≤ ∑ l ∈ D M i, rowVal M q l := by
    unfold rowVal
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg
    intro j _
    rw [← Finset.sum_mul]
    by_cases hj : j ∈ D M i
    · exact mul_nonneg (hcolD j hj) (hq0 j)
    · rw [hqout j hj, mul_zero]
  rw [← Finset.add_sum_erase _ _ hiD] at hsumq
  have hErq : ∑ l ∈ (D M i).erase i, rowVal M q l = 0 :=
    Finset.sum_eq_zero (fun l hl => by
      have h := Finset.mem_erase.mp hl
      exact hqD l h.2 h.1)
  rw [hErq, add_zero] at hsumq
  -- M_i z ≤ 0
  have hziz : z i = 0 := hz_out i (fun h => h.2 rfl)
  have hMiz : rowVal M z i ≤ 0 := by
    unfold rowVal
    apply Finset.sum_nonpos
    intro j _
    by_cases hji : j = i
    · simp [hji, hziz]
    · exact mul_nonpos_of_nonpos_of_nonneg (offdiag_nonpos M hM i j (Ne.symm hji)) (hz_nn j)
  have hzi : rowVal M z i = (γ i : ℝ) - kappa M γ i * rowVal M q i := by
    rw [hrowz, hxrow i hiD]
  have hγi : (0 : ℝ) < (γ i : ℝ) := by exact_mod_cast hγ i
  have hkpos : 0 ≤ kappa M γ i := by
    by_contra hk
    push_neg at hk
    have : kappa M γ i * rowVal M q i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk.le hsumq
    linarith
  -- x = z + κ q is nonnegative
  have hxnn : ∀ l, (0 : ℝ) ≤ (x l : ℝ) := by
    intro l
    have h1 := hze l
    have h2 := hz_nn l
    have h3 := mul_nonneg hkpos (hq0 l)
    linarith
  have hrowx : ∀ l, rowVal M (fun j => (x j : ℝ)) l = ((∑ j, M l j * x j : ℚ) : ℝ) := by
    intro l
    unfold rowVal
    simp only [Rat.cast_sum, Rat.cast_mul]
  refine ⟨fun j => (x j : ℝ), fun l => hxnn l, ?_, ?_, ?_⟩
  · intro l
    by_cases hl : l ∈ D M i
    · exact le_of_eq (by rw [hrowx, hxrow l hl])
    · have hle : rowVal M (fun j => (x j : ℝ)) l ≤ 0 := by
        unfold rowVal
        apply Finset.sum_nonpos
        intro j _
        by_cases hj : j ∈ D M i
        · have hlj : l ≠ j := fun h => hl (by rw [h]; exact hj)
          exact mul_nonpos_of_nonpos_of_nonneg (offdiag_nonpos M hM l j hlj) (hxnn j)
        · show (M l j : ℝ) * (x j : ℝ) ≤ 0
          rw [hx_out j hj]
          simp
      have := hγ l
      have h2 : (0 : ℝ) < (γ l : ℝ) := by exact_mod_cast this
      linarith
  · intro l hl
    rw [hrowx, hxrow l hl]
  · exact hxi
