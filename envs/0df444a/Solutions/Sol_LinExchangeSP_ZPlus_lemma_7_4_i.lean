-- Prove2me | solution 1 for LinExchangeSP.ZPlus.lemma_7_4_i
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:47:38.201981+00:00
-- url     : https://prove2.me/submissions/433f28c8-5707-4fe9-9703-919036b34d13

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace Aux_LinExchangeSP_ZPlus_lemma_7_4_i

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

end Aux_LinExchangeSP_ZPlus_lemma_7_4_i

open LinExchangeSP.ZPlus Aux_LinExchangeSP_ZPlus_lemma_7_4_i in
theorem solution {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (i : Fin t) (hi : InT2 M i ∨ InT3 M i) :
    ∃! q : Fin t → ℝ, (∀ l, 0 ≤ q l) ∧ (∀ l ∈ D M i, l ≠ i → rowVal M q l = 0) ∧
      q i = 1 ∧ ∀ l, l ∉ D M i → q l = 0 := by
  classical
  -- index set D \ {i}
  obtain ⟨P, hP⟩ : ∃ P : Fin t → Prop, P = fun l => l ∈ D M i ∧ l ≠ i := ⟨_, rfl⟩
  have hPiff : ∀ l, P l ↔ (l ∈ D M i ∧ l ≠ i) := fun l => by rw [hP]
  have hPi : ¬ P i := fun h => ((hPiff i).mp h).2 rfl
  have hPD : ∀ l, P l → Relation.ReflTransGen (arcH M) i l :=
    fun l hl => reach_of_mem_D M i l ((hPiff l).mp hl).1
  have hiD : i ∈ D M i := self_mem_D M i
  -- the matrix of the reduced system
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin t) (Fin t) ℝ,
      A = fun l j => if P l ∧ P j then (M l j : ℝ) else if l = j then 1 else 0 := ⟨_, rfl⟩
  have hAe : ∀ l j, A l j = if P l ∧ P j then (M l j : ℝ) else if l = j then 1 else 0 :=
    fun l j => by rw [hA]
  obtain ⟨b, hb⟩ : ∃ b : Fin t → ℝ,
      b = fun l => if P l then -(M l i : ℝ) else if l = i then 1 else 0 := ⟨_, rfl⟩
  have hbe : ∀ l, b l = if P l then -(M l i : ℝ) else if l = i then 1 else 0 :=
    fun l => by rw [hb]
  -- formulas
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
  have hmv_in : ∀ (q : Fin t → ℝ) l, P l → (∀ j, j ∉ D M i → q j = 0) →
      ∑ j, (M l j : ℝ) * q j = Matrix.mulVec A q l + (M l i : ℝ) * q i := by
    intro q l hl hq
    have hli : l ≠ i := ((hPiff l).mp hl).2
    have hpt : ∀ j, (M l j : ℝ) * q j =
        A l j * q j + (if j = i then (M l j : ℝ) * q j else 0) := by
      intro j
      by_cases hji : j = i
      · rw [if_pos hji, hAe, if_neg (fun h => hPi (by rw [← hji]; exact h.2)),
          if_neg (fun h => hli (h.trans hji))]
        ring
      · rw [if_neg hji, hAe]
        by_cases hPj : P j
        · rw [if_pos ⟨hl, hPj⟩]; ring
        · have hjD : j ∉ D M i := fun hjD => hPj ((hPiff j).mpr ⟨hjD, hji⟩)
          rw [hq j hjD]
          simp
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
    simp only [Matrix.mulVec, dotProduct]
  -- injectivity of vecMul
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
        have := hcol0 j hj
        have e : ∑ l, -y l * (M l j : ℝ) = -∑ l, y l * (M l j : ℝ) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro l _
          ring
        rw [e, this, neg_zero])
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
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hU
  have hsurjv := Matrix.vecMul_surjective_iff_isUnit.mpr hU
  obtain ⟨q, hq⟩ := hsurj b
  have hqe : ∀ l, Matrix.mulVec A q l = b l := fun l => congrFun hq l
  -- properties of q
  have hqi : q i = 1 := by
    rw [← hmv_out q i hPi, hqe, hbe, if_neg hPi, if_pos rfl]
  have hqout : ∀ l, l ∉ D M i → q l = 0 := by
    intro l hl
    have hPl : ¬ P l := fun h => hl ((hPiff l).mp h).1
    have hli : l ≠ i := fun h => hl (by rw [h]; exact hiD)
    rw [← hmv_out q l hPl, hqe, hbe, if_neg hPl, if_neg hli]
  have hqrow : ∀ l ∈ D M i, l ≠ i → rowVal M q l = 0 := by
    intro l hl hli
    have hPl : P l := (hPiff l).mpr ⟨hl, hli⟩
    unfold rowVal
    rw [hmv_in q l hPl hqout, hqe, hbe, if_pos hPl, hqi]
    ring
  have hbnn : ∀ l, 0 ≤ b l := by
    intro l
    rw [hbe]
    split_ifs with h1 h2
    · have hli : l ≠ i := ((hPiff l).mp h1).2
      have := offdiag_nonpos M hM l i hli
      linarith
    · exact zero_le_one
    · exact le_rfl
  have hqnn : ∀ k, 0 ≤ q k := by
    intro k
    by_cases hPk : P k
    · obtain ⟨y, hy⟩ := hsurjv (Pi.single k 1)
      have hy' : Matrix.vecMul y A = Pi.single k (1 : ℝ) := hy
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
            have e : ∑ l, -y l * (M l j : ℝ) = -∑ l, y l * (M l j : ℝ) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro l _
              ring
            rw [e, h3]
            by_cases hjk : j = k
            · rw [hjk, Pi.single_eq_same]; norm_num
            · rw [Pi.single_eq_of_ne hjk]; norm_num)
        intro l
        have h4 : -y l ≤ 0 := h2 l
        linarith
      have hdot : q k = dotProduct y b := by
        have e1 : dotProduct (Pi.single k (1 : ℝ) : Fin t → ℝ) q = q k := by
          rw [single_dotProduct, one_mul]
        rw [← e1, ← hy', ← Matrix.dotProduct_mulVec, hq]
      rw [hdot]
      unfold dotProduct
      exact Finset.sum_nonneg (fun l _ => mul_nonneg (hynn l) (hbnn l))
    · rw [← hmv_out q k hPk, hqe]
      exact hbnn k
  refine ⟨q, ⟨hqnn, hqrow, hqi, hqout⟩, ?_⟩
  rintro q' ⟨_, hrow', hi', hout'⟩
  apply hinj
  rw [hq]
  funext l
  by_cases hPl : P l
  · have hl := (hPiff l).mp hPl
    have h1 := hmv_in q' l hPl hout'
    have h2 := hrow' l hl.1 hl.2
    unfold rowVal at h2
    rw [h2, hi'] at h1
    rw [hbe, if_pos hPl]
    linarith
  · rw [hmv_out q' l hPl, hbe, if_neg hPl]
    by_cases hli : l = i
    · rw [if_pos hli, hli, hi']
    · rw [if_neg hli]
      exact hout' l (fun hlD => hPl ((hPiff l).mpr ⟨hlD, hli⟩))
