-- Prove2me | solution 1 for LinExchangeSP.ZPlus.theorem_6_4_square
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:35:45.477718+00:00
-- url     : https://prove2.me/submissions/975c0b73-1e4f-46e0-9220-b7510bf632b6

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting

namespace Aux_LinExchangeSP_ZPlus_theorem_6_4_square

open LinExchangeSP.ZPlus

def arcH {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i j : Fin t) : Prop :=
  i ≠ j ∧ M i j < 0

open Classical in
noncomputable def D {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i : Fin t) : Finset (Fin t) :=
  Finset.univ.filter (fun j => Relation.ReflTransGen (arcH M) i j)

theorem self_mem_D {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i : Fin t) : i ∈ D M i := by
  classical
  simp [D, Relation.ReflTransGen.refl]

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
theorem solve_S {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (i : Fin t) :
    (∀ b : Fin t → ℚ, (∀ l, 0 ≤ b l) →
    ∃ x : Fin t → ℚ, (∀ l, 0 ≤ x l) ∧ (∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → x l = b l) ∧
      (∀ l, (l ∈ D M i ∧ l ≠ i) →
        ∑ j, (if (j ∈ D M i ∧ j ≠ i) then M l j else 0) * x j = b l)) ∧
    (∀ k, (k ∈ D M i ∧ k ≠ i) → ∃ y : Fin t → ℚ, (∀ l, 0 ≤ y l) ∧
      (∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → y l = 0) ∧
      ∀ c, (c ∈ D M i ∧ c ≠ i) → ∑ l, y l * M l c = if c = k then 1 else 0) := by
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
  have hdual : ∀ k, (k ∈ D M i ∧ k ≠ i) → ∃ y : Fin t → ℚ, (∀ l, 0 ≤ y l) ∧
      (∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → y l = 0) ∧
      ∀ c, (c ∈ D M i ∧ c ≠ i) → ∑ l, y l * M l c = if c = k then 1 else 0 := by
    intro k hk
    have hPk : P k := (hPiff k).mpr hk
    obtain ⟨y, hy⟩ := hsurjv (Pi.single k 1)
    have hy' : Matrix.vecMul y A = (Pi.single k (1 : ℚ) : Fin t → ℚ) := hy
    have hye : ∀ j, Matrix.vecMul y A j = (Pi.single k (1 : ℚ) : Fin t → ℚ) j :=
      fun j => congrFun hy' j
    have hysupp : ∀ l, ¬ P l → y l = 0 := by
      intro l hl
      have hlk : l ≠ k := fun h => hl (by rw [h]; exact hPk)
      rw [← hvm_out y l hl, hye, Pi.single_eq_of_ne hlk]
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
    refine ⟨y, fun l => ?_, fun l hl => hysupp l (fun h => hl ((hPiff l).mp h)), fun c hc => ?_⟩
    · have h4 : -y l ≤ 0 := h2 l
      linarith
    · have h3 := hye c
      rw [hvm_in y c ((hPiff c).mpr hc) hysupp] at h3
      rw [h3, Pi.single_apply]
  refine ⟨fun b hb0 => ?_, hdual⟩
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


theorem zero_out {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (i : Fin t) :
    ∀ l ∈ D M i, ∀ c, c ∉ D M i → M l c = 0 := by
  classical
  intro l hl c hc
  by_contra hne
  have hlc : l ≠ c := fun h => hc (by rw [← h]; exact hl)
  have hneg : M l c < 0 := lt_of_le_of_ne (offdiag_nonpos M hM l c hlc) hne
  apply hc
  unfold D
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (reach_of_mem_D M i l hl).tail (And.intro hlc hneg)⟩

theorem colD_nonneg {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (i : Fin t) :
    ∀ c ∈ D M i, 0 ≤ ∑ l ∈ D M i, M l c := by
  intro c hc
  have hall : 0 ≤ ∑ l, M l c := hM.2 c
  have hsplit := Finset.sum_sdiff (Finset.subset_univ (D M i)) (f := fun l => M l c)
  have hneg : ∑ l ∈ Finset.univ \ D M i, M l c ≤ 0 := by
    apply Finset.sum_nonpos
    intro l hl
    have hlc : l ≠ c := fun h => (Finset.mem_sdiff.mp hl).2 (by rw [h]; exact hc)
    exact offdiag_nonpos M hM l c hlc
  linarith

theorem exists_q {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M) (i : Fin t) :
    ∃ q : Fin t → ℚ, (∀ l, 0 ≤ q l) ∧
      (∀ l, (l ∈ D M i ∧ l ≠ i) → ∑ c, M l c * q c = 0) ∧
      q i = 1 ∧ ∀ l, l ∉ D M i → q l = 0 := by
  classical
  have hiD : i ∈ D M i := self_mem_D M i
  obtain ⟨b, hb⟩ : ∃ b : Fin t → ℚ, b = fun l =>
      if (l ∈ D M i ∧ l ≠ i) then -M l i else if l = i then 1 else 0 := ⟨_, rfl⟩
  have hbe : ∀ l, b l = if (l ∈ D M i ∧ l ≠ i) then -M l i else if l = i then 1 else 0 :=
    fun l => by rw [hb]
  have hb0 : ∀ l, 0 ≤ b l := by
    intro l
    rw [hbe]
    split_ifs with h1 h2
    · have := offdiag_nonpos M hM l i h1.2
      linarith
    · exact zero_le_one
    · exact le_rfl
  obtain ⟨q, hq0, hqout', hqin⟩ := (solve_S M hM i).1 b hb0
  have hqi : q i = 1 := by
    rw [hqout' i (fun h => h.2 rfl), hbe, if_neg (fun h => h.2 rfl), if_pos rfl]
  have hqout : ∀ l, l ∉ D M i → q l = 0 := by
    intro l hl
    have hli : l ≠ i := fun h => hl (by rw [h]; exact hiD)
    rw [hqout' l (fun h => hl h.1), hbe, if_neg (fun h => hl h.1), if_neg hli]
  refine ⟨q, hq0, ?_, hqi, hqout⟩
  intro l hS
  have hpt : ∀ j, M l j * q j =
      (if (j ∈ D M i ∧ j ≠ i) then M l j else 0) * q j +
        (if j = i then M l j * q j else 0) := by
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
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, hqin l hS,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hqi, hbe, if_pos hS]
  ring

end Aux_LinExchangeSP_ZPlus_theorem_6_4_square

open LinExchangeSP.ZPlus Aux_LinExchangeSP_ZPlus_theorem_6_4_square in
theorem solution {t : ℕ} (ht : 0 < t) (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (γ : Fin t → ℚ) (hγ : ∀ i, 0 < γ i) :
    ∃ (l' : ℕ) (Mbar : Matrix (Fin l') (Fin t) ℚ) (γbar : Fin l' → ℚ),
      l' ≤ nnz M ∧ IsM2 Mbar ∧
      polyhedron M γ ⊆ polyhedron Mbar γbar ∧
      polyhedron Mbar γbar ⊆ LinExchangeSP.ZPlus.scale (Bconst γ ht ^ 2) (polyhedron M γ) := by
  classical
  choose qv hq0 hqrow hqi hqout using fun i => exists_q M hM i
  have hdual' : ∀ i c, ∃ y : Fin t → ℚ, (c ∈ D M i ∧ c ≠ i) →
      ((∀ l, 0 ≤ y l) ∧ (∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → y l = 0) ∧
        ∀ c', (c' ∈ D M i ∧ c' ≠ i) → ∑ l, y l * M l c' = if c' = c then 1 else 0) := by
    intro i c
    by_cases hc : (c ∈ D M i ∧ c ≠ i)
    · obtain ⟨y, h⟩ := (solve_S M hM i).2 c hc
      exact ⟨y, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose yv hyv using hdual'
  have hy0 : ∀ i c, (c ∈ D M i ∧ c ≠ i) → ∀ l, 0 ≤ yv i c l := fun i c hc => (hyv i c hc).1
  have hyS : ∀ i c, (c ∈ D M i ∧ c ≠ i) → ∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → yv i c l = 0 :=
    fun i c hc => (hyv i c hc).2.1
  have hycol : ∀ i c, (c ∈ D M i ∧ c ≠ i) → ∀ c', (c' ∈ D M i ∧ c' ≠ i) →
      ∑ l, yv i c l * M l c' = if c' = c then 1 else 0 := fun i c hc => (hyv i c hc).2.2
  -- auxiliary rational quantities
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin t → ℚ, lam = fun l => (∑ l', γ l') - γ l := ⟨_, rfl⟩
  have hlame : ∀ l, lam l = (∑ l', γ l') - γ l := fun l => by rw [hlam]
  obtain ⟨Mq, hMq⟩ : ∃ Mq : Fin t → ℚ, Mq = fun i => ∑ c, M i c * qv i c := ⟨_, rfl⟩
  have hMqe : ∀ i, Mq i = ∑ c, M i c * qv i c := fun i => by rw [hMq]
  obtain ⟨Ev, hEv⟩ : ∃ Ev : Fin t → ℚ, Ev = fun i => ∑ c,
      (if (c ∈ D M i ∧ c ≠ i) then (-M i c) * ∑ l, yv i c l * γ l else 0) := ⟨_, rfl⟩
  have hEve : ∀ i, Ev i = ∑ c,
      (if (c ∈ D M i ∧ c ≠ i) then (-M i c) * ∑ l, yv i c l * γ l else 0) :=
    fun i => by rw [hEv]
  obtain ⟨Rc, hRc⟩ : ∃ Rc : Fin t → Fin t → Fin t → ℚ, Rc = fun i c j =>
      if c = i then (if 0 < Mq i ∧ j = i then 1 else 0)
      else (if j = i then qv i c else 0) - (if j = c then 1 else 0) := ⟨_, rfl⟩
  have hRce : ∀ i c j, Rc i c j = if c = i then (if 0 < Mq i ∧ j = i then 1 else 0)
      else (if j = i then qv i c else 0) - (if j = c then 1 else 0) := fun i c j => by rw [hRc]
  obtain ⟨Rr, hRr⟩ : ∃ Rr : Fin t → Fin t → ℚ, Rr = fun i c =>
      if c = i then (if 0 < Mq i then (γ i + Ev i) / Mq i else 1)
      else ∑ l, yv i c l * lam l := ⟨_, rfl⟩
  have hRre : ∀ i c, Rr i c = if c = i then (if 0 < Mq i then (γ i + Ev i) / Mq i else 1)
      else ∑ l, yv i c l * lam l := fun i c => by rw [hRr]
  obtain ⟨E, hE⟩ : ∃ E : Finset (Fin t × Fin t),
      E = Finset.univ.filter (fun e : Fin t × Fin t => M e.1 e.2 ≠ 0) := ⟨_, rfl⟩
  obtain ⟨eqv, -⟩ : ∃ eqv : {x // x ∈ E} ≃ Fin E.card, True := ⟨E.equivFin, trivial⟩
  -- basic facts
  have hiD : ∀ i, i ∈ D M i := fun i => self_mem_D M i
  have harcS : ∀ i c, M i c ≠ 0 → c ≠ i → (c ∈ D M i ∧ c ≠ i) := by
    intro i c hne hci
    refine ⟨?_, hci⟩
    have hneg : M i c < 0 := lt_of_le_of_ne (offdiag_nonpos M hM i c (Ne.symm hci)) hne
    unfold D
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      Relation.ReflTransGen.single (And.intro (Ne.symm hci) hneg)⟩
  -- row sums of the new rows
  have hrowR : ∀ i c (p : Fin t → ℝ), ∑ j, ((Rc i c j : ℚ) : ℝ) * p j =
      if c = i then (if 0 < Mq i then p i else 0) else (qv i c : ℝ) * p i - p c := by
    intro i c p
    by_cases hci : c = i
    · rw [if_pos hci]
      by_cases hpos : 0 < Mq i
      · rw [if_pos hpos]
        have : ∀ j, ((Rc i c j : ℚ) : ℝ) * p j = if j = i then p j else 0 := by
          intro j
          rw [hRce, if_pos hci]
          by_cases hji : j = i
          · rw [if_pos ⟨hpos, hji⟩, if_pos hji]; simp
          · rw [if_neg (fun h => hji h.2), if_neg hji]; simp
        rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_ite_eq',
          if_pos (Finset.mem_univ _)]
      · rw [if_neg hpos]
        apply Finset.sum_eq_zero
        intro j _
        rw [hRce, if_pos hci, if_neg (fun h => hpos h.1)]
        simp
    · rw [if_neg hci]
      have : ∀ j, ((Rc i c j : ℚ) : ℝ) * p j =
          (if j = i then (qv i c : ℝ) * p j else 0) - (if j = c then p j else 0) := by
        intro j
        rw [hRce, if_neg hci]
        by_cases hji : j = i
        · have hjc : j ≠ c := fun h => hci (h.symm.trans hji)
          rw [if_pos hji, if_neg hjc, if_pos hji, if_neg hjc]
          push_cast
          ring
        · rw [if_neg hji, if_neg hji]
          by_cases hjc : j = c
          · rw [if_pos hjc, if_pos hjc]; push_cast; ring
          · rw [if_neg hjc, if_neg hjc]; push_cast; ring
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  -- (I) decomposition of row i
  have hI : ∀ i (p : Fin t → ℝ), rowVal M p i = (Mq i : ℝ) * p i +
      ∑ c, (if (c ∈ D M i ∧ c ≠ i) then (M i c : ℝ) * (p c - (qv i c : ℝ) * p i) else 0) := by
    intro i p
    unfold rowVal
    have hpt : ∀ c, (M i c : ℝ) * p c = (M i c : ℝ) * (qv i c : ℝ) * p i +
        (if (c ∈ D M i ∧ c ≠ i) then (M i c : ℝ) * (p c - (qv i c : ℝ) * p i) else 0) := by
      intro c
      by_cases hci : c = i
      · rw [if_neg (fun h => h.2 hci), hci, hqi i]
        simp
      · by_cases hS : (c ∈ D M i ∧ c ≠ i)
        · rw [if_pos hS]
          ring
        · have hcD : c ∉ D M i := fun h => hS ⟨h, hci⟩
          rw [if_neg hS, zero_out M hM i i (hiD i) c hcD]
          simp
    rw [Finset.sum_congr rfl (fun c _ => hpt c), Finset.sum_add_distrib, hMqe]
    push_cast
    rw [Finset.sum_mul]
  -- (II) the dual vectors
  have hII : ∀ i c, (c ∈ D M i ∧ c ≠ i) → ∀ (p : Fin t → ℝ),
      ∑ l, (yv i c l : ℝ) * rowVal M p l = p c - (qv i c : ℝ) * p i := by
    intro i c hc p
    have hv : ∀ j, j ≠ i → ∑ l, yv i c l * M l j = if j = c then 1 else 0 := by
      intro j hji
      by_cases hSj : (j ∈ D M i ∧ j ≠ i)
      · exact hycol i c hc j hSj
      · have hjD : j ∉ D M i := fun h => hSj ⟨h, hji⟩
        have hjc : j ≠ c := fun h => hjD (by rw [h]; exact hc.1)
        rw [if_neg hjc]
        apply Finset.sum_eq_zero
        intro l _
        by_cases hSl : (l ∈ D M i ∧ l ≠ i)
        · rw [zero_out M hM i l hSl.1 j hjD, mul_zero]
        · rw [hyS i c hc l hSl, zero_mul]
    have hvq : ∑ j, (∑ l, yv i c l * M l j) * qv i j = 0 := by
      calc ∑ j, (∑ l, yv i c l * M l j) * qv i j
          = ∑ j, ∑ l, yv i c l * M l j * qv i j := by simp_rw [Finset.sum_mul]
        _ = ∑ l, ∑ j, yv i c l * M l j * qv i j := Finset.sum_comm
        _ = ∑ l, yv i c l * ∑ j, M l j * qv i j := by simp_rw [Finset.mul_sum, mul_assoc]
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro l _
          by_cases hSl : (l ∈ D M i ∧ l ≠ i)
          · rw [hqrow i l hSl, mul_zero]
          · rw [hyS i c hc l hSl, zero_mul]
    have hcmem : c ∈ (Finset.univ : Finset (Fin t)).erase i :=
      Finset.mem_erase.mpr ⟨hc.2, Finset.mem_univ _⟩
    have hvi : ∑ l, yv i c l * M l i = -qv i c := by
      have h1 := hvq
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h1
      have h2 : ∑ j ∈ (Finset.univ : Finset (Fin t)).erase i,
          (∑ l, yv i c l * M l j) * qv i j = qv i c := by
        have h4 : ∀ j ∈ (Finset.univ : Finset (Fin t)).erase i,
            (∑ l, yv i c l * M l j) * qv i j = if j = c then qv i j else 0 := by
          intro j hj
          rw [hv j (Finset.ne_of_mem_erase hj)]
          split_ifs <;> ring
        rw [Finset.sum_congr rfl h4, Finset.sum_ite_eq', if_pos hcmem]
      rw [h2, hqi i, mul_one] at h1
      linarith
    have conv : ∑ l, (yv i c l : ℝ) * rowVal M p l =
        ∑ j, ((∑ l, yv i c l * M l j : ℚ) : ℝ) * p j := by
      unfold rowVal
      simp only [Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [conv, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hvi]
    have h3 : ∀ j ∈ (Finset.univ : Finset (Fin t)).erase i,
        ((∑ l, yv i c l * M l j : ℚ) : ℝ) * p j = if j = c then p j else 0 := by
      intro j hj
      rw [hv j (Finset.ne_of_mem_erase hj)]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq', if_pos hcmem]
    push_cast
    ring
  -- Lemma 7.1
  have h71 : ∀ (p : Fin t → ℝ), (∀ j, 0 ≤ p j) → (∀ l, rowVal M p l ≤ (γ l : ℝ)) →
      ∀ h, -((lam h : ℚ) : ℝ) ≤ rowVal M p h := by
    intro p hp0 hpM h
    have hsum0 : 0 ≤ ∑ l, rowVal M p l := by
      unfold rowVal
      rw [Finset.sum_comm]
      apply Finset.sum_nonneg
      intro c _
      rw [← Finset.sum_mul]
      apply mul_nonneg _ (hp0 c)
      have := hM.2 c
      exact_mod_cast this
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h)] at hsum0
    have hle : ∑ l ∈ (Finset.univ : Finset (Fin t)).erase h, rowVal M p l ≤
        ∑ l ∈ (Finset.univ : Finset (Fin t)).erase h, (γ l : ℝ) :=
      Finset.sum_le_sum (fun l _ => hpM l)
    have hγs : (γ h : ℝ) + ∑ l ∈ (Finset.univ : Finset (Fin t)).erase h, (γ l : ℝ) =
        ∑ l, (γ l : ℝ) := Finset.add_sum_erase _ (fun l => (γ l : ℝ)) (Finset.mem_univ h)
    rw [hlame]
    push_cast
    linarith
  -- bounds on Ev
  have hEv0 : ∀ i, 0 ≤ Ev i := by
    intro i
    rw [hEve]
    apply Finset.sum_nonneg
    intro c _
    split_ifs with hS
    · apply mul_nonneg
      · have := offdiag_nonpos M hM i c (Ne.symm hS.2)
        linarith
      · exact Finset.sum_nonneg (fun l _ => mul_nonneg (hy0 i c hS l) (hγ l).le)
    · exact le_rfl
  have hEvlam : ∀ i, Ev i ≤ lam i := by
    intro i
    obtain ⟨u, hu⟩ : ∃ u : Fin t → ℚ, u = fun l => ∑ c,
        (if (c ∈ D M i ∧ c ≠ i) then (-M i c) * yv i c l else 0) := ⟨_, rfl⟩
    have hue : ∀ l, u l = ∑ c,
        (if (c ∈ D M i ∧ c ≠ i) then (-M i c) * yv i c l else 0) := fun l => by rw [hu]
    have hu_out : ∀ l, ¬ (l ∈ D M i ∧ l ≠ i) → u l = 0 := by
      intro l hl
      rw [hue]
      apply Finset.sum_eq_zero
      intro c _
      split_ifs with hS
      · rw [hyS i c hS l hl, mul_zero]
      · rfl
    have hswap : Ev i = ∑ l, u l * γ l := by
      rw [hEve]
      simp_rw [hue, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hS : (c ∈ D M i ∧ c ≠ i)
      · simp_rw [if_pos hS]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      · simp_rw [if_neg hS]
        simp
    -- u ≤ 1 by the maximum principle
    have hule : ∀ l, u l ≤ 1 := by
      obtain ⟨w, hw⟩ : ∃ w : Fin t → ℚ, w = fun l =>
          if (l ∈ D M i ∧ l ≠ i) then u l - 1 else 0 := ⟨_, rfl⟩
      have hwe : ∀ l, w l = if (l ∈ D M i ∧ l ≠ i) then u l - 1 else 0 := fun l => by rw [hw]
      have hmax := maxp M hM i (fun l => l ∈ D M i ∧ l ≠ i) (fun h => h.2 rfl)
        (fun l hl => reach_of_mem_D M i l hl.1) w
        (fun l hl => by rw [hwe, if_neg (show ¬ (l ∈ D M i ∧ l ≠ i) from hl)])
        (fun c' hc' => by
          have hpt : ∀ l, w l * M l c' =
              u l * M l c' - (if (l ∈ D M i ∧ l ≠ i) then M l c' else 0) := by
            intro l
            rw [hwe]
            split_ifs with hS
            · ring
            · rw [hu_out l hS]; ring
          rw [Finset.sum_congr rfl (fun l _ => hpt l), Finset.sum_sub_distrib]
          have huM : ∑ l, u l * M l c' = -M i c' := by
            simp_rw [hue, Finset.sum_mul]
            rw [Finset.sum_comm]
            have hpc : ∀ c, ∑ l, (if (c ∈ D M i ∧ c ≠ i) then (-M i c) * yv i c l else 0) *
                M l c' = if c = c' then -M i c' else 0 := by
              intro c
              by_cases hS : (c ∈ D M i ∧ c ≠ i)
              · have : ∑ l, (if (c ∈ D M i ∧ c ≠ i) then (-M i c) * yv i c l else 0) * M l c'
                    = (-M i c) * ∑ l, yv i c l * M l c' := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro l _
                  rw [if_pos hS]
                  ring
                rw [this, hycol i c hS c' hc']
                by_cases hcc : c = c'
                · rw [if_pos hcc.symm, if_pos hcc, hcc]; ring
                · rw [if_neg (fun h => hcc h.symm), if_neg hcc]; ring
              · have hcc : c ≠ c' := fun h => hS (by rw [h]; exact hc')
                rw [if_neg hcc]
                apply Finset.sum_eq_zero
                intro l _
                rw [if_neg hS, zero_mul]
            rw [Finset.sum_congr rfl (fun c _ => hpc c), Finset.sum_ite_eq',
              if_pos (Finset.mem_univ _)]
          have hfe : Finset.univ.filter (fun l => l ∈ D M i ∧ l ≠ i) = (D M i).erase i := by
            ext l
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            tauto
          have hDsplit : ∑ l, (if (l ∈ D M i ∧ l ≠ i) then M l c' else 0) + M i c' =
              ∑ l ∈ D M i, M l c' := by
            rw [← Finset.sum_filter, hfe, ← Finset.add_sum_erase _ _ (hiD i)]
            ring
          have hcD := colD_nonneg M hM i c' hc'.1
          rw [huM]
          linarith)
      intro l
      by_cases hS : (l ∈ D M i ∧ l ≠ i)
      · have := hmax l
        rw [hwe, if_pos hS] at this
        linarith
      · rw [hu_out l hS]
        exact zero_le_one
    rw [hswap]
    calc ∑ l, u l * γ l ≤ ∑ l, (if l = i then 0 else γ l) := by
          apply Finset.sum_le_sum
          intro l _
          by_cases hS : (l ∈ D M i ∧ l ≠ i)
          · rw [if_neg hS.2]
            have := hule l
            have := hγ l
            nlinarith
          · rw [hu_out l hS, zero_mul]
            split_ifs
            · exact le_rfl
            · exact (hγ l).le
      _ = lam i := by
          rw [hlame]
          have h1 : ∀ l, γ l = (if l = i then γ l else 0) + (if l = i then 0 else γ l) := by
            intro l
            split_ifs <;> ring
          have h2 : ∑ l, γ l = γ i + ∑ l, (if l = i then 0 else γ l) := by
            rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib,
              Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
          linarith
  -- the constant B
  have hBγ : ∀ l, ∑ j, (γ j : ℝ) ≤ Bconst γ ht * (γ l : ℝ) := by
    intro l
    unfold Bconst
    obtain ⟨m, hm⟩ : ∃ m, m = Finset.univ.inf' ⟨⟨0, ht⟩, Finset.mem_univ _⟩
        (fun i => (γ i : ℝ)) := ⟨_, rfl⟩
    rw [← hm]
    have hmle : m ≤ (γ l : ℝ) := by
      rw [hm]
      exact Finset.inf'_le _ (Finset.mem_univ l)
    have hmpos : 0 < m := by
      rw [hm]
      obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' ⟨⟨0, ht⟩, Finset.mem_univ _⟩
        (fun i => (γ i : ℝ))
      rw [hk]
      exact_mod_cast hγ k
    have hS : 0 ≤ ∑ j, (γ j : ℝ) := Finset.sum_nonneg (fun j _ => by exact_mod_cast (hγ j).le)
    rw [div_mul_eq_mul_div, le_div_iff₀ hmpos]
    exact mul_le_mul_of_nonneg_left hmle hS
  obtain ⟨B, hB⟩ : ∃ B, B = Bconst γ ht := ⟨_, rfl⟩
  rw [← hB] at hBγ
  rw [← hB]
  have hγR : ∀ l, (0 : ℝ) < (γ l : ℝ) := fun l => by exact_mod_cast hγ l
  have hγle : ∀ l, (γ l : ℝ) ≤ ∑ j, (γ j : ℝ) := fun l =>
    Finset.single_le_sum (f := fun j => (γ j : ℝ)) (fun j _ => (hγR j).le) (Finset.mem_univ l)
  have hB1 : 1 ≤ B := by
    obtain ⟨l0⟩ : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
    have h1 := hBγ l0
    have h2 := hγle l0
    have h3 := hγR l0
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_lt_mul_of_pos_right hcon h3]
  have hlamB : ∀ l, ((lam l : ℚ) : ℝ) ≤ (B - 1) * (γ l : ℝ) := by
    intro l
    rw [hlame]
    push_cast
    have := hBγ l
    linarith
  -- assemble
  refine ⟨E.card, fun r j => Rc (eqv.symm r).1.1 (eqv.symm r).1.2 j,
    fun r => Rr (eqv.symm r).1.1 (eqv.symm r).1.2, ?_, ?_, ?_, ?_⟩
  · rw [hE]
    exact le_rfl
  · -- IsM2
    have hpos_i : ∀ i c j, 0 < Rc i c j → j = i := by
      intro i c j h
      by_contra hji
      rw [hRce] at h
      by_cases hci : c = i
      · rw [if_pos hci, if_neg (fun h' => hji h'.2)] at h
        exact lt_irrefl _ h
      · rw [if_neg hci, if_neg hji] at h
        split_ifs at h <;> linarith
    have hneg_c : ∀ i c j, Rc i c j < 0 → j = c := by
      intro i c j h
      by_contra hjc
      rw [hRce] at h
      by_cases hci : c = i
      · rw [if_pos hci] at h
        split_ifs at h <;> linarith
      · rw [if_neg hci, if_neg hjc, sub_zero] at h
        split_ifs at h
        · linarith [hq0 i c]
        · linarith
    unfold IsM2
    intro r
    refine ⟨fun j j' h1 h2 => ?_, fun j j' h1 h2 => ?_⟩
    · rw [hpos_i _ _ j h1, hpos_i _ _ j' h2]
    · rw [hneg_c _ _ j h1, hneg_c _ _ j' h2]
  · -- P_M ⊆ P̄
    intro p hp
    simp only [polyhedron, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨hp0, hpM⟩ := hp
    refine ⟨hp0, fun r => ?_⟩
    unfold rowVal
    show ∑ j, ((Rc (eqv.symm r).1.1 (eqv.symm r).1.2 j : ℚ) : ℝ) * p j ≤
      ((Rr (eqv.symm r).1.1 (eqv.symm r).1.2 : ℚ) : ℝ)
    generalize eqv.symm r = e
    obtain ⟨⟨i, c⟩, he⟩ := e
    simp only
    have hMne : M i c ≠ 0 := by
      rw [hE, Finset.mem_filter] at he
      exact he.2
    have hpM' : ∀ l, rowVal M p l ≤ (γ l : ℝ) := hpM
    rw [hrowR i c p, hRre]
    by_cases hci : c = i
    · rw [if_pos hci, if_pos hci]
      by_cases hpos : 0 < Mq i
      · rw [if_pos hpos, if_pos hpos]
        -- (Mq) p_i ≤ γ_i + Ev
        have hkey : (Mq i : ℝ) * p i ≤ (γ i : ℝ) + (Ev i : ℝ) := by
          have h1 := hI i p
          have h2 : ∀ c, 0 ≤ (if (c ∈ D M i ∧ c ≠ i) then (M i c : ℝ) * (p c - (qv i c : ℝ) * p i)
              else 0) + (((if (c ∈ D M i ∧ c ≠ i) then
                ((-M i c) * ∑ l, yv i c l * γ l) else 0 : ℚ)) : ℝ) := by
            intro c
            split_ifs with hS
            · rw [← hII i c hS p]
              have hle : ∑ l, (yv i c l : ℝ) * rowVal M p l ≤ ∑ l, (yv i c l : ℝ) * (γ l : ℝ) :=
                Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hpM' l)
                  (by exact_mod_cast hy0 i c hS l))
              have hMic : (M i c : ℝ) ≤ 0 := by
                exact_mod_cast offdiag_nonpos M hM i c (Ne.symm hS.2)
              have := mul_le_mul_of_nonpos_left hle hMic
              push_cast
              linarith
            · simp
          have h3 := Finset.sum_nonneg (fun c (_ : c ∈ Finset.univ) => h2 c)
          rw [Finset.sum_add_distrib] at h3
          rw [hEve, Rat.cast_sum]
          linarith [hpM' i]
        have hMqR : (0 : ℝ) < (Mq i : ℝ) := by exact_mod_cast hpos
        rw [Rat.cast_div, Rat.cast_add, le_div_iff₀ hMqR]
        linarith
      · rw [if_neg hpos, if_neg hpos]
        norm_num
    · rw [if_neg hci, if_neg hci]
      have hS := harcS i c hMne hci
      have h1 := hII i c hS p
      have hle : ∑ l, (yv i c l : ℝ) * (-((lam l : ℚ) : ℝ)) ≤
          ∑ l, (yv i c l : ℝ) * rowVal M p l :=
        Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (h71 p hp0 hpM' l)
          (by exact_mod_cast hy0 i c hS l))
      push_cast
      have e1 : ∑ l, (yv i c l : ℝ) * (-((lam l : ℚ) : ℝ)) =
          -∑ l, (yv i c l : ℝ) * ((lam l : ℚ) : ℝ) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro l _
        ring
      linarith
  · -- P̄ ⊆ B² P_M
    intro p hp
    simp only [polyhedron, Set.mem_setOf_eq] at hp
    obtain ⟨hp0, hpQ⟩ := hp
    have hrowQ : ∀ i c, M i c ≠ 0 → ∑ j, ((Rc i c j : ℚ) : ℝ) * p j ≤ ((Rr i c : ℚ) : ℝ) := by
      intro i c hne
      have he : (i, c) ∈ E := by
        rw [hE, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hne⟩
      have h := hpQ (eqv ⟨(i, c), he⟩)
      unfold rowVal at h
      simp only [Equiv.symm_apply_apply] at h
      exact h
    have hMp : ∀ i, rowVal M p i ≤ B ^ 2 * (γ i : ℝ) := by
      intro i
      have h1 := hI i p
      -- arc constraints
      have h2 : ∀ c, (if (c ∈ D M i ∧ c ≠ i) then (M i c : ℝ) * (p c - (qv i c : ℝ) * p i)
          else 0) ≤ (B - 1) * (if (c ∈ D M i ∧ c ≠ i) then
            (((-M i c) * ∑ l, yv i c l * γ l : ℚ) : ℝ) else 0) := by
        intro c
        split_ifs with hS
        · have hMic : (M i c : ℝ) ≤ 0 := by
            exact_mod_cast offdiag_nonpos M hM i c (Ne.symm hS.2)
          have hlamle : ∑ l, (yv i c l : ℝ) * ((lam l : ℚ) : ℝ) ≤
              (B - 1) * ∑ l, (yv i c l : ℝ) * (γ l : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro l _
            have hyl : (0 : ℝ) ≤ (yv i c l : ℝ) := by exact_mod_cast hy0 i c hS l
            have := mul_le_mul_of_nonneg_left (hlamB l) hyl
            linarith
          by_cases hz : M i c = 0
          · have hz' : (M i c : ℝ) = 0 := by exact_mod_cast hz
            have hz'' : (((-M i c) * ∑ l, yv i c l * γ l : ℚ) : ℝ) = 0 := by
              rw [hz]; simp
            rw [hz', hz'', zero_mul, mul_zero]
          · have hq := hrowQ i c hz
            rw [hrowR i c p, if_neg hS.2, hRre, if_neg hS.2] at hq
            push_cast at hq
            have h3 : (M i c : ℝ) * (p c - (qv i c : ℝ) * p i) ≤
                (-(M i c : ℝ)) * ∑ l, (yv i c l : ℝ) * ((lam l : ℚ) : ℝ) := by
              have := mul_le_mul_of_nonpos_left
                (show -(∑ l, (yv i c l : ℝ) * ((lam l : ℚ) : ℝ)) ≤ p c - (qv i c : ℝ) * p i by
                  linarith) hMic
              linarith
            have h4 : (-(M i c : ℝ)) * ∑ l, (yv i c l : ℝ) * ((lam l : ℚ) : ℝ) ≤
                (-(M i c : ℝ)) * ((B - 1) * ∑ l, (yv i c l : ℝ) * (γ l : ℝ)) :=
              mul_le_mul_of_nonneg_left hlamle (by linarith)
            push_cast
            nlinarith
        · simp
      have h3 := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => h2 c)
      rw [← Finset.mul_sum] at h3
      have hEvR : ∑ c, (if (c ∈ D M i ∧ c ≠ i) then
          (((-M i c) * ∑ l, yv i c l * γ l : ℚ) : ℝ) else 0) = (Ev i : ℝ) := by
        rw [hEve, Rat.cast_sum]
        apply Finset.sum_congr rfl
        intro c _
        split_ifs <;> simp
      rw [hEvR] at h3
      have hEvlamR : (Ev i : ℝ) ≤ ((lam i : ℚ) : ℝ) := by exact_mod_cast hEvlam i
      have hEv0R : (0 : ℝ) ≤ (Ev i : ℝ) := by exact_mod_cast hEv0 i
      have hlamγ : ((lam i : ℚ) : ℝ) + (γ i : ℝ) = ∑ j, (γ j : ℝ) := by
        rw [hlame]; push_cast; ring
      have hBg := hBγ i
      have hγi := hγR i
      have hlamB' := hlamB i
      by_cases hpos : 0 < Mq i
      · have hq := hrowQ i i (ne_of_gt (hdiag i))
        rw [hrowR i i p, if_pos rfl, if_pos hpos, hRre, if_pos rfl, if_pos hpos] at hq
        have hMqR : (0 : ℝ) < (Mq i : ℝ) := by exact_mod_cast hpos
        rw [Rat.cast_div, Rat.cast_add, le_div_iff₀ hMqR] at hq
        have hMqp : (Mq i : ℝ) * p i ≤ (γ i : ℝ) + (Ev i : ℝ) := by linarith
        have hB0 : (0 : ℝ) ≤ B - 1 := by linarith
        have h5 : (B - 1) * (Ev i : ℝ) ≤ (B - 1) * ((lam i : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left hEvlamR hB0
        have h6 : (B - 1) * ((lam i : ℚ) : ℝ) ≤ (B - 1) * ((B - 1) * (γ i : ℝ)) :=
          mul_le_mul_of_nonneg_left hlamB' hB0
        nlinarith [mul_nonneg hB0 hγi.le]
      · have hMq0 : (Mq i : ℝ) ≤ 0 := by
          push_neg at hpos
          exact_mod_cast hpos
        have hMqp : (Mq i : ℝ) * p i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hMq0 (hp0 i)
        have hB0 : (0 : ℝ) ≤ B - 1 := by linarith
        have h5 : (B - 1) * (Ev i : ℝ) ≤ (B - 1) * ((lam i : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left hEvlamR hB0
        have h6 : (B - 1) * ((lam i : ℚ) : ℝ) ≤ (B - 1) * ((B - 1) * (γ i : ℝ)) :=
          mul_le_mul_of_nonneg_left hlamB' hB0
        have h7 : (0 : ℝ) ≤ (2 * B - 1) * (γ i : ℝ) := mul_nonneg (by linarith) hγi.le
        nlinarith
    -- scaling
    have hBpos : (0 : ℝ) < B ^ 2 := pow_pos (by linarith) 2
    rw [LinExchangeSP.ZPlus.scale, Set.mem_image]
    refine ⟨(B ^ 2)⁻¹ • p, ?_, ?_⟩
    swap
    · show B ^ 2 • ((B ^ 2)⁻¹ • p) = p
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hBpos), one_smul]
    simp only [polyhedron, Set.mem_setOf_eq]
    refine ⟨fun j => ?_, fun l => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr hBpos.le) (hp0 j)
    · have : rowVal M ((B ^ 2)⁻¹ • p) l = (B ^ 2)⁻¹ * rowVal M p l := by
        unfold rowVal
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [this, inv_mul_le_iff₀ hBpos]
      exact hMp l
