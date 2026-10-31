-- Prove2me | solution 1 for MinBuying.canonical_list_completion
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:46:56.029964+00:00
-- url     : https://prove2.me/submissions/e1ccceee-237b-46f6-9dee-9a12cca32488

import Theorems.Thm_MinBuying_canonical_boundary_replacement
import Theorems.Thm_MinBuying_canonical_revenue_bridge

open MinBuying
open scoped BigOperators

noncomputable section

private lemma step_nonneg (a v C : ℝ) (ha : 0 ≤ a) (hv : 0 < v)
    (hC : 0 ≤ C) : 0 ≤ continuationStep a v C := by
  unfold continuationStep
  positivity

private lemma rejection_step (a v C t : ℝ) (ha : 0 ≤ a) (hv : 0 < v)
    (hC : 0 ≤ C) (ht : 0 < t) :
    t / (t + C) * (t / (t + a)) ≤ t / (t + continuationStep a v C) := by
  have hS := step_nonneg a v C ha hv hC
  have hbound : continuationStep a v C ≤ a + C := by
    unfold continuationStep
    apply div_le_self (add_nonneg ha hC)
    have : 0 ≤ a / v := div_nonneg ha hv.le
    linarith
  have hTC : 0 < t + C := by positivity
  have hTA : 0 < t + a := by positivity
  have hTS : 0 < t + continuationStep a v C := by positivity
  have hcore : t * (t + continuationStep a v C) ≤ (t + C) * (t + a) := by
    nlinarith only [mul_nonneg ha hC, mul_le_mul_of_nonneg_left hbound ht.le]
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos hTC hTA) hTS).2
  nlinarith only [mul_le_mul_of_nonneg_left hcore ht.le]

private lemma reject_nonneg (a v t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    0 ≤ triangularReject a v t := by
  unfold triangularReject
  split_ifs <;> positivity

private lemma reject_prod_nonneg (L : List (ℝ × ℝ))
    (hpar : ∀ x ∈ L, 0 < x.1 ∧ 1 < x.2) (t : ℝ) (ht : 0 < t) :
    0 ≤ (L.map (fun x => triangularReject x.1 x.2 t)).prod := by
  apply List.prod_nonneg
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  exact reject_nonneg x.1 x.2 t (hpar x hx).1 ht

private lemma reject_prod_above (L : List (ℝ × ℝ)) (t : ℝ) (ht : 0 < t)
    (hcap : ∀ x ∈ L, x.2 < t) :
    (L.map (fun x => triangularReject x.1 x.2 t)).prod = 1 := by
  apply List.prod_eq_one
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  simp [triangularReject, ht.not_ge, (hcap x hx).not_ge]

private lemma step_loss (a v x y ε : ℝ) (ha : 0 ≤ a) (hv : 0 < v)
    (hε : 0 ≤ ε) (hxy : x - ε ≤ y) :
    continuationStep a v x - ε ≤ continuationStep a v y := by
  have hd : 0 < 1 + a / v := by positivity
  have hd1 : 1 ≤ 1 + a / v := by have := div_nonneg ha hv.le; linarith
  have heq : continuationStep a v x * (1 + a / v) = a + x :=
    div_mul_cancel₀ _ hd.ne'
  unfold continuationStep at ⊢
  apply (le_div_iff₀ hd).2
  change (continuationStep a v x - ε) * (1 + a / v) ≤ a + y
  nlinarith only [heq, hxy, mul_le_mul_of_nonneg_left hd1 hε]

private lemma fold_loss (L : List (ℝ × ℝ))
    (hpar : ∀ z ∈ L, 0 < z.1 ∧ 1 < z.2)
    (x y ε : ℝ) (hε : 0 ≤ ε) (hxy : x - ε ≤ y) :
    L.foldl (fun S z => continuationStep z.1 z.2 S) x - ε ≤
      L.foldl (fun S z => continuationStep z.1 z.2 S) y := by
  induction L generalizing x y with
  | nil => simpa using hxy
  | cons z L ih =>
    have hz := hpar z (by simp)
    have htail : ∀ u ∈ L, 0 < u.1 ∧ 1 < u.2 := fun u hu => hpar u (by simp [hu])
    exact ih htail _ _ (step_loss z.1 z.2 x y ε hz.1.le (lt_trans zero_lt_one hz.2) hε hxy)

private def ofList (L : List (ℝ × ℝ)) (P : ℝ)
    (hP : 1 < P) (hpar : ∀ x ∈ L, 0 < x.1 ∧ 1 < x.2)
    (hcaps : ∀ x ∈ L, x.2 < P)
    (hdec : L.Pairwise (fun x y => y.2 < x.2)) : CanonicalInstance where
  count := L.length
  terminalCap := P
  a := fun i => (L.get i).1
  cap := fun i => (L.get i).2
  terminal_one_lt := hP
  a_pos := fun i => (hpar _ (List.get_mem L i)).1
  cap_one_lt := fun i => (hpar _ (List.get_mem L i)).2
  cap_lt_terminal := fun i => hcaps _ (List.get_mem L i)
  caps_decreasing := fun _ _ hij => hdec.rel_get_of_lt hij

private lemma ofList_cap (L : List (ℝ × ℝ)) (P : ℝ)
    (hP : 1 < P) (hpar : ∀ x ∈ L, 0 < x.1 ∧ 1 < x.2)
    (hcaps : ∀ x ∈ L, x.2 < P)
    (hdec : L.Pairwise (fun x y => y.2 < x.2)) :
    canonicalCapRevenue (ofList L P hP hpar hcaps hdec) =
      L.foldl (fun S x => continuationStep x.1 x.2 S) (P / (P + 1)) := by
  have hmap : (List.finRange L.length).map L.get = L := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  change ((List.finRange L.length).take L.length).foldl
    (fun C i => continuationStep (L.get i).1 (L.get i).2 C) (P / (P + 1)) = _
  rw [List.take_of_length_le (by simp)]
  calc
    _ = ((List.finRange L.length).map L.get).foldl
        (fun S x => continuationStep x.1 x.2 S) (P / (P + 1)) := by rw [List.foldl_map]
    _ = _ := by rw [hmap]

private lemma ofList_uniform (L : List (ℝ × ℝ)) (P : ℝ)
    (hP : 1 < P) (hpar : ∀ x ∈ L, 0 < x.1 ∧ 1 < x.2)
    (hcaps : ∀ x ∈ L, x.2 < P)
    (hdec : L.Pairwise (fun x y => y.2 < x.2)) (t : ℝ) :
    canonicalUniformRevenueAt (ofList L P hP hpar hcaps hdec) t =
      t * (1 - triangularReject 1 P t *
        (L.map (fun x => triangularReject x.1 x.2 t)).prod) := by
  change t * (1 - triangularReject 1 P t *
    ∏ i : Fin L.length, triangularReject (L.get i).1 (L.get i).2 t) = _
  congr 3
  rw [← Fin.prod_ofFn]
  congr 1
  simpa using (List.ofFn_getElem_eq_map L (fun x => triangularReject x.1 x.2 t))

private lemma terminal_bound (P t : ℝ) (ht : 0 ≤ t) :
    t * (1 - triangularReject 1 P t) ≤ 1 := by
  by_cases ht0 : t = 0
  · subst t; norm_num
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hcap : t ≤ P
  · simp only [triangularReject, if_neg htpos.not_ge, if_pos hcap]
    have hd : 0 < t + 1 := by positivity
    have heq : t * (1 - t / (t + 1)) = t / (t + 1) := by field_simp; ring
    rw [heq]
    exact (div_le_one hd).mpr (by linarith)
  · simp [triangularReject, htpos.not_ge, hcap]

private lemma up_of_uniform (J : CanonicalInstance)
    (hU : ∀ t : ℝ, 0 ≤ t → canonicalUniformRevenueAt J t ≤ 1) :
    UPRevenue (canonicalLaw J) ≤ 1 := by
  apply csSup_le
  · exact ⟨uniformRevenue (canonicalLaw J) 0, 0, le_refl _, rfl⟩
  · rintro r ⟨t, ht, rfl⟩
    rw [(canonical_revenue_bridge J).2.2.2 t ht]
    exact hU t ht

theorem solution (L : List (ℝ × ℝ))
    (hpar : ∀ x ∈ L, 0 < x.1 ∧ 1 < x.2)
    (hdec : L.Pairwise (fun x y => y.2 < x.2))
    (C : ℝ) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hUP : ∀ t : ℝ, 0 < t →
      t * (1 - (t / (t + C)) *
        (L.map (fun x => triangularReject x.1 x.2 t)).prod) ≤ 1)
    (hfinal : 1 < L.foldl (fun S x => continuationStep x.1 x.2 S) C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : CanonicalInstance, J.count ≤ L.length ∧
      L.foldl (fun S x => continuationStep x.1 x.2 S) C - ε ≤ canonicalCapRevenue J ∧
      UPRevenue (canonicalLaw J) ≤ 1 := by
  induction L generalizing C with
  | nil => simp only [List.foldl_nil] at hfinal; linarith
  | cons x L ih =>
    have hx := hpar x (by simp)
    have htail : ∀ y ∈ L, 0 < y.1 ∧ 1 < y.2 := fun y hy => hpar y (by simp [hy])
    obtain ⟨hbelow, hLdec⟩ := List.pairwise_cons.mp hdec
    let D := continuationStep x.1 x.2 C
    have hD0 : 0 ≤ D := step_nonneg x.1 x.2 C hx.1.le (lt_trans zero_lt_one hx.2) hC0
    have hfinalD : 1 < L.foldl (fun S y => continuationStep y.1 y.2 S) D := hfinal
    by_cases hD1 : D ≤ 1
    · have hUD : ∀ t : ℝ, 0 < t → t * (1 - (t / (t + D)) *
          (L.map (fun y => triangularReject y.1 y.2 t)).prod) ≤ 1 := by
        intro t ht
        by_cases htp : t ≤ x.2
        · have hstep := rejection_step x.1 x.2 C t hx.1.le
            (lt_trans zero_lt_one hx.2) hC0 ht
          have hprod := reject_prod_nonneg L htail t ht
          have hrej := mul_le_mul_of_nonneg_right hstep hprod
          have h := hUP t ht
          have hhead : triangularReject x.1 x.2 t = t / (t + x.1) := by
            simp [triangularReject, ht.not_ge, htp]
          simp only [List.map_cons, List.prod_cons, hhead] at h
          change t / (t + C) * (t / (t + x.1)) *
            (L.map (fun y => triangularReject y.1 y.2 t)).prod ≤
            t / (t + D) * (L.map (fun y => triangularReject y.1 y.2 t)).prod at hrej
          nlinarith only [h, mul_le_mul_of_nonneg_left (sub_le_sub_left hrej 1) ht.le]
        · have habove : ∀ y ∈ L, y.2 < t := fun y hy => (hbelow y hy).trans (lt_of_not_ge htp)
          rw [reject_prod_above L t ht habove, mul_one]
          have hd : 0 < t + D := by positivity
          have heq : t * (1 - t / (t + D)) = D * (t / (t + D)) := by field_simp; ring
          rw [heq]
          have hfrac : t / (t + D) ≤ 1 := (div_le_one hd).mpr (by linarith)
          exact (mul_le_of_le_one_right hD0 hfrac).trans hD1
      obtain ⟨J, hcount, hcap, hU⟩ := ih htail hLdec D hD0 hD1 hUD hfinalD
      exact ⟨J, hcount.trans (by simp), hcap, hU⟩
    · have hcross : 1 < D := lt_of_not_ge hD1
      have hAtCap : x.2 * (1 - (x.2 / (x.2 + C)) * (x.2 / (x.2 + x.1))) ≤ 1 := by
        have h := hUP x.2 (lt_trans zero_lt_one hx.2)
        have hall := reject_prod_above L x.2 (lt_trans zero_lt_one hx.2) hbelow
        have hhead : triangularReject x.1 x.2 x.2 = x.2 / (x.2 + x.1) := by
          simp [triangularReject, not_le.mpr (lt_trans zero_lt_one hx.2)]
        simpa only [List.map_cons, List.prod_cons, hhead, hall, mul_one] using h
      let b := x.2 * (D - 1) / (x.2 - D)
      obtain ⟨hb, hDp, hDC, hstep, hprod, hloss⟩ :=
        canonical_boundary_replacement x.1 x.2 C hx.1 hx.2 hC0 hC1 hcross hAtCap
      change 0 < b at hb
      change continuationStep b x.2 1 = D at hstep
      change ∀ t : ℝ, 0 ≤ t → (t + 1) * (t + b) ≤ (t + C) * (t + x.1) at hprod
      change ∀ δ z : ℝ, 0 ≤ δ → 1 - δ ≤ z → D - δ ≤ continuationStep b x.2 z at hloss
      let P := x.2 + 1 + 1 / ε
      have hinv : 0 < 1 / ε := one_div_pos.mpr hε
      have hPp : x.2 < P := by dsimp [P]; linarith
      have hP1 : 1 < P := hx.2.trans hPp
      have hPden : 0 < P + 1 := by linarith
      have hεP : 1 ≤ ε * (P + 1) := by
        have hinveq : ε * (1 / ε) = 1 := mul_one_div_cancel hε.ne'
        have hsmall : 1 / ε ≤ P + 1 := by dsimp [P]; linarith
        nlinarith only [hinveq, mul_le_mul_of_nonneg_left hsmall hε.le]
      have hz : 1 - ε ≤ P / (P + 1) := by
        apply (le_div_iff₀ hPden).mpr
        nlinarith only [hεP]
      let K := (b, x.2) :: L
      have hKpar : ∀ y ∈ K, 0 < y.1 ∧ 1 < y.2 := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨hb, hx.2⟩
        · exact htail y hy
      have hKcaps : ∀ y ∈ K, y.2 < P := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hPp
        · exact (hbelow y hy).trans hPp
      have hKdec : K.Pairwise (fun y z => z.2 < y.2) :=
        List.pairwise_cons.mpr ⟨hbelow, hLdec⟩
      let J := ofList K P hP1 hKpar hKcaps hKdec
      refine ⟨J, le_refl _, ?_, up_of_uniform J ?_⟩
      · rw [ofList_cap]
        exact fold_loss L htail D (continuationStep b x.2 (P / (P + 1))) ε hε.le
          (hloss ε (P / (P + 1)) hε.le hz)
      · intro t ht
        rw [ofList_uniform]
        by_cases ht0 : t = 0
        · subst t; norm_num
        have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        by_cases htp : t ≤ x.2
        · have htP : t ≤ P := htp.trans hPp.le
          have htC : 0 < t + C := by positivity
          have hta : 0 < t + x.1 := add_pos htpos hx.1
          have ht1 : 0 < t + 1 := by positivity
          have htb : 0 < t + b := by positivity
          have hpair : t / (t + C) * (t / (t + x.1)) ≤
              t / (t + 1) * (t / (t + b)) := by
            rw [div_mul_div_comm, div_mul_div_comm]
            exact div_le_div_of_nonneg_left (mul_nonneg ht ht) (mul_pos ht1 htb) (hprod t ht)
          have hQ := reject_prod_nonneg L htail t htpos
          have hrej := mul_le_mul_of_nonneg_right hpair hQ
          have h := hUP t htpos
          have hhead : triangularReject x.1 x.2 t = t / (t + x.1) := by
            simp [triangularReject, htpos.not_ge, htp]
          have hbound : triangularReject b x.2 t = t / (t + b) := by
            simp [triangularReject, htpos.not_ge, htp]
          have hterm : triangularReject 1 P t = t / (t + 1) := by
            simp [triangularReject, htpos.not_ge, htP]
          simp only [List.map_cons, List.prod_cons, hhead] at h
          simp only [K, List.map_cons, List.prod_cons, hbound, hterm]
          nlinarith only [h, mul_le_mul_of_nonneg_left (sub_le_sub_left hrej 1) ht]
        · have habove : ∀ y ∈ K, y.2 < t := by
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact lt_of_not_ge htp
            · exact (hbelow y hy).trans (lt_of_not_ge htp)
          rw [reject_prod_above K t htpos habove, mul_one]
          exact terminal_bound P t ht
