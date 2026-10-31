-- Prove2me | solution 1 for MinBuying.triangular_list_pruning
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:51:59.488285+00:00
-- url     : https://prove2.me/submissions/8b3c82d4-311d-486b-90fe-6d2ff9260ad7

import Definitions.Def_MinBuying_Triangular

open MinBuying

noncomputable section

private lemma reject_bounds (a v t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    0 ≤ triangularReject a v t ∧ triangularReject a v t ≤ 1 := by
  unfold triangularReject
  rw [if_neg ht.not_ge]
  split_ifs
  · exact ⟨div_nonneg ht.le (add_pos ht ha).le,
      (div_le_one (add_pos ht ha)).mpr (by linarith)⟩
  · norm_num

private lemma prod_bounds (L : List (ℝ × ℝ))
    (ha : ∀ x ∈ L, 0 < x.1) (t : ℝ) (ht : 0 < t) :
    0 ≤ (L.map (fun x => triangularReject x.1 x.2 t)).prod ∧
      (L.map (fun x => triangularReject x.1 x.2 t)).prod ≤ 1 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := reject_bounds x.1 x.2 t (ha x (by simp)) ht
    have hL := ih (fun y hy => ha y (by simp [hy]))
    simp only [List.map_cons, List.prod_cons]
    exact ⟨mul_nonneg hx.1 hL.1, (mul_le_mul_of_nonneg_left hL.2 hx.1).trans (by simpa using hx.2)⟩

private lemma step_nonneg (a v C : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hC : 0 ≤ C) : 0 ≤ continuationStep a v C := by
  unfold continuationStep
  positivity

private lemma step_upper (a v C B : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hvB : v ≤ B) (hCB : C ≤ B) : continuationStep a v C ≤ B := by
  have hd : 0 < 1 + a / v := by positivity
  unfold continuationStep
  apply (div_le_iff₀ hd).mpr
  have hmul : a ≤ B * (a / v) := by
    have := mul_le_mul_of_nonneg_right hvB (div_nonneg ha.le hv.le)
    simpa [mul_div_cancel₀ _ hv.ne', mul_comm v] using this
  nlinarith only [hCB, hmul]

private lemma low_fold_upper (L : List (ℝ × ℝ))
    (hpar : ∀ x ∈ L, 0 < x.1 ∧ 0 < x.2 ∧ x.2 ≤ 1)
    (C B : ℝ) (hB : 1 ≤ B) (hCB : C ≤ B) :
    L.foldl (fun S x => continuationStep x.1 x.2 S) C ≤ B := by
  induction L generalizing C with
  | nil => exact hCB
  | cons x L ih =>
    have hx := hpar x (by simp)
    exact ih (fun y hy => hpar y (by simp [hy])) _
      (step_upper x.1 x.2 C B hx.1 hx.2.1 (hx.2.2.trans hB) hCB)

private lemma prune_low (L : List (ℝ × ℝ))
    (hpar : ∀ x ∈ L, 0 < x.1 ∧ 0 < x.2)
    (hdec : L.Pairwise (fun x y => y.2 ≤ x.2)) (C : ℝ) (hC : 0 ≤ C) :
    ∃ M : List (ℝ × ℝ), M.length ≤ L.length ∧
      (∀ x ∈ M, 0 < x.1 ∧ 1 < x.2) ∧
      M.Pairwise (fun x y => y.2 ≤ x.2) ∧
      (∀ x ∈ M, x ∈ L) ∧
      L.foldl (fun S x => continuationStep x.1 x.2 S) C ≤
        max 1 (M.foldl (fun S x => continuationStep x.1 x.2 S) C) ∧
      (∀ t : ℝ, 0 < t →
        (L.map (fun x => triangularReject x.1 x.2 t)).prod ≤
          (M.map (fun x => triangularReject x.1 x.2 t)).prod) := by
  induction L generalizing C with
  | nil => exact ⟨[], le_refl _, by simp, by simp, by simp, le_max_right _ _, by simp⟩
  | cons x L ih =>
    have hx := hpar x (by simp)
    have htail : ∀ y ∈ L, 0 < y.1 ∧ 0 < y.2 := fun y hy => hpar y (by simp [hy])
    obtain ⟨hbelow,hLdec⟩ := List.pairwise_cons.mp hdec
    by_cases hxcap : 1 < x.2
    · obtain ⟨M, hlen, hMpar, hMdec, hsub, hfold, hprod⟩ :=
        ih htail hLdec (continuationStep x.1 x.2 C) (step_nonneg _ _ _ hx.1 hx.2 hC)
      refine ⟨x :: M, by simpa using hlen, ?_, ?_, ?_, hfold, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨hx.1,hxcap⟩
        · exact hMpar y hy
      · exact List.pairwise_cons.mpr ⟨fun y hy => hbelow y (hsub y hy),hMdec⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · simp
        · exact List.mem_cons_of_mem _ (hsub y hy)
      · intro t ht
        simp only [List.map_cons,List.prod_cons]
        exact mul_le_mul_of_nonneg_left (hprod t ht) (reject_bounds _ _ _ hx.1 ht).1
    · have hlow : ∀ y ∈ x :: L, 0 < y.1 ∧ 0 < y.2 ∧ y.2 ≤ 1 := by
        intro y hy
        have h := hpar y hy
        refine ⟨h.1,h.2,?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_of_not_gt hxcap
        · exact (hbelow y hy).trans (le_of_not_gt hxcap)
      refine ⟨[], by simp, by simp, by simp, by simp, ?_, ?_⟩
      · exact low_fold_upper (x :: L) hlow C (max 1 C) (le_max_left _ _) (le_max_right _ _)
      · intro t ht
        exact (prod_bounds _ (fun y hy => (hpar y hy).1) t ht).2

private lemma equal_cap_merge (a c v : ℝ) (ha : 0 < a) (hc : 0 < c) (hv : 0 < v) :
    let b := a + c + a * c / v
    0 < b ∧
      (∀ C : ℝ, continuationStep c v (continuationStep a v C) = continuationStep b v C) ∧
      (∀ t : ℝ, 0 < t →
        triangularReject a v t * triangularReject c v t ≤ triangularReject b v t) := by
  let b := a + c + a * c / v
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨hb, ?_, ?_⟩
  · intro C
    have hdA : 1 + a / v ≠ 0 := (by positivity : 0 < 1 + a / v).ne'
    have hdC : 1 + c / v ≠ 0 := (by positivity : 0 < 1 + c / v).ne'
    have hdB : 1 + b / v ≠ 0 := (by positivity : 0 < 1 + b / v).ne'
    unfold continuationStep
    field_simp
    ring
  · intro t ht
    by_cases htv : t ≤ v
    · simp only [triangularReject, if_neg ht.not_ge, if_pos htv]
      have hta : 0 < t + a := add_pos ht ha
      have htc : 0 < t + c := add_pos ht hc
      have htb : 0 < t + b := add_pos ht hb
      have hid : (t + a) * (t + c) - t * (t + b) = a * c / v * (v - t) := by
        dsimp [b]
        field_simp
        ring
      have hcore : t * (t + b) ≤ (t + a) * (t + c) := by
        have hnn : 0 ≤ a * c / v * (v - t) :=
          mul_nonneg (div_nonneg (mul_nonneg ha.le hc.le) hv.le) (sub_nonneg.mpr htv)
        linarith only [hid,hnn]
      rw [div_mul_div_comm]
      apply (div_le_div_iff₀ (mul_pos hta htc) htb).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hcore ht.le]
    · simp [triangularReject, ht.not_ge, htv]

private lemma merge_ordered (k : ℕ) (L : List (ℝ × ℝ)) (hlen : L.length ≤ k)
    (hpar : ∀ x ∈ L, 0 < x.1 ∧ 1 < x.2)
    (hdec : L.Pairwise (fun x y => y.2 ≤ x.2)) :
    ∃ M : List (ℝ × ℝ), M.length ≤ L.length ∧
      (∀ x ∈ M, 0 < x.1 ∧ 1 < x.2) ∧
      M.Pairwise (fun x y => y.2 < x.2) ∧
      (∀ x ∈ M, ∃ y ∈ L, x.2 = y.2) ∧
      (∀ C : ℝ, L.foldl (fun S x => continuationStep x.1 x.2 S) C =
        M.foldl (fun S x => continuationStep x.1 x.2 S) C) ∧
      (∀ t : ℝ, 0 < t →
        (L.map (fun x => triangularReject x.1 x.2 t)).prod ≤
          (M.map (fun x => triangularReject x.1 x.2 t)).prod) := by
  induction k generalizing L with
  | zero =>
    have hnil : L = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst L
    exact ⟨[],le_refl _,by simp,by simp,by simp,by simp,by simp⟩
  | succ k ih =>
    cases L with
    | nil => exact ⟨[],le_refl _,by simp,by simp,by simp,by simp,by simp⟩
    | cons x T =>
      cases T with
      | nil =>
        refine ⟨[x],le_refl _,hpar,by simp,?_,by simp,by simp⟩
        intro y hy
        simp only [List.mem_singleton] at hy
        subst y
        exact ⟨x,by simp,rfl⟩
      | cons y L =>
        have hx := hpar x (by simp)
        have hy := hpar y (by simp)
        have htail : ∀ z ∈ y :: L, 0 < z.1 ∧ 1 < z.2 :=
          fun z hz => hpar z (List.mem_cons_of_mem x hz)
        obtain ⟨hbelowX,hTdec⟩ := List.pairwise_cons.mp hdec
        obtain ⟨hbelowY,hLdec⟩ := List.pairwise_cons.mp hTdec
        have hyx : y.2 ≤ x.2 := hbelowX y (by simp)
        by_cases heq : y.2 = x.2
        · let b := x.1 + y.1 + x.1 * y.1 / x.2
          let z : ℝ × ℝ := (b,x.2)
          have hmerge := equal_cap_merge x.1 y.1 x.2 hx.1 hy.1 (lt_trans zero_lt_one hx.2)
          change 0 < b ∧
            (∀ C : ℝ, continuationStep y.1 x.2 (continuationStep x.1 x.2 C) = continuationStep b x.2 C) ∧
            (∀ t : ℝ, 0 < t → triangularReject x.1 x.2 t * triangularReject y.1 x.2 t ≤
              triangularReject b x.2 t) at hmerge
          have hWpar : ∀ u ∈ z :: L, 0 < u.1 ∧ 1 < u.2 := by
            intro u hu
            rcases List.mem_cons.mp hu with rfl | hu
            · exact ⟨hmerge.1,hx.2⟩
            · exact hpar u (by simp [hu])
          have hWdec : (z :: L).Pairwise (fun u w => w.2 ≤ u.2) := by
            apply List.pairwise_cons.mpr
            exact ⟨fun u hu => hbelowX u (by simp [hu]),hLdec⟩
          obtain ⟨M,hMlen,hMpar,hMdec,hMsupport,hMeq,hMprod⟩ :=
            ih (z :: L) (by simp only [List.length_cons] at hlen ⊢; omega) hWpar hWdec
          refine ⟨M,hMlen.trans (by simp),hMpar,hMdec,?_,?_,?_⟩
          · intro u hu
            obtain ⟨w,hw,huweq⟩ := hMsupport u hu
            rcases List.mem_cons.mp hw with rfl | hw
            · exact ⟨x,by simp,huweq⟩
            · exact ⟨w,by simp [hw],huweq⟩
          · intro C
            calc
              (x :: y :: L).foldl (fun S u => continuationStep u.1 u.2 S) C =
                  (z :: L).foldl (fun S u => continuationStep u.1 u.2 S) C := by
                simp only [List.foldl_cons]
                change L.foldl _ (continuationStep y.1 y.2 (continuationStep x.1 x.2 C)) =
                  L.foldl _ (continuationStep b x.2 C)
                rw [heq,hmerge.2.1 C]
              _ = _ := hMeq C
          · intro t ht
            have hLnonneg := (prod_bounds L (fun u hu => (hpar u (by simp [hu])).1) t ht).1
            calc
              ((x :: y :: L).map (fun u => triangularReject u.1 u.2 t)).prod ≤
                  ((z :: L).map (fun u => triangularReject u.1 u.2 t)).prod := by
                simp only [List.map_cons,List.prod_cons]
                change triangularReject x.1 x.2 t *
                    (triangularReject y.1 y.2 t * (L.map (fun u => triangularReject u.1 u.2 t)).prod) ≤
                  triangularReject b x.2 t * (L.map (fun u => triangularReject u.1 u.2 t)).prod
                rw [heq,← mul_assoc]
                exact mul_le_mul_of_nonneg_right (hmerge.2.2 t ht) hLnonneg
              _ ≤ _ := hMprod t ht
        · have hyxlt : y.2 < x.2 := lt_of_le_of_ne hyx heq
          obtain ⟨M,hMlen,hMpar,hMdec,hMsupport,hMeq,hMprod⟩ :=
            ih (y :: L) (by simp only [List.length_cons] at hlen ⊢; omega) htail hTdec
          refine ⟨x :: M,by simpa using hMlen,?_,?_,?_,?_,?_⟩
          · intro u hu
            rcases List.mem_cons.mp hu with rfl | hu
            · exact hx
            · exact hMpar u hu
          · apply List.pairwise_cons.mpr
            refine ⟨?_,hMdec⟩
            intro u hu
            obtain ⟨w,hw,huweq⟩ := hMsupport u hu
            rw [huweq]
            have hwy : w.2 ≤ y.2 := by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact le_refl _
              · exact hbelowY w hw
            exact hwy.trans_lt hyxlt
          · intro u hu
            rcases List.mem_cons.mp hu with rfl | hu
            · exact ⟨u,by simp,rfl⟩
            · obtain ⟨w,hw,huweq⟩ := hMsupport u hu
              exact ⟨w,List.mem_cons_of_mem _ hw,huweq⟩
          · intro C
            exact hMeq (continuationStep x.1 x.2 C)
          · intro t ht
            simp only [List.map_cons,List.prod_cons]
            exact mul_le_mul_of_nonneg_left (hMprod t ht) (reject_bounds _ _ _ hx.1 ht).1

theorem solution (L : List (ℝ × ℝ))
    (hpar : ∀ x ∈ L, 0 < x.1 ∧ 0 < x.2)
    (hdec : L.Pairwise (fun x y => y.2 ≤ x.2))
    (hfinal : 1 < L.foldl (fun S x => continuationStep x.1 x.2 S) 0) :
    ∃ M : List (ℝ × ℝ), M.length ≤ L.length ∧
      (∀ x ∈ M, 0 < x.1 ∧ 1 < x.2) ∧
      M.Pairwise (fun x y => y.2 < x.2) ∧
      L.foldl (fun S x => continuationStep x.1 x.2 S) 0 ≤
        M.foldl (fun S x => continuationStep x.1 x.2 S) 0 ∧
      (∀ t : ℝ, 0 < t →
        (L.map (fun x => triangularReject x.1 x.2 t)).prod ≤
          (M.map (fun x => triangularReject x.1 x.2 t)).prod) := by
  obtain ⟨K,hKlen,hKpar,hKdec,hKsub,hKfold,hKprod⟩ := prune_low L hpar hdec 0 (le_refl _)
  have hK : L.foldl (fun S x => continuationStep x.1 x.2 S) 0 ≤
      K.foldl (fun S x => continuationStep x.1 x.2 S) 0 := by
    rcases le_max_iff.mp hKfold with h | h
    · exact False.elim (not_lt_of_ge h hfinal)
    · exact h
  obtain ⟨M,hMlen,hMpar,hMdec,hMsupport,hMeq,hMprod⟩ :=
    merge_ordered K.length K (le_refl _) hKpar hKdec
  refine ⟨M,hMlen.trans hKlen,hMpar,hMdec,?_,?_⟩
  · simpa only [hMeq 0] using hK
  · intro t ht
    exact (hKprod t ht).trans (hMprod t ht)
