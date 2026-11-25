-- Prove2me | solution 1 for IntConeFPT.counted_grid
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:38:41.98332+00:00
-- url     : https://prove2.me/submissions/33d9d967-4b1e-4a5b-b649-855d6949bca9

import Theorems.Thm_IntConeFPT_polytope_height_product
import Definitions.Def_IntConeFPT_Problem
open OnlineCRS.Combine IntConeFPT RobustToDynamics
namespace IntConeFPT.BudgetGrid
private lemma bitCap (n : ℕ) : n < 2 ^ (encNat n).length := by
  have hp (p : PosNum) : (p : ℕ) < 2 ^ (Computability.encodePosNum p).length := by
    induction p with
    | one => decide
    | bit0 p ih => simp [Computability.encodePosNum, PosNum.cast_bit0, pow_succ]; omega
    | bit1 p ih => simp [Computability.encodePosNum, PosNum.cast_bit1, pow_succ]; omega
  simp only [encNat, List.length_map, Computability.encodeNat]
  conv_lhs => rw [← Num.to_of_nat n]
  cases (n : Num) with
  | zero => decide
  | pos p => exact hp p

private def H (q : ℚ) := (q.num.natAbs + 1) * q.den

private lemma height (q : ℚ) : H q ≤ 2 ^ (encRat q).length := by
  have h := Nat.mul_le_mul (bitCap q.num.natAbs) (bitCap q.den).le
  unfold H
  refine h.trans ?_
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  simp [encRat, encInt]; omega

private lemma concatCap {α : Type} (h : α → ℕ) (f : α → List Sym)
    (hf : ∀ x, h x ≤ 2 ^ (f x).length) (xs : List α) :
    (xs.map h).prod ≤ 2 ^ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa [pow_add] using Nat.mul_le_mul (hf x) ih

private lemma vecCap {k : ℕ} (x : Fin k → ℚ) : ∏ j, H (x j) ≤ 2 ^ (encVec x).length := by
  rw [Fin.prod_univ_def]
  apply concatCap
  intro j
  exact (height _).trans (Nat.pow_le_pow_right (by decide) (by simp))

private lemma matCap {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℚ) :
    ∏ i, ∏ j, H (A i j) ≤ 2 ^ (encMat A).length := by
  rw [Fin.prod_univ_def]
  apply concatCap
  intro i
  exact (vecCap (A i)).trans (Nat.pow_le_pow_right (by decide) (by simp))

lemma length_flatMap_finRange {n : ℕ} (f : Fin n → List Sym) :
    ((List.finRange n).flatMap f).length = ∑ i : Fin n, (f i).length := by
  rw [List.length_flatMap, Fin.sum_univ_def]

lemma encVec_len_eq {n : ℕ} (v : Fin n → ℚ) :
    (encVec v).length = ∑ j : Fin n, ((encRat (v j)).length + 1) := by
  unfold encVec
  rw [length_flatMap_finRange]
  simp [List.length_append]

lemma card_le_encVec_len {n : ℕ} (v : Fin n → ℚ) : n ≤ (encVec v).length := by
  rw [encVec_len_eq]
  calc n = ∑ _ : Fin n, 1 := by simp
    _ ≤ ∑ j : Fin n, ((encRat (v j)).length + 1) :=
        Finset.sum_le_sum fun j _ => by omega

lemma sum_encRat_le_encVec_len {n : ℕ} (v : Fin n → ℚ) :
    (∑ j : Fin n, (encRat (v j)).length) ≤ (encVec v).length := by
  rw [encVec_len_eq]
  exact Finset.sum_le_sum fun j _ => Nat.le_succ _

def locBlockLen (I : Instance) (t : Fin I.τ) : ℕ :=
  (encNat (I.m t) ++ [3] ++ encMat (I.Aloc t) ++ encMat (I.Bloc t) ++ encVec (I.bloc t) ++ [3] ++
    encNat (I.deg t) ++ [3] ++ encVec (I.coeff t) ++ [3]).length

lemma locBlockLen_ge (I : Instance) (t : Fin I.τ) :
    1 + (encMat (I.Aloc t)).length + (encMat (I.Bloc t)).length + (encVec (I.bloc t)).length ≤
      locBlockLen I t := by
  unfold locBlockLen
  simp only [List.length_append, List.length_singleton]
  omega

lemma sum_locBlockLen_le (I : Instance) :
    (∑ t : Fin I.τ, locBlockLen I t) +
      ((encMat I.QY).length + (encMat I.QV).length + (encVec I.cQ).length) +
      ((∑ t : Fin I.τ, ((encMat (I.AY t)).length + (encMat (I.AV t)).length)) +
        (encMat I.AN).length + (encVec I.cA).length) + 1 ≤
      (encInstance I).length := by
  have h1 : ((List.finRange I.τ).flatMap (fun t =>
      encNat (I.m t) ++ [3] ++ encMat (I.Aloc t) ++ encMat (I.Bloc t) ++ encVec (I.bloc t) ++ [3] ++
      encNat (I.deg t) ++ [3] ++ encVec (I.coeff t) ++ [3])).length =
      ∑ t : Fin I.τ, locBlockLen I t := length_flatMap_finRange _
  have h2 : ((List.finRange I.τ).flatMap (fun t => encMat (I.AY t) ++ encMat (I.AV t))).length =
      ∑ t : Fin I.τ, ((encMat (I.AY t)).length + (encMat (I.AV t)).length) := by
    rw [length_flatMap_finRange]
    simp [List.length_append]
  unfold encInstance
  simp only [List.length_append, List.length_singleton]
  omega


private lemma integral_cost (I : Instance) : ∀ μ : Mult I, ∃ z : ℤ,
    ((∏ t, ∏ j, (I.coeff t j).den : ℕ) : ℝ) * I.cost μ = (z : ℝ) := by
  let Q_den : ℕ := ∏ t : Fin I.τ, ∏ j : Fin (monomials I.d (I.deg t)).length, (I.coeff t j).den
  have hQ_pos : 0 < Q_den := by
    refine Finset.prod_pos fun t _ => Finset.prod_pos fun j _ => (I.coeff t j).pos
  let coeffZ : (t : Fin I.τ) → Fin (monomials I.d (I.deg t)).length → ℤ := fun t j =>
    (I.coeff t j).num * ((Q_den / (I.coeff t j).den : ℕ) : ℤ)
  have hcoeff_eq : ∀ t j, (coeffZ t j : ℝ) = (Q_den : ℝ) * (I.coeff t j : ℝ) := by
    intro t j
    have hdvd : (I.coeff t j).den ∣ Q_den :=
      dvd_trans (Finset.dvd_prod_of_mem (fun j => (I.coeff t j).den) (Finset.mem_univ j))
        (Finset.dvd_prod_of_mem _ (Finset.mem_univ t))
    have hmul_den : ((Q_den / (I.coeff t j).den : ℕ) : ℝ) * ((I.coeff t j).den : ℝ) = (Q_den : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hden_ne : ((I.coeff t j).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (I.coeff t j).pos.ne'
    have hq_eq : (I.coeff t j : ℝ) = ((I.coeff t j).num : ℝ) / ((I.coeff t j).den : ℝ) := by
      rw [Rat.cast_def]
    calc (coeffZ t j : ℝ)
      _ = ((I.coeff t j).num : ℝ) * ((Q_den / (I.coeff t j).den : ℕ) : ℝ) := by
          simp only [coeffZ, Int.cast_mul, Int.cast_natCast]
      _ = ((I.coeff t j).num : ℝ) * ((Q_den : ℝ) / ((I.coeff t j).den : ℝ)) := by
          rw [(eq_div_iff hden_ne).mpr hmul_den]
      _ = (Q_den : ℝ) * (((I.coeff t j).num : ℝ) / ((I.coeff t j).den : ℝ)) := by ring
      _ = (Q_den : ℝ) * (I.coeff t j : ℝ) := by rw [← hq_eq]
  have hcost_int : ∀ μ : Mult I, ∃ z : ℤ, (Q_den : ℝ) * I.cost μ = (z : ℝ) := by
    intro μ
    let fZ : (t : Fin I.τ) → (Fin I.d → ℤ) → ℤ := fun t x =>
      ∑ j : Fin (monomials I.d (I.deg t)).length,
        coeffZ t j * ∏ i, x i ^ ((monomials I.d (I.deg t)).get j i)
    refine ⟨∑ t : Fin I.τ, (μ t).sum fun g n => (n : ℤ) * fZ t g.1, ?_⟩
    unfold Instance.cost costOf
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hf_eq : (Q_den : ℝ) * ((μ t g : ℝ) * I.f t (fun i => (g.1 i : ℝ))) =
        (μ t g : ℝ) * (fZ t g.1 : ℝ) := by
      rw [mul_left_comm]
      congr 1
      simp only [fZ, Instance.f, Finset.mul_sum, Int.cast_sum, Int.cast_mul, Int.cast_prod,
        Int.cast_pow, hcoeff_eq]
      refine Finset.sum_congr rfl fun j _ => by ring
    exact hf_eq
  exact hcost_int

private lemma mon_nonempty (d D : ℕ) : (monomials d D).length ≠ 0 := by
  induction d generalizing D with
  | zero => simp [monomials]
  | succ d ih =>
    have h := List.exists_mem_of_ne_nil (monomials d (D-0)) (show monomials d (D-0) ≠ [] by
      intro e; exact ih (D-0) (by rw [e]; rfl))
    obtain ⟨v,hv⟩ := h
    have hm : (Fin.cons 0 v : Fin (d+1) → ℕ) ∈ monomials (d+1) D :=
      List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (Nat.zero_lt_succ _), List.mem_map.mpr ⟨v,hv,rfl⟩⟩
    intro hh; simp_all

private lemma degree_len (d D : ℕ) : D ≤ (monomials (d+1) D).length := by
  let f := fun e => (monomials d (D-e)).map (fun r => (Fin.cons e r : Fin (d+1) → ℕ))
  have aux (l : List ℕ) : l.length ≤ (l.flatMap f).length := by
    induction l with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append,f,List.length_map]
      have := mon_nonempty d (D-hd)
      dsimp only [f] at ih
      omega
  exact (Nat.le_succ D).trans (by simpa only [List.length_range, monomials, f] using aux (List.range (D+1)))

private lemma total_degree (d D : ℕ) (v : Fin d → ℕ) (hv : v ∈ monomials d D) :
    ∑ i, v i ≤ D := by
  induction d generalizing D with
  | zero => simp
  | succ d ih =>
    obtain ⟨e,he,h⟩ := List.mem_flatMap.mp hv
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
    have := ih _ _ hr
    have he' := List.mem_range.mp he
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]; omega

end IntConeFPT.BudgetGrid
open IntConeFPT.BudgetGrid

set_option maxHeartbeats 900000 in
theorem solution (I : Instance) (hI : I.Valid) (N : ℕ) :
    let L := (encInstance I ++ encNat N ++ [3]).length
    let q := ∏ t, ∏ j, (I.coeff t j).den
    0 < q ∧ q ≤ 2^L ∧ ∀ μ : Mult I, I.FeasibleN N μ →
      ∃ z : ℤ, (q : ℝ) * I.cost μ = z ∧ z.natAbs ≤ 2^(L^2+4*L) := by
  intro L q
  let B := 2^L
  have hL : (encInstance I).length ≤ L := by simp [L]; omega
  have ht : ∑ t, locBlockLen I t ≤ L := by have := sum_locBlockLen_le I; omega
  have hloc t : locBlockLen I t ≤ L :=
    (Finset.single_le_sum (fun k _ => Nat.zero_le (locBlockLen I k)) (Finset.mem_univ t)).trans ht
  have hvlen t : (encVec (I.coeff t)).length ≤ locBlockLen I t := by
    simp only [locBlockLen,List.length_append]; omega
  have hprod t : ∏ j, (I.coeff t j).den ≤ ∏ j, H (I.coeff t j) := by
    exact Finset.prod_le_prod' (fun j _ => by
      dsimp [H]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hq : q ≤ B := calc
    _ ≤ ∏ t, 2^(locBlockLen I t) := Finset.prod_le_prod' fun t _ =>
      (hprod t).trans ((vecCap _).trans (Nat.pow_le_pow_right (by decide) (hvlen t)))
    _ = 2^(∑ t, locBlockLen I t) := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) ht
  refine ⟨Finset.prod_pos fun t _ => Finset.prod_pos fun j _ => Rat.pos _,hq,?_⟩
  have box t (g : Gen I.d I.k) (hg : g ∈ I.S t) : ∀ i, |(g.1 i : ℝ)| ≤ B := by
    have hb := polytope_height_product (I.Aloc t) (I.Bloc t) (I.bloc t) (hI.bounded t) g.toReal hg
    have h := Nat.mul_le_mul (Nat.mul_le_mul (matCap (I.Aloc t)) (matCap (I.Bloc t))) (vecCap (I.bloc t))
    rw [← pow_add,← pow_add] at h
    have hh := locBlockLen_ge I t
    have hh' := hloc t
    have cap := h.trans (Nat.pow_le_pow_right (by decide) (by omega : _ ≤ L))
    exact fun i => (hb.1 i).trans (Nat.cast_le.mpr cap)
  have hB1 : (1:ℝ) ≤ (B : ℝ) := by exact_mod_cast (Nat.one_le_two_pow (n:=L))
  have hf t (g : Gen I.d I.k) (hg : g ∈ I.S t) :
      |I.f t (fun i => (g.1 i : ℝ))| ≤ (L:ℝ) * B * (B:ℝ)^L := by
    have hm := (card_le_encVec_len (I.coeff t)).trans ((hvlen t).trans (hloc t))
    have hdeg : I.deg t ≤ L := by
      have := hI.one_le_d
      have hh := degree_len (I.d-1) (I.deg t)
      rw [show I.d-1+1 = I.d by omega] at hh
      exact hh.trans hm
    unfold Instance.f
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin (monomials I.d (I.deg t)).length, (B:ℝ) * (B:ℝ)^L := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul,Finset.abs_prod]
        apply mul_le_mul _ _ (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) (Nat.cast_nonneg _)
        · have hl : (encRat (I.coeff t j)).length ≤ L :=
            (Finset.single_le_sum (fun i _ => Nat.zero_le (encRat (I.coeff t i)).length) (Finset.mem_univ j)).trans
              ((sum_encRat_le_encVec_len _).trans ((hvlen t).trans (hloc t)))
          let c := I.coeff t j
          have hnum : c.num.natAbs ≤ B := calc
            _ ≤ H c := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ c.pos)
            _ ≤ _ := (height c).trans (Nat.pow_le_pow_right (by decide) hl)
          change |(c : ℝ)| ≤ _
          rw [Rat.cast_def, abs_div, abs_of_nonneg (Nat.cast_nonneg c.den : (0:ℝ) ≤ c.den)]
          apply (div_le_iff₀ (Nat.cast_pos.mpr c.pos)).mpr
          exact le_trans (by simpa only [Nat.cast_natAbs,Int.cast_abs] using
            (Nat.cast_le.mpr hnum : (c.num.natAbs : ℝ) ≤ B))
            (le_mul_of_one_le_right (Nat.cast_nonneg _) (Nat.one_le_cast.mpr c.pos))
        · let v := (monomials I.d (I.deg t)).get j
          have hds := (total_degree _ _ v (List.get_mem ..)).trans hdeg
          simp_rw [abs_pow]
          calc
            _ ≤ ∏ i, (B:ℝ)^(v i) := Finset.prod_le_prod
              (fun _ _ => by positivity) (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (box t g hg i) _)
            _ = _ := Finset.prod_pow_eq_pow_sum ..
            _ ≤ _ := pow_le_pow_right₀ hB1 hds
      _ ≤ _ := by simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
                  rw [mul_assoc]; gcongr
  intro μ hμ
  obtain ⟨z,hz⟩ := integral_cost I μ
  refine ⟨z,hz,?_⟩
  let F : ℝ := (L:ℝ) * B * (B:ℝ)^L
  have hcost : |I.cost μ| ≤ (N:ℝ)*F := by
    unfold Instance.cost
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, (count (μ t) : ℝ) * F := by
        apply Finset.sum_le_sum; intro t _
        unfold costOf count Finsupp.sum
        rw [Nat.cast_sum, Finset.sum_mul]
        apply (Finset.abs_sum_le_sum_abs ..).trans
        apply Finset.sum_le_sum; intro g hg
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hf t g (hμ.1.1 t hg)) (Nat.cast_nonneg _)
      _ = (I.totalCount μ : ℝ)*F := by simp [Instance.totalCount,Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hμ.2)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg (Nat.cast_nonneg _) _))
  have hN : N ≤ B := (bitCap N).le.trans (Nat.pow_le_pow_right (by decide) (by simp [L]; omega))
  have hLB : L ≤ B := (Nat.lt_two_pow_self (n:=L)).le
  have bound : q * (N*(L*B*B^L)) ≤ 2^(L^2+4*L) := calc
    _ ≤ B*(B*(B*B*B^L)) := Nat.mul_le_mul hq (Nat.mul_le_mul hN
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hLB)))
    _ = _ := by dsimp [B]; ring
  have haz : |(z:ℝ)| ≤ (2^(L^2+4*L) : ℕ) := by
    rw [← hz,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    change (q : ℝ) * |I.cost μ| ≤ _
    exact (mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg _)).trans (by
      simpa only [F,Nat.cast_mul,Nat.cast_pow] using
        (Nat.cast_le.mpr bound : ((q*(N*(L*B*B^L)) : ℕ) : ℝ) ≤ ((2^(L^2+4*L) : ℕ) : ℝ)))
  apply (Nat.cast_le (α:=ℝ)).mp
  simpa only [Nat.cast_natAbs,Int.cast_abs] using haz
