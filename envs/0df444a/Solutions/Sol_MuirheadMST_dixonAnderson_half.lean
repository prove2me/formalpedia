-- Prove2me | solution 1 for MuirheadMST.dixonAnderson_half
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:20:33.101774+00:00
-- url     : https://prove2.me/submissions/e9d67f74-4290-440b-91fe-94a50318eb3d

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

/-!
Dixon-Anderson integral with all exponents `1/2`. For strictly decreasing `l`, the map
`μ ↦ (w_1, …, w_m)`, `w_i = ∏_j (l_i - μ_j) / ∏_{k ≠ i} (l_i - l_k)`, sends the interlacing region
bijectively onto the open simplex, with Jacobian `V(μ)/V(l)`; the integral becomes a Dirichlet integral.
-/

open MeasureTheory Polynomial Finset

noncomputable section

namespace DixonHalf

variable {m : ℕ}


lemma prod_erase_eq_prod_succAbove {M : Type*} [CommMonoid M] {n : ℕ} (i : Fin (n + 1))
    (f : Fin (n + 1) → M) : ∏ k ∈ univ.erase i, f k = ∏ j, f (i.succAbove j) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ, Finset.prod_image]
  intro a _ b _ h
  exact Fin.succAbove_right_injective h

/-- `P'(l_i) = ∏_{k ≠ i} (l_i - l_k)`. -/
def Pd (l : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : ℝ := ∏ k ∈ univ.erase i, (l i - l k)

/-- The partial-fraction weights `w_i(μ) = ∏_j (l_i - μ_j) / ∏_{k ≠ i} (l_i - l_k)`. -/
def wt (l : Fin (m + 1) → ℝ) (μ : Fin m → ℝ) (i : Fin (m + 1)) : ℝ := (∏ j, (l i - μ j)) / Pd l i

/-- `∏_{k ≠ i} (X - l_k)`. -/
def N (l : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : ℝ[X] := ∏ k ∈ univ.erase i, (X - C (l k))

/-- `∑_i W_i ∏_{k ≠ i} (X - l_k)`. -/
def R (l : Fin (m + 1) → ℝ) (W : Fin (m + 1) → ℝ) : ℝ[X] := ∑ i, C (W i) * N l i

/-- `∏_j (X - μ_j)`. -/
def Qp (μ : Fin m → ℝ) : ℝ[X] := ∏ j, (X - C (μ j))

/-- The interlacing region. -/
def U (l : Fin (m + 1) → ℝ) : Set (Fin m → ℝ) :=
  {μ | ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i}

lemma Pd_ne {l : Fin (m + 1) → ℝ} (hl : Function.Injective l) (i : Fin (m + 1)) : Pd l i ≠ 0 := by
  unfold Pd
  rw [prod_ne_zero_iff]
  intro k hk
  exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hk) (hl h).symm

lemma N_monic (l : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : (N l i).Monic :=
  Lagrange.nodal_monic (s := univ.erase i) (v := l)

lemma N_natDegree (l : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : (N l i).natDegree = m := by
  apply natDegree_eq_of_degree_eq_some
  have : (N l i).degree = ((univ.erase i).card : WithBot ℕ) := Lagrange.degree_nodal
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.add_sub_cancel]

lemma eval_N (l : Fin (m + 1) → ℝ) (i k : Fin (m + 1)) :
    eval (l k) (N l i) = if k = i then Pd l i else 0 := by
  have : eval (l k) (N l i) = ∏ j ∈ univ.erase i, (l k - l j) :=
    Lagrange.eval_nodal (s := univ.erase i) (v := l)
  rw [this]
  split_ifs with h
  · subst h; rfl
  · exact prod_eq_zero (mem_erase.mpr ⟨h, mem_univ _⟩) (sub_self _)

lemma eval_R (l : Fin (m + 1) → ℝ) (W : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    eval (l k) (R l W) = W k * Pd l k := by
  simp [R, eval_finsetSum, eval_N]

lemma R_natDegree_le (l : Fin (m + 1) → ℝ) (W : Fin (m + 1) → ℝ) : (R l W).natDegree ≤ m := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans (N_natDegree l i).le

lemma R_coeff (l : Fin (m + 1) → ℝ) (W : Fin (m + 1) → ℝ) : (R l W).coeff m = ∑ i, W i := by
  simp only [R, finsetSum_coeff, coeff_C_mul]
  refine sum_congr rfl fun i _ => ?_
  have h := (N_monic l i).coeff_natDegree
  rw [N_natDegree] at h
  rw [h, mul_one]

lemma Qp_monic (μ : Fin m → ℝ) : (Qp μ).Monic := Lagrange.nodal_monic (s := univ) (v := μ)

lemma Qp_natDegree (μ : Fin m → ℝ) : (Qp μ).natDegree = m := by
  apply natDegree_eq_of_degree_eq_some
  have : (Qp μ).degree = ((univ : Finset (Fin m)).card : WithBot ℕ) := Lagrange.degree_nodal
  rw [this, card_univ, Fintype.card_fin]

lemma eval_Qp (μ : Fin m → ℝ) (x : ℝ) : eval x (Qp μ) = ∏ j, (x - μ j) :=
  Lagrange.eval_nodal (s := univ) (v := μ)

/-- Lagrange interpolation of `∏ (X - μ_j)` at the nodes `l`. -/
lemma Qp_eq_R {l : Fin (m + 1) → ℝ} (hl : Function.Injective l) (μ : Fin m → ℝ) :
    Qp μ = R l (wt l μ) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero (v := l) univ hl.injOn ?_ ?_
  · rw [card_univ, Fintype.card_fin]
    refine (degree_le_of_natDegree_le ?_).trans_lt (by exact_mod_cast Nat.lt_succ_self m)
    exact (natDegree_sub_le _ _).trans (max_le (Qp_natDegree μ).le (R_natDegree_le l _))
  · intro k _
    rw [eval_sub, eval_R, eval_Qp, wt, div_mul_cancel₀ _ (Pd_ne hl k), sub_self]

lemma sum_wt {l : Fin (m + 1) → ℝ} (hl : Function.Injective l) (μ : Fin m → ℝ) :
    ∑ i, wt l μ i = 1 := by
  rw [← R_coeff, ← Qp_eq_R hl]
  have h := (Qp_monic μ).coeff_natDegree
  rwa [Qp_natDegree] at h

/-- `W` is determined by `∑ W = 1` and the `m` distinct roots `μ_j` of `R W`. -/
lemma eq_wt {l : Fin (m + 1) → ℝ} (hl : Function.Injective l) {μ : Fin m → ℝ}
    (hμ : Function.Injective μ) {W : Fin (m + 1) → ℝ} (hW : ∑ i, W i = 1)
    (hroot : ∀ j, eval (μ j) (R l W) = 0) : W = wt l μ := by
  have hRQ : R l W = Qp μ := by
    rw [← sub_eq_zero]
    refine eq_zero_of_degree_lt_of_eval_index_eq_zero (v := μ) univ hμ.injOn ?_ ?_
    · rw [card_univ, Fintype.card_fin, degree_lt_iff_coeff_zero]
      intro k hk
      rcases hk.lt_or_eq with hk | rfl
      · rw [coeff_sub, coeff_eq_zero_of_natDegree_lt ((R_natDegree_le l W).trans_lt hk),
          coeff_eq_zero_of_natDegree_lt ((Qp_natDegree μ).le.trans_lt hk), sub_zero]
      · rw [coeff_sub, R_coeff, hW]
        have h := (Qp_monic μ).coeff_natDegree
        rw [Qp_natDegree] at h
        rw [h, sub_self]
    · intro j _
      rw [eval_sub, hroot, eval_Qp, prod_eq_zero (mem_univ j) (sub_self _), sub_zero]
  funext k
  have h1 := eval_R l W k
  rw [hRQ, Qp_eq_R hl, eval_R] at h1
  exact (mul_right_cancel₀ (Pd_ne hl k) h1).symm

lemma strictAnti_of_mem_U {l : Fin (m + 1) → ℝ} (hl : StrictAnti l) {μ : Fin m → ℝ}
    (hμ : μ ∈ U l) : StrictAnti μ := by
  intro i j hij
  calc μ j < l j.castSucc := (hμ j).1
    _ ≤ l i.succ := hl.antitone (Fin.succ_le_castSucc_iff.mpr hij)
    _ < μ i := (hμ i).2

lemma wt_pos {l : Fin (m + 1) → ℝ} (hl : StrictAnti l) {μ : Fin m → ℝ} (hμ : μ ∈ U l)
    (i : Fin (m + 1)) : 0 < wt l μ i := by
  rw [wt, Pd, prod_erase_eq_prod_succAbove i (fun k => l i - l k), ← prod_div_distrib]
  refine prod_pos fun j _ => ?_
  by_cases h : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    apply div_pos_of_neg_of_neg
    · have : l i ≤ l j.succ := hl.antitone (Fin.castSucc_lt_iff_succ_le.mp h)
      linarith [(hμ j).2]
    · linarith [hl h]
  · rw [not_lt] at h
    rw [Fin.succAbove_of_le_castSucc _ _ h]
    apply div_pos
    · have : l j.castSucc ≤ l i := hl.antitone h
      linarith [(hμ j).1]
    · linarith [hl (h.trans_lt Fin.castSucc_lt_succ)]

lemma Pd_mul_neg {l : Fin (m + 1) → ℝ} (hl : StrictAnti l) (j : Fin m) :
    Pd l j.castSucc * Pd l j.succ < 0 := by
  rw [Pd, Pd, prod_erase_eq_prod_succAbove _ (fun k => l j.castSucc - l k),
    prod_erase_eq_prod_succAbove _ (fun k => l j.succ - l k), ← prod_mul_distrib,
    ← mul_prod_erase univ _ (mem_univ j)]
  apply mul_neg_of_neg_of_pos
  · rw [Fin.succAbove_of_le_castSucc _ _ le_rfl, Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ]
    have := hl (Fin.castSucc_lt_succ (i := j))
    nlinarith
  · refine prod_pos fun t ht => ?_
    have htj := ne_of_mem_erase ht
    rcases lt_or_gt_of_ne htj with h | h
    · have h1 : t.castSucc < j.castSucc := Fin.castSucc_lt_castSucc_iff.mpr h
      have h2 : t.castSucc < j.succ := h1.trans Fin.castSucc_lt_succ
      rw [Fin.succAbove_of_castSucc_lt _ _ h1, Fin.succAbove_of_castSucc_lt _ _ h2]
      have := hl h1
      have := hl h2
      nlinarith
    · have h1 : j.castSucc ≤ t.castSucc := Fin.castSucc_le_castSucc_iff.mpr h.le
      have h2 : j.succ ≤ t.castSucc := Fin.succ_le_castSucc_iff.mpr h
      rw [Fin.succAbove_of_le_castSucc _ _ h1, Fin.succAbove_of_le_castSucc _ _ h2]
      have := hl (h1.trans_lt Fin.castSucc_lt_succ)
      have := hl (h2.trans_lt Fin.castSucc_lt_succ)
      nlinarith

lemma exists_root {l : Fin (m + 1) → ℝ} (hl : StrictAnti l) {W : Fin (m + 1) → ℝ}
    (hW : ∀ i, 0 < W i) (j : Fin m) :
    ∃ c, c < l j.castSucc ∧ l j.succ < c ∧ eval c (R l W) = 0 := by
  have hab : l j.succ ≤ l j.castSucc := (hl Fin.castSucc_lt_succ).le
  have hcont : ContinuousOn (fun x => eval x (R l W)) (Set.uIcc (l j.succ) (l j.castSucc)) :=
    (Polynomial.continuous _).continuousOn
  have hprod : eval (l j.succ) (R l W) * eval (l j.castSucc) (R l W) < 0 := by
    rw [eval_R, eval_R]
    have := Pd_mul_neg hl j
    have := mul_pos (hW j.succ) (hW j.castSucc)
    nlinarith
  have h0 : (0 : ℝ) ∈ Set.uIcc (eval (l j.succ) (R l W)) (eval (l j.castSucc) (R l W)) := by
    rw [Set.mem_uIcc]
    rcases mul_neg_iff.mp hprod with h | h
    · right; exact ⟨h.2.le, h.1.le⟩
    · left; exact ⟨h.1.le, h.2.le⟩
  obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc hcont h0
  simp only at hc0
  rw [Set.uIcc_of_le hab] at hc
  refine ⟨c, lt_of_le_of_ne hc.2 ?_, lt_of_le_of_ne hc.1 ?_, hc0⟩
  · rintro rfl
    rw [hc0] at hprod; simp at hprod
  · rintro rfl
    rw [hc0] at hprod; simp at hprod

/-- The map `μ ↦ (w_1, …, w_m)`. -/
def F (l : Fin (m + 1) → ℝ) (μ : Fin m → ℝ) : Fin m → ℝ := fun i => wt l μ i.castSucc

/-- The open simplex. -/
def Δ (m : ℕ) : Set (Fin m → ℝ) := {w | (∀ i, 0 < w i) ∧ ∑ i, w i < 1}

lemma wt_last {l : Fin (m + 1) → ℝ} (hl : Function.Injective l) (μ : Fin m → ℝ) :
    wt l μ (Fin.last m) = 1 - ∑ i, F l μ i := by
  have := sum_wt hl μ
  rw [Fin.sum_univ_castSucc] at this
  simp only [F]; linarith

lemma image_F {l : Fin (m + 1) → ℝ} (hl : StrictAnti l) : F l '' U l = Δ m := by
  ext w
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨fun i => wt_pos hl hμ _, ?_⟩
    have := wt_last hl.injective μ
    have := wt_pos hl hμ (Fin.last m)
    linarith
  · rintro ⟨hw, hsum⟩
    set W : Fin (m + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) w (1 - ∑ i, w i) with hWdef
    have hWpos : ∀ i, 0 < W i := by
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [W]; linarith
      · simp [W, hw i]
    have hWsum : ∑ i, W i = 1 := by simp [W, Fin.sum_univ_castSucc]
    choose μ hμ1 hμ2 hμ3 using exists_root hl hWpos
    have hμU : μ ∈ U l := fun i => ⟨hμ1 i, hμ2 i⟩
    have := eq_wt hl.injective (strictAnti_of_mem_U hl hμU).injective hWsum hμ3
    refine ⟨μ, hμU, funext fun i => ?_⟩
    simp only [F, ← this, W, Fin.snoc_castSucc]

lemma injOn_F {l : Fin (m + 1) → ℝ} (hl : StrictAnti l) : Set.InjOn (F l) (U l) := by
  intro μ hμ μ' hμ' h
  have hw : wt l μ = wt l μ' := by
    funext k
    refine Fin.lastCases ?_ (fun i => congrFun h i) k
    rw [wt_last hl.injective, wt_last hl.injective, h]
  have hQ : Qp μ = Qp μ' := by rw [Qp_eq_R hl.injective, Qp_eq_R hl.injective, hw]
  funext j
  have h0 : eval (μ j) (Qp μ') = 0 := by
    rw [← hQ, eval_Qp, prod_eq_zero (mem_univ j) (sub_self _)]
  rw [eval_Qp, prod_eq_zero_iff] at h0
  obtain ⟨k, _, hk⟩ := h0
  rw [sub_eq_zero] at hk
  rcases lt_trichotomy k j with hkj | rfl | hkj
  · exfalso
    have := hl.antitone (Fin.succ_le_castSucc_iff.mpr hkj)
    linarith [(hμ j).1, (hμ' k).2]
  · exact hk
  · exfalso
    have := hl.antitone (Fin.succ_le_castSucc_iff.mpr hkj)
    linarith [(hμ j).2, (hμ' k).1]


/-- The Jacobian matrix of `F`: `∂w_i/∂μ_j = -∏_{k ≠ j} (l_i - μ_k) / P'(l_i)`. -/
def Mjac (l : Fin (m + 1) → ℝ) (μ : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => -(∏ k ∈ univ.erase j, (l i.castSucc - μ k)) / Pd l i.castSucc

/-- The derivative of `F` as a continuous linear map. -/
def Fd (l : Fin (m + 1) → ℝ) (μ : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Mjac l μ))

lemma hasFDerivAt_F (l : Fin (m + 1) → ℝ) (μ : Fin m → ℝ) : HasFDerivAt (F l) (Fd l μ) μ := by
  rw [hasFDerivAt_pi']
  intro i
  have hg : ∀ j ∈ (univ : Finset (Fin m)), HasFDerivAt (fun x : Fin m → ℝ => l i.castSucc - x j)
      (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j)) μ := by
    intro j _
    exact (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin m => ℝ) j μ).const_sub _
  have h := (HasFDerivAt.finsetProd hg).mul_const (Pd l i.castSucc)⁻¹
  have e : (fun x => F l x i) = fun y => (∏ j, (l i.castSucc - y j)) * (Pd l i.castSucc)⁻¹ := by
    funext x; simp [F, wt, div_eq_mul_inv]
  rw [e]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [Fd, Mjac, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, div_eq_mul_inv]
  exact sum_congr rfl fun j _ => by ring

lemma det_Fd (l : Fin (m + 1) → ℝ) (μ : Fin m → ℝ) : (Fd l μ).det = (Mjac l μ).det := by
  simp [Fd, ContinuousLinearMap.det]



/-- `|V(x)| = ∏_{i<j} |x_i - x_j|`. -/
def AV {n : ℕ} (x : Fin n → ℝ) : ℝ := ∏ i, ∏ j, if i < j then |x i - x j| else 1

lemma AV_pos {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) : 0 < AV x := by
  refine prod_pos fun i _ => prod_pos fun j _ => ?_
  split_ifs with h
  · exact abs_pos.mpr (sub_ne_zero.mpr fun e => h.ne (hx e))
  · exact one_pos

lemma vandermondeProd_eq_AV {n : ℕ} {x : Fin n → ℝ} (hx : StrictAnti x) :
    MuirheadMST.vandermondeProd x = AV x := by
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [abs_of_pos (sub_pos.mpr (hx h))]
  · rfl

lemma abs_det_vandermonde {n : ℕ} (x : Fin n → ℝ) : |(Matrix.vandermonde x).det| = AV x := by
  rw [Matrix.det_vandermonde, abs_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [abs_prod, ← prod_filter]
  refine prod_congr (by ext j; simp) fun j _ => abs_sub_comm _ _

lemma prod_prod_erase_abs {n : ℕ} (x : Fin n → ℝ) :
    ∏ i, ∏ k ∈ univ.erase i, |x i - x k| = AV x ^ 2 := by
  have h : ∀ i, ∏ k ∈ univ.erase i, |x i - x k| =
      ∏ k, ((if i < k then |x i - x k| else 1) * (if k < i then |x k - x i| else 1)) := by
    intro i
    rw [← prod_erase univ (a := i) (by simp)]
    refine prod_congr rfl fun k hk => ?_
    rcases lt_or_gt_of_ne (ne_of_mem_erase hk) with h | h
    · simp [h, h.not_gt, abs_sub_comm]
    · simp [h, h.not_gt]
  simp_rw [h, prod_mul_distrib]
  rw [prod_comm (f := fun i k => if k < i then |x k - x i| else 1), sq]
  rfl

lemma AV_castSucc {m : ℕ} (l : Fin (m + 1) → ℝ) :
    AV l = AV (fun i : Fin m => l i.castSucc) * ∏ i : Fin m, |l i.castSucc - l (Fin.last m)| := by
  unfold AV
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.prod_univ_castSucc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last,
    if_true, if_false, mul_one, not_lt.mpr (Fin.le_last _), prod_const_one,
    prod_mul_distrib]

/-- The matrix `A_{ij} = ∏_{k ≠ j} (x_i - μ_k)`. -/
def Amat {n : ℕ} (x μ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∏ k ∈ univ.erase j, (x i - μ k)

lemma Amat_eq_mul {n : ℕ} (x μ : Fin n → ℝ) :
    Amat x μ = Matrix.vandermonde x *
      Matrix.of fun (k j : Fin n) => (∏ k' ∈ univ.erase j, (X - C (μ k'))).coeff k := by
  ext i j
  have hn : 0 < n := j.pos
  have hdeg : (∏ k' ∈ univ.erase j, (X - C (μ k'))).natDegree < n := by
    have : (∏ k' ∈ univ.erase j, (X - C (μ k'))).degree = ((univ.erase j).card : WithBot ℕ) :=
      Lagrange.degree_nodal
    rw [natDegree_eq_of_degree_eq_some this, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin]
    omega
  have h := eval_eq_sum_range' hdeg (x i)
  rw [eval_prod, Finset.sum_range] at h
  simp only [eval_sub, eval_X, eval_C] at h
  simp only [Amat, Matrix.of_apply, Matrix.mul_apply, Matrix.vandermonde_apply]
  rw [show (∏ k ∈ univ.erase j, (x i - μ k)) = _ from h]
  exact sum_congr rfl fun k _ => mul_comm _ _

lemma abs_det_Amat {n : ℕ} (x : Fin n → ℝ) {μ : Fin n → ℝ} (hμ : Function.Injective μ) :
    |(Amat x μ).det| = AV x * AV μ := by
  set K := Matrix.of fun (k j : Fin n) => (∏ k' ∈ univ.erase j, (X - C (μ k'))).coeff k
  have hx : |(Amat x μ).det| = AV x * |K.det| := by
    rw [Amat_eq_mul, Matrix.det_mul, abs_mul, abs_det_vandermonde]
  have hμμ : |(Amat μ μ).det| = AV μ ^ 2 := by
    have : Amat μ μ = Matrix.diagonal fun j => ∏ k ∈ univ.erase j, (μ j - μ k) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Amat]
      · simp only [Amat, Matrix.of_apply, Matrix.diagonal_apply_ne _ h]
        exact prod_eq_zero (mem_erase.mpr ⟨h, mem_univ _⟩) (sub_self _)
    rw [this, Matrix.det_diagonal, abs_prod]
    simp_rw [abs_prod]
    exact prod_prod_erase_abs μ
  have hK : |K.det| = AV μ := by
    have h2 : |(Amat μ μ).det| = AV μ * |K.det| := by
      rw [Amat_eq_mul, Matrix.det_mul, abs_mul, abs_det_vandermonde]
    have hpos := AV_pos hμ
    rw [hμμ, sq] at h2
    exact (mul_left_cancel₀ hpos.ne' h2).symm
  rw [hx, hK]

lemma prod_abs_Pd {m : ℕ} {l : Fin (m + 1) → ℝ} (hl : Function.Injective l) :
    ∏ i : Fin m, ∏ k ∈ univ.erase i.castSucc, |l i.castSucc - l k| =
      AV l * AV (fun i : Fin m => l i.castSucc) := by
  have h1 := prod_prod_erase_abs l
  rw [Fin.prod_univ_castSucc] at h1
  have h2 := AV_castSucc l
  have hlast : ∏ k ∈ univ.erase (Fin.last m), |l (Fin.last m) - l k| =
      ∏ i : Fin m, |l i.castSucc - l (Fin.last m)| := by
    rw [prod_erase_eq_prod_succAbove]
    simp [Fin.succAbove_last, abs_sub_comm]
  rw [hlast] at h1
  have hne : ∏ i : Fin m, |l i.castSucc - l (Fin.last m)| ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun i _ => abs_ne_zero.mpr (sub_ne_zero.mpr fun e => ?_)
    exact (Fin.castSucc_lt_last i).ne (hl e)
  apply mul_right_cancel₀ hne
  rw [h1, sq, mul_assoc, ← h2]



/-- `∫_0^s t^{a-1} (s-t)^{b-1} dt = s^{a+b-1} Γ(a)Γ(b)/Γ(a+b)`. -/
lemma lintegral_beta {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    ∫⁻ t in Set.Ioo 0 s, ENNReal.ofReal (t ^ (a - 1) * (s - t) ^ (b - 1)) =
      ENNReal.ofReal (s ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b))) := by
  set g : ℝ → ℝ := fun t => t ^ (a - 1) * (s - t) ^ (b - 1)
  set f : ℝ → ℂ := fun x => (x : ℂ) ^ ((a : ℂ) - 1) * ((s : ℂ) - x) ^ ((b : ℂ) - 1)
  have hfg : ∀ x ∈ Set.uIcc 0 s, f x = (g x : ℂ) := by
    intro x hx
    rw [Set.uIcc_of_le hs.le] at hx
    simp only [f, g, Complex.ofReal_mul]
    rw [Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (by linarith [hx.2])]
    push_cast; ring_nf
  have hΓ : Complex.betaIntegral a b = ((Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) : ℝ) : ℂ) := by
    have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
      (by simpa using ha) (by simpa using hb)
    rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
      Complex.Gamma_ofReal] at h
    have hne : (Real.Gamma (a + b) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by linarith)).ne'
    push_cast
    rw [eq_div_iff hne, mul_comm, h]
  have hval : ∫ x in (0:ℝ)..s, f x = ((s ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral_scaled _ _ hs, hΓ, Complex.ofReal_mul,
      Complex.ofReal_cpow hs.le]
    push_cast; ring_nf
  have hpos : 0 < s ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) := by
    have := Real.Gamma_pos_of_pos ha
    have := Real.Gamma_pos_of_pos hb
    have := Real.Gamma_pos_of_pos (add_pos ha hb)
    positivity
  have hint : IntervalIntegrable f MeasureTheory.volume 0 s := by
    by_contra h
    rw [intervalIntegral.integral_undef h] at hval
    have := congrArg Complex.re hval
    simp only [Complex.zero_re, Complex.ofReal_re] at this
    linarith
  have hintg : IntegrableOn g (Set.Ioo 0 s) := by
    have h1 := (intervalIntegrable_iff_integrableOn_Ioo_of_le hs.le).mp hint
    have h2 : IntegrableOn (fun x => (g x : ℂ)) (Set.Ioo 0 s) := by
      refine h1.congr_fun (fun x hx => hfg x ?_) measurableSet_Ioo
      rw [Set.uIcc_of_le hs.le]; exact Set.Ioo_subset_Icc_self hx
    exact h2.re
  have hg_int : ∫ x in (0:ℝ)..s, g x = s ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) := by
    apply Complex.ofReal_injective
    rw [← hval, ← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr fun x hx => (hfg x hx).symm
  rw [← hg_int, intervalIntegral.integral_of_le hs.le, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal hintg]
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  have := hx.1; have := hx.2
  exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.rpow_nonneg (by linarith) _)


/-- The Dirichlet integrand with all exponents `1/2` on the simplex `{w > 0, ∑ w < s}`. -/
def dirF (m : ℕ) (s : ℝ) (w : Fin m → ℝ) : ENNReal :=
  if (∀ i, 0 < w i) ∧ ∑ i, w i < s then
    ENNReal.ofReal ((∏ i, w i ^ (-(1:ℝ)/2)) * (s - ∑ i, w i) ^ (-(1:ℝ)/2)) else 0

/-- `Γ(1/2)^{m+1} / Γ((m+1)/2)`. -/
def dirC (m : ℕ) : ℝ := Real.pi ^ (((m:ℝ) + 1) / 2) / Real.Gamma (((m:ℝ) + 1) / 2)

lemma measurable_dirF (m : ℕ) (s : ℝ) : Measurable (dirF m s) := by
  refine Measurable.ite ?_ (Measurable.ennreal_ofReal (by fun_prop)) measurable_const
  rw [Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    (measurableSet_lt (by fun_prop) measurable_const)

lemma dirF_cons {m : ℕ} {s t : ℝ} (v : Fin m → ℝ) :
    dirF (m + 1) s (Fin.cons t v) =
      Set.indicator (Set.Ioo 0 s) (fun t => ENNReal.ofReal (t ^ (-(1:ℝ)/2)) * dirF m (s - t) v) t := by
  by_cases ht : t ∈ Set.Ioo 0 s
  · rw [Set.indicator_of_mem ht]
    have e : t + ∑ i, v i < s ↔ ∑ i, v i < s - t := by constructor <;> intro h <;> linarith
    simp only [dirF, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_cons, Fin.prod_univ_succ,
      ht.1, true_and, e]
    split_ifs
    · rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.1.le _)]
      congr 1; ring_nf
    · simp
  · rw [Set.indicator_of_notMem ht]
    simp only [dirF, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_cons]
    rw [if_neg]
    rintro ⟨⟨h0, hv⟩, hsum⟩
    have : 0 ≤ ∑ i, v i := sum_nonneg fun i _ => (hv i).le
    exact ht ⟨h0, by linarith⟩

lemma lintegral_dirF (m : ℕ) : ∀ s : ℝ, 0 < s →
    ∫⁻ w, dirF m s w = ENNReal.ofReal (s ^ (((m:ℝ) + 1) / 2 - 1) * dirC m) := by
  induction m with
  | zero =>
    intro s hs
    have : ∀ w : Fin 0 → ℝ, dirF 0 s w = ENNReal.ofReal (s ^ (-(1:ℝ)/2)) := by
      intro w; simp [dirF, hs]
    simp_rw [this, lintegral_const]
    rw [volume_pi, Measure.pi_univ]
    have h0 : dirC 0 = 1 := by
      rw [dirC]; norm_num
      rw [Real.Gamma_one_half_eq, Real.sqrt_eq_rpow, div_self (Real.rpow_pos_of_pos Real.pi_pos _).ne']
    simp [h0]
    norm_num
  | succ m ih =>
    intro s hs
    have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
    rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    rw [Measure.volume_eq_prod, lintegral_prod (f := fun p => dirF (m + 1) s ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm p))
      ((measurable_dirF _ _).comp (MeasurableEquiv.measurable _)).aemeasurable]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply]
    have key : ∀ (x : ℝ) (y : Fin m → ℝ), (Fin.insertNthEquiv (fun _ => ℝ) 0) (x, y) = Fin.cons x y := by
      intro x y; simp [Fin.insertNthEquiv, Fin.insertNth_zero']
    simp_rw [key, dirF_cons]
    have inner : ∀ x : ℝ, ∫⁻ y : Fin m → ℝ, Set.indicator (Set.Ioo 0 s)
        (fun t => ENNReal.ofReal (t ^ (-(1:ℝ)/2)) * dirF m (s - t) y) x =
        Set.indicator (Set.Ioo 0 s) (fun t => ENNReal.ofReal (dirC m) *
          ENNReal.ofReal (t ^ ((1:ℝ)/2 - 1) * (s - t) ^ (((m:ℝ) + 1) / 2 - 1))) x := by
      intro x
      by_cases hx : x ∈ Set.Ioo 0 s
      · simp only [Set.indicator_of_mem hx]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ih _ (by linarith [hx.2]),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hx.1.le _),
          ← ENNReal.ofReal_mul (by rw [dirC]; have := Real.Gamma_pos_of_pos (show (0:ℝ) < ((m:ℝ)+1)/2 by positivity); positivity)]
        congr 1; norm_num; ring
      · simp [Set.indicator_of_notMem hx]
    simp_rw [inner]
    rw [lintegral_indicator measurableSet_Ioo, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_beta (by norm_num) (by positivity) hs,
      ← ENNReal.ofReal_mul (by rw [dirC]; have := Real.Gamma_pos_of_pos (show (0:ℝ) < ((m:ℝ)+1)/2 by positivity); positivity)]
    congr 1
    have e1 : (1:ℝ)/2 + ((m:ℝ)+1)/2 - 1 = ((↑(m+1):ℝ)+1)/2 - 1 := by push_cast; ring
    have e2 : (1:ℝ)/2 + ((m:ℝ)+1)/2 = ((↑(m+1):ℝ)+1)/2 := by push_cast; ring
    have hπ : Real.pi ^ (((m:ℝ)+1)/2) * Real.pi ^ ((1:ℝ)/2) = Real.pi ^ (((↑(m+1):ℝ)+1)/2) := by
      rw [← Real.rpow_add Real.pi_pos]; push_cast; ring_nf
    have hΓ := (Real.Gamma_pos_of_pos (show (0:ℝ) < ((m:ℝ)+1)/2 by positivity)).ne'
    rw [e1, e2, dirC, dirC, Real.Gamma_one_half_eq, Real.sqrt_eq_rpow, ← hπ]
    field_simp


lemma abs_det_Mjac {m : ℕ} {l : Fin (m + 1) → ℝ} (hl : StrictAnti l) {μ : Fin m → ℝ}
    (hμ : Function.Injective μ) : |(Mjac l μ).det| = AV μ / AV l := by
  have hM : Mjac l μ = Matrix.of fun i j =>
      (-(Pd l i.castSucc)⁻¹) * Amat (fun i : Fin m => l i.castSucc) μ i j := by
    ext i j; simp [Mjac, Amat, div_eq_mul_inv]; ring
  rw [hM, Matrix.det_mul_column, abs_mul, abs_det_Amat _ hμ, abs_prod]
  simp only [abs_neg, abs_inv, Pd, abs_prod]
  rw [prod_inv_distrib, prod_abs_Pd hl.injective]
  have h1 := AV_pos hl.injective
  have h2 : 0 < AV (fun i : Fin m => l i.castSucc) :=
    AV_pos (hl.injective.comp (Fin.castSucc_injective m))
  field_simp

lemma rpow_wt {m : ℕ} {l : Fin (m + 1) → ℝ} (hl : StrictAnti l) {μ : Fin m → ℝ} (hμ : μ ∈ U l)
    (i : Fin (m + 1)) : wt l μ i ^ (-(1:ℝ)/2) =
      (∏ j, |l i - μ j| ^ (-(1:ℝ)/2)) * (∏ k ∈ univ.erase i, |l i - l k|) ^ ((1:ℝ)/2) := by
  have hw : wt l μ i = (∏ j, |l i - μ j|) / ∏ k ∈ univ.erase i, |l i - l k| := by
    rw [← abs_of_pos (wt_pos hl hμ i), wt, abs_div, abs_prod, Pd, abs_prod]
  have hb : 0 ≤ ∏ k ∈ univ.erase i, |l i - l k| := prod_nonneg fun _ _ => abs_nonneg _
  rw [hw, Real.div_rpow (prod_nonneg fun _ _ => abs_nonneg _) hb,
    Real.finsetProd_rpow _ _ (fun _ _ => abs_nonneg _), neg_div, Real.rpow_neg hb, div_inv_eq_mul]

lemma prod_sqrt {m : ℕ} (l : Fin (m + 1) → ℝ) :
    ∏ i, (∏ k ∈ univ.erase i, |l i - l k|) ^ ((1:ℝ)/2) = AV l := by
  rw [Real.finsetProd_rpow _ _ (fun _ _ => prod_nonneg fun _ _ => abs_nonneg _),
    prod_prod_erase_abs, ← Real.sqrt_eq_rpow, Real.sqrt_sq]
  exact prod_nonneg fun _ _ => prod_nonneg fun _ _ => by split_ifs <;> positivity

lemma key_real {m : ℕ} {l : Fin (m + 1) → ℝ} (hl : StrictAnti l) {μ : Fin m → ℝ} (hμ : μ ∈ U l) :
    |(Mjac l μ).det| * ((∏ i, F l μ i ^ (-(1:ℝ)/2)) * (1 - ∑ i, F l μ i) ^ (-(1:ℝ)/2)) =
      MuirheadMST.vandermondeProd μ * ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1:ℝ)/2) := by
  rw [← wt_last hl.injective]
  have e : (∏ i, F l μ i ^ (-(1:ℝ)/2)) * wt l μ (Fin.last m) ^ (-(1:ℝ)/2) =
      ∏ i : Fin (m + 1), wt l μ i ^ (-(1:ℝ)/2) := by
    rw [Fin.prod_univ_castSucc]; rfl
  rw [e]
  simp_rw [rpow_wt hl hμ, prod_mul_distrib]
  rw [prod_sqrt, abs_det_Mjac hl (strictAnti_of_mem_U hl hμ).injective,
    vandermondeProd_eq_AV (strictAnti_of_mem_U hl hμ), prod_comm (s := (univ : Finset (Fin (m + 1))))]
  simp_rw [abs_sub_comm (l _) (μ _)]
  have := AV_pos hl.injective
  field_simp

lemma measurableSet_U {m : ℕ} (l : Fin (m + 1) → ℝ) : MeasurableSet (U l) := by
  simp only [U, Set.ofPred_forall, Set.ofPred_and]
  exact MeasurableSet.iInter fun i => (measurableSet_lt (measurable_pi_apply i) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_pi_apply i))

lemma measurableSet_Δ (m : ℕ) : MeasurableSet (Δ m) := by
  simp only [Δ, Set.ofPred_forall, Set.ofPred_and]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    (measurableSet_lt (by fun_prop) measurable_const)

end DixonHalf

open DixonHalf in
theorem solution (m : ℕ) (l : Fin (m + 1) → ℝ) (hl : StrictAnti l) :
    ∫⁻ μ : Fin m → ℝ,
        (if ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i then
          ENNReal.ofReal (MuirheadMST.vandermondeProd μ *
            ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2))
        else 0) =
      ENNReal.ofReal (Real.pi ^ (((m : ℝ) + 1) / 2) / Real.Gamma (((m : ℝ) + 1) / 2)) := by
  set g : (Fin m → ℝ) → ENNReal := fun w =>
    ENNReal.ofReal ((∏ i, w i ^ (-(1:ℝ)/2)) * (1 - ∑ i, w i) ^ (-(1:ℝ)/2)) with hg
  have h1 : (∫⁻ μ : Fin m → ℝ,
        (if ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i then
          ENNReal.ofReal (MuirheadMST.vandermondeProd μ *
            ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2))
        else 0)) = ∫⁻ μ in U l, ENNReal.ofReal |(Fd l μ).det| * g (F l μ) := by
    rw [← lintegral_indicator (measurableSet_U l)]
    refine lintegral_congr fun μ => ?_
    by_cases hμ : μ ∈ U l
    · have hμ' : ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i := hμ
      rw [Set.indicator_of_mem hμ, if_pos hμ', det_Fd, hg, ← ENNReal.ofReal_mul (abs_nonneg _),
        key_real hl hμ]
    · have hμ' : ¬ ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i := hμ
      rw [Set.indicator_of_notMem hμ, if_neg hμ']
  rw [h1, ← lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_U l)
    (fun μ _ => (hasFDerivAt_F l μ).hasFDerivWithinAt) (injOn_F hl), image_F hl]
  have h2 : ∫⁻ w in Δ m, g w = ∫⁻ w, dirF m 1 w := by
    rw [← lintegral_indicator (measurableSet_Δ m)]
    refine lintegral_congr fun w => ?_
    by_cases hw : w ∈ Δ m
    · have hw' : (∀ i, 0 < w i) ∧ ∑ i, w i < 1 := hw
      rw [Set.indicator_of_mem hw, dirF, if_pos hw']
    · have hw' : ¬ ((∀ i, 0 < w i) ∧ ∑ i, w i < 1) := hw
      rw [Set.indicator_of_notMem hw, dirF, if_neg hw']
  rw [h2, lintegral_dirF m 1 one_pos, Real.one_rpow, one_mul, dirC]
