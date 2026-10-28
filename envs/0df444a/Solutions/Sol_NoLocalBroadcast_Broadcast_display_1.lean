-- Prove2me | solution 1 for NoLocalBroadcast.Broadcast.display_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:25:18.180061+00:00
-- url     : https://prove2.me/submissions/2acd7c9c-ed92-4ab9-925e-20f1f1ca419b

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

open Matrix
open scoped Kronecker ComplexOrder

namespace P2MAux

lemma sum_eig_eq {n : Type} [Fintype n] [DecidableEq n] (A U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (hA : A = U * diagonal (fun i => (d i : ℂ)) * Uᴴ) (hH : A.IsHermitian) (g : ℝ → ℝ) :
    ∑ i, g (hH.eigenvalues i) = ∑ i, g (d i) := by
  have hc : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((d i : ℝ) : ℂ)) := by
    rw [hA, charpoly_mul_comm, ← mul_assoc]
    have : Uᴴ * U = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').1 hU
      simpa [Matrix.star_eq_conjTranspose] using this
    rw [this, one_mul, charpoly_diagonal]
  have hr : A.charpoly.roots = Multiset.map (fun i => ((d i : ℝ) : ℂ)) Finset.univ.val := by
    rw [hc, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h2 := hH.roots_charpoly_eq_eigenvalues
  rw [hr] at h2
  have h3 := congrArg (fun s : Multiset ℂ => (s.map (fun z => g z.re)).sum) h2
  simp only [Multiset.map_map] at h3
  have e1 : ∀ (h : n → ℝ), ∑ i, g (h i) = (Multiset.map (fun i => g (h i)) Finset.univ.val).sum := fun h => rfl
  rw [e1, e1]
  simpa [Function.comp_def] using h3.symm

lemma trace_cfc_eq {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hH : A.IsHermitian)
    (f : ℝ → ℝ) : (cfc f A).trace = ∑ i, ((f (hH.eigenvalues i) : ℝ) : ℂ) := by
  rw [hH.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle]
  have : (star (hH.eigenvectorUnitary : Matrix n n ℂ)) * (hH.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_star_mul_self _
  rw [this, one_mul, trace_diagonal]
  rfl

lemma vn_mul_log {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hH : A.IsHermitian) :
    QAlgorithms.vnEntropy A * Real.log 2 = ∑ i, Real.negMulLog (hH.eigenvalues i) := by
  unfold QAlgorithms.vnEntropy
  rw [trace_cfc_eq A hH]
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : Real.log 2 ≠ 0 := by positivity
  simp only [Real.negMulLog, Real.logb]
  field_simp

lemma vn_decomp {n : Type} [Fintype n] [DecidableEq n] (A U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (hA : A = U * diagonal (fun i => (d i : ℂ)) * Uᴴ) :
    QAlgorithms.vnEntropy A * Real.log 2 = ∑ i, Real.negMulLog (d i) := by
  have hH : A.IsHermitian := by
    rw [hA]
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
      ← mul_assoc]
    congr 3
    ext i
    simp
  rw [vn_mul_log A hH, sum_eig_eq A U hU d hA hH]


lemma unitary_row {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ)
    (hW : W ∈ Matrix.unitaryGroup n ℂ) (k : n) : ∑ l, Complex.normSq (W k l) = 1 := by
  have h := congrFun (congrFun ((Matrix.mem_unitaryGroup_iff).1 hW) k) k
  simp only [mul_apply, star_apply, one_apply_eq] at h
  have : ∑ l, ((Complex.normSq (W k l) : ℝ) : ℂ) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  exact_mod_cast this

lemma unitary_col {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ)
    (hW : W ∈ Matrix.unitaryGroup n ℂ) (l : n) : ∑ k, Complex.normSq (W k l) = 1 := by
  have h := congrFun (congrFun ((Matrix.mem_unitaryGroup_iff').1 hW) l) l
  simp only [mul_apply, star_apply, one_apply_eq] at h
  have : ∑ k, ((Complex.normSq (W k l) : ℝ) : ℂ) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm, Complex.star_def, Complex.mul_conj]
  exact_mod_cast this

lemma diag_conj_re {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ) (d : n → ℝ) (k : n) :
    ((W * diagonal (fun i => (d i : ℂ)) * Wᴴ) k k).re = ∑ l, Complex.normSq (W k l) * d l := by
  simp only [mul_apply, diagonal_apply, conjTranspose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.re_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm (W k l), mul_assoc, Complex.star_def, Complex.mul_conj]
  simp [mul_comm]

lemma peierls_aux {n : Type} [Fintype n] [DecidableEq n] (B U V : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) (lam : n → ℝ)
    (hl : ∀ l, 0 ≤ lam l) (hBd : B = U * diagonal (fun i => ((lam i : ℝ) : ℂ)) * Uᴴ) :
    ∑ l, Real.negMulLog (lam l) ≤ ∑ k, Real.negMulLog ((Vᴴ * B * V) k k).re := by
  set W := Vᴴ * U
  have hW : W ∈ Matrix.unitaryGroup n ℂ := by
    refine Submonoid.mul_mem _ ?_ hU
    have : Vᴴ = star V := rfl
    rw [this]; exact Unitary.star_mem hV
  have hc : ∀ k, ((Vᴴ * B * V) k k).re = ∑ l, Complex.normSq (W k l) * lam l := by
    intro k
    rw [← diag_conj_re]
    congr 2
    rw [hBd]
    simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp_rw [hc]
  have hj : ∀ k, ∑ l, Complex.normSq (W k l) * Real.negMulLog (lam l)
      ≤ Real.negMulLog (∑ l, Complex.normSq (W k l) * lam l) := by
    intro k
    have := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun l => Complex.normSq (W k l)) (p := fun l => lam l)
      (fun l _ => Complex.normSq_nonneg _) (unitary_row W hW k)
      (fun l _ => Set.mem_Ici.2 (hl l))
    simpa [smul_eq_mul] using this
  calc ∑ l, Real.negMulLog (lam l)
      = ∑ k, ∑ l, Complex.normSq (W k l) * Real.negMulLog (lam l) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_mul, unitary_col W hW l, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun k _ => hj k

lemma peierls {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) (hB : B.PosSemidef)
    (V : Matrix n n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    ∑ l, Real.negMulLog (hB.1.eigenvalues l) ≤ ∑ k, Real.negMulLog ((Vᴴ * B * V) k k).re :=
  peierls_aux B _ V (hB.1.eigenvectorUnitary).2 hV _ (hB.eigenvalues_nonneg)
    hB.1.spectral_theorem

lemma vn_concave {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] (w : ι → ℝ)
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (A : ι → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) :
    ∑ j, w j * QAlgorithms.vnEntropy (A j) ≤
      QAlgorithms.vnEntropy (∑ j, ((w j : ℝ) : ℂ) • A j) := by
  set M := ∑ j, ((w j : ℝ) : ℂ) • A j
  have hM : M.PosSemidef := by
    apply Matrix.posSemidef_sum
    intro j _
    exact (hA j).smul (Complex.zero_le_real.2 (hw0 j))
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← mul_le_mul_iff_of_pos_right hl, vn_mul_log M hM.1, Finset.sum_mul]
  simp_rw [mul_assoc, vn_mul_log _ (hA _).1]
  set V : Matrix n n ℂ := (hM.1.eigenvectorUnitary : Matrix n n ℂ)
  have hV : V ∈ Matrix.unitaryGroup n ℂ := (hM.1.eigenvectorUnitary).2
  have hD : Vᴴ * M * V = diagonal (fun i => ((hM.1.eigenvalues i : ℝ) : ℂ)) := by
    have := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this
  have hx : ∀ k, hM.1.eigenvalues k = ∑ j, w j * ((Vᴴ * A j * V) k k).re := by
    intro k
    have h1 := congrFun (congrFun hD k) k
    rw [diagonal_apply_eq] at h1
    have h2 : (Vᴴ * M * V) k k = ∑ j, ((w j : ℝ) : ℂ) * (Vᴴ * A j * V) k k := by
      simp only [M, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [h2] at h1
    have h3 := congrArg Complex.re h1
    rw [Complex.re_sum] at h3
    simp only [Complex.ofReal_re] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  have hpos : ∀ j k, 0 ≤ ((Vᴴ * A j * V) k k).re := by
    intro j k
    have := ((hA j).conjTranspose_mul_mul_same V).diag_nonneg (i := k)
    have h' : Vᴴ * A j * V = Vᴴ * A j * V := rfl
    exact (Complex.nonneg_iff.1 this).1
  calc ∑ j, w j * ∑ l, Real.negMulLog ((hA j).1.eigenvalues l)
      ≤ ∑ j, w j * ∑ k, Real.negMulLog ((Vᴴ * A j * V) k k).re := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (peierls (A j) (hA j) V hV) (hw0 j)
    _ = ∑ k, ∑ j, w j * Real.negMulLog ((Vᴴ * A j * V) k k).re := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ k, Real.negMulLog (hM.1.eigenvalues k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [hx k]
        have := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
          (w := w) (p := fun j => ((Vᴴ * A j * V) k k).re)
          (fun j _ => hw0 j) hw1 (fun j _ => Set.mem_Ici.2 (hpos j k))
        simpa [smul_eq_mul] using this


lemma vn_submatrix {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m m ℂ) (hX : X.IsHermitian) (e : n ≃ m) :
    QAlgorithms.vnEntropy (X.submatrix e e) * Real.log 2 =
      QAlgorithms.vnEntropy X * Real.log 2 := by
  set U : Matrix m m ℂ := (hX.eigenvectorUnitary : Matrix m m ℂ)
  have hU : U ∈ Matrix.unitaryGroup m ℂ := (hX.eigenvectorUnitary).2
  have hXd : X = U * diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * Uᴴ :=
    hX.spectral_theorem
  rw [vn_mul_log X hX]
  have hU' : U.submatrix e e ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have h1 : star (U.submatrix e e) = (star U).submatrix e e := by
      simp [Matrix.star_eq_conjTranspose, conjTranspose_submatrix]
    rw [h1, submatrix_mul_equiv, (Matrix.mem_unitaryGroup_iff).1 hU, submatrix_one_equiv]
  rw [vn_decomp (X.submatrix e e) (U.submatrix e e) hU' (fun i => hX.eigenvalues (e i))]
  · exact Equiv.sum_comp e (fun i => Real.negMulLog (hX.eigenvalues i))
  · conv_lhs => rw [hXd]
    rw [← submatrix_mul_equiv (e₂ := e), ← submatrix_mul_equiv (e₂ := e), submatrix_diagonal_equiv,
      conjTranspose_submatrix]
    rfl

lemma vn_blockDiagonal {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (C : ι → Matrix α α ℂ) (hC : ∀ i, (C i).IsHermitian) :
    QAlgorithms.vnEntropy (blockDiagonal C) * Real.log 2 =
      ∑ i, QAlgorithms.vnEntropy (C i) * Real.log 2 := by
  set U : ι → Matrix α α ℂ := fun i => ((hC i).eigenvectorUnitary : Matrix α α ℂ)
  have hU : ∀ i, U i ∈ Matrix.unitaryGroup α ℂ := fun i => ((hC i).eigenvectorUnitary).2
  have hUb : blockDiagonal U ∈ Matrix.unitaryGroup (α × ι) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    rw [Matrix.star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    have : (fun k => U k * (U k)ᴴ) = 1 := by
      funext k
      exact (Matrix.mem_unitaryGroup_iff).1 (hU k)
    rw [this, blockDiagonal_one]
  rw [vn_decomp (blockDiagonal C) (blockDiagonal U) hUb
    (fun ik => (hC ik.2).eigenvalues ik.1)]
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vn_mul_log (C i) (hC i)]
  · have : C = fun i => U i * diagonal (fun x => (((hC i).eigenvalues x : ℝ) : ℂ)) * (U i)ᴴ := by
      funext i
      exact (hC i).spectral_theorem
    conv_lhs => rw [this]
    rw [blockDiagonal_mul, blockDiagonal_mul, ← blockDiagonal_conjTranspose,
      blockDiagonal_diagonal]

lemma vn_smul {α : Type} [Fintype α] [DecidableEq α] (c : ℝ) (B : Matrix α α ℂ)
    (hB : B.IsHermitian) :
    QAlgorithms.vnEntropy (((c : ℝ) : ℂ) • B) * Real.log 2 =
      Real.negMulLog c * (B.trace).re + c * (QAlgorithms.vnEntropy B * Real.log 2) := by
  set U : Matrix α α ℂ := (hB.eigenvectorUnitary : Matrix α α ℂ)
  have hU : U ∈ Matrix.unitaryGroup α ℂ := (hB.eigenvectorUnitary).2
  have hBd : B = U * diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) * Uᴴ := hB.spectral_theorem
  rw [vn_decomp _ U hU (fun x => c * hB.eigenvalues x), vn_mul_log B hB]
  · rw [hB.trace_eq_sum_eigenvalues, Complex.re_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Real.negMulLog_mul]
    have : (((hB.eigenvalues x : ℝ) : ℂ)).re = hB.eigenvalues x := Complex.ofReal_re _
    erw [this]
    ring
  · conv_lhs => rw [hBd]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    simp [diagonal_apply]

lemma vn_diagonal {α : Type} [Fintype α] [DecidableEq α] (d : α → ℝ) :
    QAlgorithms.vnEntropy (diagonal fun i => ((d i : ℝ) : ℂ)) * Real.log 2 =
      ∑ i, Real.negMulLog (d i) :=
  vn_decomp _ 1 (Submonoid.one_mem _) d (by simp)

lemma traceRight_eq_sum {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix (α × β) (α × β) ℂ) :
    QAlgorithms.traceRight M = ∑ h : β,
      (Matrix.of fun (r : α × β) (a : α) => if r = (a, h) then (1 : ℂ) else 0)ᴴ * M *
      (Matrix.of fun (r : α × β) (a : α) => if r = (a, h) then (1 : ℂ) else 0) := by
  ext j k
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.sum_apply, mul_apply,
    conjTranspose_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp [apply_ite, ite_mul]

lemma traceLeft_eq_sum {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix (α × β) (α × β) ℂ) :
    QAlgorithms.traceLeft M = ∑ h : α,
      (Matrix.of fun (r : α × β) (b : β) => if r = (h, b) then (1 : ℂ) else 0)ᴴ * M *
      (Matrix.of fun (r : α × β) (b : β) => if r = (h, b) then (1 : ℂ) else 0) := by
  ext j k
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.sum_apply, mul_apply,
    conjTranspose_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp [apply_ite, ite_mul]

lemma traceRight_psd {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix (α × β) (α × β) ℂ) (hM : M.PosSemidef) :
    (QAlgorithms.traceRight M).PosSemidef := by
  rw [traceRight_eq_sum]
  exact Matrix.posSemidef_sum _ fun h _ => hM.conjTranspose_mul_mul_same _

lemma traceLeft_psd {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix (α × β) (α × β) ℂ) (hM : M.PosSemidef) :
    (QAlgorithms.traceLeft M).PosSemidef := by
  rw [traceLeft_eq_sum]
  exact Matrix.posSemidef_sum _ fun h _ => hM.conjTranspose_mul_mul_same _

lemma trace_traceRight {α β : Type} [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) : (QAlgorithms.traceRight M).trace = M.trace := by
  simp [QAlgorithms.traceRight, Matrix.trace, Fintype.sum_prod_type]

lemma trace_traceLeft {α β : Type} [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) : (QAlgorithms.traceLeft M).trace = M.trace := by
  simp [QAlgorithms.traceLeft, Matrix.trace, Fintype.sum_prod_type]
  exact Finset.sum_comm


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

lemma blockDiag_herm {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (C : ι → Matrix α α ℂ) (hC : ∀ i, (C i).IsHermitian) : (blockDiagonal C).IsHermitian := by
  unfold IsHermitian
  rw [blockDiagonal_conjTranspose]
  congr 1
  funext i
  exact hC i

section flag
open NoLocalBroadcast.Broadcast

variable {ι κ a' b' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']

lemma flag_traceRight (p : ι × κ → ℝ) (ρij : ι × κ → Matrix (a' × b') (a' × b') ℂ) :
    QAlgorithms.traceRight (flaggedState p ρij) =
      (blockDiagonal (fun i => ∑ j, ((p (i, j) : ℝ) : ℂ) • QAlgorithms.traceRight (ρij (i, j)))).submatrix
        (Equiv.prodComm ι a') (Equiv.prodComm ι a') := by
  ext ⟨i, x⟩ ⟨i', x'⟩
  simp only [QAlgorithms.traceRight, flaggedState, Matrix.of_apply, submatrix_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk, blockDiagonal_apply', Fintype.sum_prod_type]
  by_cases h : i = i'
  · subst h
    simp [Matrix.sum_apply, Finset.mul_sum]
  · simp [h, Ne.symm h]

lemma flag_traceLeft (p : ι × κ → ℝ) (ρij : ι × κ → Matrix (a' × b') (a' × b') ℂ) :
    QAlgorithms.traceLeft (flaggedState p ρij) =
      (blockDiagonal (fun j => ∑ i, ((p (i, j) : ℝ) : ℂ) • QAlgorithms.traceLeft (ρij (i, j)))).submatrix
        (Equiv.prodComm κ b') (Equiv.prodComm κ b') := by
  ext ⟨j, y⟩ ⟨j', y'⟩
  simp only [QAlgorithms.traceLeft, flaggedState, Matrix.of_apply, submatrix_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk, blockDiagonal_apply', Fintype.sum_prod_type]
  by_cases h : j = j'
  · subst h
    simp [Matrix.sum_apply, Finset.mul_sum]
  · simp [h, Ne.symm h]

lemma flag_eq (p : ι × κ → ℝ) (ρij : ι × κ → Matrix (a' × b') (a' × b') ℂ) :
    flaggedState p ρij =
      (blockDiagonal (fun ij => ((p ij : ℝ) : ℂ) • ρij ij)).submatrix
        ((Equiv.prodProdProdComm ι a' κ b').trans (Equiv.prodComm _ _))
        ((Equiv.prodProdProdComm ι a' κ b').trans (Equiv.prodComm _ _)) := by
  ext ⟨⟨i, x⟩, ⟨j, y⟩⟩ ⟨⟨i', x'⟩, ⟨j', y'⟩⟩
  simp only [flaggedState, Matrix.of_apply, submatrix_apply, Equiv.trans_apply,
    Equiv.prodProdProdComm_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, blockDiagonal_apply',
    Prod.mk.injEq, Matrix.smul_apply, smul_eq_mul]

lemma diag_traceRight (p : ι × κ → ℝ) :
    QAlgorithms.traceRight (Matrix.diagonal fun ij => ((p ij : ℝ) : ℂ)) =
      Matrix.diagonal fun i => (((∑ j, p (i, j) : ℝ)) : ℂ) := by
  ext i i'
  by_cases h : i = i'
  · subst h; simp [QAlgorithms.traceRight, diagonal_apply]
  · simp [QAlgorithms.traceRight, diagonal_apply, h]

lemma diag_traceLeft (p : ι × κ → ℝ) :
    QAlgorithms.traceLeft (Matrix.diagonal fun ij => ((p ij : ℝ) : ℂ)) =
      Matrix.diagonal fun j => (((∑ i, p (i, j) : ℝ)) : ℂ) := by
  ext j j'
  by_cases h : j = j'
  · subst h; simp [QAlgorithms.traceLeft, diagonal_apply]
  · simp [QAlgorithms.traceLeft, diagonal_apply, h]

end flag

end P2MAux

open NoLocalBroadcast.Broadcast P2MAux in
theorem solution {ι κ a' b' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype a'] [DecidableEq a'] [Nonempty a'] [Fintype b'] [DecidableEq b'] [Nonempty b']
    (p : ι × κ → ℝ) (hp0 : ∀ ij, 0 ≤ p ij) (hp1 : ∑ ij, p ij = 1)
    (ρij : ι × κ → Matrix (a' × b') (a' × b') ℂ)
    (hρij : ∀ ij, QAlgorithms.IsDensityMatrix (ρij ij)) :
    mutualInfo (flaggedState p ρij) =
        mutualInfo (Matrix.diagonal fun ij => (p ij : ℂ))
          + ∑ i, (∑ j, p (i, j)) * QAlgorithms.vnEntropy
              (∑ j, ((p (i, j) / ∑ j', p (i, j') : ℝ) : ℂ) • QAlgorithms.traceRight (ρij (i, j)))
          + ∑ j, (∑ i, p (i, j)) * QAlgorithms.vnEntropy
              (∑ i, ((p (i, j) / ∑ i', p (i', j) : ℝ) : ℂ) • QAlgorithms.traceLeft (ρij (i, j)))
          - ∑ ij, p ij * QAlgorithms.vnEntropy (ρij ij) ∧
    mutualInfo (Matrix.diagonal fun ij => (p ij : ℂ)) + ∑ ij, p ij * mutualInfo (ρij ij)
      ≤ mutualInfo (flaggedState p ρij) := by
  classical
  set L := Real.log 2 with hLdef
  have hL : 0 < L := Real.log_pos (by norm_num)
  set Pa : ι → ℝ := fun i => ∑ j, p (i, j) with hPa
  set Pb : κ → ℝ := fun j => ∑ i, p (i, j) with hPb
  set τ : ι → Matrix a' a' ℂ := fun i =>
    ∑ j, ((p (i, j) / ∑ j', p (i, j') : ℝ) : ℂ) • QAlgorithms.traceRight (ρij (i, j)) with hτ
  set τ' : κ → Matrix b' b' ℂ := fun j =>
    ∑ i, ((p (i, j) / ∑ i', p (i', j) : ℝ) : ℂ) • QAlgorithms.traceLeft (ρij (i, j)) with hτ'
  -- basic facts
  have hPa0 : ∀ i, 0 ≤ Pa i := fun i => Finset.sum_nonneg fun j _ => hp0 _
  have hPb0 : ∀ j, 0 ≤ Pb j := fun j => Finset.sum_nonneg fun i _ => hp0 _
  have hPaz : ∀ i, Pa i = 0 → ∀ j, p (i, j) = 0 := fun i h j =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp0 (i, j))).1 h j (Finset.mem_univ _)
  have hPbz : ∀ j, Pb j = 0 → ∀ i, p (i, j) = 0 := fun j h i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp0 (i, j))).1 h i (Finset.mem_univ _)
  have hρA : ∀ ij, (QAlgorithms.traceRight (ρij ij)).PosSemidef :=
    fun ij => traceRight_psd _ (hρij ij).1
  have hρB : ∀ ij, (QAlgorithms.traceLeft (ρij ij)).PosSemidef :=
    fun ij => traceLeft_psd _ (hρij ij).1
  have hτpsd : ∀ i, (τ i).PosSemidef := fun i =>
    Matrix.posSemidef_sum _ fun j _ => (hρA _).smul
      (Complex.zero_le_real.2 (div_nonneg (hp0 _) (hPa0 i)))
  have hτ'psd : ∀ j, (τ' j).PosSemidef := fun j =>
    Matrix.posSemidef_sum _ fun i _ => (hρB _).smul
      (Complex.zero_le_real.2 (div_nonneg (hp0 _) (hPb0 j)))
  have hτsmul : ∀ i, ((Pa i : ℝ) : ℂ) • τ i =
      ∑ j, ((p (i, j) : ℝ) : ℂ) • QAlgorithms.traceRight (ρij (i, j)) := by
    intro i
    simp only [τ, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    by_cases h : Pa i = 0
    · rw [hPaz i h j]; simp
    · rw [← Complex.ofReal_mul]; congr 1; simp only [Pa] at h ⊢; field_simp
  have hτ'smul : ∀ j, ((Pb j : ℝ) : ℂ) • τ' j =
      ∑ i, ((p (i, j) : ℝ) : ℂ) • QAlgorithms.traceLeft (ρij (i, j)) := by
    intro j
    simp only [τ', Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    by_cases h : Pb j = 0
    · rw [hPbz j h i]; simp
    · rw [← Complex.ofReal_mul]; congr 1; simp only [Pb] at h ⊢; field_simp
  have htrτ : ∀ i, Real.negMulLog (Pa i) * (τ i).trace.re = Real.negMulLog (Pa i) := by
    intro i
    by_cases h : Pa i = 0
    · rw [h]; simp
    · have : (τ i).trace = 1 := by
        simp only [τ, Matrix.trace_sum, Matrix.trace_smul, trace_traceRight, (hρij _).2,
          smul_eq_mul, mul_one]
        rw [← Complex.ofReal_one, ← Complex.ofReal_sum, ← Finset.sum_div]
        simp only [Pa] at h
        rw [div_self h]
      rw [this]; simp
  have htrτ' : ∀ j, Real.negMulLog (Pb j) * (τ' j).trace.re = Real.negMulLog (Pb j) := by
    intro j
    by_cases h : Pb j = 0
    · rw [h]; simp
    · have : (τ' j).trace = 1 := by
        simp only [τ', Matrix.trace_sum, Matrix.trace_smul, trace_traceLeft, (hρij _).2,
          smul_eq_mul, mul_one]
        rw [← Complex.ofReal_one, ← Complex.ofReal_sum, ← Finset.sum_div]
        simp only [Pb] at h
        rw [div_self h]
      rw [this]; simp
  -- entropies
  have hSA : QAlgorithms.vnEntropy (QAlgorithms.traceRight (flaggedState p ρij)) * L =
      ∑ i, Real.negMulLog (Pa i) + ∑ i, Pa i * (QAlgorithms.vnEntropy (τ i) * L) := by
    rw [flag_traceRight, vn_submatrix _ ?_]
    · simp_rw [← hτsmul]
      rw [vn_blockDiagonal _ (fun i => ?_), ← Finset.sum_add_distrib]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [vn_smul _ _ (hτpsd i).1, htrτ]
      · exact ((hτpsd i).smul (Complex.zero_le_real.2 (hPa0 i))).1
    · exact blockDiag_herm _ (fun i => by
        rw [← hτsmul]; exact ((hτpsd i).smul (Complex.zero_le_real.2 (hPa0 i))).1)
  have hSB : QAlgorithms.vnEntropy (QAlgorithms.traceLeft (flaggedState p ρij)) * L =
      ∑ j, Real.negMulLog (Pb j) + ∑ j, Pb j * (QAlgorithms.vnEntropy (τ' j) * L) := by
    rw [flag_traceLeft, vn_submatrix _ ?_]
    · simp_rw [← hτ'smul]
      rw [vn_blockDiagonal _ (fun j => ?_), ← Finset.sum_add_distrib]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [vn_smul _ _ (hτ'psd j).1, htrτ']
      · exact ((hτ'psd j).smul (Complex.zero_le_real.2 (hPb0 j))).1
    · exact blockDiag_herm _ (fun j => by
        rw [← hτ'smul]; exact ((hτ'psd j).smul (Complex.zero_le_real.2 (hPb0 j))).1)
  have hS : QAlgorithms.vnEntropy (flaggedState p ρij) * L =
      ∑ ij, Real.negMulLog (p ij) + ∑ ij, p ij * (QAlgorithms.vnEntropy (ρij ij) * L) := by
    rw [flag_eq, vn_submatrix _ ?_]
    · rw [vn_blockDiagonal _ (fun ij => ?_), ← Finset.sum_add_distrib]
      · refine Finset.sum_congr rfl fun ij _ => ?_
        rw [vn_smul _ _ (hρij ij).1.1, (hρij ij).2]
        simp only [Complex.one_re, mul_one]
        rfl
      · exact ((hρij ij).1.smul (Complex.zero_le_real.2 (hp0 ij))).1
    · exact blockDiag_herm _ (fun ij =>
        ((hρij ij).1.smul (Complex.zero_le_real.2 (hp0 ij))).1)
  have hDA : QAlgorithms.vnEntropy (QAlgorithms.traceRight
      (Matrix.diagonal fun ij => ((p ij : ℝ) : ℂ))) * L = ∑ i, Real.negMulLog (Pa i) := by
    rw [diag_traceRight, vn_diagonal]
  have hDB : QAlgorithms.vnEntropy (QAlgorithms.traceLeft
      (Matrix.diagonal fun ij => ((p ij : ℝ) : ℂ))) * L = ∑ j, Real.negMulLog (Pb j) := by
    rw [diag_traceLeft, vn_diagonal]
  have hD : QAlgorithms.vnEntropy (Matrix.diagonal fun ij => ((p ij : ℝ) : ℂ)) * L =
      ∑ ij, Real.negMulLog (p ij) := vn_diagonal _
  have key : mutualInfo (flaggedState p ρij) =
        mutualInfo (Matrix.diagonal fun ij => (p ij : ℂ))
          + ∑ i, Pa i * QAlgorithms.vnEntropy (τ i)
          + ∑ j, Pb j * QAlgorithms.vnEntropy (τ' j)
          - ∑ ij, p ij * QAlgorithms.vnEntropy (ρij ij) := by
    apply mul_right_cancel₀ hL.ne'
    simp only [mutualInfo, sub_mul, add_mul, Finset.sum_mul, mul_assoc]
    rw [hSA, hSB, hS, hDA, hDB, hD]
    ring
  refine ⟨key, ?_⟩
  -- concavity
  have hcA : ∀ i, ∑ j, p (i, j) * QAlgorithms.vnEntropy (QAlgorithms.traceRight (ρij (i, j)))
      ≤ Pa i * QAlgorithms.vnEntropy (τ i) := by
    intro i
    by_cases h : Pa i = 0
    · simp [hPaz i h, h]
    · have hpos : 0 < Pa i := lt_of_le_of_ne (hPa0 i) (Ne.symm h)
      have := vn_concave (fun j => p (i, j) / Pa i) (fun j => div_nonneg (hp0 _) (hPa0 i))
        (by rw [← Finset.sum_div]; exact div_self h)
        (fun j => QAlgorithms.traceRight (ρij (i, j))) (fun j => hρA _)
      have h2 := mul_le_mul_of_nonneg_left this (hPa0 i)
      rw [Finset.mul_sum] at h2
      refine le_trans (le_of_eq ?_) h2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, mul_div_cancel₀ _ h]
  have hcB : ∀ j, ∑ i, p (i, j) * QAlgorithms.vnEntropy (QAlgorithms.traceLeft (ρij (i, j)))
      ≤ Pb j * QAlgorithms.vnEntropy (τ' j) := by
    intro j
    by_cases h : Pb j = 0
    · simp [hPbz j h, h]
    · have hpos : 0 < Pb j := lt_of_le_of_ne (hPb0 j) (Ne.symm h)
      have := vn_concave (fun i => p (i, j) / Pb j) (fun i => div_nonneg (hp0 _) (hPb0 j))
        (by rw [← Finset.sum_div]; exact div_self h)
        (fun i => QAlgorithms.traceLeft (ρij (i, j))) (fun i => hρB _)
      have h2 := mul_le_mul_of_nonneg_left this (hPb0 j)
      rw [Finset.mul_sum] at h2
      refine le_trans (le_of_eq ?_) h2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, mul_div_cancel₀ _ h]
  have sA := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcA i
  have sB := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hcB j
  rw [← Fintype.sum_prod_type'] at sA
  rw [Finset.sum_comm, ← Fintype.sum_prod_type'] at sB
  rw [key]
  have e : ∑ ij, p ij * mutualInfo (ρij ij) =
      ∑ ij, p ij * QAlgorithms.vnEntropy (QAlgorithms.traceRight (ρij ij)) +
      ∑ ij, p ij * QAlgorithms.vnEntropy (QAlgorithms.traceLeft (ρij ij)) -
      ∑ ij, p ij * QAlgorithms.vnEntropy (ρij ij) := by
    simp only [mutualInfo, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e]
  have sB' : ∑ x : ι × κ, p x * QAlgorithms.vnEntropy (QAlgorithms.traceLeft (ρij x)) ≤
      ∑ j, Pb j * QAlgorithms.vnEntropy (τ' j) := by
    convert sB using 1
  linarith
