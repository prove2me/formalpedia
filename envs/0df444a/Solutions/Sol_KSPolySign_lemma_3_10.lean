-- Prove2me | solution 1 for KSPolySign.lemma_3_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T13:35:33.242707+00:00
-- url     : https://prove2.me/submissions/5e66c4b4-1835-4f2b-871d-50368dd16b63

import Mathlib
import Definitions.Def_KSPolySign_IsOptimal
import Definitions.Def_KSPolySign_IsInstance
open Matrix
open scoped ComplexOrder

namespace KSLib

theorem exists_vecMulVec_of_rank_le_one {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (h : C.rank ≤ 1) :
    ∃ a b : Fin n → ℂ, C = vecMulVec a b := by
  classical
  have h' : Module.finrank ℂ (LinearMap.range C.mulVecLin) ≤ 1 := h
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h'
  have hcol : ∀ j : Fin n, ∃ c : ℂ, c • (v : Fin n → ℂ) = C *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨c, hc⟩ := hv ⟨C *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  choose c hc using hcol
  refine ⟨v, c, ?_⟩
  ext i j
  have := congrFun (hc j) i
  simp [mulVec_single] at this
  simp [vecMulVec_apply, ← this, mul_comm]

theorem sandwich_of_rank_le_one {n : ℕ} (C D : Matrix (Fin n) (Fin n) ℂ) (h : C.rank ≤ 1) :
    C * D * C = (C * D).trace • C := by
  obtain ⟨a, b, rfl⟩ := exists_vecMulVec_of_rank_le_one C h
  ext i j
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, trace, diag, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem trace_mul_nonneg_of_posSemidef {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  open scoped MatrixOrder in
  open scoped Matrix.Norms.L2Operator in
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.mul_assoc, trace_mul_comm]
  rw [Matrix.mul_assoc]
  have := (hB.mul_mul_conjTranspose_same S)
  simp only [star_eq_conjTranspose] at *
  rw [← Matrix.mul_assoc]
  exact this.trace_nonneg

theorem trace_mul_re_nonneg_of_posSemidef {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re :=
  (Complex.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hA hB)).1

end KSLib

namespace KSPolySign.L310
open KSPolySign

theorem aux_sum_update {k n : ℕ} (y : Fin k → ℝ) (i : Fin k) (s : ℝ)
    (g : Fin k → ℝ → Matrix (Fin n) (Fin n) ℂ) :
    ∑ j, g j (Function.update y i s j) = ∑ j, g j (y j) + (g i s - g i (y i)) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, g j (Function.update y i s j) =
      ∑ j ∈ Finset.univ.erase i, g j (y j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this, Function.update_self]
  abel

theorem aux_beta_nonneg (t : ℝ) : 0 ≤ beta t := Real.sqrt_nonneg _

theorem aux_coupling_psd {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, (C i).IsHermitian) (y : Fin k → ℝ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.PosSemidef) : (coupling C y D).PosSemidef := by
  unfold coupling
  apply PosSemidef.smul _ (by exact_mod_cast (show (0:ℝ) ≤ iota by norm_num [iota]))
  apply posSemidef_sum
  intro j _
  apply PosSemidef.smul _ (by exact_mod_cast aux_beta_nonneg _)
  have := hD.conjTranspose_mul_mul_same (C j)
  rwa [(hC j).eq] at this

theorem aux_b_pos {n k : ℕ} (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, (C i).IsHermitian) (F : Matrix (Fin n) (Fin n) ℂ) (y : Fin k → ℝ) (b : ℝ)
    (U V : Matrix (Fin n) (Fin n) ℂ) (h : Feasible C F y b U V) : 0 < b := by
  obtain ⟨hU, hV, h1, h2⟩ := h
  have hsum := ((h1.add h2).add (aux_coupling_psd C hC y V hV.posSemidef)).add (aux_coupling_psd C hC y U hU.posSemidef)
  have hVi := hV.inv.posSemidef
  have := hsum.add hVi
  let x : Fin n → ℂ := Pi.single ⟨0, hn⟩ 1
  have hx : x ≠ 0 := by
    intro h0; have := congrFun h0 ⟨0, hn⟩; simp [x] at this
  have e : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (U⁻¹ + Msum C F y + coupling C y V)) +
      ((b : ℂ) • 1 - (V⁻¹ - Msum C F y + coupling C y U)) + coupling C y V + coupling C y U + V⁻¹
      = ((2 * b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - U⁻¹ := by
    push_cast; rw [two_mul, add_smul]; abel
  rw [e] at this
  have p1 := this.re_dotProduct_nonneg x
  have p2 := hU.inv.re_dotProduct_pos hx
  simp only [sub_mulVec, dotProduct_sub, map_sub, smul_mulVec, one_mulVec, dotProduct_smul] at p1
  have : RCLike.re (star x ⬝ᵥ x) = 1 := by simp [x]
  simp only [smul_eq_mul] at p1
  rw [RCLike.re_eq_complex_re, Complex.re_ofReal_mul] at p1
  rw [RCLike.re_eq_complex_re] at p2 this
  rw [this] at p1
  linarith

theorem aux_value_pos {n k : ℕ} (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, (C i).IsHermitian) (F : Matrix (Fin n) (Fin n) ℂ) (y : Fin k → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (b : ℝ)
    (U V : Matrix (Fin n) (Fin n) ℂ) (h : Feasible C F y b U V) : 0 < b + ρ * (U + V).trace.re := by
  have hb := aux_b_pos hn C hC F y b U V h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have ht := (h.1.add h.2.1).trace_pos
  have : 0 < (U + V).trace.re := (Complex.pos_iff.mp ht).1
  positivity

theorem aux_pot_le {n k : ℕ} (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, (C i).IsHermitian) (F : Matrix (Fin n) (Fin n) ℂ) (y : Fin k → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (b : ℝ)
    (U V : Matrix (Fin n) (Fin n) ℂ) (h : Feasible C F y b U V) :
    pot C F ρ y ≤ b + ρ * (U + V).trace.re := by
  unfold pot
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨b', U', V', hf, rfl⟩
    exact (aux_value_pos hn C hC F y ρ hρ b' U' V' hf).le
  · exact ⟨b, U, V, h, rfl⟩


theorem aux_Msum_update {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin k → ℝ) (i : Fin k) (s : ℝ) :
    Msum C F (Function.update y i s) = Msum C F y + (((s - y i : ℝ)) : ℂ) • C i := by
  unfold Msum
  rw [aux_sum_update y i s (fun j t => ((t : ℝ) : ℂ) • C j)]
  push_cast
  rw [sub_smul]; abel

theorem aux_coupling_update {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (y : Fin k → ℝ) (i : Fin k) (s : ℝ) (hs : beta s = 0) (D : Matrix (Fin n) (Fin n) ℂ) :
    coupling C (Function.update y i s) D =
      coupling C y D - ((iota * beta (y i) : ℝ) : ℂ) • (C i * D * C i) := by
  unfold coupling
  rw [aux_sum_update y i s (fun j t => ((beta t : ℝ) : ℂ) • (C j * D * C j)), hs]
  push_cast
  rw [smul_add, zero_smul, zero_sub, smul_neg, mul_smul]
  abel

theorem aux_tr_real {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A * B).trace = (((A * B).trace.re : ℝ) : ℂ) := by
  have := KSLib.trace_mul_nonneg_of_posSemidef hA hB
  rw [Complex.nonneg_iff] at this
  apply Complex.ext <;> simp [this.2.symm]

theorem aux_psd_add_smul {n : ℕ} {X D : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosSemidef)
    (hD : D.PosSemidef) {c : ℝ} (hc : 0 ≤ c) : (X + ((c : ℝ) : ℂ) • D).PosSemidef :=
  hX.add (hD.smul (by exact_mod_cast hc))

theorem lemma_3_10 (n k : ℕ) (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (hC : IsInstance C)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : F.IsHermitian) (ρ : ℝ) (hρ : 0 < ρ)
    (y : Fin k → ℝ) (hy : ∀ i, |y i| ≤ 1) (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ) (hopt : IsOptimal C F ρ y b U V)
    (i : Fin k) (hi : |y i| < 1) :
    (1 - y i ≤ iota * beta (y i) * (C i * V).trace.re →
        Feasible C F (Function.update y i 1) b U V ∧
          pot C F ρ (Function.update y i 1) ≤ pot C F ρ y) ∧
      (1 + y i ≤ iota * beta (y i) * (C i * U).trace.re →
        Feasible C F (Function.update y i (-1)) b U V ∧
          pot C F ρ (Function.update y i (-1)) ≤ pot C F ρ y) := by
  obtain ⟨⟨hU, hV, h1, h2⟩, hval⟩ := hopt
  have hCH : ∀ j, (C j).IsHermitian := fun j => (hC.1 j).1.isHermitian
  have hCi := (hC.1 i).1
  have hr := (hC.1 i).2
  have hu := KSLib.trace_mul_re_nonneg_of_posSemidef hCi hU.posSemidef
  have hv := KSLib.trace_mul_re_nonneg_of_posSemidef hCi hV.posSemidef
  set u := (C i * U).trace.re with hu_def
  set v := (C i * V).trace.re with hv_def
  have hsU : C i * U * C i = ((u : ℝ) : ℂ) • C i := by
    rw [KSLib.sandwich_of_rank_le_one (C i) U hr.le]
    exact congrArg (· • C i) (aux_tr_real hCi hU.posSemidef)
  have hsV : C i * V * C i = ((v : ℝ) : ℂ) • C i := by
    rw [KSLib.sandwich_of_rank_le_one (C i) V hr.le]
    exact congrArg (· • C i) (aux_tr_real hCi hV.posSemidef)
  have hb := aux_beta_nonneg (y i)
  have hio : (0:ℝ) ≤ iota := by norm_num [iota]
  have hy1 := abs_lt.mp hi
  have hb1 : beta 1 = 0 := by simp [beta]
  have hbm1 : beta (-1) = 0 := by simp [beta]
  have hbu : 0 ≤ iota * beta (y i) * u := by positivity
  have hbv : 0 ≤ iota * beta (y i) * v := by positivity
  constructor
  · intro hcond
    have hfeas : Feasible C F (Function.update y i 1) b U V := by
      refine ⟨hU, hV, ?_, ?_⟩
      · convert aux_psd_add_smul h1 hCi (c := iota * beta (y i) * v - (1 - y i)) (by linarith) using 1
        rw [aux_Msum_update, aux_coupling_update C y i 1 hb1, hsV]
        push_cast
        module
      · convert aux_psd_add_smul h2 hCi (c := (1 - y i) + iota * beta (y i) * u) (by linarith) using 1
        rw [aux_Msum_update, aux_coupling_update C y i 1 hb1, hsU]
        push_cast
        module
    exact ⟨hfeas, hval ▸ aux_pot_le hn C hCH F _ ρ hρ b U V hfeas⟩
  · intro hcond
    have hfeas : Feasible C F (Function.update y i (-1)) b U V := by
      refine ⟨hU, hV, ?_, ?_⟩
      · convert aux_psd_add_smul h1 hCi (c := (1 + y i) + iota * beta (y i) * v) (by linarith) using 1
        rw [aux_Msum_update, aux_coupling_update C y i (-1) hbm1, hsV]
        push_cast
        module
      · convert aux_psd_add_smul h2 hCi (c := iota * beta (y i) * u - (1 + y i)) (by linarith) using 1
        rw [aux_Msum_update, aux_coupling_update C y i (-1) hbm1, hsU]
        push_cast
        module
    exact ⟨hfeas, hval ▸ aux_pot_le hn C hCH F _ ρ hρ b U V hfeas⟩

end KSPolySign.L310

open Matrix
open scoped ComplexOrder
open KSPolySign

theorem solution (n k : ℕ) (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (hC : IsInstance C)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : F.IsHermitian) (ρ : ℝ) (hρ : 0 < ρ)
    (y : Fin k → ℝ) (hy : ∀ i, |y i| ≤ 1) (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ) (hopt : IsOptimal C F ρ y b U V)
    (i : Fin k) (hi : |y i| < 1) :
    (1 - y i ≤ iota * beta (y i) * (C i * V).trace.re →
        Feasible C F (Function.update y i 1) b U V ∧
          pot C F ρ (Function.update y i 1) ≤ pot C F ρ y) ∧
      (1 + y i ≤ iota * beta (y i) * (C i * U).trace.re →
        Feasible C F (Function.update y i (-1)) b U V ∧
          pot C F ρ (Function.update y i (-1)) ≤ pot C F ρ y) := by
  apply KSPolySign.L310.lemma_3_10 <;> assumption
