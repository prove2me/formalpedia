-- Prove2me | solution 1 for KSPolySign.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T14:02:31.391699+00:00
-- url     : https://prove2.me/submissions/481a7c0c-446c-400e-bed0-caf76eaee2b9

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
import Definitions.Def_KSPolySign_pot
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

namespace KSPolySign.L34
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


section KSOrd
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem algebraMap_eq {n : ℕ} (r : ℝ) :
    algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) r = ((r : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one]
  ext i j
  simp [Matrix.smul_apply, one_apply]

theorem posDef_margin {n : ℕ} (hn : 1 ≤ n) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosDef) :
    ∃ r : ℝ, 0 < r ∧ (X - ((r : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsp := isStrictlyPositive_iff_posDef.mpr hX
  have hsa : IsSelfAdjoint X := hX.isHermitian
  have hspec := (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp hsp).2
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff hsa).mpr hspec
  refine ⟨r, hr, ?_⟩
  rw [← algebraMap_eq]
  exact Matrix.le_iff.mp hle

theorem norm_le_of_two_sided {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) {c : ℝ}
    (hc : 0 ≤ c)
    (h1 : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - M).PosSemidef)
    (h2 : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + M).PosSemidef) : ‖M‖ ≤ c := by
  have hsa : IsSelfAdjoint M := hM
  have hup : M ≤ algebraMap ℝ _ c := by rw [algebraMap_eq]; exact Matrix.le_iff.mpr h1
  have hlo : algebraMap ℝ _ (-c) ≤ M := by
    rw [algebraMap_eq]; apply Matrix.le_iff.mpr
    have e : M - ((-c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
        ((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + M := by
      push_cast; rw [neg_smul, sub_neg_eq_add, add_comm]
    rw [e]; exact h2
  have hs1 := (le_algebraMap_iff_spectrum_le hsa).mp hup
  have hs2 := (algebraMap_le_iff_le_spectrum hsa).mp hlo
  rw [← hsa.toReal_spectralRadius_eq_norm]
  apply ENNReal.toReal_le_of_le_ofReal hc
  unfold spectralRadius
  refine iSup₂_le fun x hx => ?_
  have := abs_le.mpr ⟨hs2 x hx, hs1 x hx⟩
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal this

end KSOrd


section L2
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem opNorm_eq_l2 {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    AgnosticTNS.opNorm M = ‖M‖ := by
  rw [Matrix.cstar_norm_def, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  unfold AgnosticTNS.opNorm
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq]; exact Real.sqrt_le_one.mpr hx
    · rw [EuclideanSpace.norm_eq]; simp
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.ofLp, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq] at hx
      simpa using (Real.sqrt_le_one (x := ∑ i, ‖x i‖ ^ 2)).mp hx
    · rw [EuclideanSpace.norm_eq]; simp

theorem herm_le_norm {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) :
    (((‖X‖ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef := by
  have hsa : IsSelfAdjoint X := hX
  have := hsa.le_algebraMap_norm_self
  rw [algebraMap_eq] at this
  exact Matrix.le_iff.mp this

theorem Msum_herm {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, (C i).IsHermitian) (F : Matrix (Fin n) (Fin n) ℂ) (hF : F.IsHermitian)
    (y : Fin k → ℝ) : (Msum C F y).IsHermitian := by
  unfold Msum IsHermitian
  rw [conjTranspose_add, hF.eq, conjTranspose_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_smul, (hC i).eq]; simp

theorem coupling_herm {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, (C i).IsHermitian) (y : Fin k → ℝ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.IsHermitian) : (coupling C y D).IsHermitian := by
  unfold coupling IsHermitian
  rw [conjTranspose_smul, conjTranspose_sum]
  simp only [conjTranspose_smul, conjTranspose_mul, (hC _).eq, hD.eq, Complex.star_def,
    Complex.conj_ofReal, Matrix.mul_assoc]

theorem smul_one_inv {n : ℕ} (c : ℂ) (hc : c ≠ 0) :
    (c • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ = c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  apply Matrix.inv_eq_left_inv
  rw [smul_mul_smul, Matrix.one_mul, inv_mul_cancel₀ hc, one_smul]

theorem lemma_3_4 :
    ((∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ beta t) ∧ ContinuousOn beta (Set.Icc (-1) 1) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) beta (Set.Ioo (-1) 1) ∧
      beta (-1) = 0 ∧ beta 1 = 0 ∧ beta 0 = 1 ∧
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, 1 - t ^ 2 ≤ beta t ∧ beta t ≤ 1) ∧
    ∀ (n k : ℕ), 1 ≤ n → ∀ C : Fin k → Matrix (Fin n) (Fin n) ℂ, IsInstance C → ∀ ρ : ℝ, 0 < ρ →
      (∀ F : Matrix (Fin n) (Fin n) ℂ, F.IsHermitian → ∀ y : Fin k → ℝ, (∀ i, |y i| ≤ 1) →
        (∀ (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ), Feasible C F y b U V → AgnosticTNS.opNorm (Msum C F y) < b) ∧
        AgnosticTNS.opNorm (Msum C F y) ≤ pot C F ρ y) ∧
      ∀ ζbar : ℝ, AgnosticTNS.opNorm (∑ i, C i * C i) ≤ ζbar →
        pot C 0 ρ 0 ≤ 2 * Real.sqrt (iota * ζbar + 2 * n * ρ) := by
  refine ⟨⟨fun t _ => aux_beta_nonneg t, ?_, ?_, by simp [beta], by simp [beta], by simp [beta], ?_⟩, ?_⟩
  · exact (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).continuousOn
  · unfold beta
    apply ContDiffOn.sqrt
    · exact (contDiff_const.sub (contDiff_id.pow 2)).contDiffOn
    · intro t ht
      have := ht.1; have := ht.2
      nlinarith
  · intro t ht
    have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have h1 : 1 - t ^ 2 ≤ 1 := by nlinarith
    refine ⟨?_, Real.sqrt_le_one.mpr h1⟩
    unfold beta
    calc 1 - t ^ 2 = Real.sqrt ((1 - t ^ 2) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  intro n k hn C hC ρ hρ
  have hCH : ∀ i, (C i).IsHermitian := fun i => (hC.1 i).1.isHermitian
  constructor
  · intro F hF y hy
    have hM := Msum_herm C hCH F hF y
    have hlt : ∀ (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ), Feasible C F y b U V →
        ‖Msum C F y‖ < b := by
      intro b U V hfe
      have hb := aux_b_pos hn C hCH F y b U V hfe
      obtain ⟨hU, hV, h1, h2⟩ := hfe
      have hP1 : (((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Msum C F y).PosDef := by
        have := (hU.inv.add_posSemidef (h1.add (aux_coupling_psd C hCH y V hV.posSemidef)))
        have e : ((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Msum C F y = U⁻¹ +
            (((b : ℝ) : ℂ) • 1 - (U⁻¹ + Msum C F y + coupling C y V) + coupling C y V) := by abel
        rw [e]; exact this
      have hP2 : (((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + Msum C F y).PosDef := by
        have := (hV.inv.add_posSemidef (h2.add (aux_coupling_psd C hCH y U hU.posSemidef)))
        have e : ((b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + Msum C F y = V⁻¹ +
            (((b : ℝ) : ℂ) • 1 - (V⁻¹ - Msum C F y + coupling C y U) + coupling C y U) := by abel
        rw [e]; exact this
      obtain ⟨r1, hr1, hq1⟩ := posDef_margin hn hP1
      obtain ⟨r2, hr2, hq2⟩ := posDef_margin hn hP2
      set r := min (min r1 r2) b with hr
      have hr0 : 0 < r := lt_min (lt_min hr1 hr2) hb
      have hrb : r ≤ b := min_le_right _ _
      have hrr1 : r ≤ r1 := (min_le_left _ _).trans (min_le_left _ _)
      have hrr2 : r ≤ r2 := (min_le_left _ _).trans (min_le_right _ _)
      have hI : ∀ c : ℝ, 0 ≤ c → (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
        intro c hc; exact PosSemidef.one.smul (by exact_mod_cast hc)
      have hle : ‖Msum C F y‖ ≤ b - r := by
        apply norm_le_of_two_sided hM (by linarith)
        · convert hq1.add (hI (r1 - r) (by linarith)) using 1
          push_cast; rw [sub_smul, sub_smul]; abel
        · convert hq2.add (hI (r2 - r) (by linarith)) using 1
          push_cast; rw [sub_smul, sub_smul]; abel
      linarith
    refine ⟨fun b U V h => by rw [opNorm_eq_l2]; exact hlt b U V h, ?_⟩
    rw [opNorm_eq_l2]
    unfold pot
    apply le_csInf
    · -- nonempty
      set X1 := (1 : Matrix (Fin n) (Fin n) ℂ) + Msum C F y + coupling C y 1
      set X2 := (1 : Matrix (Fin n) (Fin n) ℂ) - Msum C F y + coupling C y 1
      have hK1 := coupling_herm C hCH y 1 isHermitian_one
      have hX1 : X1.IsHermitian := (isHermitian_one.add hM).add hK1
      have hX2 : X2.IsHermitian := (isHermitian_one.sub hM).add hK1
      set b := ‖X1‖ + ‖X2‖
      refine ⟨b + ρ * ((1 : Matrix (Fin n) (Fin n) ℂ) + 1).trace.re, b, 1, 1, ⟨PosDef.one, PosDef.one, ?_, ?_⟩, rfl⟩
      · rw [inv_one]
        convert (herm_le_norm hX1).add (PosSemidef.one.smul (a := ((‖X2‖ : ℝ) : ℂ))
          (by exact_mod_cast norm_nonneg X2)) using 1
        simp only [b, X1]; push_cast; rw [add_smul]; abel
      · rw [inv_one]
        convert (herm_le_norm hX2).add (PosSemidef.one.smul (a := ((‖X1‖ : ℝ) : ℂ))
          (by exact_mod_cast norm_nonneg X1)) using 1
        simp only [b, X2]; push_cast; rw [add_smul]; abel
    · rintro v ⟨b, U, V, hfe, rfl⟩
      have h1 := hlt b U V hfe
      have h2 := aux_value_pos hn C hCH F y ρ hρ b U V hfe
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      have ht := (hfe.1.add hfe.2.1).trace_pos
      have : 0 < (U + V).trace.re := (Complex.pos_iff.mp ht).1
      nlinarith
  · intro ζbar hζ
    rw [opNorm_eq_l2] at hζ
    have hio : (0:ℝ) < iota := by norm_num [iota]
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hζ0 : 0 ≤ ζbar := (norm_nonneg _).trans hζ
    set S := iota * ζbar + 2 * n * ρ with hS
    have hSpos : 0 < S := by positivity
    set q := Real.sqrt S with hq
    have hqpos : 0 < q := Real.sqrt_pos.mpr hSpos
    have hqq : q * q = S := Real.mul_self_sqrt hSpos.le
    set s := 1 / q with hs
    have hspos : 0 < s := by positivity
    set b := q + iota * s * ζbar
    have hsumH : (∑ i, C i * C i).IsHermitian := by
      unfold IsHermitian
      rw [conjTranspose_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [conjTranspose_mul, (hCH i).eq]
    have hζI : (((ζbar : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - ∑ i, C i * C i).PosSemidef := by
      convert (herm_le_norm hsumH).add (PosSemidef.one.smul (a := (((ζbar - ‖∑ i, C i * C i‖) : ℝ) : ℂ))
        (by exact_mod_cast (sub_nonneg.mpr hζ))) using 1
      push_cast; rw [sub_smul]; abel
    have hcoup : coupling C (0 : Fin k → ℝ) (((s : ℝ) : ℂ) • 1) =
        ((iota * s : ℝ) : ℂ) • ∑ i, C i * C i := by
      unfold coupling
      have hb0 : beta 0 = 1 := by simp [beta]
      simp only [Pi.zero_apply, hb0, Complex.ofReal_one, one_smul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, ← Finset.smul_sum, smul_smul]
      push_cast; ring_nf
    have hMsum : Msum C 0 (0 : Fin k → ℝ) = 0 := by simp [Msum]
    have hUinv : (((s : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ =
        ((q : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [smul_one_inv _ (by exact_mod_cast hspos.ne')]
      congr 1; rw [hs]; push_cast; field_simp
    have hUpd : (((s : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      PosDef.one.smul (by exact_mod_cast hspos)
    have hfe : Feasible C 0 (0 : Fin k → ℝ) b (((s : ℝ) : ℂ) • 1) (((s : ℝ) : ℂ) • 1) := by
      have hpsd : (((iota * s : ℝ) : ℂ) • ((((ζbar : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
          ∑ i, C i * C i))).PosSemidef := hζI.smul (by exact_mod_cast (by positivity : (0:ℝ) ≤ iota * s))
      refine ⟨hUpd, hUpd, ?_, ?_⟩
      · rw [hUinv, hMsum, hcoup]
        convert hpsd using 1
        simp only [b]; push_cast; rw [smul_sub, smul_smul, add_smul]; abel
      · rw [hUinv, hMsum, hcoup]
        convert hpsd using 1
        simp only [b]; push_cast; rw [smul_sub, smul_smul, add_smul]; abel
    have := aux_pot_le hn C hCH 0 0 ρ hρ b _ _ hfe
    refine this.trans (le_of_eq ?_)
    rw [← smul_add, trace_smul, trace_add, trace_one, Fintype.card_fin]
    simp only [b, smul_eq_mul]
    rw [show ((s : ℂ) * ((n : ℂ) + (n : ℂ))).re = s * (2 * n) by
      rw [show ((n : ℂ) + (n : ℂ)) = ((2 * n : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_mul, Complex.ofReal_re]]
    rw [hs]
    field_simp
    nlinarith [hqq]

end L2

end KSPolySign.L34

open Matrix
open scoped ComplexOrder
open KSPolySign

theorem solution :
    ((∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ beta t) ∧ ContinuousOn beta (Set.Icc (-1) 1) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) beta (Set.Ioo (-1) 1) ∧
      beta (-1) = 0 ∧ beta 1 = 0 ∧ beta 0 = 1 ∧
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, 1 - t ^ 2 ≤ beta t ∧ beta t ≤ 1) ∧
    ∀ (n k : ℕ), 1 ≤ n → ∀ C : Fin k → Matrix (Fin n) (Fin n) ℂ, IsInstance C → ∀ ρ : ℝ, 0 < ρ →
      (∀ F : Matrix (Fin n) (Fin n) ℂ, F.IsHermitian → ∀ y : Fin k → ℝ, (∀ i, |y i| ≤ 1) →
        (∀ (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ), Feasible C F y b U V → AgnosticTNS.opNorm (Msum C F y) < b) ∧
        AgnosticTNS.opNorm (Msum C F y) ≤ pot C F ρ y) ∧
      ∀ ζbar : ℝ, AgnosticTNS.opNorm (∑ i, C i * C i) ≤ ζbar →
        pot C 0 ρ 0 ≤ 2 * Real.sqrt (iota * ζbar + 2 * n * ρ) := by
  apply KSPolySign.L34.lemma_3_4 <;> assumption
