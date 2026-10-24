-- Prove2me | solution 1 for ModernConvex.Ellipsoids.outer_sum_sdp_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T00:12:39.593782+00:00
-- url     : https://prove2.me/submissions/a6e324fd-0ae4-443a-99ac-5ab3db723908

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Definitions.Def_ModernConvex_Ellipsoids_Programs
import Theorems.Thm_ModernConvex_Ellipsoids_nesterov_ye

open Matrix MeasureTheory
open scoped ENNReal

namespace OS100
open ModernConvex.Ellipsoids

lemma V_unitBall_bdd (n : ℕ) : Bornology.IsBounded (unitBall n) := by
  refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset ?_
  intro u hu
  simp only [unitBall, Set.mem_ofPred_eq, dotProduct] at hu
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h1 : u i * u i ≤ ∑ j, u j * u j :=
    Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j))
      (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  have : |u i| * |u i| ≤ 1 := by rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; linarith
  nlinarith [abs_nonneg (u i)]

lemma V_unitBall_pos (n : ℕ) : volume (unitBall n) ≠ 0 := by
  have hopen : IsOpen {u : Fin n → ℝ | u ⬝ᵥ u < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hne : ({u : Fin n → ℝ | u ⬝ᵥ u < 1}).Nonempty := ⟨0, by simp⟩
  have := hopen.measure_pos volume hne
  refine (lt_of_lt_of_le this (measure_mono ?_)).ne'
  intro u hu
  exact le_of_lt (show u ⬝ᵥ u < 1 from hu)

theorem vol_quadSet {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosDef) :
    Vol (quadSet Z) = ENNReal.ofReal (Z.det ^ (-(1 : ℝ) / 2)) := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.posSemidef.nonneg
  have hBt : star B = Bᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hBt] at hB
  have hdet : Z.det = B.det ^ 2 := by rw [hB, det_mul, det_transpose]; ring
  have hZd : 0 < Z.det := hZ.det_pos
  have hBd : B.det ≠ 0 := by
    intro h; rw [hdet, h] at hZd; simp at hZd
  have hset : quadSet Z = (Matrix.toLin' B) ⁻¹' unitBall n := by
    ext x
    simp only [quadSet, unitBall, Set.mem_ofPred_eq, Set.mem_preimage, Matrix.toLin'_apply]
    rw [hB, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have hdetf : LinearMap.det (Matrix.toLin' B) ≠ 0 := by rwa [LinearMap.det_toLin']
  have hc : |(LinearMap.det (Matrix.toLin' B))⁻¹| = Z.det ^ (-(1 : ℝ) / 2) := by
    rw [LinearMap.det_toLin', hdet, abs_inv, ← sq_abs, ← Real.rpow_natCast,
      ← Real.rpow_mul (abs_nonneg _)]
    norm_num [Real.rpow_neg_one]
  unfold Vol
  rw [hset, MeasureTheory.Measure.addHaar_preimage_linearMap _ hdetf, hc]
  exact ENNReal.mul_div_cancel_right (V_unitBall_pos n) (V_unitBall_bdd n).measure_lt_top.ne

end OS100


open Matrix MeasureTheory
open scoped ENNReal

namespace OS100
open ModernConvex.Ellipsoids

lemma N_qf_sub {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι ι ℝ) (e : ι ≃ κ) (x : κ → ℝ) :
    x ⬝ᵥ (M.submatrix e.symm e.symm *ᵥ x) = (x ∘ e) ⬝ᵥ (M *ᵥ (x ∘ e)) := by
  simp only [dotProduct, mulVec, submatrix_apply, Function.comp]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← e.sum_comp]
  simp

lemma N_qf_blockSel {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (i : Fin m)
    (X : Fin m × Fin n → ℝ) :
    X ⬝ᵥ (blockSel B i *ᵥ X) = (fun k => X (i, k)) ⬝ᵥ (B i *ᵥ fun k => X (i, k)) := by
  simp [dotProduct, mulVec, blockSel, Fintype.sum_prod_type, ite_and, Finset.mul_sum]

lemma N_qf_blockAll {m n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin m × Fin n → ℝ) :
    X ⬝ᵥ (blockAll Z *ᵥ X) = (fun k => ∑ i, X (i, k)) ⬝ᵥ (Z *ᵥ fun k => ∑ i, X (i, k)) := by
  simp only [dotProduct, mulVec, blockAll, of_apply, Fintype.sum_prod_type, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]

lemma N_smul_qf {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (s : ℝ) (v : Fin k → ℝ) :
    (s • v) ⬝ᵥ (M *ᵥ (s • v)) = s * s * (v ⬝ᵥ (M *ᵥ v)) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

lemma N_cmp {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, (B i).PosDef)
    (Zss : Matrix (Fin n) (Fin n) ℝ)
    (hcont : minkowskiSum (fun i => quadSet (B i)) ⊆ quadSet Zss) (v : Fin m → Fin n → ℝ) :
    (∑ i, v i) ⬝ᵥ (Zss *ᵥ ∑ i, v i) ≤ ∑ i, v i ⬝ᵥ (B i *ᵥ v i) := by
  have hq : ∀ i, 0 ≤ v i ⬝ᵥ (B i *ᵥ v i) := fun i => by
    simpa using (hB i).posSemidef.dotProduct_mulVec_nonneg (v i)
  set t := ∑ i, v i ⬝ᵥ (B i *ᵥ v i) with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => hq i
  apply le_of_forall_pos_le_add
  intro ε hε
  have htε : 0 < t + ε := by linarith
  set s := Real.sqrt (1 / (t + ε)) with hs
  have hss : s * s = 1 / (t + ε) := Real.mul_self_sqrt (by positivity)
  have hmem : (∑ i, s • v i) ∈ quadSet Zss := by
    refine hcont ⟨fun i => s • v i, fun i => ?_, rfl⟩
    show (s • v i) ⬝ᵥ (B i *ᵥ (s • v i)) ≤ 1
    rw [N_smul_qf, hss]
    have : v i ⬝ᵥ (B i *ᵥ v i) ≤ t :=
      Finset.single_le_sum (f := fun i => v i ⬝ᵥ (B i *ᵥ v i)) (fun j _ => hq j)
        (Finset.mem_univ i)
    rw [div_mul_eq_mul_div, one_mul, div_le_one htε]; linarith
  have h2 : (s • ∑ i, v i) ⬝ᵥ (Zss *ᵥ (s • ∑ i, v i)) ≤ 1 := by
    rw [Finset.smul_sum]; exact hmem
  rw [N_smul_qf, hss, div_mul_eq_mul_div, one_mul, div_le_one htε] at h2
  exact h2

lemma N_bs_mul_zero {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) {i j : Fin m} (hij : i ≠ j) :
    blockSel B i * blockSel B j = 0 := by
  ext r c
  simp only [mul_apply, blockSel, of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs with h1 h2
  · exact absurd (h1.2.symm.trans h2.1) hij
  all_goals simp

lemma N_bs_herm {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, (B i).IsHermitian)
    (i : Fin m) : (blockSel B i).IsHermitian := by
  refine IsHermitian.ext fun r c => ?_
  simp only [blockSel, of_apply, star_trivial]
  split_ifs with h1 h2 h2
  · simpa using (hB i).apply r.2 c.2
  · exact absurd ⟨h1.2, h1.1⟩ h2
  · exact absurd ⟨h2.2, h2.1⟩ h1
  · rfl

lemma N_ba_herm {m n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.IsHermitian) :
    (blockAll (m := m) Z).IsHermitian := by
  refine IsHermitian.ext fun r c => ?_
  simpa [blockAll] using hZ.apply r.2 c.2

open scoped MatrixOrder in
lemma N_trace_nonneg {k : ℕ} {M X : Matrix (Fin k) (Fin k) ℝ} (hM : M.PosSemidef)
    (hX : X.PosSemidef) : 0 ≤ (M * X).trace := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  rw [← mul_assoc, trace_mul_comm, ← mul_assoc]
  exact (hM.mul_mul_conjTranspose_same C).trace_nonneg

theorem sdd_mult {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, (B i).PosDef)
    (Zss : Matrix (Fin n) (Fin n) ℝ) (hZss : Zss.PosDef)
    (hcont : minkowskiSum (fun i => quadSet (B i)) ⊆ quadSet Zss) :
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i ≤ Real.pi / 2 ∧
      (∑ i, lam i • blockSel B i - blockAll Zss).PosSemidef := by
  classical
  set e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv with he
  let S : QuadraticSystem (m * n) m :=
    ⟨fun i => (blockSel B i).submatrix e.symm e.symm, fun _ => 1,
      (blockAll Zss).submatrix e.symm e.symm⟩
  let V : (Fin (m * n) → ℝ) → Fin m → Fin n → ℝ := fun x i k => x (e (i, k))
  have hqB : ∀ i x, x ⬝ᵥ (S.B i *ᵥ x) = V x i ⬝ᵥ (B i *ᵥ V x i) := by
    intro i x
    show x ⬝ᵥ ((blockSel B i).submatrix e.symm e.symm *ᵥ x) = _
    rw [N_qf_sub, N_qf_blockSel]; rfl
  have hqA : ∀ x, x ⬝ᵥ (S.A *ᵥ x) = (∑ i, V x i) ⬝ᵥ (Zss *ᵥ ∑ i, V x i) := by
    intro x
    show x ⬝ᵥ ((blockAll Zss).submatrix e.symm e.symm *ᵥ x) = _
    rw [N_qf_sub, N_qf_blockAll]
    have : (fun k => ∑ i, (x ∘ e) (i, k)) = ∑ i, V x i := by
      funext k; simp [V, Finset.sum_apply]
    rw [this]
  have hBh : ∀ i, (S.B i).IsHermitian := fun i =>
    (N_bs_herm B (fun i => (hB i).1) i).submatrix _
  have hAh : S.A.IsHermitian := (N_ba_herm Zss hZss.1).submatrix _
  have hcomm : ∀ i j, S.B i * S.B j = S.B j * S.B i := by
    intro i j
    show (blockSel B i).submatrix e.symm e.symm * (blockSel B j).submatrix e.symm e.symm =
      (blockSel B j).submatrix e.symm e.symm * (blockSel B i).submatrix e.symm e.symm
    rw [submatrix_mul_equiv, submatrix_mul_equiv]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [N_bs_mul_zero B hij, N_bs_mul_zero B (Ne.symm hij)]
  have hstrict : S.StrictlyFeasible := ⟨0, fun i => by simp [S]⟩
  have hqnn : ∀ i x, 0 ≤ x ⬝ᵥ (S.B i *ᵥ x) := fun i x => by
    rw [hqB]; simpa using (hB i).posSemidef.dotProduct_mulVec_nonneg (V x i)
  have hpd : ∃ μ : Fin m → ℝ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • S.B i).PosDef := by
    refine ⟨fun _ => 1, fun _ => zero_le_one, ?_⟩
    simp only [one_smul]
    refine PosDef.of_dotProduct_mulVec_pos (isSelfAdjoint_sum _ fun i _ => hBh i) ?_
    intro x hx
    rw [star_trivial, sum_mulVec, dotProduct_sum]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h; push Not at h; exact hx (funext h)
    have hV : V x (e.symm j).1 ≠ 0 := by
      intro h0
      have := congrFun h0 (e.symm j).2
      simp [V] at this
      exact hj this
    have hpos : 0 < x ⬝ᵥ (S.B (e.symm j).1 *ᵥ x) := by
      rw [hqB]; simpa using (hB _).dotProduct_mulVec_pos hV
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i => x ⬝ᵥ (S.B i *ᵥ x))
      (fun i _ => hqnn i x) (Finset.mem_univ _))
  have hA : S.A.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg hAh fun x => ?_
    rw [star_trivial, hqA]; simpa using hZss.posSemidef.dotProduct_mulVec_nonneg _
  have hPA : (∑ i, S.B i - S.A).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      ((isSelfAdjoint_sum _ fun i _ => hBh i).sub hAh) fun x => ?_
    rw [star_trivial, sub_mulVec, dotProduct_sub, sum_mulVec, dotProduct_sum, sub_nonneg, hqA]
    simp_rw [hqB]
    exact N_cmp B hB Zss hcont (V x)
  -- P-value
  set Pset := (fun x => x ⬝ᵥ (S.A *ᵥ x)) '' {x | S.Solves x} with hPset
  have hPne : Pset.Nonempty := ⟨_, 0, fun i => by simp [S], rfl⟩
  have hPub : ∀ y ∈ Pset, y ≤ 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show x ⬝ᵥ (S.A *ᵥ x) ≤ 1
    rw [hqA]
    exact hcont ⟨V x, fun i => by
      show V x i ⬝ᵥ (B i *ᵥ V x i) ≤ 1
      rw [← hqB]; exact hx i, rfl⟩
  have hf : S.IsPValue (sSup Pset) := isLUB_csSup hPne ⟨1, hPub⟩
  have hf1 : sSup Pset ≤ 1 := csSup_le hPne hPub
  -- SDP value
  set Fset := (fun X => (S.A * X).trace) '' {X | S.SDPFeasible X} with hFset
  have hFne : Fset.Nonempty :=
    ⟨_, 0, ⟨fun i => by simp [S], PosSemidef.zero⟩, rfl⟩
  have hFub : ∀ y ∈ Fset, y ≤ (m : ℝ) := by
    rintro _ ⟨X, ⟨hX1, hX2⟩, rfl⟩
    have h1 := N_trace_nonneg hPA hX2
    rw [sub_mul, trace_sub, Finset.sum_mul, trace_sum, sub_nonneg] at h1
    refine h1.trans ?_
    calc ∑ i, (S.B i * X).trace ≤ ∑ _i : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => hX1 i
      _ = m := by simp
  have hF : S.IsSDPValue (sSup Fset) := isLUB_csSup hFne ⟨m, hFub⟩
  obtain ⟨-, ⟨⟨lam, ⟨hlamPSD, hlam0⟩, hval⟩, -⟩, hle⟩ :=
    ModernConvex.Ellipsoids.nesterov_ye S hBh (fun _ => zero_le_one) hcomm hstrict hpd hA
      (sSup Pset) (sSup Fset) hf hF
  have hsum : ∑ i, lam i = sSup Fset := by simpa [S] using hval
  refine ⟨lam, hlam0, ?_, ?_⟩
  · rw [hsum]
    have hpi : 0 ≤ Real.pi / 2 := by positivity
    nlinarith
  · have : ∑ i, lam i • S.B i - S.A =
        (∑ i, lam i • blockSel B i - blockAll Zss).submatrix e.symm e.symm := by
      ext a b; simp [S, Matrix.sum_apply]
    rw [this] at hlamPSD
    exact (posSemidef_submatrix_equiv e.symm).mp hlamPSD

end OS100


open Matrix MeasureTheory
open scoped ENNReal

namespace OS100
open ModernConvex.Ellipsoids

theorem blockSel_psd {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, (B i).PosDef)
    (i : Fin m) : (blockSel B i).PosSemidef := by
  -- direct proof via quadratic form
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext r c
    simp only [blockSel, conjTranspose_apply, of_apply, star_trivial]
    by_cases h1 : r.1 = i <;> by_cases h2 : c.1 = i <;> simp [h1, h2]
    have := (hB i).1.apply r.2 c.2
    simpa using this
  · have key : star x ⬝ᵥ (blockSel B i *ᵥ x) =
        (fun k => x (i, k)) ⬝ᵥ (B i *ᵥ fun k => x (i, k)) := by
      simp only [star_trivial, dotProduct, mulVec, blockSel, of_apply, Fintype.sum_prod_type]
      simp [ite_and, Finset.mul_sum]
    rw [key]
    exact (hB i).posSemidef.dotProduct_mulVec_nonneg _ |> fun h => by simpa using h

theorem blockAll_smul {m n : ℕ} (c : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (blockAll (c • Z) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ) = c • blockAll Z := by
  ext r s; simp [blockAll]

theorem main {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, (B i).PosDef)
    (Zss : Matrix (Fin n) (Fin n) ℝ) (hZss : Zss.PosDef)
    (hcont : minkowskiSum (fun i => quadSet (B i)) ⊆ quadSet Zss)
    (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (lam : Fin m → ℝ) (hopt : OOptimal B t Z lam) :
    Vol (quadSet Z) ≤
      ENNReal.ofReal ((Real.pi / 2) ^ ((n : ℝ) / 2)) * Vol (quadSet Zss) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have := hopt.1.2.2.2.2
    simp at this
  obtain ⟨μ, hμ0, hμs, hμpsd⟩ := sdd_mult B hB Zss hZss hcont
  set F := ∑ i, μ i with hF
  set k : ℝ := 2 / Real.pi with hk
  have hk0 : 0 < k := by positivity
  set sl : ℝ := (1 - k * F) / m with hsl
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hkF : k * F ≤ 1 := by
    rw [hk, div_mul_eq_mul_div, div_le_one hpi]; linarith
  have hsl0 : 0 ≤ sl := div_nonneg (by linarith) hmpos.le
  set lam' : Fin m → ℝ := fun i => k * μ i + sl with hlam'
  set Z2 : Matrix (Fin n) (Fin n) ℝ := k • Zss with hZ2
  have hfeas : OFeasible B (Z2.det ^ ((1 : ℝ) / n)) Z2 lam' := by
    refine ⟨le_rfl, ?_, fun i => add_nonneg (mul_nonneg hk0.le (hμ0 i)) hsl0, (hZss.smul hk0).posSemidef, ?_⟩
    · have e : ∑ i, lam' i • blockSel B i - blockAll Z2 =
          k • (∑ i, μ i • blockSel B i - blockAll Zss) + sl • ∑ i, blockSel B i := by
        simp only [hlam', add_smul, Finset.sum_add_distrib, hZ2, blockAll_smul, smul_sub,
          Finset.smul_sum, mul_smul]
        abel
      rw [e]
      exact (hμpsd.smul hk0.le).add ((posSemidef_sum Finset.univ fun i _ => blockSel_psd B hB i).smul hsl0)
    · simp only [hlam', Finset.sum_add_distrib, ← Finset.mul_sum, ← hF, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsl]
      field_simp
      ring
  have ht := hopt.2 _ _ _ hfeas
  have htZ := hopt.1.1
  have hZpsd := hopt.1.2.2.2.1
  have hdetZ2 : Z2.det = k ^ n * Zss.det := by rw [hZ2, det_smul, Fintype.card_fin]
  have hdss := hZss.det_pos
  have hdet : Z2.det ≤ Z.det := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [Matrix.det_isEmpty]
    · have hn' : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      exact (Real.rpow_le_rpow_iff (by rw [hdetZ2]; positivity) hZpsd.det_nonneg hn').mp
        (le_trans ht htZ)
  have hdZ2pos : 0 < Z2.det := by rw [hdetZ2]; positivity
  have hZpd : Z.PosDef := hZpsd.posDef_iff_det_ne_zero.mpr (by linarith)
  rw [vol_quadSet Z hZpd, vol_quadSet Zss hZss, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc Z.det ^ (-(1 : ℝ) / 2) ≤ Z2.det ^ (-(1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos hdZ2pos hdet (by norm_num)
    _ = (Real.pi / 2) ^ ((n : ℝ) / 2) * Zss.det ^ (-(1 : ℝ) / 2) := by
        rw [hdetZ2, Real.mul_rpow (by positivity) hdss.le, ← Real.rpow_natCast,
          ← Real.rpow_mul hk0.le]
        congr 1
        rw [hk, show ((n : ℝ) * (-(1 : ℝ) / 2)) = -((n : ℝ) / 2) by ring, Real.rpow_neg (by positivity),
          ← Real.inv_rpow (by positivity), inv_div]

end OS100

open Matrix
open ModernConvex.Ellipsoids

theorem solution {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, (B i).PosDef)
    (Zss : Matrix (Fin n) (Fin n) ℝ) (hZss : Zss.PosDef)
    (hcont : minkowskiSum (fun i => quadSet (B i)) ⊆ quadSet Zss)
    (hmin : ∀ E : Set (Fin n → ℝ), IsFullDimEllipsoid E →
      minkowskiSum (fun i => quadSet (B i)) ⊆ E → Vol (quadSet Zss) ≤ Vol E)
    (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (lam : Fin m → ℝ) (hopt : OOptimal B t Z lam) :
    Vol (quadSet Z) ≤
      ENNReal.ofReal ((Real.pi / 2) ^ ((n : ℝ) / 2)) * Vol (quadSet Zss) :=
  OS100.main B hB Zss hZss hcont t Z lam hopt
