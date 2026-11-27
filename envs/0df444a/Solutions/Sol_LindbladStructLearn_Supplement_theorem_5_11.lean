-- Prove2me | solution 1 for LindbladStructLearn.Supplement.theorem_5_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:46:18.901678+00:00
-- url     : https://prove2.me/submissions/f21aa478-eb23-4c29-8b39-557715ce5154

import Mathlib
import Definitions.Def_LindbladStructLearn_Supplement_HamiltonianF
import Definitions.Def_LindbladStructLearn_b1Norm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix NNReal
noncomputable section


namespace LindbladStructLearn.Supplement.H511
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.Supplement

variable {n k : ℕ}

lemma b1Norm_nonneg' (y : Pauli n × Pauli n → ℂ) : 0 ≤ b1Norm y := by
  unfold b1Norm; exact NNReal.coe_nonneg _

lemma b1Norm_le_comb (y u w : Pauli n × Pauli n → ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ P, ‖y P‖ ≤ a * ‖u P‖ + b * ‖w P‖) : b1Norm y ≤ a * b1Norm u + b * b1Norm w := by
  have hbu := b1Norm_nonneg' u
  have hbw := b1Norm_nonneg' w
  have key : ∀ (v : Pauli n × Pauli n → ℂ) (i : Fin n),
      (∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0 ∧ i ∈ pairSupport P),
        ‖v P‖) ≤ b1Norm v := by
    intro v i
    unfold b1Norm
    have := Finset.le_sup (f := fun i : Fin n =>
      ∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0 ∧ i ∈ pairSupport P),
        ‖v P‖₊) (Finset.mem_univ i)
    have h2 : ((∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0 ∧ i ∈ pairSupport P),
        ‖v P‖₊ : ℝ≥0) : ℝ) = ∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n =>
          P.1 ≠ 0 ∧ i ∈ pairSupport P), ‖v P‖ := by
      rw [NNReal.coe_sum]; rfl
    rw [← h2]
    exact_mod_cast this
  unfold b1Norm
  have : (Finset.univ.sup fun i : Fin n =>
      ∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0 ∧ i ∈ pairSupport P),
        ‖y P‖₊) ≤ ⟨a * b1Norm u + b * b1Norm w, by positivity⟩ := by
    apply Finset.sup_le
    intro i _
    show ((∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0 ∧ i ∈ pairSupport P),
        ‖y P‖₊ : ℝ≥0) : ℝ) ≤ a * b1Norm u + b * b1Norm w
    rw [NNReal.coe_sum]
    simp only [coe_nnnorm]
    calc ∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0 ∧ i ∈ pairSupport P), ‖y P‖
        ≤ ∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0 ∧ i ∈ pairSupport P),
            (a * ‖u P‖ + b * ‖w P‖) := Finset.sum_le_sum (fun P _ => h P)
      _ = a * (∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0 ∧ i ∈ pairSupport P),
            ‖u P‖) + b * (∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n =>
              P.1 ≠ 0 ∧ i ∈ pairSupport P), ‖w P‖) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ a * b1Norm u + b * b1Norm w := by
            gcongr
            · exact key u i
            · exact key w i
  exact this

lemma norm_hamVec_le (y u w : HIdx n k → ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ P, ‖y P‖ ≤ a * ‖u P‖ + b * ‖w P‖) (P : Pauli n × Pauli n) :
    ‖hamVec y P‖ ≤ a * ‖hamVec u P‖ + b * ‖hamVec w P‖ := by
  unfold hamVec
  split_ifs with hP
  · exact h _
  · simp

lemma b1_hamVec_comb (y u w : HIdx n k → ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ P, ‖y P‖ ≤ a * ‖u P‖ + b * ‖w P‖) :
    b1Norm (hamVec y) ≤ a * b1Norm (hamVec u) + b * b1Norm (hamVec w) :=
  b1Norm_le_comb _ _ _ a b ha hb (norm_hamVec_le y u w a b ha hb h)

end LindbladStructLearn.Supplement.H511


namespace LindbladStructLearn.Supplement.H511
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.Supplement

variable {n k : ℕ}

lemma clm_apply_decomp (L : (HIdx n k → ℂ) →L[ℂ] ℂ) (Δ : HIdx n k → ℂ) :
    L Δ = ∑ Q, Δ Q * L (Pi.single Q 1) := by
  classical
  conv_lhs => rw [show Δ = ∑ Q, Δ Q • (Pi.single Q (1 : ℂ) : HIdx n k → ℂ) by
    funext P; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  simp [map_smul]

open Classical in
lemma F_lin_bound (F : (HIdx n k → ℂ) → (HIdx n k → ℂ)) (lam x : HIdx n k → ℂ) (g C : ℝ)
    (hg : 0 ≤ g) (hlam : b1Norm (hamVec lam) ≤ g) (hx : b1Norm (hamVec x) ≤ 2 * g)
    (hF0 : F lam = 0)
    (hdiff : ∀ y : HIdx n k → ℂ, b1Norm (hamVec y) ≤ 2 * g → ∀ P,
      DifferentiableAt ℂ (fun z => F z P) y)
    (hjac : ∀ y : HIdx n k → ℂ, b1Norm (hamVec y) ≤ 2 * g → ∀ P : HIdx n k,
      ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0),
        ‖jac F y P Q - (if P = Q then 1 else 0)‖ ≤ C)
    (hsupp : ∀ Q, lam Q = 0 → x Q = 0) (P : HIdx n k) :
    ‖F x P - (x P - lam P)‖ ≤ C * ‖x - lam‖ := by
  set Δ := x - lam with hΔ
  set p : ℝ → HIdx n k → ℂ := fun s => lam + (s : ℂ) • Δ with hp
  have hpB : ∀ s ∈ Set.Icc (0 : ℝ) 1, b1Norm (hamVec (p s)) ≤ 2 * g := by
    intro s hs
    have h1 : b1Norm (hamVec (p s)) ≤ (1 - s) * b1Norm (hamVec lam) + s * b1Norm (hamVec x) := by
      apply b1_hamVec_comb _ _ _ (1 - s) s (by linarith [hs.2]) hs.1
      intro Q
      have : p s Q = ((1 - s : ℝ) : ℂ) * lam Q + (s : ℂ) * x Q := by
        simp only [hp, hΔ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; push_cast; ring
      rw [this]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by linarith [hs.2]), Real.norm_of_nonneg hs.1]
    have h2 : (1 - s) * b1Norm (hamVec lam) + s * b1Norm (hamVec x) ≤ (1 - s) * g + s * (2 * g) := by
      gcongr
      · linarith [hs.2]
      · exact hs.1
    nlinarith [hs.1, hs.2]
  set f : ℝ → ℂ := fun s => F (p s) P - (s : ℂ) * Δ P with hf
  set f' : ℝ → ℂ := fun s => fderiv ℂ (fun z => F z P) (p s) Δ - Δ P with hf'
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f (f' s) (Set.Icc 0 1) s := by
    intro s hs
    apply HasDerivAt.hasDerivWithinAt
    have hpath : HasDerivAt p Δ s := by
      have := ((hasDerivAt_id s).ofReal_comp).smul_const Δ
      simp only [Function.comp_def, id] at this
      have h2 := this.const_add lam
      simpa [hp] using h2
    have hF := ((hdiff (p s) (hpB s hs) P).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hpath
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * Δ P) (Δ P) s := by
      have := (hasDerivAt_id s).ofReal_comp.mul_const (Δ P)
      simpa using this
    exact hF.sub hlin
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖f' s‖ ≤ C * ‖Δ‖ := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    simp only [hf']
    rw [clm_apply_decomp]
    have hδ : Δ P = ∑ Q, Δ Q * (if P = Q then 1 else 0) := by
      rw [Finset.sum_eq_single P]
      · simp
      · intro b _ hb; rw [if_neg (Ne.symm hb), mul_zero]
      · simp
    rw [hδ, ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    have hjacs := hjac (p s) (hpB s hs') P
    calc ‖∑ Q, Δ Q * ((fderiv ℂ (fun z => F z P) (p s)) (Pi.single Q 1) - if P = Q then 1 else 0)‖
        ≤ ∑ Q, ‖Δ Q‖ * ‖(fderiv ℂ (fun z => F z P) (p s)) (Pi.single Q 1) -
            if P = Q then 1 else 0‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp_rw [norm_mul]
      _ = ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0), ‖Δ Q‖ *
            ‖jac F (p s) P Q - if P = Q then 1 else 0‖ := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun Q _ => ?_)
          by_cases hQ : lam Q ≠ 0
          · rw [if_pos hQ]; rfl
          · rw [if_neg hQ]
            push Not at hQ
            have : Δ Q = 0 := by simp [hΔ, hsupp Q hQ, hQ]
            rw [this, norm_zero, zero_mul]
      _ ≤ ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0), ‖Δ‖ *
            ‖jac F (p s) P Q - if P = Q then 1 else 0‖ := by
          apply Finset.sum_le_sum
          intro Q _
          exact mul_le_mul_of_nonneg_right (norm_le_pi_norm Δ Q) (norm_nonneg _)
      _ = ‖Δ‖ * ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0),
            ‖jac F (p s) P Q - if P = Q then 1 else 0‖ := by rw [Finset.mul_sum]
      _ ≤ ‖Δ‖ * C := mul_le_mul_of_nonneg_left hjacs (norm_nonneg _)
      _ = C * ‖Δ‖ := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  simp only [hf, hp] at this
  have h0 : F (lam + ((0 : ℝ) : ℂ) • Δ) P = 0 := by simp [hF0]
  have h1 : lam + ((1 : ℝ) : ℂ) • Δ = x := by simp [hΔ]
  rw [h0, h1] at this
  simpa [hΔ] using this

end LindbladStructLearn.Supplement.H511


namespace LindbladStructLearn.Supplement.H511
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.Supplement

variable {n k : ℕ}

open Classical in
theorem alg5_conv (F : (HIdx n k → ℂ) → (HIdx n k → ℂ)) (lam : HIdx n k → ℂ) (g C ε : ℝ)
    (hε : 0 < ε) (hC0 : 0 ≤ C) (hC : C < 1 / 20) (hB1 : b1Norm (hamVec lam) ≤ g)
    (hinf : ∀ P, ‖lam P‖ ≤ 1) (hF0 : F lam = 0)
    (hdiff : ∀ y : HIdx n k → ℂ, b1Norm (hamVec y) ≤ 2 * g → ∀ P,
      DifferentiableAt ℂ (fun z => F z P) y)
    (hjac : ∀ y : HIdx n k → ℂ, b1Norm (hamVec y) ≤ 2 * g → ∀ P : HIdx n k,
      ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0),
        ‖jac F y P Q - (if P = Q then 1 else 0)‖ ≤ C)
    (Fhat : ℕ → (HIdx n k → ℂ) → (HIdx n k → ℂ))
    (hFhat : ∀ j < ⌈Real.logb 2 (1 / ε)⌉₊,
      ‖F (alg5Iter Fhat j) - Fhat j (alg5Iter Fhat j)‖ ≤ ε / 20) :
    ‖alg5Iter Fhat ⌈Real.logb 2 (1 / ε)⌉₊ - lam‖ ≤ ε := by
  set T := ⌈Real.logb 2 (1 / ε)⌉₊ with hT
  have hg : 0 ≤ g := le_trans (b1Norm_nonneg' _) hB1
  have hεj : ∀ j < T, ε ≤ 1 / 2 ^ j := by
    intro j hj
    have h1 : (j : ℝ) < Real.logb 2 (1 / ε) := Nat.lt_ceil.1 hj
    have h2 : (2 : ℝ) ^ (j : ℝ) < 2 ^ Real.logb 2 (1 / ε) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_natCast] at h2
    rw [le_div_iff₀ (by positivity)]
    have := (lt_div_iff₀ hε).1 h2
    linarith
  have inv : ∀ j ≤ T, ‖alg5Iter Fhat j - lam‖ ≤ 1 / 2 ^ j ∧
      ∀ P, ‖alg5Iter Fhat j P‖ ≤ 2 * ‖lam P‖ := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [alg5Iter, zero_sub, norm_neg, pow_zero, div_one, Pi.zero_apply, norm_zero]
      refine ⟨(pi_norm_le_iff_of_nonneg zero_le_one).2 hinf, fun P => by positivity⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      set x := alg5Iter Fhat j with hx
      have hxB : b1Norm (hamVec x) ≤ 2 * g := by
        have := b1_hamVec_comb x lam lam 2 0 (by norm_num) le_rfl
          (fun P => by have := h2 P; linarith)
        linarith
      have hsupp : ∀ Q, lam Q = 0 → x Q = 0 := by
        intro Q hQ
        have := h2 Q
        rw [hQ, norm_zero, mul_zero] at this
        exact norm_le_zero_iff.1 this
      have hlin := F_lin_bound F lam x g C hg hB1 hxB hF0 hdiff hjac hsupp
      have hest := hFhat j (by omega)
      have hεj' := hεj j (by omega)
      set e : ℝ := 1 / 2 ^ j with he
      have hepos : 0 < e := by positivity
      have hy : ∀ P, ‖(x - Fhat j x) P - lam P‖ ≤ e / 10 := by
        intro P
        have hP1 := hlin P
        have hP2 : ‖F x P - Fhat j x P‖ ≤ ε / 20 := (norm_le_pi_norm (F x - Fhat j x) P).trans hest
        have : (x - Fhat j x) P - lam P = -(F x P - (x P - lam P)) + (F x P - Fhat j x P) := by
          simp only [Pi.sub_apply]; ring
        rw [this]
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        have : C * ‖x - lam‖ ≤ C * e := mul_le_mul_of_nonneg_left h1 hC0
        nlinarith
      have hy' : ∀ P, ‖x P - Fhat j x P - lam P‖ ≤ e / 10 := fun P => by simpa using hy P
      have hstep : alg5Iter Fhat (j + 1) = roundVec (e / 4) (x - Fhat j x) := by
        simp only [alg5Iter, hx, he]
      have he2 : 1 / (2 : ℝ) ^ (j + 1) = e / 2 := by rw [he, pow_succ]; field_simp
      rw [hstep, he2]
      constructor
      · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
        intro P
        simp only [Pi.sub_apply, roundVec]
        split_ifs with hr
        · rw [zero_sub, norm_neg]
          have := norm_sub_norm_le (lam P) (x P - Fhat j x P)
          have h3 := hy' P
          rw [norm_sub_rev] at h3
          linarith
        · have := hy' P; linarith
      · intro P
        simp only [roundVec]
        split_ifs with hr
        · simp
        · push Not at hr
          have h3 := hy' P
          have hr' : e / 4 < ‖x P - Fhat j x P‖ := by simpa using hr
          have h4 := norm_sub_norm_le (x P - Fhat j x P) (lam P)
          show ‖x P - Fhat j x P‖ ≤ 2 * ‖lam P‖
          linarith
  have hfin := (inv T le_rfl).1
  refine hfin.trans ?_
  have h1 : Real.logb 2 (1 / ε) ≤ (T : ℝ) := Nat.le_ceil _
  have h2 : (2 : ℝ) ^ Real.logb 2 (1 / ε) ≤ 2 ^ (T : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_natCast] at h2
  rw [div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left h2 hε.le
  rw [mul_one_div_cancel hε.ne'] at this
  linarith

end LindbladStructLearn.Supplement.H511


namespace LindbladStructLearn.Supplement.H511
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.Supplement

variable {n k : ℕ}

lemma hamOp_differentiable (x : HIdx n k → ℂ) :
    letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
    DifferentiableAt ℂ (fun y : HIdx n k → ℂ => hamOp y) x := by
  letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
  let L : (HIdx n k → ℂ) →ₗ[ℂ] Op (Qubits n) :=
    { toFun := fun y => hamOp y
      map_add' := fun y z => by
        simp only [hamOp, Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]
      map_smul' := fun c y => by
        simp only [hamOp, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, RingHom.id_apply]
        rw [smul_comm] }
  exact (LinearMap.toContinuousLinearMap L).differentiableAt

lemma exp_differentiable (M : Op (Qubits n)) :
    letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
    DifferentiableAt ℂ (NormedSpace.exp : Op (Qubits n) → Op (Qubits n)) M := by
  letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
  apply AnalyticAt.differentiableAt
  apply NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℂ)
  rw [NormedSpace.expSeries_radius_eq_top]
  simp

lemma trace_differentiable :
    letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
    ∀ M : Op (Qubits n), DifferentiableAt ℂ (fun A : Op (Qubits n) => A.trace) M := by
  letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
  intro M
  exact (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Qubits n) ℂ ℂ)).differentiableAt

lemma trace_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}
    (f : E → Op (Qubits n)) :
    letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
    DifferentiableAt ℂ f x → DifferentiableAt ℂ (fun y => (f y).trace) x := by
  letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
  intro hf
  exact (trace_differentiable (f x)).comp x hf

lemma mul_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}
    (f g : E → Op (Qubits n)) :
    letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
    DifferentiableAt ℂ f x → DifferentiableAt ℂ g x →
      DifferentiableAt ℂ (fun y => f y * g y) x := by
  letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
  intro hf hg
  exact hf.mul hg

lemma rtF_differentiable (t : ℝ) (lam x : HIdx n k → ℂ) (P : HIdx n k) :
    DifferentiableAt ℂ (fun y => rtF t lam y P) x := by
  letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
  unfold rtF rtExpVec pauliAvg ntr
  simp only [div_eq_mul_inv]
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.sub_const
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.fun_sum
  intro R _
  apply DifferentiableAt.mul_const
  have hH := hamOp_differentiable (k := k) x
  have hS1 : DifferentiableAt ℂ (fun y : HIdx n k → ℂ => (-((t : ℂ) * Complex.I)) • hamOp y) x :=
    hH.fun_const_smul _
  have hS2 : DifferentiableAt ℂ (fun y : HIdx n k → ℂ => ((t : ℂ) * Complex.I) • hamOp y) x :=
    hH.fun_const_smul _
  have h1 : DifferentiableAt ℂ (fun y : HIdx n k → ℂ =>
      NormedSpace.exp ((-((t : ℂ) * Complex.I)) • hamOp y)) x :=
    (exp_differentiable _).comp x hS1
  have h2 : DifferentiableAt ℂ (fun y : HIdx n k → ℂ =>
      NormedSpace.exp (((t : ℂ) * Complex.I) • hamOp y)) x :=
    (exp_differentiable _).comp x hS2
  have hc : ∀ M : Op (Qubits n), DifferentiableAt ℂ (fun _ : HIdx n k → ℂ => M) x :=
    fun M => differentiableAt_const M
  apply trace_comp
  apply mul_comp _ _ _ (hc _)
  apply mul_comp _ _ _ (hc _)
  apply mul_comp _ _ _ h2
  exact mul_comp _ _ h1 (hc _)

lemma gibbsF_differentiable (β : ℝ) (lam x : HIdx n k → ℂ) (P : HIdx n k)
    (hx : (NormedSpace.exp (-(β : ℂ) • hamOp x)).trace ≠ 0) :
    DifferentiableAt ℂ (fun y => gibbsF β lam y P) x := by
  letI : NormedRing (Op (Qubits n)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Op (Qubits n)) := Matrix.linftyOpNormedAlgebra
  unfold gibbsF gibbsExpVec WolfAreaLaw.thermalState QAlgorithms.gibbsState
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub_const
  have hH := hamOp_differentiable (k := k) x
  have hS : DifferentiableAt ℂ (fun y : HIdx n k → ℂ => (-(β : ℂ)) • hamOp y) x :=
    hH.fun_const_smul _
  have hE : DifferentiableAt ℂ (fun y : HIdx n k → ℂ =>
      NormedSpace.exp (-(β : ℂ) • hamOp y)) x :=
    (exp_differentiable _).comp x hS
  have htr : DifferentiableAt ℂ (fun y : HIdx n k → ℂ =>
      (NormedSpace.exp (-(β : ℂ) • hamOp y)).trace) x := trace_comp _ hE
  have hinv := htr.inv hx
  have : (fun y : HIdx n k → ℂ => (pauliMatrix P.1 * ((NormedSpace.exp (-(β : ℂ) • hamOp y)).trace⁻¹ •
      NormedSpace.exp (-(β : ℂ) • hamOp y))).trace) =
      fun y => (NormedSpace.exp (-(β : ℂ) • hamOp y)).trace⁻¹ *
        (pauliMatrix P.1 * NormedSpace.exp (-(β : ℂ) • hamOp y)).trace := by
    funext y; rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [this]
  exact hinv.mul (trace_comp _ (mul_comp _ _ (differentiableAt_const _) hE))

end LindbladStructLearn.Supplement.H511


namespace LindbladStructLearn.Supplement.H511
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.Supplement

variable {n k : ℕ}

theorem theorem_5_11_aux (ε : ℝ) (hε : 0 < ε) (g : ℝ) (lam : HIdx n k → ℂ)
    (hlam : ∀ P, (lam P).re = 0) (hB1 : b1Norm (hamVec lam) ≤ g) (hinf : ∀ P, ‖lam P‖ ≤ 1)
    (c : ℝ) (hc : 0 < c) :
    (∀ t : ℝ, 0 < t → t < 1 / (20 * c) →
      ∀ Fhat : ℕ → (HIdx n k → ℂ) → (HIdx n k → ℂ),
      (∀ j < ⌈Real.logb 2 (1 / ε)⌉₊,
        ‖rtF t lam (alg5Iter Fhat j) - Fhat j (alg5Iter Fhat j)‖ ≤ ε / 20) →
      (∀ x : HIdx n k → ℂ, b1Norm (hamVec x) ≤ 2 * g → ∀ P : HIdx n k,
        ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0),
          ‖jac (rtF t lam) x P Q - (if P = Q then 1 else 0)‖ ≤ c * t) →
      ‖alg5Iter Fhat ⌈Real.logb 2 (1 / ε)⌉₊ - lam‖ ≤ ε) ∧
    (∀ β : ℝ, 0 < β → β < 1 / (20 * c) →
      ∀ Fhat : ℕ → (HIdx n k → ℂ) → (HIdx n k → ℂ),
      (∀ j < ⌈Real.logb 2 (1 / ε)⌉₊,
        ‖gibbsF β lam (alg5Iter Fhat j) - Fhat j (alg5Iter Fhat j)‖ ≤ ε / 20) →
      (∀ x : HIdx n k → ℂ, b1Norm (hamVec x) ≤ 2 * g →
        (NormedSpace.exp (-(β : ℂ) • hamOp x)).trace ≠ 0 ∧ ∀ P : HIdx n k,
        ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0),
          ‖jac (gibbsF β lam) x P Q - (if P = Q then 1 else 0)‖ ≤ c * β) →
      ‖alg5Iter Fhat ⌈Real.logb 2 (1 / ε)⌉₊ - lam‖ ≤ ε) := by
  classical
  constructor
  · intro t ht ht' Fhat hF hJ
    have hct : c * t < 1 / 20 := by
      rw [lt_div_iff₀ (by positivity)] at ht'
      rw [lt_div_iff₀ (by norm_num)]; nlinarith
    refine alg5_conv (rtF t lam) lam g (c * t) ε hε (by positivity) hct hB1 hinf ?_
      (fun y _ P => rtF_differentiable t lam y P) ?_ Fhat hF
    · funext P; simp [rtF]
    · intro y hy P
      convert hJ y hy P
  · intro β hβ hβ' Fhat hF hJ
    have hcb : c * β < 1 / 20 := by
      rw [lt_div_iff₀ (by positivity)] at hβ'
      rw [lt_div_iff₀ (by norm_num)]; nlinarith
    refine alg5_conv (gibbsF β lam) lam g (c * β) ε hε (by positivity) hcb hB1 hinf ?_
      (fun y hy P => gibbsF_differentiable β lam y P (hJ y hy).1) ?_ Fhat hF
    · funext P; simp [gibbsF]
    · intro y hy P
      convert (hJ y hy).2 P

end LindbladStructLearn.Supplement.H511

open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.Supplement

theorem solution (n k : ℕ) (ε : ℝ) (hε : 0 < ε) (g : ℝ) (lam : HIdx n k → ℂ)
    (hlam : ∀ P, (lam P).re = 0) (hB1 : b1Norm (hamVec lam) ≤ g) (hinf : ∀ P, ‖lam P‖ ≤ 1)
    (c : ℝ) (hc : 0 < c) :
    (∀ t : ℝ, 0 < t → t < 1 / (20 * c) →
      ∀ Fhat : ℕ → (HIdx n k → ℂ) → (HIdx n k → ℂ),
      (∀ j < ⌈Real.logb 2 (1 / ε)⌉₊,
        ‖rtF t lam (alg5Iter Fhat j) - Fhat j (alg5Iter Fhat j)‖ ≤ ε / 20) →
      (∀ x : HIdx n k → ℂ, b1Norm (hamVec x) ≤ 2 * g → ∀ P : HIdx n k,
        ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0),
          ‖jac (rtF t lam) x P Q - (if P = Q then 1 else 0)‖ ≤ c * t) →
      ‖alg5Iter Fhat ⌈Real.logb 2 (1 / ε)⌉₊ - lam‖ ≤ ε) ∧
    (∀ β : ℝ, 0 < β → β < 1 / (20 * c) →
      ∀ Fhat : ℕ → (HIdx n k → ℂ) → (HIdx n k → ℂ),
      (∀ j < ⌈Real.logb 2 (1 / ε)⌉₊,
        ‖gibbsF β lam (alg5Iter Fhat j) - Fhat j (alg5Iter Fhat j)‖ ≤ ε / 20) →
      (∀ x : HIdx n k → ℂ, b1Norm (hamVec x) ≤ 2 * g →
        (NormedSpace.exp (-(β : ℂ) • hamOp x)).trace ≠ 0 ∧ ∀ P : HIdx n k,
        ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0),
          ‖jac (gibbsF β lam) x P Q - (if P = Q then 1 else 0)‖ ≤ c * β) →
      ‖alg5Iter Fhat ⌈Real.logb 2 (1 / ε)⌉₊ - lam‖ ≤ ε) :=
  LindbladStructLearn.Supplement.H511.theorem_5_11_aux ε hε g lam hlam hB1 hinf c hc
