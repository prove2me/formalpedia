-- Prove2me | solution 1 for LogLogJam.pure_angular_curvature_integral
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:14:42.340301+00:00
-- url     : https://prove2.me/submissions/6f9cc46a-f3b9-41c4-9585-e7ce885360e0

import Definitions.Def_LogLogJam_Obs

open Matrix LogLogJam MeasureTheory Filter

open scoped Matrix.Norms.L2Operator MatrixOrder Kronecker ENNReal Topology

noncomputable section

set_option maxHeartbeats 600000

set_option linter.unusedSimpArgs false

namespace LogLogJam.PureProof

private abbrev M (k : ℕ) := Matrix (Q k) (Q k) ℝ
private abbrev J (k : ℕ) := Omega k
private def Z (k : ℕ) : M k := ( !![1,0;0,-1] : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
private def R (k : ℕ) (x : ℝ) : M k := Real.cos x • 1 + Real.sin x • J k
private def L (k : ℕ) (t : ℝ) : M k := R k (-(2*t)) * Z k
private lemma neg_kron (k : ℕ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (-B) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ) = -(B ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)) := by
  ext i j; simp [Matrix.kroneckerMap_apply]
private lemma Jsq (k) : J k * J k = -1 := by
  unfold J Omega
  rw [← Matrix.mul_kronecker_mul,one_mul]
  have h : (!![0,1;-1,0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0,1;-1,0] = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_two]
  rw [h,neg_kron]; simp
private lemma Zsq (k) : Z k * Z k = 1 := by
  unfold Z
  rw [← Matrix.mul_kronecker_mul,one_mul]
  have h : (!![1,0;0,-1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1,0;0,-1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_two]
  rw [h]; simp
private lemma ZJ (k) : Z k * J k = -(J k * Z k) := by
  unfold Z J Omega
  rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,one_mul]
  have h : (!![1,0;0,-1] : Matrix (Fin 2) (Fin 2) ℝ) * !![0,1;-1,0] = -(!![0,1;-1,0] * !![1,0;0,-1]) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_two]
  rw [h,neg_kron]
private lemma Rzero (k) : R k 0 = 1 := by simp [R]
private lemma Rmul (k) (x y) : R k x * R k y = R k (x+y) := by
  simp only [R,Real.cos_add,Real.sin_add,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,Jsq,smul_smul,add_smul,sub_smul,smul_neg,smul_add]
  ext i j; simp [smul_eq_mul]; ring
private lemma Rpow (k) (x) (n : ℕ) : R k x ^ n = R k (n*x) := by
  induction n with
  | zero => simp [Rzero]
  | succ n ih => rw [pow_succ,ih,Rmul]; congr 1; push_cast; ring
private lemma Rcomm {k} (B : M k) (h : B * J k = J k * B) (x) : B * R k x = R k x * B := by
  simp only [R,mul_add,add_mul,smul_mul_assoc,mul_smul_comm,mul_one,one_mul,h]
private lemma Ranti {k} (B : M k) (h : B * J k = -(J k * B)) (x) : B * R k x = R k (-x) * B := by
  simp only [R,mul_add,add_mul,smul_mul_assoc,mul_smul_comm,mul_one,one_mul,h,Real.cos_neg,Real.sin_neg,neg_smul,smul_neg,neg_mul]
private lemma Jrot (k) (x) : J k * R k x = R k x * J k := Rcomm _ rfl _
private lemma Lsq (k) (t) : L k t * L k t = 1 := by
  unfold L
  calc
    _ = R k (-(2*t)) * (Z k * R k (-(2*t))) * Z k := by simp [mul_assoc]
    _ = _ := by rw [Ranti _ (ZJ k),neg_neg,← mul_assoc,Rmul,neg_add_cancel,Rzero,one_mul,Zsq]
private lemma LJ (k) (t) : L k t * J k = -(J k * L k t) := by
  simp only [L,mul_assoc,ZJ,mul_neg];rw [← mul_assoc,← Jrot, mul_assoc]
private lemma CZcomm {k} (C : M k) (hc : C * J k = -(J k * C)) : (C*Z k) * J k = J k * (C*Z k) := by
  rw [mul_assoc,ZJ,mul_neg,← mul_assoc,hc,neg_mul,neg_neg,mul_assoc]
private lemma CLpow {k} (C : M k) (hc : C * J k = -(J k * C)) (t) (n : ℕ) :
    (C * L k t)^n = R k (n*(2*t)) * (C*Z k)^n := by
  have h := Rcomm (C*Z k) (CZcomm C hc) (2*t)
  simp only [L,← mul_assoc C,Ranti _ hc,neg_neg,mul_assoc]
  rw [(show Commute (R k (2*t)) (C*Z k) from h.symm).mul_pow,Rpow]
private lemma anti_trace {k} (A : M k) (ha : A * J k = -(J k * A)) : A.trace = 0 := by
  have h := congrArg Matrix.trace (show J k * A * J k = A by rw [mul_assoc,ha,mul_neg,← mul_assoc,Jsq,neg_mul,one_mul,neg_neg])
  rw [Matrix.trace_mul_cycle,Jsq,neg_mul,one_mul,trace_neg] at h
  linarith

private lemma contract_of_order {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : (1 - Aᴴ*A).PosSemidef) : ‖A‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [EuclideanSpace.real_norm_sq_eq]
  have hx := hA.dotProduct_mulVec_nonneg (x : n → ℝ)
  simp only [sub_mulVec,one_mulVec,dotProduct_sub,sub_nonneg,star_trivial,← mulVec_mulVec,dotProduct_mulVec,vecMul_conjTranspose,star_trivial] at hx
  rw [← dotProduct_mulVec] at hx
  simpa [dotProduct, pow_two] using hx

private def Cmat {k} (W : M k) : M k := 1 - 2 * (W+1)⁻¹
private lemma cayley_props {k} (W : M k) (hp : W.PosDef) (hs : W * J k * W = J k) :
    let C := Cmat W
    ‖C‖ ≤ 1 ∧ C * J k = -(J k * C) ∧ (1-C) * W = 1+C ∧ (1-C)*(W+1) = 2 := by
  let T := W+1
  let U := T⁻¹
  let C := Cmat W
  have hT : T.PosDef := hp.add PosDef.one
  have hUnit := (isUnit_iff_isUnit_det _).mp hT.isUnit
  have hL : U*T = 1 := Matrix.nonsing_inv_mul T hUnit
  have hR : T*U = 1 := Matrix.mul_nonsing_inv T hUnit
  have hci : C = 1-2*U := rfl
  have hTC : T*C = W-1 := by rw [hci]; dsimp only [T] at hR ⊢; noncomm_ring [hR]
  have hCT : C*T = W-1 := by rw [hci,sub_mul,one_mul,mul_assoc,hL,mul_one]; dsimp only [T]; rw [show (2:M k)=1+1 by norm_num];abel
  have hAnti : C * J k = -(J k * C) := by
    apply hT.isUnit.mul_left_cancel
    apply hT.isUnit.mul_right_cancel
    calc
      _ = (W-1) * J k * (W+1) := by rw [← mul_assoc,hTC]
      _ = -((W+1) * J k * (W-1)) := by noncomm_ring [hs]
      _ = _ := by rw [← hCT]; simp [T,mul_assoc]
  have hU : Uᴴ = U := hT.inv.isHermitian.eq
  have hstar : Cᴴ = C := by rw [hci];simp only [two_mul,conjTranspose_sub,conjTranspose_add,conjTranspose_one,hU]
  have hUU : U*W*U = U-U*U := by
    calc
      _ = U*T*U - U*U := by dsimp only [T];noncomm_ring
      _ = _ := by rw [hL,one_mul]
  have hAC : 1-Cᴴ*C = (4:ℝ) • (U*W*Uᴴ) := by
    rw [hstar,hU,hci,hUU];rw [show (4:ℝ)=1+1+1+1 by norm_num];simp only [add_smul,one_smul];noncomm_ring
  have hN := contract_of_order C (hAC ▸ (hp.posSemidef.mul_mul_conjTranspose_same U).smul (show 0≤(4:ℝ) by norm_num))
  refine ⟨hN,hAnti,?_,?_⟩
  · change (1-C)*W = 1+C;dsimp only [T] at hCT;rw [sub_mul,one_mul];rw [mul_add,mul_one] at hCT;abel_nf at hCT ⊢;linear_combination (norm := abel) -hCT
  · change (1-C)*T = 2;rw [sub_mul,one_mul,hCT];dsimp only [T];rw [show (2:M k)=1+1 by norm_num];abel

private lemma starJ (k) : (J k)ᴴ = -(J k) := by
  unfold J Omega; rw [conjTranspose_kronecker,conjTranspose_one,← neg_kron]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> norm_num [conjTranspose_apply]
private lemma starZ (k) : (Z k)ᴴ = Z k := by
  unfold Z; rw [conjTranspose_kronecker,conjTranspose_one]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> norm_num [conjTranspose_apply]
private lemma starR (k) (x) : (R k x)ᴴ = R k (-x) := by
  have h : (J k)ᵀ = -(J k) := by simpa only [conjTranspose_eq_transpose_of_trivial] using starJ k
  simp [R,h]
private lemma normL (k) [NeZero k] (t) : ‖L k t‖ ≤ 1 := by
  have hs : (L k t)ᴴ = L k t := by
    rw [L,conjTranspose_mul,starZ,starR,Ranti _ (ZJ k), neg_neg]
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (L k t)
  rw [hs,Lsq,norm_one] at h
  nlinarith [norm_nonneg (L k t)]
private lemma Rcont (k) : Continuous (R k) := by unfold R;fun_prop
private lemma Lcont (k) : Continuous (L k) := by unfold L R;fun_prop
private lemma mode_mean {k} (n : ℕ) (hn : 0<n) (Q : M k) :
    (∫ t in (0:ℝ)..Real.pi, R k (n*(2*t)) * Q) = 0 := by
  let b := (n:ℝ)*2
  have hb : b ≠ 0 := by dsimp [b]; positivity
  have he : b * Real.pi = (n:ℝ)*(2*Real.pi) := by dsimp [b];ring
  have hzC : (∫ t in (0:ℝ)..Real.pi, Real.cos (b*t)) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left _ hb,integral_cos,he]; rw [show (n:ℝ)*(2*Real.pi) = ((2*n:ℕ):ℝ)*Real.pi by push_cast;ring, Real.sin_nat_mul_pi];simp
  have hzS : (∫ t in (0:ℝ)..Real.pi, Real.sin (b*t)) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left _ hb,integral_sin,he]; simp [Real.cos_nat_mul_two_pi]
  simp only [R,← mul_assoc,b,add_mul,smul_mul_assoc,one_mul]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable;fun_prop) (by apply Continuous.intervalIntegrable;fun_prop), intervalIntegral.integral_smul_const,intervalIntegral.integral_smul_const,hzC,hzS];simp

private def Bmat {k} (r : ℝ) (C : M k) (t : ℝ) : M k := ∑' n : ℕ, (r • (C * L k t)) ^ n
private lemma res_bound {k} [NeZero k] (r : ℝ) (hr : 0≤r) (C : M k) (hn : ‖C‖≤1) (t) :
    ‖r • (C * L k t)‖ ≤ r := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  calc
    _ ≤ r * (1*1) := mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (mul_le_mul hn (normL k t) (norm_nonneg _) zero_le_one)) hr
    _ = _ := by ring
private lemma resolvent_mean {k} [NeZero k] {r : ℝ} (hr : 0≤r) (hlt : r<1) (C : M k) (hn : ‖C‖ ≤ 1)
    (hc : C*J k = -(J k*C)) :
    (∫ t in (0:ℝ)..Real.pi, Bmat r C t) = Real.pi • 1 := by
  let F (n : ℕ) (t : ℝ) := (r • (C * L k t)) ^ n
  have hcont (n) : Continuous (F n) := by dsimp [F,L,R];fun_prop
  have hpow (n) (t) : ‖F n t‖ ≤ r^n := (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (res_bound r hr C hn t) _)
  have hsum := summable_geometric_of_lt_one hr hlt
  have hD : HasSum (fun n => ∫ t in (0:ℝ)..Real.pi, F n t) (∫ t in (0:ℝ)..Real.pi, Bmat r C t) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => r^n)
      (fun n => (hcont n).aestronglyMeasurable) (fun n => ae_of_all _ fun t _ => hpow n t)
      (ae_of_all _ fun _ _ => hsum) (intervalIntegrable_const)
    exact ae_of_all _ fun t _ => (summable_geometric_of_norm_lt_one ((res_bound r hr C hn t).trans_lt hlt)).hasSum
  have hz (n : ℕ) (hn' : n≠0) : (∫ t in (0:ℝ)..Real.pi, F n t) = 0 := by
    simp only [F,smul_pow,CLpow C hc]
    rw [intervalIntegral.integral_smul,mode_mean n (Nat.pos_of_ne_zero hn')];simp
  rw [← hD.tsum_eq,tsum_eq_single 0 hz]
  simp [F,intervalIntegral.integral_const]

private def lift2 (k) (A : Matrix (Fin 2) (Fin 2) ℝ) : M k := A ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
private lemma liftmul k (A B : Matrix (Fin 2) (Fin 2) ℝ) : lift2 k (A*B) = lift2 k A * lift2 k B := by simp [lift2, ← Matrix.mul_kronecker_mul]
private lemma liftadd k (A B : Matrix (Fin 2) (Fin 2) ℝ) : lift2 k (A+B) = lift2 k A + lift2 k B := by ext i j;simp [lift2,Matrix.kroneckerMap_apply,add_mul]
private lemma liftsmul k (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : lift2 k (r • A) = r • lift2 k A := by ext i j;simp [lift2,Matrix.kroneckerMap_apply,smul_eq_mul,mul_assoc]
private lemma liftone k : lift2 k 1 = 1 := Matrix.one_kronecker_one
private lemma liftrot k (t : ℝ) : R k (-t) = lift2 k (rot t) := by
  have he : rot t = Real.cos t • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin (-t) • !![0,1;-1,0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rot,smul_eq_mul]
  rw [he,liftadd,liftsmul,liftsmul,liftone];simp [R,J,Omega,lift2]
private lemma liftL k (t : ℝ) : L k t = lift2 k (rot t * !![1,0;0,-1] * (rot t)ᵀ) := by
  have he : rot t * !![1,0;0,-1] * (rot t)ᵀ = rot (2*t) * !![1,0;0,-1] := by
    ext i j;fin_cases i <;> fin_cases j
    all_goals simp [rot,Matrix.mul_apply,Fin.sum_univ_two,Real.cos_two_mul,Real.sin_two_mul]
    all_goals nlinarith [Real.sin_sq_add_cos_sq t]
  rw [he,L,liftrot,liftmul];rfl
private lemma vp (k) (l t : ℝ) : VsqK l t k = ((l+l⁻¹)/2) • (1:M k) + ((l-l⁻¹)/2) • L k t := by
  rw [liftL,← liftone k,← liftsmul,← liftsmul,← liftadd]
  change lift2 k _ = lift2 k _
  congr 1
  ext i j;fin_cases i <;> fin_cases j
  all_goals simp [Vsq,rot,Matrix.mul_apply,Fin.sum_univ_two,smul_eq_mul,vecMul,dotProduct]
  all_goals nlinarith [Real.sin_sq_add_cos_sq t,congrArg (fun x : ℝ => l*x) (Real.sin_sq_add_cos_sq t),congrArg (fun x : ℝ => l⁻¹*x) (Real.sin_sq_add_cos_sq t)]
private lemma vacc (k) (l t : ℝ) :
    ((2*(l-l⁻¹)) • (rot t * !![-1,0;0,1] * (rot t)ᵀ)) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ) =
    (-(2*(l-l⁻¹))) • L k t := by
  have he : (!![-1,0;0,1] : Matrix (Fin 2) (Fin 2) ℝ) = - !![1,0;0,-1] := by ext i j;fin_cases i <;> fin_cases j <;> norm_num
  rw [liftL, ← liftsmul,he,mul_neg,neg_mul,smul_neg,neg_smul];rfl
private lemma v_cayley (k) (l t : ℝ) (h : 1<l) :
    let r := (l-1)/(l+1)
    VsqK l t k * (1-r • L k t) = 1+r • L k t := by
  let r := (l-1)/(l+1)
  let a := (l+l⁻¹)/2
  let b := (l-l⁻¹)/2
  have h1 : a-r*b = 1  := by
    have h0 : l ≠ 0 := by linarith
    have h1 : l+1 ≠ 0 := by linarith
    dsimp [a,b,r];field_simp [h0,h1];ring
  have h2 : b-r*a = r  := by
    have h0 : l ≠ 0 := by linarith
    have h1 : l+1 ≠ 0 := by linarith
    dsimp [a,b,r];field_simp [h0,h1];ring
  change VsqK l t k * (1-r • L k t) = _
  rw [vp];change (a • 1 + b • L k t) * (1-r • L k t) = 1+r • L k t
  calc
    _ = (a-r*b) • (1 : M k)+(b-r*a) • L k t := by simp [sub_smul,sub_mul,mul_sub,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,Lsq,smul_smul,smul_add];module
    _ = _ := by rw [h1,h2,one_smul]

private lemma res_trace {k} [NeZero k] {r : ℝ} (hr : 0<r) (hlt : r<1) (W C V : M k) (t : ℝ)
    (hcN : ‖C‖ ≤ 1) (hcJ : C*J k = -(J k*C)) (hcW : (1-C)*W = 1+C)
    (hv : V * (1-r • L k t) = 1+r • L k t) :
    ((V+W)⁻¹ * L k t).trace = (2*(k:ℝ) - (1+r^2)*(Bmat r C t).trace)/(2*r) := by
  let L := L k t
  let B := Bmat r C t
  let X := r • (C*L)
  let G := 1-X
  let Q := 1-r • L
  let E := 1-C
  have hX : ‖X‖ < 1 := (res_bound r hr.le C hcN t).trans_lt hlt
  have hBG : B*G = 1 := geom_series_mul_neg X hX
  have hQ : IsUnit Q := by
    apply isUnit_one_sub_of_norm_lt_one
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (show r*‖L‖ ≤ r by simpa using mul_le_mul_of_nonneg_left (normL k t) hr.le).trans_lt hlt
  have hbase : E*(V+W)*Q = (2:ℝ) • G := by
    rw [mul_add,add_mul,mul_assoc,hv,show E*W = 1+C from hcW]
    dsimp only [E,Q,G,X]
    simp only [add_mul,sub_mul,mul_add,mul_sub,one_mul,mul_one,mul_smul_comm,smul_mul_assoc,smul_sub]
    module
  have hprod : Q*(B*E)*(V+W) = (2:ℝ) • (1:M k) := by
    apply hQ.mul_right_cancel
    calc
      _ = Q*(B*(E*(V+W)*Q)) := by simp [mul_assoc]
      _ = _ := by rw [hbase,mul_smul_comm,hBG,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  have hi : (V+W)⁻¹ = (1/2:ℝ) • (Q*(B*E)) := by
    apply Matrix.inv_eq_left_inv
    rw [smul_mul_assoc,hprod,smul_smul];norm_num
  have hLJ : L*J k = -(J k*L) := LJ k t
  have hcL : J k * (C*L) = C*L*J k := by
    rw [mul_assoc C L,hLJ,mul_neg,← mul_assoc C _ _,hcJ,neg_mul,neg_neg,mul_assoc]
  have hJX : Commute (J k) X := by dsimp [X,Commute,SemiconjBy];rw [mul_smul_comm,smul_mul_assoc,hcL]
  have hJB : J k*B = B*J k := Commute.tsum_right _ (fun n => hJX.pow_right n)
  have hAnt (Y : M k) (hY : Y*J k = -(J k*Y)) : (B*Y).trace = 0 := by
    apply anti_trace;rw [mul_assoc,hY,mul_neg,← mul_assoc,← hJB,mul_assoc]
  have hrel : r*(B*(C*L)).trace = B.trace-(2*(k:ℝ)) := by
    have h := congrArg Matrix.trace hBG
    dsimp only [G,X] at h
    simp only [mul_sub,mul_one,mul_smul_comm,trace_sub,trace_smul,smul_eq_mul,trace_one,Q, Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at h
    linarith
  have hLQ : L*Q = L-r • (1:M k) := by dsimp only [Q];rw [mul_sub,mul_one,mul_smul_comm,Lsq]
  have htr : ((Q*(B*E))*L).trace = (B*(E*(L*Q))).trace := by
    rw [Matrix.trace_mul_cycle,Matrix.trace_mul_comm (L*Q)];simp [mul_assoc]
  rw [hi,smul_mul_assoc,trace_smul,htr,hLQ]
  dsimp only [E]
  simp only [sub_mul,one_mul,mul_sub,mul_smul_comm,mul_one,trace_sub,trace_smul,smul_eq_mul,hAnt L hLJ,hAnt C hcJ]
  field_simp [hr.ne'];nlinarith [hrel]

end LogLogJam.PureProof

open LogLogJam.PureProof


theorem solution (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (hk : 1 ≤ k)
    (W : Matrix (Q k) (Q k) ℝ) (hpd : W.PosDef) (hs : W * Omega k * W = Omega k) :
    let D := fun θ => VsqK lam θ k + W
    let A := fun θ : ℝ => ((2*(lam-lam⁻¹)) • (rot θ * !![-1,0;0,1] * (rot θ)ᵀ)) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
    let I := ∫ θ in Set.Ico 0 Real.pi, ((D θ)⁻¹ * A θ).trace / 2
    I = k * Real.pi * (4 * energy lam - 2) := by
  let : NeZero k := ⟨by omega⟩
  let r := (lam-1)/(lam+1)
  let C := Cmat W
  have hr : 0<r := div_pos (by linarith) (by linarith)
  have hlt : r<1 := (div_lt_one (by linarith : 0<lam+1)).mpr (by linarith)
  obtain ⟨hN,hJ,hW,_⟩ := cayley_props W hpd hs
  let B := Bmat r C
  have hBcont : Continuous B := by
    let F := fun t => 1-r • (C*L k t)
    have hco : Continuous F := by dsimp [F,L,R];fun_prop
    have hunit (t) : IsUnit (F t) := isUnit_one_sub_of_norm_lt_one ((res_bound r hr.le C hN t).trans_lt hlt)
    have hinv : Continuous (fun t => (F t)⁻¹) := continuous_iff_continuousAt.mpr fun t =>
      (continuousAt_matrix_inv (A:= F t) (by simpa [Ring.inverse_eq_inv] using continuousAt_inv₀ ((isUnit_iff_isUnit_det _).mp (hunit t)).ne_zero)).comp hco.continuousAt
    convert hinv using 1
    funext t
    dsimp [B,Bmat,F]
    rw [geom_series_eq_inverse _ ((res_bound r hr.le C hN t).trans_lt hlt),Matrix.nonsing_inv_eq_ringInverse]
  let tr := (Matrix.traceLinearMap (Q k) ℝ ℝ).toContinuousLinearMap
  have htm := tr.intervalIntegral_comp_comm (hBcont.intervalIntegrable (μ := volume) (0:ℝ) Real.pi)
  have hMean := resolvent_mean hr.le hlt C hN hJ
  have htr : (∫ t in (0:ℝ)..Real.pi, (B t).trace) = Real.pi*(2*(k:ℝ)) := by
    change (∫ t in (0:ℝ)..Real.pi, tr (B t)) = _
    rw [htm,show (∫ t in (0:ℝ)..Real.pi, B t)=Real.pi • 1 from hMean,map_smul]
    simp [tr,Matrix.trace_one,LogLogJam.Q,smul_eq_mul]
  have point (t) := res_trace hr hlt W C (VsqK lam t k) t hN hJ hW (v_cayley k lam t hlam)
  let α := -(lam-lam⁻¹)*(2*(k:ℝ))/(2*r)
  let β := (lam-lam⁻¹)*(1+r^2)/(2*r)
  have hf (t) : ((VsqK lam t k +W)⁻¹ * (((2*(lam-lam⁻¹)) • (rot t * !![-1,0;0,1] * (rot t)ᵀ)) ⊗ₖ (1:Matrix (Fin k) (Fin k) ℝ))).trace/2 = α + β*(B t).trace := by
    rw [vacc,mul_smul_comm,trace_smul,smul_eq_mul,point]
    dsimp only [α,β,B];ring
  dsimp only
  simp_rw [hf]
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  have hbt : Continuous (fun t => (B t).trace) := tr.continuous.comp hBcont
  rw [intervalIntegral.integral_add (f:=fun _ : ℝ => α) (g:=fun t => β*(B t).trace) intervalIntegrable_const ((continuous_const.mul hbt).intervalIntegrable _ _), intervalIntegral.integral_const,intervalIntegral.integral_const_mul,htr,sub_zero,smul_eq_mul]
  have hlamNZ : lam ≠ 0 := by linarith
  have hlamNZp : lam+1 ≠ 0 := by linarith
  have hlamNZm : lam-1 ≠ 0 := by linarith
  dsimp [α,β,r,energy]
  field_simp [hlamNZ,hlamNZp,hlamNZm];ring



