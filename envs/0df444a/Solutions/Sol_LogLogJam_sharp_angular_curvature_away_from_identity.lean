-- Prove2me | solution 1 for LogLogJam.sharp_angular_curvature_away_from_identity
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:14:42.378189+00:00
-- url     : https://prove2.me/submissions/8056d993-915d-4f75-90e1-2b9d73aef184

import Theorems.Thm_LogLogJam_pure_angular_curvature_integral
open Matrix MeasureTheory LogLogJam Filter
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.Operator ComplexOrder Kronecker Topology
set_option maxHeartbeats 1000000
private theorem omega_sq (k : ℕ) : Omega k * Omega k = -1 := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;-1,0]
  have e : M * M = -1 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [M, Matrix.mul_apply,Fin.sum_univ_two]
  change (M ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)) * (M ⊗ₖ 1) = _
  rw [← Matrix.mul_kronecker_mul, e,one_mul]
  ext ⟨i,a⟩ ⟨j,b⟩
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]; split_ifs <;> simp_all

private theorem omega_sym (k : ℕ) : (Omega k)ᵀ = -Omega k := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;> by_cases h : a=b <;> simp [Omega, Matrix.kroneckerMap_apply, h, Ne.symm]

private theorem omega_unit (k : ℕ) : IsUnit (Omega k) := by
  have h : IsUnit (Omega k * Omega k) := by rw [omega_sq]; exact isUnit_one.neg
  exact isUnit_of_mul_isUnit_left h

private theorem physical_pd (k : ℕ) (W : Matrix (Q k) (Q k) ℝ) (hW : IsCov k W) : W.PosDef := by
  let B := W.map Complex.ofReal + Complex.I • (Omega k).map Complex.ofReal
  have hB : B.PosSemidef := hW.2
  apply posDef_iff_dotProduct_mulVec.mpr
  refine ⟨by simpa [IsHermitian,conjTranspose_eq_transpose_of_trivial] using hW.1, ?_⟩
  intro v hv
  let z := fun i => (v i : ℂ)
  have hre : (star z ⬝ᵥ B *ᵥ z).re = star v ⬝ᵥ W *ᵥ v := by
    simp [B,z, dotProduct, Matrix.mulVec, Complex.mul_re,Complex.mul_im,Complex.re_sum]
  have hpos := Complex.nonneg_iff.mp (hB.dotProduct_mulVec_nonneg z)
  apply lt_of_le_of_ne (hre ▸ hpos.1)
  intro hz
  have hzC : star z ⬝ᵥ B *ᵥ z = 0 := Complex.ext (hre.trans hz.symm) hpos.2.symm
  have hker := (hB.dotProduct_mulVec_zero_iff z).mp hzC
  have hom : Omega k *ᵥ v = 0 := by
    funext i
    have hh := congrArg Complex.im (congrFun hker i)
    simpa [B,z,Matrix.mulVec,dotProduct,Complex.im_sum,Complex.mul_im,Complex.mul_re] using hh
  exact hv ((mulVec_injective_of_isUnit (omega_unit k)) (hom.trans (mulVec_zero _).symm))

private abbrev cx {n : Type} [Fintype n] [DecidableEq n] :
    Matrix n n ℝ →+* Matrix n n ℂ := Complex.ofRealHom.mapMatrix

private theorem cx_real_psd {n : Type} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ) (hV : V.IsHermitian) (h : (cx V).PosSemidef) : V.PosSemidef := by
  apply posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hV,fun v => ?_⟩
  have p := (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg (fun i => (v i : ℂ)))).1
  simpa [cx, dotProduct,Matrix.mulVec, Complex.mul_re,Complex.mul_im,Complex.re_sum] using p

private theorem cx_star {n : Type} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ) : (cx V)ᴴ = cx Vᵀ := by ext; simp [cx,conjTranspose_apply]

private theorem polar_contraction {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : Pᵀ = -P) (h : ((1: Matrix n n ℂ) + Complex.I • cx P).PosSemidef) :
    -P*P ≤ 1 := by
  let J := Complex.I • cx P
  have ht : ((1 : Matrix n n ℂ) + J)ᵀ = 1-J := by
    change ((1:Matrix n n ℂ) + Complex.I • (P.map Complex.ofReal))ᵀ = _
    rw [transpose_add, transpose_one, transpose_smul, ← Matrix.transpose_map, hP]
    ext i j; simp [J,cx,sub_eq_add_neg]
  have hm : ((1 : Matrix n n ℂ)-J).PosSemidef := ht ▸ h.transpose
  have hcomm : Commute (1+J) (1-J) := by unfold Commute SemiconjBy; noncomm_ring
  have hprod := Commute.mul_nonneg h.nonneg hm.nonneg hcomm
  have hmap : cx (1 - (-P*P)) = (1+J)*(1-J) := by
    simp only [map_sub,map_one,map_mul,map_neg,J,add_mul,mul_sub,mul_one,one_mul,
      Matrix.smul_mul,Matrix.mul_smul,smul_smul,Complex.I_mul_I, neg_smul, one_smul, neg_mul]; abel
  apply Matrix.le_iff.mpr
  apply cx_real_psd _ ?_ (hmap ▸ hprod.posSemidef)
  simp [IsHermitian,conjTranspose_eq_transpose_of_trivial,hP,Matrix.transpose_mul]

private theorem sqrt_le_id {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (ha : 0 ≤ A) (h : A ≤ 1) : CFC.sqrt A ≤ 1 := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt A ha]
  apply (cfc_le_one_iff (fun x : ℝ => ((NNReal.sqrt x.toNNReal : ℝ≥0) : ℝ)) A
    (by fun_prop) ha.posSemidef.isHermitian).mpr
  intro u hu
  have h' := (CFC.le_one_iff (R := ℝ) A ha.posSemidef.isHermitian).mp h u hu
  simpa only [Real.sqrt] using Real.sqrt_le_one.mpr h'

private theorem det_one_contraction {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (ha : A.PosDef) (h : A ≤ 1) (hd : A.det = 1) : A = 1 := by
  let vals := ha.isHermitian.eigenvalues
  have he (i) : vals i ≤ 1 := (CFC.le_one_iff (R:=ℝ) A ha.isHermitian).mp h _ (ha.isHermitian.eigenvalues_mem_spectrum_real i)
  have eq (i) : vals i = 1 := by
    by_contra hne
    have hp := Finset.prod_lt_prod (s:=Finset.univ) (g:=fun _ : n => (1:ℝ))
      (fun j _ => ha.eigenvalues_pos j) (fun j _ => he j) ⟨i,Finset.mem_univ i,lt_of_le_of_ne (he i) hne⟩
    rw [ha.isHermitian.det_eq_prod_eigenvalues] at hd
    simp at hp hd
    linarith
  calc
    _ = _ := ha.isHermitian.spectral_theorem
    _ = 1 := by simp [show ha.isHermitian.eigenvalues = fun _ => (1 : ℝ) from funext eq, diagonal_one]

private theorem polar_purify (k : ℕ) (W : Matrix (Q k) (Q k) ℝ) (hw : IsCov k W) :
    ∃ V : Matrix (Q k) (Q k) ℝ, V.PosDef ∧ V * Omega k * V = Omega k ∧
      V.det = 1 ∧ V ≤ W ∧ (W.det = 1 → W = V) := by
  have hW := physical_pd k W hw
  let C := CFC.sqrt W
  let F := C⁻¹
  let J := Omega k
  let P := F * J * F
  let Q' := C * J * C
  let R := CFC.sqrt (-P*P)
  have hcc : C*C = W := CFC.sqrt_mul_sqrt_self _ hW.posSemidef.nonneg
  have hcu : IsUnit C := isUnit_of_mul_isUnit_left (hcc ▸ hW.isUnit)
  have hcd : C.PosDef := (CFC.sqrt_nonneg W).posSemidef.posDef_iff_isUnit.mpr hcu
  have hcF : C*F = 1 := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hcu)
  have hFc : F*C = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hcu)
  have hft : Fᵀ=F := by simpa [conjTranspose_eq_transpose_of_trivial] using hcd.inv.isHermitian.eq
  have hpt : Pᵀ = -P := by simp [P,transpose_mul,hft, J,omega_sym,mul_assoc]
  have hpn : 0 ≤ -P*P := by
    have h := (posSemidef_conjTranspose_mul_self P).nonneg
    simpa [conjTranspose_eq_transpose_of_trivial,hpt] using h
  have hpu : IsUnit P := (hcd.inv.isUnit.mul (omega_unit k)).mul hcd.inv.isUnit
  have hr2 : R*R = -P*P := CFC.sqrt_mul_sqrt_self _ hpn
  have hru : IsUnit R := isUnit_of_mul_isUnit_left (hr2 ▸ (hpu.neg.mul hpu))
  have hrd : R.PosDef := (CFC.sqrt_nonneg _).posSemidef.posDef_iff_isUnit.mpr hru
  have hccx : (cx F)ᴴ = cx F := by rw [cx_star,hft]
  have hpush := hw.2.mul_mul_conjTranspose_same (cx F)
  have hfwf : F*W*F = 1 := by rw [← hcc, ← mul_assoc, hFc,one_mul,hcF]
  have hpushed : ((1 : Matrix (LogLogJam.Q k) (LogLogJam.Q k) ℂ)+Complex.I • cx P).PosSemidef := by
    change (cx F * (cx W + Complex.I • cx J) * (cx F)ᴴ).PosSemidef at hpush
    simpa only [hccx, mul_add, add_mul, Matrix.mul_smul,Matrix.smul_mul,
      ← map_mul, hfwf, map_one,P] using hpush
  have hrle := sqrt_le_id hpn (polar_contraction P hpt hpushed)
  have hq : P*Q' = -1 := by
    calc
      _ = F*J*(F*C)*J*C := by simp only [P,Q',mul_assoc]
      _ = F*(J*J)*C := by rw [hFc]; simp [mul_assoc]
      _ = _ := by rw [show J*J=-1 from omega_sq k]; simp [hFc]
  have hq' : Q'*P = -1 := by
    calc
      _ = C*J*(C*F)*J*F := by simp only [P,Q',mul_assoc]
      _ = C*(J*J)*F := by rw [hcF]; simp [mul_assoc]
      _ = _ := by rw [show J*J=-1 from omega_sq k]; simp [hcF]
  have hcom : Commute P Q' := hq.trans hq'.symm
  have hcom' : Commute (-P*P) Q' := hcom.neg_left.mul_left hcom
  have hRcomm : Commute R Q' := by
    dsimp only [R]; rw [CFC.sqrt_eq_cfc]; exact hcom'.cfc_nnreal _
  have hcore : R*Q'*R=P := by
    calc
      _ = Q'*(R*R) := (congrArg (· * R) hRcomm.eq).trans (mul_assoc _ _ _)
      _ = -(Q'*P)*P := by rw [hr2]; noncomm_ring
      _ = _ := by rw [hq']; simp
  let V := C*R*C
  have hvc : V.PosDef := by simpa only [V,hcd.isHermitian.eq] using hrd.mul_mul_conjTranspose_same (vecMul_injective_of_isUnit hcu)
  have hsym : V*J*V=J := by
    calc
      _ = C*(R*Q'*R)*C := by simp only [V,Q',mul_assoc]
      _ = (C*F)*J*(F*C) := by simp only [hcore,P,mul_assoc]
      _ = _ := by rw [hcF,hFc,one_mul,mul_one]
  have hdet : V.det=1 := by
    have h := congrArg Matrix.det hsym
    simp only [Matrix.det_mul] at h
    have hj := ((isUnit_iff_isUnit_det _).mp (omega_unit k)).ne_zero
    have h2 : V.det*V.det=1 := by apply mul_right_cancel₀ hj; simpa [mul_comm,mul_left_comm,mul_assoc] using h
    nlinarith [hvc.det_pos]
  have hle : V ≤ W := by
    apply Matrix.le_iff.mpr
    have hrle' : R ≤ 1 := hrle
    have h := (Matrix.le_iff.mp hrle').mul_mul_conjTranspose_same C
    simpa only [V,hcd.isHermitian.eq,mul_sub,sub_mul,hcc,mul_one] using h
  refine ⟨V,hvc,hsym,hdet,hle, fun he => ?_⟩
  have hdprod : V.det = W.det * R.det := by
    dsimp [V]; rw [← hcc]; simp [Matrix.det_mul]; ring
  have heR : R.det=1 := by simpa [he,hdet] using hdprod.symm
  rw [show V=C*R*C from rfl, det_one_contraction hrd hrle heR,mul_one,hcc]
private theorem inv_antitone_real {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℝ}
    (ha : A.PosDef) (hb : B.PosDef) (hab : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  let X := A⁻¹
  let Y := B⁻¹
  have hXa : X*A = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp ha.isUnit)
  have haX : A*X = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp ha.isUnit)
  have hYb : Y*B = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hb.isUnit)
  have hs : (X-Y)ᴴ=X-Y := by rw [conjTranspose_sub,ha.inv.isHermitian.eq,hb.inv.isHermitian.eq]
  have h1 := ha.posSemidef.mul_mul_conjTranspose_same (X-Y)
  have h2 := (Matrix.le_iff.mp hab).mul_mul_conjTranspose_same Y
  rw [hs] at h1
  rw [hb.inv.isHermitian.eq] at h2
  apply Matrix.le_iff.mpr
  have id : (X-Y)*A*(X-Y)+Y*(B-A)*Y=X-Y := by
    calc
      _ = X*A*X-X*A*Y-Y*(A*X)+Y*A*Y+Y*B*Y-Y*A*Y := by noncomm_ring
      _ = X-Y := by rw [hXa, haX, hYb]; simp; abel
  rw [←id]; exact h1.add h2

private theorem strict_trace_product {n : Type} [Fintype n] [DecidableEq n] {E B : Matrix n n ℝ}
    (hE : E.PosSemidef) (hne : E ≠ 0) (hB : B.PosDef) : 0 < (E*B).trace := by
  let C := CFC.sqrt B
  have hcc : C*C=B := CFC.sqrt_mul_sqrt_self _ hB.posSemidef.nonneg
  have hC := (CFC.sqrt_nonneg B).posSemidef.isHermitian
  have hc : IsUnit C := isUnit_of_mul_isUnit_left (hcc ▸ hB.isUnit)
  have hp := hE.mul_mul_conjTranspose_same C
  rw [hC.eq] at hp
  have hn : C*E*C ≠ 0 := by
    intro h
    have h' : C*E*C = (C*0)*C := by simpa using h
    exact hne (hc.mul_left_cancel (hc.mul_right_cancel h'))
  have pos := lt_of_le_of_ne hp.trace_nonneg (fun h => hn (hp.trace_eq_zero_iff.mp h.symm))
  have id : (E*B).trace = (C*E*C).trace := by rw [←hcc, ← mul_assoc,trace_mul_cycle]
  rw [id]; exact pos

private theorem strict_fisher_trace {n : Type} [Fintype n] [DecidableEq n] {A B H : Matrix n n ℝ}
    (ha : A.PosDef) (hb : B.PosDef) (hab : A ≤ B) (hne : A ≠ B)
    (hH : H.IsHermitian) (hHu : IsUnit H) :
    ((B⁻¹*H)*(B⁻¹*H)).trace < ((A⁻¹*H)*(A⁻¹*H)).trace := by
  let X := A⁻¹
  let Y := B⁻¹
  have he : (X-Y).PosSemidef := Matrix.le_iff.mp (inv_antitone_real ha hb hab)
  have hne' : X-Y ≠ 0 := by
    intro e
    apply hne
    have hi := congrArg Inv.inv (sub_eq_zero.mp e)
    simpa only [X,Y,nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp ha.isUnit),
      nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hb.isUnit)] using hi
  have hp : (H * (X+Y) * H).PosDef := by
    simpa only [hH.eq] using (ha.inv.add hb.inv).mul_mul_conjTranspose_same (vecMul_injective_of_isUnit hHu)
  have hs := strict_trace_product he hne' hp
  have id : ((X-Y)*(H*(X+Y)*H)).trace = ((X*H)*(X*H)).trace - ((Y*H)*(Y*H)).trace := by
    have e : (X-Y)*(H*(X+Y)*H) = (X*H)*(X*H) + (X*H)*(Y*H) - (Y*H)*(X*H) - (Y*H)*(Y*H) := by noncomm_ring
    rw [e,trace_sub,trace_sub,trace_add,trace_mul_comm (X*H) (Y*H)]; abel
  simpa only [id,sub_pos] using hs
private theorem curveInverse {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ℝ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (θ : ℝ)
    (hu : IsUnit (D θ)) (hd : ∀ i j, HasDerivAt (fun t => D t i j) (H i j) θ) :
    ∀ i j, HasDerivAt (fun t => (D t)⁻¹ i j) ((-(D θ)⁻¹ * H * (D θ)⁻¹) i j) θ := by
  have h : HasDerivAt D H θ := hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hd i))
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  rw [hu.unit_spec] at hi
  have hi' := hi.comp_hasDerivAt θ h
  intro i j
  have hv := hasDerivAt_pi.mp (hasDerivAt_pi.mp hi' i) j
  simpa only [Function.comp_def, _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    coe_units_inv, hu.unit_spec, nonsing_inv_eq_ringInverse, neg_mul] using hv

open scoped Matrix.Norms.Operator in
private theorem periodic_trace_energy {n : Type} [Fintype n] [DecidableEq n]
    (D H A : ℝ → Matrix n n ℝ)
    (hd : ∀ t i j, HasDerivAt (fun s => D s i j) (H t i j) t)
    (hh : ∀ t i j, HasDerivAt (fun s => H s i j) (A t i j) t)
    (hu : ∀ t, IsUnit (D t)) (hc : Continuous A)
    (hD : D Real.pi = D 0) (hH : H Real.pi = H 0) :
    (∫ t in Set.Ico 0 Real.pi, (((D t)⁻¹ * H t) * ((D t)⁻¹ * H t)).trace / 2) =
      ∫ t in Set.Ico 0 Real.pi, ((D t)⁻¹ * A t).trace / 2 := by
  let I := fun t => (D t)⁻¹
  have di (t : ℝ) : HasDerivAt I (-I t * H t * I t) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr (curveInverse D (H t) t (hu t) (hd t) i)
  have dh (t : ℝ) : HasDerivAt H (A t) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr (hh t i)
  let L := fun t => ((I t * H t) * (I t * H t)).trace / 2
  let R := fun t => (I t * A t).trace / 2
  have ci : Continuous I := continuous_iff_continuousAt.mpr fun t => (di t).continuousAt
  have ch : Continuous H := continuous_iff_continuousAt.mpr fun t => (dh t).continuousAt
  have cl : Continuous L := ((ci.mul ch).mul (ci.mul ch)).matrix_trace.div_const 2
  have cr : Continuous R := (ci.mul hc).matrix_trace.div_const 2
  have derivTrace (t : ℝ) : HasDerivAt (fun s => (I s * H s).trace / 2) (R t - L t) t := by
    have dp := (di t).mul (dh t)
    have dtr : HasDerivAt (fun s => (I s * H s).trace)
        (((-I t * H t * I t) * H t + I t * A t).trace) t := by
      apply HasDerivAt.fun_sum
      intro i _
      exact hasDerivAt_pi.mp (hasDerivAt_pi.mp dp i) i
    have e : R t - L t = (((-I t * H t * I t) * H t + I t * A t).trace / 2) := by
      simp only [R, L, Matrix.trace_add, neg_mul, Matrix.trace_neg, mul_assoc]
      ring
    rw [e]
    exact dtr.div_const 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := Real.pi)
    (fun t _ => derivTrace t) ((cr.sub cl).intervalIntegrable _ _)
  change (∫ t in (0 : ℝ)..Real.pi, R t - L t) =
    (((D Real.pi)⁻¹ * H Real.pi).trace / 2) - (((D 0)⁻¹ * H 0).trace / 2) at h
  rw [intervalIntegral.integral_sub (cr.intervalIntegrable _ _) (cl.intervalIntegrable _ _),
    hD, hH, sub_self, sub_eq_zero] at h
  change (∫ t in Set.Ico 0 Real.pi, L t) = ∫ t in Set.Ico 0 Real.pi, R t
  simpa only [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ico_eq_integral_Ioc] using h.symm

private theorem inputPos (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ)
    : (VsqK lam θ k).PosDef := by
  have hrot : (rot θ).det = 1 := by
    simp [rot, det_fin_two, ← sq, Real.cos_sq_add_sin_sq]
  have hU : IsUnit (rot θ) := (isUnit_iff_isUnit_det _).mpr (by simp [hrot])
  have hdiag : (diagonal ![lam, lam⁻¹]).PosDef := by
    apply PosDef.diagonal
    intro i
    fin_cases i <;> simp <;> positivity
  have hV : (Vsq lam θ).PosDef := by
    have h := hdiag.mul_mul_conjTranspose_same (B := rot θ)
      (vecMul_injective_of_isUnit hU)
    have heq : diagonal ![lam, lam⁻¹] = !![lam,0;0,lam⁻¹] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    simpa [Vsq, heq, conjTranspose_eq_transpose_of_trivial] using h
  exact hV.kronecker (PosDef.one : (1 : Matrix (Fin k) (Fin k) ℝ).PosDef)

private noncomputable def velocity (lam θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (lam-lam⁻¹) • (rot θ * !![0,1;1,0] * (rot θ)ᵀ)

private theorem velocity_deriv (lam θ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => Vsq lam t i j) (velocity lam θ i j) θ := by
  fin_cases i <;> fin_cases j
  all_goals
    simp [Vsq, velocity, rot, vecMul, dotProduct, Fin.sum_univ_two]
    apply HasDerivAt.congr_deriv (f := _) (f' := deriv _ θ)
    · apply DifferentiableAt.hasDerivAt
      fun_prop
    · simp (disch := fun_prop) [deriv_fun_mul, deriv_fun_add]
      ring

private noncomputable def accel (l θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (2*(l-l⁻¹)) • (rot θ * !![-1,0;0,1] * (rot θ)ᵀ)
private theorem acc_deriv (l θ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => velocity l t i j) (accel l θ i j) θ := by
  fin_cases i <;> fin_cases j
  all_goals
    simp [velocity,accel,rot,vecMul,dotProduct,Fin.sum_univ_two]
    apply HasDerivAt.congr_deriv (f := _) (f' := deriv _ θ)
    · apply DifferentiableAt.hasDerivAt; fun_prop
    · simp (disch := fun_prop) [deriv_fun_mul, deriv_fun_add]; ring

private theorem velocityUnit (lam t : ℝ) (hl : 1 < lam) : IsUnit (velocity lam t) := by
  have hrot : (rot t).det = 1 := by simp [rot,det_fin_two, ← sq,Real.cos_sq_add_sin_sq]
  have hp : lam⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0<lam)).2 hl
  have hn : lam-lam⁻¹ ≠ 0 := by linarith
  apply (isUnit_iff_isUnit_det _).2
  simp [velocity,Matrix.det_mul,Matrix.det_transpose,hrot,hn,Matrix.det_fin_two]

private theorem curvature_equal (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (W : Matrix (Q k) (Q k) ℝ)
    (hW : W.PosDef) :
    let D := fun θ => VsqK lam θ k + W
    let H := fun θ => velocity lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
    let A := fun θ => accel lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
    (∫ t in Set.Ico 0 Real.pi, (((D t)⁻¹ * H t) * ((D t)⁻¹ * H t)).trace / 2) =
      ∫ t in Set.Ico 0 Real.pi, ((D t)⁻¹ * A t).trace / 2 := by
  let D := fun θ => VsqK lam θ k + W
  let H := fun θ => velocity lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
  let A := fun θ => accel lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
  have hd (t) (i j : Q k) : HasDerivAt (fun s => D s i j) (H t i j) t :=
    ((velocity_deriv lam t i.1 j.1).mul_const ((1 : Matrix (Fin k) (Fin k) ℝ) i.2 j.2)).add_const _
  have hh (t) (i j : Q k) : HasDerivAt (fun s => H s i j) (A t i j) t :=
    (acc_deriv lam t i.1 j.1).mul_const ((1 : Matrix (Fin k) (Fin k) ℝ) i.2 j.2)
  have hc : Continuous A := by
    apply continuous_pi; rintro ⟨i,a⟩; apply continuous_pi; rintro ⟨j,b⟩
    fin_cases i <;> fin_cases j <;> simp [A,accel,rot,Matrix.kroneckerMap_apply] <;> fun_prop
  have hD : D Real.pi = D 0 := by
    ext ⟨i,a⟩ ⟨j,b⟩; fin_cases i <;> fin_cases j <;> simp [D,VsqK,Vsq,rot,Matrix.kroneckerMap_apply,vecMul,dotProduct,Fin.sum_univ_two]
  have hH : H Real.pi = H 0 := by
    ext ⟨i,a⟩ ⟨j,b⟩; fin_cases i <;> fin_cases j <;> simp [H,velocity,rot,Matrix.kroneckerMap_apply,vecMul,dotProduct,Fin.sum_univ_two]

  exact periodic_trace_energy D H A hd hh (fun t => ((inputPos lam t hlam k).add hW).isUnit) hc hD hH

theorem solution (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (hk : 1 ≤ k)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) (hother : Matrix.of W ≠ 1) :
    let D := fun θ => VsqK lam θ k + Matrix.of W
    let A := fun θ : ℝ => ((2*(lam-lam⁻¹)) • (rot θ * !![-1,0;0,1] * (rot θ)ᵀ)) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
    let I := ∫ θ in Set.Ico 0 Real.pi, ((D θ)⁻¹ * A θ).trace / 2
    I ≤ k * Real.pi * (4 * energy lam - 2) ∧
      (I = k * Real.pi * (4 * energy lam - 2) ↔ (Matrix.of W).det = 1) := by
  obtain ⟨V,hV,hsym,hdet,hle,heq⟩ := polar_purify k (Matrix.of W) hW
  let D := fun (S : Matrix (Q k) (Q k) ℝ) t => VsqK lam t k + S
  let H := fun θ => velocity lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
  let A := fun θ => accel lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
  let F := fun S (t : ℝ) => (((D S t)⁻¹ * H t) * ((D S t)⁻¹ * H t)).trace / 2
  let I := fun S => ∫ t in Set.Ico 0 Real.pi, F S t
  let B : ℝ := k * Real.pi * (4*energy lam-2)
  let R := fun S => ∫ t in Set.Ico 0 Real.pi, ((D S t)⁻¹ * A t).trace /2
  have hreal (S : Matrix (Q k) (Q k) ℝ) (hS : S.PosDef) : I S = R S :=
    curvature_equal lam hlam k S hS
  have hsharp : R V = B := pure_angular_curvature_integral lam hlam k hk V hV hsym
  change R (Matrix.of W) ≤ B ∧ (R (Matrix.of W) = B ↔ (Matrix.of W).det = 1)
  by_cases hwv : Matrix.of W = V
  · simpa only [hwv,hsharp,hdet] using (show B ≤ B ∧ (B = B ↔ (1:ℝ) = 1) by simp)
  have hWpd := physical_pd k (Matrix.of W) hW
  have hinput t := inputPos lam t hlam k
  have hHh (t : ℝ) : (H t).IsHermitian := by
    apply IsHermitian.ext; rintro ⟨i,a⟩ ⟨j,b⟩
    fin_cases i <;> fin_cases j <;> by_cases e : a=b <;> simp [H,velocity,rot,vecMul,dotProduct,Fin.sum_univ_two,kroneckerMap_apply,e,Ne.symm] <;> ring <;> simp
  have hHu t : IsUnit (H t) := (velocityUnit lam t hlam).kronecker isUnit_one
  have hpoint (t) : F (Matrix.of W) t < F V t := by
    apply div_lt_div_of_pos_right _ (by norm_num)
    apply strict_fisher_trace ((hinput t).add hV) ((hinput t).add hWpd) (add_le_add_right hle _)
    · exact fun e => hwv (add_left_cancel e).symm
    · exact hHh t
    · exact hHu t
  have hcD (S : Matrix (Q k) (Q k) ℝ) : Continuous (D S) := by
    apply continuous_pi; rintro ⟨i,a⟩; apply continuous_pi; rintro ⟨j,b⟩
    fin_cases i <;> fin_cases j <;> simp [D,VsqK,Vsq,rot,Matrix.kroneckerMap_apply] <;> fun_prop
  have hcH : Continuous H := by
    apply continuous_pi; rintro ⟨i,a⟩; apply continuous_pi; rintro ⟨j,b⟩
    fin_cases i <;> fin_cases j <;> simp [H,velocity,rot,Matrix.kroneckerMap_apply] <;> fun_prop
  have hcF (S : Matrix (Q k) (Q k) ℝ) (hS : S.PosDef) : Continuous (F S) := by
    have hi : Continuous (fun t => (D S t)⁻¹) := continuous_iff_continuousAt.mpr fun t =>
      (continuousAt_matrix_inv (A := D S t) (by simpa [Ring.inverse_eq_inv] using (continuousAt_inv₀ ((hinput t).add hS).det_pos.ne'))).comp (hcD S).continuousAt
    exact (((hi.mul hcH).mul (hi.mul hcH)).matrix_trace).div_const _
  have hlt : I (Matrix.of W) < I V := by
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt Real.pi_pos
      (hcF _ hWpd).continuousOn (hcF _ hV).continuousOn (fun x _ => (hpoint x).le)
      ⟨0,⟨le_rfl,Real.pi_pos.le⟩,hpoint 0⟩
    simpa only [I,intervalIntegral.integral_of_le Real.pi_pos.le,integral_Ico_eq_integral_Ioc] using h
  rw [hreal _ hWpd, hreal V hV, hsharp] at hlt
  exact ⟨hlt.le, ⟨fun h => (hlt.ne h).elim,fun h => (hwv (heq h)).elim⟩⟩
