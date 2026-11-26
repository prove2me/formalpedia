-- Prove2me | solution 1 for LogLogJam.Supplement.squeezed_trace_distance
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:26:25.823836+00:00
-- url     : https://prove2.me/submissions/455f60de-391e-4271-855e-32ab481fb43a

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Theorems.Thm_BosonicLearn_state_ext_characteristic
import Theorems.Thm_BosonicLearn_isDensity_of_posSemidef
import Theorems.Thm_LogLogJam_Supplement_squeezed_fock_realization
open Matrix LogLogJam LogLogJam.Supplement BosonicLearn Filter MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal Matrix Topology
set_option maxHeartbeats 350000
noncomputable section


/-! ### `ℓ²` basics -/

open Classical in
/-- The basis vector `e_i` of `ℓ²(I)`. -/
private def bv {I : Type} (i : I) : Hilbert I := lp.single 2 i (1 : ℂ)

private lemma bv_apply_self {I : Type} (i : I) : (bv i : Hilbert I) i = 1 := by
  classical
  unfold bv
  rw [lp.single_apply]
  simp

private lemma bv_apply_ne {I : Type} {i j : I} (h : j ≠ i) : (bv i : Hilbert I) j = 0 := by
  classical
  unfold bv
  rw [lp.single_apply]
  simp [h]

private lemma inner_bv_left {I : Type} (i : I) (x : Hilbert I) : inner ℂ (bv i) x = x i := by
  classical
  unfold bv
  rw [lp.inner_single_left]
  simp

private lemma inner_bv_right {I : Type} (i : I) (x : Hilbert I) :
    inner ℂ x (bv i) = star (x i) := by
  classical
  unfold bv
  rw [lp.inner_single_right]
  simp

private lemma norm_bv {I : Type} (i : I) : ‖(bv i : Hilbert I)‖ = 1 := by
  classical
  unfold bv
  rw [lp.norm_single (by norm_num)]
  simp

private lemma hasSum_bv {I : Type} (x : Hilbert I) : HasSum (fun i => x i • (bv i : Hilbert I)) x := by
  classical
  have h := lp.hasSum_single (p := 2) (E := fun _ : I => ℂ) (by norm_num) x
  refine h.congr_fun fun i => ?_
  unfold bv
  rw [← lp.single_smul, smul_eq_mul, mul_one]

/-- Coordinates of the image of a vector under a bounded operator. -/
private lemma clm_apply_hasSum {I : Type} (A : Hilbert I →L[ℂ] Hilbert I) (y : Hilbert I) (u : I) :
    HasSum (fun w => y w * (A (bv w)) u) ((A y) u) := by
  have h := ((innerSL ℂ (bv u)).comp A).hasSum (hasSum_bv y)
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_bv_left, map_smul,
    smul_eq_mul] at h
  exact h

/-- A bounded operator on `ℓ²` is determined by its matrix. -/
private lemma clm_ext {I : Type} {A B : Hilbert I →L[ℂ] Hilbert I}
    (h : ∀ v u, (A (bv v)) u = (B (bv v)) u) : A = B := by
  ext y u
  refine (clm_apply_hasSum A y u).unique ?_
  refine (clm_apply_hasSum B y u).congr_fun fun w => ?_
  rw [h]


/-- The matrix of a bounded operator. -/
private def matOf {I : Type} (A : Hilbert I →L[ℂ] Hilbert I) : Matrix I I ℂ :=
  fun u v => (A (bv v)) u

/-- `A = ∑ₖ |lₖ⟩⟨rₖ|` strongly, with `∑ₖ ‖lₖ‖‖rₖ‖ < ∞`. -/
private def IsNuc {I : Type} (A : Hilbert I →L[ℂ] Hilbert I) (l r : ℕ → Hilbert I) : Prop :=
  Summable (fun k => ‖l k‖ * ‖r k‖) ∧ ∀ x, HasSum (fun k => inner ℂ (r k) x • l k) (A x)

/-- The operator `∑ₖ |lₖ⟩⟨rₖ|`. -/
private def nucOp {I : Type} (l r : ℕ → Hilbert I) : Hilbert I →L[ℂ] Hilbert I :=
  ∑' k, (innerSL ℂ (r k)).smulRight (l k)

private lemma nucOp_isNuc {I : Type} (l r : ℕ → Hilbert I)
    (h : Summable (fun k => ‖l k‖ * ‖r k‖)) : IsNuc (nucOp l r) l r := by
  refine ⟨h, fun x => ?_⟩
  have hs : Summable (fun k => (innerSL ℂ (r k)).smulRight (l k)) := by
    refine Summable.of_norm ?_
    refine h.congr fun k => ?_
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]
  have h2 := (ContinuousLinearMap.apply ℂ (Hilbert I) x).hasSum hs.hasSum
  simpa [nucOp] using h2

private lemma isNuc_entry {I : Type} {A : Hilbert I →L[ℂ] Hilbert I} {l r : ℕ → Hilbert I}
    (h : IsNuc A l r) (u v : I) : HasSum (fun k => l k u * star (r k v)) (matOf A u v) := by
  have h2 := (innerSL ℂ (bv u)).hasSum (h.2 (bv v))
  simp only [innerSL_apply_apply, inner_bv_left, inner_bv_right, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul] at h2
  refine h2.congr_fun fun k => ?_
  ring

/-- The nuclear expansion of the matrix of a nuclear operator. -/
private def expOf {I : Type} {A : Hilbert I →L[ℂ] Hilbert I} {l r : ℕ → Hilbert I}
    (h : IsNuc A l r) : NuclearExpansion (matOf A) :=
  ⟨l, r, h.1, fun i j => (isNuc_entry h i j).tsum_eq.symm⟩

/-- A nuclear expansion of the matrix of an operator is a nuclear decomposition of the operator. -/
private lemma isNuc_of_exp {I : Type} (A : Hilbert I →L[ℂ] Hilbert I)
    (e : NuclearExpansion (matOf A)) : IsNuc A e.left e.right := by
  have h := nucOp_isNuc e.left e.right e.summable
  have hA : nucOp e.left e.right = A := by
    refine clm_ext fun v u => ?_
    have h1 := (isNuc_entry h u v).tsum_eq
    rw [← e.coefficients u v] at h1
    exact h1.symm
  rwa [hA] at h

private noncomputable def crossOp {I : Type} (p q : Hilbert I) (c : ℝ) : Hilbert I →L[ℂ] Hilbert I :=
  (c:ℂ) • ((innerSL ℂ p).smulRight q + (innerSL ℂ q).smulRight p)
private theorem offdiag_apply {I : Type} (p q v : Hilbert I) (c : ℝ) :
    crossOp p q c v = (c:ℂ) • (inner ℂ p v • q + inner ℂ q v • p) := rfl
private theorem cross_entry {I : Type} (p q : Hilbert I) (c : ℝ) (i j : I) :
    matOf (crossOp p q c) i j = (c:ℂ) * (p i * star (q j) + q i * star (p j)) := by
  rw [matOf,offdiag_apply,inner_bv_right,inner_bv_right]
  change (c:ℂ) * (star (p j)*q i + star (q j)*p i) = _
  ring

private theorem pair_squares {I : Type} (p q u : Hilbert I) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) : ‖inner ℂ p u‖ ^ 2 + ‖inner ℂ q u‖ ^ 2 ≤ ‖u‖^2 := by
  have hqp : inner ℂ q p = 0 := by rw [← inner_conj_symm, hpq]; simp
  let f : Fin 2 → Hilbert I := ![p,q]
  have hf : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]; intro i j;fin_cases i <;> fin_cases j <;>
      simp [f,hp,hq,hpq,hqp,inner_self_eq_norm_sq_to_K]
  simpa [f,Fin.sum_univ_two,← inner_conj_symm u] using (hf.sum_inner_products_le (s:=Finset.univ) u)

private theorem offdiag_bound {I : Type} (p q l r : Hilbert I) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : inner ℂ p q = 0) :
    ‖inner ℂ r q * inner ℂ p l + inner ℂ r p * inner ℂ q l‖ ≤ ‖l‖*‖r‖ := by
  have hl := pair_squares p q l hp hq hpq
  have hr := pair_squares p q r hp hq hpq
  calc _ ≤ ‖inner ℂ p l‖*‖inner ℂ r q‖ + ‖inner ℂ q l‖*‖inner ℂ r p‖ := by
          simpa [norm_mul,mul_comm] using norm_add_le (inner ℂ r q * inner ℂ p l) (inner ℂ r p * inner ℂ q l)
       _ ≤ Real.sqrt (‖inner ℂ p l‖^2+‖inner ℂ q l‖^2) * Real.sqrt (‖inner ℂ q r‖^2+‖inner ℂ p r‖^2) := by
          rw [norm_inner_symm r q,norm_inner_symm r p]
          have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 2))
            ![‖inner ℂ p l‖,‖inner ℂ q l‖] ![‖inner ℂ q r‖,‖inner ℂ p r‖]
          simpa [Fin.sum_univ_two] using h
       _ ≤ ‖l‖*‖r‖ := by
          rw [← Real.sqrt_sq (norm_nonneg l),← Real.sqrt_sq (norm_nonneg r)]
          apply mul_le_mul (Real.sqrt_le_sqrt hl) _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          apply Real.sqrt_le_sqrt
          linarith

private theorem cross_lower {I : Type} (p q : Hilbert I) (c : ℝ) (hc : 0 ≤ c)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : inner ℂ p q = 0) :
    ENNReal.ofReal (2*c) ≤ traceSize (matOf (crossOp p q c)) := by
  apply le_iInf; intro e
  have he := isNuc_of_exp _ e
  have hqp : inner ℂ q p = 0 := by rw [← inner_conj_symm,hpq];simp
  have h1 := (innerSL ℂ p).hasSum (he.2 q)
  have h2 := (innerSL ℂ q).hasSum (he.2 p)
  let f (i : ℕ) := inner ℂ (e.right i) q * inner ℂ p (e.left i) + inner ℂ (e.right i) p * inner ℂ q (e.left i)
  have hf : HasSum f ((2*c:ℝ):ℂ) := by
    simpa [f,innerSL_apply_apply,inner_smul_right,offdiag_apply,hpq,hqp,inner_self_eq_norm_sq_to_K,hp,hq,two_mul] using h1.add h2
  have hb (i) := offdiag_bound p q (e.left i) (e.right i) hp hq hpq
  have hs : Summable (fun i => ‖f i‖) := e.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  apply ENNReal.ofReal_le_ofReal
  calc 2*c = ‖((2*c:ℝ):ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
       _ = ‖∑' i, f i‖ := congrArg norm hf.tsum_eq.symm
       _ ≤ ∑' i, ‖f i‖ := norm_tsum_le_tsum_norm hs
       _ ≤ _ := hs.tsum_le_tsum hb e.summable

private theorem cross_upper {I : Type} (p q : Hilbert I) (c : ℝ) (hc : 0 ≤ c)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    traceSize (matOf (crossOp p q c)) ≤ ENNReal.ofReal (2*c) := by
  classical
  let l (i : ℕ) : Hilbert I := if i = 0 then (c:ℂ) • p else if i = 1 then (c:ℂ) • q else 0
  let r (i : ℕ) : Hilbert I := if i = 0 then q else if i = 1 then p else 0
  have zero (i : ℕ) (hi : i ∉ ({0,1} : Finset ℕ)) : l i = 0 := by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; simp [l,hi.1,hi.2]
  have ht : HasSum (fun i => ‖l i‖*‖r i‖) (2*c) := by
    have h : HasSum (fun i => ‖l i‖*‖r i‖) (∑ i ∈ ({0,1}:Finset ℕ), ‖l i‖*‖r i‖) := hasSum_sum_of_ne_finset_zero (s := {0,1}) (fun i hi => by rw [zero i hi,norm_zero,zero_mul] : ∀ i ∉ _, ‖l i‖*‖r i‖=0)
    have cp : ‖(c:ℂ) • p‖ = c := by rw [norm_smul,hp,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
    have cq : ‖(c:ℂ) • q‖ = c := by rw [norm_smul,hq,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
    simpa only [Finset.sum_insert (by decide : (0:ℕ) ∉ ({1}:Finset ℕ)),Finset.sum_singleton,l,r,if_true,if_pos rfl,if_neg (by decide : (1:ℕ) ≠ 0),cp,cq,hp,hq,mul_one,two_mul] using h
  let e : NuclearExpansion (matOf (crossOp p q c)) := {
    left := l, right := r, summable := ht.summable, coefficients := by
      intro i j
      rw [tsum_eq_sum (s:={0,1}) (fun k hk => by rw [zero k hk];simp)]
      simp [l,r,cross_entry]
      change _ = ((c:ℂ)*p i)*star (q j) + ((c:ℂ)*q i)*star (p j)
      simp only [Complex.star_def]; ring }
  exact (iInf_le (fun e : NuclearExpansion (matOf (crossOp p q c)) => ENNReal.ofReal (∑' k, ‖e.left k‖*‖e.right k‖)) e).trans_eq (congrArg ENNReal.ofReal ht.tsum_eq)
private def dmat {I : Type} (u : Hilbert I) : Matrix I I ℂ := fun i j => u i * star (u j)

private theorem nuclear_zero {I : Type} : traceSize (0 : Matrix I I ℂ) = 0 := by
  let e : NuclearExpansion (0 : Matrix I I ℂ) := ⟨fun _ => 0,fun _ => 0,by simp,fun _ _ => by simp⟩
  refine le_antisymm ((iInf_le _ e).trans ?_) bot_le
  simp [e]

private theorem aligned_dist {I : Type} (u v : Hilbert I) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) (huv : inner ℂ u v = (t:ℂ)) :
    traceDist (dmat u) (dmat v) = ENNReal.ofReal (Real.sqrt (1-t^2)) := by
  let a := ‖u+v‖
  let b := ‖u-v‖
  have ha : a^2 = 2+2*t := by rw [show a = _ from rfl,norm_add_sq (𝕜:=ℂ),hu,hv,huv]; simp; ring
  have hb : b^2 = 2-2*t := by rw [show b = _ from rfl,norm_sub_sq (𝕜:=ℂ),hu,hv,huv]; simp; ring
  have ha0 : 0 < a := by have := norm_nonneg (u+v); change 0 ≤ a at this; nlinarith
  by_cases hb0 : b = 0
  · have eqv : u = v := sub_eq_zero.mp (norm_eq_zero.mp hb0)
    have ht1 : t = 1 := by rw [hb0] at hb; linarith
    rw [eqv,ht1]; simp [traceDist,nuclear_zero]
  have hbpos : 0 < b := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb0)
  let p := ((a⁻¹:ℝ):ℂ) • (u+v)
  let q := ((b⁻¹:ℝ):ℂ) • (u-v)
  have hp : ‖p‖ = 1 := by change ‖((a⁻¹:ℝ):ℂ) • (u+v)‖=1; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha0)];exact inv_mul_cancel₀ ha0.ne'
  have hq : ‖q‖ = 1 := by change ‖((b⁻¹:ℝ):ℂ) • (u-v)‖=1; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hbpos)];exact inv_mul_cancel₀ hb0
  have hvu : inner ℂ v u = (t:ℂ) := by rw [← inner_conj_symm,huv];simp
  have hpq : inner ℂ p q = 0 := by
    simp [p,q,inner_smul_left,inner_smul_right,inner_add_left,inner_sub_right,inner_self_eq_norm_sq_to_K,hu,hv,huv,hvu,hb0,ha0.ne']; try ring <;> simp
  let c := a*b/2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hid : dmat u - dmat v = matOf (crossOp p q c) := by
    ext i j
    rw [cross_entry]; change u i * star (u j) - v i * star (v j) = _
    have pp (i : I) : p i = ((a⁻¹:ℝ):ℂ) * (u i+v i) := rfl
    have qq (i : I) : q i = ((b⁻¹:ℝ):ℂ) * (u i-v i) := rfl
    simp only [pp,qq,c,star_mul',star_add,star_sub,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_ofNat]
    simp only [map_inv₀,Complex.conj_ofReal]
    field_simp [Complex.ofReal_ne_zero.mpr ha0.ne',Complex.ofReal_ne_zero.mpr hb0]; ring
  have hs : Real.sqrt (1-t^2) = c := by
    rw [← Real.sqrt_sq hc]
    congr 1; symm
    calc c^2 = (a^2*b^2)/4 := by dsimp [c]; ring
         _ = 1-t^2 := by rw [ha,hb];ring
  rw [traceDist,hid,le_antisymm (cross_upper p q c hc hp hq) (cross_lower p q c hc hp hq hpq),hs]
  rw [← show ENNReal.ofReal 2 = 2 by norm_num,← ENNReal.ofReal_div_of_pos zero_lt_two]
  congr 1; ring

private theorem distance_of_pure {I : Type} (u v : Hilbert I) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    traceDist (dmat u) (dmat v) = ENNReal.ofReal (Real.sqrt (1-‖inner ℂ u v‖^2)) := by
  let w := inner ℂ u v
  let a := Complex.exp ((w.arg:ℂ)*Complex.I)
  have ha : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have ha0 : a ≠ 0 := Complex.exp_ne_zero _
  let v' := a⁻¹ • v
  have hv' : ‖v'‖ = 1 := by simp only [v',norm_smul,norm_inv,ha,hv,inv_one,mul_one]
  have hi : inner ℂ u v' = (‖w‖:ℂ) := by
    rw [show v' = _ from rfl,inner_smul_right];change a⁻¹*w=_
    conv_lhs => rw [show w = (‖w‖:ℂ) * a from (Complex.norm_mul_exp_arg_mul_I w).symm]
    field_simp
  have heq : dmat v' = dmat v := by
    have hphase : a⁻¹ * star (a⁻¹) = 1 := by rw [Complex.star_def,Complex.mul_conj',norm_inv,ha]; norm_num
    ext i j
    change (a⁻¹*v i)*star (a⁻¹*v j) = v i*star (v j)
    rw [star_mul',show a⁻¹*v i*(star (a⁻¹)*star (v j)) =
       (a⁻¹*star (a⁻¹))*(v i*star (v j)) by ring,hphase,one_mul]
  rw [← heq];exact aligned_dist u v' hu hv' ‖w‖ (norm_nonneg _) hi

private theorem middle_coef (n : ℕ) : Ring.multichoose (1/2:ℂ) n = (n.centralBinom : ℂ)/4^n := by
  induction n with
  | zero => simp [Nat.centralBinom, Ring.multichoose_zero_right]
  | succ n ih =>
    have ha := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1/2:ℂ) n
    have hb := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1/2:ℂ) (n+1)
    rw [ascPochhammer_succ_right,Polynomial.smeval_mul,Polynomial.smeval_add,Polynomial.smeval_X,← ha] at hb
    simp [nsmul_eq_mul,Nat.factorial_succ,ih] at hb
    have hnat : ((n:ℂ)+1) * ((n+1).centralBinom : ℂ) = 2*(2*(n:ℂ)+1)*(n.centralBinom:ℂ) := by exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hfac : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [pow_succ]
    have ev : (n : Polynomial ℕ).smeval (1/2:ℂ) = n := by rw [← Polynomial.C_eq_natCast,Polynomial.smeval_C]; simp
    field_simp at hb
    rw [ev,ih] at hb
    field_simp at hb
    apply (eq_div_iff (by norm_num)).mpr
    apply (mul_left_cancel₀ hn)
    linear_combination 2*hb - hnat

private theorem center_series (z : ℂ) (hz : ‖z‖ < 1) : HasSum (fun n : ℕ =>
    ((n.centralBinom:ℂ)/4^n) * z^n) (1/(1-z)^(1/2:ℂ)) := by
  have hb : z ∈ Metric.eball 0 1 := by simpa [Metric.mem_eball,edist_dist] using (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z)).mpr hz
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (1/2)).hasSum hb
  have H (n : ℕ) : Ring.choose ((1/2:ℂ) + n - 1) n = (n.centralBinom:ℂ)/4^n := by
    rw [Ring.choose,show (1/2:ℂ) + n - 1 - n + 1 = 1/2 by ring,middle_coef]
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,H,smul_eq_mul,zero_add] using h
@[irreducible] private noncomputable def wAmp (r θ : ℝ) (n : ℕ) : ℂ :=
  if Even n then ((Real.sqrt ((n/2).centralBinom : ℝ) / ((2:ℝ)^(n/2) * Real.sqrt (Real.cosh r)) : ℝ) : ℂ) *
    ((Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ) * Complex.I))^(n/2) else 0

private theorem sq_n (r θ : ℝ) (j : ℕ) : ‖wAmp r θ (2*j)‖^2 =
    1/Real.cosh r * ((j.centralBinom:ℝ)/4^j * (Real.tanh r ^ 2)^j) := by
  have c := (Real.cosh_pos r).le
  simp only [wAmp, even_two_mul, if_true, Nat.mul_div_cancel_left _ (by decide : 0<2),norm_mul,norm_pow,
    Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs, mul_pow, ← Nat.pow_mul, ← sq_abs,
    sq_abs, div_pow,Real.sq_sqrt c,Real.sq_sqrt (Nat.cast_nonneg _)]
  have h : |Real.tanh r| ^ (j*2) = Real.tanh r ^ (j*2) := by rw [Nat.mul_comm, pow_mul, sq_abs, ← pow_mul]
  ring_nf; rw [h, show ((2:ℝ)⁻¹)^(j*2) = (4⁻¹:ℝ)^j by rw [Nat.mul_comm, pow_mul]; norm_num]

private theorem tanh_gap (r : ℝ) : 1 - Real.tanh r ^2 = (Real.cosh r ^ 2)⁻¹ := by
  rw [Real.tanh_eq_sinh_div_cosh]; field_simp [(Real.cosh_pos r).ne']; nlinarith [Real.cosh_sq_sub_sinh_sq r]

private theorem center_sum_real (r : ℝ) : HasSum (fun j : ℕ => (j.centralBinom:ℝ)/4^j * (Real.tanh r ^ 2)^j) (Real.cosh r) := by
  let q := Real.tanh r ^ 2
  have hq : 0 ≤ q := sq_nonneg _
  have hlt : q < 1 := by have h := tanh_gap r; have h' := inv_pos.mpr (sq_pos_of_pos (Real.cosh_pos r)); unfold q; linarith
  have h := center_series (q:ℂ) (by simpa [abs_of_nonneg hq] using hlt)
  have he : 1 / (1 - (q:ℂ))^(1/2:ℂ) = (Real.cosh r : ℂ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow (sub_nonneg.mpr hlt.le)]
    change 1 / (( (1-q)^(1/2:ℝ) : ℝ) : ℂ) = _
    rw [← Real.sqrt_eq_rpow,show 1-q = _ from tanh_gap r, Real.sqrt_inv,Real.sqrt_sq (Real.cosh_pos r).le]
    simp
  rw [he] at h
  have hc := Complex.reCLM.hasSum h
  simpa only [← Complex.ofReal_natCast,← Complex.ofReal_ofNat,← Complex.ofReal_pow,← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.reCLM_apply,Complex.ofReal_re,q] using hc

private theorem amp_normalized (r θ : ℝ) : HasSum (fun n : ℕ => ‖wAmp r θ n‖^2) 1 := by
  have he : HasSum (fun j : ℕ => ‖wAmp r θ (2*j)‖^2) 1 := by
    simp_rw [sq_n]
    simpa [(Real.cosh_pos r).ne'] using (center_sum_real r).mul_left (1/Real.cosh r)
  have ho : HasSum (fun j : ℕ => ‖wAmp r θ (2*j+1)‖^2) 0 := by simpa [wAmp] using (hasSum_zero : HasSum (fun _ : ℕ => (0:ℝ)) 0)
  simpa using HasSum.even_add_odd (f:=fun n => ‖wAmp r θ n‖^2) he ho

private theorem rank_density {I : Type} [Countable I] (w : I → ℂ) (hn : HasSum (fun i => ‖w i‖^2) 1) :
    IsDensity (fun i j => w i * star (w j)) := by
  classical
  have d (i) : (w i * star (w i)).re = ‖w i‖^2 := by simp [Complex.mul_conj',← Complex.ofReal_pow]
  apply isDensity_of_posSemidef _ _ (by simpa only [d] using hn.summable) (by simpa only [d] using hn.tsum_eq)
  intro s z
  let v := ∑ i ∈ s, star (z i) * w i
  have he : (∑ i ∈ s, ∑ j ∈ s, star (z i) * (w i * star (w j)) * z j) = v * star v := by
    simp only [v,star_sum,star_mul',star_star,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  rw [he,Complex.star_def,Complex.mul_conj']; norm_cast; exact ⟨rfl,sq_nonneg _⟩


private theorem sum_over_fock {M : Type} [AddCommMonoid M] [TopologicalSpace M] {f : ℕ → M} {a : M}
    (h : HasSum f a) : HasSum (fun u : Fin 1 → ℕ => f (u 0)) a := by
  let e : ℕ ≃ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm
  exact (e.hasSum_iff (f := fun u : Fin 1 → ℕ => f (u 0))).mp h

private theorem state_of_amp (r θ : ℝ) : ∃ ρ : State (Occupation (Fin 1)),
    ∀ u v, ρ.coefficients u v = wAmp r θ (u 0) * star (wAmp r θ (v 0)) := by
  have h : HasSum (fun u : Fin 1 → ℕ => ‖wAmp r θ (u 0)‖^2) 1 := sum_over_fock (amp_normalized r θ)
  let v : (Fin 1 → ℕ) → ℂ := fun u => wAmp r θ (u 0)
  let X : Matrix (Fin 1 → ℕ) (Fin 1 → ℕ) ℂ := fun u j => v u * star (v j)
  have hd : IsDensity X := rank_density (I := (Fin 1 → ℕ)) v h
  let ρ : State (Fin 1 → ℕ) := ⟨X, hd⟩
  exact ⟨ρ,fun _ _ => rfl⟩
private noncomputable def sv (r θ : ℝ) : Hilbert (Occupation (Fin 1)) :=
  ⟨fun u => wAmp r θ (u 0),memℓp_gen (p:=2) (by simpa using (sum_over_fock (amp_normalized r θ)).summable)⟩
private theorem sv_norm (r θ : ℝ) : ‖sv r θ‖ = 1 := by
  have hn := lp.norm_rpow_eq_tsum (p:=2) (by norm_num) (sv r θ)
  have hs := (sum_over_fock (amp_normalized r θ)).tsum_eq
  change (∑' u : Fin 1 → ℕ, ‖sv r θ u‖^2) = 1 at hs
  have hn' : ‖sv r θ‖^2 = ∑' u, ‖sv r θ u‖^2 := by simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hn
  have : ‖sv r θ‖^2 = 1 := hn'.trans hs
  nlinarith [norm_nonneg (sv r θ)]

private noncomputable def zz (r θ : ℝ) : ℂ := (Real.tanh r:ℂ) * Complex.exp ((2*θ : ℝ)*Complex.I)
private theorem zz_lt (r θ : ℝ) : ‖zz r θ‖ < 1 := by
  simp only [zz,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact abs_lt.mpr ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩

private theorem wnormprod (r θ s φ : ℝ) (j : ℕ) :
    star (wAmp r θ (2*j)) * wAmp s φ (2*j) =
      ((((Real.sqrt (Real.cosh r) * Real.sqrt (Real.cosh s))⁻¹:ℝ):ℂ)) *
      ((j.centralBinom:ℂ)/4^j * (star (zz r θ) * zz s φ)^j) := by
  let k : ℂ := (Real.sqrt (j.centralBinom:ℝ):ℂ)
  have hk : k^2 = j.centralBinom := by dsimp [k]; norm_cast; exact Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [wAmp, even_two_mul, if_true, Nat.mul_div_cancel_left _ (by decide : 0<2),zz,star_mul',star_pow,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_ofNat,
    Complex.star_def,Complex.conj_ofReal,map_div₀,map_mul,map_pow,map_ofNat,mul_pow]
  rw [show (4:ℂ)^j = 2^j*2^j by rw [← mul_pow];norm_num]
  change (k / _ * _) * (k / _ * _) = _
  rw [← hk]
  ring

private theorem sinner (r θ s φ : ℝ) :
    inner ℂ (sv r θ) (sv s φ) =
      ((((Real.sqrt (Real.cosh r) * Real.sqrt (Real.cosh s))⁻¹:ℝ):ℂ)) *
       (1/(1-star (zz r θ)*zz s φ)^(1/2:ℂ)) := by
  let f (n : ℕ) := star (wAmp r θ n) * wAmp s φ n
  let k : ℂ := ((Real.sqrt (Real.cosh r) * Real.sqrt (Real.cosh s))⁻¹:ℝ)
  let z := star (zz r θ)*zz s φ
  have hz : ‖z‖ < 1 := by
    dsimp only [z];rw [norm_mul,norm_star]
    calc _ ≤ 1*‖zz s φ‖ := mul_le_mul_of_nonneg_right (zz_lt r θ).le (norm_nonneg _)
         _ < _ := by simpa using zz_lt s φ
  have he : HasSum (fun n : ℕ => f (2*n)) (k*(1/(1-z)^(1/2:ℂ))) := by
    simp only [f,wnormprod];exact (center_series z hz).mul_left k
  have ho : HasSum (fun n : ℕ => f (2*n+1)) 0 := by simp [f,wAmp]
  have h := HasSum.even_add_odd (f:=f) he ho
  rw [add_zero] at h
  rw [lp.inner_eq_tsum]
  simpa only [RCLike.inner_apply',sv,f,z,k,Complex.star_def] using (sum_over_fock h).tsum_eq

private theorem s_overlap (r θ s φ : ℝ) :
    ‖inner ℂ (sv r θ) (sv s φ)‖^2 =
      1/(Real.cosh r * Real.cosh s * ‖1-star (zz r θ)*zz s φ‖) := by
  rw [sinner,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,inv_pow,mul_pow,
    Real.sq_sqrt (Real.cosh_pos r).le,Real.sq_sqrt (Real.cosh_pos s).le,norm_div,norm_one,
    show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,Complex.norm_cpow_real,← Real.sqrt_eq_rpow,div_pow,Real.sq_sqrt (norm_nonneg _)]
  ring
private noncomputable def ch (r : ℝ) := Real.cosh r ^ 2 + Real.sinh r ^ 2
private noncomputable def sh (r : ℝ) := 2*Real.cosh r*Real.sinh r
private theorem chandsh (r : ℝ) : ch r^2-sh r^2 = 1 := by
  rw [show ch r^2-sh r^2 = (Real.cosh r^2-Real.sinh r^2)^2 by dsimp [ch,sh];ring,
    Real.cosh_sq_sub_sinh_sq];norm_num
private theorem rot_entries (r θ : ℝ) :
    Vsq (Real.exp (2*r)) θ =
    !![ch r+sh r*Real.cos (2*θ),sh r*Real.sin (2*θ);
       sh r*Real.sin (2*θ),ch r-sh r*Real.cos (2*θ)] := by
  have he : Real.exp (2*r) = (Real.cosh r+Real.sinh r)^2 := by rw [Real.cosh_add_sinh,two_mul,Real.exp_add];ring
  have hei : (Real.exp (2*r))⁻¹ = (Real.cosh r-Real.sinh r)^2 := by rw [Real.cosh_sub_sinh,← Real.exp_neg,← Real.exp_nat_mul]; congr 1; push_cast;ring
  unfold Vsq ch sh; rw [hei,he]
  generalize Real.cosh r = C
  generalize Real.sinh r = S
  ext i j;fin_cases i <;> fin_cases j <;> simp [rot,Matrix.mul_apply,Fin.sum_univ_two,Real.cos_two_mul',Real.sin_two_mul] <;> try ring
  all_goals linear_combination (C^2+S^2)*(Real.cos_sq_add_sin_sq θ)

private theorem det_expr (r θ s φ : ℝ) :
    (Vsq (Real.exp (2*r)) θ+Vsq (Real.exp (2*s)) φ).det =
     2+2*ch r*ch s-2*sh r*sh s*(Real.cos (2*θ)*Real.cos (2*φ)+Real.sin (2*θ)*Real.sin (2*φ)) := by
  rw [rot_entries,rot_entries,det_fin_two]
  simp only [Matrix.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.of_apply,Matrix.cons_val_fin_one]
  change (ch r+sh r*Real.cos (2*θ)+(ch s+sh s*Real.cos (2*φ)))*
    (ch r-sh r*Real.cos (2*θ)+(ch s-sh s*Real.cos (2*φ))) -
    (sh r*Real.sin (2*θ)+sh s*Real.sin (2*φ))*(sh r*Real.sin (2*θ)+sh s*Real.sin (2*φ)) = _
  linear_combination chandsh r + chandsh s - (sh r)^2*(Real.cos_sq_add_sin_sq (2*θ)) -
     (sh s)^2*(Real.cos_sq_add_sin_sq (2*φ))

private theorem pairang (r θ s φ : ℝ) : ‖1-star (zz r θ)*zz s φ‖^2 =
    1+(Real.tanh r)^2*(Real.tanh s)^2-2*Real.tanh r*Real.tanh s*
    (Real.cos (2*θ)*Real.cos (2*φ)+Real.sin (2*θ)*Real.sin (2*φ)) := by
  have nr (s φ : ℝ) : Complex.normSq (zz s φ) = Real.tanh s^2 := by
    rw [← Complex.sq_norm,zz,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [Complex.sq_norm,Complex.normSq_sub,Complex.normSq_one,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,nr,nr,one_mul,Complex.conj_re,Complex.mul_re]
  simp only [zz,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im];ring

private theorem det_disk (r θ s φ : ℝ) :
    (Vsq (Real.exp (2*r)) θ + Vsq (Real.exp (2*s)) φ).det =
      (2*Real.cosh r*Real.cosh s*‖1-star (zz r θ)*zz s φ‖)^2 := by
  rw [det_expr,mul_pow,pairang,Real.tanh_eq_sinh_div_cosh,Real.tanh_eq_sinh_div_cosh]
  let X := Real.cos (2*θ)*Real.cos (2*φ)+Real.sin (2*θ)*Real.sin (2*φ)
  have h (r s : ℝ) : 2+2*ch r*ch s = 4*(Real.cosh r^2*Real.cosh s^2+Real.sinh r^2*Real.sinh s^2) := by
    calc _ = 4*(Real.cosh r^2*Real.cosh s^2+Real.sinh r^2*Real.sinh s^2) +
        2*(1-(Real.cosh r^2-Real.sinh r^2)*(Real.cosh s^2-Real.sinh s^2)) := by dsimp [ch];ring
        _ = _ := by rw [Real.cosh_sq_sub_sinh_sq,Real.cosh_sq_sub_sinh_sq];ring
  rw [h];dsimp [sh]; field_simp [(Real.cosh_pos r).ne',(Real.cosh_pos s).ne'];ring

private theorem cov_fidelity (r θ s φ : ℝ) :
    1/(Real.cosh r*Real.cosh s*‖1-star (zz r θ)*zz s φ‖) =
      2/Real.sqrt (Vsq (Real.exp (2*r)) θ+Vsq (Real.exp (2*s)) φ).det := by
  rw [det_disk,Real.sqrt_sq (by positivity)]; ring

private theorem members (ρ : State (Occupation (Fin 1))) (r θ : ℝ) (hρ : squeezedAt ρ r θ) :
    ρ.coefficients = dmat (sv r θ) := by
  obtain ⟨σ,hσ,hs⟩ := squeezed_fock_realization r θ hρ.1
  have he := state_ext_characteristic ρ σ (fun ξ => (hρ.2.2 ξ).trans (hσ.2.2 ξ).symm)
  rw [he]
  ext i j; simpa only [sv,wAmp,dmat] using hs i j

theorem solution (ρ σ : State (Occupation (Fin 1))) (r θ s φ : ℝ)
    (hρ : squeezedAt ρ r θ) (hσ : squeezedAt σ s φ) :
    BosonicLearn.traceDist ρ.coefficients σ.coefficients = ENNReal.ofReal
      (Real.sqrt (1-2/Real.sqrt (Vsq (Real.exp (2*r)) θ + Vsq (Real.exp (2*s)) φ).det)) := by
  rw [members _ _ _ hρ,members _ _ _ hσ,distance_of_pure _ _ (sv_norm _ _) (sv_norm _ _), s_overlap, cov_fidelity]
end
