-- Prove2me | solution 1 for KhachiyanRound.BCD.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T07:55:14.883241+00:00
-- url     : https://prove2.me/submissions/5d19cc81-8c3e-472a-a2d8-71592f687530

-- Complete checked reconstruction of the native Khachiyan barycentric rounding theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_KhachiyanRound_BCD_Setting
import Mathlib


-- Begin Canonical

open scoped Pointwise
namespace KhachiyanRound.BCD.Proof
end KhachiyanRound.BCD.Proof
-- End Canonical

-- Begin MomentBasic

namespace KhachiyanRound.BCD.Proof
open Matrix
variable {ι : Type*} [Fintype ι] {d : ℕ}

lemma moment_apply (a : ι → Fin d → ℝ) (p : ι → ℝ) (i j : Fin d) :
    momentMatrix a p i j = ∑ k, p k * a k i * a k j := by
  simp only [momentMatrix,Matrix.sum_apply,Matrix.smul_apply,vecMulVec_apply,smul_eq_mul]
  simp only [mul_assoc]

lemma moment_quadratic (a : ι → Fin d → ℝ) (p : ι → ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (momentMatrix a p) *ᵥ x = ∑ k, p k * (x ⬝ᵥ a k)^2 := by
  simp only [momentMatrix,sum_mulVec,dotProduct_sum,smul_mulVec,
    vecMulVec_mulVec,dotProduct_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [dotProduct_comm (a k) x]
  simp only [op_smul_eq_smul,smul_eq_mul]
  ring

lemma moment_psd (a : ι → Fin d → ℝ) (p : ι → ℝ) (hp : ∀j,0≤p j) :
    (momentMatrix a p).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j _
  have h : (vecMulVec (a j) (a j)).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (a j)
  exact h.smul (hp j)

lemma moment_pd_of_positive (a : ι → Fin d → ℝ) (p : ι → ℝ) (hp : ∀j,0<p j)
    (hspan : ∀u : Fin d → ℝ, u≠0 → ∃j,u ⬝ᵥ a j ≠ 0) :
    (momentMatrix a p).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (moment_psd a p (fun j => (hp j).le)).isHermitian
  intro u hu
  simp only [star_trivial]
  rw [moment_quadratic]
  obtain ⟨j,hj⟩ := hspan u hu
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hp i).le (sq_nonneg _))
    ⟨j,Finset.mem_univ j,mul_pos (hp j) (sq_pos_of_ne_zero hj)⟩

lemma moment_add (a : ι → Fin d → ℝ) (p q : ι → ℝ) :
    momentMatrix a (p+q) = momentMatrix a p + momentMatrix a q := by
  simp [momentMatrix,add_smul,Finset.sum_add_distrib]

lemma moment_smul (a : ι → Fin d → ℝ) (p : ι → ℝ) (t : ℝ) :
    momentMatrix a (t•p) = t • momentMatrix a p := by
  simp [momentMatrix,smul_smul,Finset.smul_sum]

lemma moment_single [DecidableEq ι] (a : ι → Fin d → ℝ) (j : ι) :
    momentMatrix a (Pi.single j 1) = vecMulVec (a j) (a j) := by
  classical
  simp [momentMatrix,Pi.single_apply]

lemma leverage_nonneg (a : ι → Fin d → ℝ) (p : ι → ℝ)
    (hA : (momentMatrix a p).PosDef) (j : ι) : 0 ≤ w a p j := by
  simpa only [w,star_trivial] using hA.inv.posSemidef.dotProduct_mulVec_nonneg (a j)

lemma weighted_leverage (a : ι → Fin d → ℝ) (p : ι → ℝ)
    (hA : (momentMatrix a p).PosDef) : ∑ j, p j * w a p j = (d:ℝ) := by
  have hh := congrArg Matrix.trace (Matrix.nonsing_inv_mul (momentMatrix a p) (isUnit_iff_ne_zero.mpr hA.det_pos.ne'))
  change Matrix.trace ((momentMatrix a p)⁻¹ * (∑ j, p j • vecMulVec (a j) (a j))) = _ at hh
  rw [Matrix.mul_sum,Matrix.trace_sum] at hh
  simpa only [mul_smul_comm,mul_vecMulVec,Matrix.trace_smul,Matrix.trace_vecMulVec,
    smul_eq_mul,w, dotProduct_comm,Matrix.trace_one,Fintype.card_fin,Nat.cast_id] using hh

end KhachiyanRound.BCD.Proof
-- End MomentBasic

-- Begin LeverageBasic

namespace KhachiyanRound.BCD.Proof
open Matrix
variable {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ}

lemma eps_eq_max (a : ι → Fin d → ℝ) (p : ι → ℝ) (r : ι)
    (hr : ∀j,w a p j ≤ w a p r) : epsOf a p = w a p r / (d:ℝ) - 1 := by
  unfold epsOf
  congr 2
  exact le_antisymm (ciSup_le hr) (le_ciSup (Set.finite_range _).bddAbove r)

omit [Nonempty ι] in
lemma leverage_max_ge (a : ι → Fin d → ℝ) (p : ι → ℝ)
    (hp : p ∈ stdSimplex ℝ ι) (hA : (momentMatrix a p).PosDef) (r : ι)
    (hr : ∀j,w a p j ≤ w a p r) : (d:ℝ) ≤ w a p r := by
  calc
    (d:ℝ) = ∑ j,p j*w a p j := (weighted_leverage a p hA).symm
    _ ≤ ∑ j,p j*w a p r := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hr j) (hp.1 j)
    _ = w a p r := by rw [← Finset.sum_mul,hp.2,one_mul]

lemma eps_nonneg (a : ι → Fin d → ℝ) (p : ι → ℝ)
    (hp : p ∈ stdSimplex ℝ ι) (hA : (momentMatrix a p).PosDef) (hd : 0<d)
    (r : ι) (hr : ∀j,w a p j ≤ w a p r) : 0 ≤ epsOf a p := by
  rw [eps_eq_max a p r hr]
  have h := leverage_max_ge a p hp hA r hr
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  exact sub_nonneg.mpr ((le_div_iff₀ hd').mpr (by simpa using h))

lemma step_fraction_bounds (d k : ℝ) (hd : 2≤d) (hk : d≤k) :
    0 ≤ (k/d-1)/(k-1) ∧ (k/d-1)/(k-1) < 1 := by
  have hd0 : 0<d := by linarith
  have hk0 : 0<k-1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr ((le_div_iff₀ hd0).mpr (by linarith))) hk0.le
  · apply (div_lt_iff₀ hk0).mpr
    have hh : k/d < k := (div_lt_iff₀ hd0).mpr (by nlinarith)
    linarith

lemma uniform_simplex : (fun _ : ι => 1/(Fintype.card ι:ℝ)) ∈ stdSimplex ℝ ι := by
  refine ⟨fun _ => by positivity,?_⟩
  simp [ne_of_gt (Fintype.card_pos : 0<Fintype.card ι)]

lemma uniform_moment_pd (a : ι → Fin d → ℝ)
    (hspan : ∀u : Fin d → ℝ,u≠0 → ∃j,u ⬝ᵥ a j ≠0) :
    (momentMatrix a (fun _ => 1/(Fintype.card ι:ℝ))).PosDef := by
  apply moment_pd_of_positive a _ (fun _ => by positivity) hspan

omit [Nonempty ι] in
lemma moment_step [DecidableEq ι] (a : ι → Fin d → ℝ) (p : ι → ℝ) (r : ι) (t : ℝ) :
    momentMatrix a ((1-t)•p+t•Pi.single r 1) =
      (1-t)•momentMatrix a p+t•vecMulVec (a r) (a r) := by
  rw [moment_add,moment_smul,moment_smul,moment_single]

omit [Nonempty ι] in
lemma simplex_pd_step [DecidableEq ι] (a : ι → Fin d → ℝ) (p : ι → ℝ)
    (hp : p ∈ stdSimplex ℝ ι) (hA : (momentMatrix a p).PosDef)
    (r : ι) (t : ℝ) (ht0 : 0≤t) (ht1 : t<1) :
    ((1-t)•p+t•Pi.single r 1) ∈ stdSimplex ℝ ι ∧
      (momentMatrix a ((1-t)•p+t•Pi.single r 1)).PosDef := by
  constructor
  · exact convex_stdSimplex ℝ ι hp (single_mem_stdSimplex ℝ r)
      (sub_nonneg.mpr ht1.le) ht0 (by ring)
  · rw [moment_step]
    have hr : (vecMulVec (a r) (a r)).PosSemidef := by
      simpa only [star_trivial] using posSemidef_vecMulVec_self_star (a r)
    exact (hA.smul (sub_pos.mpr ht1)).add_posSemidef (hr.smul ht0)

end KhachiyanRound.BCD.Proof
-- End LeverageBasic

-- Begin RunValidity

namespace KhachiyanRound.BCD.Proof
open Matrix
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {d : ℕ}

lemma bcd_valid (a : ι → Fin d → ℝ) (hd : 2≤d)
    (hspan : ∀u : Fin d → ℝ,u≠0 → ∃j,u ⬝ᵥ a j ≠0)
    (p : ℕ → ι → ℝ) (hrun : IsBCDRun a p) :
    ∀k, p k ∈ stdSimplex ℝ ι ∧ (momentMatrix a (p k)).PosDef := by
  intro k
  induction k with
  | zero => rw [hrun.1]; exact ⟨uniform_simplex,uniform_moment_pd a hspan⟩
  | succ k ih =>
    obtain ⟨r,hr,he⟩ := hrun.2 k
    rw [he]
    have hmax := leverage_max_ge a (p k) ih.1 ih.2 r hr
    have hbounds := step_fraction_bounds (d:ℝ) (w a (p k) r) (by exact_mod_cast hd) hmax
    rw [← eps_eq_max a (p k) r hr] at hbounds
    exact simplex_pd_step a (p k) ih.1 ih.2 r _ hbounds.1 hbounds.2

lemma bcd_eps_nonneg (a : ι → Fin d → ℝ) (hd : 2≤d)
    (hspan : ∀u : Fin d → ℝ,u≠0 → ∃j,u ⬝ᵥ a j ≠0)
    (p : ℕ → ι → ℝ) (hrun : IsBCDRun a p) (k : ℕ) : 0≤epsOf a (p k) := by
  obtain ⟨r,hr,_⟩ := hrun.2 k
  have h := bcd_valid a hd hspan p hrun k
  exact eps_nonneg a (p k) h.1 h.2 (by omega) r hr

omit [DecidableEq ι] in
lemma uniform_eps_bound (a : ι → Fin d → ℝ) (hd : 0<d)
    (hspan : ∀u : Fin d → ℝ,u≠0 → ∃j,u ⬝ᵥ a j ≠0) :
    epsOf a (fun _ => 1/(Fintype.card ι:ℝ)) ≤ (Fintype.card ι:ℝ)-1 := by
  let p : ι → ℝ := fun _ => 1/(Fintype.card ι:ℝ)
  have hA := uniform_moment_pd a hspan
  have hs := weighted_leverage a p hA
  have hm : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hh (j : ι) : w a p j ≤ (Fintype.card ι:ℝ)*(d:ℝ) := by
    have hterm := Finset.single_le_sum
      (fun i (_ : i ∈ Finset.univ) => mul_nonneg (show 0≤p i by dsimp [p]; positivity)
        (leverage_nonneg a p hA i)) (Finset.mem_univ j)
    rw [hs] at hterm
    dsimp [p] at hterm ⊢
    have hdiv : w a (fun _ => 1/(Fintype.card ι:ℝ)) j / (Fintype.card ι:ℝ) ≤ (d:ℝ) := by
      simpa only [one_div,div_eq_inv_mul,mul_one] using hterm
    simpa only [mul_comm] using (div_le_iff₀ hm).mp hdiv
  change (⨆ j,w a p j)/(d:ℝ)-1 ≤ _
  have hsle := ciSup_le hh
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hdiv : (⨆j,w a p j)/(d:ℝ) ≤ (Fintype.card ι:ℝ) :=
    (div_le_iff₀ hd').mpr (by simpa only [mul_comm] using hsle)
  linarith

omit [Nonempty ι] [DecidableEq ι] in
lemma relaxed_of_eps_le (a : ι → Fin d → ℝ) (p : ι → ℝ) (hd : 0<d)
    {eta : ℝ} (he : epsOf a p ≤ eta) : IsRelaxedOpt a p eta := by
  intro j
  have hj : w a p j ≤ ⨆j,w a p j := le_ciSup (Set.finite_range _).bddAbove j
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hb : (⨆j,w a p j)/(d:ℝ) ≤ 1+eta := by unfold epsOf at he; linarith
  exact hj.trans ((div_le_iff₀ hd').mp hb)

end KhachiyanRound.BCD.Proof
-- End RunValidity

-- Begin LogDetTrace

namespace KhachiyanRound.BCD.Proof
open Matrix
variable {d : ℕ}

lemma logdet_le_of_trace_le (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    (K : ℝ) (hK : 0<K) (htrace : A.trace ≤ (d:ℝ)*K) :
    Real.log A.det ≤ (d:ℝ)*Real.log K := by
  let v := hA.isHermitian.eigenvalues
  have hv (i : Fin d) : 0<v i := hA.eigenvalues_pos i
  have hi (i : Fin d) : Real.log (v i) ≤ Real.log K + v i/K-1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos (hv i) hK)
    rw [Real.log_div (hv i).ne' hK.ne'] at h
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have ht : ∑ i,v i ≤ (d:ℝ)*K := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues] at htrace
    exact htrace
  have ht' : (∑ i,v i)/K ≤ (d:ℝ) := (div_le_iff₀ hK).mpr ht
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  change Real.log (∏ i,v i) ≤ _
  rw [Real.log_prod (fun i _ => (hv i).ne')]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  rw [← Finset.sum_div] at hs
  linarith

lemma pd_of_psd_det_pos (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (hd : 0<A.det) : A.PosDef :=
  hA.posDef_iff_det_ne_zero.mpr hd.ne'

end KhachiyanRound.BCD.Proof
-- End LogDetTrace

-- Begin LogDetComparison

namespace KhachiyanRound.BCD.Proof
open Matrix
open scoped MatrixOrder
variable {d : ℕ}

lemma logdet_comparison (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (K : ℝ) (hK : 0<K)
    (ht : (A⁻¹*B).trace ≤ (d:ℝ)*K) :
    Real.log B.det - Real.log A.det ≤ (d:ℝ)*Real.log K := by
  let R := CFC.sqrt A⁻¹
  have hR : R.PosSemidef := (CFC.sqrt_nonneg A⁻¹).posSemidef
  have hRR : R*R=A⁻¹ := by
    have h := CFC.sq_sqrt A⁻¹ (ha := hA.inv.posSemidef.nonneg)
    simpa only [pow_two] using h
  let C := R*B*R
  have hC : C.PosSemidef := by
    have h := hB.posSemidef.conjTranspose_mul_mul_same R
    simpa only [hR.isHermitian.eq] using h
  have hdet : C.det = B.det / A.det := by
    have hh := congrArg Matrix.det hRR
    simp only [Matrix.det_mul] at hh
    dsimp [C]
    rw [Matrix.det_mul,Matrix.det_mul]
    calc
      R.det * B.det * R.det = B.det * (R.det*R.det) := by ring
      _ = B.det * A⁻¹.det := by rw [hh]
      _ = B.det / A.det := by rw [Matrix.det_nonsing_inv]; simp [div_eq_mul_inv]
  have hCp : C.PosDef := pd_of_psd_det_pos C hC (by rw [hdet]; exact div_pos hB.det_pos hA.det_pos)
  have htr : C.trace = (A⁻¹*B).trace := by
    dsimp [C]
    rw [Matrix.trace_mul_cycle,hRR]
  have h := logdet_le_of_trace_le C hCp K hK (by rwa [htr])
  rwa [hdet,Real.log_div hB.det_pos.ne' hA.det_pos.ne'] at h

end KhachiyanRound.BCD.Proof
-- End LogDetComparison

-- Begin DetOptimum

namespace KhachiyanRound.BCD.Proof
open Matrix
variable {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ}

omit [Nonempty ι] in
lemma continuous_moment (a : ι → Fin d → ℝ) : Continuous (momentMatrix a) := by
  unfold momentMatrix
  fun_prop

lemma det_optimum (a : ι → Fin d → ℝ)
    (hspan : ∀u : Fin d → ℝ,u≠0 → ∃j,u ⬝ᵥ a j ≠0) :
    ∃ q ∈ stdSimplex ℝ ι, (momentMatrix a q).PosDef ∧
      ∀p∈stdSimplex ℝ ι,(momentMatrix a p).det ≤ (momentMatrix a q).det := by
  have hc : Continuous (fun p => (momentMatrix a p).det) :=
    (continuous_moment a).matrix_det
  obtain ⟨q,hq,hmax⟩ := (isCompact_stdSimplex (𝕜 := ℝ) (ι := ι)).exists_isMaxOn
    ⟨_,uniform_simplex⟩ hc.continuousOn
  refine ⟨q,hq,?_,hmax⟩
  apply pd_of_psd_det_pos _ (moment_psd a q hq.1)
  exact (uniform_moment_pd a hspan).det_pos.trans_le (hmax uniform_simplex)

omit [Nonempty ι] in
lemma trace_inv_moment (a : ι → Fin d → ℝ) (p q : ι → ℝ) :
    ((momentMatrix a p)⁻¹ * momentMatrix a q).trace = ∑j,q j*w a p j := by
  change Matrix.trace ((momentMatrix a p)⁻¹ * (∑j,q j•vecMulVec (a j) (a j))) = _
  rw [Matrix.mul_sum,Matrix.trace_sum]
  simp only [mul_smul_comm,mul_vecMulVec,Matrix.trace_smul,Matrix.trace_vecMulVec,
    smul_eq_mul,w,dotProduct_comm]

omit [Nonempty ι] in
lemma objective_gap (a : ι → Fin d → ℝ) (p q : ι → ℝ)
    (hp : (momentMatrix a p).PosDef) (hq : (momentMatrix a q).PosDef)
    (hqs : q ∈ stdSimplex ℝ ι) (hd : 0<d)
    (he : 0≤epsOf a p) : F a q-F a p ≤ (d:ℝ)*Real.log (1+epsOf a p) := by
  apply logdet_comparison _ _ hp hq _ (by linarith)
  rw [trace_inv_moment]
  have hs : (⨆j,w a p j) = (1+epsOf a p)*(d:ℝ) := by
    unfold epsOf
    have hn : (d:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp
    ring
  calc
    (∑j,q j*w a p j) ≤ ∑j,q j*((1+epsOf a p)*(d:ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hqs.1 j)
      rw [← hs]
      exact le_ciSup (Set.finite_range _).bddAbove j
    _ = (d:ℝ)*(1+epsOf a p) := by rw [← Finset.sum_mul,hqs.2]; ring

end KhachiyanRound.BCD.Proof
-- End DetOptimum

-- Begin RankOneDet

namespace KhachiyanRound.BCD.Proof
open Matrix
variable {d : ℕ}

lemma det_add_rank_one (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (u : Fin d → ℝ) (t : ℝ) :
    (A+t•vecMulVec u u).det = A.det*(1+t*(u ⬝ᵥ A⁻¹ *ᵥ u)) := by
  have h := Matrix.det_add_replicateCol_mul_replicateRow (ι := Unit) hA (t•u) u
  simp only [← vecMulVec_eq,smul_vecMulVec] at h
  rw [h]
  congr 2
  simp only [Matrix.det_unique,Matrix.add_apply,Matrix.one_apply_eq,
    Matrix.mul_apply,Matrix.replicateRow_apply,Matrix.replicateCol_apply,
    Pi.smul_apply,smul_eq_mul]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


lemma update_det (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (u : Fin d → ℝ) (t : ℝ) (ht : t<1) :
    ((1-t)•A+t•vecMulVec u u).det =
      (1-t)^d * A.det * (1+t/(1-t)*(u ⬝ᵥ A⁻¹ *ᵥ u)) := by
  have hn : 1-t≠0 := (sub_pos.mpr ht).ne'
  have he : (1-t)•A+t•vecMulVec u u = (1-t)•(A+(t/(1-t))•vecMulVec u u) := by
    rw [smul_add,smul_smul]
    congr 1
    field_simp
  rw [he,Matrix.det_smul,det_add_rank_one A hA]
  simp only [Fintype.card_fin]
  ring

lemma update_logdet (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    (u : Fin d → ℝ) (t : ℝ) (ht0 : 0≤t) (ht1 : t<1) :
    Real.log ((1-t)•A+t•vecMulVec u u).det =
      Real.log A.det + (d:ℝ)*Real.log (1-t) +
        Real.log (1+t/(1-t)*(u ⬝ᵥ A⁻¹ *ᵥ u)) := by
  have hh : 0≤u ⬝ᵥ A⁻¹ *ᵥ u := by
    simpa only [star_trivial] using hA.inv.posSemidef.dotProduct_mulVec_nonneg u
  have ht : 0<1-t := sub_pos.mpr ht1
  have hp : 0<1+t/(1-t)*(u ⬝ᵥ A⁻¹ *ᵥ u) := by positivity
  rw [update_det A (isUnit_iff_ne_zero.mpr hA.det_pos.ne') u t ht1,
    Real.log_mul (mul_ne_zero (pow_ne_zero _ ht.ne') hA.det_pos.ne') hp.ne',
    Real.log_mul (pow_ne_zero _ ht.ne') hA.det_pos.ne',Real.log_pow]
  ring

end KhachiyanRound.BCD.Proof
-- End RankOneDet

-- Begin NumericRun

namespace KhachiyanRound.BCD.Proof

noncomputable def gain (e : ℝ) : ℝ := Real.log (1 + e) - e / (1 + e)

structure NumericRun (d M : ℝ) (eps D : ℕ → ℝ) : Prop where
  dim_ge : 2 ≤ d
  size_ge : 4 ≤ M
  eps_nonneg : ∀ k, 0 ≤ eps k
  gap_nonneg : ∀ k, 0 ≤ D k
  gap_le : ∀ k, D k ≤ d * Real.log (1 + eps k)
  initial_le : D 0 ≤ d * Real.log M
  step_le : ∀ k, D (k + 1) ≤ D k - gain (eps k)

end KhachiyanRound.BCD.Proof
-- End NumericRun

-- Begin UpdateGain

namespace KhachiyanRound.BCD.Proof
open Matrix

lemma scalar_update_gain (d e : ℝ) (hd : 2≤d) (he : 0≤e) :
    let t := e/(d*(1+e)-1)
    gain e ≤ d*Real.log (1-t) + Real.log (1+t/(1-t)*(d*(1+e))) := by
  dsimp
  let t := e/(d*(1+e)-1)
  have hd0 : 0<d := by linarith
  have hd1 : 0<d-1 := by linarith
  have he1 : 0<1+e := by linarith
  have hk : 0<d*(1+e)-1 := by nlinarith
  have ht1 : t<1 := (div_lt_iff₀ hk).mpr (by nlinarith)
  have ht : 0<1-t := sub_pos.mpr ht1
  have hratio : 1+t/(1-t)*(d*(1+e)) = (1+e)/(1-t) := by
    have hn : d*(1+e)-1-e ≠ 0 := by nlinarith
    dsimp [t]
    field_simp [hk.ne', hn, hd1.ne', he1.ne']
    ring
  have hinv : (1-t)⁻¹ = 1+e/((d-1)*(1+e)) := by
    have hn : d*(1+e)-1-e ≠ 0 := by nlinarith
    dsimp [t]
    field_simp [hk.ne', hn, hd1.ne', he1.ne']
    ring
  have hlog : Real.log (1-t) = -Real.log (1+e/((d-1)*(1+e))) := by
    rw [← hinv,Real.log_inv,neg_neg]
  have hv : 0<1+e/((d-1)*(1+e)) := by positivity
  have hbound := Real.log_le_sub_one_of_pos hv
  have hmul := mul_le_mul_of_nonneg_left hbound hd1.le
  have halg : (d-1)*(1+e/((d-1)*(1+e))-1)=e/(1+e) := by
    field_simp
    ring
  rw [halg] at hmul
  change gain e ≤ d*Real.log (1-t)+Real.log (1+t/(1-t)*(d*(1+e)))
  rw [hratio,Real.log_div he1.ne' ht.ne',hlog]
  unfold gain
  nlinarith

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {d : ℕ}

lemma bcd_gain (a : ι → Fin d → ℝ) (hd : 2≤d)
    (hspan : ∀u : Fin d → ℝ,u≠0 → ∃j,u ⬝ᵥ a j ≠0)
    (p : ℕ → ι → ℝ) (hrun : IsBCDRun a p) (k : ℕ) :
    gain (epsOf a (p k)) ≤ F a (p (k+1))-F a (p k) := by
  obtain ⟨r,hr,hstep⟩ := hrun.2 k
  have hvalid := bcd_valid a hd hspan p hrun k
  have he := bcd_eps_nonneg a hd hspan p hrun k
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  have hk : w a (p k) r = (d:ℝ)*(1+epsOf a (p k)) := by
    rw [eps_eq_max a (p k) r hr]
    have hn : (d:ℝ)≠0 := by positivity
    field_simp
    ring
  have ht := step_fraction_bounds (d:ℝ) (w a (p k) r) hd'
    (leverage_max_ge a (p k) hvalid.1 hvalid.2 r hr)
  rw [← eps_eq_max a (p k) r hr] at ht
  have hlog := update_logdet (momentMatrix a (p k)) hvalid.2 (a r)
    (epsOf a (p k)/(w a (p k) r-1)) ht.1 ht.2
  have hgain := scalar_update_gain (d:ℝ) (epsOf a (p k)) hd' he
  rw [hstep]
  unfold F
  rw [moment_step,hlog]
  dsimp only [w] at hk
  simp only [w] at *
  rw [hk]
  linarith

end KhachiyanRound.BCD.Proof
-- End UpdateGain

-- Begin RunNumeric

namespace KhachiyanRound.BCD.Proof
open Matrix
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {d : ℕ}

lemma bcd_numeric (a : ι → Fin d → ℝ) (hd : 2≤d)
    (hM : 4≤Fintype.card ι)
    (hspan : ∀u : Fin d → ℝ,u≠0 → ∃j,u ⬝ᵥ a j ≠0)
    (p : ℕ → ι → ℝ) (hrun : IsBCDRun a p) :
    ∃D : ℕ → ℝ, NumericRun (d:ℝ) (Fintype.card ι:ℝ) (fun k=>epsOf a (p k)) D := by
  obtain ⟨q,hq,hqpd,hmax⟩ := det_optimum a hspan
  let D := fun k=>F a q-F a (p k)
  have hv := bcd_valid a hd hspan p hrun
  have he := bcd_eps_nonneg a hd hspan p hrun
  have hd0 : 0<d := by omega
  have hgap : ∀k,D k≤(d:ℝ)*Real.log (1+epsOf a (p k)) :=
    fun k=>objective_gap a (p k) q (hv k).2 hqpd hq hd0 (he k)
  refine ⟨D, ⟨by exact_mod_cast hd,by exact_mod_cast hM,he,?_,hgap,?_,?_⟩⟩
  · intro k
    exact sub_nonneg.mpr (Real.log_le_log (hv k).2.det_pos (hmax _ (hv k).1))
  · apply (hgap 0).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    apply Real.log_le_log (by linarith [he 0])
    have hu := uniform_eps_bound a hd0 hspan
    rw [hrun.1]
    linarith
  · intro k
    have h:=bcd_gain a hd hspan p hrun k
    dsimp [D]
    linarith

end KhachiyanRound.BCD.Proof
-- End RunNumeric

-- Begin LiftNondegenerate

namespace KhachiyanRound.BCD.Proof
open Matrix

lemma affine_card_bound {m n : ℕ} (a : Fin m → Fin n → ℝ)
    (ha : affineSpan ℝ (Set.range a)=⊤) : n + 1 ≤ m :=  by
  obtain ⟨_,j,_⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top ℝ (Fin n→ℝ) (Fin n→ℝ) ha
  let : Nonempty (Fin m) := ⟨j⟩
  have h := finrank_vectorSpan_range_add_one_le ℝ a
  rw [AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ (Fin n→ℝ) (Fin n→ℝ) ha] at h
  simpa using h

lemma lift_nondegenerate {m n : ℕ} (a : Fin m → Fin n → ℝ)
    (ha : affineSpan ℝ (Set.range a)=⊤) :
    ∀u : Fin (n+1)→ℝ,u≠0 → ∃j,u ⬝ᵥ liftPts a j ≠0 := by
  intro u hu
  by_contra h
  push Not at h
  let v : Fin n→ℝ := fun i=>u i.castSucc
  have hj : ∀j,v ⬝ᵥ a j+u (Fin.last n)=0 := by
    intro j
    have hh := h (Sum.inl j)
    simpa [liftPts,dotProduct,Fin.sum_univ_castSucc,v] using hh
  have hall : ∀x : Fin n→ℝ,v ⬝ᵥ x+u (Fin.last n)=0 := by
    intro x
    have hx : x∈affineSpan ℝ (Set.range a) := by rw [ha]; trivial
    refine affineSpan_induction hx (fun x hx => ?_) (fun c x y z hx hy hz => ?_)
    · obtain ⟨j,rfl⟩ := hx
      exact hj j
    · simp only [vsub_eq_sub,vadd_eq_add,dotProduct_add,dotProduct_smul,dotProduct_sub,smul_eq_mul]
      have heq : v ⬝ᵥ x = v ⬝ᵥ y := by linarith
      rw [heq,sub_self,mul_zero,zero_add]
      exact hz
  have hl : u (Fin.last n)=0 := by simpa using hall 0
  have hv : v=0 := by
    ext i
    have hh := hall (Pi.single i 1)
    simpa [hl] using hh
  apply hu
  ext i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · exact hl
  · exact congrFun hv j

end KhachiyanRound.BCD.Proof
-- End LiftNondegenerate

-- Begin ScalarGain

namespace KhachiyanRound.BCD.Proof

lemma gain_deriv {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt gain (x / (1+x)^2) x := by
  have hn : 1+x ≠ 0 := by positivity
  have h := ((hasDerivAt_id x).const_add 1).log hn
  have hq := (hasDerivAt_id x).div ((hasDerivAt_id x).const_add 1) hn
  convert! h.sub hq using 1
  dsimp [gain]
  field_simp
  ring

lemma gain_mono : MonotoneOn gain (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro x hx
    exact (gain_deriv hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (gain_deriv (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(gain_deriv (interior_subset hx)).deriv]
    exact div_nonneg (interior_subset hx) (sq_nonneg _)

@[simp] lemma gain_zero : gain 0 = 0 := by simp [gain]

lemma gain_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gain x := by
  simpa using gain_mono (show (0:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr le_rfl) hx hx

lemma gain_quadratic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x^2 / 8 ≤ gain x := by
  have hd : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun t => gain t-t^2/8) (t/(1+t)^2-t/4) t := by
    intro t ht
    convert! (gain_deriv ht.1).sub (((hasDerivAt_id t).pow 2).div_const 8) using 1
    dsimp
    ring
  have hm : MonotoneOn (fun t => gain t-t^2/8) (Set.Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have h := interior_subset ht
      rw [(hd t h).deriv]
      have ht0 : 0 ≤ t := h.1
      have hp : 0 < (1+t)^2 := by positivity
      have hs : (1+t)^2 ≤ 4 := by nlinarith [h.1,h.2]
      have hh : t/4 ≤ t/(1+t)^2 := by
        apply (le_div_iff₀ hp).mpr
        nlinarith [mul_le_mul_of_nonneg_left hs h.1]
      linarith
  have h := hm (by simp) ⟨hx,hx1⟩ hx
  simp only [gain_zero,zero_pow (by decide : 2 ≠ 0),zero_div,sub_zero] at h
  linarith

lemma gain_log_lower {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1+x)-1 ≤ gain x := by
  have h : x/(1+x) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  unfold gain
  linarith

end KhachiyanRound.BCD.Proof
-- End ScalarGain

-- Begin GapBasic

namespace KhachiyanRound.BCD.Proof

variable {d M : ℝ} {eps D : ℕ → ℝ} (h : NumericRun d M eps D)
include h

lemma NumericRun.dim_pos : 0 < d := by linarith [h.dim_ge]

lemma NumericRun.gap_antitone : Antitone D := by
  apply antitone_nat_of_succ_le
  intro k
  linarith [h.step_le k, gain_nonneg (h.eps_nonneg k)]

lemma NumericRun.gap_le_linear (k : ℕ) : D k ≤ d * eps k := by
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1+eps k by linarith [h.eps_nonneg k])
  have hm := mul_le_mul_of_nonneg_left hl h.dim_pos.le
  linarith [h.gap_le k]

lemma NumericRun.affine_decay (k : ℕ) :
    D (k+1) ≤ (1-1/d)*D k+1 := by
  have hl : D k / d ≤ Real.log (1+eps k) := by
    apply (div_le_iff₀ h.dim_pos).mpr
    simpa [mul_comm] using h.gap_le k
  have hg := gain_log_lower (h.eps_nonneg k)
  have hs := h.step_le k
  have he : (1-1/d)*D k+1 = D k-D k/d+1 := by ring
  rw [he]
  linarith

lemma NumericRun.quadratic_decay (k : ℕ) (hk : D k ≤ 2*d) :
    D (k+1) ≤ D k-(D k)^2/(32*d^2) := by
  have hd := h.dim_pos
  have hD := h.gap_nonneg k
  have he := h.eps_nonneg k
  have hh : (D k)^2/(32*d^2) ≤ gain (eps k) := by
    by_cases he1 : eps k ≤ 1
    · have hg := gain_quadratic he he1
      have hs : (D k)^2 ≤ d^2*(eps k)^2 := by
        nlinarith [h.gap_le_linear k, sq_nonneg (d*eps k-D k)]
      have hp : 0 < 32*d^2 := by positivity
      have hb : (D k)^2/(32*d^2) ≤ (eps k)^2/8 := by
        apply (div_le_iff₀ hp).mpr
        nlinarith [sq_nonneg (eps k)]
      exact hb.trans hg
    · have hg := gain_mono (show (1:ℝ) ∈ Set.Ici 0 by norm_num)
        he (le_of_not_ge he1)
      have h1 := gain_quadratic (x:=1) (by norm_num) le_rfl
      have hp : 0 < 32*d^2 := by positivity
      have hb : (D k)^2/(32*d^2) ≤ 1/8 := by
        apply (div_le_iff₀ hp).mpr
        nlinarith [sq_nonneg (2*d-D k)]
      norm_num at h1
      linarith
  linarith [h.step_le k]

end KhachiyanRound.BCD.Proof
-- End GapBasic

-- Begin AffineDecay

namespace KhachiyanRound.BCD.Proof

lemma NumericRun.geometric_decay {d M : ℝ} {eps D : ℕ → ℝ}
    (h : NumericRun d M eps D) (k : ℕ) :
    D k ≤ d+(1-1/d)^k*D 0 := by
  have hd := h.dim_pos
  have hq : 0 ≤ 1-1/d := by
    have : 1/d ≤ 1 := (div_le_one hd).mpr (by linarith [h.dim_ge])
    linarith
  induction k with
  | zero => simp; linarith
  | succ k ih =>
    have hm := mul_le_mul_of_nonneg_left ih hq
    have hs := h.affine_decay k
    have he : (1-1/d)*d=d-1 := by field_simp
    rw [pow_succ]
    nlinarith

lemma NumericRun.exponential_decay {d M : ℝ} {eps D : ℕ → ℝ}
    (h : NumericRun d M eps D) (k : ℕ) :
    D k ≤ d+Real.exp (-(k:ℝ)/d)*(d*Real.log M) := by
  have hd := h.dim_pos
  have hq : 0 ≤ 1-1/d := by
    have : 1/d ≤ 1 := (div_le_one hd).mpr (by linarith [h.dim_ge])
    linarith
  have he : 1-1/d ≤ Real.exp (-1/d) := by
    have hh := Real.add_one_le_exp (-1/d)
    rw [neg_div] at hh ⊢
    linarith
  have hp := pow_le_pow_left₀ hq he k
  have hr : Real.exp (-1/d)^k=Real.exp (-(k:ℝ)/d) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hr] at hp
  have hmul := mul_le_mul_of_nonneg_right hp (h.gap_nonneg 0)
  have hi := mul_le_mul_of_nonneg_left h.initial_le (Real.exp_pos (-(k:ℝ)/d)).le
  linarith [h.geometric_decay k]

lemma NumericRun.small_gap_after {d M : ℝ} {eps D : ℕ → ℝ}
    (h : NumericRun d M eps D) (k : ℕ)
    (hk : d*Real.log (Real.log M) ≤ k) : D k ≤ 2*d := by
  have hd := h.dim_pos
  have hM : 1 < M := by linarith [h.size_ge]
  have hl : 0 < Real.log M := Real.log_pos hM
  have hex : -(k:ℝ)/d ≤ -Real.log (Real.log M) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hb := Real.exp_le_exp.mpr hex
  have hh := mul_le_mul_of_nonneg_right hb (mul_nonneg hd.le hl.le)
  rw [Real.exp_neg,Real.exp_log hl] at hh
  have he : (Real.log M)⁻¹*(d*Real.log M)=d := by field_simp
  rw [he] at hh
  linarith [h.exponential_decay k]

end KhachiyanRound.BCD.Proof
-- End AffineDecay

-- Begin ReciprocalDecay

namespace KhachiyanRound.BCD.Proof

lemma reciprocal_step {A t x y : ℝ} (hA : 0 < A) (ht : 2 ≤ t)
    (hx : 0 ≤ x) (hxb : x ≤ A/t) (hy : y ≤ x-x^2/A) :
    y ≤ A/(t+1) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t+1 := by linarith
  have hb : A/t ≤ A/2 := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith
  have hxA : x+A/t ≤ A := by linarith
  have hf : x-x^2/A ≤ A/t-(A/t)^2/A := by
    have hxb2 := (le_div_iff₀ ht0).mp hxb
    have hxA2 := mul_le_mul_of_nonneg_right hxA ht0.le
    have he : (x+A/t)*t=x*t+A := by field_simp
    rw [he] at hxA2
    have hm := mul_nonneg (show 0 ≤ A-x*t by linarith)
      (show 0 ≤ A*t-x*t-A by linarith)
    apply (le_of_mul_le_mul_right ?_ hA)
    field_simp
    nlinarith
  have hg : A/t-(A/t)^2/A ≤ A/(t+1) := by
    apply (le_of_mul_le_mul_right ?_ (show 0 < t^2*(t+1) by positivity))
    field_simp
    nlinarith
  exact hy.trans (hf.trans hg)

lemma NumericRun.reciprocal_decay {d M : ℝ} {eps D : ℕ → ℝ}
    (h : NumericRun d M eps D) (s : ℕ) (hs : D s ≤ 2*d) (k : ℕ) :
    D (s+k) ≤ (32*d^2)/((k:ℝ)+16*d) := by
  have hd := h.dim_pos
  have hA : 0 < 32*d^2 := by positivity
  induction k with
  | zero =>
    simpa only [Nat.add_zero,Nat.cast_zero,zero_add,
      show 32*d^2/(16*d)=2*d by field_simp; norm_num] using hs
  | succ k ih =>
    have ht : 2 ≤ (k:ℝ)+16*d := by
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      linarith [h.dim_ge]
    have hbound : D (s+k) ≤ 2*d :=
      (h.gap_antitone (Nat.le_add_right s k)).trans hs
    have hr := reciprocal_step hA ht (h.gap_nonneg (s+k)) ih
      (h.quadratic_decay (s+k) hbound)
    simpa only [Nat.cast_add,Nat.cast_one,Nat.add_assoc,add_assoc,add_comm (16*d) 1] using hr

end KhachiyanRound.BCD.Proof
-- End ReciprocalDecay

-- Begin FiniteHit

namespace KhachiyanRound.BCD.Proof

lemma NumericRun.fixed_gain_sum {d M : ℝ} {eps D : ℕ → ℝ}
    (h : NumericRun d M eps D) (s N : ℕ) (a : ℝ)
    (ha : ∀ k < N, a ≤ gain (eps (s+k))) :
    D (s+N) ≤ D s-(N:ℝ)*a := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))
    have hs := h.step_le (s+N)
    have hg := ha N (Nat.lt_succ_self N)
    rw [Nat.cast_succ]
    simp only [Nat.add_assoc] at hs
    linarith

lemma NumericRun.hit_of_small_gap {d M : ℝ} {eps D : ℕ → ℝ}
    (h : NumericRun d M eps D) (s : ℕ) {eta : ℝ}
    (he : 0 < eta) (he1 : eta ≤ 1) (hs : D s ≤ d*eta) :
    ∃ j ≤ ⌊8*d/eta⌋₊+1, eps (s+j) ≤ eta := by
  by_contra! hh
  let N := ⌊8*d/eta⌋₊+1
  have hn : 8*d/eta < (N:ℝ) := by
    simpa [N,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (8*d/eta)
  have hg : ∀ k < N, eta^2/8 ≤ gain (eps (s+k)) := by
    intro k hk
    exact (gain_quadratic he.le he1).trans
      (gain_mono he.le (h.eps_nonneg _) (hh k (Nat.le_of_lt hk)).le)
  have ht := h.fixed_gain_sum s N (eta^2/8) hg
  have hmul := (div_lt_iff₀ he).mp hn
  have hm := mul_lt_mul_of_pos_right hmul he
  nlinarith [h.gap_nonneg (s+N)]

end KhachiyanRound.BCD.Proof
-- End FiniteHit

-- Begin IterationCount

namespace KhachiyanRound.BCD.Proof

lemma loglog_nonneg {M : ℝ} (hM : 4 ≤ M) : 0 ≤ Real.log (Real.log M) := by
  have hM0 : 0 < M := by linarith
  have hl : 1 ≤ Real.log M := by
    apply (Real.le_log_iff_exp_le hM0).mpr
    linarith [Real.exp_one_lt_three]
  exact Real.log_nonneg hl

lemma NumericRun.iteration_small {d M : ℝ} {eps D : ℕ → ℝ}
    (h : NumericRun d M eps D) {eta : ℝ} (he : 0 < eta) (he1 : eta ≤ 1) :
    ∃ k : ℕ, (k:ℝ) ≤ d*Real.log (Real.log M)+40*d/eta+3 ∧ eps k ≤ eta := by
  have hd := h.dim_pos
  have hl := loglog_nonneg h.size_ge
  let s := ⌈d*Real.log (Real.log M)⌉₊
  let t := ⌈32*d/eta⌉₊
  have hslo : d*Real.log (Real.log M) ≤ (s:ℝ) := Nat.le_ceil _
  have htlo : 32*d/eta ≤ (t:ℝ) := Nat.le_ceil _
  have hs := h.small_gap_after s hslo
  have hrec := h.reciprocal_decay s hs t
  have hden : 0 < (t:ℝ)+16*d := by positivity
  have hm := (div_le_iff₀ he).mp htlo
  have hb : 32*d^2/((t:ℝ)+16*d) ≤ d*eta := by
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hm hd.le
    nlinarith [mul_nonneg (sq_nonneg d) he.le]
  obtain ⟨j,hj,hje⟩ := h.hit_of_small_gap (s+t) he he1 (hrec.trans hb)
  refine ⟨s+t+j,?_,by simpa only [Nat.add_assoc] using hje⟩
  have hsbound : (s:ℝ) ≤ d*Real.log (Real.log M)+1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hd.le hl)).le
  have htbound : (t:ℝ) ≤ 32*d/eta+1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 32*d/eta)).le
  have hjbound : (j:ℝ) ≤ 8*d/eta+1 := by
    have hj' : (j:ℝ) ≤ (⌊8*d/eta⌋₊:ℝ)+1 := by exact_mod_cast hj
    linarith [Nat.floor_le (show 0 ≤ 8*d/eta by positivity)]
  push_cast
  have heq : 32*d/eta+8*d/eta=40*d/eta := by ring
  linarith

end KhachiyanRound.BCD.Proof
-- End IterationCount

-- Begin NumericCount

namespace KhachiyanRound.BCD.Proof

lemma NumericRun.iteration_bound {d M : ℝ} {eps D : ℕ → ℝ}
    (h : NumericRun d M eps D) {eta : ℝ} (he : 0 < eta) :
    ∃ k : ℕ, (k:ℝ) ≤ 128*d*(1/eta+1+Real.log (Real.log M)) ∧ eps k ≤ eta := by
  have hd := h.dim_pos
  have hl := loglog_nonneg h.size_ge
  have hdl := mul_nonneg hd.le hl
  have hi : 0 < (1:ℝ)/eta := one_div_pos.mpr he
  have hdi := mul_pos hd hi
  by_cases he1 : eta ≤ 1
  · obtain ⟨k,hk,hke⟩ := h.iteration_small he he1
    refine ⟨k,?_,hke⟩
    have heq : 40*d/eta=40*(d*(1/eta)) := by ring
    rw [heq] at hk
    nlinarith [h.dim_ge]
  · obtain ⟨k,hk,hke⟩ := h.iteration_small (eta:=1) (by norm_num) le_rfl
    refine ⟨k,?_,hke.trans (le_of_not_ge he1)⟩
    norm_num at hk
    nlinarith [h.dim_ge]

end KhachiyanRound.BCD.Proof
-- End NumericCount

-- Begin NativeIteration

namespace KhachiyanRound.BCD.Proof

lemma native_iteration {m n : ℕ} (a : Fin m → Fin n → ℝ) (hn : 1≤n)
    (ha : affineSpan ℝ (Set.range a)=⊤) (epsilon : ℝ) (he : 0<epsilon)
    (p : ℕ → (Fin m ⊕ Fin m → ℝ)) (hrun : IsBCDRun (liftPts a) p) :
    ∃k : ℕ, (k:ℝ) ≤ 1024*(n+1)*(1/epsilon+Real.log (n+1)+Real.log (Real.log (2*m))) ∧
      IsRelaxedOpt (liftPts a) (p k) ((n:ℝ)/(n+1)*epsilon) ∧
      (momentMatrix (liftPts a) (p k)).PosDef ∧ p k∈stdSimplex ℝ (Fin m⊕Fin m) := by
  have hm := affine_card_bound a ha
  have hm2 : 2 ≤ m := by omega
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
  have hd : 2≤n+1 := by omega
  have hsize : 4≤Fintype.card (Fin m⊕Fin m) := by simp; omega
  have hs := lift_nondegenerate a ha
  obtain ⟨D,hD⟩ := bcd_numeric (liftPts a) hd hsize hs p hrun
  let eta := (n:ℝ)/(n+1)*epsilon
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hd0 : (0:ℝ)<n+1 := by positivity
  have heta : 0<eta := by dsimp [eta]; positivity
  obtain ⟨k,hk,hke⟩ := hD.iteration_bound heta
  have hv := bcd_valid (liftPts a) hd hs p hrun k
  refine ⟨k,?_,relaxed_of_eps_le _ _ (by omega) hke,hv.2,hv.1⟩
  have hi : 1/eta ≤ 2/epsilon := by
    apply (div_le_div_iff₀ heta he).mpr
    dsimp [eta]
    have hratio : (1:ℝ)/2 ≤ (n:ℝ)/(n+1) := by
      apply (div_le_div_iff₀ (by norm_num) hd0).mpr
      have : (1:ℝ)≤n := by exact_mod_cast hn
      linarith
    nlinarith
  have hlog : (1:ℝ)/2 ≤ Real.log (n+1) := by
    have hb := Real.log_two_gt_d9
    have hmono : Real.log 2 ≤ Real.log (n+1) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hd)
    linarith
  have hll : 0≤Real.log (Real.log (2*m:ℝ)) := by
    apply loglog_nonneg
    exact_mod_cast (by omega : 4≤2*m)
  have hie : 0≤1/epsilon := by positivity
  have hh : 1/eta+1+Real.log (Real.log (2*m:ℝ)) ≤
      8*(1/epsilon+Real.log (n+1)+Real.log (Real.log (2*m:ℝ))) := by
    have heq : 2/epsilon=2*(1/epsilon) := by ring
    rw [heq] at hi
    linarith
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hk
  have heq : (m:ℝ)+(m:ℝ)=2*m := by ring
  rw [heq] at hk
  apply hk.trans
  have hmul := mul_le_mul_of_nonneg_left hh (show 0≤128*((n:ℝ)+1) by positivity)
  nlinarith

end KhachiyanRound.BCD.Proof
-- End NativeIteration

-- Begin CovarianceBasic

open Matrix
namespace KhachiyanRound.BCD.Proof

noncomputable def barycenter {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ) : Fin n → ℝ := ∑ j,q j • a j

noncomputable def covariance {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  momentMatrix (fun j => a j-barycenter a q) q

lemma barycenter_apply {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ) (i : Fin n) :
    barycenter a q i = ∑ j,q j*a j i := by simp [barycenter]

lemma centered_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ) (hq : ∑ j,q j=1) :
    ∑ j,q j • (a j-barycenter a q)=0 := by
  simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,hq,one_smul]
  exact sub_self _

lemma centered_dot_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ) (hq : ∑ j,q j=1) (u : Fin n → ℝ) :
    ∑ j,q j*(u ⬝ᵥ (a j-barycenter a q))=0 := by
  have h := congrArg (fun v => u ⬝ᵥ v) (centered_sum a q hq)
  simpa only [dotProduct_sum,dotProduct_smul,smul_eq_mul,dotProduct_zero] using h

lemma covariance_quadratic {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ covariance a q *ᵥu = ∑ j,q j*(u ⬝ᵥ (a j-barycenter a q))^2 :=
  moment_quadratic _ _ _

lemma dot_snoc {n : ℕ} (x y : Fin n → ℝ) (s t : ℝ) :
    Fin.snoc x s ⬝ᵥ Fin.snoc y t = x ⬝ᵥ y+s*t := by
  simp only [dotProduct,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]

lemma aggr_simplex {m : ℕ} (p : Fin m ⊕ Fin m → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin m ⊕ Fin m)) : aggr p ∈ stdSimplex ℝ (Fin m) := by
  refine ⟨fun j => add_nonneg (hp.1 _) (hp.1 _),?_⟩
  simpa only [aggr,Finset.sum_add_distrib,Fintype.sum_sum_type] using hp.2

lemma moment_lift_aggr {m n : ℕ} (a : Fin m → Fin n → ℝ)
    (p : Fin m ⊕ Fin m → ℝ) :
    momentMatrix (liftPts a) p = momentMatrix (fun j => Fin.snoc (a j) 1) (aggr p) := by
  ext i j
  simp only [moment_apply,Fintype.sum_sum_type,liftPts,Sum.elim_inl,Sum.elim_inr,
    Pi.neg_apply,aggr,add_mul,Finset.sum_add_distrib]
  apply congrArg₂ (·+·) rfl
  apply Finset.sum_congr rfl
  intro k _
  ring

end KhachiyanRound.BCD.Proof
-- End CovarianceBasic

-- Begin CovarianceMatrix

open Matrix
namespace KhachiyanRound.BCD.Proof

lemma covariance_eq {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ) (hq : ∑ j,q j=1) :
    covariance a q = momentMatrix a q-vecMulVec (barycenter a q) (barycenter a q) := by
  ext i j
  simp only [covariance,moment_apply,Matrix.sub_apply,vecMulVec_apply,Pi.sub_apply]
  have he : (∑ k,q k*(a k i-barycenter a q i)*(a k j-barycenter a q j)) =
      (∑ k,q k*a k i*a k j)-barycenter a q i*(∑ k,q k*a k j)-
      barycenter a q j*(∑ k,q k*a k i)+barycenter a q i*barycenter a q j*(∑ k,q k) := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,← barycenter_apply a q i,← barycenter_apply a q j,hq]
  ring

lemma moment_snoc_block {m n : ℕ} (a : Fin m → Fin n → ℝ)
    (q : Fin m → ℝ) (hq : ∑ j,q j=1) :
    momentMatrix (fun j => Fin.snoc (a j) 1) q=blockMatrix a q := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  all_goals simp [moment_apply,blockMatrix,Matrix.of_apply,Fin.snoc_last,
    Fin.snoc_castSucc,hq]

lemma covariance_pd {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ) (hq : ∀j,0≤q j)
    (hM : (momentMatrix (fun j => Fin.snoc (a j) 1) q).PosDef) :
    (covariance a q).PosDef := by
  have hp := moment_psd (fun j => a j-barycenter a q) q hq
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hp.isHermitian
  intro u hu
  simp only [star_trivial]
  let z : Fin (n+1) → ℝ := Fin.snoc u (-(u ⬝ᵥ barycenter a q))
  have hz : z ≠ 0 := by
    intro he
    apply hu
    funext i
    have hi := congrFun he i.castSucc
    simpa [z] using hi
  have hh := hM.dotProduct_mulVec_pos hz
  simp only [star_trivial,moment_quadratic] at hh
  rw [moment_quadratic]
  convert hh using 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [z,dot_snoc,dotProduct_sub,mul_one]
  ring

end KhachiyanRound.BCD.Proof
-- End CovarianceMatrix

-- Begin BlockInverse

open Matrix
namespace KhachiyanRound.BCD.Proof

lemma block_mulVec {m n : ℕ} (a : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (u : Fin n → ℝ) (t : ℝ) :
    blockMatrix a q *ᵥ Fin.snoc u t =
      Fin.snoc (momentMatrix a q *ᵥu+t • barycenter a q) (barycenter a q ⬝ᵥu+t) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [mulVec,dotProduct,Fin.sum_univ_castSucc,blockMatrix,Matrix.of_apply,
      barycenter_apply]
  · simp [mulVec,dotProduct,Fin.sum_univ_castSucc,blockMatrix,Matrix.of_apply,
      barycenter_apply,mul_comm]

lemma covariance_mulVec {m n : ℕ} (a : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (hq : ∑ j,q j=1) (u : Fin n → ℝ) :
    covariance a q *ᵥu=momentMatrix a q *ᵥu-(barycenter a q ⬝ᵥu) • barycenter a q := by
  rw [covariance_eq a q hq,sub_mulVec,vecMulVec_mulVec]
  simp only [op_smul_eq_smul]

lemma block_inverse_quadratic {m n : ℕ} (a : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (hq : ∑ j,q j=1) (hM : (blockMatrix a q).PosDef)
    (hC : (covariance a q).PosDef) (x : Fin n → ℝ) :
    Fin.snoc x 1 ⬝ᵥ (blockMatrix a q)⁻¹*ᵥFin.snoc x 1 =
      1+(x-barycenter a q) ⬝ᵥ (covariance a q)⁻¹*ᵥ(x-barycenter a q) := by
  let b := barycenter a q
  let u := (covariance a q)⁻¹*ᵥ(x-b)
  let t := 1-b ⬝ᵥu
  have hCu : covariance a q *ᵥu=x-b := by
    dsimp [u]
    rw [mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC.det_pos.ne'),one_mulVec]
  have hsolve : blockMatrix a q *ᵥFin.snoc u t=Fin.snoc x 1 := by
    rw [block_mulVec]
    have hu := covariance_mulVec a q hq u
    rw [hCu] at hu
    congr 1
    · funext i
      have hi := congrFun hu i
      simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hi ⊢
      dsimp [t,b]
      dsimp [b] at hi
      nlinarith
    · dsimp [t,b]
      ring
  have hinv : (blockMatrix a q)⁻¹*ᵥFin.snoc x 1=Fin.snoc u t := by
    rw [← hsolve,mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM.det_pos.ne'),one_mulVec]
  rw [hinv,dot_snoc]
  change x ⬝ᵥu+1*t=1+(x-b) ⬝ᵥu
  rw [sub_dotProduct]
  dsimp [t]
  ring

end KhachiyanRound.BCD.Proof
-- End BlockInverse

-- Begin QuadraticCS

open Matrix
open scoped MatrixOrder
namespace KhachiyanRound.BCD.Proof

lemma psd_cauchy {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosSemidef) (x y : Fin n → ℝ) :
    (x ⬝ᵥ C*ᵥy)^2 ≤ (x ⬝ᵥ C*ᵥx)*(y ⬝ᵥ C*ᵥy) := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  have he : C=Bᵀ*B := by
    simpa only [star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial] using hB
  have hxy : ∀ u v : Fin n → ℝ, u ⬝ᵥ C*ᵥv = (B*ᵥu) ⬝ᵥ (B*ᵥv) := by
    intro u v
    rw [he,← mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
  rw [hxy,hxy,hxy]
  simpa only [dotProduct,pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (B*ᵥx) (B*ᵥy)

lemma inverse_cauchy {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosDef) (x y : Fin n → ℝ) :
    (x ⬝ᵥ y)^2 ≤ (x ⬝ᵥ C*ᵥx)*(y ⬝ᵥ C⁻¹*ᵥy) := by
  have hm : C*C⁻¹=1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.mpr hC.det_pos.ne')
  have hv : C*ᵥ(C⁻¹*ᵥy)=y := by rw [mulVec_mulVec,hm,one_mulVec]
  have h := psd_cauchy C hC.posSemidef x (C⁻¹*ᵥy)
  rw [hv,dotProduct_comm (C⁻¹*ᵥy) y] at h
  exact h

lemma inverse_cauchy_abs {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosDef) (x y : Fin n → ℝ) {r : ℝ}
    (_hr : 0 ≤ r) (hy : y ⬝ᵥ C⁻¹*ᵥy ≤ r) :
    |x ⬝ᵥ y| ≤ Real.sqrt (r*(x ⬝ᵥ C*ᵥx)) := by
  have hx : 0 ≤ x ⬝ᵥ C*ᵥx := by
    simpa only [star_trivial] using hC.posSemidef.dotProduct_mulVec_nonneg x
  have hc := inverse_cauchy C hC x y
  have hm := mul_le_mul_of_nonneg_left hy hx
  apply Real.abs_le_sqrt
  nlinarith [mul_nonneg _hr hx]

end KhachiyanRound.BCD.Proof
-- End QuadraticCS

-- Begin QuadraticSet

open Matrix
open scoped Pointwise
namespace KhachiyanRound.BCD.Proof

lemma quadratic_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (c : ℝ) :
    (c • x) ⬝ᵥ A*ᵥ(c • x)=c^2*(x ⬝ᵥ A*ᵥx) := by
  simp only [mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

lemma quadratic_sublevel_convex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (R : ℝ) : Convex ℝ {x | x ⬝ᵥ A*ᵥx ≤ R} := by
  intro x hx y hy a b ha hb hab
  have hp : 0 ≤ (x-y) ⬝ᵥ A*ᵥ(x-y) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (x-y)
  have he : (a • x+b • y) ⬝ᵥ A*ᵥ(a • x+b • y) =
      a*(x ⬝ᵥ A*ᵥx)+b*(y ⬝ᵥ A*ᵥy)-a*b*((x-y) ⬝ᵥ A*ᵥ(x-y)) := by
    have hbe : b=1-a := by linarith
    rw [hbe]
    simp only [mulVec_add,mulVec_smul,add_dotProduct,smul_dotProduct,dotProduct_add,
      dotProduct_smul,smul_eq_mul,mulVec_sub,sub_dotProduct,dotProduct_sub]
    ring
  change (a • x+b • y) ⬝ᵥ A*ᵥ(a • x+b • y) ≤ R
  rw [he]
  have hm := mul_nonneg (mul_nonneg ha hb) hp
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  have hh : (a+b)*R=R := by rw [hab,one_mul]
  nlinarith

lemma centered_sublevel_convex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (b : Fin n → ℝ) (R : ℝ) :
    Convex ℝ {x | (x-b) ⬝ᵥ A*ᵥ(x-b) ≤ R} := by
  simpa only [Set.preimage_ofPred_eq,sub_eq_add_neg,add_comm] using
    (quadratic_sublevel_convex A hA R).translate_preimage_right (-b)

lemma mem_scaled_ellipsoid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ) {R : ℝ} (hR : 0 < R) :
    z ∈ Real.sqrt R • LinearOptimization.ellipsoid 0 A ↔ z ⬝ᵥ A⁻¹*ᵥz ≤ R := by
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsq := Real.sq_sqrt hR.le
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (Real.sqrt R • y) ⬝ᵥ A⁻¹*ᵥ(Real.sqrt R • y) ≤ R
    rw [quadratic_smul,hsq]
    have hy' : y ⬝ᵥ A⁻¹*ᵥy ≤ 1 := by simpa only [LinearOptimization.ellipsoid,Set.mem_ofPred_eq,sub_zero] using hy
    nlinarith
  · intro hz
    refine ⟨(Real.sqrt R)⁻¹ • z,?_,?_⟩
    · change ((Real.sqrt R)⁻¹ • z-0) ⬝ᵥ A⁻¹*ᵥ((Real.sqrt R)⁻¹ • z-0) ≤ 1
      rw [sub_zero,quadratic_smul,inv_pow,hsq]
      exact (inv_mul_le_iff₀ hR).mpr (by simpa using hz)
    · change Real.sqrt R • ((Real.sqrt R)⁻¹ • z)=z
      rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]

end KhachiyanRound.BCD.Proof
-- End QuadraticSet

-- Begin NativeSlice

open Matrix
open scoped Pointwise
namespace KhachiyanRound.BCD.Proof

lemma native_slice_iff {m n : ℕ} (a : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (hq : ∑ j,q j=1) (hM : (blockMatrix a q).PosDef) (hC : (covariance a q).PosDef)
    (eps : ℝ) (hr : 0 < (1+eps)*(n:ℝ)) (x : Fin n → ℝ) :
    x ∈ lemma5Ellipsoid a q eps ↔
      (x-barycenter a q) ⬝ᵥ (covariance a q)⁻¹*ᵥ(x-barycenter a q) ≤ (1+eps)*(n:ℝ) := by
  change Fin.snoc x 1 ∈ Real.sqrt (1+(1+eps)*(n:ℝ)) •
    LinearOptimization.ellipsoid 0 (blockMatrix a q) ↔ _
  rw [mem_scaled_ellipsoid _ _ (by linarith),block_inverse_quadratic a q hq hM hC x]
  constructor <;> intro h <;> linarith

lemma lift_block_pd {m n : ℕ} (a : Fin m → Fin n → ℝ)
    (p : Fin m ⊕ Fin m → ℝ) (hp : p ∈ stdSimplex ℝ (Fin m ⊕ Fin m))
    (hM : (momentMatrix (liftPts a) p).PosDef) :
    (blockMatrix a (aggr p)).PosDef ∧ (covariance a (aggr p)).PosDef := by
  have hq := aggr_simplex p hp
  rw [moment_lift_aggr] at hM
  exact ⟨by rwa [moment_snoc_block a _ hq.2] at hM,
    covariance_pd a _ hq.1 hM⟩

lemma relaxed_points_in_slice {m n : ℕ} (a : Fin m → Fin n → ℝ)
    (p : Fin m ⊕ Fin m → ℝ) (hp : p ∈ stdSimplex ℝ (Fin m ⊕ Fin m))
    (hM : (momentMatrix (liftPts a) p).PosDef) (eps : ℝ)
    (hrel : IsRelaxedOpt (liftPts a) p ((n:ℝ)/(n+1)*eps)) :
    ∀ j,(a j-barycenter a (aggr p)) ⬝ᵥ (covariance a (aggr p))⁻¹*ᵥ
      (a j-barycenter a (aggr p)) ≤ (1+eps)*(n:ℝ) := by
  have hq := aggr_simplex p hp
  obtain ⟨hb,hc⟩ := lift_block_pd a p hp hM
  have hm : momentMatrix (liftPts a) p=blockMatrix a (aggr p) := by
    rw [moment_lift_aggr,moment_snoc_block a _ hq.2]
  intro j
  have hh := hrel (Sum.inl j)
  change Fin.snoc (a j) 1 ⬝ᵥ (momentMatrix (liftPts a) p)⁻¹*ᵥFin.snoc (a j) 1 ≤ _ at hh
  rw [hm,block_inverse_quadratic a _ hq.2 hb hc] at hh
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have he : (1+(n:ℝ)/(n+1)*eps)*((n:ℝ)+1)=1+(1+eps)*(n:ℝ) := by
    field_simp
    ring
  push_cast at hh
  rw [he] at hh
  linarith

end KhachiyanRound.BCD.Proof
-- End NativeSlice

-- Begin ScalarSupport

namespace KhachiyanRound.BCD.Proof

lemma weighted_variance_support {ι : Type*} [Fintype ι]
    (q z : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i,q i=1)
    (hz : ∑ i,q i*z i=0) (a B : ℝ)
    (hlo : ∀ i,-a ≤ z i) (hhi : ∀ i,z i ≤ B) :
    ∑ i,q i*(z i)^2 ≤ a*B := by
  have hh : 0 ≤ ∑ i,q i*((z i+a)*(B-z i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hq i)
      (mul_nonneg (by linarith [hlo i]) (by linarith [hhi i]))
  have he : (∑ i,q i*((z i+a)*(B-z i))) =
      (B-a)*(∑ i,q i*z i)+a*B*(∑ i,q i)-(∑ i,q i*(z i)^2) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hz,hq1] at hh
  linarith

lemma sqrt_support_lower {v r B : ℝ} (hv : 0 < v) (hr : 0 < r)
    (h : v ≤ Real.sqrt (r*v)*B) : Real.sqrt (v/r) ≤ B := by
  have hs : 0 < Real.sqrt (r*v) := Real.sqrt_pos.mpr (mul_pos hr hv)
  have hv0 := hv.le
  have hr0 := hr.le
  have hsq := Real.sq_sqrt (mul_nonneg hr0 hv0)
  have ht := Real.sq_sqrt (div_nonneg hv0 hr0)
  have htn := Real.sqrt_nonneg (v/r)
  have hprod : Real.sqrt (r*v)*Real.sqrt (v/r)=v := by
    rw [← Real.sqrt_mul (mul_nonneg hr0 hv0)]
    have he : r*v*(v/r)=v^2 := by field_simp
    rw [he,Real.sqrt_sq hv0]
  nlinarith

end KhachiyanRound.BCD.Proof
-- End ScalarSupport

-- Begin SupportHull

open Matrix
namespace KhachiyanRound.BCD.Proof

lemma linear_eq_dot {n : ℕ} (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) (x : Fin n → ℝ) :
    f x = (fun i => f (Pi.single i 1)) ⬝ᵥx := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : Pi.single i (x i)=x i • (Pi.single i 1 : Fin n → ℝ) := by
    ext j
    by_cases h : j=i <;> simp [h]
  rw [hi,map_smul]
  simp only [smul_eq_mul,mul_comm]

lemma mem_hull_of_support {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : ∀ u : Fin n → ℝ, ∃j,u ⬝ᵥx ≤ u ⬝ᵥa j) :
    x ∈ convexHull ℝ (Set.range a) := by
  by_contra hn
  have hc : IsClosed (convexHull ℝ (Set.range a)) :=
    ((Set.finite_range a).isCompact_convexHull (𝕜 := ℝ)).isClosed
  obtain ⟨f,b,hxb,hb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hc hn
  obtain ⟨j,hj⟩ := hx (fun i => -f (Pi.single i 1))
  have hf (y : Fin n → ℝ) : f y=(fun i => f (Pi.single i 1)) ⬝ᵥy :=
    linear_eq_dot f.toLinearMap y
  have hbj := hb (a j) (subset_convexHull ℝ _ (Set.mem_range_self j))
  have hj' : -f x ≤ -f (a j) := by
    rw [hf x,hf (a j)]
    change (-(fun i => f (Pi.single i 1))) ⬝ᵥ x ≤
      (-(fun i => f (Pi.single i 1))) ⬝ᵥ a j at hj
    rw [neg_dotProduct,neg_dotProduct] at hj
    exact hj
  linarith

lemma covariance_support {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ)
    (hq : q ∈ stdSimplex ℝ ι) (hC : (covariance a q).PosDef) {r : ℝ} (hr : 0 < r)
    (ha : ∀ j,(a j-barycenter a q) ⬝ᵥ (covariance a q)⁻¹*ᵥ(a j-barycenter a q) ≤ r)
    (u : Fin n → ℝ) :
    ∃ j, Real.sqrt ((u ⬝ᵥ covariance a q*ᵥu)/r) ≤ u ⬝ᵥ(a j-barycenter a q) := by
  classical
  by_cases hu : u=0
  · subst u
    exact ⟨Classical.arbitrary ι,by simp⟩
  let z : ι → ℝ := fun j => u ⬝ᵥ(a j-barycenter a q)
  obtain ⟨j,hj⟩ := Finset.exists_max_image Finset.univ z Finset.univ_nonempty
  have hv : 0 < u ⬝ᵥ covariance a q*ᵥu := by
    simpa only [star_trivial] using hC.dotProduct_mulVec_pos hu
  have habs (i : ι) : |z i| ≤ Real.sqrt (r*(u ⬝ᵥ covariance a q*ᵥu)) :=
    inverse_cauchy_abs _ hC u _ hr.le (ha i)
  have hs := weighted_variance_support q z hq.1 hq.2 (centered_dot_sum a q hq.2 u)
    (Real.sqrt (r*(u ⬝ᵥ covariance a q*ᵥu))) (z j)
    (fun i => (abs_le.mp (habs i)).1) (fun i => hj.2 i (Finset.mem_univ i))
  rw [← covariance_quadratic] at hs
  exact ⟨j,sqrt_support_lower hv hr hs⟩

end KhachiyanRound.BCD.Proof
-- End SupportHull

-- Begin CovarianceRounding

open Matrix
namespace KhachiyanRound.BCD.Proof

lemma covariance_inner {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ)
    (hq : q ∈ stdSimplex ℝ ι) (hC : (covariance a q).PosDef) {r : ℝ} (hr : 0 < r)
    (ha : ∀ j,(a j-barycenter a q) ⬝ᵥ (covariance a q)⁻¹*ᵥ(a j-barycenter a q) ≤ r)
    (y : Fin n → ℝ) (hy : y ⬝ᵥ (covariance a q)⁻¹*ᵥy ≤ 1/r) :
    barycenter a q+y ∈ convexHull ℝ (Set.range a) := by
  apply mem_hull_of_support
  intro u
  obtain ⟨j,hj⟩ := covariance_support a q hq hC hr ha u
  have hu := inverse_cauchy_abs _ hC u y (by positivity : 0 ≤ 1/r) hy
  have he : 1/r*(u ⬝ᵥ covariance a q*ᵥu)=(u ⬝ᵥ covariance a q*ᵥu)/r := by ring
  rw [he] at hu
  refine ⟨j,?_⟩
  rw [dotProduct_add]
  rw [dotProduct_sub] at hj
  linarith [le_abs_self (u ⬝ᵥy)]

lemma covariance_outer {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ) (hC : (covariance a q).PosDef) (r : ℝ)
    (ha : ∀ j,(a j-barycenter a q) ⬝ᵥ (covariance a q)⁻¹*ᵥ(a j-barycenter a q) ≤ r) :
    convexHull ℝ (Set.range a) ⊆
      {x | (x-barycenter a q) ⬝ᵥ (covariance a q)⁻¹*ᵥ(x-barycenter a q) ≤ r} := by
  apply convexHull_min
  · rintro _ ⟨j,rfl⟩
    exact ha j
  · exact centered_sublevel_convex _ hC.inv.posSemidef _ _

lemma covariance_homothety {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (q : ι → ℝ)
    (hq : q ∈ stdSimplex ℝ ι) (hC : (covariance a q).PosDef) {r : ℝ} (hr : 0 < r)
    (ha : ∀ j,(a j-barycenter a q) ⬝ᵥ (covariance a q)⁻¹*ᵥ(a j-barycenter a q) ≤ r) :
    (AffineMap.homothety (barycenter a q) r⁻¹) ''
      {x | (x-barycenter a q) ⬝ᵥ (covariance a q)⁻¹*ᵥ(x-barycenter a q) ≤ r}
      ⊆ convexHull ℝ (Set.range a) := by
  rintro _ ⟨x,hx,rfl⟩
  have hy : (r⁻¹ • (x-barycenter a q)) ⬝ᵥ (covariance a q)⁻¹*ᵥ
      (r⁻¹ • (x-barycenter a q)) ≤ 1/r := by
    rw [quadratic_smul]
    have hm := mul_le_mul_of_nonneg_left hx (sq_nonneg r⁻¹)
    have he : (r⁻¹)^2*r=1/r := by field_simp
    exact hm.trans (le_of_eq he)
  have hh := covariance_inner a q hq hC hr ha _ hy
  simpa only [AffineMap.homothety_apply,vsub_eq_sub,vadd_eq_add,add_comm] using hh

end KhachiyanRound.BCD.Proof
-- End CovarianceRounding

-- Begin NativeRounding

open Matrix
namespace KhachiyanRound.BCD.Proof

lemma native_rounding {m n : ℕ} [Nonempty (Fin m)]
    (a : Fin m → Fin n → ℝ) (hn : 1 ≤ n) (eps : ℝ) (he : 0 < eps)
    (p : Fin m ⊕ Fin m → ℝ) (hp : p ∈ stdSimplex ℝ (Fin m ⊕ Fin m))
    (hM : (momentMatrix (liftPts a) p).PosDef)
    (hrel : IsRelaxedOpt (liftPts a) p ((n:ℝ)/(n+1)*eps)) :
    (AffineMap.homothety (∑ j,aggr p j • a j) ((1+eps)*(n:ℝ))⁻¹) ''
      lemma5Ellipsoid a (aggr p) eps ⊆ convexHull ℝ (Set.range a) ∧
      convexHull ℝ (Set.range a) ⊆ lemma5Ellipsoid a (aggr p) eps := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hr : 0 < (1+eps)*(n:ℝ) := mul_pos (by linarith) hn0
  have hq := aggr_simplex p hp
  obtain ⟨hb,hc⟩ := lift_block_pd a p hp hM
  have ha := relaxed_points_in_slice a p hp hM eps hrel
  have hset : lemma5Ellipsoid a (aggr p) eps =
      {x | (x-barycenter a (aggr p)) ⬝ᵥ (covariance a (aggr p))⁻¹*ᵥ
        (x-barycenter a (aggr p)) ≤ (1+eps)*(n:ℝ)} := by
    ext x
    exact native_slice_iff a _ hq.2 hb hc eps hr x
  rw [hset]
  exact ⟨covariance_homothety a _ hq hc hr ha,covariance_outer a _ hc _ ha⟩

end KhachiyanRound.BCD.Proof
-- End NativeRounding

-- Begin RootAssembly

namespace KhachiyanRound.BCD

theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (a : Fin m → Fin n → ℝ), 1 ≤ n →
      affineSpan ℝ (Set.range a) = ⊤ → ∀ ε : ℝ, 0 < ε →
        ∀ p : ℕ → (Fin m ⊕ Fin m → ℝ), IsBCDRun (liftPts a) p →
          ∃ k : ℕ, (k : ℝ) ≤ C * (n + 1) *
              (1 / ε + Real.log (n + 1) + Real.log (Real.log (2 * m))) ∧
            IsRelaxedOpt (liftPts a) (p k) ((n : ℝ) / (n + 1) * ε) ∧
            (momentMatrix (liftPts a) (p k)).PosDef ∧
            (AffineMap.homothety (∑ j, aggr (p k) j • a j) ((1 + ε) * (n : ℝ))⁻¹) ''
                lemma5Ellipsoid a (aggr (p k)) ε ⊆ convexHull ℝ (Set.range a) ∧
            convexHull ℝ (Set.range a) ⊆ lemma5Ellipsoid a (aggr (p k)) ε := by
  refine ⟨1024, by norm_num, ?_⟩
  intro n m a hn ha epsilon he p hrun
  have hm := Proof.affine_card_bound a ha
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨k,hk,hrel,hM,hp⟩ := Proof.native_iteration a hn ha epsilon he p hrun
  obtain ⟨hi,ho⟩ := Proof.native_rounding a hn epsilon he (p k) hp hM hrel
  exact ⟨k,hk,hrel,hM,hi,ho⟩
end KhachiyanRound.BCD
-- End RootAssembly

-- Begin Solution

open KhachiyanRound.BCD
open scoped Pointwise


theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (a : Fin m → Fin n → ℝ), 1 ≤ n →
      affineSpan ℝ (Set.range a) = ⊤ → ∀ ε : ℝ, 0 < ε →
        ∀ p : ℕ → (Fin m ⊕ Fin m → ℝ), IsBCDRun (liftPts a) p →
          ∃ k : ℕ, (k : ℝ) ≤ C * (n + 1) *
              (1 / ε + Real.log (n + 1) + Real.log (Real.log (2 * m))) ∧
            IsRelaxedOpt (liftPts a) (p k) ((n : ℝ) / (n + 1) * ε) ∧
            (momentMatrix (liftPts a) (p k)).PosDef ∧
            (AffineMap.homothety (∑ j, aggr (p k) j • a j) ((1 + ε) * (n : ℝ))⁻¹) ''
                lemma5Ellipsoid a (aggr (p k)) ε ⊆ convexHull ℝ (Set.range a) ∧
            convexHull ℝ (Set.range a) ⊆ lemma5Ellipsoid a (aggr (p k)) ε := by
  exact KhachiyanRound.BCD.theorem_2

-- End Solution
