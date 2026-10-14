-- Prove2me | solution 1 for KleinbergHITS.Conv.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T04:45:53.989407+00:00
-- url     : https://prove2.me/submissions/c59efdbf-23d9-4b29-9ee1-a9540f5b5780

-- Complete checked reconstruction of the full native HITS convergence and principal-eigenvector theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_KleinbergHITS_Conv_Setting
import Mathlib


-- Begin Canonical
section ModuleScope_Canonical

end ModuleScope_Canonical
-- End Canonical

-- Begin Normalization
section ModuleScope_Normalization

open scoped BigOperators
namespace KleinbergHITS.Conv.Proof

 theorem sum_sq_pos {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < ∑ i, v i ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    ext i
    simpa using not_exists.mp h i
  exact Finset.sum_pos' (fun j _ => sq_nonneg (v j)) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

 theorem normalize_smul_pos {n : ℕ} (v : Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    normalize (c • v) = normalize v := by
  have hs : ∑ i, (c • v) i ^ 2 = c ^ 2 * ∑ i, v i ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  unfold normalize
  rw [hs, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_pos hc]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, mul_inv_rev]
  field_simp

 theorem normalize_unit {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) :
    ∑ i, normalize v i ^ 2 = 1 := by
  have hs := sum_sq_pos hv
  have hr := Real.sqrt_pos.2 hs
  simp only [normalize, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [inv_pow, Real.sq_sqrt hs.le]
  exact inv_mul_cancel₀ (ne_of_gt hs)

 theorem continuousAt_normalize {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) :
    ContinuousAt (normalize : (Fin n → ℝ) → Fin n → ℝ) v := by
  unfold normalize
  have h : ContinuousAt (fun w : Fin n → ℝ => (Real.sqrt (∑ i, w i ^ 2))⁻¹) v := by
    apply ContinuousAt.inv₀
    · exact Real.continuous_sqrt.continuousAt.comp ((continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)).continuousAt)
    · exact ne_of_gt (Real.sqrt_pos.2 (sum_sq_pos hv))
  exact h.smul continuousAt_id

 theorem normalize_eigen {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ}
    {l : ℝ} (he : M.mulVec v = l • v) : M.mulVec (normalize v) = l • normalize v := by
  unfold normalize
  rw [Matrix.mulVec_smul, he, smul_comm]

end KleinbergHITS.Conv.Proof
end ModuleScope_Normalization
-- End Normalization

-- Begin PositivePowers
section ModuleScope_PositivePowers

open scoped BigOperators
namespace KleinbergHITS.Conv.Proof
open Matrix Filter Topology

 theorem mulVec_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, 0 ≤ M i j) {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ M.mulVec v i := by
  intro i
  change 0 ≤ ∑ j, M i j * v j
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hM i j) (hv j))

 theorem mulVec_abs_bound {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, 0 ≤ M i j) {v w : Fin n → ℝ} (hw : ∀ i, |v i| ≤ w i) :
    ∀ i, |M.mulVec v i| ≤ M.mulVec w i := by
  intro i
  calc
    |∑ j, M i j * v j| ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, M i j * |v j| := by simp only [abs_mul, abs_of_nonneg (hM _ _)]
    _ ≤ ∑ j, M i j * w j := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hw j) (hM i j))

 theorem power_abs_domination {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (v : Fin n → ℝ) (k : ℕ) :
    ∀ i, |(M ^ k).mulVec v i| ≤ (∑ j, |v j|) * (M ^ k).mulVec (allOnes n) i := by
  induction k with
  | zero =>
    intro i
    simpa [allOnes] using (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i))
  | succ k ih =>
    rw [pow_succ']
    simp only [← Matrix.mulVec_mulVec]
    have hh := mulVec_abs_bound hM ih
    intro i
    specialize hh i
    change |(M *ᵥ M ^ k *ᵥ v) i| ≤ (M *ᵥ ((∑ j, |v j|) • (M ^ k *ᵥ allOnes n))) i at hh
    simpa only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] using hh

 theorem scaled_projection_ne_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, 0 ≤ M i j) {l : ℝ} (hl : 0 < l)
    {v : Fin n → ℝ} (hv : v ≠ 0) (he : M.mulVec v = l • v)
    {z : Fin n → ℝ}
    (hz : Tendsto (fun k : ℕ => (l ^ k)⁻¹ • (M ^ k).mulVec (allOnes n)) atTop (𝓝 z)) :
    z ≠ 0 ∧ ∀ k : ℕ, (M ^ k).mulVec (allOnes n) ≠ 0 := by
  have hpow : ∀ k : ℕ, (M ^ k).mulVec v = l ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, he, smul_smul, pow_succ]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    ext i
    simpa using not_exists.mp h i
  let D := ∑ j, |v j|
  have hD : 0 < D := Finset.sum_pos' (fun j _ => abs_nonneg _) ⟨i, Finset.mem_univ _, abs_pos.2 hi⟩
  have hb : ∀ k, |v i| ≤ D * ((l ^ k)⁻¹ • (M ^ k).mulVec (allOnes n)) i := by
    intro k
    have hh := power_abs_domination hM v k i
    rw [hpow] at hh
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (pow_pos hl k)] at hh ⊢
    dsimp [D] at *
    rw [mul_comm (l ^ k)] at hh
    apply (le_div_iff₀ (pow_pos hl k)).2 at hh
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm ((l ^ k)⁻¹)] using hh
  have hz' := (tendsto_pi_nhds.1 hz i).const_mul D
  have hvz : |v i| ≤ D * z i := ge_of_tendsto hz' (Filter.Eventually.of_forall hb)
  constructor
  · intro hz0
    simp only [hz0, Pi.zero_apply, mul_zero] at hvz
    exact (abs_pos.2 hi).not_ge hvz
  · intro k hk
    have hh := power_abs_domination hM v k i
    rw [hk, hpow] at hh
    simp only [Pi.zero_apply, mul_zero, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (pow_pos hl k)] at hh
    exact (mul_pos (pow_pos hl k) (abs_pos.2 hi)).not_ge hh

end KleinbergHITS.Conv.Proof
end ModuleScope_PositivePowers
-- End PositivePowers

-- Begin SpectrumBasic
section ModuleScope_SpectrumBasic

open scoped BigOperators RealInnerProductSpace
namespace KleinbergHITS.Conv.Proof

structure FiniteSpectrum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) where
  value : Fin n → ℝ
  vector : Fin n → Fin n → ℝ
  eigen : ∀ i, M.mulVec (vector i) = value i • vector i
  ortho : ∀ i j, ∑ x, vector i x * vector j x = if i=j then 1 else 0
  expand : ∀ (v : Fin n → ℝ) (x : Fin n), ∑ i,(∑ y,vector i y*v y)*vector i x=v x

noncomputable def finiteSpectrum {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) : FiniteSpectrum M := by
  let b := hM.eigenvectorBasis
  refine ⟨hM.eigenvalues,fun i => ⇑(b i),hM.mulVec_eigenvectorBasis,?_,?_⟩
  · intro i j
    have h := b.inner_eq_ite i j
    simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm] using h
  · intro v x
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z x)
      (b.sum_repr' (WithLp.toLp 2 v))
    simpa only [WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,
      smul_eq_mul,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm] using h

lemma eigen_pow {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {lam : ℝ}
    (hv : M.mulVec v=lam • v) (k : ℕ) : (M^k).mulVec v=lam^k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,hv]
    simp only [smul_smul,pow_succ',mul_comm]

namespace FiniteSpectrum
variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}

def coeff (s : FiniteSpectrum M) (v : Fin n → ℝ) (i : Fin n) : ℝ := ∑ y,s.vector i y*v y

lemma vector_ne_zero (s : FiniteSpectrum M) (i : Fin n) : s.vector i≠0 := by
  intro h
  have hh := s.ortho i i
  simp [h] at hh

lemma value_hasEigenvalue (s : FiniteSpectrum M) (i : Fin n) :
    Module.End.HasEigenvalue (Matrix.toLin' M) (s.value i) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
  exact ⟨Module.End.mem_eigenspace_iff.mpr (s.eigen i),s.vector_ne_zero i⟩

lemma pow_expand (s : FiniteSpectrum M) (v : Fin n → ℝ) (k : ℕ) (x : Fin n) :
    (M^k).mulVec v x=∑ i,s.coeff v i*s.value i^k*s.vector i x := by
  have he : v=∑ i,s.coeff v i • s.vector i := by
    funext y
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,coeff] using (s.expand v y).symm
  conv_lhs => rw [he,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,eigen_pow (s.eigen _),Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end FiniteSpectrum
end KleinbergHITS.Conv.Proof
end ModuleScope_SpectrumBasic
-- End SpectrumBasic

-- Begin EigenPositive
section ModuleScope_EigenPositive

open scoped BigOperators
namespace KleinbergHITS.Conv.Proof

lemma eigen_sum_sq_pos {n : ℕ} {v : Fin n → ℝ} (hv : v≠0) : 0<∑ i,v i^2 := by
  have hex : ∃ i,v i≠0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i,hi⟩ := hex
  exact (sq_pos_of_ne_zero hi).trans_le
    (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

lemma eigenvalue_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) {lam : ℝ} (hlam : Module.End.HasEigenvalue (Matrix.toLin' M) lam) : 0≤lam := by
  obtain ⟨v,hv⟩ := hlam.exists_hasEigenvector
  have he : M.mulVec v=lam • v := hv.apply_eq_smul
  have hp := hM.dotProduct_mulVec_nonneg v
  rw [he] at hp
  have hsum : dotProduct v (lam • v)=lam*(∑ i,v i^2) := by
    simp only [dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hh : 0 ≤ lam*(∑ i,v i^2) := by simpa only [star_trivial,hsum] using hp
  exact (mul_nonneg_iff_of_pos_right (eigen_sum_sq_pos hv.2)).mp hh

lemma principal_positive {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) {lam : ℝ} (hlam : IsPrincipalEigenvalue M lam) (hne : lam≠0) : 0<lam :=
  lt_of_le_of_ne (eigenvalue_nonneg hM hlam.1) hne.symm

lemma spectrum_ratio_lt {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) {lam : ℝ} (hlam : IsPrincipalEigenvalue M lam) (hne : lam≠0)
    (s : FiniteSpectrum M) (i : Fin n) (hi : s.value i≠lam) :
    0 ≤ s.value i/lam ∧ s.value i/lam < 1 := by
  have hl := principal_positive hM hlam hne
  have hv := eigenvalue_nonneg hM (s.value_hasEigenvalue i)
  have hb := hlam.2.2 (s.value i) (s.value_hasEigenvalue i) hi
  rw [abs_of_nonneg hv,abs_of_pos hl] at hb
  exact ⟨div_nonneg hv hl.le,(div_lt_one hl).mpr hb⟩

end KleinbergHITS.Conv.Proof
end ModuleScope_EigenPositive
-- End EigenPositive

-- Begin ScaledPower
section ModuleScope_ScaledPower

open Filter Topology
open scoped BigOperators
namespace KleinbergHITS.Conv.Proof

noncomputable def principalProjection {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (s : FiniteSpectrum M) (lam : ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun x => ∑ i,if s.value i=lam then s.coeff v i*s.vector i x else 0

lemma projection_eigen {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (s : FiniteSpectrum M) (lam : ℝ) (v : Fin n → ℝ) :
    M.mulVec (principalProjection s lam v)=lam • principalProjection s lam v := by
  classical
  have he : principalProjection s lam v=∑ i,if s.value i=lam then s.coeff v i • s.vector i else 0 := by
    funext x
    simp only [principalProjection,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> rfl
  rw [he,Matrix.mulVec_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : s.value i=lam
  · simp only [hi,if_pos,Matrix.mulVec_smul,s.eigen,smul_smul]
    congr 1
    ring
  · simp only [hi,if_false,Matrix.mulVec_zero,smul_zero]

lemma scaled_power_tendsto {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) {lam : ℝ} (hlam : IsPrincipalEigenvalue M lam) (hne : lam≠0)
    (s : FiniteSpectrum M) (v : Fin n → ℝ) :
    Tendsto (fun k : ℕ => (lam^k)⁻¹ • (M^k).mulVec v) atTop
      (𝓝 (principalProjection s lam v)) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro x
  have hterm (i : Fin n) :
      Tendsto (fun k : ℕ => s.coeff v i*(s.value i/lam)^k*s.vector i x) atTop
        (𝓝 (if s.value i=lam then s.coeff v i*s.vector i x else 0)) := by
    by_cases hi : s.value i=lam
    · simp only [hi,if_pos,div_self hne,one_pow,mul_one]
      exact tendsto_const_nhds
    · have hr := spectrum_ratio_lt hM hlam hne s i hi
      have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2).const_mul (s.coeff v i)).mul_const (s.vector i x)
      simpa only [hi,if_false,mul_zero,zero_mul] using hh
  have hh := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  change Tendsto _ atTop (𝓝 (∑ i,if s.value i=lam then s.coeff v i*s.vector i x else 0))
  convert hh using 1
  funext k
  simp only [Pi.smul_apply,smul_eq_mul,s.pow_expand,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_pow]
  ring

lemma exists_scaled_power_limit {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) {lam : ℝ} (hlam : IsPrincipalEigenvalue M lam) (hne : lam≠0)
    (v : Fin n → ℝ) :
    ∃ z : Fin n → ℝ,
      Tendsto (fun k : ℕ => (lam^k)⁻¹ • (M^k).mulVec v) atTop (𝓝 z) ∧
      M.mulVec z=lam • z := by
  let s := finiteSpectrum hM.1
  exact ⟨principalProjection s lam v,scaled_power_tendsto hM hlam hne s v,projection_eigen s lam v⟩

end KleinbergHITS.Conv.Proof
end ModuleScope_ScaledPower
-- End ScaledPower

-- Begin NativeMatrix
section ModuleScope_NativeMatrix

open scoped BigOperators
namespace KleinbergHITS.Conv.Proof
open Matrix

 theorem opI_matrix {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (v : Fin n → ℝ) :
    opI E v = (adjMatrix E)ᵀ.mulVec v := by
  ext i
  simp [opI, Matrix.mulVec, dotProduct, adjMatrix, Finset.sum_filter]

 theorem opO_matrix {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (v : Fin n → ℝ) :
    opO E v = (adjMatrix E).mulVec v := by
  ext i
  simp [opO, Matrix.mulVec, dotProduct, adjMatrix, Finset.sum_filter]

 theorem adj_nonneg {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (i j : Fin n) :
    0 ≤ adjMatrix E i j := by
  unfold adjMatrix
  split_ifs <;> norm_num

 theorem gram_nonneg {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (i j : Fin n) :
    0 ≤ (adjMatrix E * (adjMatrix E)ᵀ) i j := by
  change 0 ≤ ∑ k, adjMatrix E i k * adjMatrix E j k
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (adj_nonneg E i k) (adj_nonneg E j k))

 theorem gram_left_psd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : (Aᵀ * A).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self A

 theorem gram_right_psd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : (A * Aᵀ).PosSemidef := by
  simpa only [transpose_transpose] using gram_left_psd Aᵀ

 theorem hits_succ_matrix {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (k : ℕ) :
    hitsIter E (k+1) =
      (normalize ((adjMatrix E)ᵀ.mulVec (hitsIter E k).2),
       normalize ((adjMatrix E * (adjMatrix E)ᵀ).mulVec (hitsIter E k).2)) := by
  simp only [hitsIter, opI_matrix, opO_matrix, Matrix.mulVec_mulVec]

end KleinbergHITS.Conv.Proof
end ModuleScope_NativeMatrix
-- End NativeMatrix

-- Begin NativeIteration
section ModuleScope_NativeIteration

open scoped BigOperators
namespace KleinbergHITS.Conv.Proof
open Matrix

 theorem hits_power_y {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E]
    (hb : ∀ k : ℕ, ((adjMatrix E * (adjMatrix E)ᵀ)^k).mulVec (allOnes n) ≠ 0) :
    ∀ k : ℕ, (hitsIter E (k+1)).2 = normalize (((adjMatrix E * (adjMatrix E)ᵀ)^(k+1)).mulVec (allOnes n)) := by
  let B := adjMatrix E * (adjMatrix E)ᵀ
  intro k
  induction k with
  | zero => simp [hitsIter, opI_matrix, opO_matrix, Matrix.mulVec_mulVec]
  | succ k ih =>
    rw [hits_succ_matrix]
    change normalize (B.mulVec (hitsIter E (k+1)).2) = normalize ((B^(k+1+1)).mulVec (allOnes n))
    rw [ih]
    change normalize (_ *ᵥ ((Real.sqrt (∑ i, ((((adjMatrix E * (adjMatrix E)ᵀ)^(k+1)).mulVec (allOnes n)) i)^2))⁻¹ • _)) = _
    rw [Matrix.mulVec_smul, normalize_smul_pos _ (inv_pos.2 (Real.sqrt_pos.2 (sum_sq_pos (hb (k+1)))))]
    change normalize (B.mulVec ((B^(k+1)).mulVec (allOnes n))) = _
    rw [Matrix.mulVec_mulVec, ← pow_succ']

 theorem hits_power_x {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E]
    (hb : ∀ k : ℕ, ((adjMatrix E * (adjMatrix E)ᵀ)^k).mulVec (allOnes n) ≠ 0) (k : ℕ) :
    (hitsIter E (k+1)).1 = normalize ((adjMatrix E)ᵀ.mulVec (((adjMatrix E * (adjMatrix E)ᵀ)^k).mulVec (allOnes n))) := by
  cases k with
  | zero => simp [hitsIter, opI_matrix, opO_matrix, Matrix.mulVec_mulVec]
  | succ k =>
    rw [hits_succ_matrix]
    change normalize ((adjMatrix E)ᵀ.mulVec (hitsIter E (k+1)).2) = _
    rw [hits_power_y E hb k]
    change normalize (_ *ᵥ ((Real.sqrt (∑ i, ((((adjMatrix E * (adjMatrix E)ᵀ)^(k+1)).mulVec (allOnes n)) i)^2))⁻¹ • _)) = _
    rw [Matrix.mulVec_smul, normalize_smul_pos _ (inv_pos.2 (Real.sqrt_pos.2 (sum_sq_pos (hb (k+1)))))]

end KleinbergHITS.Conv.Proof
end ModuleScope_NativeIteration
-- End NativeIteration

-- Begin GramTransfer
section ModuleScope_GramTransfer

open scoped BigOperators
namespace KleinbergHITS.Conv.Proof
open Matrix

 theorem gram_transfer_nonzero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {v : Fin n → ℝ} (hv : v ≠ 0) {l : ℝ} (hl : l ≠ 0)
    (he : (A * Aᵀ).mulVec v = l • v) :
    Aᵀ.mulVec v ≠ 0 ∧ (Aᵀ * A).mulVec (Aᵀ.mulVec v) = l • Aᵀ.mulVec v := by
  constructor
  · intro h
    have hh : l • v = 0 := by
      rw [← he, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    exact hv ((smul_eq_zero.mp hh).resolve_left hl)
  · have hh := congrArg (fun w => Aᵀ.mulVec w) he
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mulVec_smul] using hh

 theorem eigenvalue_of_equation {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    {v : Fin n → ℝ} (hv : v ≠ 0) {l : ℝ} (he : M.mulVec v = l • v) :
    Module.End.HasEigenvalue (Matrix.toLin' M) l := by
  exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩

 theorem gram_principal_transfer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {l : ℝ} (hB : IsPrincipalEigenvalue (A * Aᵀ) l) (hl : l ≠ 0)
    (hC : Dagger (Aᵀ * A)) : IsPrincipalEigenvalue (Aᵀ * A) l := by
  obtain ⟨m, hm, hm0⟩ := hC
  obtain ⟨v, hv⟩ := hB.1.exists_hasEigenvector
  have hv' := gram_transfer_nonzero A hv.2 hl hv.apply_eq_smul
  have hlC := eigenvalue_of_equation hv'.1 hv'.2
  obtain ⟨w, hw⟩ := hm.1.exists_hasEigenvector
  have hw' := gram_transfer_nonzero Aᵀ hw.2 hm0 (by simpa only [transpose_transpose] using (show (Aᵀ * A).mulVec w = m • w from hw.apply_eq_smul))
  have hmB : Module.End.HasEigenvalue (Matrix.toLin' (A * Aᵀ)) m := by
    simpa only [transpose_transpose] using eigenvalue_of_equation hw'.1 hw'.2
  have heq : l = m := by
    by_contra h
    have h1 := hm.2.2 l hlC h
    have h2 := hB.2.2 m hmB (Ne.symm h)
    exact (lt_asymm h1 h2)
  simpa only [heq] using hm

end KleinbergHITS.Conv.Proof
end ModuleScope_GramTransfer
-- End GramTransfer

-- Begin PowerConvergence
section ModuleScope_PowerConvergence

open scoped BigOperators
namespace KleinbergHITS.Conv.Proof
open Matrix Filter Topology

 theorem hits_converges {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E]
    (hAtA : Dagger ((adjMatrix E)ᵀ * adjMatrix E))
    (hAAt : Dagger (adjMatrix E * (adjMatrix E)ᵀ)) :
    ∃ xstar ystar : Fin n → ℝ,
      Tendsto (fun k => (hitsIter E k).1) atTop (𝓝 xstar) ∧
      Tendsto (fun k => (hitsIter E k).2) atTop (𝓝 ystar) ∧
      IsPrincipalEigenvector ((adjMatrix E)ᵀ * adjMatrix E) xstar ∧
      IsPrincipalEigenvector (adjMatrix E * (adjMatrix E)ᵀ) ystar := by
  let A := adjMatrix E
  let B := A * Aᵀ
  obtain ⟨l, hl, hl0⟩ := hAAt
  have hlp := principal_positive (gram_right_psd A) hl hl0
  obtain ⟨z, hz, hze⟩ := exists_scaled_power_limit (gram_right_psd A) hl hl0 (allOnes n)
  obtain ⟨v, hv⟩ := hl.1.exists_hasEigenvector
  have hzn := scaled_projection_ne_zero (gram_nonneg E) hlp hv.2 hv.apply_eq_smul hz
  have ht := gram_transfer_nonzero A hzn.1 hl0 hze
  have hn : Tendsto (fun k : ℕ => normalize ((B^k).mulVec (allOnes n))) atTop (𝓝 (normalize z)) := by
    have h := (continuousAt_normalize hzn.1).tendsto.comp hz
    have heq : (fun k : ℕ => normalize ((l^k)⁻¹ • (B^k).mulVec (allOnes n))) =
        (fun k : ℕ => normalize ((B^k).mulVec (allOnes n))) := by
      funext k
      exact normalize_smul_pos _ (inv_pos.2 (pow_pos hlp k))
    change Tendsto (fun k : ℕ => normalize ((l^k)⁻¹ • (B^k).mulVec (allOnes n))) atTop _ at h
    rwa [heq] at h
  have hAt : Continuous (fun w : Fin n → ℝ => Aᵀ.mulVec w) := by
    apply continuous_pi
    intro i
    change Continuous (fun w : Fin n → ℝ => ∑ j, Aᵀ i j * w j)
    exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j))
  have hxn : Tendsto (fun k : ℕ => normalize (Aᵀ.mulVec ((B^k).mulVec (allOnes n)))) atTop
      (𝓝 (normalize (Aᵀ.mulVec z))) := by
    have h := (continuousAt_normalize ht.1).tendsto.comp (hAt.continuousAt.tendsto.comp hz)
    have heq : (fun k : ℕ => normalize (Aᵀ.mulVec ((l^k)⁻¹ • (B^k).mulVec (allOnes n)))) =
        (fun k : ℕ => normalize (Aᵀ.mulVec ((B^k).mulVec (allOnes n)))) := by
      funext k
      rw [Matrix.mulVec_smul, normalize_smul_pos _ (inv_pos.2 (pow_pos hlp k))]
    change Tendsto (fun k : ℕ => normalize (Aᵀ.mulVec ((l^k)⁻¹ • (B^k).mulVec (allOnes n)))) atTop _ at h
    rwa [heq] at h
  refine ⟨normalize (Aᵀ.mulVec z), normalize z, ?_, ?_, ?_, ?_⟩
  · apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [hits_power_x E hzn.2] using hxn
  · apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [hits_power_y E hzn.2] using ((tendsto_add_atTop_iff_nat 1).2 hn)
  · exact ⟨l, gram_principal_transfer A hl hl0 hAtA, normalize_eigen ht.2, normalize_unit ht.1⟩
  · exact ⟨l, hl, normalize_eigen hze, normalize_unit hzn.1⟩

end KleinbergHITS.Conv.Proof
end ModuleScope_PowerConvergence
-- End PowerConvergence

-- Begin RootAssembly
section ModuleScope_RootAssembly

namespace KleinbergHITS.Conv

open Matrix Filter Topology

/-- Kleinberg (1999), §3, Theorems 3.1 and 3.2, pp. 10–11: under Assumption (†) for `AᵀA` and `AAᵀ`,
the `Iterate` sequences converge to limits `x*` and `y*`, and `x*` is the principal eigenvector of
`AᵀA` and `y*` is the principal eigenvector of `AAᵀ`. -/
theorem theorem_3_2 {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E]
    (hAtA : Dagger ((adjMatrix E)ᵀ * adjMatrix E)) (hAAt : Dagger (adjMatrix E * (adjMatrix E)ᵀ)) :
    ∃ xstar ystar : Fin n → ℝ,
      Tendsto (fun k => (hitsIter E k).1) atTop (𝓝 xstar) ∧
      Tendsto (fun k => (hitsIter E k).2) atTop (𝓝 ystar) ∧
      IsPrincipalEigenvector ((adjMatrix E)ᵀ * adjMatrix E) xstar ∧
      IsPrincipalEigenvector (adjMatrix E * (adjMatrix E)ᵀ) ystar := by
  exact Proof.hits_converges E hAtA hAAt

end KleinbergHITS.Conv
end ModuleScope_RootAssembly
-- End RootAssembly

-- Begin Solution
section ModuleScope_Solution

open Matrix Filter Topology KleinbergHITS.Conv

theorem solution {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E]
    (hAtA : Dagger ((adjMatrix E)ᵀ * adjMatrix E)) (hAAt : Dagger (adjMatrix E * (adjMatrix E)ᵀ)) :
    ∃ xstar ystar : Fin n → ℝ,
      Tendsto (fun k => (hitsIter E k).1) atTop (𝓝 xstar) ∧
      Tendsto (fun k => (hitsIter E k).2) atTop (𝓝 ystar) ∧
      IsPrincipalEigenvector ((adjMatrix E)ᵀ * adjMatrix E) xstar ∧
      IsPrincipalEigenvector (adjMatrix E * (adjMatrix E)ᵀ) ystar := by
  exact KleinbergHITS.Conv.theorem_3_2 E hAtA hAAt

end ModuleScope_Solution
-- End Solution
