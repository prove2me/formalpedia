-- Prove2me | solution 1 for MixedCloning.Optimal.proposition_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:07:48.326429+00:00
-- url     : https://prove2.me/submissions/ea7a5cbd-cacb-4d14-ac68-f9b97873ca2e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MixedCloning_Optimal_lemma_12
import Theorems.Thm_MixedCloning_Optimal_lemma_13
import Theorems.Thm_MixedCloning_Optimal_lemma_14
import Theorems.Thm_MixedCloning_Optimal_lemma_16
import Theorems.Thm_MixedCloning_Optimal_lemma_17
import Theorems.Thm_MixedCloning_Optimal_lemma_19

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## Reindexing (copied from the proved `fidelity_le_partialTrace` solution) -/

section Reindex
open scoped MatrixOrder
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Reindexing a matrix by an equivalence commutes with the square-root functional calculus. -/
lemma fdp_cfc_sqrt_reindex (e : m ≃ n) (A : Matrix m m ℂ) :
    cfc Real.sqrt (reindex e e A) = reindex e e (cfc Real.sqrt A) := by
  let φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ :=
    { (reindexAlgEquiv ℂ ℂ e).toAlgHom with
      map_star' := fun X => by
        change reindex e e (star X) = star (reindex e e X)
        simp [Matrix.star_eq_conjTranspose] }
  have hφ : Continuous φ := continuous_id.matrix_reindex e e
  have hφA : ∀ X, φ X = reindex e e X := fun X => rfl
  by_cases hA : IsSelfAdjoint A
  · have hA' : IsSelfAdjoint (φ A) := hA.map φ
    have h := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) φ Real.sqrt A
      Real.continuous_sqrt.continuousOn hφ hA hA'
    rw [hφA, hφA] at h
    exact h.symm
  · have hA' : ¬ IsSelfAdjoint (reindex e e A) := by
      intro h
      apply hA
      have h2 : reindex e e (star A) = reindex e e A := by
        have h3 := h.star_eq
        rwa [Matrix.star_eq_conjTranspose, conjTranspose_reindex,
          ← Matrix.star_eq_conjTranspose] at h3
      exact (reindex e e).injective h2
    rw [cfc_apply_of_not_predicate A hA, cfc_apply_of_not_predicate _ hA']
    simp

/-- Trace is invariant under reindexing. -/
lemma fdp_trace_reindex (e : m ≃ n) (A : Matrix m m ℂ) : (reindex e e A).trace = A.trace := by
  simp only [Matrix.trace, reindex_apply, submatrix_apply, diag_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

/-- The root fidelity is invariant under reindexing both arguments by the same equivalence. -/
lemma fdp_rootFidelity_reindex (e : m ≃ n) (X Y : Matrix m m ℂ) :
    QAlgorithms.rootFidelity (reindex e e X) (reindex e e Y) = QAlgorithms.rootFidelity X Y := by
  have hmul : ∀ A B : Matrix m m ℂ, reindex e e A * reindex e e B = reindex e e (A * B) := by
    intro A B
    simp [reindex_apply, submatrix_mul_equiv]
  unfold QAlgorithms.rootFidelity
  rw [fdp_cfc_sqrt_reindex, hmul, hmul, fdp_cfc_sqrt_reindex, fdp_trace_reindex]

end Reindex

/-! ## Tensor powers -/

lemma p11_tensorPower_mul {a : Type} [Fintype a] (m : ℕ) (A B : Op a) :
    tensorPower m A * tensorPower m B = tensorPower m (A * B) := by
  ext i j
  simp only [tensorPower, Matrix.mul_apply]
  rw [Fintype.prod_sum (fun t l => A (i t) l * B l (j t))]
  simp only [Finset.prod_mul_distrib]

lemma p11_tensorPower_conjTranspose {a : Type} (m : ℕ) (A : Op a) :
    (tensorPower m A)ᴴ = tensorPower m Aᴴ := by
  ext i j
  simp [tensorPower, Matrix.conjTranspose_apply]

lemma p11_tensorPower_trace {a : Type} [Fintype a] (m : ℕ) (A : Op a) :
    (tensorPower m A).trace = A.trace ^ m := by
  simp only [Matrix.trace, Matrix.diag, tensorPower]
  rw [← Fintype.prod_sum (fun (_ : Fin m) j => A j j)]
  simp [Finset.prod_const]

lemma p11_tensorPower_projectorState {a : Type} (m r : ℕ) (P : Op a) :
    tensorPower m (projectorState r P) = projectorState (r^m) (tensorPower m P) := by
  ext i j
  simp only [tensorPower, projectorState, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [inv_pow]

/-! ## Projectors and states -/

/-- The trace of an idempotent matrix is its rank. -/
lemma p11_idem_trace {a : Type} [Fintype a] [DecidableEq a] (Q : Op a) (hQ : Q * Q = Q) :
    Q.trace = (Q.rank : ℂ) := by
  have hI : IsIdempotentElem (Matrix.toLin' Q) := by
    show Matrix.toLin' Q * Matrix.toLin' Q = Matrix.toLin' Q
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hQ]
  have h := LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ hI)
  rw [Matrix.trace_toLin'_eq] at h
  rw [h]
  rfl

/-- A rank-`s` orthogonal projector has trace `s`. -/
lemma p11_projector_trace (d s : ℕ) (P : Op (Fin d)) (hP : IsProjector s P) :
    P.trace = s := by
  rw [p11_idem_trace P hP.2.1, hP.2.2]

/-- A Hermitian idempotent is positive semidefinite. -/
lemma p11_idem_psd {a : Type} [Fintype a] (Q : Op a) (hh : Q.IsHermitian) (hi : Q * Q = Q) :
    Q.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self Q
  rwa [hh.eq, hi] at h

/-- `Q/s` is a state for a Hermitian idempotent `Q` of trace `s ≥ 1`. -/
lemma p11_projState_isState {a : Type} [Fintype a] (s : ℕ) (hs : 1 ≤ s) (Q : Op a)
    (hh : Q.IsHermitian) (hi : Q * Q = Q) (ht : Q.trace = s) : IsState (projectorState s Q) := by
  have hpsd := p11_idem_psd Q hh hi
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have hc : (0 : ℂ) ≤ (s : ℂ)⁻¹ := by
    have : (s : ℂ)⁻¹ = (((s : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact Complex.zero_le_real.mpr (by positivity)
  refine ⟨hpsd.smul hc, ?_⟩
  simp only [projectorState, Matrix.trace_smul, ht, smul_eq_mul]
  exact inv_mul_cancel₀ hs'

/-- Tensor powers of a rank-`r` projector: Hermitian, idempotent, trace `r^m`. -/
lemma p11_tensorPower_projector (d r m : ℕ) (P : Op (Fin d)) (hP : IsProjector r P) :
    (tensorPower m P).IsHermitian ∧ tensorPower m P * tensorPower m P = tensorPower m P ∧
      (tensorPower m P).trace = ((r^m : ℕ) : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · show (tensorPower m P)ᴴ = tensorPower m P
    rw [p11_tensorPower_conjTranspose, hP.1.eq]
  · rw [p11_tensorPower_mul, hP.2.1]
  · rw [p11_tensorPower_trace, p11_projector_trace d r P hP]
    push_cast
    rfl

/-- Channels in Kraus form map states to states. -/
lemma p11_channel_state {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {Φ : QAlgorithms.Superop ι κ} (hΦ : QAlgorithms.IsChannel Φ) {ρ : Op ι} (hρ : IsState ρ) :
    IsState (Φ ρ) := by
  obtain ⟨N, E, hE, hΦE⟩ := hΦ
  rw [hΦE]
  unfold QAlgorithms.krausApply
  refine ⟨Matrix.posSemidef_sum _ fun j _ => hρ.1.mul_mul_conjTranspose_same (E j), ?_⟩
  have h : ∀ j, (E j * ρ * (E j)ᴴ).trace = ((E j)ᴴ * E j * ρ).trace := fun j => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [Matrix.trace_sum]
  simp_rw [h]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  unfold QAlgorithms.IsKrausFamily at hE
  rw [hE, Matrix.one_mul]
  exact hρ.2

/-! ## Step 1: fidelity is at most the overlap -/

lemma p11_fidelity_le_overlap (d r n m : ℕ) (hr : 1 ≤ r) (C : Cloner d n m)
    (hC : QAlgorithms.IsChannel C) (P : Op (Fin d)) (hP : IsProjector r P) :
    fidelity (C (tensorPower n (projectorState r P))) (tensorPower m (projectorState r P)) ≤
      overlap d r n m C P := by
  obtain ⟨hnh, hni, hnt⟩ := p11_tensorPower_projector d r n P hP
  obtain ⟨hmh, hmi, hmt⟩ := p11_tensorPower_projector d r m P hP
  have hin : IsState (tensorPower n (projectorState r P)) := by
    rw [p11_tensorPower_projectorState]
    exact p11_projState_isState (r^n) (Nat.one_le_pow _ _ hr) _ hnh hni hnt
  have hσ : IsState (C (tensorPower n (projectorState r P))) := p11_channel_state hC hin
  unfold overlap
  rw [p11_tensorPower_projectorState m r P]
  set σ := C (tensorPower n (projectorState r P)) with hσdef
  set Pm := tensorPower m P with hPmdef
  let e := Fintype.equivFin (Word (Fin d) m)
  have hmul : ∀ A B : Op (Word (Fin d) m), reindex e e A * reindex e e B = reindex e e (A * B) := by
    intro A B
    simp [reindex_apply, submatrix_mul_equiv]
  have hrank : Pm.rank = r^m := by
    have h := p11_idem_trace Pm hmi
    rw [hmt] at h
    exact_mod_cast h.symm
  have hproj : IsProjector (r^m) (reindex e e Pm) := by
    refine ⟨?_, ?_, ?_⟩
    · exact hmh.submatrix e.symm
    · rw [hmul, hmi]
    · rw [Matrix.rank_reindex, hrank]
  have hstate : IsState (reindex e e σ) := by
    refine ⟨?_, ?_⟩
    · exact (Matrix.posSemidef_submatrix_equiv e.symm).mpr hσ.1
    · rw [fdp_trace_reindex]; exact hσ.2
  have h12 := lemma_12 _ (r^m) (reindex e e Pm) (reindex e e σ) hproj hstate
  have hps : projectorState (r^m) (reindex e e Pm) = reindex e e (projectorState (r^m) Pm) := by
    ext i j
    simp [projectorState, reindex_apply]
  rw [hps, hmul, fdp_trace_reindex] at h12
  unfold fidelity at h12 ⊢
  rw [fdp_rootFidelity_reindex] at h12
  exact h12

/-! ## Step 4 glue: the operator norm of the transposed integral -/

lemma p11_rotatedProjector {d : ℕ} (r : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (rotatedProjector r U)ᴴ = rotatedProjector r U ∧
      rotatedProjector r U * rotatedProjector r U = rotatedProjector r U := by
  have hB : (baseProjector d r)ᴴ = baseProjector d r := by
    unfold baseProjector
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : d - r ≤ (i : ℕ)
    · simp only [Pi.star_apply, if_pos h, star_one]
    · simp only [Pi.star_apply, if_neg h, star_zero]
  have hBB : baseProjector d r * baseProjector d r = baseProjector d r := by
    unfold baseProjector
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : d - r ≤ (i : ℕ)
    · simp only [if_pos h, mul_one]
    · simp only [if_neg h, mul_zero]
  have hU : (U : Op (Fin d))ᴴ * (U : Op (Fin d)) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp U.2
    rwa [Matrix.star_eq_conjTranspose] at this
  unfold rotatedProjector
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hB,
      Matrix.mul_assoc]
  · calc (U : Op (Fin d)) * baseProjector d r * (U : Op (Fin d))ᴴ *
          ((U : Op (Fin d)) * baseProjector d r * (U : Op (Fin d))ᴴ)
        = (U : Op (Fin d)) * baseProjector d r * ((U : Op (Fin d))ᴴ * (U : Op (Fin d))) *
            baseProjector d r * (U : Op (Fin d))ᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc (U : Op (Fin d)), hBB]

lemma p11_cellTensor_mul (L : YoungDiagram) {d : ℕ} (A B : Op (Fin d)) :
    cellTensor L A * cellTensor L B = cellTensor L (A * B) := by
  ext i j
  simp only [cellTensor, Matrix.mul_apply]
  rw [Fintype.prod_sum (fun c l => A (i c) l * B l (j c))]
  simp only [Finset.prod_mul_distrib]

lemma p11_cellTensor_conjTranspose (L : YoungDiagram) {d : ℕ} (A : Op (Fin d)) :
    (cellTensor L A)ᴴ = cellTensor L Aᴴ := by
  ext i j
  simp [cellTensor, Matrix.conjTranspose_apply]

lemma p11_cellTensor_psd (L : YoungDiagram) {d : ℕ} (P : Op (Fin d)) (hh : Pᴴ = P)
    (hi : P * P = P) : (cellTensor L P).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (cellTensor L P)
  rwa [p11_cellTensor_conjTranspose, hh, p11_cellTensor_mul, hi] at h

lemma p11_q_psd (L : YoungDiagram) {d : ℕ} (b : SchurBasis L d) (P : Op (Fin d)) (hh : Pᴴ = P)
    (hi : P * P = P) : (q L b P).PosSemidef := by
  have hT : (Matrix.toEuclideanLin (cellTensor L P)).toContinuousLinearMap.IsPositive := by
    rw [LinearMap.isPositive_toContinuousLinearMap_iff, Matrix.isPositive_toEuclideanLin_iff]
    exact p11_cellTensor_psd L P hh hi
  have h := hT.conj_adjoint (F := ↥(schurModule L d)) (schurModule L d).orthogonalProjectionOnto
  rw [Submodule.adjoint_orthogonalProjectionOnto,
    ← ContinuousLinearMap.isPositive_toLinearMap_iff] at h
  unfold q
  refine (LinearMap.posSemidef_toMatrix_iff b).mpr ?_
  convert h using 1
  all_goals rfl

lemma p11_isClosed_psd {ι : Type} [Fintype ι] : IsClosed {A : Op ι | A.PosSemidef} := by
  have h : {A : Op ι | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : ι → ℂ, {A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by
    ext A
    simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [h]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  fun_prop

lemma p11_transposedIntegral_psd {d : ℕ} (r : ℕ) (L M : YoungDiagram) (b : SchurBasis L d)
    (c : SchurBasis M d) : (transposedIntegral r L M b c).PosSemidef := by
  unfold transposedIntegral
  by_cases hi : (∫ U, Matrix.kronecker (q L b (rotatedProjector r U)).transpose
      (q M c (rotatedProjector r U)) ∂haar d) = 0
  · rw [hi]
    exact Matrix.PosSemidef.zero
  · refine Convex.integral_mem (s := {A | A.PosSemidef}) ?_ ?_
      (Filter.Eventually.of_forall fun U => ?_) (Integrable.of_integral_ne_zero hi)
    · intro A hA B hB a b ha hb _
      exact (Matrix.PosSemidef.smul hA ha).add (Matrix.PosSemidef.smul hB hb)
    · exact p11_isClosed_psd
    · obtain ⟨hh, hi'⟩ := p11_rotatedProjector r U
      exact Matrix.PosSemidef.kronecker
        (Matrix.posSemidef_transpose_iff.mpr (p11_q_psd L b _ hh hi')) (p11_q_psd M c _ hh hi')

/-- `0 ⪯ T ⪯ c·1` gives `‖T‖_∞ ≤ c`. -/
lemma p11_opnorm_le_of_loewner {ι : Type} [Fintype ι] [DecidableEq ι] (T : Op ι) (c : ℝ)
    (hc : 0 ≤ c) (h0 : T.PosSemidef) (h1 : ((c : ℂ) • (1 : Op ι) - T).PosSemidef) :
    operatorNorm T ≤ c := by
  have hpos : ∀ X : Op ι, X.PosSemidef → 0 ≤ Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) X := by
    intro X hX
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ← ContinuousLinearMap.isPositive_toLinearMap_iff,
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.isPositive_toEuclideanLin_iff]
    exact hX
  have hA : (Matrix.toEuclideanLin T).toContinuousLinearMap =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) T := rfl
  unfold operatorNorm
  have halg : algebraMap ℝ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) c =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) ((c : ℂ) • (1 : Op ι)) := by
    rw [map_smul, map_one, Algebra.algebraMap_eq_smul_one]
    ext x i
    simp
  rw [hA, CStarAlgebra.norm_le_iff_le_algebraMap _ hc (hpos T h0), ← sub_nonneg, halg, ← map_sub]
  exact hpos _ h1

lemma p11_opnorm_le (d r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d) (L M : YoungDiagram)
    (hL : height L ≤ d) (hM : height M ≤ d) (b : SchurBasis L d) (c : SchurBasis M d) :
    operatorNorm (transposedIntegral r L M b c) ≤ ratio (L ⊔ M) r d := by
  have hc : 0 ≤ ratio (L ⊔ M) r d := by unfold ratio; positivity
  exact p11_opnorm_le_of_loewner _ _ hc (p11_transposedIntegral_psd r L M b c)
    (lemma_19 d r hr hrd L M hL hM b c)

/-! ## Steps 5–6: the WSS sum -/

lemma p11_mem_partitions {n r : ℕ} {L : YoungDiagram} (h : L ∈ partitions n r) :
    L.card = n ∧ height L ≤ r := by
  unfold partitions at h
  rw [Finset.mem_filter] at h
  refine ⟨h.2, ?_⟩
  unfold diagramsInBox at h
  obtain ⟨S, hS, hL⟩ := Finset.mem_biUnion.mp h.1
  split_ifs at hL with hs
  · rw [Finset.mem_singleton] at hL
    subst hL
    unfold height
    by_contra hc
    push_neg at hc
    have hmem : (r, 0) ∈ (⟨S, hs⟩ : YoungDiagram) := YoungDiagram.mem_iff_lt_colLen.mpr hc
    have := Finset.mem_powerset.mp hS hmem
    simp at this
  · simp at hL

lemma p11_extraProduct_nonneg (d r k : ℕ) (L : YoungDiagram) : 0 ≤ extraProduct d r k L := by
  unfold extraProduct
  exact Finset.prod_nonneg fun j _ => by positivity

lemma p11_sum_le (d r n k : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d) :
    ∑ L ∈ partitions n r, (spechtDim L : ℝ) * schurCount L d / (r : ℝ)^n *
      sSup ((partitions (n+k) r).image fun M =>
        operatorNorm (transposedIntegral r L M (schurBasis L d) (schurBasis M d))) ≤
    wssExpectation n r (extraProduct d r k) := by
  unfold wssExpectation
  apply Finset.sum_le_sum
  intro L hL
  obtain ⟨hLc, hLh⟩ := p11_mem_partitions hL
  obtain ⟨-, hmax, heq⟩ := lemma_16 d r n k hr hrd L hLc hLh
  have hS : sSup (((partitions (n+k) r).image fun M =>
        operatorNorm (transposedIntegral r L M (schurBasis L d) (schurBasis M d))) : Set ℝ) ≤
      ratio L r d * extraProduct d r k L := by
    rw [← heq]
    apply Real.sSup_le
    · intro x hx
      rw [Finset.coe_image] at hx
      obtain ⟨M, hM, rfl⟩ := hx
      obtain ⟨hMc, hMh⟩ := p11_mem_partitions (Finset.mem_coe.mp hM)
      exact (p11_opnorm_le d r hr hrd L M (hLh.trans hrd) (hMh.trans hrd) _ _).trans
        (hmax M hMc (hMh.trans hrd))
    · rw [heq]
      exact mul_nonneg (by unfold ratio; positivity) (p11_extraProduct_nonneg d r k L)
  have hcoef : 0 ≤ (spechtDim L : ℝ) * schurCount L d / (r : ℝ)^n := by positivity
  refine (mul_le_mul_of_nonneg_left hS hcoef).trans ?_
  have hrn : ((r : ℝ))^n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show r ≠ 0 by omega))
  by_cases h0 : (schurCount L d : ℝ) = 0
  · rw [h0]
    simp only [mul_zero, zero_div, zero_mul]
    exact mul_nonneg (by positivity) (p11_extraProduct_nonneg d r k L)
  · apply le_of_eq
    unfold ratio
    field_simp

/-! ## Proposition 11 -/

theorem solution (d r n k : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : 2*r ≤ d)
    (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) (heps16 : eps ≤ 1/16)
    (C : Cloner d n (n+k)) (hC : QAlgorithms.IsChannel C)
    (hclone : ∀ P : Op (Fin d), IsProjector r P →
      1-eps ≤ fidelity (C (tensorPower n (projectorState r P)))
        (tensorPower (n+k) (projectorState r P))) :
    (k : ℝ)*r*d/(8*eps) ≤ n := by
  have hrd' : r ≤ d := by omega
  -- Step 1: fidelity ≤ overlap (Lemma 12)
  have hov : ∀ P : Op (Fin d), IsProjector r P → 1 - eps ≤ overlap d r n (n+k) C P :=
    fun P hP => (hclone P hP).trans (p11_fidelity_le_overlap d r n (n+k) hr C hC P hP)
  -- Step 2: permutation invariance (Lemma 13)
  obtain ⟨Cbar, hCbar, hperm, hsame, -, -⟩ := lemma_13 d r n (n+k) hr hrd' C hC
  -- Step 3: Schur-basis bound (Lemma 14)
  obtain ⟨P, hP, hle⟩ := lemma_14 d r n (n+k) hr hrd' Cbar hCbar hperm (fun L => schurBasis L d)
  -- Steps 4–6: Lemmas 19 and 16 turn the bound into the WSS expectation
  have h1 : 1 - eps ≤ wssExpectation n r (extraProduct d r k) :=
    calc 1 - eps ≤ overlap d r n (n+k) C P := hov P hP
      _ = overlap d r n (n+k) Cbar P := (hsame P hP).symm
      _ ≤ _ := hle
      _ ≤ wssExpectation n r (extraProduct d r k) := p11_sum_le d r n k hr hrd'
  -- Step 7: Lemma 17
  exact lemma_17 d r n k hd hr hrd hk eps heps heps16 h1
