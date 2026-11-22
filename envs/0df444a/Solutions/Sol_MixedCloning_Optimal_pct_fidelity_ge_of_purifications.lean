-- Prove2me | solution 1 for MixedCloning.Optimal.pct_fidelity_ge_of_purifications
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:13:14.643155+00:00
-- url     : https://prove2.me/submissions/470a688c-5181-486a-8e6e-523d5c4e03ff

import Theorems.Thm_MixedCloning_Optimal_werner_pure_fidelity
import Theorems.Thm_MayersBC_fuchs_caves

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## Square roots and positivity (`MatrixOrder` only locally) -/

section Positivity
open scoped MatrixOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The root fidelity is nonnegative: it is the trace of a positive semidefinite square root. -/
lemma pfp_rootFidelity_nonneg (X Y : Matrix ι ι ℂ) : 0 ≤ QAlgorithms.rootFidelity X Y := by
  unfold QAlgorithms.rootFidelity
  have h : (0 : Matrix ι ι ℂ) ≤ cfc Real.sqrt (cfc Real.sqrt X * Y * cfc Real.sqrt X) :=
    cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
  have ht := (Matrix.nonneg_iff_posSemidef.mp h).trace_nonneg
  exact (Complex.nonneg_iff.mp ht).1

/-- `Re tr(M X) ≥ 0` for positive semidefinite `M`, `X`. -/
lemma pfp_trace_mul_nonneg (M X : Matrix ι ι ℂ) (hM : M.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (M * X).trace.re := by
  have hSsa : IsSelfAdjoint (CFC.sqrt M) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)
  have hSh : (CFC.sqrt M)ᴴ = CFC.sqrt M := hSsa.star_eq
  have hSS : CFC.sqrt M * CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM.nonneg
  have htr : (M * X).trace = (CFC.sqrt M * X * (CFC.sqrt M)ᴴ).trace := by
    rw [hSh]
    conv_lhs => rw [← hSS]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  have hpsd : (CFC.sqrt M * X * (CFC.sqrt M)ᴴ).PosSemidef := hX.mul_mul_conjTranspose_same _
  rw [htr]
  exact (Complex.nonneg_iff.mp hpsd.trace_nonneg).1

end Positivity

/-! ## Tensor powers -/

section TP
variable {a : Type} [Fintype a]

lemma pfp_pure_eq (w : a → ℂ) : MixedCloning.Optimal.pure w = vecMulVec w (star w) := by
  ext i j
  simp [MixedCloning.Optimal.pure, vecMulVec]

lemma pfp_tensorPower_mul (n : ℕ) (A B : Op a) :
    tensorPower n A * tensorPower n B = tensorPower n (A * B) := by
  ext i j
  simp only [tensorPower, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib]

lemma pfp_tensorPower_conjTranspose (n : ℕ) (A : Op a) :
    (tensorPower n A)ᴴ = tensorPower n Aᴴ := by
  ext i j
  simp [tensorPower, conjTranspose_apply, map_prod]

lemma pfp_mul_pure_mul (B : Op a) (v : a → ℂ) :
    B * MixedCloning.Optimal.pure v * Bᴴ = MixedCloning.Optimal.pure (B *ᵥ v) := by
  rw [pfp_pure_eq, pfp_pure_eq, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- `B^{⊗n} |v⟩⟨v|^{⊗n} (B^{⊗n})† = |Bv⟩⟨Bv|^{⊗n}`. -/
lemma pfp_conj_tensorPower_pure (n : ℕ) (B : Op a) (v : a → ℂ) :
    tensorPower n B * tensorPower n (MixedCloning.Optimal.pure v) * (tensorPower n B)ᴴ =
      tensorPower n (MixedCloning.Optimal.pure (B *ᵥ v)) := by
  rw [pfp_tensorPower_conjTranspose, pfp_tensorPower_mul, pfp_tensorPower_mul, pfp_mul_pure_mul]

lemma pfp_tensorPower_trace (m : ℕ) (X : Op a) : (tensorPower m X).trace = X.trace ^ m := by
  rw [← Fin.prod_const]
  simp only [Matrix.trace, Matrix.diag, tensorPower]
  rw [Fintype.prod_sum]

/-- Tracing out `B_1,…,B_m` from `X^{⊗m}` gives `(tr_B X)^{⊗m}`. -/
lemma pfp_partialTrace_tensorPower {b : Type} [Fintype b] (m : ℕ) (X : Op (a × b)) :
    partialTrace m (tensorPower m X) = tensorPower m (fun i j => ∑ z : b, X (i, z) (j, z)) := by
  ext i j
  simp only [partialTrace, tensorPower]
  rw [Fintype.prod_sum]

/-- `(|u⟩⟨u|)^{⊗m}` is positive semidefinite. -/
lemma pfp_tensorPower_pure_posSemidef (m : ℕ) (u : a → ℂ) :
    (tensorPower m (MixedCloning.Optimal.pure u)).PosSemidef := by
  have h : tensorPower m (MixedCloning.Optimal.pure u) =
      vecMulVec (fun i : Word a m => ∏ t, u (i t)) (star fun i : Word a m => ∏ t, u (i t)) := by
    ext i j
    simp only [tensorPower, MixedCloning.Optimal.pure, vecMulVec, Matrix.of_apply, Pi.star_apply,
      RCLike.star_def, Finset.prod_mul_distrib, map_prod]
  rw [h]
  exact posSemidef_vecMulVec_self_star _

end TP

/-! ## The partial trace preserves states -/

section PT
variable {a b : Type} [Fintype a] [Fintype b]

lemma pfp_partialTrace_eq_sum (m : ℕ) (X : Op (Word (a × b) m)) :
    partialTrace m X =
      ∑ z : Word b m, X.submatrix (fun i t => (i t, z t)) (fun i t => (i t, z t)) := by
  ext i j
  simp [partialTrace, Matrix.sum_apply, submatrix_apply]

lemma pfp_partialTrace_posSemidef (m : ℕ) (X : Op (Word (a × b) m)) (hX : X.PosSemidef) :
    (partialTrace m X).PosSemidef := by
  rw [pfp_partialTrace_eq_sum]
  exact Matrix.posSemidef_sum _ fun z _ => hX.submatrix _

lemma pfp_partialTrace_trace (m : ℕ) (X : Op (Word (a × b) m)) :
    (partialTrace m X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTrace]
  rw [← Fintype.sum_prod_type']
  let e : Word a m × Word b m ≃ Word (a × b) m :=
    { toFun := fun p t => (p.1 t, p.2 t)
      invFun := fun w => (fun t => (w t).1, fun t => (w t).2)
      left_inv := fun p => rfl
      right_inv := fun w => rfl }
  exact Fintype.sum_equiv e _ _ (fun p => rfl)

lemma pfp_partialTrace_isState (m : ℕ) (X : Op (Word (a × b) m)) (hX : IsState X) :
    IsState (partialTrace m X) :=
  ⟨pfp_partialTrace_posSemidef m X hX.1, (pfp_partialTrace_trace m X).trans hX.2⟩

lemma pfp_partialTrace_add (m : ℕ) (X Y : Op (Word (a × b) m)) :
    partialTrace m (X + Y) = partialTrace m X + partialTrace m Y := by
  ext i j
  simp only [partialTrace, Matrix.add_apply, Finset.sum_add_distrib]

lemma pfp_partialTrace_smul (m : ℕ) (c : ℂ) (X : Op (Word (a × b) m)) :
    partialTrace m (c • X) = c • partialTrace m X := by
  ext i j
  simp only [partialTrace, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

end PT

/-! ## Linearity of the Werner map (no `DecidableEq` binder: see the `1` inside `werner`) -/

section Lin
variable {a : Type} [Fintype a]

lemma pfp_appendIdentity_add (n k : ℕ) (X Y : Op (Word a n)) :
    appendIdentity n k (X + Y) = appendIdentity n k X + appendIdentity n k Y := by
  ext i j
  simp only [appendIdentity, Matrix.add_apply, add_mul]

lemma pfp_appendIdentity_smul (n k : ℕ) (c : ℂ) (X : Op (Word a n)) :
    appendIdentity n k (c • X) = c • appendIdentity n k X := by
  ext i j
  simp only [appendIdentity, Matrix.smul_apply, smul_eq_mul, mul_assoc]

lemma pfp_werner_add (n k : ℕ) (tau : Op (Word a (n+k))) (X Y : Op (Word a n)) :
    werner a n k tau (X + Y) = werner a n k tau X + werner a n k tau Y := by
  simp only [werner, Matrix.mul_add, Matrix.add_mul, pfp_appendIdentity_add, smul_add,
    Matrix.trace_add, add_smul]
  abel

lemma pfp_werner_smul (n k : ℕ) (tau : Op (Word a (n+k))) (c : ℂ) (X : Op (Word a n)) :
    werner a n k tau (c • X) = c • werner a n k tau X := by
  simp only [werner, Matrix.mul_smul, Matrix.smul_mul, pfp_appendIdentity_smul,
    Matrix.trace_smul, smul_eq_mul]
  rw [smul_add, smul_comm c, mul_smul]

end Lin

/-- `X ↦ tr_B(W(X))` as a `ℂ`-linear map. -/
lemma pfp_exists_L (d r n k : ℕ) (tau : Op (Word (Fin d × Fin r) (n+k))) :
    ∃ L : Op (Word (Fin d × Fin r) n) →ₗ[ℂ] Op (Word (Fin d) (n+k)),
      ∀ X, L X = partialTrace (n+k) (werner (Fin d × Fin r) n k tau X) :=
  ⟨{ toFun := fun X => partialTrace (n+k) (werner (Fin d × Fin r) n k tau X)
     map_add' := fun X Y => by
       simp only [pfp_werner_add, pfp_partialTrace_add]
     map_smul' := fun c X => by
       simp only [pfp_werner_smul, pfp_partialTrace_smul, RingHom.id_apply] },
   fun _ => rfl⟩

/-- `X ↦ Re tr(M X)` as an `ℝ`-linear functional. -/
lemma pfp_exists_effect_linear {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) :
    ∃ T : Matrix ι ι ℂ →ₗ[ℝ] ℝ, ∀ X, T X = (M * X).trace.re :=
  ⟨{ toFun := fun X => (M * X).trace.re
     map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.trace_add]
     map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.trace_smul] },
   fun _ => rfl⟩

/-! ## Marginals and purifications -/

/-- The local unitary `I ⊗ U` does not change the marginal on the first factor. -/
lemma pfp_auxAction_mulVec {d r : ℕ} (U : Matrix.unitaryGroup (Fin r) ℂ)
    (w : Fin d × Fin r → ℂ) (i : Fin d) (z : Fin r) :
    (auxAction (d := d) U *ᵥ w) (i, z) = ((U : Op (Fin r)) *ᵥ (fun z' => w (i, z'))) z := by
  simp only [Matrix.mulVec, dotProduct, auxAction]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

lemma pfp_marg_auxAction {d r : ℕ} (U : Matrix.unitaryGroup (Fin r) ℂ) (w : Fin d × Fin r → ℂ) :
    (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure (auxAction (d := d) U *ᵥ w) (i,z) (j,z)) =
      (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure w (i,z) (j,z)) := by
  funext i j
  have hU : (U : Op (Fin r))ᴴ * (U : Op (Fin r)) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp U.2
    simpa [Matrix.star_eq_conjTranspose] using h
  simp only [MixedCloning.Optimal.pure, pfp_auxAction_mulVec]
  have h1 : ∀ x y : Fin r → ℂ, ∑ z, ((U : Op (Fin r)) *ᵥ x) z * conj (((U : Op (Fin r)) *ᵥ y) z) =
      star y ⬝ᵥ x := by
    intro x y
    have h2 : ∑ z, ((U : Op (Fin r)) *ᵥ x) z * conj (((U : Op (Fin r)) *ᵥ y) z) =
        star ((U : Op (Fin r)) *ᵥ y) ⬝ᵥ ((U : Op (Fin r)) *ᵥ x) := by
      simp only [dotProduct, Pi.star_apply, RCLike.star_def]
      exact Finset.sum_congr rfl fun z _ => mul_comm _ _
    rw [h2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU,
      Matrix.one_mulVec]
  rw [h1]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/-- `‖w‖² = Re tr ρ` when `ρ` is the first marginal of `|w⟩⟨w|`. -/
lemma pfp_norm_sq_of_marg {a b : Type} [Fintype a] [Fintype b] (w : EuclideanSpace ℂ (a × b))
    (ρ : Op a) (hm : (fun i j => ∑ z : b, MixedCloning.Optimal.pure w (i,z) (j,z)) = ρ) :
    ‖w‖ ^ 2 = ρ.trace.re := by
  rw [← hm, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, MixedCloning.Optimal.pure, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun z _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma pfp_sum_embed {S T : Type} [Fintype S] [Fintype T] [DecidableEq T] (φ : S ↪ T)
    (α β : S → ℂ) :
    ∑ z : T, (∑ k, if φ k = z then α k else 0) * conj (∑ k, if φ k = z then β k else 0) =
      ∑ k, α k * conj (β k) := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  congr 2
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    simp [φ.injective.ne hk']
  · simp

lemma pfp_exists_embed_marg {a S T : Type} [Fintype a] [Fintype S] [Fintype T] (φ : S ↪ T)
    (B : a → S → ℂ) :
    ∃ w : a × T → ℂ, (fun i j => ∑ z : T, MixedCloning.Optimal.pure w (i,z) (j,z)) =
      fun i j => ∑ k, B i k * conj (B j k) := by
  classical
  refine ⟨fun p => ∑ k, if φ k = p.2 then B p.1 k else 0, ?_⟩
  funext i j
  simp only [MixedCloning.Optimal.pure]
  exact pfp_sum_embed φ (fun k => B i k) (fun k => B j k)

/-- Purification of a rank-`≤ r` state on `ℂ^d ⊗ ℂ^r`, from the spectral decomposition. -/
lemma pfp_exists_purification {d r : ℕ} (ρ : Op (Fin d)) (hρ : ρ.PosSemidef)
    (hrank : ρ.rank ≤ r) :
    ∃ w : Fin d × Fin r → ℂ,
      (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure w (i,z) (j,z)) = ρ := by
  have hH : ρ.IsHermitian := hρ.1
  have hcard : Fintype.card {k // hH.eigenvalues k ≠ 0} ≤ Fintype.card (Fin r) := by
    rw [Fintype.card_fin]
    have h := hH.rank_eq_card_non_zero_eigs
    convert hrank using 1
    convert h.symm
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨w, hw⟩ := pfp_exists_embed_marg φ (fun i (k : {k // hH.eigenvalues k ≠ 0}) =>
    ((Real.sqrt (hH.eigenvalues k) : ℝ) : ℂ) * (hH.eigenvectorUnitary : Op (Fin d)) i k)
  refine ⟨w, hw.trans ?_⟩
  funext i j
  have hspec : ρ i j = ∑ k, (hH.eigenvectorUnitary : Op (Fin d)) i k *
      (hH.eigenvalues k : ℂ) * conj ((hH.eigenvectorUnitary : Op (Fin d)) j k) := by
    conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
    simp [Matrix.mul_diagonal, Matrix.star_apply]
  rw [hspec]
  have hterm : ∀ k : {k // hH.eigenvalues k ≠ 0},
      ((Real.sqrt (hH.eigenvalues k) : ℝ) : ℂ) * (hH.eigenvectorUnitary : Op (Fin d)) i k *
        conj (((Real.sqrt (hH.eigenvalues k) : ℝ) : ℂ) *
          (hH.eigenvectorUnitary : Op (Fin d)) j k) =
      (hH.eigenvectorUnitary : Op (Fin d)) i k * (hH.eigenvalues k : ℂ) *
        conj ((hH.eigenvectorUnitary : Op (Fin d)) j k) := by
    intro k
    have hl : 0 ≤ hH.eigenvalues k := hρ.eigenvalues_nonneg k
    have hs : ((Real.sqrt (hH.eigenvalues k) : ℝ) : ℂ) * ((Real.sqrt (hH.eigenvalues k) : ℝ) : ℂ) =
        (hH.eigenvalues k : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
    rw [map_mul, Complex.conj_ofReal]
    linear_combination ((hH.eigenvectorUnitary : Op (Fin d)) i k *
      conj ((hH.eigenvectorUnitary : Op (Fin d)) j k)) * hs
  simp only [hterm]
  rw [← Finset.sum_subtype (Finset.univ.filter fun k => hH.eigenvalues k ≠ 0) (by simp)
    (fun k => (hH.eigenvectorUnitary : Op (Fin d)) i k * (hH.eigenvalues k : ℂ) *
      conj ((hH.eigenvectorUnitary : Op (Fin d)) j k))]
  rw [Finset.sum_filter_of_ne]
  intro k _ hk
  intro h0
  apply hk
  rw [h0]
  simp

/-! ## Integrals -/

lemma pfp_map_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →ₗ[ℝ] F) {f : α → E} (hf : Integrable f μ) :
    T (∫ x, f x ∂μ) = ∫ x, T (f x) ∂μ := by
  have h := (LinearMap.toContinuousLinearMap T).integral_comp_comm hf
  simpa only [LinearMap.coe_toContinuousLinearMap'] using h.symm

/-- Jensen's inequality for the square root. -/
lemma pfp_integral_sqrt_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hsf : Integrable (fun x => Real.sqrt (f x)) μ) :
    ∫ x, Real.sqrt (f x) ∂μ ≤ Real.sqrt (∫ x, f x ∂μ) :=
  (Real.strictConcaveOn_sqrt.concaveOn).le_map_integral Real.continuous_sqrt.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hf0) hf hsf

lemma pfp_isClosed_state {ι : Type} [Fintype ι] : IsClosed {X : Op ι | IsState X} := by
  have hset : {X : Op ι | IsState X} =
      ({X | Xᴴ = X} ∩ ⋂ x : ι → ℂ, {X | 0 ≤ star x ⬝ᵥ (X *ᵥ x)}) ∩ {X | X.trace = 1} := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, QAlgorithms.IsDensityMatrix,
      Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [hset]
  refine IsClosed.inter (IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))))
    (isClosed_eq continuous_id.matrix_trace continuous_const)

lemma pfp_convex_state {ι : Type} [Fintype ι] : Convex ℝ {X : Op ι | IsState X} := by
  intro X hX Y hY s t hs ht hst
  obtain ⟨hX1, hX2⟩ : IsState X := hX
  obtain ⟨hY1, hY2⟩ : IsState Y := hY
  show IsState (s • X + t • Y)
  refine ⟨(hX1.smul hs).add (hY1.smul ht), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX2, hY2, ← add_smul, hst, one_smul]

lemma pfp_continuous_auxAction (d r : ℕ) :
    Continuous (fun U : Matrix.unitaryGroup (Fin r) ℂ => auxAction (d := d) U) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : i.1 = j.1
  · simp only [auxAction, h, if_true]
    exact continuous_subtype_val.matrix_elem i.2 j.2
  · simp only [auxAction, h, if_false]
    exact continuous_const

lemma pfp_continuous_tp {X : Type*} [TopologicalSpace X] {a : Type} [Fintype a] (n : ℕ)
    (v : X → a → ℂ) (hv : Continuous v) :
    Continuous fun x => tensorPower n (MixedCloning.Optimal.pure (v x)) := by
  refine continuous_matrix fun i j => ?_
  simp only [tensorPower, MixedCloning.Optimal.pure]
  refine continuous_finsetProd _ fun t _ => ?_
  exact ((continuous_apply _).comp hv).mul
    (Complex.continuous_conj.comp ((continuous_apply _).comp hv))

lemma pfp_integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {r : ℕ}
    (f : Matrix.unitaryGroup (Fin r) ℂ → E) (hf : Continuous f) : Integrable f (haar r) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-! ## Concavity and the main theorem -/

/-- Concavity of the root fidelity in its first argument, for a continuous family of states
averaged against the Haar probability measure (Fuchs–Caves + Jensen for `√`). -/
lemma pfp_concavity {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (g : Matrix.unitaryGroup (Fin r) ℂ → Matrix ι ι ℂ) (hg : Continuous g)
    (hgs : ∀ U, IsState (g U)) (Y : Matrix ι ι ℂ) (hY : IsState Y) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ U, c ≤ fidelity (g U) Y) : c ≤ fidelity (∫ U, g U ∂haar r) Y := by
  have hg_int := pfp_integrable_of_continuous g hg
  have hG : IsState (∫ U, g U ∂haar r) :=
    pfp_convex_state.integral_mem pfp_isClosed_state (Filter.Eventually.of_forall hgs) hg_int
  obtain ⟨m, M, hM, hMeq⟩ := (MayersBC.fuchs_caves _ _ hG hY).2
  -- pointwise bound
  have hbound : ∀ U, Real.sqrt c ≤ ∑ j, Real.sqrt ((M j * g U).trace.re * (M j * Y).trace.re) := by
    intro U
    have h3 : Real.sqrt c ≤ QAlgorithms.rootFidelity (g U) Y :=
      (Real.sqrt_le_sqrt (hc U)).trans_eq (Real.sqrt_sq (pfp_rootFidelity_nonneg _ _))
    have h4 := (MayersBC.fuchs_caves _ _ (hgs U) hY).1 M hM
    exact h3.trans h4
  have hp_cont : ∀ j, Continuous fun U => (M j * g U).trace.re := fun j =>
    Complex.continuous_re.comp ((continuous_const.matrix_mul hg).matrix_trace)
  have hint_p : ∀ j, Integrable (fun U => (M j * g U).trace.re * (M j * Y).trace.re) (haar r) :=
    fun j => pfp_integrable_of_continuous _ ((hp_cont j).mul continuous_const)
  have hint_h : ∀ j, Integrable (fun U => Real.sqrt ((M j * g U).trace.re * (M j * Y).trace.re))
      (haar r) := fun j =>
    pfp_integrable_of_continuous _ (Real.continuous_sqrt.comp ((hp_cont j).mul continuous_const))
  have hp_nonneg : ∀ U j, 0 ≤ (M j * g U).trace.re := fun U j =>
    pfp_trace_mul_nonneg _ _ (hM.1 j) (hgs U).1
  have hq_nonneg : ∀ j, 0 ≤ (M j * Y).trace.re := fun j =>
    pfp_trace_mul_nonneg _ _ (hM.1 j) hY.1
  -- integrate the pointwise bound
  have hstep : Real.sqrt c ≤
      ∑ j, ∫ U, Real.sqrt ((M j * g U).trace.re * (M j * Y).trace.re) ∂haar r := by
    rw [← integral_finsetSum _ (fun j _ => hint_h j)]
    have h := integral_mono (integrable_const (Real.sqrt c))
      (integrable_finsetSum _ (fun j _ => hint_h j)) hbound
    have hconst : ∫ _U, Real.sqrt c ∂(haar r) = Real.sqrt c := by simp
    rw [hconst] at h
    exact h
  -- Jensen for each outcome
  have hjensen : ∀ j, ∫ U, Real.sqrt ((M j * g U).trace.re * (M j * Y).trace.re) ∂haar r ≤
      Real.sqrt ((M j * ∫ U, g U ∂haar r).trace.re * (M j * Y).trace.re) := by
    intro j
    have h := pfp_integral_sqrt_le (haar r) _ (hint_p j)
      (fun U => mul_nonneg (hp_nonneg U j) (hq_nonneg j)) (hint_h j)
    rw [integral_mul_const] at h
    obtain ⟨T, hT⟩ := pfp_exists_effect_linear (M j)
    have hTi := pfp_map_integral T hg_int
    simp only [hT] at hTi
    rw [hTi]
    exact h
  have hfinal : Real.sqrt c ≤ QAlgorithms.rootFidelity (∫ U, g U ∂haar r) Y := by
    rw [← hMeq]
    exact hstep.trans (Finset.sum_le_sum fun j _ => hjensen j)
  show c ≤ QAlgorithms.rootFidelity (∫ U, g U ∂haar r) Y ^ 2
  calc c = Real.sqrt c ^ 2 := (Real.sq_sqrt hc0).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg c) hfinal 2

/-- Each `(I ⊗ U) w` is again a unit purification of `rho`. -/
lemma pfp_rotated_purification {d r : ℕ} (rho : Op (Fin d)) (hrho : IsState rho)
    (w : Fin d × Fin r → ℂ)
    (hw : (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure w (i,z) (j,z)) = rho)
    (U : Matrix.unitaryGroup (Fin r) ℂ) :
    ‖(WithLp.toLp 2 (auxAction (d := d) U *ᵥ w) : EuclideanSpace ℂ (Fin d × Fin r))‖ = 1 ∧
      (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure
        (WithLp.toLp 2 (auxAction (d := d) U *ᵥ w) : EuclideanSpace ℂ (Fin d × Fin r))
          (i,z) (j,z)) = rho := by
  have hm : (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure
      (WithLp.toLp 2 (auxAction (d := d) U *ᵥ w) : EuclideanSpace ℂ (Fin d × Fin r)) (i,z) (j,z))
      = rho := (pfp_marg_auxAction U w).trans hw
  refine ⟨?_, hm⟩
  have h2 := pfp_norm_sq_of_marg _ rho hm
  rw [hrho.2, Complex.one_re] at h2
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]

lemma pfp_unit_purification {d r : ℕ} (rho : Op (Fin d)) (hrho : IsState rho)
    (w : Fin d × Fin r → ℂ)
    (hw : (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure w (i,z) (j,z)) = rho) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin d × Fin r))‖ = 1 := by
  have h2 := pfp_norm_sq_of_marg (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin d × Fin r)) rho hw
  rw [hrho.2, Complex.one_re] at h2
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]

/-- `ρ^{⊗m}` is a state. -/
lemma pfp_tensorPower_isState {d r : ℕ} (m : ℕ) (rho : Op (Fin d)) (hrho : IsState rho)
    (w : Fin d × Fin r → ℂ)
    (hw : (fun i j => ∑ z : Fin r, MixedCloning.Optimal.pure w (i,z) (j,z)) = rho) :
    IsState (tensorPower m rho) := by
  refine ⟨?_, ?_⟩
  · have htp : tensorPower m rho =
        partialTrace m (tensorPower m (MixedCloning.Optimal.pure w)) := by
      rw [pfp_partialTrace_tensorPower, hw]
    rw [htp]
    exact pfp_partialTrace_posSemidef _ _ (pfp_tensorPower_pure_posSemidef _ _)
  · rw [pfp_tensorPower_trace, hrho.2, one_pow]

theorem solution (d r n k : ℕ)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n)) (hR : IsRPC d r n R)
    (tau : Op (Word (Fin d × Fin r) (n+k)))
    (rho : Op (Fin d)) (hrho : IsState rho) (hrank : rho.rank ≤ r) (c : ℝ)
    (hc : ∀ u : EuclideanSpace ℂ (Fin d × Fin r), ‖u‖ = 1 →
      (fun i j => ∑ z : Fin r, pure u (i,z) (j,z)) = rho →
      c ≤ fidelity (partialTrace (n+k) (werner (Fin d × Fin r) n k tau (tensorPower n (pure u))))
        (tensorPower (n+k) rho)) :
    c ≤ fidelity (pct d r n k R tau (tensorPower n rho)) (tensorPower (n+k) rho) := by
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact hc0.le.trans (sq_nonneg _)
  obtain ⟨w, hw⟩ := pfp_exists_purification rho hrho.1 hrank
  have hRint := hR.2 rho hrho hrank _ (pfp_unit_purification rho hrho w hw) hw
  obtain ⟨f, hf⟩ : ∃ f : Matrix.unitaryGroup (Fin r) ℂ → Op (Word (Fin d × Fin r) n),
      ∀ U, f U = tensorPower n (MixedCloning.Optimal.pure (auxAction (d := d) U *ᵥ w)) :=
    ⟨_, fun _ => rfl⟩
  have hfun : (fun U : Matrix.unitaryGroup (Fin r) ℂ =>
      tensorPower n (auxAction (d := d) U) * tensorPower n (MixedCloning.Optimal.pure w) *
        (tensorPower n (auxAction (d := d) U))ᴴ) = f := by
    funext U
    rw [hf]
    exact pfp_conj_tensorPower_pure n _ w
  have hRf : R (tensorPower n rho) = ∫ U, f U ∂haar r := by
    rw [← hfun]
    exact hRint
  obtain ⟨L, hL⟩ := pfp_exists_L d r n k tau
  have hf_cont : Continuous f := by
    rw [show f = fun U => tensorPower n (MixedCloning.Optimal.pure (auxAction (d := d) U *ᵥ w))
      from funext hf]
    exact pfp_continuous_tp n _ ((pfp_continuous_auxAction d r).matrix_mulVec continuous_const)
  have hf_int := pfp_integrable_of_continuous f hf_cont
  have hpct : pct d r n k R tau (tensorPower n rho) = ∫ U, L (f U) ∂haar r := by
    show partialTrace (n+k) (werner (Fin d × Fin r) n k tau (R (tensorPower n rho))) = _
    rw [← hL, hRf]
    exact pfp_map_integral (L.restrictScalars ℝ) hf_int
  rw [hpct]
  refine pfp_concavity (fun U => L (f U)) (L.continuous_of_finiteDimensional.comp hf_cont)
    ?_ _ (pfp_tensorPower_isState (n+k) rho hrho w hw) c hc0 ?_
  · intro U
    show IsState (L (f U))
    rw [hL, hf]
    exact pfp_partialTrace_isState (n+k) _
      (werner_pure_fidelity (a := Fin d × Fin r) n k tau _
        (pfp_rotated_purification rho hrho w hw U).1).1
  · intro U
    have h1 := hc _ (pfp_rotated_purification rho hrho w hw U).1
      (pfp_rotated_purification rho hrho w hw U).2
    show c ≤ fidelity (L (f U)) (tensorPower (n+k) rho)
    rw [hL, hf]
    exact h1

end
