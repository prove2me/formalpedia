-- Prove2me | solution 1 for GinibrePermanent977.Anticoncentration.proposition_3_5_fourier_compression
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:30:19.958107+00:00
-- url     : https://prove2.me/submissions/8e9016aa-6b8a-4991-b1b6-bdf772ba0a99

import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
import Theorems.Thm_GinibrePermanent977_Anticoncentration_corollary_3_3_two_coordinate_compression
import Mathlib

-- Solutions/PermanentAlgebra.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma perK_columns_perm {K : Type*} [Ring K] {n : ℕ}
    (A : Fin n → Fin n → K) (τ : Equiv.Perm (Fin n)) :
    perK (fun i j => A i (τ j)) = perK A := by
  unfold perK
  simpa only [Equiv.Perm.mul_apply] using
    (Group.mulLeft_bijective τ).sum_comp (fun σ : Equiv.Perm (Fin n) =>
      (List.ofFn fun i => A i (σ i)).prod)

lemma continuous_ordered_product {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [Monoid K] [ContinuousMul K] {n : ℕ} (f : Fin n → X → K)
    (hf : ∀ i, Continuous (f i)) : Continuous (fun x => (List.ofFn fun i => f i x).prod) := by
  induction n with
  | zero => simpa using (continuous_const : Continuous (fun _ : X => (1 : K)))
  | succ n ih =>
    simp_rw [List.ofFn_succ, List.prod_cons]
    exact (hf 0).mul (ih (fun i => f i.succ) (fun i => hf i.succ))

lemma continuous_perK {K : Type*} [NormedRing K] {n : ℕ} :
    Continuous (perK : (Fin n → Fin n → K) → K) := by
  unfold perK
  apply continuous_finset_sum
  intro σ _
  exact continuous_ordered_product (fun i (A : Fin n → Fin n → K) => A i (σ i)) (by intro i; fun_prop)

lemma perK_succ_first_row {K : Type*} [Ring K] {n : ℕ}
    (A : Fin (n+1) → Fin (n+1) → K) :
    perK A = ∑ j : Fin (n+1), A 0 j * perK (fun i k => A i.succ (j.succAbove k)) := by
  unfold perK
  rw [Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  simp only [List.ofFn_succ, List.prod_cons,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  rw [← Finset.mul_sum]
  congr 1
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Equiv.swap_self, Equiv.coe_refl, Fin.succAbove_zero, id_eq]
  · have h := perK_columns_perm (fun i k : Fin n => A i.succ (j.succ.succAbove k)) (Fin.cycleRange j)
    unfold perK at h
    rw [← h]
    simp only [Fin.succAbove_cycleRange]

lemma skipCol_succAbove {n : ℕ} (j : Fin (n+1)) (k : Fin n) :
    skipCol j k = j.succAbove k := by
  apply Fin.ext
  simp only [skipCol, Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

lemma perK_cons_row {K : Type*} [Ring K] {n : ℕ}
    (w : Fin (n+1) → K) (B : Fin n → Fin (n+1) → K) :
    perK (Fin.cons w B) = ∑ j, w j * perCofactor (n := n+1) B j := by
  rw [perK_succ_first_row]
  simp only [Fin.cons_zero, Fin.cons_succ]
  change (∑ j, w j * perK (fun i k => B i (j.succAbove k))) =
    ∑ j, w j * perK (fun i k => B i (skipCol j k))
  simp_rw [skipCol_succAbove]

lemma perCofactor_columns_perm {K : Type*} [Ring K] {n : ℕ}
    (B : Fin n → Fin (n+1) → K) (τ : Equiv.Perm (Fin (n+1))) (j : Fin (n+1)) :
    perCofactor (n := n+1) (fun i k => B i (τ k)) j = perCofactor (n := n+1) B (τ j) := by
  classical
  have h := perK_columns_perm (Fin.cons (Pi.single (τ j) (1 : K)) B) τ
  have hf : (fun (i k : Fin (n+1)) => (Fin.cons (Pi.single (τ j) (1 : K)) B : Fin (n+1) → Fin (n+1) → K) i (τ k)) =
      Fin.cons (Pi.single j (1 : K)) (fun i k => B i (τ k)) := by
    funext i k
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Pi.single_apply, τ.injective.eq_iff]
    · rfl
  rw [hf, perK_cons_row, perK_cons_row] at h
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  convert h using 1
  rfl

lemma perK_columns_multilinear {R K : Type*} [CommSemiring R] [Ring K] [Algebra R K] (n : ℕ) :
    ∃ P : MultilinearMap R (fun _ : Fin n => Fin n → K) K,
      ∀ cols : Fin n → Fin n → K, P cols = perK (fun i j => cols j i) := by
  let P : MultilinearMap R (fun _ : Fin n => Fin n → K) K :=
    ∑ σ : Equiv.Perm (Fin n),
      ((MultilinearMap.mkPiAlgebraFin R n K).domDomCongr σ).compLinearMap
        (fun j => LinearMap.proj (σ.symm j))
  refine ⟨P, fun cols => ?_⟩
  simp [P, perK, MultilinearMap.domDomCongr_apply]

lemma perK_rows_multilinear {R K : Type*} [CommSemiring R] [Ring K] [Algebra R K] (n : ℕ) :
    ∃ P : MultilinearMap R (fun _ : Fin n => Fin n → K) K,
      ∀ rows : Fin n → Fin n → K, P rows = perK rows := by
  let P : MultilinearMap R (fun _ : Fin n => Fin n → K) K :=
    ∑ σ : Equiv.Perm (Fin n),
      (MultilinearMap.mkPiAlgebraFin R n K).compLinearMap
        (fun i => LinearMap.proj (σ i))
  refine ⟨P, fun rows => ?_⟩
  simp [P, perK]

lemma perCofactor_rows_multilinear {K : Type*} [Ring K] [Algebra ℝ K] (n : ℕ)
    (l : Fin n → K →ₗ[ℝ] ℝ) :
    ∃ H : MultilinearMap ℝ (fun _ : Fin (n-1) => Fin n → K) ℝ,
      ∀ B : Fin (n-1) → Fin n → K, H B = ∑ j, l j (perCofactor B j) := by
  obtain ⟨P, hP⟩ := perK_rows_multilinear (R := ℝ) (K := K) (n-1)
  let r (j : Fin n) : (Fin n → K) →ₗ[ℝ] (Fin (n-1) → K) :=
    LinearMap.pi (fun k => LinearMap.proj (skipCol j k))
  let H : MultilinearMap ℝ (fun _ : Fin (n-1) => Fin n → K) ℝ :=
    ∑ j, (l j).compMultilinearMap (P.compLinearMap (fun _ => r j))
  refine ⟨H, fun B => ?_⟩
  simp only [H, _root_.sum_apply, LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply]
  simp_rw [hP]
  rfl

lemma perK_cons_column_linear {K : Type*} [Ring K] [Algebra ℝ K] {n : ℕ}
    (R : Fin (n+1) → Fin n → K) :
    ∃ L : (Fin (n+1) → K) →ₗ[ℝ] K,
      ∀ X, L X = perK (fun i => Fin.cons (X i) (R i)) := by
  obtain ⟨P, hP⟩ := perK_columns_multilinear (R := ℝ) (K := K) (n+1)
  let L : (Fin (n+1) → K) →ₗ[ℝ] K :=
    { toFun := fun X => P (Fin.cons X (fun j i => R i j))
      map_add' := by intro X Y; exact MultilinearMap.cons_add P _ X Y
      map_smul' := by intro r X; exact MultilinearMap.cons_smul P _ r X }
  refine ⟨L, fun X => ?_⟩
  rw [show L X = P (Fin.cons X (fun j i => R i j)) from rfl, hP]
  congr 1
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

lemma perK_cons_two_columns_bilinear {K : Type*} [Ring K] [Algebra ℝ K] {n : ℕ}
    (R : Fin (n+2) → Fin n → K) :
    ∃ Q : (Fin (n+2) → K) →ₗ[ℝ] (Fin (n+2) → K) →ₗ[ℝ] K,
      ∀ X Y, Q X Y = perK (fun i => Fin.cons (X i) (Fin.cons (Y i) (R i))) := by
  obtain ⟨P, hP⟩ := perK_columns_multilinear (R := ℝ) (K := K) (n+2)
  let Q := LinearMap.mk₂ ℝ
    (fun X Y => P (Fin.cons X (Fin.cons Y (fun j i => R i j))))
    (fun X X' Y => MultilinearMap.cons_add P _ X X')
    (fun r X Y => MultilinearMap.cons_smul P _ r X)
    (fun X Y Y' => MultilinearMap.cons_add (P.curryLeft X) _ Y Y')
    (fun r X Y => MultilinearMap.cons_smul (P.curryLeft X) _ r Y)
  refine ⟨Q, fun X Y => ?_⟩
  rw [show Q X Y = P (Fin.cons X (Fin.cons Y (fun j i => R i j))) from rfl, hP]
  congr 1
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j <;> rfl

end GinibrePermanent977.Anticoncentration


-- Solutions/ScalarGaussian.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace NNReal Quaternion ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma real_gaussian_characteristic (v : ℝ≥0) (z : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * (x*z : ℝ)) ∂gaussianReal 0 v) =
      (Real.exp (-(v : ℝ)*z^2/2) : ℂ) := by
  simpa [charFun_apply_real, mul_comm, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow, neg_div] using charFun_gaussianReal (μ := 0) (v := v) z

lemma vector_gaussian_characteristic {d : ℕ} (v : ℝ≥0) (z : Fin d → ℝ) :
    (∫ x : Fin d → ℝ, Complex.exp (Complex.I * (x ⬝ᵥ z : ℝ))
      ∂Measure.pi (fun _ => gaussianReal 0 v)) =
      (Real.exp (-(v : ℝ)*(∑ i, z i^2)/2) : ℂ) := by
  have hfactor (x : Fin d → ℝ) : Complex.exp (Complex.I * (x ⬝ᵥ z : ℝ)) =
      ∏ i, Complex.exp (Complex.I * (x i*z i : ℝ)) := by
    simp [dotProduct, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  simp_rw [hfactor]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Complex.exp (Complex.I * (x*z i : ℝ)))]
  simp_rw [real_gaussian_characteristic]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 3
  rw [← Finset.sum_div, ← Finset.mul_sum]

lemma scalar_gaussian_characteristic (F : Scalar) (z : F.K) :
    (∫ x : F.K, Complex.exp (Complex.I * ((inner ℝ z x : ℝ) : ℂ)) ∂gaussian F) =
      (Real.exp (-‖z‖^2/(2*(F.beta : ℝ))) : ℂ) := by
  cases F
  · dsimp only [Scalar.K] at z ⊢
    have hz : ‖z‖^2 = (show ℝ from z)^2 := by
      rw [← real_inner_self_eq_norm_sq]
      change (show ℝ from z)*(show ℝ from z) = (show ℝ from z)^2
      ring
    rw [hz]
    simpa only [gaussian, Scalar.beta, Nat.cast_one, mul_one, Scalar.instNormedRing,
      Scalar.instInnerProductSpace, Real.norm_eq_abs, sq_abs, RCLike.inner_apply,
      starRingEnd_apply, star_trivial, NNReal.coe_one, neg_mul, one_mul] using
      real_gaussian_characteristic 1 (show ℝ from z)
  · have hmk : Measurable (fun p : ℝ × ℝ => (⟨p.1,p.2⟩ : ℂ)) :=
      Complex.equivRealProdCLM.symm.continuous.measurable
    change (∫ x : ℂ, Complex.exp (Complex.I * ((inner ℝ z x : ℝ) : ℂ))
      ∂((gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2))).map
        (fun p : ℝ × ℝ => (⟨p.1,p.2⟩ : ℂ))) = _
    rw [integral_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by fun_prop))]
    rw [← (measurePreserving_finTwoArrow (gaussianReal 0 (1/2))).map_eq,
      integral_map (Measurable.aemeasurable (by fun_prop))
        (Measurable.aestronglyMeasurable (by fun_prop))]
    let e := Complex.orthonormalBasisOneI.repr
    let w : Fin 2 → ℝ := e z
    have hi (x : Fin 2 → ℝ) : inner ℝ z (⟨x 0,x 1⟩ : ℂ) = x ⬝ᵥ w := by
      have hx : e (⟨x 0,x 1⟩ : ℂ) = WithLp.toLp 2 x := by
        ext i
        fin_cases i <;> rfl
      calc
        inner ℝ z (⟨x 0,x 1⟩ : ℂ) = inner ℝ (e z) (e (⟨x 0,x 1⟩ : ℂ)) :=
          (e.inner_map_map z (⟨x 0,x 1⟩ : ℂ)).symm
        _ = inner ℝ (e z) (WithLp.toLp 2 x) := by rw [hx]
        _ = x ⬝ᵥ w := by simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, w]
    change (∫ x : Fin 2 → ℝ, Complex.exp (Complex.I * ((inner ℝ z (⟨x 0,x 1⟩ : ℂ) : ℝ) : ℂ))
      ∂Measure.pi (fun _ => gaussianReal 0 (1/2))) = _
    simp_rw [hi]
    rw [vector_gaussian_characteristic]
    have hn : ∑ i, w i^2 = ‖z‖^2 := by
      rw [← EuclideanSpace.real_norm_sq_eq (e z), e.norm_map]
    rw [hn]
    congr 2
    norm_num [Scalar.beta]
    ring
  · letI : MeasureSpace ℍ := Scalar.instMeasureSpace .quaternion
    haveI : BorelSpace ℍ := Scalar.instBorelSpace .quaternion
    have hmap : Measurable quatOfCoords := quatOfCoords.continuous_of_finiteDimensional.measurable
    change (∫ x : ℍ, Complex.exp (Complex.I * ((inner ℝ z x : ℝ) : ℂ))
      ∂(Measure.pi (fun _ : Fin 4 => gaussianReal 0 (1/4))).map quatOfCoords) = _
    rw [integral_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by fun_prop))]
    let e := Quaternion.linearIsometryEquivTuple
    let w : Fin 4 → ℝ := e z
    have hi (x : Fin 4 → ℝ) : inner ℝ z (quatOfCoords x) = x ⬝ᵥ w := by
      have hx : e (quatOfCoords x) = WithLp.toLp 2 x := by
        ext i
        fin_cases i <;> rfl
      have he := (e.inner_map_map z (quatOfCoords x)).symm
      rw [hx] at he
      simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, w] using he
    simp_rw [hi]
    rw [vector_gaussian_characteristic]
    have hn : ∑ i, w i^2 = ‖z‖^2 := by
      rw [← EuclideanSpace.real_norm_sq_eq (e z), e.norm_map]
    rw [hn]
    congr 2
    norm_num [Scalar.beta]
    ring

lemma vector_scalar_gaussian_characteristic (F : Scalar) {m : ℕ} (z : Fin m → F.K) :
    (∫ x : Fin m → F.K, Complex.exp (Complex.I * ((realInner z x : ℝ) : ℂ)) ∂gaussVec F m) =
      (Real.exp (-(∑ i, ‖z i‖^2)/(2*(F.beta : ℝ))) : ℂ) := by
  have hfactor (x : Fin m → F.K) : Complex.exp (Complex.I * ((realInner z x : ℝ) : ℂ)) =
      ∏ i, Complex.exp (Complex.I * ((inner ℝ (z i) (x i) : ℝ) : ℂ)) := by
    simp [realInner, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  simp_rw [hfactor]
  unfold gaussVec
  rw [integral_fintype_prod_eq_prod (fun i (x : F.K) =>
    Complex.exp (Complex.I * ((inner ℝ (z i) x : ℝ) : ℂ)))]
  simp_rw [scalar_gaussian_characteristic]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 3
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

lemma vector_scalar_gaussian_linear_nonneg (F : Scalar) {m : ℕ}
    (l : (Fin m → F.K) →ₗ[ℝ] ℝ) :
    0 ≤ (∫ x, Complex.exp (Complex.I * ((l x : ℝ) : ℂ)) ∂gaussVec F m) := by
  haveI : FiniteDimensional ℝ F.K := by
    cases F
    · exact inferInstanceAs (FiniteDimensional ℝ ℝ)
    · exact inferInstanceAs (FiniteDimensional ℝ ℂ)
    · exact inferInstanceAs (FiniteDimensional ℝ ℍ)
  haveI : CompleteSpace F.K := by cases F <;> infer_instance
  let lj (j : Fin m) : F.K →L[ℝ] ℝ :=
    (l.comp (LinearMap.single ℝ (fun _ : Fin m => F.K) j)).toContinuousLinearMap
  let z (j : Fin m) : F.K := (InnerProductSpace.toDual ℝ F.K).symm (lj j)
  have hl (x : Fin m → F.K) : l x = realInner z x := by
    calc
      l x = l (∑ j, Pi.single j (x j)) := congrArg l (Finset.univ_sum_single x).symm
      _ = ∑ j, l (Pi.single j (x j)) := by rw [map_sum]
      _ = realInner z x := by
        unfold realInner
        apply Finset.sum_congr rfl
        intro j _
        exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (y := lj j) (x := x j)).symm
  simp_rw [hl]
  rw [vector_scalar_gaussian_characteristic]
  apply Complex.nonneg_iff.mpr
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨(Real.exp_pos _).le, trivial⟩

end GinibrePermanent977.Anticoncentration


-- Solutions/GaussianCoordinates.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace ComplexOrder Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

instance scalar_finiteDimensional (F : Scalar) : FiniteDimensional ℝ F.K := by
  cases F
  · exact inferInstanceAs (FiniteDimensional ℝ ℝ)
  · exact inferInstanceAs (FiniteDimensional ℝ ℂ)
  · exact inferInstanceAs (FiniteDimensional ℝ ℍ)

instance scalar_completeSpace (F : Scalar) : CompleteSpace F.K := by cases F <;> infer_instance
instance scalar_secondCountable (F : Scalar) : SecondCountableTopology F.K := by
  cases F
  · exact inferInstanceAs (SecondCountableTopology ℝ)
  · exact inferInstanceAs (SecondCountableTopology ℂ)
  · exact inferInstanceAs (SecondCountableTopology ℍ)


lemma scalar_smul_mul (F : Scalar) (r : ℝ) (x y : F.K) : (r • x)*y = r • (x*y) := by
    cases F
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℝ from x) (show ℝ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℂ from x) (show ℂ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℍ[ℝ] from x) (show ℍ[ℝ] from y)

lemma scalar_mul_smul (F : Scalar) (r : ℝ) (x y : F.K) : x*(r • y) = r • (x*y) := by
    cases F
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℝ from x) (show ℝ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℂ from x) (show ℂ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℍ[ℝ] from x) (show ℍ[ℝ] from y)

lemma gaussian_vector_stdGaussian (F : Scalar) (m : ℕ) :
    (stdGaussian (PiLp 2 (fun _ : Fin m => F.K))).map
      (fun x => (Real.sqrt (F.beta : ℝ))⁻¹ • x) =
    (gaussVec F m).map (WithLp.toLp 2) := by
  let E := PiLp 2 (fun _ : Fin m => F.K)
  haveI : IsProbabilityMeasure (gaussVec F m) := by unfold gaussVec; infer_instance
  have hto : Measurable (WithLp.toLp 2 : (Fin m → F.K) → E) :=
    (PiLp.continuous_toLp 2 _).measurable
  haveI : IsProbabilityMeasure ((gaussVec F m).map (WithLp.toLp 2)) :=
    Measure.isProbabilityMeasure_map hto.aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_smul, charFun_stdGaussian, charFun_apply,
    integral_map hto.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop))]
  have heq (x : Fin m → F.K) :
      Complex.exp (((inner ℝ (WithLp.toLp 2 x : E) t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((realInner t.ofLp x : ℝ) : ℂ)) := by
    rw [real_inner_comm, PiLp.inner_apply]
    simp only [WithLp.ofLp_toLp, realInner, mul_comm]
  simp_rw [heq]
  rw [vector_scalar_gaussian_characteristic]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, ← Complex.ofReal_div]
  rw [← Complex.ofReal_exp]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    inv_pow, Real.sq_sqrt (beta_pos F).le, PiLp.norm_sq_eq_of_L2]
  congr 2
  field_simp

lemma gaussian_vector_coordinates (F : Scalar) (m : ℕ) (hm : 0 < m) :
    ∃ d : ℕ, 0 < d ∧ ∃ Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin m → F.K),
      MeasurePreserving Φ (SmoothBerr.stdGaussianVec d) (gaussVec F m) := by
  let E := PiLp 2 (fun _ : Fin m => F.K)
  let d := Module.finrank ℝ E
  let c := (Real.sqrt (F.beta : ℝ))⁻¹
  let b := stdOrthonormalBasis ℝ E
  let Ψ : (Fin d → ℝ) →ₗ[ℝ] E :=
    ∑ a : Fin d, (LinearMap.proj a).smulRight (b a)
  let Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin m → F.K) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => F.K)).toLinearMap.comp (c • Ψ)
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  haveI : Nontrivial F.K := by
    cases F
    · exact inferInstanceAs (Nontrivial ℝ)
    · exact inferInstanceAs (Nontrivial ℂ)
    · exact inferInstanceAs (Nontrivial ℍ[ℝ])
  refine ⟨d, Module.finrank_pos, Φ, ?_⟩
  have hΦ : Measurable Φ := Φ.continuous_of_finiteDimensional.measurable
  refine ⟨hΦ, ?_⟩
  apply (MeasurableEquiv.toLp 2 (Fin m → F.K)).measurableEmbedding.map_injective
  change Measure.map (WithLp.toLp 2) (Measure.map Φ _) = Measure.map (WithLp.toLp 2) _
  rw [Measure.map_map (PiLp.continuous_toLp 2 _).measurable hΦ]
  have hg := gaussian_vector_stdGaussian F m
  rw [stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)] at hg
  convert hg using 1
  congr 1
  funext x
  change WithLp.toLp 2 ((c • Ψ x).ofLp) = c • ∑ i, x i • b i
  rw [WithLp.toLp_ofLp]
  congr 1
  simp [Ψ, _root_.sum_apply]

end GinibrePermanent977.Anticoncentration
-- Solutions/TwoColumns.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

def twoCols {K : Type*} {r c : ℕ} (X Y : Fin r → K) (R : Fin r → Fin c → K) :
    Fin r → Fin (c+2) → K := fun i => Fin.cons (X i) (Fin.cons (Y i) (R i))

lemma minor_twoCols_zero {K : Type*} {n : ℕ} (X Y : Fin (n+1) → K)
    (R : Fin (n+1) → Fin n → K) :
    minor (n := n+2) (twoCols X Y R) 0 = fun i => Fin.cons (Y i) (R i) := by
  funext i k
  change twoCols X Y R i (skipCol 0 k) = _
  rw [skipCol_succAbove]
  simp [twoCols]

lemma minor_twoCols_one {K : Type*} {n : ℕ} (X Y : Fin (n+1) → K)
    (R : Fin (n+1) → Fin n → K) :
    minor (n := n+2) (twoCols X Y R) 1 = fun i => Fin.cons (X i) (R i) := by
  funext i k
  change twoCols X Y R i (skipCol 1 k) = _
  rw [skipCol_succAbove]
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [twoCols]
  · simp [twoCols, Fin.one_succAbove_succ]

lemma minor_twoCols_succ_succ {K : Type*} {n : ℕ} (X Y : Fin (n+2) → K)
    (R : Fin (n+2) → Fin (n+1) → K) (j : Fin (n+1)) :
    minor (n := n+3) (twoCols X Y R) j.succ.succ =
      twoCols X Y (fun i k => R i (skipCol j k)) := by
  funext i k
  change twoCols X Y R i (skipCol j.succ.succ k) = _
  rw [skipCol_succAbove]
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [twoCols]
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp [twoCols]
    · simp [twoCols, skipCol_succAbove]

lemma cofactor_twoCols_form {K : Type*} [NormedRing K] [InnerProductSpace ℝ K] {n : ℕ}
    (hsmul₁ : ∀ (r : ℝ) (x y : K), (r • x)*y = r • (x*y))
    (hsmul₂ : ∀ (r : ℝ) (x y : K), x*(r • y) = r • (x*y))
    (R : Fin (n+2) → Fin (n+1) → K) (z : Fin (n+1) → K) :
    ∃ L : (Fin (n+2) → K) →ₗ[ℝ] K,
    (∀ X, L X = perK (fun i => Fin.cons (X i) (R i))) ∧
    ∃ Q : (Fin (n+2) → K) →ₗ[ℝ] (Fin (n+2) → K) →ₗ[ℝ] ℝ,
      ∀ X Y a b, realInner (Fin.cons a (Fin.cons b z))
        (perCofactor (n := n+3) (twoCols X Y R)) =
        Q X Y + inner ℝ a (L Y) + inner ℝ b (L X) := by
  classical
  letI : Algebra ℝ K := Algebra.ofModule hsmul₁ hsmul₂
  obtain ⟨L, hL⟩ := perK_cons_column_linear R
  choose P hP using fun j : Fin (n+1) => perK_cons_two_columns_bilinear
    (fun i k => R i (skipCol j k))
  let Q : (Fin (n+2) → K) →ₗ[ℝ] (Fin (n+2) → K) →ₗ[ℝ] ℝ :=
    ∑ j, (P j).compr₂ ((innerSL ℝ (z j)).toLinearMap)
  refine ⟨L, hL, Q, ?_⟩
  intro X Y a b
  unfold realInner
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have h0 : perCofactor (n := n+3) (twoCols X Y R) 0 = L Y := by
    rw [hL]; unfold perCofactor; rw [minor_twoCols_zero]
  have h1 : perCofactor (n := n+3) (twoCols X Y R) 1 = L X := by
    rw [hL]; unfold perCofactor; rw [minor_twoCols_one]
  simp only [Fin.succ_zero_eq_one]
  rw [h0, h1]
  have hQ : Q X Y = ∑ j, inner ℝ (z j)
      (perCofactor (n := n+3) (twoCols X Y R) j.succ.succ) := by
    simp only [Q, LinearMap.sum_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply, LinearMap.compr₂_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hP]
    unfold perCofactor
    rw [minor_twoCols_succ_succ]
    rfl
  rw [hQ]
  ring

end GinibrePermanent977.Anticoncentration
-- Solutions/GinibreMaps.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
set_option autoImplicit false
namespace GinibrePermanent977.Anticoncentration

lemma measurePreserving_delete_coordinate (F : Scalar) {n : ℕ} (j : Fin (n+1)) :
    MeasurePreserving (fun x : Fin (n+1) → F.K => fun k : Fin n => x (skipCol j k))
      (gaussVec F (n+1)) (gaussVec F n) := by
  haveI : IsProbabilityMeasure (gaussVec F n) := by unfold gaussVec; infer_instance
  have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussian F) j
  have hsnd := (measurePreserving_snd (μ := gaussian F)
    (ν := Measure.pi (fun _ : Fin n => gaussian F))).comp hsplit
  change MeasurePreserving _ (Measure.pi (fun _ : Fin (n+1) => gaussian F))
    (Measure.pi (fun _ : Fin n => gaussian F))
  convert hsnd using 1
  ext x k
  rw [skipCol_succAbove]
  rfl

lemma measurePreserving_minor (F : Scalar) {n : ℕ} (j : Fin (n+1)) :
    MeasurePreserving (fun B : Fin n → Fin (n+1) → F.K => minor (n := n+1) B j)
      (ginibre F n (n+1)) (ginibre F n n) := by
  haveI : IsProbabilityMeasure (gaussVec F n) := by unfold gaussVec; infer_instance
  have h := measurePreserving_pi (fun _ : Fin n => gaussVec F (n+1))
    (fun _ : Fin n => gaussVec F n) (fun _ => measurePreserving_delete_coordinate F j)
  exact h

lemma measurePreserving_ginibre_columns_perm (F : Scalar) {m n : ℕ}
    (τ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun B : Fin m → Fin n → F.K => fun i j => B i (τ j))
      (ginibre F m n) (ginibre F m n) := by
  haveI : IsProbabilityMeasure (gaussVec F n) := by unfold gaussVec; infer_instance
  have h := measurePreserving_piCongrLeft (fun _ : Fin n => gaussian F) τ.symm
  have hrow : MeasurePreserving (fun x : Fin n → F.K => fun j => x (τ j))
      (gaussVec F n) (gaussVec F n) := by
    change MeasurePreserving _ (Measure.pi (fun _ : Fin n => gaussian F))
      (Measure.pi (fun _ : Fin n => gaussian F))
    convert h using 1
    ext x j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  exact measurePreserving_pi (fun _ : Fin m => gaussVec F n)
    (fun _ : Fin m => gaussVec F n) (fun _ => hrow)

end GinibrePermanent977.Anticoncentration
-- Solutions/ColumnMeasures.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma measurePreserving_cons_column (F : Scalar) (m n : ℕ) :
    MeasurePreserving (fun p : (Fin m → F.K) × (Fin m → Fin n → F.K) =>
      fun i => Fin.cons (p.1 i) (p.2 i))
      ((gaussVec F m).prod (ginibre F m n)) (ginibre F m (n+1)) := by
  haveI : IsProbabilityMeasure (gaussVec F n) := by unfold gaussVec; infer_instance
  haveI : IsProbabilityMeasure (gaussVec F (n+1)) := by unfold gaussVec; infer_instance
  have hrow := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussian F) 0).symm
  have hrows := measurePreserving_pi
    (fun _ : Fin m => (gaussian F).prod (gaussVec F n))
    (fun _ : Fin m => gaussVec F (n+1)) (fun _ => hrow)
  have hprod := (measurePreserving_arrowProdEquivProdArrow F.K (Fin n → F.K) (Fin m)
    (fun _ => gaussian F) (fun _ => gaussVec F n)).symm
  convert hrows.comp hprod using 1 <;> try rfl
  ext p i j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

lemma measurePreserving_twoCols (F : Scalar) (m n : ℕ) :
    MeasurePreserving (fun p : (Fin m → F.K) × ((Fin m → F.K) × (Fin m → Fin n → F.K)) =>
      twoCols p.1 p.2.1 p.2.2)
      ((gaussVec F m).prod ((gaussVec F m).prod (ginibre F m n)))
      (ginibre F m (n+2)) := by
  haveI : IsProbabilityMeasure (gaussVec F m) := by unfold gaussVec; infer_instance
  haveI : IsProbabilityMeasure (ginibre F m n) := by unfold ginibre; infer_instance
  have h := (measurePreserving_cons_column F m (n+1)).comp
    ((MeasurePreserving.id (gaussVec F m)).prod (measurePreserving_cons_column F m n))
  exact h

end GinibrePermanent977.Anticoncentration
-- Solutions/BilinearCoordinates.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma bilinear_dotProduct {d k : ℕ}
    (Q : (Fin d → ℝ) →ₗ[ℝ] (Fin k → ℝ) →ₗ[ℝ] ℝ) (x : Fin d → ℝ) (y : Fin k → ℝ) :
    x ⬝ᵥ ((fun i j => Q (Pi.single i 1) (Pi.single j 1)) *ᵥ y) = Q x y := by
  classical
  have hx : (∑ i : Fin d, x i • Pi.single i (1 : ℝ)) = x := by
    ext i
    simp [Pi.smul_apply, Pi.single_apply]
  have hy : (∑ j : Fin k, y j • Pi.single j (1 : ℝ)) = y := by
    ext j
    simp [Pi.smul_apply, Pi.single_apply]
  conv_rhs => rw [← hx, ← hy]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    RingHom.id_apply, smul_eq_mul, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end GinibrePermanent977.Anticoncentration
-- Solutions/ConditionalForm.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

lemma cofactor_twoCols_matrix_form {K : Type*} [NormedRing K] [InnerProductSpace ℝ K]
    {n d k : ℕ}
    (hsmul₁ : ∀ (r : ℝ) (x y : K), (r • x)*y = r • (x*y))
    (hsmul₂ : ∀ (r : ℝ) (x y : K), x*(r • y) = r • (x*y))
    (R : Fin (n+2) → Fin (n+1) → K) (z : Fin (n+1) → K)
    (Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin (n+2) → K)) (e : (Fin k → ℝ) →ₗ[ℝ] K) :
    let T : Matrix (Fin d) (Fin d) ℝ := fun i j =>
      realInner (Fin.cons 0 (Fin.cons 0 z))
        (perCofactor (n := n+3) (twoCols (Φ (Pi.single i 1)) (Φ (Pi.single j 1)) R))
    let M : Matrix (Fin d) (Fin k) ℝ := fun i j =>
      inner ℝ (e (Pi.single j 1))
        (perK (fun a => Fin.cons (Φ (Pi.single i 1) a) (R a)))
    ∀ X Y a b, realInner (Fin.cons (e a) (Fin.cons (e b) z))
      (perCofactor (n := n+3) (twoCols (Φ X) (Φ Y) R)) =
      X ⬝ᵥ (T *ᵥ Y) + X ⬝ᵥ (M *ᵥ b) + Y ⬝ᵥ (M *ᵥ a) := by
  classical
  obtain ⟨L, hL, Q, hQ⟩ := cofactor_twoCols_form hsmul₁ hsmul₂ R z
  let Q' := (Q.comp Φ).compl₂ Φ
  let L' := ((innerₗ K).comp (L.comp Φ)).compl₂ e
  intro T M X Y a b
  have hT : T = fun i j => Q' (Pi.single i 1) (Pi.single j 1) := by
    ext i j
    dsimp [T, Q']
    rw [hQ]
    simp
  have hM : M = fun i j => L' (Pi.single i 1) (Pi.single j 1) := by
    ext i j
    dsimp [M, L']
    rw [hL, real_inner_comm]
  rw [hT, hM, bilinear_dotProduct, bilinear_dotProduct, bilinear_dotProduct, hQ]
  dsimp [Q', L']
  rw [real_inner_comm (L (Φ X)), real_inner_comm (L (Φ Y))]
  ring

end GinibrePermanent977.Anticoncentration
-- Solutions/CofactorPositivity.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

lemma gaussian_multilinear_characteristic_nonneg (F : Scalar) {m n : ℕ}
    (P : MultilinearMap ℝ (fun _ : Fin (m+1) => Fin n → F.K) ℝ) (hP : Continuous P) :
    0 ≤ (∫ B, Complex.exp (Complex.I * ((P B : ℝ) : ℂ)) ∂ginibre F (m+1) n) := by
  haveI : SecondCountableTopology F.K := by
    cases F
    · exact inferInstanceAs (SecondCountableTopology ℝ)
    · exact inferInstanceAs (SecondCountableTopology ℂ)
    · exact inferInstanceAs (SecondCountableTopology ℍ[ℝ])
  haveI : IsProbabilityMeasure (gaussVec F n) := by unfold gaussVec; infer_instance
  change 0 ≤ (∫ B, Complex.exp (Complex.I * ((P B : ℝ) : ℂ))
    ∂Measure.pi (fun _ : Fin (m+1) => gaussVec F n))
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => gaussVec F n) 0).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
    Fin.zero_succAbove, Function.comp_def]
  have hPm : Measurable P := hP.measurable
  have hcons : Measurable (fun p : (Fin n → F.K) × (Fin m → Fin n → F.K) => (Fin.cons p.1 p.2 : Fin (m+1) → Fin n → F.K)) := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply i).comp measurable_snd
  let f := fun p : (Fin n → F.K) × (Fin m → Fin n → F.K) =>
    Complex.exp (Complex.I * ((P (Fin.cons p.1 p.2) : ℝ) : ℂ))
  have hi : Integrable f ((gaussVec F n).prod (Measure.pi fun _ : Fin m => gaussVec F n)) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (Measurable.aestronglyMeasurable (by dsimp [f]; fun_prop))
    exact Filter.Eventually.of_forall (fun p => by simp [f, Complex.norm_exp])
  change 0 ≤ ∫ p, f p ∂(gaussVec F n).prod (Measure.pi fun _ : Fin m => gaussVec F n)
  rw [integral_prod_symm _ hi]
  have hnn (R : Fin m → Fin n → F.K) : 0 ≤ ∫ x, f (x,R) ∂gaussVec F n := by
    let l := P.toLinearMap (Fin.cons 0 R) 0
    have he (x : Fin n → F.K) : P (Fin.cons x R) = l x := by
      change P (Fin.cons x R) = P (Function.update (Fin.cons 0 R) 0 x)
      congr 1
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    simpa only [f, he] using vector_scalar_gaussian_linear_nonneg F l
  have ho := hi.integral_prod_right
  have hr : (∫ R, ∫ x, f (x,R) ∂gaussVec F n ∂Measure.pi (fun _ : Fin m => gaussVec F n)).re =
      ∫ R, (∫ x, f (x,R) ∂gaussVec F n).re ∂Measure.pi (fun _ : Fin m => gaussVec F n) :=
    (integral_re ho).symm
  have him : (∫ R, ∫ x, f (x,R) ∂gaussVec F n ∂Measure.pi (fun _ : Fin m => gaussVec F n)).im =
      ∫ R, (∫ x, f (x,R) ∂gaussVec F n).im ∂Measure.pi (fun _ : Fin m => gaussVec F n) :=
    (integral_im ho).symm
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [hr]
    apply integral_nonneg
    intro R
    exact (Complex.nonneg_iff.mp (hnn R)).1
  · rw [him]
    have hzero (R : Fin m → Fin n → F.K) : (∫ x, f (x,R) ∂gaussVec F n).im = 0 :=
      (Complex.nonneg_iff.mp (hnn R)).2.symm
    simp only [hzero, integral_zero]

lemma continuous_perCofactor {K : Type*} [NormedRing K] {n : ℕ} :
    Continuous (perCofactor : (Fin (n-1) → Fin n → K) → Fin n → K) := by
  apply continuous_pi
  intro j
  exact continuous_perK.comp (by unfold minor; fun_prop)

lemma perCofactor_characteristic_nonnegative (F : Scalar) {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → F.K) : 0 ≤ charFunK (ginibre F (n-1) n) perCofactor z := by
  have hsmul₁ (r : ℝ) (x y : F.K) : (r • x)*y = r • (x*y) := by
    cases F
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℝ from x) (show ℝ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℂ from x) (show ℂ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℍ[ℝ] from x) (show ℍ[ℝ] from y)
  have hsmul₂ (r : ℝ) (x y : F.K) : x*(r • y) = r • (x*y) := by
    cases F
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℝ from x) (show ℝ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℂ from x) (show ℂ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℍ[ℝ] from x) (show ℍ[ℝ] from y)
  letI : Algebra ℝ F.K := Algebra.ofModule hsmul₁ hsmul₂
  obtain ⟨H,hH⟩ := perCofactor_rows_multilinear (K := F.K) n
    (fun j => (innerSL ℝ (z j)).toLinearMap)
  have hHeq (B : Fin (n-1) → Fin n → F.K) : H B = realInner z (perCofactor B) := hH B
  have hcont : Continuous H := by
    have heq : (H : (Fin (n-1) → Fin n → F.K) → ℝ) = fun B => realInner z (perCofactor B) :=
      funext hHeq
    rw [heq]
    unfold realInner
    apply continuous_finsetSum
    intro j _
    exact continuous_const.inner (continuous_apply j |>.comp continuous_perCofactor)
  obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  have hHpoint (B : Fin (m+1) → Fin (m+2) → F.K) :
      H B = realInner z (perCofactor (n := m+2) B) := hHeq B
  have hp := gaussian_multilinear_characteristic_nonneg F H hcont
  have heq : (∫ B : Fin (m+1) → Fin (m+2) → F.K,
      Complex.exp (Complex.I * ((H B : ℝ) : ℂ)) ∂ginibre F (m+1) (m+2)) =
      charFunK (ginibre F (m+2-1) (m+2)) perCofactor z := by
    unfold charFunK
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro B
    exact congrArg (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ))) (hHpoint B)
  exact hp.trans_eq heq

end GinibrePermanent977.Anticoncentration
-- Solutions/ConditionalCharacteristic.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

def phaseMatrices (F : Scalar) {n d k : ℕ}
    (Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin (n+2) → F.K)) (e : (Fin k → ℝ) →ₗ[ℝ] F.K)
    (z : Fin (n+1) → F.K) (R : Fin (n+2) → Fin (n+1) → F.K) :
    (Fin d → Fin d → ℝ) × (Fin d → Fin k → ℝ) :=
    (fun i j => realInner (Fin.cons 0 (Fin.cons 0 z))
        (perCofactor (n := n+3) (twoCols (Φ (Pi.single i 1)) (Φ (Pi.single j 1)) R)),
      fun i j => inner ℝ (e (Pi.single j 1))
        (perK (fun a => Fin.cons (Φ (Pi.single i 1) a) (R a))))

lemma measurable_phaseMatrices (F : Scalar) {n d k : ℕ}
    (Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin (n+2) → F.K)) (e : (Fin k → ℝ) →ₗ[ℝ] F.K)
    (z : Fin (n+1) → F.K) : Measurable (phaseMatrices F Φ e z) := by
  unfold phaseMatrices realInner
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr; intro i
    apply measurable_pi_iff.mpr; intro j
    apply Finset.measurable_sum; intro a _
    apply Measurable.inner measurable_const
    apply (measurable_pi_apply a).comp
    apply continuous_perCofactor.measurable.comp
    apply measurable_pi_iff.mpr; intro b
    apply measurable_pi_iff.mpr; intro c
    refine Fin.cases ?_ (fun c => ?_) c
    · exact measurable_const
    · refine Fin.cases ?_ (fun c => ?_) c
      · exact measurable_const
      · exact (measurable_pi_apply c).comp (measurable_pi_apply b)
  · apply measurable_pi_iff.mpr; intro i
    apply measurable_pi_iff.mpr; intro j
    apply Measurable.inner measurable_const
    apply continuous_perK.measurable.comp
    apply measurable_pi_iff.mpr; intro b
    apply measurable_pi_iff.mpr; intro c
    refine Fin.cases ?_ (fun c => ?_) c
    · exact measurable_const
    · exact (measurable_pi_apply c).comp (measurable_pi_apply b)

lemma conditional_cofactor_bilinChar (F : Scalar) {n d k : ℕ}
    (Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin (n+2) → F.K)) (e : (Fin k → ℝ) →ₗ[ℝ] F.K)
    (z : Fin (n+1) → F.K) (R : Fin (n+2) → Fin (n+1) → F.K)
    (a b : Fin k → ℝ) :
    (∫ p : (Fin d → ℝ) × (Fin d → ℝ),
      Complex.exp (Complex.I * ((realInner (Fin.cons (e a) (Fin.cons (e b) z))
        (perCofactor (n := n+3) (twoCols (Φ p.1) (Φ p.2) R)) : ℝ) : ℂ))
      ∂(SmoothBerr.stdGaussianVec d).prod (SmoothBerr.stdGaussianVec d)) =
    bilinChar (Matrix.of (phaseMatrices F Φ e z R).1)
      (Matrix.of (phaseMatrices F Φ e z R).2) a b := by
  unfold bilinChar
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  apply congrArg (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)))
  exact cofactor_twoCols_matrix_form (scalar_smul_mul F) (scalar_mul_smul F) R z Φ e p.1 p.2 a b

lemma measurePreserving_raw_twoCols (F : Scalar) {n d : ℕ}
    (Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin (n+2) → F.K))
    (hΦ : MeasurePreserving Φ (SmoothBerr.stdGaussianVec d) (gaussVec F (n+2))) :
    MeasurePreserving
      (fun p : (Fin (n+2) → Fin (n+1) → F.K) × ((Fin d → ℝ) × (Fin d → ℝ)) =>
        twoCols (Φ p.2.1) (Φ p.2.2) p.1)
      ((ginibre F (n+2) (n+1)).prod
        ((SmoothBerr.stdGaussianVec d).prod (SmoothBerr.stdGaussianVec d)))
      (ginibre F (n+2) (n+3)) := by
  haveI : IsProbabilityMeasure (gaussVec F (n+2)) := by unfold gaussVec; infer_instance
  haveI : IsProbabilityMeasure (ginibre F (n+2) (n+1)) := by unfold ginibre; infer_instance
  let ρ := SmoothBerr.stdGaussianVec d
  let ν := gaussVec F (n+2)
  let η := ginibre F (n+2) (n+1)
  have h0 : MeasurePreserving Prod.swap (η.prod (ρ.prod ρ)) ((ρ.prod ρ).prod η) :=
    Measure.measurePreserving_swap
  have h1 := (hΦ.prod hΦ).prod (MeasurePreserving.id η)
  have h2 := measurePreserving_prodAssoc ν ν η
  exact (measurePreserving_twoCols F (n+2) (n+1)).comp (h2.comp (h1.comp h0))

lemma cofactor_characteristic_bilin_integral (F : Scalar) {n d k : ℕ}
    (Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin (n+2) → F.K))
    (hΦ : MeasurePreserving Φ (SmoothBerr.stdGaussianVec d) (gaussVec F (n+2)))
    (e : (Fin k → ℝ) →ₗ[ℝ] F.K) (z : Fin (n+1) → F.K) (a b : Fin k → ℝ) :
    charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3))
      (Fin.cons (e a) (Fin.cons (e b) z)) =
    ∫ R, bilinChar (Matrix.of (phaseMatrices F Φ e z R).1)
      (Matrix.of (phaseMatrices F Φ e z R).2) a b ∂ginibre F (n+2) (n+1) := by
  haveI : IsProbabilityMeasure (ginibre F (n+2) (n+1)) := by unfold ginibre; infer_instance
  let g := fun G : Fin (n+2) → Fin (n+3) → F.K =>
    Complex.exp (Complex.I * ((realInner (Fin.cons (e a) (Fin.cons (e b) z))
      (perCofactor (n := n+3) G) : ℝ) : ℂ))
  have hCm : Measurable (perCofactor (n := n+3) :
      (Fin (n+2) → Fin (n+3) → F.K) → Fin (n+3) → F.K) := continuous_perCofactor.measurable
  have hg : Measurable g := by unfold g realInner; fun_prop
  have hp := measurePreserving_raw_twoCols F Φ hΦ
  have he := integral_map hp.aemeasurable hg.aestronglyMeasurable
  rw [hp.map_eq] at he
  have hi : Integrable
      (fun p : (Fin (n+2) → Fin (n+1) → F.K) × ((Fin d → ℝ) × (Fin d → ℝ)) =>
        g (twoCols (Φ p.2.1) (Φ p.2.2) p.1))
      ((ginibre F (n+2) (n+1)).prod
        ((SmoothBerr.stdGaussianVec d).prod (SmoothBerr.stdGaussianVec d))) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hg.comp hp.measurable).aestronglyMeasurable
    exact Eventually.of_forall (fun p => by simp [g, Complex.norm_exp])
  calc
    _ = ∫ p : (Fin (n+2) → Fin (n+1) → F.K) × ((Fin d → ℝ) × (Fin d → ℝ)),
        g (twoCols (Φ p.2.1) (Φ p.2.2) p.1)
        ∂((ginibre F (n+2) (n+1)).prod
          ((SmoothBerr.stdGaussianVec d).prod (SmoothBerr.stdGaussianVec d))) := he
    _ = ∫ R, ∫ p : (Fin d → ℝ) × (Fin d → ℝ), g (twoCols (Φ p.1) (Φ p.2) R)
        ∂(SmoothBerr.stdGaussianVec d).prod (SmoothBerr.stdGaussianVec d)
        ∂ginibre F (n+2) (n+1) := integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun R => conditional_cofactor_bilinChar F Φ e z R a b)

end GinibrePermanent977.Anticoncentration
-- Solutions/CofactorPairCompression.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

lemma continuous_bilin_parameters {d k : ℕ} (a b : Fin k → ℝ) :
    Continuous (fun q : (Fin d → Fin d → ℝ) × (Fin d → Fin k → ℝ) =>
      bilinChar (Matrix.of q.1) (Matrix.of q.2) a b) := by
  unfold bilinChar
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro q
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · intro q
    exact Eventually.of_forall (fun p => by simp [Complex.norm_exp])
  · exact integrable_const 1
  · apply Eventually.of_forall
    intro p
    fun_prop

lemma norm_bilinChar_le_one {d k : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ) : ‖bilinChar T L a b‖ ≤ 1 := by
  unfold bilinChar
  have h := norm_integral_le_of_norm_le_const (C := (1 : ℝ))
    (μ := (SmoothBerr.stdGaussianVec d).prod (SmoothBerr.stdGaussianVec d))
    (f := fun p : (Fin d → ℝ) × (Fin d → ℝ) => Complex.exp (Complex.I *
      ((p.1 ⬝ᵥ (T *ᵥ p.2) + p.1 ⬝ᵥ (L *ᵥ b) + p.2 ⬝ᵥ (L *ᵥ a) : ℝ) : ℂ)))
    (Eventually.of_forall (fun p => by simp [Complex.norm_exp]))
  simpa using h

lemma cofactor_pair_compression_raw (F : Scalar) {n d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin (n+2) → F.K))
    (hΦ : MeasurePreserving Φ (SmoothBerr.stdGaussianVec d) (gaussVec F (n+2)))
    (e : (Fin k → ℝ) →ₗ[ℝ] F.K) (z : Fin (n+1) → F.K)
    (a b : Fin k → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3))
      (Fin.cons (e (Real.sqrt θ • a)) (Fin.cons (e (Real.sqrt (1-θ) • b)) z))).re ≤
    max (charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3))
        (Fin.cons (e a) (Fin.cons (e 0) z))).re
      (charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3))
        (Fin.cons (e 0) (Fin.cons (e b) z))).re := by
  haveI : IsProbabilityMeasure (ginibre F (n+2) (n+1)) := by unfold ginibre; infer_instance
  let ρ := (ginibre F (n+2) (n+1)).map (phaseMatrices F Φ e z)
  have hm := measurable_phaseMatrices F Φ e z
  haveI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hm.aemeasurable
  let H := fun a b : Fin k → ℝ =>
    charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3))
      (Fin.cons (e a) (Fin.cons (e b) z))
  have hH (a b : Fin k → ℝ) : H a b =
      ∫ q, bilinChar (Matrix.of q.1) (Matrix.of q.2) a b ∂ρ := by
    rw [show H a b = _ from cofactor_characteristic_bilin_integral F Φ hΦ e z a b]
    exact (integral_map hm.aemeasurable
      (continuous_bilin_parameters a b).measurable.aestronglyMeasurable).symm
  have hi (a b : Fin k → ℝ) : Integrable
      (fun q => bilinChar (Matrix.of q.1) (Matrix.of q.2) a b) ρ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (continuous_bilin_parameters a b).measurable.aestronglyMeasurable
    exact Eventually.of_forall (fun q => norm_bilinChar_le_one _ _ a b)
  have hc := corollary_3_3_two_coordinate_compression hd hk ρ a b θ hθ0 hθ1
  change (H (Real.sqrt θ • a) (Real.sqrt (1-θ) • b)).re ≤ max (H a 0).re (H 0 b).re
  calc
    _ ≤ ‖H (Real.sqrt θ • a) (Real.sqrt (1-θ) • b)‖ := Complex.re_le_norm _
    _ ≤ ∫ q, ‖bilinChar (Matrix.of q.1) (Matrix.of q.2)
        (Real.sqrt θ • a) (Real.sqrt (1-θ) • b)‖ ∂ρ := by
      rw [hH]
      exact norm_integral_le_integral_norm _
    _ ≤ max (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) a 0).re ∂ρ)
        (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) 0 b).re ∂ρ) := hc.1.trans hc.2
    _ = _ := by
      have hr (a b : Fin k → ℝ) :
          (∫ q, bilinChar (Matrix.of q.1) (Matrix.of q.2) a b ∂ρ).re =
          ∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) a b).re ∂ρ := (integral_re (hi a b)).symm
      rw [← hr a 0, ← hr 0 b, ← hH, ← hH]

end GinibrePermanent977.Anticoncentration
-- Solutions/PairScaling.lean
open scoped Real
set_option autoImplicit false
namespace GinibrePermanent977.Anticoncentration

lemma pair_scaling_parameters (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    let r := Real.sqrt (a^2+b^2)
    let θ := a^2/(a^2+b^2)
    0 ≤ θ ∧ θ ≤ 1 ∧ Real.sqrt θ*(r/a) = 1 ∧ Real.sqrt (1-θ)*(r/b) = 1 := by
  dsimp
  have hD : 0 < a^2+b^2 := by positivity
  have hr : Real.sqrt (a^2+b^2) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  refine ⟨by positivity, (div_le_one hD).2 (by nlinarith), ?_, ?_⟩
  · rw [Real.sqrt_div (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
    field_simp
  · have heq : 1-a^2/(a^2+b^2) = b^2/(a^2+b^2) := by field_simp; ring
    rw [heq, Real.sqrt_div (sq_nonneg b), Real.sqrt_sq_eq_abs, abs_of_pos hb]
    field_simp

end GinibrePermanent977.Anticoncentration
-- Solutions/FirstPairCompression.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ComplexOrder Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

lemma cofactor_first_pair_compression (F : Scalar) {n : ℕ}
    (z : Fin (n+1) → F.K) (a b : F.K) (ha : a ≠ 0) (hb : b ≠ 0) :
    let r := Real.sqrt (‖a‖^2+‖b‖^2)
    (charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3))
      (Fin.cons a (Fin.cons b z))).re ≤
    max (charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3))
        (Fin.cons ((r/‖a‖) • a) (Fin.cons 0 z))).re
      (charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3))
        (Fin.cons 0 (Fin.cons ((r/‖b‖) • b) z))).re := by
  haveI : Nontrivial F.K := by
    cases F
    · exact inferInstanceAs (Nontrivial ℝ)
    · exact inferInstanceAs (Nontrivial ℂ)
    · exact inferInstanceAs (Nontrivial ℍ[ℝ])
  obtain ⟨d, hd, Φ, hΦ⟩ := gaussian_vector_coordinates F (n+2) (by omega)
  let k := Module.finrank ℝ F.K
  let e : (Fin k → ℝ) ≃ₗ[ℝ] F.K := (stdOrthonormalBasis ℝ F.K).toBasis.equivFun.symm
  have hk : 1 ≤ k := Module.finrank_pos
  let r := Real.sqrt (‖a‖^2+‖b‖^2)
  let θ := ‖a‖^2/(‖a‖^2+‖b‖^2)
  obtain ⟨hθ0,hθ1,hθa,hθb⟩ := pair_scaling_parameters ‖a‖ ‖b‖ (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb)
  have heqa : Real.sqrt θ • ((r/‖a‖) • a) = a := by
    rw [smul_smul, hθa, one_smul]
  have heqb : Real.sqrt (1-θ) • ((r/‖b‖) • b) = b := by
    rw [smul_smul, hθb, one_smul]
  have h := cofactor_pair_compression_raw F hd hk Φ hΦ e.toLinearMap z
    (e.symm ((r/‖a‖) • a)) (e.symm ((r/‖b‖) • b)) θ hθ0 hθ1
  simpa only [LinearEquiv.coe_toLinearMap, map_smul, LinearEquiv.apply_symm_apply, map_zero,
    heqa, heqb] using h

end GinibrePermanent977.Anticoncentration
-- Solutions/CoordinateCompression.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
set_option autoImplicit false
namespace GinibrePermanent977.Anticoncentration

lemma finite_support_descent {E : Type*} [Zero E] [DecidableEq E] {n : ℕ}
    (φ r : (Fin n → E) → ℝ) (f : ℝ → ℝ)
    (hsmall : ∀ z, (Finset.univ.filter (fun i => z i ≠ 0)).card ≤ 1 → φ z ≤ f (r z))
    (hstep : ∀ z, 1 < (Finset.univ.filter (fun i => z i ≠ 0)).card →
      ∃ w, (Finset.univ.filter (fun i => w i ≠ 0)).card <
          (Finset.univ.filter (fun i => z i ≠ 0)).card ∧ r w = r z ∧ φ z ≤ φ w) :
    ∀ z, φ z ≤ f (r z) := by
  classical
  intro z
  induction z using ((measure (fun z : Fin n → E =>
      (Finset.univ.filter (fun i => z i ≠ 0)).card)).wf).induction with
  | h z ih =>
    by_cases hz : (Finset.univ.filter (fun i => z i ≠ 0)).card ≤ 1
    · exact hsmall z hz
    obtain ⟨w, hw, hr, hp⟩ := hstep z (by omega)
    calc
      φ z ≤ φ w := hp
      _ ≤ f (r w) := ih w hw
      _ = f (r z) := congrArg f hr

end GinibrePermanent977.Anticoncentration
-- Solutions/SupportDescent.lean
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
namespace GinibrePermanent977.Anticoncentration

lemma support_card_cons {E : Type*} [Zero E] [DecidableEq E] {n : ℕ} (a : E) (z : Fin n → E) :
    (Finset.univ.filter (fun i : Fin (n+1) => (Fin.cons a z : Fin (n+1) → E) i ≠ 0)).card =
    (if a = 0 then 0 else 1) + (Finset.univ.filter (fun i => z i ≠ 0)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  by_cases h : a = 0 <;> simp [h]

lemma support_card_perm {E : Type*} [Zero E] [DecidableEq E] {n : ℕ}
    (τ : Equiv.Perm (Fin n)) (z : Fin n → E) :
    (Finset.univ.filter (fun i => z (τ i) ≠ 0)).card =
    (Finset.univ.filter (fun i => z i ≠ 0)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Equiv.sum_comp τ (fun i => if z i ≠ 0 then (1 : ℕ) else 0)

lemma support_card_le_one {E : Type*} [Zero E] [DecidableEq E] {n : ℕ}
    (z : Fin n → E) (h : (Finset.univ.filter (fun i => z i ≠ 0)).card ≤ 1) :
    z = 0 ∨ ∃ i, z = Pi.single i (z i) := by
  classical
  by_cases hz : z = 0
  · exact Or.inl hz
  right
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hz
    ext i
    exact h i
  refine ⟨i, ?_⟩
  ext j
  by_cases hji : j = i
  · simp [hji]
  · have hj : z j = 0 := by
      by_contra hnj
      have he := Finset.card_le_one.mp h j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnj⟩) i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      exact hji he
    simp [Pi.single_eq_of_ne hji, hj]

end GinibrePermanent977.Anticoncentration
-- Solutions/GaussianRow.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder Quaternion RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma scalar_inner_mul_right (F : Scalar) (z x c : F.K) :
    inner ℝ z (x*c) = inner ℝ (z*star c) x := by
  cases F
  · dsimp only [Scalar.K] at z x c ⊢
    simp [RCLike.inner_apply, mul_assoc, mul_comm, mul_left_comm]
  · dsimp only [Scalar.K] at z x c ⊢
    simp [real_inner_eq_re_inner, RCLike.inner_apply, star_mul, mul_assoc,
      mul_comm, mul_left_comm]
  · dsimp only [Scalar.K] at z x c ⊢
    simp [Quaternion.inner_def, star_mul, mul_assoc]

lemma scalar_norm_mul_star (F : Scalar) (z c : F.K) : ‖z*star c‖ = ‖z‖*‖c‖ := by
  cases F <;> dsimp only [Scalar.K] at z c ⊢
  · exact (norm_mul z (star c)).trans (congrArg (fun r : ℝ => ‖z‖*r) (norm_star c))
  · exact (norm_mul z (star c)).trans (congrArg (fun r : ℝ => ‖z‖*r) (norm_star c))
  · exact (norm_mul z (star c)).trans (congrArg (fun r : ℝ => ‖z‖*r) (norm_star c))

lemma gaussian_row_characteristic (F : Scalar) {n : ℕ} (C : Fin n → F.K) (z : F.K) :
    (∫ g : Fin n → F.K, Complex.exp (Complex.I * ((inner ℝ z (∑ j, g j*C j) : ℝ) : ℂ))
      ∂gaussVec F n) =
    (Real.exp (-‖z‖^2*(∑ j, ‖C j‖^2)/(2*(F.beta : ℝ))) : ℂ) := by
  have he (g : Fin n → F.K) : inner ℝ z (∑ j, g j*C j) =
      realInner (fun j => z*star (C j)) g := by
    simp only [inner_sum, realInner, scalar_inner_mul_right]
  simp_rw [he]
  rw [vector_scalar_gaussian_characteristic]
  congr 3
  simp only [scalar_norm_mul_star, mul_pow]
  rw [← Finset.mul_sum]
  ring

lemma permanent_characteristic_first_row (F : Scalar) {n : ℕ} (z : F.K) :
    (∫ G : Fin (n+1) → Fin (n+1) → F.K,
      Complex.exp (Complex.I * ((inner ℝ z (perK G) : ℝ) : ℂ)) ∂ginibre F (n+1) (n+1)) =
    ∫ B : Fin n → Fin (n+1) → F.K,
      (Real.exp (-‖z‖^2*(∑ j, ‖perCofactor (n := n+1) B j‖^2)/(2*(F.beta : ℝ))) : ℂ)
      ∂ginibre F n (n+1) := by
  haveI : SecondCountableTopology F.K := by
    cases F
    · exact inferInstanceAs (SecondCountableTopology ℝ)
    · exact inferInstanceAs (SecondCountableTopology ℂ)
    · exact inferInstanceAs (SecondCountableTopology ℍ[ℝ])
  haveI : IsProbabilityMeasure (gaussVec F (n+1)) := by unfold gaussVec; infer_instance
  change (∫ G, Complex.exp (Complex.I * ((inner ℝ z (perK G) : ℝ) : ℂ))
      ∂Measure.pi (fun _ : Fin (n+1) => gaussVec F (n+1))) = _
  have hsplit := (measurePreserving_piFinSuccAbove (n := n)
    (α := fun _ : Fin (n+1) => Fin (n+1) → F.K)
    (fun _ : Fin (n+1) => gaussVec F (n+1)) 0).symm
  have hsplitIntegral := hsplit.integral_comp'
    (fun G : Fin (n+1) → Fin (n+1) → F.K =>
      Complex.exp (Complex.I * ((inner ℝ z (perK G) : ℝ) : ℂ)))
  rw [← hsplitIntegral]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
    Fin.zero_succAbove]
  have hcons : Measurable (fun p : (Fin (n+1) → F.K) × (Fin n → Fin (n+1) → F.K) =>
      (Fin.cons p.1 p.2 : Fin (n+1) → Fin (n+1) → F.K)) := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply i).comp measurable_snd
  have hPm : Measurable (perK : (Fin (n+1) → Fin (n+1) → F.K) → F.K) := continuous_perK.measurable
  let f := fun p : (Fin (n+1) → F.K) × (Fin n → Fin (n+1) → F.K) =>
    Complex.exp (Complex.I * ((inner ℝ z (perK (Fin.cons p.1 p.2)) : ℝ) : ℂ))
  have hi : Integrable f ((gaussVec F (n+1)).prod (Measure.pi fun _ : Fin n => gaussVec F (n+1))) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (Measurable.aestronglyMeasurable (by dsimp [f]; fun_prop))
    exact Filter.Eventually.of_forall (fun p => by simp [f, Complex.norm_exp])
  change (∫ p, f p ∂(gaussVec F (n+1)).prod (Measure.pi fun _ : Fin n => gaussVec F (n+1))) = _
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro B
  dsimp only [f]
  simp_rw [perK_cons_row]
  exact gaussian_row_characteristic F (perCofactor (n := n+1) B) z

end GinibrePermanent977.Anticoncentration

-- Solutions/CofactorEndpoint.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder Quaternion RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma cofactor_characteristic_single (F : Scalar) {n : ℕ} (j : Fin (n+1)) (z : F.K) :
    charFunK (ginibre F n (n+1)) (perCofactor (n := n+1)) (Pi.single j z) =
    ∫ G : Fin n → Fin n → F.K,
      Complex.exp (Complex.I * ((inner ℝ z (perK G) : ℝ) : ℂ)) ∂ginibre F n n := by
  haveI : SecondCountableTopology F.K := by
    cases F
    · exact inferInstanceAs (SecondCountableTopology ℝ)
    · exact inferInstanceAs (SecondCountableTopology ℂ)
    · exact inferInstanceAs (SecondCountableTopology ℍ[ℝ])
  have h := measurePreserving_minor F j
  let g := fun G : Fin n → Fin n → F.K =>
    Complex.exp (Complex.I * ((inner ℝ z (perK G) : ℝ) : ℂ))
  have hPm : Measurable (perK : (Fin n → Fin n → F.K) → F.K) := continuous_perK.measurable
  have hg : Measurable g := by dsimp [g]; fun_prop
  have he := (integral_map h.aemeasurable hg.aestronglyMeasurable).symm
  rw [h.map_eq] at he
  unfold charFunK
  have hsingle (B : Fin n → Fin (n+1) → F.K) :
      realInner (Pi.single j z) (perCofactor B) = inner ℝ z (perK (minor (n := n+1) B j)) := by
    unfold realInner
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same]
      rfl
    · intro k hk hkj
      rw [Pi.single_eq_of_ne hkj]
      exact inner_zero_left _
    · simp
  simp_rw [hsingle]
  exact he

lemma cofactor_characteristic_single_recurrence (F : Scalar) {n : ℕ}
    (j : Fin (n+2)) (z : F.K) :
    charFunK (ginibre F (n+1) (n+2)) (perCofactor (n := n+2)) (Pi.single j z) =
    ∫ B : Fin n → Fin (n+1) → F.K,
      (Real.exp (-‖z‖^2*(∑ k, ‖perCofactor (n := n+1) B k‖^2)/(2*(F.beta : ℝ))) : ℂ)
      ∂ginibre F n (n+1) := by
  rw [cofactor_characteristic_single]
  exact permanent_characteristic_first_row F z

end GinibrePermanent977.Anticoncentration
-- Solutions/CofactorSymmetry.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma cofactor_characteristic_columns_perm (F : Scalar) {n : ℕ}
    (τ : Equiv.Perm (Fin (n+1))) (z : Fin (n+1) → F.K) :
    charFunK (ginibre F n (n+1)) (perCofactor (n := n+1)) (fun i => z (τ i)) =
    charFunK (ginibre F n (n+1)) (perCofactor (n := n+1)) z := by
  haveI : SecondCountableTopology F.K := by
    cases F
    · exact inferInstanceAs (SecondCountableTopology ℝ)
    · exact inferInstanceAs (SecondCountableTopology ℂ)
    · exact inferInstanceAs (SecondCountableTopology ℍ[ℝ])
  have h := measurePreserving_ginibre_columns_perm F (m := n) τ
  let g := fun B : Fin n → Fin (n+1) → F.K =>
    Complex.exp (Complex.I * ((realInner (fun i => z (τ i))
      (perCofactor (n := n+1) B) : ℝ) : ℂ))
  have hCm : Measurable (perCofactor (n := n+1) :
    (Fin n → Fin (n+1) → F.K) → Fin (n+1) → F.K) := continuous_perCofactor.measurable
  have hg : Measurable g := by unfold g realInner; fun_prop
  have he := (integral_map h.aemeasurable hg.aestronglyMeasurable).symm
  rw [h.map_eq] at he
  have heq (B : Fin n → Fin (n+1) → F.K) :
      realInner (fun i => z (τ i)) (perCofactor (n := n+1) (fun i j => B i (τ j))) =
      realInner z (perCofactor (n := n+1) B) := by
    unfold realInner
    simp_rw [perCofactor_columns_perm]
    exact Equiv.sum_comp τ (fun j => inner ℝ (z j) (perCofactor (n := n+1) B j))
  unfold charFunK
  rw [← he]
  apply integral_congr_ae
  exact Eventually.of_forall (fun B => congrArg (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ))) (heq B))

lemma exists_perm_first_pair {n : ℕ} (i j : Fin (n+2)) (hij : i ≠ j) :
    ∃ τ : Equiv.Perm (Fin (n+2)), τ 0 = i ∧ τ 1 = j := by
  classical
  let κ : Equiv.Perm (Fin (n+2)) := Equiv.swap 0 i
  have hκi : κ i = 0 := by simp [κ]
  have hκ0 : κ 0 = i := by simp [κ]
  have hj : κ j ≠ 0 := by
    intro h
    apply hij
    exact (κ.injective (h.trans hκi.symm)).symm
  refine ⟨κ * Equiv.swap 1 (κ j), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by intro h; have hv := congrArg Fin.val h; simp at hv) (Ne.symm hj)]
    exact hκ0
  · simp [Equiv.Perm.mul_apply, κ]

end GinibrePermanent977.Anticoncentration
-- Solutions/CoordinateMaximization.lean
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma compressed_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) (ha : a ≠ 0) :
    ‖(Real.sqrt (‖a‖^2+‖b‖^2)/‖a‖) • a‖^2 = ‖a‖^2+‖b‖^2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (by positivity)]
  field_simp

lemma coordinate_maximization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] {n : ℕ} (ψ : (Fin (n+3) → E) → ℝ) (f : ℝ → ℝ)
    (hperm : ∀ (τ : Equiv.Perm (Fin (n+3))) z, ψ (fun i => z (τ i)) = ψ z)
    (hsmall : ∀ z, (Finset.univ.filter (fun i => z i ≠ 0)).card ≤ 1 →
      ψ z ≤ f (∑ i, ‖z i‖^2))
    (hcompress : ∀ a b (z : Fin (n+1) → E), a ≠ 0 → b ≠ 0 →
      let r := Real.sqrt (‖a‖^2+‖b‖^2)
      ψ (Fin.cons a (Fin.cons b z)) ≤
        max (ψ (Fin.cons ((r/‖a‖) • a) (Fin.cons 0 z)))
          (ψ (Fin.cons 0 (Fin.cons ((r/‖b‖) • b) z)))) :
    ∀ z, ψ z ≤ f (∑ i, ‖z i‖^2) := by
  classical
  apply finite_support_descent ψ (fun z => ∑ i, ‖z i‖^2) f hsmall
  intro z hz
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hz
  have ha : z i ≠ 0 := (Finset.mem_filter.mp hi).2
  have hb : z j ≠ 0 := (Finset.mem_filter.mp hj).2
  obtain ⟨τ,hτ0,hτ1⟩ := exists_perm_first_pair (n := n+1) i j hij
  let a := z i
  let b := z j
  let v : Fin (n+1) → E := fun k => z (τ k.succ.succ)
  have heq : (fun k => z (τ k)) = Fin.cons a (Fin.cons b v) := by
    ext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [a, hτ0]
    · refine Fin.cases ?_ (fun k => ?_) k
      · simpa [b, Fin.succ_zero_eq_one] using congrArg z hτ1
      · rfl
  have hψ : ψ (Fin.cons a (Fin.cons b v)) = ψ z := heq ▸ hperm τ z
  have hcard : (Finset.univ.filter (fun i => z i ≠ 0)).card =
      2+(Finset.univ.filter (fun i => v i ≠ 0)).card := by
    have hp := congrArg (fun w : Fin (n+3) → E =>
      (Finset.univ.filter (fun i => w i ≠ 0)).card) heq
    rw [← support_card_perm τ z, hp, support_card_cons, support_card_cons]
    simp [a, b, ha, hb]
    omega
  have hnorm : (∑ i, ‖z i‖^2) = ‖a‖^2+‖b‖^2+(∑ i, ‖v i‖^2) := by
    rw [← Equiv.sum_comp τ (fun i => ‖z i‖^2)]
    change (∑ k, ‖(fun k => z (τ k)) k‖^2) = _
    rw [heq, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  have hc := hcompress a b v ha hb
  rcases le_max_iff.mp hc with hc | hc
  · let w : Fin (n+3) → E := Fin.cons ((Real.sqrt (‖a‖^2+‖b‖^2)/‖a‖) • a) (Fin.cons 0 v)
    refine ⟨fun k => w (τ.symm k), ?_, ?_, ?_⟩
    · rw [support_card_perm, hcard]
      dsimp [w]
      rw [support_card_cons, support_card_cons]
      simp only [ite_true]
      simp only [ne_eq] at *
      split_ifs <;> omega
    · change (∑ i, ‖w (τ.symm i)‖^2) = _
      rw [Equiv.sum_comp τ.symm (fun i => ‖w i‖^2), hnorm]
      dsimp [w]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
      rw [compressed_norm_sq a b ha]
    · rw [hperm, ← hψ]
      exact hc
  · let w : Fin (n+3) → E := Fin.cons 0 (Fin.cons ((Real.sqrt (‖a‖^2+‖b‖^2)/‖b‖) • b) v)
    refine ⟨fun k => w (τ.symm k), ?_, ?_, ?_⟩
    · rw [support_card_perm, hcard]
      dsimp [w]
      rw [support_card_cons, support_card_cons]
      simp only [ite_true, zero_add]
      simp only [ne_eq] at *
      split_ifs <;> omega
    · change (∑ i, ‖w (τ.symm i)‖^2) = _
      rw [Equiv.sum_comp τ.symm (fun i => ‖w i‖^2), hnorm]
      dsimp [w]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
      rw [show ‖a‖^2+‖b‖^2 = ‖b‖^2+‖a‖^2 from add_comm _ _, compressed_norm_sq b a hb]
    · rw [hperm, ← hψ]
      exact hc

end GinibrePermanent977.Anticoncentration
-- Solutions/CofactorTwo.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma perK_one {K : Type*} [Ring K] (A : Fin 1 → Fin 1 → K) : perK A = A 0 0 := by
  simp [perK, List.ofFn_succ]

lemma cofactor_two_eval (F : Scalar) (x : Fin 2 → F.K) :
    perCofactor (n := 2) (fun _ : Fin 1 => x) = ![x 1, x 0] := by
  ext j
  fin_cases j <;> simp [perCofactor, minor, perK_one, skipCol]

lemma cofactor_two_characteristic (F : Scalar) (z : Fin 2 → F.K) :
    charFunK (ginibre F 1 2) (perCofactor (n := 2)) z =
      (Real.exp (-(∑ i, ‖z i‖^2)/(2*(F.beta : ℝ))) : ℂ) := by
  haveI : IsProbabilityMeasure (gaussVec F 2) := by unfold gaussVec; infer_instance
  unfold charFunK
  change (∫ B : Fin 1 → Fin 2 → F.K,
    Complex.exp (Complex.I * ((realInner z (perCofactor (n := 2) B) : ℝ) : ℂ))
      ∂Measure.pi (fun _ : Fin 1 => gaussVec F 2)) = _
  rw [← (measurePreserving_piUnique (fun _ : Fin 1 => gaussVec F 2)).symm.integral_comp']
  change (∫ x : Fin 2 → F.K, Complex.exp (Complex.I *
    ((realInner z (perCofactor (n := 2) (fun _ : Fin 1 => x)) : ℝ) : ℂ)) ∂gaussVec F 2) = _
  simp_rw [cofactor_two_eval]
  have heq (x : Fin 2 → F.K) : realInner z ![x 1, x 0] = realInner ![z 1, z 0] x := by
    simp [realInner, Fin.sum_univ_two, add_comm]
  simp_rw [heq]
  rw [vector_scalar_gaussian_characteristic]
  simp [Fin.sum_univ_two, add_comm]

end GinibrePermanent977.Anticoncentration
-- Solutions/FourierCompression.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ComplexOrder Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

lemma scalar_norm_one (F : Scalar) : ‖(1 : F.K)‖ = 1 := by
  cases F
  · exact (norm_one : ‖(1 : ℝ)‖ = 1)
  · exact (norm_one : ‖(1 : ℂ)‖ = 1)
  · exact (norm_one : ‖(1 : ℍ[ℝ])‖ = 1)

lemma sum_norm_single_sq (F : Scalar) {n : ℕ} (j : Fin n) (x : F.K) :
    (∑ i, ‖(Pi.single j x : Fin n → F.K) i‖^2) = ‖x‖^2 := by
  classical
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    rw [Pi.single_eq_of_ne hij]
    simp
  · simp

lemma sum_norm_axis_sq (F : Scalar) {n : ℕ} (j : Fin n) (z : Fin n → F.K) :
    (∑ i, ‖(Pi.single j (norm2 z • (1 : F.K)) : Fin n → F.K) i‖^2) =
      ∑ i, ‖z i‖^2 := by
  rw [sum_norm_single_sq, norm_smul, scalar_norm_one, mul_one,
    Real.norm_eq_abs, sq_abs, norm2, Real.sq_sqrt (by positivity)]

lemma cofactor_single_eq_of_norm (F : Scalar) {n : ℕ} (j k : Fin (n+2)) (x y : F.K)
    (h : ‖x‖ = ‖y‖) :
    charFunK (ginibre F (n+1) (n+2)) (perCofactor (n := n+2)) (Pi.single j x) =
    charFunK (ginibre F (n+1) (n+2)) (perCofactor (n := n+2)) (Pi.single k y) := by
  rw [cofactor_characteristic_single_recurrence, cofactor_characteristic_single_recurrence, h]

lemma cofactor_single_radial (F : Scalar) {n : ℕ} (j k : Fin (n+2)) (x : F.K) :
    charFunK (ginibre F (n+1) (n+2)) (perCofactor (n := n+2)) (Pi.single j x) =
    charFunK (ginibre F (n+1) (n+2)) (perCofactor (n := n+2))
      (Pi.single k (Real.sqrt (‖x‖^2) • (1 : F.K))) := by
  apply cofactor_single_eq_of_norm
  rw [norm_smul, scalar_norm_one, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_sq_eq_abs, abs_norm]

lemma cofactor_compression_re (F : Scalar) {n : ℕ} (z : Fin (n+3) → F.K) :
    (charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3)) z).re ≤
    (charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3))
      (Pi.single 0 (norm2 z • (1 : F.K)))).re := by
  classical
  let ψ := fun w : Fin (n+3) → F.K =>
    (charFunK (ginibre F (n+2) (n+3)) (perCofactor (n := n+3)) w).re
  let f := fun s : ℝ => ψ (Pi.single 0 (Real.sqrt s • (1 : F.K)))
  have hs (j : Fin (n+3)) (x : F.K) : ψ (Pi.single j x) = f (‖x‖^2) :=
    congrArg Complex.re (cofactor_single_radial F (n := n+1) j 0 x)
  have hsmall (w : Fin (n+3) → F.K)
      (hw : (Finset.univ.filter (fun i => w i ≠ 0)).card ≤ 1) :
      ψ w ≤ f (∑ i, ‖w i‖^2) := by
    rcases support_card_le_one w hw with hz | ⟨j,hz⟩
    · rw [hz]
      have h := (hs 0 0).le
      simpa only [Pi.single_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply,
        Finset.sum_const_zero] using h
    · have hsum : (∑ i, ‖w i‖^2) = ‖w j‖^2 := by
        calc
          _ = ∑ i, ‖(Pi.single j (w j) : Fin (n+3) → F.K) i‖^2 := congrArg (fun v : Fin (n+3) → F.K => ∑ i, ‖v i‖^2) hz
          _ = _ := sum_norm_single_sq F j (w j)
      calc
        ψ w = ψ (Pi.single j (w j)) := congrArg ψ hz
        _ = f (‖w j‖^2) := hs j (w j)
        _ ≤ _ := (congrArg f hsum.symm).le
  have hp (τ : Equiv.Perm (Fin (n+3))) (w : Fin (n+3) → F.K) :
      ψ (fun i => w (τ i)) = ψ w :=
    congrArg Complex.re (cofactor_characteristic_columns_perm F τ w)
  exact coordinate_maximization ψ f hp hsmall (fun a b w ha hb =>
    cofactor_first_pair_compression F w a b ha hb) z

end GinibrePermanent977.Anticoncentration

open GinibrePermanent977.Anticoncentration

theorem solution (F : Scalar) {n : ℕ} (hn : 2 ≤ n) (z : Fin n → F.K) :
    0 ≤ charFunK (ginibre F (n-1) n) perCofactor z ∧
    charFunK (ginibre F (n-1) n) perCofactor z ≤
      charFunK (ginibre F (n-1) n) perCofactor
        (Pi.single (⟨0, by omega⟩ : Fin n) (norm2 z • (1 : F.K))) := by
  have hz := perCofactor_characteristic_nonnegative F hn z
  refine ⟨hz, ?_⟩
  have ha := perCofactor_characteristic_nonnegative F hn
    (Pi.single (⟨0, by omega⟩ : Fin n) (norm2 z • (1 : F.K)))
  apply Complex.le_def.mpr
  constructor
  · obtain ⟨m,rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
    cases m with
    | zero =>
      rw [cofactor_two_characteristic, cofactor_two_characteristic, sum_norm_axis_sq]
    | succ m => exact cofactor_compression_re F z
  · exact (Complex.le_def.mp hz).2.symm.trans (Complex.le_def.mp ha).2
