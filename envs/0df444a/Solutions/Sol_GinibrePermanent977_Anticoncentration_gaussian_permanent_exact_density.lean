-- Prove2me | solution 1 for GinibrePermanent977.Anticoncentration.gaussian_permanent_exact_density
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:12:49.860522+00:00
-- url     : https://prove2.me/submissions/53248b00-584a-4a82-86a1-f8c66e73292c

import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Theorems.Thm_GinibrePermanent977_Anticoncentration_theorem_3_6_scalar_cofactor_laplace

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

lemma scalar_real_dimension (F : Scalar) : Module.finrank ℝ F.K = F.beta := by
  cases F
  · exact (show Module.finrank ℝ ℝ = 1 by simp)
  · exact Complex.finrank_real_complex
  · exact Quaternion.finrank_eq_four

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
-- Solutions/GaussianRowLaw.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma gaussian_row_law (F : Scalar) {m : ℕ} (C : Fin m → F.K) :
    (gaussVec F m).map (fun g => ∑ j, g j*C j) =
      (gaussian F).map (fun x => norm2 C • x) := by
  have hmul : Measurable (fun g : Fin m → F.K => ∑ j, g j*C j) := by fun_prop
  haveI : IsProbabilityMeasure (gaussVec F m) := by unfold gaussVec; infer_instance
  haveI : IsProbabilityMeasure ((gaussVec F m).map (fun g => ∑ j, g j*C j)) :=
    Measure.isProbabilityMeasure_map hmul.aemeasurable
  haveI : IsProbabilityMeasure ((gaussian F).map (fun x => norm2 C • x)) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  apply Measure.ext_of_charFun
  funext z
  rw [charFun_apply, charFun_apply, integral_map hmul.aemeasurable (by fun_prop),
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  have heq (x : F.K) : Complex.exp (((inner ℝ (norm2 C • x) z : ℝ) : ℂ)*Complex.I) =
      Complex.exp (Complex.I*((inner ℝ (norm2 C • z) x : ℝ) : ℂ)) := by
    simp only [real_inner_smul_left]
    rw [real_inner_comm x z]
    ring_nf
  have heqL (g : Fin m → F.K) :
      Complex.exp (((inner ℝ (∑ j, g j*C j) z : ℝ) : ℂ)*Complex.I) =
      Complex.exp (Complex.I*((inner ℝ z (∑ j, g j*C j) : ℝ) : ℂ)) := by
    rw [real_inner_comm, mul_comm]
  simp_rw [heq, heqL]
  rw [gaussian_row_characteristic, scalar_gaussian_characteristic]
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hnorm : norm2 C^2 = ∑ i, ‖C i‖^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  rw [hnorm]
  congr 2
  ring

end GinibrePermanent977.Anticoncentration
-- Solutions/PiDensity.lean
open MeasureTheory Filter Set
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma lintegral_fin_product {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → A → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin n → A, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ a, f i a ∂μ i := by
  induction n with
  | zero => simp [Measure.pi_univ]
  | succ n ih =>
    have hsplit := (measurePreserving_piFinSuccAbove μ 0).symm
    have hm : Measurable (fun x : Fin (n+1) → A => ∏ i, f i (x i)) := by fun_prop
    rw [← hsplit.lintegral_comp hm]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
      Fin.zero_succAbove, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change (∫⁻ p : A × (Fin n → A), f 0 p.1*(∏ i : Fin n, f i.succ (p.2 i))
      ∂(μ 0).prod (Measure.pi (fun i : Fin n => μ i.succ))) = _
    rw [lintegral_prod_mul (hf 0).aemeasurable
      (Measurable.aemeasurable (by fun_prop : Measurable (fun x : Fin n → A => ∏ i, f i.succ (x i))))]
    rw [ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf i.succ)]

lemma pi_withDensity {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → A → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [lintegral_fin_product (fun i => (μ i).restrict (s i)) f hf]
  apply Finset.prod_congr rfl
  intro i _
  exact (withDensity_apply (f i) (hs i)).symm

end GinibrePermanent977.Anticoncentration
-- Solutions/DensityTransport.lean
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma map_withDensity_of_measurePreserving {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (e : A ≃ᵐ B) {μ : Measure A} {ν : Measure B} (he : MeasurePreserving e μ ν)
    (f : B → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (fun x => f (e x))).map e = ν.withDensity f := by
  ext s hs
  rw [MeasurableEquiv.map_apply, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  have h := he.lintegral_comp (hf.indicator hs)
  rw [lintegral_indicator hs] at h
  have heq : (fun x : A => s.indicator f (e x)) =
      (e ⁻¹' s).indicator (fun x => f (e x)) := by
    funext x
    by_cases hx : e x ∈ s <;> simp [Set.indicator, hx]
  rw [heq, lintegral_indicator (e.measurable hs)] at h
  exact h

end GinibrePermanent977.Anticoncentration
-- Solutions/HilbertGaussianDensity.lean
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

lemma hilbert_gaussian_density {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : ℝ≥0) (hv : v ≠ 0) :
    (Measure.pi (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 v)).map
      (fun x => ∑ i, x i • stdOrthonormalBasis ℝ E i) =
    volume.withDensity (fun x : E => ENNReal.ofReal
      ((Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹ ^ Module.finrank ℝ E *
        Real.exp (-‖x‖^2/(2*(v : ℝ))))) := by
  let d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  let e : (Fin d → ℝ) ≃ᵐ E :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).trans b.measurableEquiv.symm
  let q := fun x : E => ENNReal.ofReal
    ((Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹ ^ d * Real.exp (-‖x‖^2/(2*(v : ℝ))))
  have hq : Measurable q := by dsimp [q]; fun_prop
  have he : MeasurePreserving e volume volume :=
    b.measurePreserving_measurableEquiv.symm.comp (PiLp.volume_preserving_toLp (Fin d))
  have heq (x : Fin d → ℝ) : e x = ∑ i, x i • b i := by
    have h := b.sum_repr (e x)
    have hx : b.repr (e x) = WithLp.toLp 2 x := by
      exact b.repr.apply_symm_apply (WithLp.toLp 2 x)
    rw [hx] at h
    exact h.symm
  have hnorm (x : Fin d → ℝ) : ‖e x‖^2 = ∑ i, x i^2 := by
    have hx : b.repr (e x) = WithLp.toLp 2 x := b.repr.apply_symm_apply _
    rw [← b.repr.norm_map, hx, EuclideanSpace.real_norm_sq_eq]
  haveI (i : Fin d) : IsProbabilityMeasure (volume.withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  have hpi := pi_withDensity (fun _ : Fin d => (volume : Measure ℝ))
    (fun _ => gaussianPDF 0 v) (fun _ => measurable_gaussianPDF _ _)
  have hraw : Measure.pi (fun _ : Fin d => gaussianReal 0 v) =
      (volume : Measure (Fin d → ℝ)).withDensity (fun x => q (e x)) := by
    rw [show Measure.pi (fun _ : Fin d => gaussianReal 0 v) =
        Measure.pi (fun _ : Fin d => volume.withDensity (gaussianPDF 0 v)) from by
      simp only [gaussianReal_of_var_ne_zero 0 hv], hpi]
    congr 1
    funext x
    dsimp [q]
    rw [hnorm]
    simp only [gaussianPDF, gaussianPDFReal, sub_zero]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
  have hmap := map_withDensity_of_measurePreserving e he q hq
  change Measure.map (fun x : Fin d → ℝ => ∑ i, x i • b i) _ = _
  rw [show (fun x : Fin d → ℝ => ∑ i, x i • b i) = e from funext (fun x => (heq x).symm), hraw]
  exact hmap

end GinibrePermanent977.Anticoncentration
-- Solutions/ScalarGaussianDensity.lean
open MeasureTheory ProbabilityTheory Matrix Real Filter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

lemma scalar_gaussian_charFun (F : Scalar) (z : F.K) :
    charFun (gaussian F) z = (Real.exp (-‖z‖^2/(2*(F.beta : ℝ))) : ℂ) := by
  rw [charFun_apply]
  calc
    _ = ∫ x : F.K, Complex.exp (Complex.I*((inner ℝ z x : ℝ) : ℂ)) ∂gaussian F := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by dsimp only; rw [real_inner_comm, mul_comm])
    _ = _ := scalar_gaussian_characteristic F z

lemma scalar_scaled_gaussian_density (F : Scalar) (r : ℝ) (hr : 0 < r) :
    (gaussian F).map (fun x => r • x) =
      volume.withDensity (fun x : F.K => ENNReal.ofReal
        ((Real.sqrt (2*Real.pi*(r^2/(F.beta : ℝ))))⁻¹ ^ F.beta *
          Real.exp (-‖x‖^2/(2*(r^2/(F.beta : ℝ)))))) := by
  have hb := beta_pos F
  let v : ℝ≥0 := NNReal.mk (r^2/(F.beta : ℝ)) (by positivity)
  have hv : v ≠ 0 := by
    apply NNReal.coe_ne_zero.mp
    dsimp [v]
    positivity
  let d := Module.finrank ℝ F.K
  let b := stdOrthonormalBasis ℝ F.K
  let Φ := fun x : Fin d → ℝ => ∑ i, x i • b i
  have hΦ : Measurable Φ := by dsimp [Φ]; fun_prop
  haveI : IsProbabilityMeasure ((Measure.pi (fun _ : Fin d => gaussianReal 0 v)).map Φ) :=
    Measure.isProbabilityMeasure_map hΦ.aemeasurable
  haveI : IsProbabilityMeasure ((gaussian F).map (fun x => r • x)) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have hlaw : (Measure.pi (fun _ : Fin d => gaussianReal 0 v)).map Φ =
      (gaussian F).map (fun x => r • x) := by
    apply Measure.ext_of_charFun
    funext z
    rw [charFun_map_smul, scalar_gaussian_charFun, charFun_apply,
      integral_map hΦ.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop))]
    let w := fun i : Fin d => inner ℝ (b i) z
    have hpoint (x : Fin d → ℝ) :
        Complex.exp (((inner ℝ (Φ x) z : ℝ) : ℂ)*Complex.I) =
        Complex.exp (Complex.I*((x ⬝ᵥ w : ℝ) : ℂ)) := by
      simp only [Φ, sum_inner, real_inner_smul_left, dotProduct, w]
      rw [mul_comm]
    simp_rw [hpoint]
    rw [vector_gaussian_characteristic]
    have hn : (∑ i, w i^2) = ‖z‖^2 := b.sum_sq_inner_right z
    rw [hn, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    congr 2
    dsimp [v]
    ring
  have hpdf := hilbert_gaussian_density (E := F.K) v hv
  rw [hlaw, scalar_real_dimension F] at hpdf
  have hvol : (@volume F.K (Scalar.instMeasureSpace F)) =
      (@volume F.K (measureSpaceOfInnerProductSpace)) := by cases F <;> rfl
  rw [← hvol] at hpdf
  exact hpdf

end GinibrePermanent977.Anticoncentration
-- Solutions/GammaLaplace.lean
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma integral_gammaMeasure_real (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ x, f x ∂gammaMeasure a r) = ∫ x, gammaPDFReal a r x * f x := by
  unfold gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simp only [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  · exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a r)
  · exact Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)

lemma integral_gammaPDFReal (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∫ x, gammaPDFReal a r x = 1 := by
  haveI : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  have h := integral_gammaMeasure_real a r ha hr (fun _ => 1)
  simpa using h.symm

lemma gamma_laplace_transform (a r s : ℝ) (ha : 0 < a) (hr : 0 < r) (hs : 0 ≤ s) :
    (∫ x, Real.exp (-s*x) ∂gammaMeasure a r) = (r/(r+s))^a := by
  have hrs : 0 < r+s := by linarith
  have hpoint (x : ℝ) : gammaPDFReal a r x * Real.exp (-s*x) =
      (r/(r+s))^a * gammaPDFReal a (r+s) x := by
    unfold gammaPDFReal
    split_ifs with hx
    · rw [mul_assoc, ← Real.exp_add]
      have hex : -(r*x)+ -s*x = -((r+s)*x) := by ring
      rw [hex, Real.div_rpow hr.le hrs.le]
      field_simp
    · simp
  rw [integral_gammaMeasure_real a r ha hr]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_gammaPDFReal a (r+s) ha hrs, mul_one]

lemma gammaMeasure_ae_nonneg (a r : ℝ) : ∀ᵐ x ∂gammaMeasure a r, 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  change gammaMeasure a r (Set.Iio 0) = 0
  unfold gammaMeasure
  rw [withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma gammaPi_ae_nonneg (F : Scalar) (m : ℕ) : ∀ᵐ γ ∂gammaVec F m, 0 ≤ gammaPi γ := by
  have h (i : Fin m) : ∀ᵐ γ ∂gammaVec F m, 0 ≤ γ i := by
    exact (measurePreserving_eval (fun k : Fin m => gammaLaw F (k.val+1)) i).quasiMeasurePreserving.ae
      (gammaMeasure_ae_nonneg _ _)
  filter_upwards [ae_all_iff.mpr h] with γ hγ
  exact Finset.prod_nonneg (fun i _ => hγ i)

lemma gammaPi_succ {m : ℕ} (γ : Fin (m+2) → ℝ) :
    gammaPi γ = gammaPi (fun i : Fin (m+1) => γ i.castSucc) * γ (Fin.last (m+1)) := by
  unfold gammaPi
  simp only [Finset.prod_filter]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last]
  rw [if_pos (by omega)]

end GinibrePermanent977.Anticoncentration
-- Solutions/GammaInverseMoment.lean
open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma gammaMeasure_ae_pos (a r : ℝ) : ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  have hne : ∀ᵐ x ∂gammaMeasure a r, x ≠ 0 := by
    rw [ae_iff]
    simp only [not_not]
    exact withDensity_absolutelyContinuous volume (gammaPDF a r) (by simp)
  filter_upwards [gammaMeasure_ae_nonneg a r, hne] with x hx hne
  exact lt_of_le_of_ne hx (Ne.symm hne)

lemma gamma_inverse_density (a r b x : ℝ) (ha : 0 < a) (hr : 0 < r)
    (hab : 0 < a-b) (hx : x ≠ 0) :
    gammaPDFReal a r x * x^(-b) =
      (r^b*Real.Gamma (a-b)/Real.Gamma a)*gammaPDFReal (a-b) r x := by
  by_cases hp : 0 ≤ x
  · have hx' : 0 < x := lt_of_le_of_ne hp (Ne.symm hx)
    unfold gammaPDFReal
    rw [if_pos hp, if_pos hp]
    have hpowx : x^(a-b-1) = x^(a-1)*x^(-b) := by
      rw [← Real.rpow_add hx']
      congr 1
      ring
    have hpowr : r^a = r^b*r^(a-b) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    rw [hpowx, hpowr]
    field_simp [(Real.Gamma_pos_of_pos ha).ne', (Real.Gamma_pos_of_pos hab).ne']
  · simp [gammaPDFReal, hp]

lemma integrable_gammaPDFReal (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    Integrable (gammaPDFReal a r) := by
  have hm : AEMeasurable (gammaPDF a r) volume :=
    (ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a r)).aemeasurable
  have hfin : ∀ᵐ x : ℝ, gammaPDF a r x ≠ ⊤ := Eventually.of_forall (fun x => ENNReal.ofReal_ne_top)
  have hi := (integrable_toReal_iff hm hfin).2
    (by rw [lintegral_gammaPDF_eq_one ha hr]; simp)
  simpa only [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)] using hi

lemma gamma_inverse_moment (a r b : ℝ) (ha : 0 < a) (hr : 0 < r) (hab : 0 < a-b) :
    (∫ x : ℝ, x^(-b) ∂gammaMeasure a r) = r^b*Real.Gamma (a-b)/Real.Gamma a := by
  rw [integral_gammaMeasure_real a r ha hr]
  have heq : (fun x : ℝ => gammaPDFReal a r x*x^(-b)) =ᵐ[volume]
      (fun x => (r^b*Real.Gamma (a-b)/Real.Gamma a)*gammaPDFReal (a-b) r x) := by
    have hn : ∀ᵐ x : ℝ, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hn] with x hx
    exact gamma_inverse_density a r b x ha hr hab hx
  rw [integral_congr_ae heq, integral_const_mul, integral_gammaPDFReal (a-b) r hab hr, mul_one]

lemma gamma_inverse_lintegral (a r b : ℝ) (ha : 0 < a) (hr : 0 < r) (hab : 0 < a-b) :
    (∫⁻ x : ℝ, ENNReal.ofReal (x^(-b)) ∂gammaMeasure a r) =
      ENNReal.ofReal (r^b*Real.Gamma (a-b)/Real.Gamma a) := by
  have hm : Measurable (gammaPDF a r) := ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a r)
  have hM : Measurable (fun x : ℝ => ENNReal.ofReal (x^(-b))) := by fun_prop
  have hC : 0 ≤ r^b*Real.Gamma (a-b)/Real.Gamma a := by positivity
  unfold gammaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul volume hm hM]
  calc
    _ = ∫⁻ x : ℝ, ENNReal.ofReal (gammaPDFReal a r x*x^(-b)) := by
      apply lintegral_congr_ae
      exact Eventually.of_forall (fun x => (ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hr x)).symm)
    _ = ∫⁻ x : ℝ, ENNReal.ofReal (r^b*Real.Gamma (a-b)/Real.Gamma a)*gammaPDF (a-b) r x := by
      apply lintegral_congr_ae
      have hn : ∀ᵐ x : ℝ, x ≠ 0 := by rw [ae_iff]; simp
      filter_upwards [hn] with x hx
      rw [gamma_inverse_density a r b x ha hr hab hx, ENNReal.ofReal_mul hC]
      rfl
    _ = _ := by
      rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
        lintegral_gammaPDF_eq_one hab hr, mul_one]

end GinibrePermanent977.Anticoncentration
-- Solutions/GammaProduct.lean
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma measurable_gammaPi (m : ℕ) : Measurable (gammaPi : (Fin m → ℝ) → ℝ) := by
  unfold gammaPi
  fun_prop

instance gammaVec_probability (F : Scalar) (m : ℕ) : IsProbabilityMeasure (gammaVec F m) := by
  unfold gammaVec
  infer_instance
instance gaussVec_probability (F : Scalar) (m : ℕ) : IsProbabilityMeasure (gaussVec F m) := by
  unfold gaussVec
  infer_instance
instance ginibre_probability (F : Scalar) (m n : ℕ) : IsProbabilityMeasure (ginibre F m n) := by
  unfold ginibre
  infer_instance

lemma gammaPi_nonneg_prod {A : Type*} [MeasurableSpace A] (F : Scalar) (m : ℕ)
    (ν : Measure A) [IsProbabilityMeasure ν] :
    ∀ᵐ p ∂(gammaVec F m).prod ν, 0 ≤ gammaPi p.1 :=
  (measurePreserving_fst (μ := gammaVec F m) (ν := ν)).quasiMeasurePreserving.ae (gammaPi_ae_nonneg F m)

lemma gammaVec_split_last (F : Scalar) (m : ℕ) :
    MeasurePreserving
      (fun γ : Fin (m+2) → ℝ => (γ (Fin.last (m+1)), fun i : Fin (m+1) => γ i.castSucc))
      (gammaVec F (m+2)) ((gammaLaw F (m+2)).prod (gammaVec F (m+1))) := by
  have h := measurePreserving_piFinSuccAbove
    (fun k : Fin (m+2) => gammaLaw F (k.val+1)) (Fin.last (m+1))
  convert h using 1
  · funext γ
    apply Prod.ext
    · rfl
    · funext i
      change γ i.castSucc = γ ((Fin.last (m+1)).succAbove i)
      rw [Fin.succAbove_last]
  · rfl
  · congr 1
    simp [gammaVec, Fin.succAbove_last]

lemma gammaPi_integral_split_last (F : Scalar) (m : ℕ) (s : ℝ) :
    (∫ γ, Real.exp (-s*gammaPi γ) ∂gammaVec F (m+2)) =
    ∫ p : ℝ × (Fin (m+1) → ℝ), Real.exp (-s*gammaPi p.2*p.1)
      ∂(gammaLaw F (m+2)).prod (gammaVec F (m+1)) := by
  have h := gammaVec_split_last F m
  let g := fun p : ℝ × (Fin (m+1) → ℝ) => Real.exp (-s*gammaPi p.2*p.1)
  have hg : Measurable g := by
    have hp := measurable_gammaPi (m+1)
    dsimp [g]; fun_prop
  have he := integral_map h.aemeasurable hg.aestronglyMeasurable
  rw [h.map_eq] at he
  rw [he]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro γ
  change Real.exp (-s*gammaPi γ) = Real.exp (-s*gammaPi (fun i => γ i.castSucc)*γ (Fin.last (m+1)))
  rw [gammaPi_succ]
  congr 1
  ring

end GinibrePermanent977.Anticoncentration
-- Solutions/GammaProductMoment.lean
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma gammaVec_ae_pos (F : Scalar) (n : ℕ) :
    ∀ᵐ γ ∂gammaVec F n, ∀ i, 0 < γ i := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun k : Fin n => gammaLaw F (k.val+1)) i).quasiMeasurePreserving.ae
    (gammaMeasure_ae_pos _ _)

lemma gammaPi_ae_pos (F : Scalar) (n : ℕ) : ∀ᵐ γ ∂gammaVec F n, 0 < gammaPi γ := by
  filter_upwards [gammaVec_ae_pos F n] with γ hγ
  exact Finset.prod_pos (fun i _ => hγ i)

lemma gammaPi_inverse_lintegral_product (F : Scalar) (n : ℕ) (b : ℝ) :
    (∫⁻ γ, ENNReal.ofReal ((gammaPi γ)^(-b)) ∂gammaVec F n) =
    ∏ k ∈ Finset.univ.filter (fun k : Fin n => 1 ≤ k.val),
      ∫⁻ x : ℝ, ENNReal.ofReal (x^(-b)) ∂gammaLaw F (k.val+1) := by
  classical
  let S := Finset.univ.filter (fun k : Fin n => 1 ≤ k.val)
  let f := fun _ : Fin n => fun x : ℝ => ENNReal.ofReal (x^(-b))
  have hm (i : Fin n) : Measurable (f i) := by dsimp [f]; fun_prop
  have hind : iIndepFun (fun i (γ : Fin n → ℝ) => f i (γ i)) (gammaVec F n) :=
    iIndepFun_pi (fun i => (hm i).aemeasurable)
  calc
    _ = ∫⁻ γ, ∏ i ∈ S, f i (γ i) ∂gammaVec F n := by
      apply lintegral_congr_ae
      filter_upwards [gammaVec_ae_pos F n] with γ hγ
      unfold gammaPi
      rw [← Real.finsetProd_rpow _ _ (fun i _ => (hγ i).le),
        ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hγ i).le _)]
    _ = ∏ i ∈ S, ∫⁻ γ, f i (γ i) ∂gammaVec F n :=
      lintegral_prod_eq_prod_lintegral_of_indepFun S _ hind (fun i => by fun_prop)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (measurePreserving_eval (fun k : Fin n => gammaLaw F (k.val+1)) i).lintegral_comp (hm i)

lemma gammaPi_inverse_lintegral_factors (F : Scalar) (n : ℕ) :
    (∫⁻ γ, ENNReal.ofReal ((gammaPi γ)^(-((F.beta : ℝ)/2))) ∂gammaVec F n) =
    ∏ k ∈ Finset.univ.filter (fun k : Fin n => 1 ≤ k.val),
      ENNReal.ofReal (((F.beta : ℝ)/2)^((F.beta : ℝ)/2) *
        Real.Gamma ((F.beta : ℝ)*(k.val : ℝ)/2) /
          Real.Gamma ((F.beta : ℝ)*((k.val : ℝ)+1)/2)) := by
  rw [gammaPi_inverse_lintegral_product]
  apply Finset.prod_congr rfl
  intro k hk
  have hk1 : 1 ≤ k.val := (Finset.mem_filter.mp hk).2
  have hkR : (1 : ℝ) ≤ k.val := by exact_mod_cast hk1
  have hb := beta_pos F
  have hshape : 0 < (F.beta : ℝ)*((k.val : ℝ)+1)/2 := by positivity
  have hdiff : 0 < (F.beta : ℝ)*((k.val : ℝ)+1)/2-(F.beta : ℝ)/2 := by nlinarith
  unfold gammaLaw
  rw [gamma_inverse_lintegral _ _ _ (by exact_mod_cast hshape) (by positivity) (by exact_mod_cast hdiff)]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (F.beta : ℝ)*((k.val : ℝ)+1)/2-(F.beta : ℝ)/2 =
    (F.beta : ℝ)*(k.val : ℝ)/2 by ring]

end GinibrePermanent977.Anticoncentration
-- Solutions/GammaRatioProduct.lean
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma gamma_ratio_product (r b : ℝ) (hr : 0 < r) (hb : 0 < b) (n : ℕ) (hn : 1 ≤ n) :
    (∏ k : Fin n, if 1 ≤ k.val then r^b * Real.Gamma (b*(k.val : ℝ)) /
      Real.Gamma (b*((k.val : ℝ)+1)) else 1) =
      r^(b*((n : ℝ)-1))*Real.Gamma b/Real.Gamma (b*(n : ℝ)) := by
  refine Nat.le_induction ?_ ?_ n hn
  · simp [(Real.Gamma_pos_of_pos hb).ne']
  · intro m hm ih
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, if_pos hm]
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hgm : Real.Gamma (b*(m : ℝ)) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hgmp : Real.Gamma (b*((m : ℝ)+1)) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hpow : b*((((m+1 : ℕ) : ℝ))-1) = b*((m : ℝ)-1)+b := by push_cast; ring
    rw [hpow, Real.rpow_add hr]
    push_cast
    field_simp [hgm, hgmp]

lemma gammaPi_inverse_lintegral (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ γ, ENNReal.ofReal ((gammaPi γ)^(-((F.beta : ℝ)/2))) ∂gammaVec F n) =
      ENNReal.ofReal (((F.beta : ℝ)/2)^(((F.beta : ℝ)/2)*((n : ℝ)-1)) *
        Real.Gamma ((F.beta : ℝ)/2)/Real.Gamma (((F.beta : ℝ)/2)*(n : ℝ))) := by
  rw [gammaPi_inverse_lintegral_factors]
  let b := (F.beta : ℝ)/2
  have hb : 0 < b := by dsimp [b]; exact div_pos (beta_pos F) (by norm_num)
  have hfactor (k : Fin n) (hk : 1 ≤ k.val) :
      ((F.beta : ℝ)/2)^((F.beta : ℝ)/2)*Real.Gamma ((F.beta : ℝ)*(k.val : ℝ)/2) /
        Real.Gamma ((F.beta : ℝ)*((k.val : ℝ)+1)/2) =
      b^b*Real.Gamma (b*(k.val : ℝ))/Real.Gamma (b*((k.val : ℝ)+1)) := by
    dsimp [b]
    congr 2 <;> congr 1 <;> ring
  simp_rw [Finset.prod_filter]
  have hp : (∏ k : Fin n, if 1 ≤ k.val then ENNReal.ofReal
      (((F.beta : ℝ)/2)^((F.beta : ℝ)/2)*Real.Gamma ((F.beta : ℝ)*(k.val : ℝ)/2) /
        Real.Gamma ((F.beta : ℝ)*((k.val : ℝ)+1)/2)) else 1) =
      ENNReal.ofReal (∏ k : Fin n, if 1 ≤ k.val then
        b^b*Real.Gamma (b*(k.val : ℝ))/Real.Gamma (b*((k.val : ℝ)+1)) else 1) := by
    rw [ENNReal.ofReal_prod_of_nonneg]
    · apply Finset.prod_congr rfl
      intro k hk
      split_ifs with h
      · rw [hfactor k h]
      · simp
    · intro k hk
      split_ifs with h
      · have hkr : (1 : ℝ) ≤ k.val := by exact_mod_cast h
        positivity
      · positivity
  rw [hp, gamma_ratio_product b b hb hb n hn]

end GinibrePermanent977.Anticoncentration
-- Solutions/LaplacePositive.lean
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace StochasticOrders.LaplaceTransform

lemma integrable_laplace {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hm : Measurable X) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => Real.exp (-(s*X ω))) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (Measurable.aestronglyMeasurable (by fun_prop))
  filter_upwards [hX] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs hω))

lemma laplace_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hm : Measurable X) (hX : ∀ᵐ ω ∂μ, 0 < X ω) :
    Tendsto (fun n : ℕ => ∫ ω, Real.exp (-(((n : ℝ)+1)*X ω)) ∂μ) atTop (nhds 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ω => Real.exp (-(((n : ℝ)+1)*X ω))) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => Measurable.aestronglyMeasurable (by fun_prop)) (integrable_const 1)
    (fun n => by
      filter_upwards [hX] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (mul_nonneg (by positivity) hω.le))
    (by
      filter_upwards [hX] with ω hω
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (show Tendsto (fun n : ℕ => ((n : ℝ)+1)*X ω) atTop atTop from by
          simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
            ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)).atTop_mul_const hω))
  simpa using h

lemma LaplaceOrder.ae_pos {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (h : LaplaceOrder μ ν X Y)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX : ∀ᵐ ω ∂μ, 0 < X ω) (hY : ∀ᵐ ω ∂ν, 0 ≤ Y ω) :
    ∀ᵐ ω ∂ν, 0 < Y ω := by
  let A := {ω | Y ω = 0}
  have hA : MeasurableSet A := hYm (measurableSet_singleton 0)
  have hbound (n : ℕ) : ν.real A ≤ ∫ ω, Real.exp (-(((n : ℝ)+1)*X ω)) ∂μ := by
    calc
      _ = ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂ν := (integral_indicator_one hA).symm
      _ ≤ ∫ ω, Real.exp (-(((n : ℝ)+1)*Y ω)) ∂ν := by
        apply integral_mono ((integrable_const (1 : ℝ)).indicator hA)
          (integrable_laplace ν Y hYm hY _ (by positivity))
        intro ω
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω]
          have hy : Y ω = 0 := hω
          simp [hy]
        · simp only [Set.indicator_of_notMem hω]
          exact (Real.exp_pos _).le
      _ ≤ _ := h _ (by positivity)
  have hz : ν.real A = 0 := le_antisymm
    (ge_of_tendsto (laplace_tendsto_zero μ X hXm hX) (Eventually.of_forall hbound)) (measureReal_nonneg)
  have hzero : ν A = 0 := (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top ν A)
  have hne : ∀ᵐ ω ∂ν, Y ω ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hzero
  filter_upwards [hY, hne] with ω hω hn
  exact lt_of_le_of_ne hω (Ne.symm hn)

end StochasticOrders.LaplaceTransform
-- Solutions/LaplaceInverseMoment.lean
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace StochasticOrders.LaplaceTransform

lemma mellin_laplace_kernel (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    (∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (s^(a-1)*Real.exp (-(s*x)))) =
      ENNReal.ofReal (x^(-a)*Real.Gamma a) := by
  have hi : IntegrableOn (fun s : ℝ => s^(a-1)*Real.exp (-(s*x))) (Ioi 0) := by
    have hi0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := a-1) (p := 1) (b := x)
      (by linarith) zero_lt_one hx
    apply hi0.congr_fun _ measurableSet_Ioi
    intro s hs
    simp only [Real.rpow_one]
    congr 1
    ring
  have hn : ∀ᵐ s : ℝ ∂volume.restrict (Ioi 0), 0 ≤ s^(a-1)*Real.exp (-(s*x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  have heq : (fun s : ℝ => s^(a-1)*Real.exp (-(s*x))) =
      (fun s : ℝ => s^(a-1)*Real.exp (-(x*s))) := by funext s; rw [mul_comm s x]
  rw [heq, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hx, one_div,
    Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]

lemma mellin_laplace_normalized (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    (∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal ((Real.Gamma a)⁻¹*(s^(a-1)*Real.exp (-(s*x))))) =
      ENNReal.ofReal (x^(-a)) := by
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Real.Gamma_pos_of_pos ha).le)]
  rw [lintegral_const_mul _ (by fun_prop), mellin_laplace_kernel a x ha hx,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.Gamma_pos_of_pos ha).le)]
  congr 1
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

lemma LaplaceOrder.lintegral_inverse_moment {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (h : LaplaceOrder μ ν X Y)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX : ∀ᵐ ω ∂μ, 0 < X ω) (hY : ∀ᵐ ω ∂ν, 0 < Y ω)
    (a : ℝ) (ha : 0 < a) :
    (∫⁻ ω, ENNReal.ofReal ((Y ω)^(-a)) ∂ν) ≤ ∫⁻ ω, ENNReal.ofReal ((X ω)^(-a)) ∂μ := by
  let K := fun s x : ℝ => ENNReal.ofReal ((Real.Gamma a)⁻¹*(s^(a-1)*Real.exp (-(s*x))))
  have hrepr {A : Type} [MeasurableSpace A] (η : Measure A) (Z : A → ℝ)
      (hp : ∀ᵐ ω ∂η, 0 < Z ω) :
      (∫⁻ ω, ENNReal.ofReal ((Z ω)^(-a)) ∂η) =
      ∫⁻ ω, (∫⁻ s : ℝ in Ioi 0, K s (Z ω)) ∂η := by
    apply lintegral_congr_ae
    filter_upwards [hp] with ω hω
    exact (mellin_laplace_normalized a (Z ω) ha hω).symm
  rw [hrepr ν Y hY, hrepr μ X hX]
  have hmeasX : Measurable (Function.uncurry (fun (ω : Ω) (s : ℝ) => K s (X ω))) := by
    dsimp [K]; fun_prop
  have hmeasY : Measurable (Function.uncurry (fun (ω : Ω') (s : ℝ) => K s (Y ω))) := by
    dsimp [K]; fun_prop
  rw [lintegral_lintegral_swap hmeasY.aemeasurable,
    lintegral_lintegral_swap hmeasX.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have heq {A : Type} [MeasurableSpace A] (η : Measure A) [IsProbabilityMeasure η]
      (Z : A → ℝ) (hm : Measurable Z) (hp : ∀ᵐ ω ∂η, 0 < Z ω) :
      (∫⁻ ω, K s (Z ω) ∂η) =
      ENNReal.ofReal ((Real.Gamma a)⁻¹*s^(a-1)) *
        ENNReal.ofReal (∫ ω, Real.exp (-(s*Z ω)) ∂η) := by
    dsimp [K]
    have hc : 0 ≤ (Real.Gamma a)⁻¹*s^(a-1) :=
      mul_nonneg (inv_nonneg.mpr (Real.Gamma_pos_of_pos ha).le) (Real.rpow_nonneg hs.le _)
    simp only [← mul_assoc]
    change (∫⁻ ω, ENNReal.ofReal (((Real.Gamma a)⁻¹*s^(a-1))*Real.exp (-(s*Z ω))) ∂η) = _
    simp_rw [ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul _ (by fun_prop),
      ← ofReal_integral_eq_lintegral_ofReal
        (integrable_laplace η Z hm (hp.mono (fun _ h => h.le)) s hs.le)
        (Eventually.of_forall (fun ω => (Real.exp_pos _).le))]
  rw [heq ν Y hYm hY, heq μ X hXm hX]
  gcongr
  exact h s hs

end StochasticOrders.LaplaceTransform
-- Solutions/CofactorInverse.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma cofactor_inverse_moment (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    (∀ᵐ B ∂ginibre F (n-1) n, 0 < norm2 (perCofactor (n := n) B)^2) ∧
    (∫⁻ B, ENNReal.ofReal ((norm2 (perCofactor (n := n) B)^2)^(-((F.beta : ℝ)/2)))
      ∂ginibre F (n-1) n) ≤
      ENNReal.ofReal (((F.beta : ℝ)/2)^(((F.beta : ℝ)/2)*((n : ℝ)-1))*
        Real.Gamma ((F.beta : ℝ)/2)/Real.Gamma (((F.beta : ℝ)/2)*(n : ℝ))) := by
  have h := theorem_3_6_scalar_cofactor_laplace F n hn
  have hC : Measurable (perCofactor (n := n) :
      (Fin (n-1) → Fin n → F.K) → Fin n → F.K) := continuous_perCofactor.measurable
  have hY : Measurable (fun B : Fin (n-1) → Fin n → F.K => norm2 (perCofactor B)^2) := by
    unfold norm2
    fun_prop
  have hpos := h.ae_pos (measurable_gammaPi n) hY (gammaPi_ae_pos F n)
    (Eventually.of_forall (fun B => sq_nonneg _))
  refine ⟨hpos, ?_⟩
  have hm := h.lintegral_inverse_moment (measurable_gammaPi n) hY (gammaPi_ae_pos F n) hpos
    ((F.beta : ℝ)/2) (div_pos (beta_pos F) (by norm_num))
  rw [gammaPi_inverse_lintegral F n hn] at hm
  exact hm

end GinibrePermanent977.Anticoncentration
-- Solutions/GaussianDensityAlgebra.lean
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma inv_sqrt_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (Real.sqrt x)⁻¹ ^ n = x^(-((n : ℝ)/2)) := by
  rw [← Real.rpow_natCast, Real.inv_rpow (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx, ← Real.rpow_neg hx]
  congr 1
  ring

lemma gaussian_density_prefactor (F : Scalar) (r : ℝ) :
    (Real.sqrt (2*Real.pi*(r^2/(F.beta : ℝ))))⁻¹ ^ F.beta =
      ((F.beta : ℝ)/(2*Real.pi))^((F.beta : ℝ)/2) * (r^2)^(-((F.beta : ℝ)/2)) := by
  have hb := beta_pos F
  have hA : 0 ≤ 2*Real.pi*(r^2/(F.beta : ℝ)) := by positivity
  rw [inv_sqrt_pow _ hA]
  have heq : 2*Real.pi*(r^2/(F.beta : ℝ)) = (2*Real.pi/(F.beta : ℝ))*r^2 := by ring
  rw [heq, Real.mul_rpow (by positivity) (sq_nonneg r)]
  congr 1
  have hinv : 2*Real.pi/(F.beta : ℝ) = ((F.beta : ℝ)/(2*Real.pi))⁻¹ := by field_simp
  rw [hinv, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]

lemma normalized_gaussian_prefactor (F : Scalar) (n : ℕ) (c : ℝ) :
    (Real.sqrt (2*Real.pi*((c/Real.sqrt (n.factorial : ℝ))^2/(F.beta : ℝ))))⁻¹ ^ F.beta =
      (((F.beta : ℝ)/(2*Real.pi))^((F.beta : ℝ)/2)*(n.factorial : ℝ)^((F.beta : ℝ)/2)) *
        (c^2)^(-((F.beta : ℝ)/2)) := by
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  rw [gaussian_density_prefactor, div_pow, Real.sq_sqrt hf.le,
    Real.div_rpow (sq_nonneg c) hf.le, Real.rpow_neg hf.le, div_inv_eq_mul]
  ring

lemma density_moment_kappa (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    (((F.beta : ℝ)/(2*Real.pi))^((F.beta : ℝ)/2)*(n.factorial : ℝ)^((F.beta : ℝ)/2)) *
      (((F.beta : ℝ)/2)^(((F.beta : ℝ)/2)*((n : ℝ)-1))*
        Real.Gamma ((F.beta : ℝ)/2)/Real.Gamma (((F.beta : ℝ)/2)*(n : ℝ))) = kappa F n := by
  let b := (F.beta : ℝ)/2
  have hb : 0 < b := by dsimp [b]; exact div_pos (beta_pos F) (by norm_num)
  have hπ : Real.pi^b ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hΓ : Real.Gamma (b*(n : ℝ)) ≠ 0 := (Real.Gamma_pos_of_pos (mul_pos hb hnR)).ne'
  have heq : (F.beta : ℝ)/(2*Real.pi) = b/Real.pi := by dsimp [b]; ring
  rw [heq, Real.div_rpow hb.le Real.pi_pos.le]
  unfold kappa
  have heqn : (F.beta : ℝ)*(n : ℝ)/2 = b*(n : ℝ) := by dsimp [b]; ring
  rw [heqn, Real.rpow_neg Real.pi_pos.le]
  change (b^b/Real.pi^b*(n.factorial : ℝ)^b)*
    (b^(b*((n : ℝ)-1))*Real.Gamma b/Real.Gamma (b*(n : ℝ))) =
      (n.factorial : ℝ)^b*(Real.pi^b)⁻¹*b^(b*(n : ℝ))*Real.Gamma b/Real.Gamma (b*(n : ℝ))
  have hp : b^(b*(n : ℝ)) = b^b*b^(b*((n : ℝ)-1)) := by
    rw [← Real.rpow_add hb]
    congr 1
    ring
  rw [hp]
  ring

end GinibrePermanent977.Anticoncentration
-- Solutions/MixtureDensity.lean
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

def realGaussianKernel (F : Scalar) (r : ℝ) (z : F.K) : ℝ :=
  (Real.sqrt (2*Real.pi*(r^2/(F.beta : ℝ))))⁻¹ ^ F.beta *
    Real.exp (-‖z‖^2/(2*(r^2/(F.beta : ℝ))))

lemma realGaussianKernel_nonneg (F : Scalar) (r : ℝ) (z : F.K) :
    0 ≤ realGaussianKernel F r z := by unfold realGaussianKernel; positivity

lemma realGaussianKernel_zero (F : Scalar) (r : ℝ) :
    realGaussianKernel F r 0 = (Real.sqrt (2*Real.pi*(r^2/(F.beta : ℝ))))⁻¹ ^ F.beta := by
  simp [realGaussianKernel]

lemma realGaussianKernel_le_zero (F : Scalar) (r : ℝ) (z : F.K) :
    realGaussianKernel F r z ≤ realGaussianKernel F r 0 := by
  rw [realGaussianKernel_zero]
  unfold realGaussianKernel
  apply mul_le_of_le_one_right (by positivity)
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

lemma measurable_realGaussianKernel (F : Scalar) :
    Measurable (fun p : ℝ × F.K => realGaussianKernel F p.1 p.2) := by
  unfold realGaussianKernel
  fun_prop

lemma continuous_realGaussianKernel_right (F : Scalar) (r : ℝ) :
    Continuous (realGaussianKernel F r) := by unfold realGaussianKernel; fun_prop

lemma realGaussianKernel_radial (F : Scalar) (r : ℝ) (z w : F.K) (h : ‖z‖ = ‖w‖) :
    realGaussianKernel F r z = realGaussianKernel F r w := by unfold realGaussianKernel; rw [h]

lemma scaled_gaussian_kernel (F : Scalar) (r : ℝ) (hr : 0 < r) :
    (gaussian F).map (fun x => r • x) =
      volume.withDensity (fun z => ENNReal.ofReal (realGaussianKernel F r z)) :=
  scalar_scaled_gaussian_density F r hr

lemma gaussian_mixture_properties {A : Type*} [MeasurableSpace A] (F : Scalar)
    (μ : Measure A) [IsFiniteMeasure μ] (r : A → ℝ) (hm : Measurable r)
    (hfin : (∫⁻ a, ENNReal.ofReal (realGaussianKernel F (r a) 0) ∂μ) < ⊤) :
    ∃ p : F.K → ℝ≥0∞, Continuous p ∧
      (∀ z, p z = ∫⁻ a, ENNReal.ofReal (realGaussianKernel F (r a) z) ∂μ) ∧
      (∀ z w, ‖z‖ = ‖w‖ → p z = p w) ∧ (∀ z, p z ≤ p 0) := by
  have hmeas (z : F.K) : Measurable (fun a => realGaussianKernel F (r a) z) := by
    unfold realGaussianKernel
    fun_prop
  have h0 : Integrable (fun a => realGaussianKernel F (r a) 0) μ := by
    have hm0 : Measurable (fun a => ENNReal.ofReal (realGaussianKernel F (r a) 0)) :=
      ENNReal.measurable_ofReal.comp (hmeas 0)
    have hi := (integrable_toReal_iff hm0.aemeasurable
      (Eventually.of_forall (fun a => ENNReal.ofReal_ne_top))).2 hfin.ne
    simpa only [ENNReal.toReal_ofReal (realGaussianKernel_nonneg F _ _)] using hi
  have hi (z : F.K) : Integrable (fun a => realGaussianKernel F (r a) z) μ := by
    apply h0.mono' (hmeas z).aestronglyMeasurable
    exact Eventually.of_forall (fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (realGaussianKernel_nonneg F _ _)]
      exact realGaussianKernel_le_zero F _ _)
  let p := fun z : F.K => ENNReal.ofReal (∫ a, realGaussianKernel F (r a) z ∂μ)
  have hc : Continuous (fun z : F.K => ∫ a, realGaussianKernel F (r a) z ∂μ) := by
    apply continuous_of_dominated (bound := fun a => realGaussianKernel F (r a) 0)
    · exact fun z => (hmeas z).aestronglyMeasurable
    · intro z
      exact Eventually.of_forall (fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (realGaussianKernel_nonneg F _ _)]
        exact realGaussianKernel_le_zero F _ _)
    · exact h0
    · exact Eventually.of_forall (fun a => continuous_realGaussianKernel_right F (r a))
  refine ⟨p, ENNReal.continuous_ofReal.comp hc, ?_, ?_, ?_⟩
  · intro z
    exact ofReal_integral_eq_lintegral_ofReal (hi z)
      (Eventually.of_forall (fun a => realGaussianKernel_nonneg F _ _))
  · intro z w hzw
    apply congrArg ENNReal.ofReal
    apply integral_congr_ae
    exact Eventually.of_forall (fun a => realGaussianKernel_radial F (r a) z w hzw)
  · intro z
    apply ENNReal.ofReal_le_ofReal
    exact integral_mono (hi z) h0 (fun a => realGaussianKernel_le_zero F _ _)

end GinibrePermanent977.Anticoncentration
-- Solutions/CofactorDensityBound.lean
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

def cofactorScale (F : Scalar) (n : ℕ) (B : Fin (n-1) → Fin n → F.K) : ℝ :=
  norm2 (perCofactor (n := n) B)/Real.sqrt (n.factorial : ℝ)

lemma cofactorScale_measurable (F : Scalar) (n : ℕ) : Measurable (cofactorScale F n) := by
  have hC : Measurable (perCofactor (n := n) :
    (Fin (n-1) → Fin n → F.K) → Fin n → F.K) := continuous_perCofactor.measurable
  unfold cofactorScale norm2
  fun_prop

lemma cofactorScale_ae_pos (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ B ∂ginibre F (n-1) n, 0 < cofactorScale F n B := by
  filter_upwards [(cofactor_inverse_moment F n hn).1] with B hB
  have hnorm : 0 ≤ norm2 (perCofactor (n := n) B) := Real.sqrt_nonneg _
  unfold cofactorScale
  apply div_pos (by nlinarith)
  apply Real.sqrt_pos.mpr
  exact_mod_cast n.factorial_pos

lemma cofactor_density_at_zero_bound (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ B, ENNReal.ofReal (realGaussianKernel F (cofactorScale F n B) 0) ∂ginibre F (n-1) n) ≤
      ENNReal.ofReal (kappa F n) := by
  let A := ((F.beta : ℝ)/(2*Real.pi))^((F.beta : ℝ)/2)*(n.factorial : ℝ)^((F.beta : ℝ)/2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint (B : Fin (n-1) → Fin n → F.K) :
      ENNReal.ofReal (realGaussianKernel F (cofactorScale F n B) 0) =
      ENNReal.ofReal A*ENNReal.ofReal ((norm2 (perCofactor (n := n) B)^2)^(-((F.beta : ℝ)/2))) := by
    rw [realGaussianKernel_zero]
    unfold cofactorScale
    rw [normalized_gaussian_prefactor, ENNReal.ofReal_mul hA]
  simp_rw [hpoint]
  have hC : Measurable (perCofactor (n := n) :
    (Fin (n-1) → Fin n → F.K) → Fin n → F.K) := continuous_perCofactor.measurable
  rw [lintegral_const_mul _ (by unfold norm2; fun_prop)]
  calc
    _ ≤ ENNReal.ofReal A*ENNReal.ofReal
        (((F.beta : ℝ)/2)^(((F.beta : ℝ)/2)*((n : ℝ)-1))*
          Real.Gamma ((F.beta : ℝ)/2)/Real.Gamma (((F.beta : ℝ)/2)*(n : ℝ))) := by
      gcongr
      exact (cofactor_inverse_moment F n hn).2
    _ = _ := by rw [← ENNReal.ofReal_mul hA, density_moment_kappa F n hn]

end GinibrePermanent977.Anticoncentration
-- Solutions/NormPerRowLaw.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma normPer_measurable (F : Scalar) (n : ℕ) :
    Measurable (normPer : (Fin n → Fin n → F.K) → F.K) := by
  have hP : Measurable (perK : (Fin n → Fin n → F.K) → F.K) := continuous_perK.measurable
  unfold normPer
  fun_prop

lemma normPer_first_row_law (F : Scalar) {n : ℕ} (B : Fin n → Fin (n+1) → F.K) :
    (gaussVec F (n+1)).map (fun g => normPer (Fin.cons g B)) =
      (gaussian F).map (fun x => cofactorScale F (n+1) B • x) := by
  have hrow : Measurable (fun g : Fin (n+1) → F.K =>
      ∑ j, g j*perCofactor (n := n+1) B j) := by fun_prop
  have hlaw := gaussian_row_law F (perCofactor (n := n+1) B)
  have heq : (fun g : Fin (n+1) → F.K => normPer (Fin.cons g B)) =
      (fun x : F.K => (Real.sqrt ((n+1).factorial : ℝ))⁻¹ • x) ∘
        (fun g => ∑ j, g j*perCofactor (n := n+1) B j) := by
    funext g
    unfold normPer
    rw [perK_cons_row]
    rfl
  rw [heq, ← Measure.map_map (by fun_prop) hrow, hlaw, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply, smul_smul, cofactorScale, div_eq_mul_inv]
  rw [mul_comm]

end GinibrePermanent977.Anticoncentration
-- Solutions/ScalarGeometry.lean
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma scalar_volume_eq_canonical (F : Scalar) :
    (@volume F.K (Scalar.instMeasureSpace F)) =
      (@volume F.K measureSpaceOfInnerProductSpace) := by cases F <;> rfl

instance scalar_nontrivial (F : Scalar) : Nontrivial F.K := by
  cases F
  · exact inferInstanceAs (Nontrivial ℝ)
  · exact inferInstanceAs (Nontrivial ℂ)
  · exact inferInstanceAs (Nontrivial ℍ[ℝ])

instance scalar_volume_openpos (F : Scalar) : (volume : Measure F.K).IsOpenPosMeasure := by
  rw [scalar_volume_eq_canonical]
  infer_instance

instance scalar_volume_sigmaFinite (F : Scalar) : SigmaFinite (volume : Measure F.K) := by
  rw [scalar_volume_eq_canonical]
  infer_instance

lemma scalar_volume_closedBall (F : Scalar) (z : F.K) (ε : ℝ) (hε : 0 ≤ ε) :
    volume (Metric.closedBall z ε) = ENNReal.ofReal (omegaBall F*ε^F.beta) := by
  rw [scalar_volume_eq_canonical, InnerProductSpace.volume_closedBall, scalar_real_dimension]
  have hπ : Real.sqrt Real.pi ^ F.beta = Real.pi^((F.beta : ℝ)/2) := by
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  rw [hπ, ← ENNReal.ofReal_pow hε, ← ENNReal.ofReal_mul (pow_nonneg hε _)]
  unfold omegaBall
  congr 1
  ring

lemma essSup_continuous_max_zero (F : Scalar) (p : F.K → ℝ≥0∞)
    (hp : Continuous p) (hmax : ∀ z, p z ≤ p 0) : essSup p volume = p 0 := by
  have heq : (⨆ z, p z) = essSup p volume := by
    apply iSup_eq_essSup
    intro z a hza
    exact ne_of_gt ((isOpen_lt continuous_const hp).measure_pos volume ⟨z,hza⟩)
  rw [← heq]
  exact le_antisymm (iSup_le hmax) (le_iSup p 0)

end GinibrePermanent977.Anticoncentration
-- Solutions/NormPerMixtureLaw.lean
open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma normPer_mixture_law (F : Scalar) (n : ℕ) (s : Set F.K) (hs : MeasurableSet s) :
    ginibre F (n+1) (n+1) (normPer ⁻¹' s) =
      ∫⁻ B : Fin n → Fin (n+1) → F.K,
        ((gaussian F).map (fun x => cofactorScale F (n+1) B • x)) s ∂ginibre F n (n+1) := by
  haveI : IsProbabilityMeasure (gaussVec F (n+1)) := by unfold gaussVec; infer_instance
  haveI : IsProbabilityMeasure (ginibre F n (n+1)) := by unfold ginibre; infer_instance
  have hcons : Measurable
      (fun p : (Fin (n+1) → F.K) × (Fin n → Fin (n+1) → F.K) =>
        (Fin.cons p.1 p.2 : Fin (n+1) → Fin (n+1) → F.K)) := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply i).comp measurable_snd
  letI : ∀ i : Fin (n+1), SigmaFinite ((fun _ : Fin (n+1) => gaussVec F (n+1)) i) :=
    fun _ => inferInstance
  have hsplit := (@measurePreserving_piFinSuccAbove n
    (fun _ : Fin (n+1) => Fin (n+1) → F.K) (fun _ => inferInstance)
    (fun _ : Fin (n+1) => gaussVec F (n+1)) (fun _ => inferInstance) 0).symm
  have hmap : MeasurePreserving
      (fun p : (Fin (n+1) → F.K) × (Fin n → Fin (n+1) → F.K) =>
        (Fin.cons p.1 p.2 : Fin (n+1) → Fin (n+1) → F.K))
      ((gaussVec F (n+1)).prod (ginibre F n (n+1))) (ginibre F (n+1) (n+1)) := by
    convert hsplit using 1 <;> try rfl
    funext p
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  have hN := normPer_measurable F (n+1)
  rw [← hmap.map_eq, Measure.map_apply hcons (hN hs), Measure.prod_apply_symm (hcons (hN hs))]
  apply lintegral_congr_ae
  apply Eventually.of_forall
  intro B
  have hrow : Measurable (fun g : Fin (n+1) → F.K => normPer (Fin.cons g B)) := by
    have hCB : Measurable (fun g : Fin (n+1) → F.K =>
        (Fin.cons g B : Fin (n+1) → Fin (n+1) → F.K)) := by
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact measurable_id
      · exact measurable_const
    exact hN.comp hCB
  have hlaw := normPer_first_row_law F B
  change (gaussVec F (n+1)) ((fun g : Fin (n+1) → F.K => normPer (Fin.cons g B)) ⁻¹' s) =
    ((gaussian F).map (fun x => cofactorScale F (n+1) B • x)) s
  rw [← hlaw, Measure.map_apply hrow hs]

lemma normPer_density_law (F : Scalar) (n : ℕ) (s : Set F.K) (hs : MeasurableSet s) :
    ginibre F (n+1) (n+1) (normPer ⁻¹' s) =
      ∫⁻ z in s, ∫⁻ B : Fin n → Fin (n+1) → F.K,
        ENNReal.ofReal (realGaussianKernel F (cofactorScale F (n+1) B) z)
          ∂ginibre F n (n+1) := by
  rw [normPer_mixture_law F n s hs]
  calc
    _ = ∫⁻ B : Fin n → Fin (n+1) → F.K,
        (∫⁻ z in s, ENNReal.ofReal (realGaussianKernel F (cofactorScale F (n+1) B) z))
          ∂ginibre F n (n+1) := by
      apply lintegral_congr_ae
      filter_upwards [cofactorScale_ae_pos F (n+1) (by omega)] with B hB
      rw [scaled_gaussian_kernel F _ hB, withDensity_apply _ hs]
    _ = _ := by
      have hm : Measurable (Function.uncurry (fun (B : Fin n → Fin (n+1) → F.K) (z : F.K) =>
          ENNReal.ofReal (realGaussianKernel F (cofactorScale F (n+1) B) z))) := by
        have hS := cofactorScale_measurable F (n+1)
        unfold realGaussianKernel
        fun_prop
      exact lintegral_lintegral_swap hm.aemeasurable

end GinibrePermanent977.Anticoncentration
-- Solutions/SmallBallDensity.lean
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma omegaBall_nonneg (F : Scalar) : 0 ≤ omegaBall F := by
  have hb := beta_pos F
  unfold omegaBall
  positivity

lemma smallBall_of_density {A : Type*} [MeasurableSpace A] (F : Scalar)
    (μ : Measure A) [IsProbabilityMeasure μ] (X : A → F.K) (hX : Measurable X)
    (p : F.K → ℝ≥0∞)
    (hlaw : ∀ s : Set F.K, MeasurableSet s → μ (X ⁻¹' s) = ∫⁻ z in s, p z)
    (hmax : ∀ z, p z ≤ p 0) (κ : ℝ) (hκ : p 0 ≤ ENNReal.ofReal κ)
    (ε : ℝ) (hε : 0 < ε) (z : F.K) :
    μ {ω | ‖X ω-z‖ ≤ ε} ≤ ENNReal.ofReal (min 1 (omegaBall F*κ*ε^F.beta)) := by
  have hevent : {ω | ‖X ω-z‖ ≤ ε} = X ⁻¹' Metric.closedBall z ε := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have hball : μ {ω | ‖X ω-z‖ ≤ ε} ≤ ENNReal.ofReal (omegaBall F*κ*ε^F.beta) := by
    rw [hevent, hlaw _ measurableSet_closedBall]
    calc
      _ ≤ ∫⁻ _ in Metric.closedBall z ε, ENNReal.ofReal κ :=
        lintegral_mono (fun w => (hmax w).trans hκ)
      _ = ENNReal.ofReal κ*volume (Metric.closedBall z ε) := by simp
      _ = _ := by
        rw [scalar_volume_closedBall F z ε hε.le, mul_comm,
          ← ENNReal.ofReal_mul (mul_nonneg (omegaBall_nonneg F) (pow_nonneg hε.le _))]
        congr 1
        ring
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
  exact le_min (by exact prob_le_one) hball

end GinibrePermanent977.Anticoncentration
-- Solutions/ExactDensity.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal Nat
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open GinibrePermanent977.Anticoncentration

theorem solution (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : F.K → ℝ≥0∞,
      Measurable p ∧
      (∀ s : Set F.K, MeasurableSet s →
        ginibre F n n (normPer ⁻¹' s) = ∫⁻ z in s, p z) ∧
      (∀ z w : F.K, ‖z‖ = ‖w‖ → p z = p w) ∧
      essSup p volume = p 0 ∧
      (∀ z : F.K, p z ≤ p 0) ∧
      p 0 ≤ ENNReal.ofReal (kappa F n) ∧
      ∀ ε : ℝ, 0 < ε → ∀ z : F.K,
        ginibre F n n {G | ‖normPer G - z‖ ≤ ε} ≤
          ENNReal.ofReal (min 1 (omegaBall F * kappa F n * ε ^ F.beta)) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  have hκ := cofactor_density_at_zero_bound F (m+1) (by omega)
  have hfin := lt_of_le_of_lt hκ (ENNReal.ofReal_lt_top)
  obtain ⟨p,hcont,hp,hrad,hmax⟩ := gaussian_mixture_properties F (ginibre F m (m+1))
    (cofactorScale F (m+1)) (cofactorScale_measurable F (m+1)) hfin
  have hlaw (s : Set F.K) (hs : MeasurableSet s) :
      ginibre F (m+1) (m+1) (normPer ⁻¹' s) = ∫⁻ z in s, p z := by
    rw [normPer_density_law F m s hs]
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall (fun z => (hp z).symm)
  have hp0 : p 0 ≤ ENNReal.ofReal (kappa F (m+1)) := (hp 0).trans_le hκ
  refine ⟨p,hcont.measurable,hlaw,hrad,essSup_continuous_max_zero F p hcont hmax,hmax,hp0,?_⟩
  intro ε hε z
  exact smallBall_of_density F (ginibre F (m+1) (m+1)) normPer (normPer_measurable F (m+1))
    p hlaw hmax (kappa F (m+1)) hp0 ε hε z
