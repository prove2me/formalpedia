-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.Amplification.preferred_scaling_model
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:59:07.158868+00:00
-- url     : https://prove2.me/submissions/d11ee981-af68-4885-adea-0031b8ae1986

import Mathlib
import Definitions.Def_FreeGroupFactorProof18
import Theorems.Thm_OAI_FreeGroupFactorMain_Amplification_preferred_unit_iso

set_option linter.all false

section
namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def rightRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulRight g⁻¹)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : rightRegular g ξ h = ξ (h * g) := by
  simp [rightRegular]

@[simp] theorem rightRegular_star {G : Type uG} [Group G] (g : G) :
    star (rightRegular g) = rightRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulRight g⁻¹)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (b * g⁻¹) = rightRegular g⁻¹ ξ b
  rw [rightRegular_apply]

theorem left_right_commute {G : Type uG} [Group G] (g h : G) :
    leftRegular g * rightRegular h = rightRegular h * leftRegular g := by
  ext ξ b
  simp [mul_assoc]

theorem rightRegular_mem_commutant {G : Type uG} [Group G] (g : G) :
    rightRegular g ∈ StarSubalgebra.centralizer ℂ (leftTranslations G) := by
  rw [StarSubalgebra.mem_centralizer_iff, leftTranslations_eq_range]
  rintro _ ⟨h, rfl⟩
  exact ⟨left_right_commute h g, by simp only [leftRegular_star]; exact left_right_commute _ _⟩

theorem groupVN_commute_right {G : Type uG} [Group G] (T : groupVonNeumann G) (g : G) :
    rightRegular g * (T : GroupOperator G) = (T : GroupOperator G) * rightRegular g :=
  ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ (rightRegular_mem_commutant g)).1

theorem canonicalTrace_eq_inner {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace T = inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
      ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))) := by
  classical
  simp only [canonicalTrace, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  apply congrArg (fun v : GroupHilbert G => ((T : GroupOperator G) v) 1)
  ext b
  simp [lp.single_apply, Pi.single_apply]

theorem canonicalTrace_star_mul {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace (star T * T) =
      (‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ ^ 2 : ℂ) := by
  rw [canonicalTrace_eq_inner]
  change inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
    (star (T : GroupOperator G) ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq_to_K _

def canonicalTraceLinear {G : Type uG} [Group G] : groupVonNeumann G →ₗ[ℂ] ℂ where
  toFun := canonicalTrace
  map_add' T U := by simp [canonicalTrace]
  map_smul' c T := by simp [canonicalTrace]

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped ComplexConjugate

open scoped ComplexConjugate ENNReal

 theorem operator_matrix_ext {G : Type uG} [DecidableEq G] (T U : GroupOperator G)
    (h : ∀ g, T (lp.single 2 g 1) = U (lp.single 2 g 1)) : T = U := by
  classical
  apply ContinuousLinearMap.ext
  intro ξ
  have hT := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL T
  have hU := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL U
  have he (g : G) : T (lp.single 2 g (ξ g)) = U (lp.single 2 g (ξ g)) := by
    have hc : lp.single (E := fun _ : G => ℂ) 2 g (ξ g) =
        (ξ g) • lp.single (E := fun _ : G => ℂ) 2 g 1 := by
      ext b
      simp [lp.single_apply, Pi.single_apply]
    rw [hc, map_smul, map_smul, h]
  simp only [he] at hT
  exact hT.unique hU

 theorem operator_coeff_tsum {G : Type uG} [DecidableEq G] (T : GroupOperator G)
    (ξ : GroupHilbert G) (x : G) :
    (T ξ) x = ∑' y : G, (T (lp.single 2 y 1)) x * ξ y := by
  calc
    (T ξ) x = inner ℂ (lp.single 2 x 1) (T ξ) := by simp [lp.inner_single_left]
    _ = inner ℂ (star T (lp.single 2 x 1)) ξ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = ∑' y : G, (T (lp.single 2 y 1)) x * ξ y := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro y
      have he : conj ((star T (lp.single 2 x 1)) y) = (T (lp.single 2 y 1)) x := by
        calc
          _ = inner ℂ (star T (lp.single 2 x 1)) (lp.single 2 y 1) := by
            simp [lp.inner_single_right]
          _ = inner ℂ (lp.single 2 x 1) (T (lp.single 2 y 1)) := by
            rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
          _ = _ := by simp [lp.inner_single_left]
      simp only [RCLike.inner_apply, he, mul_comm]

 theorem matrix_of_commute_right {G : Type uG} [Group G] [DecidableEq G]
    (T : GroupOperator G) (hT : ∀ g, rightRegular g * T = T * rightRegular g)
    (x y : G) :
    (T (lp.single 2 y 1)) x = (T deltaOne) (x * y⁻¹) := by
  have hr : rightRegular y⁻¹ deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, mul_inv_eq_one]
  rw [← hr]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne) (hT y⁻¹)
  simpa only [mul_apply_eq_comp, rightRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

 theorem matrix_of_commute_left {G : Type uG} [Group G] [DecidableEq G]
    (T : GroupOperator G) (hT : ∀ g, leftRegular g * T = T * leftRegular g)
    (x y : G) :
    (T (lp.single 2 y 1)) x = (T deltaOne) (y⁻¹ * x) := by
  have hl : leftRegular y deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]
  rw [← hl]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne) (hT y)
  simpa only [mul_apply_eq_comp, leftRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

 theorem mem_groupVN_iff_commute_right {G : Type uG} [Group G]
    (T : GroupOperator G) : T ∈ groupVonNeumann G ↔
      ∀ g, rightRegular g * T = T * rightRegular g := by
  classical
  refine ⟨fun h g => groupVN_commute_right ⟨T,h⟩ g, ?_⟩
  intro hT
  have hc (U : GroupOperator G) (hU : ∀ g, leftRegular g * U = U * leftRegular g) :
      U * T = T * U := by
    apply operator_matrix_ext
    intro k
    ext x
    have hleft : ((U * T) (lp.single 2 k 1)) x =
        ∑' y : G, (U deltaOne) (y⁻¹ * x) * (T deltaOne) (y * k⁻¹) := by
      change (U (T (lp.single 2 k 1))) x = _
      rw [operator_coeff_tsum U]
      apply tsum_congr
      intro y
      rw [matrix_of_commute_left U hU x y, matrix_of_commute_right T hT y k]
    have hright : ((T * U) (lp.single 2 k 1)) x =
        ∑' y : G, (T deltaOne) (x * y⁻¹) * (U deltaOne) (k⁻¹ * y) := by
      change (T (U (lp.single 2 k 1))) x = _
      rw [operator_coeff_tsum T]
      apply tsum_congr
      intro y
      rw [matrix_of_commute_right T hT x y, matrix_of_commute_left U hU y k]
    rw [hleft, hright]
    let e : G ≃ G := ((Equiv.inv G).trans (Equiv.mulLeft x)).trans (Equiv.mulRight k)
    have hs := e.tsum_eq (fun y => (U deltaOne) (y⁻¹ * x) * (T deltaOne) (y * k⁻¹))
    change (∑' c : G, (U deltaOne) ((x * c⁻¹ * k)⁻¹ * x) *
      (T deltaOne) (x * c⁻¹ * k * k⁻¹)) = _ at hs
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel,
      mul_inv_cancel, mul_one, mul_comm] using hs.symm
  rw [groupVonNeumann, StarSubalgebra.mem_centralizer_iff]
  intro U hU
  have hu : ∀ g, leftRegular g * U = U * leftRegular g := by
    intro g
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hU _
      (leftRegular_mem_leftTranslations g)).1
  refine ⟨hc U hu, hc (star U) ?_⟩
  intro g
  have hh := congrArg star (hu g⁻¹)
  simpa only [star_mul, leftRegular_star, inv_inv] using hh.symm

open scoped ComplexConjugate

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45

namespace Amplification

section

variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

end

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

end

open scoped ENNReal

end Amplification

namespace FreeFock
open scoped ENNReal

variable {α : Type u_15} {β : Type u_16} [DecidableEq α] [DecidableEq β]

end FreeFock
open Filter Topology

namespace Amplification

section
variable {A : Type u_17} {B : Type u_18} [CStarAlgebra A] [CStarAlgebra B]

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)]
variable (p : M) (hp : IsStarProjection p)

variable {E : Type u_19} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open scoped ENNReal ComplexConjugate
attribute [local instance] OAI.FreeGroupFactorMain.Amplification.instDecidableEqNestedHilbert

variable {I : Type u_21} {J : Type u_22}
abbrev NestedHilbert (I : Type u_23) (J : Type u_24) := lp (fun _ : I => GroupHilbert J) 2

def nestedDirac (ij : I × J) : NestedHilbert I J := by
  classical
  exact lp.single 2 ij.1 (lp.single 2 ij.2 1)

theorem nestedDirac_inner (x y : I × J) :
    inner ℂ (nestedDirac x) (nestedDirac y) = if x = y then 1 else 0 := by
  classical
  rcases x with ⟨i,j⟩
  rcases y with ⟨k,l⟩
  by_cases hik : i = k
  · subst k
    simp [nestedDirac,lp.inner_single_left,lp.single_apply,Pi.single_apply,RCLike.inner_apply]
  · simp [nestedDirac,lp.inner_single_left,lp.single_apply,hik]

theorem nestedDirac_inner_apply (ij : I × J) (ξ : NestedHilbert I J) :
    inner ℂ (nestedDirac ij) ξ = ξ ij.1 ij.2 := by
  classical
  simp [nestedDirac,lp.inner_single_left,RCLike.inner_apply]

theorem nestedDirac_orthogonal :
    (Submodule.span ℂ (Set.range (nestedDirac (I := I) (J := J))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro ξ hξ
  apply show ξ = 0 → ξ ∈ (⊥ : Submodule ℂ (NestedHilbert I J)) from fun h => h ▸ Submodule.zero_mem _
  ext i j
  have hh := ((Submodule.mem_orthogonal _ _).mp hξ) (nestedDirac (i,j))
    (Submodule.subset_span (Set.mem_range_self (i,j)))
  simpa only [nestedDirac_inner_apply,lp.coeFn_zero,Pi.zero_apply] using hh

def nestedBasis (I : Type u_25) (J : Type u_26) : HilbertBasis (I × J) ℂ (NestedHilbert I J) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_iff_ite.mpr nestedDirac_inner) nestedDirac_orthogonal

@[simp] theorem nestedBasis_apply (ij : I × J) : nestedBasis I J ij = nestedDirac ij := by
  simp [nestedBasis]

def hilbertFlatten (I : Type u_27) (J : Type u_28) : NestedHilbert I J ≃ₗᵢ[ℂ] GroupHilbert (I × J) :=
  (nestedBasis I J).repr

@[simp] theorem hilbertFlatten_apply (ξ : NestedHilbert I J) (ij : I × J) :
    hilbertFlatten I J ξ ij = ξ ij.1 ij.2 := by
  rw [hilbertFlatten,HilbertBasis.repr_apply_apply,nestedBasis_apply,nestedDirac_inner_apply]

@[simp] theorem hilbertFlatten_symm_apply (ξ : GroupHilbert (I × J)) (i : I) (j : J) :
    (hilbertFlatten I J).symm ξ i j = ξ (i,j) := by
  have hh := congrArg (fun v : GroupHilbert (I × J) => v (i,j))
    ((hilbertFlatten I J).apply_symm_apply ξ)
  simpa only [hilbertFlatten_apply] using hh

def diagonalValue (A : GroupOperator J) (ξ : NestedHilbert I J) : NestedHilbert I J :=
  ⟨fun i => A (ξ i),((lp.memℓp ξ).norm.const_smul ‖A‖).mono (fun i => A.le_opNorm (ξ i))⟩

theorem diagonalValue_norm_le (A : GroupOperator J) (ξ : NestedHilbert I J) :
    ‖diagonalValue A ξ‖ ≤ ‖A‖*‖ξ‖ := by
  have hh := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (x := diagonalValue A ξ) (y := (‖A‖ : ℝ) • ξ) (fun i => by
    change ‖A (ξ i)‖ ≤ ‖(‖A‖ : ℝ) • ξ i‖
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg A)] using A.le_opNorm (ξ i))
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg A)] using hh

theorem diagonalValue_add (operator : GroupOperator J) (left right : NestedHilbert I J) :
    diagonalValue operator (left + right) = diagonalValue operator left + diagonalValue operator right := by
  ext row column
  exact congrArg (fun vector : GroupHilbert J => vector column)
    (map_add operator (left row) (right row))

theorem diagonalValue_smul (operator : GroupOperator J) (scalar : ℂ) (vector : NestedHilbert I J) :
    diagonalValue operator (scalar • vector) = scalar • diagonalValue operator vector := by
  ext row column
  exact congrArg (fun image : GroupHilbert J => image column)
    (map_smul operator scalar (vector row))

theorem continuous_diagonalValue (operator : GroupOperator J) :
    Continuous (diagonalValue (I := I) operator) :=
  (LinearMap.mkContinuous
    { toFun := diagonalValue operator
      map_add' := diagonalValue_add operator
      map_smul' := diagonalValue_smul operator }
    ‖operator‖ (diagonalValue_norm_le operator) :
      NestedHilbert I J →L[ℂ] NestedHilbert I J).continuous

def diagonalOp (I : Type u_29) (A : GroupOperator J) :
    NestedHilbert I J →L[ℂ] NestedHilbert I J where
  toFun := diagonalValue A
  map_add' := diagonalValue_add A
  map_smul' := diagonalValue_smul A
  cont := continuous_diagonalValue A

@[simp] theorem diagonalOp_apply (A : GroupOperator J) (ξ : NestedHilbert I J) (i : I) :
    diagonalOp I A ξ i = A (ξ i) := rfl

theorem diagonalOp_star (A : GroupOperator J) :
    diagonalOp I (star A) = star (diagonalOp I A) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℂ
  intro η
  change inner ℂ (diagonalOp I (star A) ξ) η =
    inner ℂ ((ContinuousLinearMap.adjoint (diagonalOp I A)) ξ) η
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [lp.inner_eq_tsum,diagonalOp_apply]
  apply tsum_congr
  intro i
  simpa only [ContinuousLinearMap.star_eq_adjoint,lp.inner_eq_tsum] using ContinuousLinearMap.adjoint_inner_left A (η i) (ξ i)

def diagonalHom (I : Type u_30) (J : Type u_31) : GroupOperator J →⋆ₐ[ℂ] (NestedHilbert I J →L[ℂ] NestedHilbert I J) where
  toFun := diagonalOp I
  map_one' := by ext ξ i j; rfl
  map_mul' A B := by ext ξ i j; rfl
  map_zero' := by ext ξ i j; rfl
  map_add' A B := by ext ξ i j; rfl
  commutes' z := by ext ξ i j; rfl
  map_star' := diagonalOp_star

def productAmplification (I : Type u_32) (J : Type u_33) : GroupOperator J →⋆ₐ[ℂ] GroupOperator (I × J) :=
  (hilbertFlatten I J).conjStarAlgEquiv.toStarAlgHom.comp (diagonalHom I J)

@[simp] theorem productAmplification_apply (A : GroupOperator J) (ξ : GroupHilbert (I × J))
    (i : I) (j : J) :
    productAmplification I J A ξ (i,j) =
      A ((hilbertFlatten I J).symm ξ i) j := by
  change hilbertFlatten I J (diagonalOp I A ((hilbertFlatten I J).symm ξ)) (i,j) = _
  rw [hilbertFlatten_apply,diagonalOp_apply]

end
section
open scoped ENNReal

variable {I : Type u_35} {J : Type u_36}

variable {G : Type u_37} [Group G]

theorem stabilizedRightTranslations_eq_range :
    stabilizedRightTranslations G = Set.range (fun g : G => productAmplification ℕ G (rightRegular g)) := by
  ext T
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨g,?_⟩
    apply ContinuousLinearMap.ext
    intro ξ
    ext x
    rw [hg]
    rcases x with ⟨i,j⟩
    simp only [productAmplification_apply,rightRegular_apply,hilbertFlatten_symm_apply]
  · rintro ⟨g,rfl⟩
    refine ⟨g,?_⟩
    intro ξ x
    rcases x with ⟨i,j⟩
    simp only [productAmplification_apply,rightRegular_apply,hilbertFlatten_symm_apply]

end

section
open scoped ENNReal
variable {G : Type u_38}

variable [Group G]

end

open scoped ENNReal
variable {G : Type u_45} [Group G]

end Amplification

namespace Interpolation

open Amplification
open scoped ENNReal

end Interpolation

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.HilbertUltraweak
variable (E : Type u_1) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

@[instance_reducible] def topology : TopologicalSpace (E →L[ℂ] E) :=
  ⨅ (ξ : lp (fun _ : ℕ => E) 2) (η : lp (fun _ : ℕ => E) 2),
    TopologicalSpace.induced (fun T : E →L[ℂ] E => ∑' k : ℕ, inner ℂ (η k) (T (ξ k))) inferInstance

variable {E} {F : Type u_2} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
def sequenceMap (L : E →L[ℂ] F) (ξ : lp (fun _ : ℕ => E) 2) : lp (fun _ : ℕ => F) 2 :=
  ⟨fun k => L (ξ k),((lp.memℓp ξ).norm.const_mul ‖L‖).mono (fun k => L.le_opNorm (ξ k))⟩

omit [CompleteSpace E] in
theorem functional_continuous (ξ η : lp (fun _ : ℕ => E) 2) :
    @Continuous _ _ (topology E) _ (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (T (ξ k))) :=
  continuous_iInf_dom (i := ξ) (continuous_iInf_dom (i := η) continuous_induced_dom)

theorem sandwich_continuous (L : E →L[ℂ] F) (R : F →L[ℂ] E) :
    @Continuous _ _ (topology E) (topology F) (fun T : E →L[ℂ] E => L.comp (T.comp R)) := by
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have he : (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (L (T (R (ξ k)))))=
      (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (sequenceMap (ContinuousLinearMap.adjoint L) η k)
        (T (sequenceMap R ξ k))) := by
    funext T
    apply tsum_congr
    intro k
    exact (ContinuousLinearMap.adjoint_inner_left L (T (R (ξ k))) (η k)).symm
  change @Continuous _ _ (topology E) _ (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (L (T (R (ξ k)))))
  rw [he]
  exact functional_continuous _ _

omit [CompleteSpace E] in
theorem add_continuous {X : Type u_3} [TopologicalSpace X] {f g : X → (E →L[ℂ] E)}
    (hf : @Continuous _ _ _ (topology E) f) (hg : @Continuous _ _ _ (topology E) g) :
    @Continuous _ _ _ (topology E) (fun x => f x+g x) := by
  let : TopologicalSpace (E →L[ℂ] E) := topology E
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have he (x : X) :
      (∑' k : ℕ,inner ℂ (η k) ((f x+g x) (ξ k)))=
        (∑' k : ℕ,inner ℂ (η k) (f x (ξ k)))+(∑' k : ℕ,inner ℂ (η k) (g x (ξ k))) := by
    simp only [add_apply,inner_add_right]
    exact (lp.summable_inner η (sequenceMap (f x) ξ)).tsum_add (lp.summable_inner η (sequenceMap (g x) ξ))
  change Continuous (fun x : X => ∑' k : ℕ,inner ℂ (η k) ((f x+g x) (ξ k)))
  simp_rw [he]
  exact ((functional_continuous ξ η).comp hf).add ((functional_continuous ξ η).comp hg)
end FreeGroupFactorMain.HilbertUltraweak

section
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_4} [Ring A] [StarRing A]

end FreeGroupFactorMain.CornerRerouting

namespace FreeGroupFactorMain.FullReducingCorner
open Amplification CornerRerouting
variable {A : Type u_5} [CStarAlgebra A]

variable (p : A) (hp : IsStarProjection p) (s : Set A)
variable (hps : p∈StarSubalgebra.centralizer ℂ s)

variable (v : A) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : p*v=v) (hvr : v*(1-p)=v) (hvi : star v*v=1-p)

end FreeGroupFactorMain.FullReducingCorner

end

namespace FreeGroupFactorMain.ReducingSubspace
variable {E : Type u_6} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (K : Submodule ℂ E) [CompleteSpace K]

variable [CompleteSpace E]

end FreeGroupFactorMain.ReducingSubspace

namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace
variable {A : Type u_7} {E : Type u_8} {I : Type u_9} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification CyclicSpectral GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31

namespace FreeGroupFactorMain
namespace InfiniteICC

end InfiniteICC

end FreeGroupFactorMain

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_9} [CStarAlgebra A]

end
section
open scoped ENNReal ComplexConjugate

variable {I : Type u_11} {J : Type u_12}
end
section
open scoped ENNReal

variable {I : Type u_14} {J : Type u_15}

variable {G : Type u_16} [Group G]

end
section
open scoped ENNReal
variable {I : Type u_17} {J : Type u_18}

def productSingle (I : Type u_19) (J : Type u_20) (j : I) : GroupHilbert J →L[ℂ] GroupHilbert (I × J) := by
  classical
  exact (hilbertFlatten I J).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (lp.singleContinuousLinearMap ℂ (fun _ : I => GroupHilbert J) 2 j)

@[simp] theorem productSingle_apply [DecidableEq I] (j i : I) (ξ : GroupHilbert J) (k : J) :
    productSingle I J j ξ (i,k) = if i = j then ξ k else 0 := by
  classical
  by_cases hi : i = j <;> simp [productSingle,hilbertFlatten_apply,lp.single_apply,hi]

def matrixEntry (T : GroupOperator (I × J)) (i j : I) : GroupOperator J :=
  (lp.evalCLM ℂ (fun _ : I => GroupHilbert J) 2 i).comp
    ((hilbertFlatten I J).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp (productSingle I J j)))

@[simp] theorem matrixEntry_apply (T : GroupOperator (I × J)) (i j : I)
    (ξ : GroupHilbert J) (k : J) :
    matrixEntry T i j ξ k = T (productSingle I J j ξ) (i,k) := by
  exact hilbertFlatten_symm_apply _ _ _

theorem productSingle_single [DecidableEq I] [DecidableEq J] [DecidableEq (I × J)]
    (j : I) (g : J) : productSingle I J j (lp.single 2 g 1) = lp.single 2 (j,g) 1 := by
  classical
  ext x
  rcases x with ⟨i,k⟩
  simp only [productSingle_apply,lp.single_apply,Pi.single_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

theorem matrixEntry_ext (T U : GroupOperator (I × J))
    (h : ∀ i j, matrixEntry T i j = matrixEntry U i j) : T = U := by
  classical
  apply operator_matrix_ext
  intro x
  rcases x with ⟨j,g⟩
  rw [← productSingle_single]
  ext y
  rcases y with ⟨i,k⟩
  simpa only [matrixEntry_apply] using congrArg (fun A : GroupOperator J => A (lp.single 2 g 1) k) (h i j)

theorem productAmplification_productSingle (S : GroupOperator J) (j : I) (ξ : GroupHilbert J) :
    productAmplification I J S (productSingle I J j ξ) = productSingle I J j (S ξ) := by
  classical
  ext x
  rcases x with ⟨i,k⟩
  rw [productAmplification_apply,productSingle_apply]
  have he : (hilbertFlatten I J).symm (productSingle I J j ξ) i = if i=j then ξ else 0 := by
    ext l
    simp only [hilbertFlatten_symm_apply,productSingle_apply]
    split_ifs <;> rfl
  rw [he]
  split_ifs <;> simp

theorem matrixEntry_diagonal_mul (S : GroupOperator J) (T : GroupOperator (I × J)) (i j : I) :
    matrixEntry (productAmplification I J S * T) i j = S * matrixEntry T i j := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext k
  simp only [matrixEntry_apply,mul_apply_eq_comp,productAmplification_apply]
  rfl

theorem matrixEntry_mul_diagonal (S : GroupOperator J) (T : GroupOperator (I × J)) (i j : I) :
    matrixEntry (T * productAmplification I J S) i j = matrixEntry T i j * S := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext k
  simp only [matrixEntry_apply,mul_apply_eq_comp,productAmplification_productSingle]

variable {G : Type u_21} [Group G]

theorem mem_stabilization_iff_matrix (T : GroupOperator (ℕ × G)) :
    T ∈ stabilization G ↔ ∀ i j, matrixEntry T i j ∈ groupVonNeumann G := by
  rw [stabilization,StarSubalgebra.mem_centralizer_iff,stabilizedRightTranslations_eq_range]
  constructor
  · intro h i j
    rw [mem_groupVN_iff_commute_right]
    intro g
    have hh := (h _ ⟨g,rfl⟩).1
    have he := congrArg (fun A => matrixEntry A i j) hh
    simpa only [matrixEntry_diagonal_mul,matrixEntry_mul_diagonal] using he
  · intro h S hS
    obtain ⟨g,rfl⟩ := hS
    have hc (g : G) : productAmplification ℕ G (rightRegular g) * T =
        T * productAmplification ℕ G (rightRegular g) := by
      apply matrixEntry_ext
      intro i j
      rw [matrixEntry_diagonal_mul,matrixEntry_mul_diagonal]
      exact (mem_groupVN_iff_commute_right _).mp (h i j) g
    exact ⟨hc g,by rw [← map_star,rightRegular_star]; exact hc g⁻¹⟩

end
section
variable {I : Type u_22} {J : Type u_23}

 def productCoordinate (I : Type u_24) (J : Type u_25) (i : I) : GroupHilbert (I × J) →L[ℂ] GroupHilbert J :=
  (lp.evalCLM ℂ (fun _ : I => GroupHilbert J) 2 i).comp
    (hilbertFlatten I J).symm.toContinuousLinearEquiv.toContinuousLinearMap

 theorem productCoordinate_apply (i : I) (ξ : GroupHilbert (I × J)) (j : J) :
    productCoordinate I J i ξ j=ξ (i,j) := hilbertFlatten_symm_apply _ _ _

 variable {G : Type u_28} [Group G]

end
open scoped ENNReal
variable {I : Type u_29} {J : Type u_30}

 theorem productSingle_inner_right (i : I) (ξ : GroupHilbert (I × J)) (η : GroupHilbert J) :
    inner ℂ ξ (productSingle I J i η)=inner ℂ (productCoordinate I J i ξ) η := by
  classical
  change inner ℂ ξ ((hilbertFlatten I J) (lp.single 2 i η))=
    inner ℂ (((hilbertFlatten I J).symm ξ) i) η
  have he := (hilbertFlatten I J).inner_map_map ((hilbertFlatten I J).symm ξ) (lp.single 2 i η)
  simpa only [LinearIsometryEquiv.apply_symm_apply,lp.inner_single_right] using he

 theorem productSingle_inner_left (i : I) (ξ : GroupHilbert (I × J)) (η : GroupHilbert J) :
    inner ℂ (productSingle I J i η) ξ=inner ℂ η (productCoordinate I J i ξ) := by
  have he := congrArg (star : ℂ → ℂ) (productSingle_inner_right i ξ η)
  change (starRingEnd ℂ) (inner ℂ ξ (productSingle I J i η))=
    (starRingEnd ℂ) (inner ℂ (productCoordinate I J i ξ) η) at he
  simpa only [inner_conj_symm] using he

 theorem matrixEntry_star (T : GroupOperator (I × J)) (i j : I) :
    matrixEntry (star T) i j=star (matrixEntry T j i) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  have he (T : GroupOperator (I × J)) (i j : I) (ξ : GroupHilbert J) :
      matrixEntry T i j ξ=productCoordinate I J i (T (productSingle I J j ξ)) := rfl
  rw [he,← productSingle_inner_left,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,productSingle_inner_right]
  change inner ℂ (matrixEntry T j i η) ξ=inner ℂ η (star (matrixEntry T j i) ξ)
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

 variable {G : Type u_31} [Group G] [DecidableEq G]

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1}

def matrixBlock (i j : ℕ) (T : GroupOperator G) : GroupOperator (ℕ × G) :=
  (productSingle ℕ G i).comp (T.comp (productCoordinate ℕ G j))

@[simp] theorem matrixBlock_apply (i j k : ℕ) (T : GroupOperator G)
    (ξ : GroupHilbert (ℕ × G)) (g : G) :
    matrixBlock i j T ξ (k,g)=if k=i then T (productCoordinate ℕ G j ξ) g else 0 := by
  simp only [matrixBlock,ContinuousLinearMap.comp_apply,productSingle_apply]

@[simp] theorem productCoordinate_productSingle (i j : ℕ) (ξ : GroupHilbert G) :
    productCoordinate ℕ G i (productSingle ℕ G j ξ)=if i=j then ξ else 0 := by
  ext g
  simp only [productCoordinate_apply,productSingle_apply]
  split_ifs <;> rfl

@[simp] theorem matrixEntry_matrixBlock (i j k l : ℕ) (T : GroupOperator G) :
    matrixEntry (matrixBlock i j T) k l=if k=i ∧ l=j then T else 0 := by
  ext ξ g
  simp only [matrixEntry_apply,matrixBlock_apply,productCoordinate_productSingle]
  by_cases hk : k=i <;> by_cases hl : l=j <;> simp [hk,hl,show (j=l) ↔ (l=j) from eq_comm]

@[simp] theorem matrixBlock_zero (i j : ℕ) : matrixBlock i j (0 : GroupOperator G)=0 := by
  ext ξ ⟨k,g⟩
  simp

@[simp] theorem matrixBlock_mul (i j k l : ℕ) (T S : GroupOperator G) :
    matrixBlock i j T * matrixBlock k l S=if j=k then matrixBlock i l (T*S) else 0 := by
  ext ξ ⟨m,g⟩
  simp only [mul_apply_eq_comp,matrixBlock_apply]
  have hc : productCoordinate ℕ G j (matrixBlock k l S ξ)=
      if j=k then S (productCoordinate ℕ G l ξ) else 0 := by
    change productCoordinate ℕ G j (productSingle ℕ G k (S (productCoordinate ℕ G l ξ)))=_
    rw [productCoordinate_productSingle]
  rw [hc]
  by_cases hj : j=k <;> by_cases hm : m=i <;> simp [hj,hm,mul_apply_eq_comp]

@[simp] theorem matrixBlock_star (i j : ℕ) (T : GroupOperator G) :
    star (matrixBlock i j T)=matrixBlock j i (star T) := by
  apply matrixEntry_ext
  intro k l
  rw [matrixEntry_star,matrixEntry_matrixBlock,matrixEntry_matrixBlock]
  by_cases h : l=i ∧ k=j
  · simp only [ite_eq_left h,ite_eq_left (And.symm h)]
  · simp only [ite_eq_right h,ite_eq_right (fun hh => h (And.symm hh)),star_zero (GroupOperator G)]

theorem matrixBlock_mem [Group G] (i j : ℕ) (T : groupVonNeumann G) :
    matrixBlock i j (T : GroupOperator G)∈stabilization G := by
  rw [mem_stabilization_iff_matrix]
  intro k l
  rw [matrixEntry_matrixBlock]
  split_ifs
  · exact T.property
  · exact (groupVonNeumann G).zero_mem

def finiteMatrix (n : ℕ) (X : Fin n → Fin n → GroupOperator G) : GroupOperator (ℕ × G) :=
  ∑ i : Fin n, ∑ j : Fin n, matrixBlock i.val j.val (X i j)

@[simp] theorem matrixEntry_sum {ι : Type u_2} (s : Finset ι) (X : ι → GroupOperator (ℕ × G)) (i j : ℕ) :
    matrixEntry (∑ k∈s,X k) i j=∑ k∈s,matrixEntry (X k) i j := by
  classical
  induction s using Finset.induction_on with
  | empty => ext ξ g; simp [matrixEntry_apply]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [show matrixEntry (X a + ∑ k∈s,X k) i j=matrixEntry (X a) i j+matrixEntry (∑ k∈s,X k) i j by ext ξ g; simp [matrixEntry_apply],ih]

theorem matrixEntry_finiteMatrix (n : ℕ) (X : Fin n → Fin n → GroupOperator G) (i j : Fin n) :
    matrixEntry (finiteMatrix n X) i.val j.val=X i j := by
  classical
  simp [finiteMatrix,matrixEntry_sum,matrixEntry_matrixBlock,Fin.val_inj,ite_and]

theorem matrixEntry_finiteMatrix_out (n : ℕ) (X : Fin n → Fin n → GroupOperator G) (i j : ℕ)
    (h : n ≤ i ∨ n ≤ j) : matrixEntry (finiteMatrix n X) i j=0 := by
  classical
  simp only [finiteMatrix,matrixEntry_sum,matrixEntry_matrixBlock]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [ite_eq_right]
  rintro ⟨rfl,rfl⟩
  cases h with
  | inl h => exact (not_le_of_gt a.isLt) h
  | inr h => exact (not_le_of_gt b.isLt) h

theorem finiteMatrix_mem [Group G] (n : ℕ) (X : Fin n → Fin n → groupVonNeumann G) :
    finiteMatrix n (fun i j => (X i j : GroupOperator G))∈stabilization G := by
  classical
  exact (stabilization G).sum_mem (fun i _ => (stabilization G).sum_mem (fun j _ => matrixBlock_mem i.val j.val (X i j)))

@[simp] theorem matrixBlock_add (i j : ℕ) (T S : GroupOperator G) :
    matrixBlock i j (T+S)=matrixBlock i j T+matrixBlock i j S := by
  ext ξ ⟨k,g⟩
  by_cases h : k=i <;> simp [h]

@[simp] theorem matrixBlock_smul (i j : ℕ) (c : ℂ) (T : GroupOperator G) :
    matrixBlock i j (c • T)=c • matrixBlock i j T := by
  ext ξ ⟨k,g⟩
  by_cases h : k=i <;> simp [h]

@[simp] theorem matrixBlock_sum {ι : Type u_3} (i j : ℕ) (s : Finset ι) (T : ι → GroupOperator G) :
    matrixBlock i j (∑ k∈s,T k)=∑ k∈s,matrixBlock i j (T k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha,ih]

 theorem matrixBlock_mul_finiteMatrix (n : ℕ) (i : ℕ) (j : Fin n) (T : GroupOperator G)
    (Y : Fin n → Fin n → GroupOperator G) :
    matrixBlock i j.val T * finiteMatrix n Y=∑ l : Fin n,matrixBlock i l.val (T*Y j l) := by
  classical
  simp only [finiteMatrix,Finset.mul_sum,matrixBlock_mul,Fin.val_inj]
  rw [Finset.sum_comm]
  congr 1
  ext l
  simp

 theorem finiteMatrix_mul (n : ℕ) (X Y : Fin n → Fin n → GroupOperator G) :
    finiteMatrix n X * finiteMatrix n Y=finiteMatrix n (fun i j => ∑ k : Fin n,X i k*Y k j) := by
  classical
  simp only [finiteMatrix,Finset.sum_mul]
  change (∑ i : Fin n,∑ j : Fin n,matrixBlock i.val j.val (X i j)*finiteMatrix n Y)=_
  simp only [matrixBlock_mul_finiteMatrix,matrixBlock_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

 theorem finiteMatrix_star (n : ℕ) (X : Fin n → Fin n → GroupOperator G) :
    star (finiteMatrix n X)=finiteMatrix n (fun i j => star (X j i)) := by
  classical
  simp only [finiteMatrix,star_sum (R := GroupOperator (ℕ × G)),matrixBlock_star]
  exact Finset.sum_comm

 def finiteDiagonal (n : ℕ) (T : GroupOperator G) : GroupOperator (ℕ × G) :=
  finiteMatrix n (fun i j => if i=j then T else 0)

 theorem finiteDiagonal_sum (n : ℕ) (T : GroupOperator G) :
    finiteDiagonal n T=∑ i : Fin n,matrixBlock i.val i.val T := by
  classical
  simp only [finiteDiagonal,finiteMatrix]
  apply Finset.sum_congr rfl
  intro i _
  have hh (j : Fin n) : matrixBlock i.val j.val (if i=j then T else 0)=if i=j then matrixBlock i.val j.val T else 0 := by split_ifs <;> simp
  simp_rw [hh]
  simp

 theorem finiteDiagonal_mul (n : ℕ) (T S : GroupOperator G) :
    finiteDiagonal n T*finiteDiagonal n S=finiteDiagonal n (T*S) := by
  classical
  rw [finiteDiagonal,finiteDiagonal,finiteMatrix_mul]
  congr 1
  funext i j
  simp

 theorem finiteDiagonal_star (n : ℕ) (T : GroupOperator G) :
    star (finiteDiagonal n T)=finiteDiagonal n (star T) := by
  classical
  rw [finiteDiagonal,finiteMatrix_star]
  congr 1
  funext i j
  split_ifs <;> simp_all [eq_comm,star_zero (R := GroupOperator G)]

theorem matrixBlock_sandwich (i j k l : ℕ) (A B : GroupOperator G) (T : GroupOperator (ℕ × G)) :
    matrixBlock i j A*T*matrixBlock k l B=matrixBlock i l (A*matrixEntry T j k*B) := by
  apply ContinuousLinearMap.ext
  intro ξ
  rfl

 theorem finiteDiagonal_sandwich (n : ℕ) (A B : GroupOperator G) (T : GroupOperator (ℕ × G)) :
    finiteDiagonal n A*T*finiteDiagonal n B=
      finiteMatrix n (fun i j => A*matrixEntry T i.val j.val*B) := by
  classical
  simp only [finiteDiagonal_sum,Finset.sum_mul,Finset.mul_sum,matrixBlock_sandwich,finiteMatrix]
  exact Finset.sum_comm

variable [Group G]

 def finiteProjection (n : ℕ) (p : groupVonNeumann G) : stabilization G :=
  ⟨finiteDiagonal n (p : GroupOperator G),by
    classical
    rw [finiteDiagonal_sum]
    exact (stabilization G).sum_mem (fun i _ => matrixBlock_mem i.val i.val p)⟩

 theorem finiteProjection_projection (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) :
    IsStarProjection (finiteProjection n p) := by
  constructor
  · apply Subtype.ext
    change finiteDiagonal n (p : GroupOperator G)*finiteDiagonal n (p : GroupOperator G)=_
    rw [finiteDiagonal_mul]
    exact congrArg (finiteDiagonal n) (congrArg Subtype.val hp.isIdempotentElem.eq)
  · apply Subtype.ext
    change star (finiteDiagonal n (p : GroupOperator G))=_
    rw [finiteDiagonal_star]
    exact congrArg (finiteDiagonal n) (congrArg Subtype.val hp.isSelfAdjoint.star_eq)

 theorem finiteDiagonal_entries (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : Corner (finiteProjection n p) (finiteProjection_projection n p hp)) :
    finiteMatrix n (fun i j => (p : GroupOperator G)*matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val*(p : GroupOperator G))=
      (x.val : GroupOperator (ℕ × G)) := by
  rw [←finiteDiagonal_sandwich]
  change ((finiteProjection n p * x.val * finiteProjection n p : stabilization G) : GroupOperator (ℕ × G))=_
  rw [x.property.1,x.property.2]

end

open scoped ENNReal
variable {G : Type u_4} [Group G]

abbrev FiniteCorner (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) :=
  Corner (finiteProjection n p) (finiteProjection_projection n p hp)

theorem finiteCorner_entry_sandwich (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (i j : Fin n) :
    (p : GroupOperator G)*matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val*(p : GroupOperator G)=
      matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val := by
  have hh := congrArg (fun T : GroupOperator (ℕ × G) => matrixEntry T i.val j.val)
    (finiteDiagonal_entries n p hp x)
  rwa [matrixEntry_finiteMatrix] at hh

def finiteCornerEntry (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (i j : Fin n) : Corner p hp := by
  let T : groupVonNeumann G := ⟨matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val,
    (mem_stabilization_iff_matrix _).mp x.val.property i.val j.val⟩
  have hh : p*T*p=T := Subtype.ext (finiteCorner_entry_sandwich n p hp x i j)
  refine ⟨T,?_,?_⟩
  · calc p*T=p*(p*T*p) := congrArg (p*·) hh.symm
         _=p*T*p := by rw [←mul_assoc,←mul_assoc,hp.isIdempotentElem.eq]
         _=T := hh
  · calc T*p=(p*T*p)*p := congrArg (·*p) hh.symm
         _=p*T*p := by rw [mul_assoc (p*T),hp.isIdempotentElem.eq]
         _=T := hh

theorem finiteCorner_reconstruct (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) :
    finiteMatrix n (fun i j => ((finiteCornerEntry n p hp x i j).val : GroupOperator G))=
      (x.val : GroupOperator (ℕ × G)) := by
  have he : (fun i j : Fin n => ((finiteCornerEntry n p hp x i j).val : GroupOperator G))=
      (fun i j : Fin n => (p : GroupOperator G)*matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val*(p : GroupOperator G)) := by
    funext i j
    exact (finiteCorner_entry_sandwich n p hp x i j).symm
  rw [he]
  exact finiteDiagonal_entries n p hp x

theorem finiteCorner_ext (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x y : FiniteCorner n p hp) (h : ∀ i j,finiteCornerEntry n p hp x i j=finiteCornerEntry n p hp y i j) : x=y := by
  apply Subtype.ext
  apply Subtype.ext
  rw [←finiteCorner_reconstruct n p hp x,←finiteCorner_reconstruct n p hp y]
  congr 1
  funext i j
  rw [h i j]

 def finiteCornerOfMatrix (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (X : Fin n → Fin n → Corner p hp) : FiniteCorner n p hp := by
  let T : stabilization G := ⟨finiteMatrix n (fun i j => ((X i j).val : GroupOperator G)),
    finiteMatrix_mem n (fun i j => (X i j).val)⟩
  refine ⟨T,?_,?_⟩
  · apply Subtype.ext
    change finiteMatrix n (fun i j => if i=j then (p : GroupOperator G) else 0)*finiteMatrix n _=_
    rw [finiteMatrix_mul]
    congr 1
    funext i j
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    exact congrArg Subtype.val (X i j).property.1
  · apply Subtype.ext
    change finiteMatrix n _*finiteMatrix n (fun i j => if i=j then (p : GroupOperator G) else 0)=_
    rw [finiteMatrix_mul]
    congr 1
    funext i j
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact congrArg Subtype.val (X i j).property.2

@[simp] theorem finiteCornerEntry_ofMatrix (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (X : Fin n → Fin n → Corner p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (finiteCornerOfMatrix n p hp X) i j=X i j := by
  apply Subtype.ext
  apply Subtype.ext
  exact matrixEntry_finiteMatrix n _ i j

@[simp] theorem finiteCornerEntry_add (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x y : FiniteCorner n p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (x+y) i j=finiteCornerEntry n p hp x i j+finiteCornerEntry n p hp y i j := by
  apply Subtype.ext
  apply Subtype.ext
  ext ξ g
  simp [finiteCornerEntry,matrixEntry_apply]

@[simp] theorem finiteCornerEntry_smul (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (c : ℂ) (i j : Fin n) :
    finiteCornerEntry n p hp (c • x) i j=c • finiteCornerEntry n p hp x i j := by
  apply Subtype.ext
  apply Subtype.ext
  ext ξ g
  simp [finiteCornerEntry,matrixEntry_apply]

@[simp] theorem finiteCornerEntry_star (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (star x) i j=star (finiteCornerEntry n p hp x j i) := by
  apply Subtype.ext
  apply Subtype.ext
  exact matrixEntry_star _ i.val j.val

 theorem finiteCornerEntry_mul (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x y : FiniteCorner n p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (x*y) i j=∑ k : Fin n,finiteCornerEntry n p hp x i k*finiteCornerEntry n p hp y k j := by
  apply Subtype.ext
  apply Subtype.ext
  change matrixEntry ((x.val : GroupOperator (ℕ × G))*(y.val : GroupOperator (ℕ × G))) i.val j.val=_
  rw [←finiteCorner_reconstruct n p hp x,←finiteCorner_reconstruct n p hp y,finiteMatrix_mul,matrixEntry_finiteMatrix]
  simp

variable {H : Type u_5} [Group H]

def finiteCornerIso (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (q : groupVonNeumann H) (hq : IsStarProjection q) (e : Corner p hp ≃⋆ₐ[ℂ] Corner q hq) :
    FiniteCorner n p hp ≃⋆ₐ[ℂ] FiniteCorner n q hq where
  toFun x := finiteCornerOfMatrix n q hq (fun i j => e (finiteCornerEntry n p hp x i j))
  invFun x := finiteCornerOfMatrix n p hp (fun i j => e.symm (finiteCornerEntry n q hq x i j))
  left_inv x := by
    apply finiteCorner_ext n p hp
    intro i j
    simp only [finiteCornerEntry_ofMatrix,StarAlgEquiv.symm_apply_apply]
  right_inv x := by
    apply finiteCorner_ext n q hq
    intro i j
    simp only [finiteCornerEntry_ofMatrix,StarAlgEquiv.apply_symm_apply]
  map_mul' x y := by
    apply finiteCorner_ext n q hq
    intro i j
    simp only [finiteCornerEntry_ofMatrix,finiteCornerEntry_mul]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact e.map_mul' _ _
  map_add' x y := by
    apply finiteCorner_ext n q hq
    intro i j
    simp only [finiteCornerEntry_add,finiteCornerEntry_ofMatrix]
    exact e.map_add' _ _
  map_smul' c x := by
    apply finiteCorner_ext n q hq
    intro i j
    simp only [finiteCornerEntry_smul,finiteCornerEntry_ofMatrix]
    exact e.map_smul' c _
  map_star' x := by
    apply finiteCorner_ext n q hq
    intro i j
    simp only [finiteCornerEntry_star,finiteCornerEntry_ofMatrix]
    exact e.map_star' _

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

section
namespace FreeGroupFactorMain.HilbertUltraweak
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {X : Type u_2} [TopologicalSpace X]

theorem finset_sum_continuous {ι : Type u_3} (s : Finset ι) (f : ι → X → (E →L[ℂ] E))
    (hf : ∀ i∈s,@Continuous _ _ _ (topology E) (f i)) :
    @Continuous _ _ _ (topology E) (fun x => ∑ i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (@continuous_const X _ _ (topology E) (0 : E →L[ℂ] E))
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact add_continuous (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
end FreeGroupFactorMain.HilbertUltraweak

namespace FreeGroupFactorMain.Amplification
variable {G : Type u_4} {H : Type u_5}

 theorem matrixEntry_normal (i j : ℕ) :
    @Continuous _ _ (ultraweakOperatorTopology (ℕ × G)) (ultraweakOperatorTopology G)
      (fun T : GroupOperator (ℕ × G) => matrixEntry T i j) := by
  have hc := HilbertUltraweak.sandwich_continuous (productCoordinate ℕ G i) (productSingle ℕ G j)
  convert hc using 1 <;> rfl

 theorem matrixBlock_normal (i j : ℕ) :
    @Continuous _ _ (ultraweakOperatorTopology G) (ultraweakOperatorTopology (ℕ × G))
      (matrixBlock (G := G) i j) :=
  HilbertUltraweak.sandwich_continuous (productSingle ℕ G i) (productCoordinate ℕ G j)

variable [Group G] [Group H]

 theorem finiteCornerEntry_normal (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) (i j : Fin n) :
    @Continuous _ _ (cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp))
      (cornerTopology (groupUltraweakTopology G) p hp) (fun x => finiteCornerEntry n p hp x i j) := by
  let : TopologicalSpace (GroupOperator (ℕ × G)) := ultraweakOperatorTopology (ℕ × G)
  let : TopologicalSpace (GroupOperator G) := ultraweakOperatorTopology G
  let : TopologicalSpace (stabilization G) := stabilizationTopology G
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (FiniteCorner n p hp) := cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp)
  let : TopologicalSpace (Corner p hp) := cornerTopology (groupUltraweakTopology G) p hp
  exact (((matrixEntry_normal i.val j.val).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _

 theorem finiteCornerOfMatrix_normal (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    {X : Type u_6} [TopologicalSpace X] (f : X → Fin n → Fin n → Corner p hp)
    (hf : ∀ i j,@Continuous _ _ _ (cornerTopology (groupUltraweakTopology G) p hp) (fun x => f x i j)) :
    @Continuous _ _ _ (cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp))
      (fun x => finiteCornerOfMatrix n p hp (f x)) := by
  let : TopologicalSpace (GroupOperator (ℕ × G)) := ultraweakOperatorTopology (ℕ × G)
  let : TopologicalSpace (GroupOperator G) := ultraweakOperatorTopology G
  let : TopologicalSpace (stabilization G) := stabilizationTopology G
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (Corner p hp) := cornerTopology (groupUltraweakTopology G) p hp
  have hc : Continuous (fun x => finiteMatrix n (fun i j => ((f x i j).val : GroupOperator G))) := by
    apply HilbertUltraweak.finset_sum_continuous
    intro i _
    apply HilbertUltraweak.finset_sum_continuous
    intro j _
    exact (matrixBlock_normal i.val j.val).comp (continuous_subtype_val.comp (continuous_subtype_val.comp (hf i j)))
  exact (hc.subtype_mk _).subtype_mk _

 theorem finiteCornerIso_normal (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (q : groupVonNeumann H) (hq : IsStarProjection q) (e : Corner p hp ≃⋆ₐ[ℂ] Corner q hq)
    (he : @Continuous _ _ (cornerTopology (groupUltraweakTopology G) p hp)
      (cornerTopology (groupUltraweakTopology H) q hq) e) :
    @Continuous _ _ (cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp))
      (cornerTopology (stabilizationTopology H) (finiteProjection n q) (finiteProjection_projection n q hq))
      (finiteCornerIso n p hp q hq e) := by
  let : TopologicalSpace (FiniteCorner n p hp) := cornerTopology (stabilizationTopology G) (finiteProjection n p) (finiteProjection_projection n p hp)
  let : TopologicalSpace (Corner p hp) := cornerTopology (groupUltraweakTopology G) p hp
  let : TopologicalSpace (Corner q hq) := cornerTopology (groupUltraweakTopology H) q hq
  exact finiteCornerOfMatrix_normal n q hq _ (fun i j => he.comp (finiteCornerEntry_normal n p hp i j))

end FreeGroupFactorMain.Amplification

end

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_7}

 theorem productSingle_norm (i : ℕ) (ξ : GroupHilbert G) : ‖productSingle ℕ G i ξ‖=‖ξ‖ := by
  classical
  let : DecidableEq ℕ := Classical.decEq ℕ
  simp only [productSingle,ContinuousLinearMap.comp_apply,lp.singleContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [LinearIsometryEquiv.norm_map,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2)]

 theorem matrixBlock_productSingle (i j k : ℕ) (T : GroupOperator G) (ξ : GroupHilbert G) :
    matrixBlock i j T (productSingle ℕ G k ξ)=if j=k then productSingle ℕ G i (T ξ) else 0 := by
  simp only [matrixBlock,ContinuousLinearMap.comp_apply,productCoordinate_productSingle]
  split_ifs <;> simp

 theorem finiteDiagonal_productSingle (n : ℕ) (T : GroupOperator G) (k : ℕ) (ξ : GroupHilbert G) :
    finiteDiagonal n T (productSingle ℕ G k ξ)=if k<n then productSingle ℕ G k (T ξ) else 0 := by
  classical
  rw [finiteDiagonal_sum]
  simp only [sum_apply,matrixBlock_productSingle]
  by_cases hk : k<n
  · rw [ite_eq_left hk]
    let j : Fin n := ⟨k,hk⟩
    have he : ∀ i : Fin n,i.val=k ↔ i=j := fun i => (Fin.ext_iff (a := i) (b := j)).symm
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rfl
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right]
    intro hi
    exact hk (hi ▸ i.isLt)

variable [Group G]

 theorem finiteProjection_trace (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (a : ℝ) (_ha : 0≤a) (hpa : canonicalTrace p=(a:ℂ)) :
    stabilizedProjectionTrace (finiteProjection n p)=ENNReal.ofReal (n*a) := by
  classical
  have hv : ‖(p : GroupOperator G) (lp.single 2 (1:G) (1:ℂ))‖^2=a := by
    apply Complex.ofReal_injective
    have hh := canonicalTrace_star_mul p
    rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq,hpa] at hh
    simpa only [Complex.ofReal_pow] using hh.symm
  change (∑' k : ℕ,ENNReal.ofReal (‖finiteDiagonal n (p : GroupOperator G) (lp.single 2 (k,1) (1:ℂ))‖^2))=_
  have he (k : ℕ) : ENNReal.ofReal (‖finiteDiagonal n (p : GroupOperator G) (lp.single 2 (k,1) (1:ℂ))‖^2)=
      if k<n then ENNReal.ofReal a else 0 := by
    rw [←productSingle_single,finiteDiagonal_productSingle]
    split_ifs
    · rw [productSingle_norm,hv]
    · simp
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range n)]
  · have hh : (∑ k∈Finset.range n,if k<n then ENNReal.ofReal a else 0)=∑ _k∈Finset.range n,ENNReal.ofReal a :=
      Finset.sum_congr rfl (fun k hk => ite_eq_left (Finset.mem_range.mp hk))
    rw [hh]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast]
  · intro k hk
    rw [ite_eq_right (fun h => hk (Finset.mem_range.mpr h))]

 theorem stabilizedTrace_matrix (T : stabilization G) :
    stabilizedTrace T=∑' k : ℕ,canonicalTrace
      (⟨matrixEntry (T : GroupOperator (ℕ × G)) k k,(mem_stabilization_iff_matrix _).mp T.property k k⟩ : groupVonNeumann G) := by
  classical
  apply tsum_congr
  intro k
  rw [←productSingle_single,productSingle_inner_left,canonicalTrace_eq_inner]
  rfl

 theorem finiteCorner_trace (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) (x : FiniteCorner n p hp) :
    stabilizedTrace x.val=∑ i : Fin n,canonicalTrace (finiteCornerEntry n p hp x i i).val := by
  classical
  rw [stabilizedTrace_matrix]
  have he (k : ℕ) : canonicalTrace
      (⟨matrixEntry (x.val : GroupOperator (ℕ × G)) k k,(mem_stabilization_iff_matrix _).mp x.val.property k k⟩ : groupVonNeumann G)=
      if hk : k<n then canonicalTrace (finiteCornerEntry n p hp x ⟨k,hk⟩ ⟨k,hk⟩).val else 0 := by
    split_ifs with hk
    · rfl
    · have hz : matrixEntry (x.val : GroupOperator (ℕ × G)) k k=0 := by
        rw [←finiteCorner_reconstruct n p hp x]
        exact matrixEntry_finiteMatrix_out n _ k k (Or.inl (le_of_not_gt hk))
      have hs : (⟨matrixEntry (x.val : GroupOperator (ℕ × G)) k k,(mem_stabilization_iff_matrix _).mp x.val.property k k⟩ : groupVonNeumann G)=0 := Subtype.ext hz
      rw [hs]
      exact map_zero (canonicalTraceLinear (G := G))
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range n)]
  · rw [←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simp only [dite_eq_left k.isLt]
  · intro k hk
    simp only [dite_eq_right (fun h => hk (Finset.mem_range.mpr h))]

variable {H : Type u_8} [Group H]
 theorem finiteCornerIso_trace (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (q : groupVonNeumann H) (hq : IsStarProjection q) (e : Corner p hp ≃⋆ₐ[ℂ] Corner q hq)
    (c : ℂ) (hc : ∀ x,canonicalTrace (e x : groupVonNeumann H)=c*canonicalTrace (x : groupVonNeumann G))
    (x : FiniteCorner n p hp) :
    stabilizedTrace (finiteCornerIso n p hp q hq e x).val=c*stabilizedTrace x.val := by
  rw [finiteCorner_trace,finiteCorner_trace,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change canonicalTrace (finiteCornerEntry n q hq (finiteCornerOfMatrix n q hq _) i i).val=_
  rw [finiteCornerEntry_ofMatrix,hc]

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1} [Group G]

section Singles
variable [DecidableEq G]

end Singles

end

section
variable {G : Type u_2} [Group G]

end

variable {G : Type u_3} {H : Type u_4} [Group G] [Group H]

theorem finiteCornerIso_symm (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (q : groupVonNeumann H) (hq : IsStarProjection q) (e : Corner p hp ≃⋆ₐ[ℂ] Corner q hq) :
    (finiteCornerIso n p hp q hq e).symm=finiteCornerIso n q hq p hp e.symm := by
  ext x
  rfl

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

namespace NormalTracialEquiv
variable {τA : A → ℂ} {τB : B → ℂ} {τC : C → ℂ}
variable {𝒯A : TopologicalSpace A} {𝒯B : TopologicalSpace B} {𝒯C : TopologicalSpace C}

def trans (e : NormalTracialEquiv τA τB 𝒯A 𝒯B) (f : NormalTracialEquiv τB τC 𝒯B 𝒯C) :
    NormalTracialEquiv τA τC 𝒯A 𝒯C where
  equiv := e.equiv.trans f.equiv
  trace_eq x := (f.trace_eq (e.equiv x)).trans (e.trace_eq x)
  normal := by
    let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace C := 𝒯C
    exact f.normal.comp e.normal
  inverse_normal := by
    let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace C := 𝒯C
    exact e.inverse_normal.comp f.inverse_normal

end NormalTracialEquiv
end

open scoped ENNReal
variable {G : Type u_4} [Group G]

theorem scaling_ratio_trace (t : ℝ) (ht : 0<t) (n : ℕ) (_hn : 0<(n:ℝ))
    (q r : groupVonNeumann G) (hq : IsStarProjection q) (hr : IsStarProjection r)
    (f : groupVonNeumann G ≃⋆ₐ[ℂ] Corner q hq) (g : groupVonNeumann G ≃⋆ₐ[ℂ] Corner r hr)
    (hf : ∀ x,canonicalTrace (f x).val=((t/(n:ℝ):ℝ):ℂ)*canonicalTrace x)
    (hg : ∀ x,canonicalTrace (g x).val=((1/(n:ℝ):ℝ):ℂ)*canonicalTrace x)
    (x : Corner q hq) : canonicalTrace (g (f.symm x)).val=(t:ℂ)⁻¹*canonicalTrace x.val := by
  have hh := hf (f.symm x)
  rw [StarAlgEquiv.apply_symm_apply] at hh
  rw [hg,hh]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

 def finiteScaledIso (n : ℕ) (t : ℝ)
    (q r : groupVonNeumann G) (hq : IsStarProjection q) (hr : IsStarProjection r)
    (e : Corner q hq ≃⋆ₐ[ℂ] Corner r hr)
    (heτ : ∀x,canonicalTrace (e x).val=(t:ℂ)⁻¹*canonicalTrace x.val)
    (hen : @Continuous _ _ (cornerTopology (groupUltraweakTopology G) q hq)
      (cornerTopology (groupUltraweakTopology G) r hr) e)
    (hein : @Continuous _ _ (cornerTopology (groupUltraweakTopology G) r hr)
      (cornerTopology (groupUltraweakTopology G) q hq) e.symm) :
    NormalTracialEquiv (normalizedCornerTrace stabilizedTrace t (finiteProjection n q) (finiteProjection_projection n q hq))
      (normalizedCornerTrace stabilizedTrace 1 (finiteProjection n r) (finiteProjection_projection n r hr))
      (cornerTopology (stabilizationTopology G) (finiteProjection n q) (finiteProjection_projection n q hq))
      (cornerTopology (stabilizationTopology G) (finiteProjection n r) (finiteProjection_projection n r hr)) where
  equiv := finiteCornerIso n q hq r hr e
  trace_eq x := by
    simp only [normalizedCornerTrace,Complex.ofReal_one,inv_one,one_mul]
    exact finiteCornerIso_trace n q hq r hr e (t:ℂ)⁻¹ heτ x
  normal := finiteCornerIso_normal n q hq r hr e hen
  inverse_normal := by
    rw [finiteCornerIso_symm]
    exact finiteCornerIso_normal n r hr q hq e.symm hein

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_1} [Group G]

theorem finiteProjection_trace_div (n : ℕ) (hn : 0<(n:ℝ)) (t : ℝ) (ht : 0≤t)
    (p : groupVonNeumann G) (hp : IsStarProjection p) (hpτ : canonicalTrace p=((t/(n:ℝ):ℝ):ℂ)) :
    stabilizedProjectionTrace (finiteProjection n p)=ENNReal.ofReal t := by
  rw [finiteProjection_trace n p hp _ (div_nonneg ht hn.le) hpτ]
  congr 1
  field_simp

theorem preferred_scaling_model
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G,Commute T S) →
      ∃ c : ℂ,T=c • (1 : groupVonNeumann G))
    (hsmall : ∀t : ℝ,0<t → t≤1 → HasCornerScaling (canonicalTrace (G := G)) (groupUltraweakTopology G) t)
    (t : ℝ) (ht : 0<t) :
    ∃ (p : stabilization G) (hp : IsStarProjection p),
      stabilizedProjectionTrace p=ENNReal.ofReal t ∧ Nonempty (GroupCornerNormalIso t p hp) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max t 1)
  have hnt : t<(n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : 1<(n:ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hn0 : 0<(n:ℝ) := by linarith
  have ha : 0<t/(n:ℝ) := div_pos ht hn0
  have ha1 : t/(n:ℝ)≤1 := (div_le_one hn0).mpr hnt.le
  have hb : 0<1/(n:ℝ) := div_pos zero_lt_one hn0
  have hb1 : 1/(n:ℝ)≤1 := (div_le_one hn0).mpr hn1.le
  rcases hsmall (t/(n:ℝ)) ha ha1 with ⟨q,hq,f,hqτ,hfn,hfin,hfτ⟩
  rcases hsmall (1/(n:ℝ)) hb hb1 with ⟨r,hr,g,hrτ,hgn,hgin,hgτ⟩
  refine ⟨finiteProjection n q,finiteProjection_projection n q hq,
    finiteProjection_trace_div n hn0 t ht.le q hq hqτ,?_⟩
  have hrtr := finiteProjection_trace_div n hn0 1 zero_le_one r hr hrτ
  obtain ⟨D⟩ := preferred_unit_iso (G := G) hbase (finiteProjection n r)
    (finiteProjection_projection n r hr) hrtr
  let e : Corner q hq ≃⋆ₐ[ℂ] Corner r hr := f.symm.trans g
  have heτ (x : Corner q hq) : canonicalTrace (e x).val=(t:ℂ)⁻¹*canonicalTrace x.val :=
    scaling_ratio_trace t ht n hn0 q r hq hr f g hfτ hgτ x
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (Corner q hq) := cornerTopology (groupUltraweakTopology G) q hq
  let : TopologicalSpace (Corner r hr) := cornerTopology (groupUltraweakTopology G) r hr
  have hen : Continuous e := hgn.comp hfin
  have hein : Continuous e.symm := hfn.comp hgin
  exact ⟨(finiteScaledIso n t q r hq hr e heτ hen hein).trans D⟩

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain

end FreeGroupFactorMain
namespace FreeGroupFactorMain.Amplification
open scoped ENNReal

end FreeGroupFactorMain.Amplification

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.FreeGroupFactorMain.Amplification.preferred_scaling_model.{u_1} := @OAI.FreeGroupFactorMain.Amplification.preferred_scaling_model.{u_1}
