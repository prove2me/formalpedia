-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.Amplification.spatial_of_trace_iso
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:41:31.376188+00:00
-- url     : https://prove2.me/submissions/6666ae30-5f9b-443d-bae2-57da3ebd20e8

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

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

theorem deltaOne_eq {G : Type uG} [Group G] [DecidableEq G] :
    (deltaOne : GroupHilbert G) = lp.single 2 1 1 := by
  ext x
  simp [deltaOne, lp.single_apply, Pi.single_apply]

theorem groupVN_matrix {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (x y : G) :
    ((T : GroupOperator G) (lp.single 2 y 1)) x =
      ((T : GroupOperator G) deltaOne) (x * y⁻¹) := by
  have hr : rightRegular y⁻¹ deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, mul_inv_eq_one]
  rw [← hr]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne)
    (groupVN_commute_right T y⁻¹)
  simpa only [mul_apply_eq_comp, rightRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

theorem groupVN_star_coefficient {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (x : G) :
    ((star T : GroupOperator G) deltaOne) x =
      conj (((T : GroupOperator G) deltaOne) x⁻¹) := by
  calc
    ((star T : GroupOperator G) deltaOne) x =
        inner ℂ (lp.single 2 x (1 : ℂ)) ((star T : GroupOperator G) deltaOne) := by
      simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    _ = inner ℂ ((T : GroupOperator G) (lp.single 2 x 1)) deltaOne := by
      exact ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = conj (((T : GroupOperator G) (lp.single 2 x 1)) 1) := by
      simp only [deltaOne, lp.inner_single_right, RCLike.inner_apply, one_mul]
    _ = _ := by rw [groupVN_matrix]; simp

theorem canonicalTrace_star_mul_inner {G : Type uG} [Group G] [DecidableEq G]
    (T U : groupVonNeumann G) :
    canonicalTrace (star T * U) = inner ℂ
      ((T : GroupOperator G) deltaOne) ((U : GroupOperator G) deltaOne) := by
  classical
  rw [canonicalTrace_eq_inner, ← deltaOne_eq]
  change inner ℂ deltaOne (star (T : GroupOperator G) ((U : GroupOperator G) deltaOne)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem canonicalTrace_mul {G : Type uG} [Group G] [DecidableEq G]
    (T U : groupVonNeumann G) : canonicalTrace (T * U) = canonicalTrace (U * T) := by
  have he (T U : groupVonNeumann G) :
      canonicalTrace (T * U) = ∑' x : G,
        ((T : GroupOperator G) deltaOne) x⁻¹ * ((U : GroupOperator G) deltaOne) x := by
    rw [← star_star T, canonicalTrace_star_mul_inner]
    change (∑' x, inner ℂ (((star T : GroupOperator G) deltaOne) x)
      (((U : GroupOperator G) deltaOne) x)) = _
    apply tsum_congr
    intro x
    rw [groupVN_star_coefficient]
    simp [RCLike.inner_apply, mul_comm]
  rw [he, he]
  simpa only [Equiv.inv_apply, inv_inv, mul_comm] using
    ((Equiv.inv G).tsum_eq (fun x =>
      ((T : GroupOperator G) deltaOne) x⁻¹ * ((U : GroupOperator G) deltaOne) x)).symm

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

 theorem rightRegular_single {G : Type uG} [Group G] [DecidableEq G] (g y : G) :
    rightRegular g (lp.single 2 y (1 : ℂ)) = lp.single 2 (y * g⁻¹) 1 := by
  ext x
  simp only [rightRegular_apply, lp.single_apply, Pi.single_apply]
  congr 1
  exact propext (eq_mul_inv_iff_mul_eq.symm)

 theorem mem_groupVN_of_matrix_invariant {G : Type uG} [Group G] [DecidableEq G]
    (T : GroupOperator G)
    (hT : ∀ x y g : G, (T (lp.single 2 (y*g) 1)) (x*g) =
      (T (lp.single 2 y 1)) x) : T ∈ groupVonNeumann G := by
  rw [mem_groupVN_iff_commute_right]
  intro g
  apply operator_matrix_ext
  intro y
  ext x
  simp only [mul_apply_eq_comp, rightRegular_apply]
  change (T (lp.single 2 y 1)) (x*g) = (T (rightRegular g (lp.single 2 y 1))) x
  rw [rightRegular_single]
  simpa only [mul_inv_cancel_right] using (hT (x*g) y g⁻¹).symm

 theorem haar_orbit_orthonormal {G : Type uG} {H : Type uH} [Group G] [Group H] [DecidableEq G]
    (ρ : G →* groupVonNeumann H)
    (hstar : ∀ g, star (ρ g) = ρ g⁻¹)
    (htrace : ∀ g, canonicalTrace (ρ g) = if g = 1 then 1 else 0) :
    Orthonormal ℂ (fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne) := by
  classical
  rw [orthonormal_iff_ite]
  intro x y
  rw [← canonicalTrace_star_mul_inner, hstar, ← map_mul, htrace]
  simp only [inv_mul_eq_one]

 theorem spatial_of_haar_total {G : Type uG} {H : Type uH} [Group G] [Group H] [DecidableEq G]
    (ρ : G →* groupVonNeumann H)
    (hstar : ∀ g, star (ρ g) = ρ g⁻¹)
    (htrace : ∀ g, canonicalTrace (ρ g) = if g = 1 then 1 else 0)
    (htotal : ⊤ ≤ (Submodule.span ℂ (Set.range
      (fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne))).topologicalClosure) :
    ∃ e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H,
      e deltaOne = deltaOne ∧
      (∀ g, e.conjStarAlgEquiv (leftRegular g) = (ρ g : GroupOperator H)) ∧
      ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔
        e.conjStarAlgEquiv T ∈ groupVonNeumann H := by
  classical
  let v : G → GroupHilbert H := fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne
  have hon : Orthonormal ℂ v := haar_orbit_orthonormal ρ hstar htrace
  let e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H :=
    (hon.isHilbertSum htotal).linearIsometryEquiv.symm
  have he (g : G) : e (lp.single 2 g 1) = v g :=
    hon.linearIsometryEquiv_symm_apply_single_one htotal g
  have hδ : e deltaOne = deltaOne := by
    rw [deltaOne_eq, he]
    simp [v]
  have hleft (g : G) : e.conjStarAlgEquiv (leftRegular g) = (ρ g : GroupOperator H) := by
    apply e.conjStarAlgEquiv.symm.injective
    change e.conjStarAlgEquiv.symm (e.conjStarAlgEquiv (leftRegular g)) =
      e.conjStarAlgEquiv.symm (ρ g : GroupOperator H)
    rw [e.conjStarAlgEquiv.symm_apply_apply]
    apply operator_matrix_ext
    intro y
    apply e.injective
    change e (leftRegular g (lp.single 2 y 1)) =
      e (e.symm ((ρ g : GroupOperator H) (e (lp.single 2 y 1))))
    rw [e.apply_symm_apply, he]
    have hl : leftRegular g (lp.single 2 y (1 : ℂ)) = lp.single 2 (g*y) 1 := by
      ext x
      simp only [leftRegular_apply, lp.single_apply, Pi.single_apply]
      congr 1
      exact propext (inv_mul_eq_iff_eq_mul)
    rw [hl, he]
    change ((ρ (g*y) : groupVonNeumann H) : GroupOperator H) deltaOne = _
    rw [map_mul]
    rfl
  refine ⟨e, hδ, hleft, ?_⟩
  intro T
  constructor
  · intro hT
    rw [mem_groupVN_iff_commute_right]
    intro g
    apply e.conjStarAlgEquiv.symm.injective
    change e.conjStarAlgEquiv.symm (rightRegular g * e.conjStarAlgEquiv T) =
      e.conjStarAlgEquiv.symm (e.conjStarAlgEquiv T * rightRegular g)
    rw [map_mul, map_mul, e.conjStarAlgEquiv.symm_apply_apply]
    have hc : e.conjStarAlgEquiv.symm (rightRegular g) ∈
        StarSubalgebra.centralizer ℂ (leftTranslations G) := by
      rw [StarSubalgebra.mem_centralizer_iff, leftTranslations_eq_range]
      rintro _ ⟨x,rfl⟩
      constructor
      · apply e.conjStarAlgEquiv.injective
        change e.conjStarAlgEquiv (leftRegular _ * e.conjStarAlgEquiv.symm (rightRegular g)) =
          e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm (rightRegular g) * leftRegular _)
        rw [map_mul, map_mul, e.conjStarAlgEquiv.apply_symm_apply, hleft]
        exact (groupVN_commute_right (ρ x) g).symm
      · rw [leftRegular_star]
        apply e.conjStarAlgEquiv.injective
        change e.conjStarAlgEquiv (leftRegular _ * e.conjStarAlgEquiv.symm (rightRegular g)) =
          e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm (rightRegular g) * leftRegular _)
        rw [map_mul, map_mul, e.conjStarAlgEquiv.apply_symm_apply, hleft]
        exact (groupVN_commute_right (ρ x⁻¹) g).symm
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hc).1
  · intro hT
    let U : groupVonNeumann H := ⟨e.conjStarAlgEquiv T, hT⟩
    have hm (x y : G) : (T (lp.single 2 y 1)) x =
        canonicalTrace (star (ρ x) * U * ρ y) := by
      calc
        (T (lp.single 2 y 1)) x = inner ℂ (lp.single 2 x 1) (T (lp.single 2 y 1)) := by
          simp [lp.inner_single_left]
        _ = inner ℂ (v x) ((U : GroupOperator H) (v y)) := by
          rw [← he x, ← he y, ← e.inner_map_map]
          change inner ℂ (e (lp.single 2 x 1)) (e (T (lp.single 2 y 1))) =
            inner ℂ (e (lp.single 2 x 1)) (e (T (e.symm (e (lp.single 2 y 1)))))
          rw [e.symm_apply_apply]
        _ = canonicalTrace (star (ρ x) * U * ρ y) := by
          rw [mul_assoc, canonicalTrace_star_mul_inner]
          rfl
    apply mem_groupVN_of_matrix_invariant T
    intro x y g
    rw [hm, hm, map_mul, map_mul, star_mul]
    have hc := canonicalTrace_mul (star (ρ g) * star (ρ x) * U * ρ y) (ρ g)
    simp only [← mul_assoc]
    rw [hc]
    simp only [hstar, ← mul_assoc, ← map_mul, mul_inv_cancel, one_mul]

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uB uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

end
section

variable {A : Type uA} [CStarAlgebra A]

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} [Fintype ι] [DecidableEq ι]

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end

theorem twoNorm_sq {G : Type uG} [Group G] (T : groupVonNeumann G) :
    (twoNorm T : ℂ)^2 = canonicalTrace (star T*T) := by
  classical
  rw [canonicalTrace_star_mul, ← deltaOne_eq]
  rfl

theorem twoNorm_iso {G : Type uG} {H : Type uH} [Group G] [Group H]
    (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (hΦ : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) (T : groupVonNeumann G) :
    twoNorm (Φ T) = twoNorm T := by
  have hs : Φ (star T) = star (Φ T) := Φ.map_star' T
  have hm : Φ (star T * T) = Φ (star T) * Φ T := Φ.map_mul' (star T) T
  have hsq : (twoNorm (Φ T) : ℂ)^2 = (twoNorm T : ℂ)^2 := by
    rw [twoNorm_sq, twoNorm_sq, ← hs, ← hm, hΦ]
  have hr := congrArg Complex.re hsq
  norm_cast at hr
  nlinarith [norm_nonneg (groupL2 (Φ T)), norm_nonneg (groupL2 T)]

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
open scoped ENNReal

variable {G : Type uG} [Group G]

omit [Group G] in
theorem group_single_total [DecidableEq G] (K : Submodule ℂ (GroupHilbert G))
    (hK : IsClosed (K : Set (GroupHilbert G)))
    (hsingle : ∀ g : G, lp.single 2 g (1 : ℂ) ∈ K) : ⊤ ≤ K := by
  classical
  intro ξ _hξ
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro g _hg
  have he : lp.single 2 g (ξ g) = (ξ g) • (lp.single 2 g (1 : ℂ) : GroupHilbert G) := by
    ext x
    simp [lp.single_apply, Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hsingle g)

variable {ι : Type uι}

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace FreeGroupFactorMain.Amplification

section

variable {G : Type u_1} {H : Type u_2} [Group G] [Group H]

def groupPolynomial (p : G →₀ ℂ) : groupVonNeumann G :=
  p.sum (fun g z => z • groupUnitary g)

theorem groupPolynomial_dense (ξ : GroupHilbert G) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G →₀ ℂ, ‖groupL2 (groupPolynomial p)-ξ‖ < ε := by
  classical
  let K := Submodule.span ℂ (Set.range (fun g : G => groupL2 (groupUnitary g)))
  have ht : ⊤ ≤ K.topologicalClosure := by
    apply group_single_total _ (Submodule.isClosed_topologicalClosure _)
    intro g
    rw [← groupL2_groupUnitary g]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g,rfl⟩)
  have hx : ξ ∈ closure (K : Set (GroupHilbert G)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact ht trivial
  obtain ⟨x,hx,hd⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨p,hp⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨p,?_⟩
  have he : groupL2 (groupPolynomial p) = x := by
    rw [groupPolynomial,Finsupp.sum]
    simp only [map_sum,map_smul]
    exact hp
  rw [he,← dist_eq_norm,dist_comm]
  exact hd

theorem trace_iso_orbit_total (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun g : G => groupL2 (Φ (groupUnitary g))))).topologicalClosure := by
  classical
  let K := Submodule.span ℂ (Set.range (fun g : G => groupL2 (Φ (groupUnitary g))))
  apply group_single_total _ (Submodule.isClosed_topologicalClosure _)
  intro h
  change lp.single 2 h (1 : ℂ) ∈ K.topologicalClosure
  change lp.single 2 h (1 : ℂ) ∈ closure (K : Set (GroupHilbert H))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨p,hp⟩ := groupPolynomial_dense (groupL2 (Φ.symm (groupUnitary h))) hε
  refine ⟨groupL2 (Φ (groupPolynomial p)),?_,?_⟩
  · change groupL2 (Φ (groupPolynomial p)) ∈ K
    rw [groupPolynomial,Finsupp.sum]
    simp only [map_sum,map_smul]
    exact Submodule.sum_mem K (fun g _ => Submodule.smul_mem K _
      (Submodule.subset_span ⟨g,rfl⟩))
  · rw [dist_comm,dist_eq_norm,← groupL2_groupUnitary h,← map_sub]
    change twoNorm (Φ (groupPolynomial p)-groupUnitary h) < ε
    rw [← Φ.apply_symm_apply (groupUnitary h),← map_sub,twoNorm_iso Φ ht]
    change ‖groupL2 (groupPolynomial p-Φ.symm (groupUnitary h))‖ < ε
    rw [map_sub]
    exact hp

theorem spatial_of_trace_iso (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) :
    ∃ e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H,
      e deltaOne = deltaOne ∧
      ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔
        e.conjStarAlgEquiv T ∈ groupVonNeumann H := by
  classical
  let ρ : G →* groupVonNeumann H := Φ.toMonoidHom.comp
    ((unitary (groupVonNeumann G)).subtype.comp (groupUnitaryUHom G))
  have hρ (g : G) : ρ g = Φ (groupUnitary g) := rfl
  obtain ⟨e,he,_hgen,hmem⟩ := spatial_of_haar_total ρ (fun g => by
    change star (Φ (groupUnitary g)) = Φ (groupUnitary g⁻¹)
    exact (Φ.map_star' (groupUnitary g)).symm.trans
      (congrArg Φ (groupUnitary_inv g).symm)) (fun g => by
    rw [hρ,ht,canonicalTrace_groupUnitary]) (trace_iso_orbit_total Φ ht)
  exact ⟨e,he,hmem⟩

end

open scoped ENNReal
variable {I : Type u_3} {G : Type u_4} {H : Type u_5}

variable [Group G] [Group H]

end FreeGroupFactorMain.Amplification

end

end OAI
end

theorem solution.{u_1,u_2} : type_of% @OAI.FreeGroupFactorMain.Amplification.spatial_of_trace_iso.{u_1,u_2} := @OAI.FreeGroupFactorMain.Amplification.spatial_of_trace_iso.{u_1,u_2}
