-- Prove2me | solution 1 for OAI.ContinuousCircleWeight.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T22:14:02.539673+00:00
-- url     : https://prove2.me/submissions/4e5326ec-ea70-4731-b690-7254e11497a0

import Mathlib
import Definitions.Def_ContinuousCircleWeight
import Definitions.Def_OAIQ2Rw002
import Theorems.Thm_OAI_CircleSampling_model_no_strict_projection
import Theorems.Thm_OAI_ContinuousCircleWeight_borel_weight_transport

section
-- module Solutions.OAIQ2_Rot.Compat
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Regular
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
namespace ContinuousCircleWeight

theorem regular_relation (u : unitary ℂ) :
    (regularV u : RegularOperator) * (regularU : RegularOperator) =
      (u : ℂ) • ((regularU : RegularOperator) * (regularV u : RegularOperator)) := by
  ext f ⟨a,b⟩
  change (regularV u : RegularOperator) ((regularU : RegularOperator) f) (a,b) =
    (u : ℂ) * ((regularU : RegularOperator) ((regularV u : RegularOperator) f) (a,b))
  simp only [regularV_apply, regularU_apply, ← mul_assoc]
  congr 1
  change (↑(u ^ a) : ℂ) = ↑(u * u ^ (a-1))
  congr 1
  calc u ^ a = u ^ (1 + (a-1)) := by congr 1; omega
    _ = u * u ^ (a-1) := by rw [zpow_add, zpow_one]

theorem regular_monomial (u : unitary ℂ) (m n : ℤ) :
    ((regularU ^ m * regularV u ^ n : unitary RegularOperator) : RegularOperator) regularVacuum =
      lp.single 2 (m,n) 1 := by
  ext ⟨a,b⟩
  change ((regularU ^ m : unitary RegularOperator) : RegularOperator)
    (((regularV u ^ n : unitary RegularOperator) : RegularOperator) regularVacuum) (a,b) = _
  simp only [regularU_zpow_apply, regularV_zpow_apply, regularVacuum, lp.single_apply]
  by_cases ha : a=m
  · subst a
    by_cases hb : b=n
    · subst b; simp
    · simp [hb, sub_eq_zero, Prod.mk.injEq]
  · have ham : a-m ≠ 0 := sub_ne_zero.mpr ha
    simp [ham, Prod.mk.injEq, Ne.symm ha]

theorem regular_moments (u : unitary ℂ) (m n : ℤ) :
    inner ℂ regularVacuum
      (((regularU ^ m * regularV u ^ n : unitary RegularOperator) : RegularOperator) regularVacuum) =
      if m=0 ∧ n=0 then 1 else 0 := by
  rw [regular_monomial, regularVacuum, lp.inner_single_left]
  simp [lp.single_apply, Pi.single_apply, Prod.mk.injEq, eq_comm]

theorem regular_cyclic (u : unitary ℂ) :
    (Submodule.span ℂ (Set.range (fun mn : ℤ × ℤ =>
      ((regularU ^ mn.1 * regularV u ^ mn.2 : unitary RegularOperator) : RegularOperator)
        regularVacuum))).topologicalClosure = ⊤ := by
  simp_rw [regular_monomial]
  have heq : (fun mn : ℤ × ℤ => lp.single 2 (mn.1,mn.2) (1 : ℂ)) =
      (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ RegularHilbert) : ℤ × ℤ → RegularHilbert) := by
    funext mn
    rw [← (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ RegularHilbert)).repr_symm_single mn]
    ext i
    simp [LinearIsometryEquiv.symm, LinearIsometryEquiv.refl, lp.single_apply]
  rw [heq]
  exact (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ RegularHilbert)).dense_span

end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TensorBasis
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uE uι uκ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators

open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma fieldMulL2_norm_le (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (hC0 : 0 ≤ C) :
    ‖fieldMulL2 μ T hT C hC‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC0
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fieldMulL2_coe μ T hT C hC f,hC] with x hx hc
  rw [hx]
  exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FiberActions
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable _root_.OAI.ContinuousCircleWeight.instCoeFunRealBorelForallCircleXReal _root_.OAI.ContinuousCircleWeight.realCutoffRange_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section

lemma circleFiberBasis_coe (a b : ℤ) :
    circleFiberBasis (a,b) =ᵐ[AddCircle.haarAddCircle] fun x ↦
      fourier b x • lp.single 2 a 1 := by
  simp only [circleFiberBasis,tensorL2Basis_apply]
  filter_upwards [pureL2_coe (AddCircle.haarAddCircle (T := (1:ℝ))) (fourierBasis b) (fiberBasis a),
    coeFn_fourierLp (T := (1:ℝ)) 2 b] with x h1 h2
  simpa only [coe_fourierBasis,h2,fiberBasis_apply] using h1

lemma continuousPi_norm_le (θ : CircleX) (g : C(CircleX,ℂ)) :
    ‖continuousPi θ g‖ ≤ ‖g‖ :=
  fieldMulL2_norm_le _ _ _ _ _ (norm_nonneg _)

lemma continuous_continuousPiHom (θ : CircleX) : Continuous (continuousPiHom θ) := by
  exact (LinearMap.mkContinuous (continuousPiHom θ).toLinearMap 1
    (by
      intro g
      change ‖continuousPi θ g‖ ≤ 1 * ‖g‖
      simpa only [one_mul] using continuousPi_norm_le θ g)).continuous

end


lemma fiberShiftL2_coe (n : ℤ) (f : CircleFiberL2) :
    fiberShiftL2 n f =ᵐ[AddCircle.haarAddCircle] fun x ↦ fiberShift n (f x) :=
  (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f

lemma fiberShift_single (n a : ℤ) (c : ℂ) :
    fiberShift n (lp.single 2 a c) = lp.single 2 (n+a) c := by
  ext k
  simp only [fiberShift_apply,lp.single_apply,Pi.single_apply]
  have he : k-n=a ↔ k=n+a := by omega
  simp only [he]

lemma fiberShiftL2_basis (n a b : ℤ) :
    fiberShiftL2 n (circleFiberBasis (a,b)) = circleFiberBasis (n+a,b) := by
  apply Lp.ext
  filter_upwards [fiberShiftL2_coe n (circleFiberBasis (a,b)),
    circleFiberBasis_coe a b,circleFiberBasis_coe (n+a) b] with x h1 h2 h3
  rw [h1,h2,h3,map_smul,fiberShift_single]

lemma circleFiberBasis_ext {A B : CircleFiberOperator}
    (h : ∀ a b, A (circleFiberBasis (a,b)) = B (circleFiberBasis (a,b))) : A=B := by
  have he : A.comp circleFiberBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      B.comp circleFiberBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro k
    apply ContinuousLinearMap.ext
    intro c
    change A (circleFiberBasis.repr.symm (lp.single 2 k c)) =
      B (circleFiberBasis.repr.symm (lp.single 2 k c))
    have hc : lp.single (E := fun _ : ℤ×ℤ ↦ ℂ) 2 k c = c•lp.single 2 k 1 := by
      simpa using lp.single_smul (E := fun _ : ℤ×ℤ ↦ ℂ) 2 k c 1
    rw [hc,map_smul,map_smul,map_smul,HilbertBasis.repr_symm_single,h k.1 k.2]
  apply ContinuousLinearMap.ext
  intro f
  simpa only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.symm_apply_apply] using
    DFunLike.congr_fun he (circleFiberBasis.repr f)

lemma regularShift_single (n a b : ℤ) (c : ℂ) :
    regularShift n (lp.single 2 (a,b) c) = lp.single 2 (n+a,b) c := by
  ext ⟨k,l⟩
  simp only [regularShift_apply,lp.single_apply,Pi.single_apply,Prod.mk.injEq]
  have he : k-n=a ∧ l=b ↔ k=n+a ∧ l=b := by omega
  simp only [he]

lemma circleFiberBasis_conj_U :
    circleFiberBasis.repr.symm.conjStarAlgEquiv (regularU : RegularOperator) = fiberShiftL2 1 := by
  apply circleFiberBasis_ext
  intro a b
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_symm,
    HilbertBasis.repr_self]
  change circleFiberBasis.repr.symm (regularShift 1 (lp.single 2 (a,b) 1)) = _
  rw [regularShift_single,HilbertBasis.repr_symm_single,fiberShiftL2_basis]

lemma continuousPi_basis (θ : CircleX) (a b : ℤ) :
    continuousPi θ (fourier 1) (circleFiberBasis (a,b)) =
      (fourier 1 (a•θ)) • circleFiberBasis (a,b+1) := by
  apply Lp.ext
  filter_upwards [continuousPi_coe θ (fourier 1) (circleFiberBasis (a,b)),
    circleFiberBasis_coe a b,circleFiberBasis_coe a (b+1),
    Lp.coeFn_smul (fourier 1 (a•θ)) (circleFiberBasis (a,b+1))] with x h1 h2 h3 h4
  rw [h1,h2,h4]
  simp only [Pi.smul_apply,h3]
  ext k
  simp only [continuousPiField_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases hk : k=a
  · subst k
    simp only [lp.single_apply,Pi.single_eq_same,mul_one]
    rw [fourier_add]
    simp only [fourier_one, AddCircle.toCircle_add,Circle.coe_mul]
    ring
  · simp [lp.single_apply,Pi.single_eq_of_ne hk]

lemma regularMagnetic_single (u : unitary ℂ) (a b : ℤ) (c : ℂ) :
    regularMagnetic u 1 (lp.single 2 (a,b) c) =
      ((u^a : unitary ℂ) : ℂ) • lp.single 2 (a,b+1) c := by
  ext ⟨k,l⟩
  simp only [regularMagnetic_apply,one_mul,lp.coeFn_smul,Pi.smul_apply,
    lp.single_apply,Pi.single_apply,Prod.mk.injEq]
  have he : k=a ∧ l-1=b ↔ k=a ∧ l=b+1 := by omega
  simp only [he]
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩; rfl
  · simp

lemma fourier_one_real (θ : ℝ) : fourier 1 (θ : CircleX) = (rotationScalar θ : ℂ) := by
  simp only [fourier_one,AddCircle.toCircle_apply_mk,Circle.coe_exp,div_one]
  simp only [rotationScalar,Complex.ofReal_mul,Complex.ofReal_ofNat]

lemma fourier_one_zsmul_real (θ : ℝ) (a : ℤ) :
    fourier 1 (a • (θ : CircleX)) = ((rotationScalar θ)^a : unitary ℂ) := by
  rw [fourier_one, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  rw [← fourier_one, fourier_one_real, Unitary.coe_zpow]

lemma circleFiberBasis_conj_V (θ : ℝ) :
    circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator) =
      continuousPi (θ : CircleX) (fourier 1) := by
  apply circleFiberBasis_ext
  intro a b
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_symm,
    HilbertBasis.repr_self]
  change circleFiberBasis.repr.symm (regularMagnetic (rotationScalar θ) 1
    (lp.single 2 (a,b) 1)) = _
  rw [regularMagnetic_single,map_smul,HilbertBasis.repr_symm_single,continuousPi_basis,
    fourier_one_zsmul_real]



end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FunctionalCalculus
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable _root_.OAI.ContinuousCircleWeight.instCoeFunRealBorelForallCircleXReal _root_.OAI.ContinuousCircleWeight.realCutoffRange_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uι uE uA

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section
open Set Metric

lemma circleFunction_circle (f : C(CircleX,ℝ)) (z : Circle) :
    circleFunction f z = (f (circleIdentification.symm z) : ℂ) := by
  simp only [circleFunction,Circle.norm_coe,dite_eq_left]
  congr 2

lemma circleFunction_fourier_one (f : C(CircleX,ℝ)) (x : CircleX) :
    circleFunction f (fourier 1 x) = (f x : ℂ) := by
  rw [fourier_one,circleFunction_circle]
  have he : (AddCircle.toCircle x) = circleIdentification x := by
    exact (AddCircle.homeomorphCircle_apply _ _).symm
  rw [he,Homeomorph.symm_apply_apply]

lemma circleFunction_continuousOn (f : C(CircleX,ℝ)) :
    ContinuousOn (circleFunction f) (sphere (0:ℂ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun z : Circle ↦ circleFunction f z)
  simp_rw [circleFunction_circle]
  exact Complex.continuous_ofReal.comp (f.continuous.comp circleIdentification.symm.continuous)

lemma circleFunction_continuousOn_spectrum (f : C(CircleX,ℝ)) :
    ContinuousOn (circleFunction f) (spectrum ℂ (fourier (T := (1:ℝ)) 1)) := by
  apply (circleFunction_continuousOn f).mono
  rw [ContinuousMap.spectrum_eq_range]
  rintro z ⟨x,rfl⟩
  rw [fourier_one]
  exact (AddCircle.toCircle x).property

lemma circle_cfc (f : C(CircleX,ℝ)) :
    cfc (circleFunction f) (fourier (T := (1:ℝ)) 1) = complexCircleMap f := by
  ext x
  have he := (ContinuousMap.evalStarAlgHom ℂ ℂ x).map_cfc (circleFunction f)
    (fourier (T := (1:ℝ)) 1) (circleFunction_continuousOn_spectrum f)
  change cfc (circleFunction f) (fourier (T := (1:ℝ)) 1) x = (f x : ℂ)
  change (cfc (circleFunction f) (fourier (T := (1:ℝ)) 1)) x = cfc (circleFunction f) (fourier 1 x) at he
  rw [he]
  have hz : cfc (circleFunction f) (fourier 1 x) = circleFunction f (fourier 1 x) := by
    simpa only [Algebra.algebraMap_self_apply] using
      (cfc_algebraMap (A := ℂ) (fourier 1 x) (circleFunction f))
  exact hz.trans (circleFunction_fourier_one f x)

variable {A : Type uA} [CStarAlgebra A]
lemma circle_cfc_hom (φ : C(CircleX,ℂ) →⋆ₐ[ℂ] A) (hφ : Continuous φ)
    (f : C(CircleX,ℝ)) :
    φ (complexCircleMap f) = cfc (circleFunction f) (φ (fourier 1)) := by
  have hn : IsStarNormal (φ (fourier 1)) := by
    constructor
    change star (φ _) * φ _ = φ _ * star (φ _)
    rw [← map_star,← map_mul,← map_mul,mul_comm]
  rw [← circle_cfc f]
  exact φ.map_cfc _ _ (circleFunction_continuousOn_spectrum f) hφ
end

open Set Filter
open scoped Topology

lemma boundedPi_eq_continuousPi (θ : CircleX) (g : C(CircleX,ℂ)) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) :
    boundedPi θ g g.continuous.measurable C hg=continuousPi θ g := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [boundedPi_coe θ g g.continuous.measurable C hg u,continuousPi_coe θ g u] with x h1 h2
  rw [h1,h2]
  ext k
  rfl


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_BorelWeights
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

namespace ContinuousCircleWeight

section
open Set Filter
open scoped Topology

lemma realPi_continuous (θ : CircleX) (g : C(CircleX,ℝ)) :
    realPi θ (RealBorel.ofContinuous g)=continuousPi θ (complexCircleMap g) := by
  apply (boundedPi_congr θ _ (complexCircleMap g) _ _ _ _ _ _ (Eventually.of_forall (fun _ => rfl))).trans
  exact boundedPi_eq_continuousPi θ (complexCircleMap g) (RealBorel.ofContinuous g).bound (fun x => by simpa [complexCircleMap,RealBorel.ofContinuous] using (RealBorel.ofContinuous g).norm_le x)
end

open Set Filter
open scoped Topology

end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TracialAction
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uA

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open Set

lemma fiberConjugacy_U : fiberConjugacy (regularU : RegularOperator)=fiberShiftL2 1 := circleFiberBasis_conj_U
lemma fiberConjugacy_V (θ : ℝ) : fiberConjugacy (regularV (rotationScalar θ) : RegularOperator)=continuousPi (θ:CircleX) (fourier 1) := circleFiberBasis_conj_V θ

lemma commute_star_unitary {A : Type uA} [Monoid A] [StarMul A] (u : unitary A) (b : A)
    (h : Commute (u:A) b) : Commute (star (u:A)) b := by
  change star (u:A)*b=b*star (u:A)
  calc
    star (u:A)*b = star (u:A)*(b*(u:A))*star (u:A) := by simp [mul_assoc]
    _ = star (u:A)*((u:A)*b)*star (u:A) := by rw [h.eq]
    _ = b*star (u:A) := by simp [←mul_assoc]

lemma mem_regularCommutant (θ : ℝ) {B : RegularOperator}
    (hB : B∈Set.centralizer ({(regularU:RegularOperator),(regularV (rotationScalar θ):RegularOperator)} : Set RegularOperator)) :
    B∈regularCommutant θ := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro a ha
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
  rcases ha with rfl|rfl
  · exact ⟨hB _ (by simp), (commute_star_unitary regularU B (hB _ (by simp))).eq⟩
  · exact ⟨hB _ (by simp), (commute_star_unitary (regularV (rotationScalar θ)) B (hB _ (by simp))).eq⟩

lemma regularAlgebra_of_commutes (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) :
    fiberConjugacy.symm A∈regularAlgebra (rotationScalar θ) := by
  intro B hB
  have hh : Commute A (fiberConjugacy B) := hA _ ⟨B,mem_regularCommutant θ hB,rfl⟩
  apply fiberConjugacy.injective
  change fiberConjugacy (B*fiberConjugacy.symm A)=fiberConjugacy (fiberConjugacy.symm A*B)
  simpa only [map_mul,fiberConjugacy.apply_symm_apply] using hh.symm.eq

lemma fiber_commutes_of_regularAlgebra (θ : ℝ) (p : RegularOperator)
    (hp : p∈regularAlgebra (rotationScalar θ)) :
    ∀ B∈fiberCommutant θ,Commute (fiberConjugacy p) B := by
  rintro B ⟨b,hb,rfl⟩
  have hb' : b∈Set.centralizer ({(regularU:RegularOperator),(regularV (rotationScalar θ):RegularOperator)} : Set RegularOperator) :=
    fun a ha => ((StarSubalgebra.mem_centralizer_iff ℂ).mp hb a ha).1
  change fiberConjugacy p*fiberConjugacy b=fiberConjugacy b*fiberConjugacy p
  simpa only [map_mul] using congrArg fiberConjugacy (hp b hb').symm


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FieldExtraction
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma indicatorV2_coe (s : Set X) (hs : MeasurableSet s) (f : VectorL2 (E := E) μ) :
    indicatorV2 μ s hs f =ᵐ[μ] s.indicator f :=
  ((Lp.memLp f).indicator hs).coeFn_toLp

lemma vectorL2_norm_sq_integral (f : VectorL2 (E := E) μ) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq]

lemma indicatorV2_norm_sq (s : Set X) (hs : MeasurableSet s) (f : VectorL2 (E := E) μ) :
    ‖indicatorV2 μ s hs f‖^2 = ∫ x in s, ‖f x‖^2 ∂μ := by
  rw [vectorL2_norm_sq_integral, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorV2_coe μ s hs f] with x hx
  rw [hx]
  by_cases hxs : x∈s <;> simp [hxs]

variable [IsFiniteMeasure μ]

lemma commutes_indicator_pointwise_bound (A : VectorL2 (E := E) μ →L[ℂ] VectorL2 (E := E) μ)
    (hA : ∀ s (hs : MeasurableSet s), A.comp (indicatorV2 μ s hs) =
      (indicatorV2 μ s hs).comp A) (v : E) :
    ∀ᵐ x ∂μ, ‖(A (Lp.const 2 μ v)) x‖ ≤ ‖A‖*‖v‖ := by
  have hi : Integrable (fun x ↦ ‖(A (Lp.const 2 μ v)) x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have he : ∀ᵐ x ∂μ, ‖(A (Lp.const 2 μ v)) x‖^2 ≤ (‖A‖*‖v‖)^2 := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const _)
    intro s hs _
    rw [← indicatorV2_norm_sq μ s hs]
    have hc : indicatorV2 μ s hs (A (Lp.const 2 μ v)) =
        A (indicatorV2 μ s hs (Lp.const 2 μ v)) :=
      (congrArg (fun B : VectorL2 (E := E) μ →L[ℂ] VectorL2 (E := E) μ ↦ B (Lp.const 2 μ v)) (hA s hs)).symm
    rw [hc]
    calc
      _ ≤ (‖A‖ * ‖indicatorV2 μ s hs (Lp.const 2 μ v)‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) _
      _ = ‖A‖^2 * ∫ x in s, ‖(Lp.const 2 μ v) x‖^2 ∂μ := by
        rw [mul_pow, indicatorV2_norm_sq]
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (Lp.coeFn_const 2 μ v)] with x hx
        rw [hx]
        simp only [Function.const_apply, mul_pow]
  filter_upwards [he] with x hx
  nlinarith [norm_nonneg ((A (Lp.const 2 μ v)) x), mul_nonneg (norm_nonneg A) (norm_nonneg v)]

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] OAI.ContinuousCircleWeight.rationalNormedSpace
lemma complexOfRat_norm_le (T : E →L[ℚ] E) (hI : ∀ v, T (Complex.I • v) = Complex.I • T v) :
    ‖complexOfRat T hI‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact T.le_opNorm

lemma rationalCore_I (v : ℕ → E) (u : rationalCore v) :
    Complex.I • (u : E) ∈ rationalCore v := by
  apply Submodule.span_induction (p := fun x _ ↦ Complex.I • x ∈ rationalCore v)
    _ _ _ _ u.property
  · intro x hx
    rcases hx with ⟨n,rfl⟩ | ⟨n,rfl⟩
    · exact Submodule.subset_span (Or.inr ⟨n,rfl⟩)
    · rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
      exact (rationalCore v).neg_mem (Submodule.subset_span (Or.inl ⟨n,rfl⟩))
  · simp only [smul_zero, Submodule.zero_mem]
  · intro x y _ _ hx hy
    simpa only [smul_add] using (rationalCore v).add_mem hx hy
  · intro a x _ hx
    rw [smul_comm]
    exact (rationalCore v).smul_mem a hx

lemma rationalCore_dense (v : ℕ → E) (hv : DenseRange v) :
    DenseRange (rationalCore v).subtypeL := by
  intro x
  apply closure_mono (s := range v) _ (hv x)
  rintro _ ⟨n,rfl⟩
  exact ⟨⟨v n, Submodule.subset_span (Or.inl ⟨n,rfl⟩)⟩,rfl⟩

variable {X : Type uX} [MeasurableSpace X] (μ : Measure X)
  [CompleteSpace E] [IsFiniteMeasure μ]

attribute [local instance] OAI.ContinuousCircleWeight.rationalTower
theorem extract_bounded_field (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hb : ∀ v : E, ∀ᵐ x ∂μ, ‖(A (Lp.const 2 μ v)) x‖ ≤ ‖A‖ * ‖v‖)
    (v : ℕ → E) (hv : DenseRange v) :
    ∃ T : X → (E →L[ℂ] E), (∀ x, ‖T x‖ ≤ ‖A‖) ∧
      (∀ u : E, ∀ᵐ x ∂μ, T x u = (A (Lp.const 2 μ u)) x) := by
  classical
  let D := rationalCore v
  let G : E →L[ℂ] Lp E 2 μ := A.comp (Lp.constL 2 μ ℂ)
  have hG (u : E) : G u = A (Lp.const 2 μ u) := rfl
  have hgadd (u w : E) : (G (u+w) : X → E) =ᵐ[μ] fun x ↦ G u x + G w x := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  have hgsmul (a : ℂ) (u : E) : (G (a•u) : X → E) =ᵐ[μ] fun x ↦ a • G u x := by
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  have hgqsmul (a : ℚ) (u : E) : (G (a•u) : X → E) =ᵐ[μ] fun x ↦ a • G u x := by
    simpa only [Rat.cast_smul_eq_qsmul] using hgsmul (a : ℂ) u
  let Good : X → Prop := fun x ↦
    (∀ u w : D, G ((u:E)+(w:E)) x = G u x + G w x) ∧
    (∀ a : ℚ, ∀ u : D, G (a • (u:E)) x = a • G u x) ∧
    (∀ u : D, ‖G u x‖ ≤ ‖A‖ * ‖(u:E)‖) ∧
    (∀ u : D, G (Complex.I • (u:E)) x = Complex.I • G u x)
  have hGood : ∀ᵐ x ∂μ, Good x := by
    have h1 := ae_all_iff.mpr (fun u : D ↦ ae_all_iff.mpr (fun w : D ↦ hgadd u w))
    have h2 := ae_all_iff.mpr (fun a : ℚ ↦ ae_all_iff.mpr (fun u : D ↦ hgqsmul a u))
    have h3 := ae_all_iff.mpr (fun u : D ↦ hb (u:E))
    have h4 := ae_all_iff.mpr (fun u : D ↦ hgsmul Complex.I u)
    filter_upwards [h1,h2,h3,h4] with x h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4⟩
  let TD : X → (D →L[ℚ] E) := fun x ↦ if hx : Good x then
    LinearMap.mkContinuous
      { toFun := fun u ↦ G (u:E) x
        map_add' := fun u w ↦ hx.1 u w
        map_smul' := fun a u ↦ hx.2.1 a u }
      ‖A‖ hx.2.2.1
    else 0
  let R : X → (E →L[ℚ] E) := fun x ↦ (TD x).extend D.subtypeL
  have hd : DenseRange D.subtypeL := rationalCore_dense v hv
  have hu : IsUniformInducing D.subtypeL := isometry_subtype_coe.isUniformInducing
  have hTDnorm (x : X) : ‖TD x‖ ≤ ‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    dsimp only [TD]
    split_ifs with hx
    · exact hx.2.2.1 u
    · simp only [zero_apply, norm_zero]
      positivity
  have hRnorm (x : X) : ‖R x‖ ≤ ‖A‖ := by
    have h := ContinuousLinearMap.opNorm_extend_le (TD x) (N := 1) hd
      (fun u : D ↦ by simp)
    have h' : ‖R x‖ ≤ ‖TD x‖ := by simpa only [NNReal.coe_one, one_mul] using h
    exact h'.trans (hTDnorm x)
  have hReq (x : X) (hx : Good x) (u : D) : R x (u:E) = G u x := by
    change (TD x).extend D.subtypeL (D.subtypeL u) = _
    rw [ContinuousLinearMap.extend_eq _ hd hu]
    simp only [TD, dite_eq_left hx]
    rfl
  have hRI (x : X) (u : E) : R x (Complex.I • u) = Complex.I • R x u := by
    refine hd.induction_on u ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro w
      by_cases hx : Good x
      · rw [show D.subtypeL w = (w:E) from rfl]
        let iw : D := ⟨Complex.I • (w:E), rationalCore_I v w⟩
        rw [show Complex.I • (w:E) = (iw:E) from rfl, hReq x hx iw, hReq x hx w]
        exact hx.2.2.2 w
      · have hz : TD x = 0 := by simp only [TD, dite_eq_right hx]
        simp only [R, hz, ContinuousLinearMap.extend_zero hd hu,
          zero_apply, smul_zero]
  let T : X → (E →L[ℂ] E) := fun x ↦ complexOfRat (R x) (hRI x)
  refine ⟨T, fun x ↦ (complexOfRat_norm_le _ _).trans (hRnorm x), ?_⟩
  intro u
  have hdelta (w : D) : ∀ᵐ x ∂μ, ‖G w x - G u x‖ ≤ ‖A‖ * ‖(w:E)-u‖ := by
    have he : (G ((w:E)-u) : X → E) =ᵐ[μ] fun x ↦ G w x - G u x := by
      rw [map_sub]
      exact Lp.coeFn_sub _ _
    filter_upwards [he, hb ((w:E)-u)] with x hx hb
    rw [← hx]
    exact hb
  filter_upwards [hGood, ae_all_iff.mpr hdelta] with x hx hdelta
  change R x u = G u x
  have hbound : ∀ z : E, ‖R x z - G u x‖ ≤ ‖A‖ * ‖z-u‖ := by
    intro z
    refine hd.induction_on z ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro w
      rw [show D.subtypeL w = (w:E) from rfl, hReq x hx w]
      exact hdelta w
  have hzero := hbound u
  simpa only [sub_self, norm_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] using hzero



end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Decomposable
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
 [NormedAddCommGroup E] [InnerProductSpace ℂ E]
lemma fieldMulL2_indicator (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (s : Set X) (hs : MeasurableSet s)
    (f : Lp E 2 μ) :
    fieldMulL2 μ T hT C hC (indicatorV2 μ s hs f) =
      indicatorV2 μ s hs (fieldMulL2 μ T hT C hC f) := by
  apply Lp.ext
  filter_upwards [fieldMulL2_coe μ T hT C hC (indicatorV2 μ s hs f),
    indicatorV2_coe μ s hs f, indicatorV2_coe μ s hs (fieldMulL2 μ T hT C hC f),
    fieldMulL2_coe μ T hT C hC f] with x h1 h2 h3 h4
  rw [h1,h2,h3]
  by_cases hx : x∈s
  · simpa only [indicator_of_mem hx] using h4.symm
  · simp only [indicator_of_notMem hx, map_zero]

variable [IsFiniteMeasure μ]

lemma indicatorConstLp_eq_indicatorV2 (c : E) (s : Set X) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) :
    indicatorConstLp 2 hs hμs c = indicatorV2 μ s hs (Lp.const 2 μ c) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c),
    indicatorV2_coe μ s hs (Lp.const 2 μ c), Lp.coeFn_const 2 μ c] with x h1 h2 h3
  rw [h1,h2]
  by_cases hx : x∈s
  · simp only [indicator_of_mem hx, h3, Function.const_apply]
  · simp only [indicator_of_notMem hx]

theorem commutes_indicators_decomposable [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ s (hs : MeasurableSet s), A.comp (indicatorV2 μ s hs) =
      (indicatorV2 μ s hs).comp A) :
    ∃ T : X → (E →L[ℂ] E), (∀ x, ‖T x‖ ≤ ‖A‖) ∧
      (∀ u : E, AEStronglyMeasurable (fun x ↦ T x u) μ) ∧
      (∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x)) := by
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq E
  obtain ⟨T,hT,heq⟩ := extract_bounded_field μ A
    (commutes_indicator_pointwise_bound μ A hA) v hv
  have hm (u : E) : AEStronglyMeasurable (fun x ↦ T x u) μ :=
    (Lp.aestronglyMeasurable (A (Lp.const 2 μ u))).congr (EventuallyEq.symm (heq u))
  let B := fieldMulL2 μ T hm ‖A‖ (Eventually.of_forall hT)
  have hconst (u : E) : B (Lp.const 2 μ u) = A (Lp.const 2 μ u) := by
    apply Lp.ext
    filter_upwards [fieldMulL2_coe μ T hm ‖A‖ (Eventually.of_forall hT) (Lp.const 2 μ u),
      Lp.coeFn_const 2 μ u, heq u] with x h1 h2 h3
    rw [h1,h2]
    exact h3
  have hAB : A = B := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.induction (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun f ↦ A f = B f) _ _ _ f
    · intro c s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_indicatorV2 μ c s hs]
      change A _ = fieldMulL2 μ T hm ‖A‖ (Eventually.of_forall hT) _
      rw [fieldMulL2_indicator]
      change A _ = indicatorV2 μ s hs (B (Lp.const 2 μ c))
      rw [hconst]
      exact congrArg (fun F : Lp E 2 μ →L[ℂ] Lp E 2 μ ↦ F (Lp.const 2 μ c)) (hA s hs)
    · intro f g _ _ _ hf hg
      simp only [map_add,hf,hg]
    · exact isClosed_eq A.continuous B.continuous
  refine ⟨T,hT,hm,fun f ↦ ?_⟩
  rw [hAB]
  exact fieldMulL2_coe μ T hm ‖A‖ (Eventually.of_forall hT) f
end

section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma inner_indicatorV2 (s : Set X) (hs : MeasurableSet s) (f g : Lp E 2 μ) :
    inner ℂ f (indicatorV2 μ s hs g) = ∫ x in s, inner ℂ (f x) (g x) ∂μ := by
  rw [L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorV2_coe μ s hs g] with x hx
  rw [hx]
  by_cases hxs : x∈s <;> simp [hxs]

variable [IsFiniteMeasure μ]

lemma decomposable_const (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (T : X → (E →L[ℂ] E))
    (hA : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x)) (u : E) :
    ∀ᵐ x ∂μ, (A (Lp.const 2 μ u)) x = T x u := by
  filter_upwards [hA (Lp.const 2 μ u), Lp.coeFn_const 2 μ u] with x h1 h2
  simpa only [h2,Function.const_apply] using h1

omit [IsFiniteMeasure μ] in
lemma ae_field_eq_of_dense [TopologicalSpace.SeparableSpace E]
    (T R : X → (E →L[ℂ] E)) (h : ∀ u, ∀ᵐ x ∂μ, T x u = R x u) :
    ∀ᵐ x ∂μ, T x = R x := by
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq E
  have hh : ∀ᵐ x ∂μ, ∀ n : ℕ, T x (v n) = R x (v n) := ae_all_iff.mpr (fun n ↦ h (v n))
  filter_upwards [hh] with x hx
  apply ContinuousLinearMap.ext
  exact congrFun (hv.equalizer (T x).continuous (R x).continuous (funext hx))

omit [IsFiniteMeasure μ] in
lemma decomposable_mul (A B : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (T R : X → (E →L[ℂ] E))
    (hA : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x))
    (hB : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (B f) x = R x (f x))
    (f : Lp E 2 μ) : ∀ᵐ x ∂μ, ((A*B) f) x = (T x*R x) (f x) := by
  filter_upwards [hA (B f),hB f] with x h1 h2
  simpa only [mul_apply_eq_comp,h2] using h1

lemma decomposable_eq [TopologicalSpace.SeparableSpace E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (T R : X → (E →L[ℂ] E))
    (hT : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x))
    (hR : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = R x (f x)) :
    ∀ᵐ x ∂μ, T x = R x := by
  apply ae_field_eq_of_dense μ T R
  intro u
  exact EventuallyEq.trans (EventuallyEq.symm (decomposable_const μ A T hT u))
    (decomposable_const μ A R hR u)

lemma decomposable_idempotent [TopologicalSpace.SeparableSpace E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (T : X → (E →L[ℂ] E))
    (hT : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x)) (hA : A*A=A) :
    ∀ᵐ x ∂μ, T x*T x=T x := by
  apply decomposable_eq μ A (fun x ↦ T x*T x) T _ hT
  intro f
  simpa only [hA] using decomposable_mul μ A A T T hT hT f

lemma decomposable_selfAdjoint [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (T : X → (E →L[ℂ] E))
    (hT : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x))
    (hc : ∀ s (hs : MeasurableSet s), A.comp (indicatorV2 μ s hs) =
      (indicatorV2 μ s hs).comp A) (hA : IsSelfAdjoint A) :
    ∀ᵐ x ∂μ, IsSelfAdjoint (T x) := by
  have hsymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hinner (u v : E) : ∀ᵐ x ∂μ, inner ℂ (T x u) v = inner ℂ u (T x v) := by
    let fu := Lp.const 2 μ u
    let fv := Lp.const 2 μ v
    have he : (fun x ↦ inner ℂ ((A fu) x) (fv x)) =ᵐ[μ]
        (fun x ↦ inner ℂ (fu x) ((A fv) x)) := by
      apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L2.integrable_inner _ _)
        (L2.integrable_inner _ _)
      intro s hs _
      rw [← inner_indicatorV2 μ s hs, ← inner_indicatorV2 μ s hs]
      change inner ℂ (A.toLinearMap fu) _ = _
      rw [hsymmetric]
      have hcomm := congrArg (fun B : Lp E 2 μ →L[ℂ] Lp E 2 μ ↦ B fv) (hc s hs)
      exact congrArg (inner ℂ fu) hcomm
    filter_upwards [he,decomposable_const μ A T hT u,decomposable_const μ A T hT v,
      Lp.coeFn_const 2 μ u,Lp.coeFn_const 2 μ v] with x h1 h2 h3 h4 h5
    change inner ℂ ((A fu) x) (fv x) = inner ℂ (fu x) ((A fv) x) at h1
    simpa only [fu,fv,h2,h3,h4,h5,Function.const_apply] using h1
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq E
  have hh : ∀ᵐ x ∂μ, ∀ n m : ℕ, inner ℂ (T x (v n)) (v m) = inner ℂ (v n) (T x (v m)) :=
    ae_all_iff.mpr (fun n ↦ ae_all_iff.mpr (fun m ↦ hinner (v n) (v m)))
  filter_upwards [hh] with x hx
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u w
  change inner ℂ (T x u) w = inner ℂ u (T x w)
  refine hv.induction_on₂ ?_ hx u w
  exact isClosed_eq (by fun_prop) (by fun_prop)
end

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma shiftedL2_coe (σ : X → X) (hσ : MeasurePreserving σ μ μ) (S : E →L[ℂ] E)
    (f : Lp E 2 μ) : shiftedL2 μ σ hσ S f =ᵐ[μ] fun x ↦ S (f (σ x)) := by
  filter_upwards [S.coeFn_compLpL (Lp.compMeasurePreserving σ hσ f),
    Lp.coeFn_compMeasurePreserving f hσ] with x h1 h2
  exact h1.trans (congrArg S h2)

variable [IsFiniteMeasure μ]
lemma shiftedL2_const (σ : X → X) (hσ : MeasurePreserving σ μ μ) (S : E →L[ℂ] E)
    (u : E) : shiftedL2 μ σ hσ S (Lp.const 2 μ u) = Lp.const 2 μ (S u) := by
  apply Lp.ext
  filter_upwards [shiftedL2_coe μ σ hσ S (Lp.const 2 μ u),
    hσ.quasiMeasurePreserving.ae (Lp.coeFn_const 2 μ u),
    Lp.coeFn_const 2 μ (S u)] with x h1 h2 h3
  simp only [h1,h2,h3,Function.const_apply]

lemma decomposable_covariance [TopologicalSpace.SeparableSpace E]
    (σ : X → X) (hσ : MeasurePreserving σ μ μ) (S : E →L[ℂ] E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (T : X → (E →L[ℂ] E))
    (hT : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x = T x (f x))
    (hAS : A * shiftedL2 μ σ hσ S = shiftedL2 μ σ hσ S * A) :
    ∀ᵐ x ∂μ, T x * S = S * T (σ x) := by
  apply ae_field_eq_of_dense μ
  intro u
  have he : A (Lp.const 2 μ (S u)) = shiftedL2 μ σ hσ S (A (Lp.const 2 μ u)) := by
    have := congrArg (fun B : Lp E 2 μ →L[ℂ] Lp E 2 μ ↦ B (Lp.const 2 μ u)) hAS
    simpa only [mul_apply_eq_comp,shiftedL2_const] using this
  filter_upwards [decomposable_const μ A T hT (S u),
    shiftedL2_coe μ σ hσ S (A (Lp.const 2 μ u)),
    hσ.quasiMeasurePreserving.ae (decomposable_const μ A T hT u)] with x h1 h2 h3
  change T x (S u) = S (T (σ x) u)
  rw [← h1,he,h2,h3]



end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Covariance
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uA uB uE uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section

lemma fiberShiftL2_indicator (n : ℤ) (s : Set CircleX) (hs : MeasurableSet s) :
    fiberShiftL2 n * indicatorV2 AddCircle.haarAddCircle s hs =
      indicatorV2 AddCircle.haarAddCircle s hs * fiberShiftL2 n := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [fiberShiftL2_coe n (indicatorV2 AddCircle.haarAddCircle s hs f),
    indicatorV2_coe AddCircle.haarAddCircle s hs f,
    indicatorV2_coe AddCircle.haarAddCircle s hs (fiberShiftL2 n f),
    fiberShiftL2_coe n f] with x h1 h2 h3 h4
  change (fiberShiftL2 n (indicatorV2 AddCircle.haarAddCircle s hs f)) x =
    (indicatorV2 AddCircle.haarAddCircle s hs (fiberShiftL2 n f)) x
  rw [h1,h2,h3]
  by_cases hx : x∈s
  · simp only [Set.indicator_of_mem hx,h4]
  · simp only [Set.indicator_of_notMem hx,map_zero]

lemma continuousPi_indicator (θ : CircleX) (g : C(CircleX,ℂ))
    (s : Set CircleX) (hs : MeasurableSet s) :
    continuousPi θ g * indicatorV2 AddCircle.haarAddCircle s hs =
      indicatorV2 AddCircle.haarAddCircle s hs * continuousPi θ g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ g (indicatorV2 AddCircle.haarAddCircle s hs f),
    indicatorV2_coe AddCircle.haarAddCircle s hs f,
    indicatorV2_coe AddCircle.haarAddCircle s hs (continuousPi θ g f),
    continuousPi_coe θ g f] with x h1 h2 h3 h4
  change (continuousPi θ g (indicatorV2 AddCircle.haarAddCircle s hs f)) x =
    (indicatorV2 AddCircle.haarAddCircle s hs (continuousPi θ g f)) x
  rw [h1,h2,h3]
  by_cases hx : x∈s
  · simp only [Set.indicator_of_mem hx,h4]
  · simp only [Set.indicator_of_notMem hx,map_zero]

lemma circleJ_coe (θ : CircleX) (n : ℤ) (f : CircleFiberL2) :
    circleJ θ n f =ᵐ[AddCircle.haarAddCircle] fun x ↦ fiberShift n (f (x+n•θ)) :=
  shiftedL2_coe _ _ _ _ _

lemma fiberShiftL2_circleJ (θ : CircleX) (n : ℤ) :
    fiberShiftL2 1 * circleJ θ n = circleJ θ n * fiberShiftL2 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [fiberShiftL2_coe 1 (circleJ θ n f),circleJ_coe θ n f,
    circleJ_coe θ n (fiberShiftL2 1 f),
    (measurePreserving_add_right AddCircle.haarAddCircle (n•θ)).quasiMeasurePreserving.ae
      (fiberShiftL2_coe 1 f)] with x h1 h2 h3 h4
  change (fiberShiftL2 1 (circleJ θ n f)) x = (circleJ θ n (fiberShiftL2 1 f)) x
  rw [h1,h2,h3,h4]
  change (fiberShift 1 * fiberShift n) (f (x+n•θ)) =
    (fiberShift n * fiberShift 1) (f (x+n•θ))
  rw [← fiberShift_add,← fiberShift_add,add_comm (1:ℤ) n]

lemma continuousPiField_covariance (θ : CircleX) (n : ℤ) (g : C(CircleX,ℂ)) (x : CircleX)
    (u : FiberHilbert) :
    continuousPiField θ g x (fiberShift n u) =
      fiberShift n (continuousPiField θ g (x+n•θ) u) := by
  ext k
  simp only [continuousPiField_apply,fiberShift_apply]
  have he : x+(k:ℤ)•θ = (x+n•θ)+(k-n)•θ := by rw [sub_zsmul]; abel
  rw [he]

lemma continuousPi_circleJ (θ : CircleX) (n : ℤ) (g : C(CircleX,ℂ)) :
    continuousPi θ g * circleJ θ n = circleJ θ n * continuousPi θ g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ g (circleJ θ n f),circleJ_coe θ n f,
    circleJ_coe θ n (continuousPi θ g f),
    (measurePreserving_add_right AddCircle.haarAddCircle (n•θ)).quasiMeasurePreserving.ae
      (continuousPi_coe θ g f)] with x h1 h2 h3 h4
  change (continuousPi θ g (circleJ θ n f)) x = (circleJ θ n (continuousPi θ g f)) x
  rw [h1,h2,h3,h4]
  exact continuousPiField_covariance θ n g x _

lemma doubleCentralizer_commute {A : Type uA} {B : Type uB} [Monoid A] [Monoid B]
    (φ : A ≃* B) (u v p : A) (hp : p ∈ Set.centralizer (Set.centralizer ({u,v} : Set A)))
    (b : B) (hu : φ u * b = b * φ u) (hv : φ v * b = b * φ v) :
    φ p * b = b * φ p := by
  have hb : φ.symm b ∈ Set.centralizer ({u,v} : Set A) := by
    intro a ha
    rcases (Set.mem_insert_iff.mp ha) with rfl | ha
    · apply φ.injective
      simpa using hu
    · have he : a=v := Set.mem_singleton_iff.mp ha
      subst a
      apply φ.injective
      simpa using hv
  have he := hp (φ.symm b) hb
  have he' := congrArg φ he.symm
  simpa only [map_mul,φ.apply_symm_apply] using he'

lemma regular_doubleCentralizer_indicators (θ : ℝ) (p : RegularOperator)
    (hp : p ∈ Set.centralizer (Set.centralizer
      ({(regularU : RegularOperator),(regularV (rotationScalar θ) : RegularOperator)} : Set RegularOperator)))
    (s : Set CircleX) (hs : MeasurableSet s) :
    circleFiberBasis.repr.symm.conjStarAlgEquiv p * indicatorV2 AddCircle.haarAddCircle s hs =
      indicatorV2 AddCircle.haarAddCircle s hs * circleFiberBasis.repr.symm.conjStarAlgEquiv p := by
  apply doubleCentralizer_commute circleFiberBasis.repr.symm.conjStarAlgEquiv.toMulEquiv
    regularU (regularV (rotationScalar θ)) p hp
  · change circleFiberBasis.repr.symm.conjStarAlgEquiv (regularU : RegularOperator) * _ =
      _ * circleFiberBasis.repr.symm.conjStarAlgEquiv (regularU : RegularOperator)
    rw [circleFiberBasis_conj_U]
    exact fiberShiftL2_indicator 1 s hs
  · change circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator) * _ =
      _ * circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator)
    rw [circleFiberBasis_conj_V]
    exact continuousPi_indicator (θ : CircleX) (fourier 1) s hs


lemma regular_doubleCentralizer_circleJ (θ : ℝ) (p : RegularOperator)
    (hp : p ∈ Set.centralizer (Set.centralizer
      ({(regularU : RegularOperator),(regularV (rotationScalar θ) : RegularOperator)} : Set RegularOperator)))
    (n : ℤ) :
    circleFiberBasis.repr.symm.conjStarAlgEquiv p * circleJ (θ : CircleX) n =
      circleJ (θ : CircleX) n * circleFiberBasis.repr.symm.conjStarAlgEquiv p := by
  apply doubleCentralizer_commute circleFiberBasis.repr.symm.conjStarAlgEquiv.toMulEquiv
    regularU (regularV (rotationScalar θ)) p hp
  · change circleFiberBasis.repr.symm.conjStarAlgEquiv (regularU : RegularOperator) * _ =
      _ * circleFiberBasis.repr.symm.conjStarAlgEquiv (regularU : RegularOperator)
    rw [circleFiberBasis_conj_U]
    exact fiberShiftL2_circleJ (θ : CircleX) n
  · change circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator) * _ =
      _ * circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator)
    rw [circleFiberBasis_conj_V]
    exact continuousPi_circleJ (θ : CircleX) n (fourier 1)
end

open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
section
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma invariant_eigenvector_zero (P Q D : E →L[ℂ] E)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hInv : (1-Q)*D*P=0) (e : E) (c : ℂ) (hc : c≠0)
    (hDe : (star D) e = c•e) (hQe : Q e=0) : P e=0 := by
  have hStar : P * star D * (1-Q)=0 := by
    have h := congrArg star hInv
    simpa only [star_mul,star_sub,star_one,hP.isSelfAdjoint.star_eq,
      hQ.isSelfAdjoint.star_eq,star_zero,mul_assoc] using h
  have h := congrArg (fun A : E →L[ℂ] E ↦ A e) hStar
  change P ((star D) (e-Q e))=0 at h
  rw [hQe,sub_zero,hDe,map_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hc

omit [CompleteSpace E] in
lemma invariant_eigenvector_one (P Q D : E →L[ℂ] E)
    (hInv : (1-Q)*D*P=0) (e : E) (c : ℂ) (hc : c≠0)
    (hDe : D e=c•e) (hPe : P e=e) : Q e=e := by
  have h := congrArg (fun A : E →L[ℂ] E ↦ A e) hInv
  change (1-Q) (D (P e))=0 at h
  rw [hPe,hDe,map_smul] at h
  have he := (smul_eq_zero.mp h).resolve_left hc
  change e-Q e=0 at he
  exact (sub_eq_zero.mp he).symm

lemma projection_diagonal_norm_sq (P : E →L[ℂ] E) (hP : IsStarProjection P) (e : E) :
    (inner ℂ e (P e)).re = ‖P e‖^2 := by
  have h := ContinuousLinearMap.adjoint_inner_right P e (P e)
  have hid : P (P e)=P e := congrArg (fun A : E →L[ℂ] E ↦ A e) hP.isIdempotentElem.eq
  change inner ℂ e ((star P) (P e)) = inner ℂ (P e) (P e) at h
  rw [hP.isSelfAdjoint.star_eq,hid] at h
  rw [h]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (P e)

lemma projection_diagonal_strict (P : E →L[ℂ] E) (hP : IsStarProjection P) (e : E)
    (he : ‖e‖=1) (hz : P e≠0) (ho : P e≠e) :
    0 < (inner ℂ e (P e)).re ∧ (inner ℂ e (P e)).re < 1 := by
  have hp := projection_diagonal_norm_sq P hP e
  have hq := projection_diagonal_norm_sq (1-P) hP.one_sub e
  have hqn : (1-P) e ≠ 0 := by
    change e-P e ≠ 0
    intro h
    exact ho (sub_eq_zero.mp h).symm
  have hqpos : 0 < ‖(1-P) e‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hqn)
  have hpn : 0 < ‖P e‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hqeq : (inner ℂ e ((1-P) e)).re = 1-(inner ℂ e (P e)).re := by
    change (inner ℂ e (e-P e)).re = _
    rw [inner_sub_right,Complex.sub_re]
    have hee : (inner ℂ e e).re = ‖e‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) e
    rw [hee,he,one_pow]
  rw [hqeq] at hq
  exact ⟨by linarith,by linarith⟩

end

open MeasureTheory Filter Set
section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma ergodic_ae_ne_of_preimage_zero (σ : X → X) (hσ : Ergodic σ μ)
    (f : X → E) (hf : AEMeasurable f μ) (e : E)
    (hinv : ∀ᵐ x ∂μ, f (σ x)=e → f x=e)
    (hne : ¬∀ᵐ x ∂μ, f x=e) : ∀ᵐ x ∂μ, f x≠e := by
  have hs : NullMeasurableSet {x | f x=e} μ := hf.nullMeasurableSet_preimage (measurableSet_singleton e)
  have hle : σ ⁻¹' {x | f x=e} ≤ᵐ[μ] {x | f x=e} := hinv
  rcases hσ.ae_empty_or_univ_of_preimage_ae_le hs hle with h | h
  · filter_upwards [h] with x hx
    intro he
    exact Eq.mp hx he
  · apply False.elim
    apply hne
    filter_upwards [h] with x hx
    exact hx.mpr (Set.mem_univ x)

lemma ergodic_ae_ne_of_zero_preimage (σ : X → X) (hσ : Ergodic σ μ)
    (f : X → E) (hf : AEMeasurable f μ) (e : E)
    (hinv : ∀ᵐ x ∂μ, f x=e → f (σ x)=e)
    (hne : ¬∀ᵐ x ∂μ, f x=e) : ∀ᵐ x ∂μ, f x≠e := by
  have hs : NullMeasurableSet {x | f x=e} μ := hf.nullMeasurableSet_preimage (measurableSet_singleton e)
  have hle : {x | f x=e} ≤ᵐ[μ] σ ⁻¹' {x | f x=e} := hinv
  rcases hσ.ae_empty_or_univ_of_ae_le_preimage hs hle with h | h
  · filter_upwards [h] with x hx
    intro he
    exact Eq.mp hx he
  · apply False.elim
    apply hne
    filter_upwards [h] with x hx
    exact hx.mpr (Set.mem_univ x)
end

section

lemma covariant_field_zero (θ : CircleX) (P : CircleX → FiberOperator)
    (hcov : ∀ n : ℤ, ∀ᵐ x ∂AddCircle.haarAddCircle,
      P x * (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap =
        (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap * P (x+n•θ))
    (hz : ∀ᵐ x ∂AddCircle.haarAddCircle, P x (lp.single 2 0 1)=0) :
    ∀ᵐ x ∂AddCircle.haarAddCircle, P x=0 := by
  have hb : ∀ n : ℤ, ∀ᵐ x ∂AddCircle.haarAddCircle, P x (lp.single 2 n 1)=0 := by
    intro n
    filter_upwards [hcov n,
      (measurePreserving_add_right AddCircle.haarAddCircle (n•θ)).quasiMeasurePreserving.ae hz]
      with x hc he
    have h := congrArg (fun A : FiberOperator ↦ A (lp.single 2 0 1)) hc
    change P x (fiberShift n (lp.single 2 0 1)) = fiberShift n (P (x+n•θ) (lp.single 2 0 1)) at h
    simpa only [fiberShift_single,add_zero,he,map_zero] using h
  filter_upwards [ae_all_iff.mpr hb] with x hx
  apply lp.ext_continuousLinearMap (by norm_num)
  intro n
  apply ContinuousLinearMap.ext
  intro c
  change P x (lp.single 2 n c)=0
  have he : (lp.single 2 n c : FiberHilbert) = c • (lp.single 2 n (1:ℂ) : FiberHilbert) := by
    ext k
    by_cases hk : k=n
    · subst k
      simp
    · simp [lp.single_apply,hk]
  rw [he,map_smul,hx n,smul_zero]

lemma covariant_field_one (θ : CircleX) (P : CircleX → FiberOperator)
    (hcov : ∀ n : ℤ, ∀ᵐ x ∂AddCircle.haarAddCircle,
      P x * (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap =
        (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap * P (x+n•θ))
    (hz : ∀ᵐ x ∂AddCircle.haarAddCircle, P x (lp.single 2 0 1)=lp.single 2 0 1) :
    ∀ᵐ x ∂AddCircle.haarAddCircle, P x=1 := by
  have hc : ∀ n : ℤ, ∀ᵐ x ∂AddCircle.haarAddCircle,
      (1-P x) * (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap =
        (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap * (1-P (x+n•θ)) := by
    intro n
    filter_upwards [hcov n] with x hx
    simp only [sub_mul,mul_sub,one_mul,mul_one,hx]
  have hz' : ∀ᵐ x ∂AddCircle.haarAddCircle, (1-P x) (lp.single 2 0 1)=0 := by
    filter_upwards [hz] with x hx
    change lp.single 2 0 1-P x (lp.single 2 0 1)=0
    rw [hx,sub_self]
  filter_upwards [covariant_field_zero θ (fun x ↦ 1-P x) hc hz'] with x hx
  exact (sub_eq_zero.mp hx).symm

lemma decomposable_eq_zero {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (P : X → (E →L[ℂ] E))
    (hP : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x=P x (f x))
    (hz : ∀ᵐ x ∂μ, P x=0) : A=0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hP f,hz,Lp.coeFn_zero E 2 μ] with x h1 h2 h3
  change (A f) x = (0 : Lp E 2 μ) x
  rw [h1,h2]
  simpa using h3.symm

lemma decomposable_eq_one {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (P : X → (E →L[ℂ] E))
    (hP : ∀ f : Lp E 2 μ, ∀ᵐ x ∂μ, (A f) x=P x (f x))
    (hz : ∀ᵐ x ∂μ, P x=1) : A=1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hP f,hz] with x h1 h2
  change (A f) x = f x
  rw [h1,h2,one_apply_eq_self]

end

lemma invariant_covariant_diagonal_strict
    (θ : CircleX) (hθ : Ergodic (fun x : CircleX ↦ x+θ) AddCircle.haarAddCircle)
    (A : CircleFiberOperator) (P : CircleX → FiberOperator)
    (hP : ∀ f : CircleFiberL2, ∀ᵐ x ∂AddCircle.haarAddCircle, (A f) x=P x (f x))
    (hproj : ∀ᵐ x ∂AddCircle.haarAddCircle, IsStarProjection (P x))
    (hcov : ∀ n : ℤ, ∀ᵐ x ∂AddCircle.haarAddCircle,
      P x * (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap =
        (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap * P (x+n•θ))
    (D : CircleX → FiberOperator) (c : CircleX → ℂ)
    (hc : ∀ᵐ x ∂AddCircle.haarAddCircle, c x≠0)
    (heigen : ∀ᵐ x ∂AddCircle.haarAddCircle,
      D x (lp.single 2 0 1)=c x • lp.single 2 0 1 ∧
      (star (D x)) (lp.single 2 0 1)=c x • lp.single 2 0 1)
    (hinv : ∀ᵐ x ∂AddCircle.haarAddCircle, (1-P (x+θ))*D x*P x=0)
    (hA0 : A≠0) (hA1 : A≠1) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,
      0 < (inner ℂ (lp.single 2 0 1) (P x (lp.single 2 0 1))).re ∧
      (inner ℂ (lp.single 2 0 1) (P x (lp.single 2 0 1))).re < 1 := by
  let : MeasurableSpace FiberHilbert := borel FiberHilbert
  let : BorelSpace FiberHilbert := ⟨rfl⟩
  let e : FiberHilbert := lp.single 2 0 1
  have hm : AEMeasurable (fun x ↦ P x e) AddCircle.haarAddCircle := by
    apply (Lp.aestronglyMeasurable (A (Lp.const 2 AddCircle.haarAddCircle e))).aemeasurable.congr
    exact decomposable_const AddCircle.haarAddCircle A P hP e
  have hz : ¬∀ᵐ x ∂AddCircle.haarAddCircle, P x e=0 := by
    intro h
    exact hA0 (decomposable_eq_zero AddCircle.haarAddCircle A P hP (covariant_field_zero θ P hcov h))
  have ho : ¬∀ᵐ x ∂AddCircle.haarAddCircle, P x e=e := by
    intro h
    exact hA1 (decomposable_eq_one AddCircle.haarAddCircle A P hP (covariant_field_one θ P hcov h))
  have hrz : ∀ᵐ x ∂AddCircle.haarAddCircle, P (x+θ) e=0 → P x e=0 := by
    filter_upwards [hproj,hθ.toMeasurePreserving.quasiMeasurePreserving.ae hproj,hc,heigen,hinv]
      with x hp hq hcx hex hix
    intro h
    exact invariant_eigenvector_zero (P x) (P (x+θ)) (D x) hp hq hix e (c x) hcx hex.2 h
  have hro : ∀ᵐ x ∂AddCircle.haarAddCircle, P x e=e → P (x+θ) e=e := by
    filter_upwards [hc,heigen,hinv] with x hcx hex hix
    intro h
    exact invariant_eigenvector_one (P x) (P (x+θ)) (D x) hix e (c x) hcx hex.1 h
  filter_upwards [hproj,
    ergodic_ae_ne_of_preimage_zero (fun x : CircleX ↦ x+θ) hθ (fun x ↦ P x e) hm 0 hrz hz,
    ergodic_ae_ne_of_zero_preimage (fun x : CircleX ↦ x+θ) hθ (fun x ↦ P x e) hm e hro ho]
    with x hp hx0 hx1
  exact projection_diagonal_strict (P x) hp e (by simp [e]) hx0 hx1


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ProjectionFields
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set

open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexInnerProductSpace
attribute [local instance] OAI.ContinuousCircleWeight.instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert
local instance instBorelSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert : BorelSpace FiberHilbert := ⟨rfl⟩
local instance instSeparableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert : TopologicalSpace.SeparableSpace FiberHilbert := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have h := ((Set.countable_range fiberBasis).isSeparable.span (R:=ℂ)).closure
  change TopologicalSpace.IsSeparable ((Submodule.span ℂ (Set.range fiberBasis)).topologicalClosure : Set FiberHilbert) at h
  simpa only [fiberBasis.dense_span,Submodule.top_coe] using h

lemma measurable_projection_version (T : CircleX → FiberOperator)
    (hm : ∀ k : ℤ,AEStronglyMeasurable (fun x => T x (lp.single 2 k 1)) AddCircle.haarAddCircle)
    (hp : ∀ᵐ x ∂AddCircle.haarAddCircle,IsStarProjection (T x)) :
    ∃ P : CircleX → FiberOperator, P=ᵐ[AddCircle.haarAddCircle] T ∧
      (∀ x,IsStarProjection (P x)) ∧ (∀ x,‖P x‖≤1) ∧
      ∀ k : ℤ,Measurable (fun x => P x (lp.single 2 k 1)) := by
  classical
  let F : ℤ → CircleX → FiberHilbert := fun k => (hm k).mk (fun x => T x (lp.single 2 k 1))
  have hgood : ∀ᵐ x ∂AddCircle.haarAddCircle,(∀ k : ℤ,T x (lp.single 2 k 1)=F k x) ∧ IsStarProjection (T x) := by
    filter_upwards [ae_all_iff.mpr (fun k => (hm k).ae_eq_mk),hp] with x hx hpx
    exact ⟨hx,hpx⟩
  obtain ⟨N,hN,hmN,hzN⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hn (x : CircleX) (hx : x∉N) : (∀ k : ℤ,T x (lp.single 2 k 1)=F k x) ∧ IsStarProjection (T x) := by
    by_contra h
    exact hx (hN h)
  let P : CircleX → FiberOperator := fun x => if x∈N then 0 else T x
  have hPP (x : CircleX) : IsStarProjection (P x) := by
    by_cases hx : x∈N
    · simp only [P,ite_eq_left hx]; exact IsStarProjection.zero _
    · simpa only [P,ite_eq_right hx] using (hn x hx).2
  refine ⟨P,?_,hPP,fun x => (hPP x).norm_le,?_⟩
  · filter_upwards [(show ∀ᵐ x ∂AddCircle.haarAddCircle,x∉N from (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hzN)))] with x hx
    exact ite_eq_right hx
  · intro k
    have he : (fun x => P x (lp.single 2 k 1))=(fun x => if x∈N then 0 else F k x) := by
      funext x
      by_cases hx : x∈N
      · simp [P,hx]
      · simpa only [P,ite_eq_right hx] using (hn x hx).1 k
    rw [he]
    exact Measurable.ite hmN measurable_const (hm k).measurable_mk

lemma fiber_commutes_indicators (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) (s : Set CircleX) (hs : MeasurableSet s) :
    A.comp (indicatorV2 AddCircle.haarAddCircle s hs)=(indicatorV2 AddCircle.haarAddCircle s hs).comp A := by
  have h := regular_doubleCentralizer_indicators θ (fiberConjugacy.symm A) (regularAlgebra_of_commutes θ A hA) s hs
  change fiberConjugacy (fiberConjugacy.symm A)*_=_*fiberConjugacy (fiberConjugacy.symm A) at h
  change A*indicatorV2 AddCircle.haarAddCircle s hs=indicatorV2 AddCircle.haarAddCircle s hs*A
  simpa only [fiberConjugacy.apply_symm_apply] using h
lemma fiber_commutes_circleJ (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) (n : ℤ) : A*circleJ (θ:CircleX) n=circleJ (θ:CircleX) n*A := by
  have h := regular_doubleCentralizer_circleJ θ (fiberConjugacy.symm A) (regularAlgebra_of_commutes θ A hA) n
  change fiberConjugacy (fiberConjugacy.symm A)*_=_*fiberConjugacy (fiberConjugacy.symm A) at h
  simpa only [fiberConjugacy.apply_symm_apply] using h

theorem extract_projection_field (θ : ℝ) (A : CircleFiberOperator) (hA : IsStarProjection A)
    (hcomm : ∀ B∈fiberCommutant θ,Commute A B) :
    ∃ P : CircleX → FiberOperator,
      (∀ x,IsStarProjection (P x)) ∧ (∀ x,‖P x‖≤1) ∧
      (∀ k : ℤ,Measurable (fun x => P x (lp.single 2 k 1))) ∧
      (∀ u : CircleFiberL2,∀ᵐ x ∂AddCircle.haarAddCircle,(A u) x=P x (u x)) ∧
      ∀ n : ℤ,∀ᵐ x ∂AddCircle.haarAddCircle,
        P x*(fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap=
          (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap*P (x+n•(θ:CircleX)) := by
  obtain ⟨T,_hbound,hm,hT⟩ := commutes_indicators_decomposable AddCircle.haarAddCircle A (fiber_commutes_indicators θ A hcomm)
  have hTproj : ∀ᵐ x ∂AddCircle.haarAddCircle,IsStarProjection (T x) := by
    filter_upwards [decomposable_idempotent AddCircle.haarAddCircle A T hT hA.isIdempotentElem,
      decomposable_selfAdjoint AddCircle.haarAddCircle A T hT (fiber_commutes_indicators θ A hcomm) hA.isSelfAdjoint] with x h1 h2
    exact ⟨h1,h2⟩
  obtain ⟨P,hPT,hPproj,hPbound,hPmeas⟩ := measurable_projection_version T (fun k => hm _) hTproj
  have hP (u : CircleFiberL2) : ∀ᵐ x ∂AddCircle.haarAddCircle,(A u) x=P x (u x) := by
    filter_upwards [hT u,hPT] with x hx hpx
    rw [hpx]; exact hx
  refine ⟨P,hPproj,hPbound,hPmeas,hP,fun n => ?_⟩
  exact decomposable_covariance AddCircle.haarAddCircle (fun x : CircleX => x+n•(θ:CircleX))
    (measurePreserving_add_right AddCircle.haarAddCircle (n•(θ:CircleX))) _ A P hP (fiber_commutes_circleJ θ A hcomm n)

lemma borelWeightedField_coe (θ : CircleX) (g : RealBorel) (u : CircleFiberL2) :
    (fiberShiftL2 1*realPi θ g) u=ᵐ[AddCircle.haarAddCircle] fun x => borelWeightedField θ g x (u x) := by
  filter_upwards [fiberShiftL2_coe 1 (realPi θ g u),realPi_coe θ g u] with x h1 h2
  change (fiberShiftL2 1 (realPi θ g u)) x=_
  rw [h1,h2]
  rfl
lemma decomposable_one_sub (A : CircleFiberOperator) (P : CircleX → FiberOperator)
    (hP : ∀ u : CircleFiberL2,∀ᵐ x ∂AddCircle.haarAddCircle,(A u) x=P x (u x))
    (u : CircleFiberL2) : ∀ᵐ x ∂AddCircle.haarAddCircle,((1-A) u) x=(1-P x) (u x) := by
  filter_upwards [Lp.coeFn_sub u (A u),hP u] with x h1 h2
  change (u-A u) x=_
  rw [h1]
  simp only [Pi.sub_apply,h2]
  rfl
lemma decomposable_invariant (A : CircleFiberOperator) (P : CircleX → FiberOperator)
    (hP : ∀ u : CircleFiberL2,∀ᵐ x ∂AddCircle.haarAddCircle,(A u) x=P x (u x))
    (θ : CircleX) (g : RealBorel) (hinv : (1-A)*(fiberShiftL2 1*realPi θ g)*A=0) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,(1-P x)*borelWeightedField θ g x*P x=0 := by
  apply ae_field_eq_of_dense AddCircle.haarAddCircle
  intro u
  have h := decomposable_mul AddCircle.haarAddCircle ((1-A)*(fiberShiftL2 1*realPi θ g)) A
    (fun x => (1-P x)*borelWeightedField θ g x) P
    (decomposable_mul AddCircle.haarAddCircle _ _ _ _ (decomposable_one_sub A P hP) (borelWeightedField_coe θ g)) hP
  have hc := decomposable_const AddCircle.haarAddCircle _ _ h u
  filter_upwards [hc,Lp.coeFn_zero FiberHilbert 2 AddCircle.haarAddCircle] with x hx hz
  rw [hinv] at hx
  exact hx.symm.trans hz

lemma realPiField_proj_eigen (θ : CircleX) (g : RealBorel) (x : CircleX) :
    realPiField θ g x (lp.single 2 0 1)=(g x:ℂ)•lp.single 2 0 1 ∧
    (star (realPiField θ g x)) (lp.single 2 0 1)=(g x:ℂ)•lp.single 2 0 1 := by
  have h1 : realPiField θ g x (lp.single 2 0 1)=(g x:ℂ)•lp.single 2 0 1 := by
    ext k
    by_cases hk : k=0
    · subst k; simp only [realPiField_apply,zero_zsmul,add_zero,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply,Pi.single_eq_same,mul_one]
    · simp only [realPiField_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply,Pi.single_eq_of_ne hk,mul_zero]
  refine ⟨h1,?_⟩
  have hs : IsSelfAdjoint (realPiField θ g x) := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (realPiField_symmetric θ g x)
  rw [hs.star_eq]
  exact h1
lemma weighted_invariant_diagonal (P Q D : FiberOperator)
    (hcov : P*(fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap=
      (fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap*Q)
    (hinv : (1-P)*((fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap*D)*P=0) :
    (1-Q)*D*P=0 := by
  have he : (1-P)*((fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap*D)*P=
      (fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap*((1-Q)*D*P) := by
    simp only [sub_mul,mul_sub,one_mul,mul_assoc]
    rw [←mul_assoc P, hcov, mul_assoc]
  rw [he] at hinv
  apply ContinuousLinearMap.ext
  intro u
  apply (fiberShift 1).injective
  exact (DFunLike.congr_fun hinv u).trans (map_zero _).symm

lemma borel_invariant_diagonal_strict (θ : ℝ)
    (hθ : Ergodic (fun x : CircleX => x+(θ:CircleX)) AddCircle.haarAddCircle)
    (A : CircleFiberOperator) (P : CircleX → FiberOperator)
    (hP : ∀ u : CircleFiberL2,∀ᵐ x ∂AddCircle.haarAddCircle,(A u) x=P x (u x))
    (hproj : ∀ x,IsStarProjection (P x))
    (hcov : ∀ n : ℤ,∀ᵐ x ∂AddCircle.haarAddCircle,P x*(fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap=
      (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap*P (x+n•(θ:CircleX)))
    (g : RealBorel) (hg : ∀ x,g x≠0)
    (hinv : (1-A)*(fiberShiftL2 1*realPi (θ:CircleX) g)*A=0) (hA0 : A≠0) (hA1 : A≠1) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,0<(inner ℂ (lp.single 2 0 1) (P x (lp.single 2 0 1))).re ∧
      (inner ℂ (lp.single 2 0 1) (P x (lp.single 2 0 1))).re<1 := by
  apply invariant_covariant_diagonal_strict (θ:CircleX) hθ A P hP (Eventually.of_forall hproj) hcov
    (realPiField (θ:CircleX) g) (fun x => (g x:ℂ))
    (Eventually.of_forall (fun x => Complex.ofReal_ne_zero.mpr (hg x)))
    (Eventually.of_forall (realPiField_proj_eigen (θ:CircleX) g)) _ hA0 hA1
  filter_upwards [decomposable_invariant A P hP (θ:CircleX) g hinv,hcov 1] with x hi hc
  rw [one_zsmul] at hc
  exact weighted_invariant_diagonal _ _ _ hc hi


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Parameters
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.CircleSampling.stageSample_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set

section
open Set Filter MeasureTheory ContinuousCircleWeight.Sampling
open scoped Topology

lemma polynomialWindow_growth (j : ℕ) : 2*polynomialWindow j<polynomialWindow (j+1) :=
  (scaleStep j).numeric.2.2.2.2.2.2.1

lemma polynomialWindow_geometric (j n : ℕ) : 2^n*polynomialWindow j≤polynomialWindow (j+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hg := (polynomialWindow_growth (j+n)).le
    calc
      2^(n+1)*polynomialWindow j = 2*(2^n*polynomialWindow j) := by ring
      _ ≤ 2*polynomialWindow (j+n) := Nat.mul_le_mul_left _ ih
      _ ≤ polynomialWindow (j+(n+1)) := by simpa only [Nat.add_assoc] using hg

end

open Set Filter MeasureTheory
open scoped Topology BigOperators

lemma window_inverse_bound (j n : ℕ) :
    1/(polynomialWindow (j+n):ℝ) ≤ (1/(polynomialWindow j:ℝ))*(1/2:ℝ)^n := by
  have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
  have hg : (2:ℝ)^n*(polynomialWindow j:ℝ) ≤ polynomialWindow (j+n) := by
    exact_mod_cast polynomialWindow_geometric j n
  calc
    1/(polynomialWindow (j+n):ℝ) ≤ 1/((2:ℝ)^n*(polynomialWindow j:ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hg
    _ = (1/(polynomialWindow j:ℝ))*(1/2:ℝ)^n := by rw [div_pow,one_pow]; field_simp

lemma summable_window_inverse (j : ℕ) : Summable (fun n => 1/(polynomialWindow (j+n):ℝ)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (window_inverse_bound j)
  exact (summable_geometric_of_norm_lt_one (x:=(1/2:ℝ)) (by norm_num)).mul_left _

lemma sum_phase_block (j : ℕ) :
    (∑ i : Fin (blockLength j), coordinatePhase (blocks.equiv ⟨j,i⟩)) ≤ 2/(polynomialWindow j:ℝ) := by
  have hm : (blockLength j:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (scaleStep j).mpos.ne'
  calc
    _ ≤ ∑ _i : Fin (blockLength j),2/((blockLength j:ℝ)*polynomialWindow j) :=
      Finset.sum_le_sum (fun i _ => (coordinatePhase_block j i).2.le)
    _ = 2/(polynomialWindow j:ℝ) := by simp; field_simp

lemma summable_coordinatePhase : Summable coordinatePhase := by
  have hs : Summable (fun j => 2/(polynomialWindow j:ℝ)) := by
    simpa only [Nat.zero_add,div_eq_mul_inv,one_mul] using (summable_window_inverse 0).mul_left 2
  have ht : Summable (fun j => ∑ i : Fin (blockLength j), coordinatePhase (blocks.equiv ⟨j,i⟩)) :=
    Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg (fun _ _ => (coordinatePhase_pos _).le))
      sum_phase_block hs
  apply blocks.equiv.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun x : Σ j, Fin (blocks.m j) => (coordinatePhase_pos (blocks.equiv x)).le)).mpr
  refine ⟨fun _ => Summable.of_finite,?_⟩
  convert ht using 1
  ext j
  rw [tsum_fintype]
  rfl

lemma block_number_equiv (j : ℕ) (i : Fin (blockLength j)) :
    coordinateBlock (blocks.equiv ⟨j,i⟩)=j := by
  exact blocks.number_eq (by change blockEnd j≤blockEnd j+i.val; omega)
    (by change blockEnd j+i.val<blockEnd j+blockLength j; omega)

lemma phase_drop_block_lower (j : ℕ) :
    (polynomialWindow j:ℝ) ≤ ∑ i : Fin (blockLength j),
      coordinateDrop (blocks.equiv ⟨j,i⟩)*coordinatePhase (blocks.equiv ⟨j,i⟩) := by
  have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
  have hm : 0<(blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
  calc
    _ = (blockLength j:ℝ)*((polynomialWindow j:ℝ)^2/((blockLength j:ℝ)*polynomialWindow j)) := by field_simp
    _ = ∑ _i : Fin (blockLength j),(polynomialWindow j:ℝ)^2/((blockLength j:ℝ)*polynomialWindow j) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      change _≤dropSize (coordinateBlock (blocks.equiv ⟨j,i⟩))*_
      rw [block_number_equiv]
      calc
        _ = (polynomialWindow j:ℝ)^2*(1/((blockLength j:ℝ)*polynomialWindow j)) := by ring
        _ ≤ dropSize j*coordinatePhase (blocks.equiv ⟨j,i⟩) := by
          exact mul_le_mul (dropSize_ge_window_sq j) (coordinatePhase_block j i).1.le (by positivity) (dropSize_nonneg j)


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_MeasurableWeight
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleModel

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
section
lemma repr_coe (x : CircleX) : ((repr x : ℝ) : CircleX) = x := by
  exact (AddCircle.measurableEquivIco 1 0).symm_apply_apply x

lemma Xi_shift (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (i : ℕ) (x : CircleX) :
    Xi q i (shift θ k x) = Int.fract (Xi q i x + k*beta q θ i) := by
  rw [← repr_mk]
  have hk : (((k:ℝ)*repr (q i • θ) : ℝ) : CircleX) = k • (q i • θ) := by
    rw [← zsmul_eq_mul,AddCircle.coe_zsmul,repr_coe]
  change repr (q i • (x+k•θ)) = repr ((repr (q i • x)+(k:ℝ)*repr (q i • θ) : ℝ) : CircleX)
  rw [AddCircle.coe_add,repr_coe,hk,nsmul_add,smul_comm]

lemma floor_cocycle (x a : ℝ) (k n : ℤ) :
    ⌊x+(k+n)*a⌋ = ⌊x+k*a⌋ + ⌊Int.fract (x+k*a)+n*a⌋ := by
  have h : x+(k+n)*a = Int.fract (x+k*a)+n*a+(⌊x+k*a⌋:ℝ) := by
    rw [Int.fract]; ring
  rw [h,Int.floor_add_intCast]
  omega

lemma shift_add (θ : CircleX) (k n : ℤ) (x : CircleX) :
    shift θ n (shift θ k x) = shift θ (k+n) x := by
  simp [shift,add_zsmul,add_assoc]
lemma good_shift (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (x : CircleX) :
    shift θ k x ∈ good q θ ↔ x ∈ good q θ := by
  constructor
  · intro h a
    have := h (a-k)
    simpa [shift_add] using this
  · intro h a
    simpa [shift_add] using h (k+a)

lemma floorTerm_add (q : ℕ → ℕ) (θ : CircleX) (k n : ℤ) (x : CircleX) (i : ℕ) :
    floorTerm q θ (k+n) x i = floorTerm q θ k x i + floorTerm q θ n (shift θ k x) i := by
  simp only [floorTerm,Xi_shift,floor_cocycle,Int.cast_add]

lemma exponent_add {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ) (k n : ℤ) {x : CircleX}
    (hx : x∈good q θ) :
    exponent q θ c (k+n) x = exponent q θ c n (shift θ k x)+exponent q θ c k x := by
  simp only [exponent,floorTerm_add,Int.cast_add,mul_add]
  rw [(summable_exponent c k hx).tsum_add (summable_exponent c n ((good_shift q θ k x).mpr hx)),add_comm]

lemma cocycle_add (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k n : ℤ) (x : CircleX) :
    cocycle q θ c (k+n) x = cocycle q θ c n (shift θ k x)*cocycle q θ c k x := by
  unfold cocycle
  by_cases hx : x∈good q θ
  · rw [ite_eq_left hx,ite_eq_left hx,ite_eq_left ((good_shift q θ k x).mpr hx),exponent_add c k n hx,neg_add,Real.exp_add]
  · rw [ite_eq_right hx,ite_eq_right hx,ite_eq_right (mt (good_shift q θ k x).mp hx),one_mul]

lemma measurePreserving_XiMap {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (i : ℕ) :
    MeasurePreserving (fun x : CircleX ↦ q i • x) volume volume := by
  simpa only [natCast_zsmul] using
    (Measure.measurePreserving_zsmul (volume : Measure CircleX) (by exact_mod_cast hq i : (q i:ℤ)≠0))

lemma measure_repr_lower {r : ℝ} : volume {x : CircleX | repr x < r} ≤ ENNReal.ofReal r := by
  change volume (repr ⁻¹' Iio r) ≤ _
  rw [AddCircle.add_projection_respects_measure 1 0 (measurable_repr measurableSet_Iio)]
  have hs : ((↑) : ℝ → CircleX) ⁻¹' {x | repr x < r} ∩ Ioc 0 (0+1) ⊆ Ioo 0 r ∪ {1} := by
    rintro s ⟨hs,hsI⟩
    by_cases he : s=1
    · exact Or.inr (by simpa using he)
    · left
      refine ⟨hsI.1,?_⟩
      change repr (s : CircleX)<r at hs
      rw [repr_mk,Int.fract_eq_self.mpr ⟨hsI.1.le,lt_of_le_of_ne (by simpa using hsI.2) he⟩] at hs
      exact hs
  calc
    _ ≤ volume (Ioo 0 r ∪ {1}) := measure_mono hs
    _ ≤ volume (Ioo 0 r) + volume ({1}:Set ℝ) := measure_union_le _ _
    _ = ENNReal.ofReal r := by simp

lemma measure_repr_upper {r : ℝ} : volume {x : CircleX | 1-r≤repr x} ≤ ENNReal.ofReal r := by
  change volume (repr ⁻¹' Ici (1-r)) ≤ _
  rw [AddCircle.add_projection_respects_measure 1 0 (measurable_repr measurableSet_Ici)]
  have hs : ((↑) : ℝ → CircleX) ⁻¹' {x | 1-r≤repr x} ∩ Ioc 0 (0+1) ⊆ Icc (1-r) 1 ∪ {1} := by
    rintro s ⟨hs,hsI⟩
    by_cases he : s=1
    · exact Or.inr (by simpa using he)
    · left
      refine ⟨?_,by simpa using hsI.2⟩
      change 1-r≤repr (s : CircleX) at hs
      rw [repr_mk,Int.fract_eq_self.mpr ⟨hsI.1.le,lt_of_le_of_ne (by simpa using hsI.2) he⟩] at hs
      exact hs
  calc
    _ ≤ volume (Icc (1-r) 1 ∪ {1}) := measure_mono hs
    _ ≤ volume (Icc (1-r) 1)+volume ({1}:Set ℝ) := measure_union_le _ _
    _ = ENNReal.ofReal r := by simp

lemma floorTerm_event_bound {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (θ : CircleX) (k : ℤ) (i : ℕ) :
    volume {x : CircleX | floorTerm q θ k x i≠0} ≤ ENNReal.ofReal (2 * |(k:ℝ)| * beta q θ i) := by
  let t := |(k:ℝ)| * beta q θ i
  have ht : 0≤t := mul_nonneg (abs_nonneg _) (repr_mem _).1
  have hs : {x : CircleX | floorTerm q θ k x i≠0} ⊆
      {x | Xi q i x<t} ∪ {x | 1-t≤Xi q i x} := by
    intro x hx
    by_contra! hh
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt,not_le] at hh
    apply hx
    apply Int.floor_eq_iff.mpr
    have hβ : 0 ≤ beta q θ i := (repr_mem (q i • θ)).1
    have ha : -(t) ≤ (k:ℝ)*beta q θ i := by
      dsimp [t]; nlinarith [neg_abs_le (k:ℝ)]
    have hb : (k:ℝ)*beta q θ i ≤ t := by
      dsimp [t]; nlinarith [le_abs_self (k:ℝ)]
    constructor <;> push_cast <;> linarith
  have h1 : volume {x : CircleX | Xi q i x<t} ≤ ENNReal.ofReal t := by
    rw [show {x : CircleX | Xi q i x<t} = (fun x : CircleX ↦ q i • x) ⁻¹' (repr ⁻¹' Iio t) from rfl,
      (measurePreserving_XiMap hq i).measure_preimage (measurable_repr measurableSet_Iio).nullMeasurableSet]
    exact measure_repr_lower
  have h2 : volume {x : CircleX | 1-t≤Xi q i x} ≤ ENNReal.ofReal t := by
    rw [show {x : CircleX | 1-t≤Xi q i x} = (fun x : CircleX ↦ q i • x) ⁻¹' (repr ⁻¹' Ici (1-t)) from rfl,
      (measurePreserving_XiMap hq i).measure_preimage (measurable_repr measurableSet_Ici).nullMeasurableSet]
    exact measure_repr_upper
  calc
    _ ≤ volume {x : CircleX | Xi q i x<t}+volume {x : CircleX | 1-t≤Xi q i x} :=
      (measure_mono hs).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal t+ENNReal.ofReal t := add_le_add h1 h2
    _ = _ := by rw [← ENNReal.ofReal_add ht ht]; congr 1; dsimp [t]; ring

lemma ae_good0 {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (θ : CircleX)
    (hβ : Summable (beta q θ)) : ∀ᵐ x : CircleX ∂volume, x∈good0 q θ := by
  apply ae_all_iff.mpr
  intro k
  apply ae_finite_setOfPred_mem
  apply ne_of_lt
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (floorTerm_event_bound hq θ k))
  exact (hβ.mul_left (2*|(k:ℝ)|)).tsum_ofReal_lt_top

lemma ae_good {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (θ : CircleX)
    (hβ : Summable (beta q θ)) : ∀ᵐ x : CircleX ∂volume, x∈good q θ := by
  apply ae_all_iff.mpr
  intro a
  exact (measurePreserving_add_right (volume : Measure CircleX) (a•θ)).quasiMeasurePreserving.ae (ae_good0 hq θ hβ)

end
open Set MeasureTheory Filter
open scoped BigOperators


end CircleModel

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_OrbitBounds
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uX uY uι

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical

section
open CircleModel Set Filter MeasureTheory
open scoped Topology BigOperators

lemma model_beta_sum : Summable (CircleModel.beta modelFrequency modelAngle) := by
  have he : CircleModel.beta modelFrequency modelAngle = coordinatePhase := funext model_beta
  rw [he]
  exact summable_coordinatePhase
lemma model_good_ae : ∀ᵐ x : CircleModel.CircleX, x∈modelGood :=
  CircleModel.ae_good (fun i => (frequency_pos (i+1)).ne') modelAngle model_beta_sum
lemma modelF_add (k n : ℤ) (x : CircleModel.CircleX) :
    modelF (k+n) x=modelF n (CircleModel.shift modelAngle k x)*modelF k x :=
  CircleModel.cocycle_add _ _ _ _ _ _

lemma phase_orbit (i : ℕ) (n : ℤ) :
    modelFrequency i • (n•modelAngle)=((n*coordinatePhase i:ℝ):CircleModel.CircleX) := by
  rw [smul_comm,←model_beta]
  unfold CircleModel.beta CircleModel.Xi
  rw [←zsmul_eq_mul,AddCircle.coe_zsmul,CircleModel.repr_coe]

end

open MeasureTheory Set Filter
open scoped ENNReal Topology

open CircleModel Set MeasureTheory
open scoped BigOperators


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Rounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleRounding

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

section
open Set MeasureTheory
open scoped ENNReal
lemma repr_measurable : Measurable repr := measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
lemma correction_measurable (δ c : ℝ) : Measurable (correction δ c) :=
  measurable_const.mul ((intervalRamp_continuous δ).measurable.comp repr_measurable)
lemma roundedDrop_coboundary (δ β c : ℝ) (x : X) :
    roundedDrop δ β c x-c*(Int.floor (repr x+β):ℤ)=correction δ c (x+(β:X))-correction δ c x := by
  rw [roundedDrop_formula,correction,correction]
  ring
end

open Set MeasureTheory
open scoped ENNReal
lemma correction_support {δ c : ℝ} (hδ : 0<δ) :
    {x : X | correction δ c x≠0} ⊆ {x | repr x<δ} ∪ {x | 1-δ ≤ repr x} := by
  intro x hx
  by_contra! hh
  have hh' : δ ≤ repr x ∧ repr x<1-δ := by simpa only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt,not_le] using hh
  apply hx
  rw [correction,intervalRamp_middle hδ ⟨hh'.1,hh'.2.le⟩,mul_zero]
lemma roundedDrop_support {δ β c : ℝ} (hδ : 0<δ) (hβ : 0 ≤ β) :
    {x : X | roundedDrop δ β c x≠0} ⊆ {x | repr x<δ} ∪ {x | 1-(β+δ) ≤ repr x} := by
  intro x hx
  by_contra! hh
  have hh' : δ ≤ repr x ∧ repr x<1-(β+δ) := by simpa only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt,not_le] using hh
  have ht : repr x+β∈Ico 0 1 := ⟨by linarith [hh'.1],by linarith [hh'.2]⟩
  apply hx
  rw [roundedDrop_formula,Int.floor_eq_zero_iff.mpr ht,repr_add,Int.fract_eq_self.mpr ht,
    intervalRamp_middle hδ ⟨by linarith [hh'.1],by linarith [hh'.2]⟩,
    intervalRamp_middle hδ ⟨hh'.1,by linarith [hh'.2]⟩]
  simp
lemma measure_repr_lower {r : ℝ} : volume {x : X | repr x < r} ≤ ENNReal.ofReal r := by
  change volume (repr ⁻¹' Iio r) ≤ _
  rw [AddCircle.add_projection_respects_measure 1 0 (repr_measurable measurableSet_Iio)]
  have hs : ((↑) : ℝ → X) ⁻¹' {x | repr x < r} ∩ Ioc 0 (0+1) ⊆ Ioo 0 r ∪ {1} := by
    rintro s ⟨hs,hsI⟩
    by_cases he : s=1
    · exact Or.inr (by simpa using he)
    · left
      refine ⟨hsI.1,?_⟩
      change repr (s : X)<r at hs
      rw [repr_mk,Int.fract_eq_self.mpr ⟨hsI.1.le,lt_of_le_of_ne (by simpa using hsI.2) he⟩] at hs
      exact hs
  calc
    _ ≤ volume (Ioo 0 r ∪ {1}) := measure_mono hs
    _ ≤ volume (Ioo 0 r) + volume ({1}:Set ℝ) := measure_union_le _ _
    _ = ENNReal.ofReal r := by simp

lemma measure_repr_upper {r : ℝ} : volume {x : X | 1-r≤repr x} ≤ ENNReal.ofReal r := by
  change volume (repr ⁻¹' Ici (1-r)) ≤ _
  rw [AddCircle.add_projection_respects_measure 1 0 (repr_measurable measurableSet_Ici)]
  have hs : ((↑) : ℝ → X) ⁻¹' {x | 1-r≤repr x} ∩ Ioc 0 (0+1) ⊆ Icc (1-r) 1 ∪ {1} := by
    rintro s ⟨hs,hsI⟩
    by_cases he : s=1
    · exact Or.inr (by simpa using he)
    · left
      refine ⟨?_,by simpa using hsI.2⟩
      change 1-r≤repr (s : X) at hs
      rw [repr_mk,Int.fract_eq_self.mpr ⟨hsI.1.le,lt_of_le_of_ne (by simpa using hsI.2) he⟩] at hs
      exact hs
  calc
    _ ≤ volume (Icc (1-r) 1 ∪ {1}) := measure_mono hs
    _ ≤ volume (Icc (1-r) 1)+volume ({1}:Set ℝ) := measure_union_le _ _
    _ = ENNReal.ofReal r := by simp

lemma correction_measure {δ c : ℝ} (hδ : 0<δ) : volume {x : X | correction δ c x≠0} ≤ ENNReal.ofReal (2*δ) := by
  apply (measure_mono (correction_support hδ)).trans
  apply (measure_union_le _ _).trans
  calc
    _ ≤ ENNReal.ofReal δ+ENNReal.ofReal δ := add_le_add measure_repr_lower measure_repr_upper
    _ = _ := by rw [←ENNReal.ofReal_add hδ.le hδ.le]; congr 1; ring
lemma roundedDrop_measure {δ β c : ℝ} (hδ : 0<δ) (hβ : 0 ≤ β) : volume {x : X | roundedDrop δ β c x≠0} ≤ ENNReal.ofReal (β+2*δ) := by
  apply (measure_mono (roundedDrop_support hδ hβ)).trans
  apply (measure_union_le _ _).trans
  calc
    _ ≤ ENNReal.ofReal δ+ENNReal.ofReal (β+δ) := add_le_add measure_repr_lower measure_repr_upper
    _ = _ := by rw [←ENNReal.ofReal_add hδ.le (add_nonneg hβ hδ.le)]; congr 1; ring
lemma roundedDrop_integral {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) (β c : ℝ) :
    (∫ x : X,roundedDrop δ β c x)=c*β := by
  have hq : Integrable (periodicCorrector δ) (volume : Measure X) := (periodicCorrector_continuous hδ hδ1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hσ : MeasurePreserving (fun x : X => x+(β:X)) volume volume := measurePreserving_add_right volume _
  have hq' : Integrable (fun x : X => periodicCorrector δ (x+(β:X))) volume := hσ.integrable_comp_of_integrable hq
  have hi : (∫ x : X,periodicCorrector δ (x+(β:X)))=∫ x : X,periodicCorrector δ x := hσ.integral_comp (Homeomorph.addRight (β:X)).isClosedEmbedding.measurableEmbedding _
  simp only [roundedDrop,integral_const_mul]
  have hs : Integrable (fun x : X => β+periodicCorrector δ (x+(β:X))) volume := (integrable_const β).add hq'
  rw [integral_sub hs hq,integral_add (integrable_const β) hq',hi]
  simp [AddCircle.volume_eq_smul_haarAddCircle]


end CircleRounding

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleConcentration

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

section
open Set Filter MeasureTheory
open scoped Topology ENNReal
lemma partition_sum (θ : X) (j : ℕ) (x : X) : ∑ b∈Finset.range (j+1),partition θ j b x=1 := by
  simp only [partition,←Finset.sum_div]
  exact div_self (ne_of_gt (partitionDenom_pos θ j x))
end

open Set Filter MeasureTheory
open scoped Topology ENNReal

lemma moveCorrection_continuous (θ : X) (j : ℕ) {h : X → ℝ} (hc : Continuous h) : Continuous (moveCorrection θ j h) := by
  apply Continuous.neg
  apply continuous_finsetSum
  intro b _
  apply continuous_finsetSum
  intro r _
  exact (moveTerm_continuous θ j b hc).comp (continuous_id.sub continuous_const)
lemma moveTerm_sum (θ : X) (j : ℕ) (h : X → ℝ) (x : X) : ∑ b∈Finset.range (j+1),moveTerm θ j b h x=h x := by
  simp only [moveTerm,←Finset.sum_mul,partition_sum,one_mul]
lemma moveCorrection_coboundary (θ : X) (j : ℕ) (h : X → ℝ) (x : X) :
    movedDrop θ j h x-h x=moveCorrection θ j h (x+θ)-moveCorrection θ j h x := by
  have he (r : ℕ) : x+θ-(r+1) • θ=x-r • θ := by rw [add_nsmul,one_nsmul]; abel
  have ht (b : ℕ) :
      (∑ r∈Finset.range b,moveTerm θ j b h (x-r • θ))-
      (∑ r∈Finset.range b,moveTerm θ j b h (x-(r+1) • θ))=moveTerm θ j b h x-moveTerm θ j b h (x-b • θ) := by
    rw [←Finset.sum_sub_distrib]
    simpa using Finset.sum_range_sub' (fun r => moveTerm θ j b h (x-r • θ)) b
  unfold movedDrop moveCorrection
  simp_rw [he]
  rw [←moveTerm_sum θ j h x,←Finset.sum_sub_distrib]
  calc
    _ = ∑ b∈Finset.range (j+1),-((∑ r∈Finset.range b,moveTerm θ j b h (x-r • θ))-(∑ r∈Finset.range b,moveTerm θ j b h (x-(r+1) • θ))) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [ht]
      ring
    _ = _ := by rw [Finset.sum_neg_distrib,Finset.sum_sub_distrib]; ring
lemma measurePreserving_sub (a : X) : MeasurePreserving (fun x : X => x-a) volume volume := by
  simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure X) (-a)
lemma integral_sub_circle (a : X) (f : X → ℝ) : (∫ x : X, f (x-a))=∫ x : X,f x := by
  have he : MeasurableEmbedding (fun x : X => x-a) := by
    convert (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding using 1
    ext x; simp [sub_eq_add_neg]
  exact (measurePreserving_sub a).integral_comp he f
lemma moveTerm_integrable (θ : X) (j b : ℕ) {h : X → ℝ} (hc : Continuous h) :
    Integrable (moveTerm θ j b h) (volume : Measure X) :=
  (moveTerm_continuous θ j b hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma movedTerm_integrable (θ : X) (j b : ℕ) {h : X → ℝ} (hc : Continuous h) :
    Integrable (fun x : X => moveTerm θ j b h (x-b • θ)) volume :=
  ((moveTerm_continuous θ j b hc).comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma movedDrop_integral (θ : X) (j : ℕ) {h : X → ℝ} (hc : Continuous h) :
    (∫ x : X,movedDrop θ j h x)=∫ x : X,h x := by
  change (∫ x : X, ∑ b ∈ Finset.range (j+1), moveTerm θ j b h (x-b • θ))= _
  rw [integral_finsetSum _ (fun b _ => movedTerm_integrable θ j b hc)]
  calc
    _ = ∑ b ∈ Finset.range (j+1), ∫ x : X, moveTerm θ j b h x :=
      Finset.sum_congr rfl (fun b _ => integral_sub_circle (b • θ) (moveTerm θ j b h))
    _ = ∫ x : X, ∑ b ∈ Finset.range (j+1), moveTerm θ j b h x :=
      (integral_finsetSum _ (fun b _ => moveTerm_integrable θ j b hc)).symm
    _ = ∫ x : X, h x := integral_congr_ae (Eventually.of_forall (moveTerm_sum θ j h))
lemma moveCorrection_support (θ : X) (j : ℕ) (h : X → ℝ) :
    {x | moveCorrection θ j h x≠0} ⊆ ⋃ r∈Finset.range j,{x : X | h (x-(r+1) • θ)≠0} := by
  intro x hx
  by_contra hh
  have hh' : ∀ r<j,h (x-(r+1) • θ)=0 := by simpa only [mem_iUnion,Finset.mem_range,mem_ofPred_eq,not_exists,not_and,not_not] using hh
  apply hx
  unfold moveCorrection
  rw [neg_eq_zero,Finset.sum_eq_zero]
  intro b hb
  apply Finset.sum_eq_zero
  intro r hr
  have hrj : r<j := by simp only [Finset.mem_range] at hr hb; omega
  simp [moveTerm,hh' r hrj]
lemma moveCorrection_measure (θ : X) (j : ℕ) {h : X → ℝ} (hm : Measurable h) :
    volume {x : X | moveCorrection θ j h x≠0} ≤ (j:ℝ≥0∞)*volume {x : X | h x≠0} := by
  apply (measure_mono (moveCorrection_support θ j h)).trans
  apply (measure_biUnion_finset_le _ _).trans
  have hs (r : ℕ) : volume {x : X | h (x-(r+1) • θ)≠0}=volume {x : X | h x≠0} := by
    have hσ : MeasurePreserving (fun x : X => x-(r+1) • θ) volume volume := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume:Measure X) (-((r+1) • θ))
    change volume ((fun x : X => x-(r+1) • θ) ⁻¹' {x : X | h x≠0}) = _
    exact hσ.measure_preimage (hm (measurableSet_singleton 0).compl).nullMeasurableSet
  simp only [hs,Finset.sum_const,Finset.card_range,nsmul_eq_mul,le_refl]


end CircleConcentration

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ContinuousWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

lemma negativeLog_concentratedWeight {X : Type uX} [TopologicalSpace X]
    (H : ℕ → X → ℝ) (z : X) (hH : ∀ i x, 0 ≤ H i x)
    (hlocal : LocallyFiniteOff H z)
    (hdiv : ∀ B : ℝ, ∃ s : Finset ℕ, B < ∑ i ∈ s, H i z) (x : X) :
    negativeLog (concentratedWeight H z x) = ∑' i, ENNReal.ofReal (H i x) := by
  classical
  by_cases hx : x = z
  · subst x
    rw [concentratedWeight_self, negativeLog, ite_eq_left rfl]
    symm
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro b
    obtain ⟨s,hs⟩ := hdiv b
    calc
      (b : ℝ≥0∞) ≤ ENNReal.ofReal (∑ i ∈ s, H i z) := by
        simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hs.le
      _ = ∑ i ∈ s, ENNReal.ofReal (H i z) := ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hH i z)
      _ ≤ ∑' i, ENNReal.ofReal (H i z) := ENNReal.sum_le_tsum s
  · rw [negativeLog, ite_eq_right ((concentratedWeight_eq_zero H z x).not.mpr hx),
      concentratedWeight, ite_eq_right hx, Real.log_exp, neg_neg]
    exact ENNReal.ofReal_tsum_of_nonneg (fun i ↦ hH i x)
      (summable_of_hasFiniteSupport (finite_support_of_locallyFiniteOff H z hlocal hx))

theorem lintegral_negativeLog_concentratedWeight {X : Type uX} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    (H : ℕ → X → ℝ) (z : X) (hc : ∀ i, Continuous (H i)) (hH : ∀ i x, 0 ≤ H i x)
    (hlocal : LocallyFiniteOff H z)
    (hdiv : ∀ B : ℝ, ∃ s : Finset ℕ, B < ∑ i ∈ s, H i z) :
    (∫⁻ x, negativeLog (concentratedWeight H z x) ∂μ) =
      ∑' i, ∫⁻ x, ENNReal.ofReal (H i x) ∂μ := by
  simp_rw [negativeLog_concentratedWeight H z hH hlocal hdiv]
  exact lintegral_tsum (fun i ↦ ((hc i).measurable.ennreal_ofReal).aemeasurable)

lemma ae_finite_support_of_support_measure_sum {X : Type uX} [MeasurableSpace X]
    (μ : Measure X) (w : ℕ → X → ℝ)
    (hw : (∑' i, μ {x | w i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i ↦ w i x)).Finite :=
  ae_finite_setOfPred_mem hw

theorem concentrated_coboundary {X : Type uX} [MeasurableSpace X]
    (μ : Measure X) (σ : X → X) (hσ : MeasurePreserving σ μ μ)
    (H G w : ℕ → X → ℝ) (z : X) (hz : μ {z} = 0)
    (hwm : ∀ i, Measurable (w i))
    (hG : (∑' i, μ {x | G i x ≠ 0}) ≠ ∞)
    (hw : (∑' i, μ {x | w i x ≠ 0}) ≠ ∞)
    (hid : ∀ᵐ x ∂μ, ∀ i, H i x - G i x = w i (σ x) - w i x) :
    ∃ a : X → ℝ, Measurable a ∧ (∀ x, 0 < a x) ∧
      ∀ᵐ x ∂μ, concentratedWeight H z x =
        Real.exp (-∑' i, G i x) * a x / a (σ x) := by
  classical
  let b : X → ℝ := fun x ↦ ∑' i, w i x
  let a : X → ℝ := fun x ↦ Real.exp (b x)
  refine ⟨a, (Measurable.tsum hwm).exp, (fun x ↦ Real.exp_pos _), ?_⟩
  have hfin := ae_finite_support_of_support_measure_sum μ w hw
  have hfinσ := hσ.quasiMeasurePreserving.ae hfin
  have hfinG := ae_finite_support_of_support_measure_sum μ G hG
  have hne : ∀ᵐ x ∂μ, x ≠ z := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hz
  filter_upwards [hfin, hfinσ, hfinG, hid, hne] with x hx hxσ hxG hix hxz
  have hsw : Summable (fun i ↦ w i x) := summable_of_hasFiniteSupport hx
  have hswσ : Summable (fun i ↦ w i (σ x)) := summable_of_hasFiniteSupport hxσ
  have hsG : Summable (fun i ↦ G i x) := summable_of_hasFiniteSupport hxG
  have he : (fun i ↦ H i x) = (fun i ↦ G i x + (w i (σ x) - w i x)) := by
    funext i
    linarith [hix i]
  have ht : (∑' i, H i x) = (∑' i, G i x) + (b (σ x) - b x) := by
    rw [he, hsG.tsum_add (hswσ.sub hsw), hswσ.tsum_sub hsw]
  rw [concentratedWeight, ite_eq_right hxz, ht]
  change Real.exp _ = Real.exp _ * Real.exp (b x) / Real.exp (b (σ x))
  rw [← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring



end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_LogarithmicDrops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uι

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

section
open CircleModel CircleRounding CircleConcentration ContinuousCircleWeight
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

lemma smoothCorrection_measurable (j : ℕ) (i : Fin (blockLength j)) : Measurable (smoothCorrection j i) :=
  (correction_measurable _ _).comp (continuous_id.nsmul _).measurable
lemma totalCorrection_measurable (j : ℕ) (i : Fin (blockLength j)) : Measurable (totalCorrection j i) :=
  (smoothCorrection_measurable j i).add (moveCorrection_continuous _ _ (smoothDrop_continuous j i)).measurable
lemma blockW_measurable (j : ℕ) : Measurable (blockW j) := Finset.measurable_sum _ (fun i _ => totalCorrection_measurable j i)

lemma smoothDrop_coboundary (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) :
    smoothDrop j i x-integerDrop j i x=smoothCorrection j i (x+modelAngle)-smoothCorrection j i x := by
  have hp := phase_orbit (blocks.equiv ⟨j,i⟩) 1
  simp only [one_smul,Int.cast_one,one_mul] at hp
  unfold smoothDrop integerDrop smoothCorrection floorTerm
  rw [model_beta]
  simp only [Int.cast_one,one_mul]
  change roundedDrop _ _ _ _ - dropSize j * (⌊CircleRounding.repr _+_⌋:ℝ)=_
  rw [roundedDrop_coboundary,nsmul_add,hp]
lemma totalCorrection_coboundary (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) :
    concentratedDrop j i x-integerDrop j i x=totalCorrection j i (x+modelAngle)-totalCorrection j i x := by
  have h1 := smoothDrop_coboundary j i x
  have h2 := moveCorrection_coboundary modelAngle j (smoothDrop j i) x
  unfold totalCorrection concentratedDrop
  linarith
lemma block_coboundary (j : ℕ) (x : CircleModel.CircleX) :
    blockH j x-blockG j x=blockW j (x+modelAngle)-blockW j x := by
  unfold blockH blockG blockW
  simp only [←Finset.sum_sub_distrib,totalCorrection_coboundary]

lemma smoothDrop_integral (j : ℕ) (i : Fin (blockLength j)) :
    (∫ x : CircleModel.CircleX,smoothDrop j i x)=dropSize j*coordinatePhase (blocks.equiv ⟨j,i⟩) := by
  have hm := measurePreserving_XiMap (q:=modelFrequency) (fun i => (frequency_pos (i+1)).ne') (blocks.equiv ⟨j,i⟩)
  let f := roundedDrop (roundingWidth j) (coordinatePhase (blocks.equiv ⟨j,i⟩)) (dropSize j)
  have hf : AEStronglyMeasurable f volume := (roundedDrop_continuous (roundingWidth_pos j) (roundingWidth_lt_one j) _ _).aestronglyMeasurable
  calc
    _ = ∫ x : CircleModel.CircleX,f x ∂Measure.map (fun x => modelFrequency (blocks.equiv ⟨j,i⟩) • x) volume := by
      rw [integral_map hm.aemeasurable (by rwa [hm.map_eq])]; rfl
    _ = ∫ x : CircleModel.CircleX,f x := by rw [hm.map_eq]
    _ = _ := roundedDrop_integral (roundingWidth_pos j) (roundingWidth_lt_one j) _ _
lemma blockH_integral_lower (j : ℕ) : (polynomialWindow j:ℝ)≤∫ x : CircleModel.CircleX,blockH j x := by
  have he : (∫ x : CircleModel.CircleX,blockH j x)=∑ i : Fin (blockLength j),dropSize j*coordinatePhase (blocks.equiv ⟨j,i⟩) := by
    unfold blockH
    rw [integral_finsetSum _ (fun i _ => (concentratedDrop_continuous j i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro i _
    exact (movedDrop_integral modelAngle j (smoothDrop_continuous j i)).trans (smoothDrop_integral j i)
  rw [he]
  simpa only [coordinateDrop,block_number_equiv] using phase_drop_block_lower j
end
open CircleModel CircleRounding CircleConcentration ContinuousCircleWeight
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

lemma measure_nonzero_sum {ι : Type uι} [Fintype ι] (f : ι → CircleModel.CircleX → ℝ) :
    volume {x | (∑ i,f i x)≠0} ≤ ∑ i,volume {x | f i x≠0} := by
  classical
  apply (measure_mono (show {x | (∑ i,f i x)≠0} ⊆ ⋃ i,{x | f i x≠0} from ?_)).trans (measure_iUnion_fintype_le _ _)
  intro x hx
  by_contra! hh
  simp only [mem_iUnion,mem_ofPred_eq,not_exists,not_not] at hh
  exact hx (Finset.sum_eq_zero (fun i _ => hh i))
lemma measure_nonzero_add (f g : CircleModel.CircleX → ℝ) :
    volume {x | f x+g x≠0}≤volume {x | f x≠0}+volume {x | g x≠0} := by
  apply (measure_mono (show {x | f x+g x≠0}⊆{x | f x≠0}∪{x | g x≠0} from ?_)).trans (measure_union_le _ _)
  intro x hx
  by_contra! hh
  simp only [mem_union,mem_ofPred_eq,not_or,not_not] at hh
  exact hx (by rw [hh.1,hh.2,add_zero])
lemma smoothCorrection_measure (j : ℕ) (i : Fin (blockLength j)) :
    volume {x | smoothCorrection j i x≠0}≤ENNReal.ofReal (2*roundingWidth j) := by
  have hm := measurePreserving_XiMap (q:=modelFrequency) (fun i => (frequency_pos (i+1)).ne') (blocks.equiv ⟨j,i⟩)
  change volume ((fun x : CircleModel.CircleX => modelFrequency (blocks.equiv ⟨j,i⟩) • x) ⁻¹' {x | correction (roundingWidth j) (dropSize j) x≠0}) ≤ _
  have he := hm.measure_preimage ((correction_measurable (roundingWidth j) (dropSize j)) (measurableSet_singleton 0).compl).nullMeasurableSet
  change volume ((fun x : CircleModel.CircleX => modelFrequency (blocks.equiv ⟨j,i⟩) • x) ⁻¹' {x | correction (roundingWidth j) (dropSize j) x≠0}) = _ at he
  exact he.le.trans (correction_measure (roundingWidth_pos j))
lemma smoothDrop_measure (j : ℕ) (i : Fin (blockLength j)) :
    volume {x | smoothDrop j i x≠0}≤ENNReal.ofReal (coordinatePhase (blocks.equiv ⟨j,i⟩)+2*roundingWidth j) := by
  have hm := measurePreserving_XiMap (q:=modelFrequency) (fun i => (frequency_pos (i+1)).ne') (blocks.equiv ⟨j,i⟩)
  change volume ((fun x : CircleModel.CircleX => modelFrequency (blocks.equiv ⟨j,i⟩) • x) ⁻¹' {x | roundedDrop (roundingWidth j) (coordinatePhase (blocks.equiv ⟨j,i⟩)) (dropSize j) x≠0}) ≤ _
  have he := hm.measure_preimage (((roundedDrop_continuous (roundingWidth_pos j) (roundingWidth_lt_one j) (coordinatePhase (blocks.equiv ⟨j,i⟩)) (dropSize j)).measurable) (measurableSet_singleton 0).compl).nullMeasurableSet
  change volume ((fun x : CircleModel.CircleX => modelFrequency (blocks.equiv ⟨j,i⟩) • x) ⁻¹' {x | roundedDrop (roundingWidth j) (coordinatePhase (blocks.equiv ⟨j,i⟩)) (dropSize j) x≠0}) = _ at he
  exact he.le.trans (roundedDrop_measure (roundingWidth_pos j) (coordinatePhase_pos _).le)
lemma integerDrop_measure (j : ℕ) (i : Fin (blockLength j)) :
    volume {x | integerDrop j i x≠0}≤ENNReal.ofReal (2*coordinatePhase (blocks.equiv ⟨j,i⟩)) := by
  have hs : {x | integerDrop j i x≠0}⊆{x | floorTerm modelFrequency modelAngle 1 x (blocks.equiv ⟨j,i⟩)≠0} := by
    intro x hx hh
    exact hx (by simp [integerDrop,hh])
  apply (measure_mono hs).trans
  simpa only [model_beta,Int.cast_one,abs_one,mul_one] using floorTerm_event_bound (q:=modelFrequency) (fun i => (frequency_pos (i+1)).ne') modelAngle 1 (blocks.equiv ⟨j,i⟩)
lemma totalCorrection_measure (j : ℕ) (i : Fin (blockLength j)) :
    volume {x | totalCorrection j i x≠0}≤ENNReal.ofReal (2*roundingWidth j+(j:ℝ)*(coordinatePhase (blocks.equiv ⟨j,i⟩)+2*roundingWidth j)) := by
  have hδ := (roundingWidth_pos j).le
  have hβ := (coordinatePhase_pos (blocks.equiv ⟨j,i⟩)).le
  calc
    _ ≤ volume {x | smoothCorrection j i x≠0}+volume {x | moveCorrection modelAngle j (smoothDrop j i) x≠0} := measure_nonzero_add _ _
    _ ≤ ENNReal.ofReal (2*roundingWidth j)+(j:ℝ≥0∞)*ENNReal.ofReal (coordinatePhase (blocks.equiv ⟨j,i⟩)+2*roundingWidth j) :=
      add_le_add (smoothCorrection_measure j i) ((moveCorrection_measure modelAngle j (smoothDrop_continuous j i).measurable).trans (mul_le_mul_right (smoothDrop_measure j i) _))
    _ = _ := by
      rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg j),←ENNReal.ofReal_add (by positivity : 0≤2*roundingWidth j) (by positivity)]

lemma blockG_measure (j : ℕ) : volume {x | blockG j x≠0}≤ENNReal.ofReal (4/(polynomialWindow j:ℝ)) := by
  calc
    _ ≤ ∑ i : Fin (blockLength j),volume {x | integerDrop j i x≠0} := measure_nonzero_sum _
    _ ≤ ∑ i : Fin (blockLength j),ENNReal.ofReal (2*coordinatePhase (blocks.equiv ⟨j,i⟩)) := Finset.sum_le_sum (fun i _ => integerDrop_measure j i)
    _ = ENNReal.ofReal (2*∑ i : Fin (blockLength j),coordinatePhase (blocks.equiv ⟨j,i⟩)) := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (by norm_num) (coordinatePhase_pos _).le)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      calc
        _ ≤ 2*(2/(polynomialWindow j:ℝ)) := mul_le_mul_of_nonneg_left (sum_phase_block j) (by norm_num)
        _ = _ := by ring)
lemma blockW_measure (j : ℕ) : volume {x | blockW j x≠0}≤ENNReal.ofReal ((1+3*(j:ℝ))/(polynomialWindow j:ℝ)) := by
  have hm : 0<(blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
  have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
  have hs := sum_phase_block j
  calc
    _ ≤ ∑ i : Fin (blockLength j),volume {x | totalCorrection j i x≠0} := measure_nonzero_sum _
    _ ≤ ∑ i : Fin (blockLength j),ENNReal.ofReal (2*roundingWidth j+(j:ℝ)*(coordinatePhase (blocks.equiv ⟨j,i⟩)+2*roundingWidth j)) := Finset.sum_le_sum (fun i _ => totalCorrection_measure j i)
    _ = ENNReal.ofReal (∑ i : Fin (blockLength j),(2*roundingWidth j+(j:ℝ)*(coordinatePhase (blocks.equiv ⟨j,i⟩)+2*roundingWidth j))) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := (coordinatePhase_pos (blocks.equiv ⟨j,i⟩)).le; have := (roundingWidth_pos j).le; positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum]
      have hn : (0:ℝ)≤j := Nat.cast_nonneg j
      have hh := mul_le_mul_of_nonneg_left hs hn
      have he : (blockLength j:ℝ)*(2*roundingWidth j)=1/(5*(polynomialWindow j:ℝ)) := by unfold roundingWidth; field_simp; ring
      rw [show (blockLength j:ℝ)*((j:ℝ)*(2*roundingWidth j))=(j:ℝ)*((blockLength j:ℝ)*(2*roundingWidth j)) by ring,he]
      calc
        _ ≤ 1/(5*(polynomialWindow j:ℝ))+(j:ℝ)*(2/(polynomialWindow j:ℝ))+(j:ℝ)*(1/(5*(polynomialWindow j:ℝ))) := by linarith
        _ = (1+11*(j:ℝ))/(5*(polynomialWindow j:ℝ)) := by ring
        _ ≤ _ := (div_le_div_iff₀ (by positivity : 0<5*(polynomialWindow j:ℝ)) hK).mpr (by nlinarith)

lemma summable_blockW_bound : Summable (fun j : ℕ => (1+3*(j:ℝ))/(polynomialWindow j:ℝ)) := by
  have hgeom : Summable (fun j : ℕ => (j:ℝ)*(1/2:ℝ)^j) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1/2:ℝ)‖<1)
  have hs : Summable (fun j : ℕ => (1+3*(j:ℝ))*((1/(polynomialWindow 0:ℝ))*(1/2:ℝ)^j)) := by
    have h1 := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).mul_left (1/(polynomialWindow 0:ℝ))
    have h2 := hgeom.mul_left (3/(polynomialWindow 0:ℝ))
    apply (h1.add h2).congr
    intro j
    ring
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ hs
  intro j
  have hh := mul_le_mul_of_nonneg_left (window_inverse_bound 0 j) (show 0≤1+3*(j:ℝ) by positivity)
  simpa only [Nat.zero_add,mul_one_div] using hh
lemma blockG_support_sum : (∑' j,volume {x | blockG j x≠0})≠∞ := by
  apply ne_of_lt ((ENNReal.tsum_le_tsum blockG_measure).trans_lt _)
  have hs : Summable (fun j : ℕ => 4/(polynomialWindow j:ℝ)) := by
    simpa only [Nat.zero_add,mul_one_div] using (summable_window_inverse 0).mul_left 4
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs]
  exact ENNReal.ofReal_lt_top
lemma blockW_support_sum : (∑' j,volume {x | blockW j x≠0})≠∞ := by
  apply ne_of_lt ((ENNReal.tsum_le_tsum blockW_measure).trans_lt _)
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) summable_blockW_bound]
  exact ENNReal.ofReal_lt_top


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace CircleSampling

section
open CircleModel CircleRounding CircleConcentration ContinuousCircleWeight
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

lemma finalWeight_bounds (x : CircleModel.CircleX) : 0 ≤ finalWeight x ∧ finalWeight x≤1 :=
  concentratedWeight_bounds _ _ blockH_nonneg x
lemma finalWeight_zero (x : CircleModel.CircleX) : finalWeight x=0 ↔ x=0 := concentratedWeight_eq_zero _ _ _
lemma finalWeight_log : (∫⁻ x : CircleModel.CircleX,negativeLog (finalWeight x))=∞ := by
  change (∫⁻ x : CircleModel.CircleX,negativeLog (concentratedWeight blockH 0 x))=_
  rw [lintegral_negativeLog_concentratedWeight volume blockH 0 blockH_continuous blockH_nonneg blockH_locallyFinite blockH_diverges_zero]
  apply top_unique
  calc
    ∞ = ∑' _j : ℕ,(1:ℝ≥0∞) := (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro j
      have hi : Integrable (blockH j) (volume : Measure CircleModel.CircleX) := (blockH_continuous j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (blockH_nonneg j))]
      rw [←ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have hK : (1:ℝ)≤polynomialWindow j := by exact_mod_cast polynomialWindow_pos j
      exact hK.trans (blockH_integral_lower j)
lemma blockG_exponent {x : CircleModel.CircleX} (hx : x∈modelGood) :
    (∑' j,blockG j x)=exponent modelFrequency modelAngle coordinateDrop 1 x := by
  let f : ℕ → ℝ := fun i => coordinateDrop i*(floorTerm modelFrequency modelAngle 1 x i:ℝ)
  have hs : Summable f := summable_exponent coordinateDrop 1 hx
  calc
    _ = ∑' j,∑' i : Fin (blocks.m j),f (blocks.equiv ⟨j,i⟩) := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _
      change dropSize j*_ = dropSize (coordinateBlock (blocks.equiv ⟨j,i⟩))*_
      rw [block_number_equiv]
    _ = ∑' ji : Σ j,Fin (blocks.m j),f (blocks.equiv ji) := (blocks.equiv.summable_iff.mpr hs).tsum_sigma.symm
    _ = _ := blocks.equiv.tsum_eq f
lemma finalWeight_coboundary : ∃ a : CircleModel.CircleX → ℝ, Measurable a ∧ (∀ x,0<a x) ∧
    ∀ᵐ x : CircleModel.CircleX, finalWeight x=modelWeight x*a x/a (x+modelAngle) := by
  have h0 : volume ({(0:CircleModel.CircleX)} : Set CircleModel.CircleX)=0 := by
    rw [←Metric.closedBall_zero,AddCircle.volume_closedBall]
    norm_num
  obtain ⟨a,ham,hapos,ha⟩ := concentrated_coboundary (volume:Measure CircleModel.CircleX)
    (fun x => x+modelAngle) (measurePreserving_add_right volume modelAngle) blockH blockG blockW 0 h0
    blockW_measurable blockG_support_sum blockW_support_sum (Eventually.of_forall (fun x j => block_coboundary j x))
  refine ⟨a,ham,hapos,?_⟩
  filter_upwards [ha,model_good_ae] with x hax hx
  change concentratedWeight blockH 0 x=_
  rw [hax,blockG_exponent hx]
  simp only [modelWeight,modelF,cocycle,ite_eq_left (show x ∈ good modelFrequency modelAngle from hx)]
end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ComplexInnerProductSpace ENNReal

lemma modelBorel_field (x : CircleX) : borelWeightedField modelAngle modelBorel x=
    fiberCocycleShift (fun k => modelF k x) (fun k => modelF_pos k x) (modelF_antitone x) := by
  ext u k
  change fiberShift 1 (realPiField modelAngle modelBorel x u) k=_
  rw [fiberShift_apply,realPiField_apply,fiberCocycleShift_apply]
  congr 1
  apply congrArg Complex.ofReal
  change modelF 1 (x+(k-1)•modelAngle)=modelF k x/modelF (k-1) x
  apply (eq_div_iff (ne_of_gt (modelF_pos _ _))).mpr
  simpa only [CircleModel.shift,sub_add_cancel] using (modelF_add (k-1) 1 x).symm

lemma modelAngle_ergodic : Ergodic (fun x : CircleX => x+modelAngle) AddCircle.haarAddCircle := by
  rw [Sampling.haarAddCircle_one_eq_volume]
  apply AddCircle.ergodic_add_right.mpr
  apply AddCircle.denseRange_zsmul_iff.mp
  simpa only [div_one,modelAngle] using (AddCircle.denseRange_zsmul_coe_iff (p:=(1:ℝ))).mpr (by simpa using parameterAngle_spec.2.2.1)

local instance instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert_3_rca4273_1 : MeasurableSpace FiberHilbert := borel FiberHilbert
theorem modelOperator_no_projection (p : CircleFiberOperator) (hp : IsStarProjection p)
    (hcomm : ∀ B∈fiberCommutant parameterAngle,Commute p B)
    (hinv : (1-p)*(fiberShiftL2 1*realPi modelAngle modelBorel)*p=0) : p=0 ∨ p=1 := by
  by_cases hp0 : p=0
  · exact Or.inl hp0
  by_cases hp1 : p=1
  · exact Or.inr hp1
  exfalso
  obtain ⟨P,hPproj,hPbound,hPmeas,hP,hcov⟩ := extract_projection_field parameterAngle p hp hcomm
  let Q : ModelProjectionField :=
    { p := P
      projection := hPproj
      norm_le := hPbound
      measurable := hPmeas
      invariant := by
        have h := decomposable_invariant p P hP modelAngle modelBorel hinv
        simpa only [Sampling.haarAddCircle_one_eq_volume,modelBorel_field] using h
      covariance := by
        intro n
        simpa only [Sampling.haarAddCircle_one_eq_volume,CircleModel.shift,modelAngle] using hcov n }
  apply model_no_strict_projection Q
  have hs := borel_invariant_diagonal_strict parameterAngle modelAngle_ergodic p P hP hPproj hcov modelBorel
    (fun x => ne_of_gt (modelWeight_bounds x).1) hinv hp0 hp1
  simpa only [Sampling.haarAddCircle_one_eq_volume,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one,
    modelDiagonal,modelColumn,Q] using hs

theorem continuousOperator_no_projection (p : CircleFiberOperator) (hp : IsStarProjection p)
    (hcomm : ∀ B∈fiberCommutant parameterAngle,Commute p B)
    (hinv : (1-p)*(fiberShiftL2 1*realPi modelAngle (RealBorel.ofContinuous finalWeight))*p=0) : p=0 ∨ p=1 := by
  by_cases hp0 : p=0
  · exact Or.inl hp0
  by_cases hp1 : p=1
  · exact Or.inr hp1
  exfalso
  obtain ⟨a,ham,hapos,ha⟩ := finalWeight_coboundary
  have he : ∀ᵐ x ∂AddCircle.haarAddCircle,RealBorel.ofContinuous finalWeight x*a (x+modelAngle)=modelBorel x*a x := by
    rw [Sampling.haarAddCircle_one_eq_volume]
    filter_upwards [ha] with x hx
    exact (eq_div_iff (ne_of_gt (hapos _))).mp hx
  obtain ⟨q,hq,hqc,hq0,hq1,hqi⟩ := borel_weight_transport parameterAngle (RealBorel.ofContinuous finalWeight) modelBorel a ham hapos he p hp hcomm hp0 hp1 hinv
  exact (modelOperator_no_projection q hq hqc hqi).elim hq0 hq1
end CircleSampling

namespace ContinuousCircleWeight

section
open MeasureTheory
open scoped ENNReal ComplexInnerProductSpace

lemma regular_isTracialRotation (θ : ℝ) :
    IsTracialRotation θ regularU (regularV (rotationScalar θ)) regularVacuum where
  relation := regular_relation (rotationScalar θ)
  moments := regular_moments (rotationScalar θ)
  cyclic := regular_cyclic (rotationScalar θ)

lemma fiberConjugacy_cfc (θ : ℝ) (f : C(CircleX,ℝ)) :
    fiberConjugacy (cfc (circleFunction f) (regularV (rotationScalar θ) : RegularOperator)) =
      realPi (θ:CircleX) (RealBorel.ofContinuous f) := by
  rw [realPi_continuous]
  have h := fiberConjugacy.toStarAlgHom.map_cfc (circleFunction f)
    (regularV (rotationScalar θ) : RegularOperator)
    ((circleFunction_continuousOn f).mono (Unitary.spectrum_subset_circle _))
    (StarAlgEquiv.isometry fiberConjugacy).continuous
  change fiberConjugacy _ = cfc (circleFunction f)
    (fiberConjugacy (regularV (rotationScalar θ) : RegularOperator)) at h
  rw [h,fiberConjugacy_V]
  exact (circle_cfc_hom (continuousPiHom (θ:CircleX)) (continuous_continuousPiHom _) f).symm

lemma fiberConjugacy_weighted (θ : ℝ) (f : C(CircleX,ℝ)) :
    fiberConjugacy (weightedRotation regularU (regularV (rotationScalar θ)) f) =
      fiberShiftL2 1 * realPi (θ:CircleX) (RealBorel.ofContinuous f) := by
  rw [weightedRotation,map_mul,fiberConjugacy_U,fiberConjugacy_cfc]

end

open MeasureTheory CircleSampling
open scoped ENNReal ComplexInnerProductSpace

theorem main_theorem_oai : MainStatement := by
  refine ⟨parameterAngle, finalWeight, regularU, regularV (rotationScalar parameterAngle),
    regularVacuum, parameterAngle_spec.1, parameterAngle_spec.2.1,
    parameterAngle_spec.2.2.1, regular_isTracialRotation parameterAngle,
    finalWeight_bounds, ⟨0, finalWeight_zero⟩, finalWeight_log, ?_⟩
  intro p hp hppr hinv
  have hi : (1-fiberConjugacy p)*
      (fiberShiftL2 1*realPi modelAngle (RealBorel.ofContinuous finalWeight))*fiberConjugacy p=0 := by
    have h := congrArg fiberConjugacy hinv
    simpa only [map_mul,map_sub,map_one,map_zero,fiberConjugacy_weighted,modelAngle] using h
  have hq := continuousOperator_no_projection (fiberConjugacy p) (hppr.map fiberConjugacy)
    (fiber_commutes_of_regularAlgebra parameterAngle p hp) hi
  rcases hq with hq|hq
  · left
    apply fiberConjugacy.injective
    change fiberConjugacy p=fiberConjugacy 0
    simpa only [map_zero] using hq
  · right
    apply fiberConjugacy.injective
    change fiberConjugacy p=fiberConjugacy 1
    simpa only [map_one] using hq

end ContinuousCircleWeight

end

end OAI
end

theorem solution : type_of% @OAI.ContinuousCircleWeight.main_theorem_oai := @OAI.ContinuousCircleWeight.main_theorem_oai
