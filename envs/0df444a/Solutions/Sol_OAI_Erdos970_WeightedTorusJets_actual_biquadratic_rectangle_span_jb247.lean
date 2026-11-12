-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.actual_biquadratic_rectangle_span_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:58:28.082823+00:00
-- url     : https://prove2.me/submissions/49cd6b69-1cc7-4e19-a46f-8feca637718a

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J007
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_Geometry_derivativeStageIdeal_graded_length_lower_jb247
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_Geometry_torus_prime_residue_logarithmicForm_ne_zero_jb247
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_Geometry_torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247

section
-- module Solutions.OAIQ247_JB.Compat
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ConeMap
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

theorem X_none_not_mem_coneIdeal (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    X none ∉ coneIdeal p := by
  simpa only [coneIdeal, RingHom.mem_ker, coneMap_X_none] using
    (Polynomial.X_ne_zero : (Polynomial.X : Polynomial (MvPolynomial σ K ⧸ p)) ≠ 0)

end WeightedTorusJets.Geometry

end

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_NormalizationPresentationLocalEquiv
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section

open Module TensorProduct

namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R] (I p : Ideal R) [p.IsPrime]

variable {K : Type*} [Field K]

theorem regular_localization_component [IsRegularRing R]
    (M : Submonoid R) (q : Ideal (Localization M)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).toRingEquiv

theorem regular_localization_component_cotangent_dim [IsRegularRing R]
    (M : Submonoid R) (q : Ideal (Localization M)) [q.IsPrime] :
    (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) : WithBot ℕ∞) =
        (q.comap (algebraMap R (Localization M))).height := by
  have := regular_localization_component M q
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height
    (q.comap (algebraMap R (Localization M))) (Localization.AtPrime q)]
  exact (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp inferInstance

theorem polynomial_component_height_bounds
    (p : Ideal (MvPolynomial (Fin 4) K)) [p.IsPrime]
    {F : MvPolynomial (Fin 4) K} (hF : F ≠ 0) (hFp : F ∈ p) :
    1 ≤ p.height ∧ p.height ≤ 4 := by
  constructor
  · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hp
    apply hF
    simpa only [hp, Ideal.mem_bot] using hFp
  · have h := p.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
    exact WithBot.coe_le_coe.mp (by simpa using h)

theorem localization_component_cotangent_bounds
    (M : Submonoid (MvPolynomial (Fin 4) K))
    (p : Ideal (Localization M)) [p.IsPrime]
    {F : MvPolynomial (Fin 4) K} (hF : F ≠ 0)
    (hFp : algebraMap (MvPolynomial (Fin 4) K) (Localization M) F ∈ p) :
    1 ≤ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.CotangentSpace (Localization.AtPrime p)) ∧
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.CotangentSpace (Localization.AtPrime p)) ≤ 4 := by
  have hb := polynomial_component_height_bounds
    (p.comap (algebraMap (MvPolynomial (Fin 4) K) (Localization M))) hF hFp
  have hd := regular_localization_component_cotangent_dim M p
  have hd' := WithBot.coe_injective hd
  rw [← hd'] at hb
  constructor
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2

end WeightedTorusJets.Geometry

end
end
end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ParameterIdeal
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section OriginalSourceGeometryOverlay
noncomputable section
open Module
open CategoryTheory _root_.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open CategoryTheory _root_.AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
open CategoryTheory _root_.AlgebraicGeometry
open _root_.Polynomial IsLocalRing TensorProduct

open TensorProduct IsLocalRing

open scoped TensorProduct

namespace WeightedTorusJets.Geometry



variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

theorem localizeDerivation_algebraMap (M : Submonoid S) [IsLocalization M T]
    (D : Derivation R S S) (s : S) :
    localizeDerivation M D (algebraMap S T s) = algebraMap S T (D s) := by
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  change ((Algebra.ofId S T).toLinearMap.compDer D).liftKaehlerDifferential.liftBaseChange T
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
      (KaehlerDifferential.D R T (algebraMap S T s))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

end WeightedTorusJets.Geometry

open scoped BigOperators

end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LogarithmicForm
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

noncomputable section
open Module
open CategoryTheory _root_.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open CategoryTheory _root_.AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
open CategoryTheory _root_.AlgebraicGeometry
open _root_.Polynomial IsLocalRing TensorProduct
open TensorProduct IsLocalRing
open scoped TensorProduct
open scoped BigOperators

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {k F ι : Type*} [Field k] [Field F] [Algebra k F] [Fintype ι]

theorem logarithmicForm_eq_zero_iff (c : ι → k) (f : ι → F) :
    logarithmicForm c f = 0 ↔
      ∀ D : Derivation k F F, ∑ i, algebraMap k F (c i) * (f i)⁻¹ * D (f i) = 0 := by
  constructor
  · intro h D
    simpa [logarithmicForm] using congrArg D.liftKaehlerDifferential h
  · intro h
    apply (Module.forall_dual_apply_eq_zero_iff F _).mp
    intro φ
    simpa [logarithmicForm] using h (φ.compDer (KaehlerDifferential.D k F))

theorem logarithmicLinearForm_apply (c : ι → k) (v : ι → F) :
    logarithmicLinearForm c v = ∑ i, algebraMap k F (c i) * v i := by
  simp [logarithmicLinearForm, Algebra.smul_def]

theorem logarithmicForm_ne_zero_iff_tangent_not_le (c : ι → k) (f : ι → F) :
    logarithmicForm c f ≠ 0 ↔
      ¬ LinearMap.range (logarithmicTangentMap (k := k) f) ≤
        LinearMap.ker (logarithmicLinearForm (F := F) c) := by
  rw [not_iff_not, logarithmicForm_eq_zero_iff]
  constructor
  · intro h v hv
    obtain ⟨D, rfl⟩ := hv
    rw [LinearMap.mem_ker, logarithmicLinearForm_apply]
    simpa only [logarithmicTangentMap, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc] using h D
  · intro h D
    have hD := h (LinearMap.mem_range_self (logarithmicTangentMap (k := k) f) D)
    rw [LinearMap.mem_ker, logarithmicLinearForm_apply] at hD
    simpa only [logarithmicTangentMap, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc] using hD

end WeightedTorusJets.Geometry






namespace WeightedTorusJets.Geometry

theorem finrank_normal_image_of_not_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ω : V →ₗ[K] K) (T : Submodule K V) (h : ¬ T ≤ LinearMap.ker ω) :
    Module.finrank K (LinearMap.range (T.mkQ.domRestrict (LinearMap.ker ω))) =
      Module.finrank K V - Module.finrank K T := by
  have hs : LinearMap.range (T.mkQ.domRestrict (LinearMap.ker ω)) = ⊤ := by
    rw [LinearMap.range_domRestrict, Submodule.map_mkQ_eq_top]
    obtain ⟨x, hxT, hxω⟩ := SetLike.not_le_iff_exists.mp h
    apply top_unique
    rw [← LinearMap.span_singleton_sup_ker_eq_top ω hxω]
    exact sup_le_sup_right ((Submodule.span_singleton_le_iff_mem _ _).mpr hxT) _
  rw [hs, finrank_top, Submodule.finrank_quotient]



end WeightedTorusJets.Geometry

end

open Module CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators TensorProduct

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_FiniteTypeFieldModelEquiv
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section OriginalSourceGeometryOverlay
open Module CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators TensorProduct
noncomputable section
noncomputable section

namespace WeightedTorusJets.Geometry

variable {K ι T : Type*} [CommRing K] [CommRing T] [Fintype ι]
  [Algebra K T] [Algebra (MvPolynomial ι K) T] [IsScalarTower K (MvPolynomial ι K) T]

theorem invariantDerivation_X (c : ι → K) (i : ι) :
    invariantDerivation c (MvPolynomial.X i) = c i • (MvPolynomial.X i : MvPolynomial ι K) := by
  classical
  simp [invariantDerivation, derivation_sum_apply', MvPolynomial.pderiv_X, Pi.single_apply]

theorem localize_invariantDerivation_X (M : Submonoid (MvPolynomial ι K))
    [IsLocalization M T] (c : ι → K) (i : ι) :
    localizeDerivation M (invariantDerivation c)
      (algebraMap (MvPolynomial ι K) T (MvPolynomial.X i)) =
    algebraMap K T (c i) * algebraMap (MvPolynomial ι K) T (MvPolynomial.X i) := by
  rw [localizeDerivation_algebraMap, invariantDerivation_X,
    MvPolynomial.smul_eq_C_mul, map_mul]
  congr 1
  exact (IsScalarTower.algebraMap_apply K (MvPolynomial ι K) T (c i)).symm

end WeightedTorusJets.Geometry
open scoped TensorProduct

namespace WeightedTorusJets.Geometry

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem derivationAmbientCovector_conormal (I : Ideal A) (D : Derivation K A A) (x : I) :
    (conormalDifferential (K := K) I).dualMap (derivationAmbientCovector I D)
      (I.toCotangent x) = Ideal.Quotient.mk I (D x) := by
  simp [LinearMap.dualMap_apply]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry
attribute [local instance] Ideal.Quotient.field
variable {K S ι : Type*} [Field K] [CommRing S] [Fintype ι]
    [Algebra K S] [Algebra (MvPolynomial ι K) S]
    [IsScalarTower K (MvPolynomial ι K) S]
    [Algebra.FormallyEtale (MvPolynomial ι K) S]

theorem logarithmicAmbientEquiv_invariantDerivation (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))
    (D : Derivation K S S) (a : ι → S)
    (ha : ∀ i, D (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) =
      a i * algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) :
    logarithmicAmbientEquiv hx (derivationAmbientCovector I D) =
      fun i => Ideal.Quotient.mk I (a i) := by
  ext i
  rw [logarithmicAmbientEquiv_apply, derivationAmbientCovector_tmul_D, ha, map_mul]
  have hi : Ideal.Quotient.mk I
      (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) ≠ 0 :=
    ((hx i).map (Ideal.Quotient.mk I)).ne_zero
  change (Ideal.Quotient.mk I
    (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))⁻¹ *
      (Ideal.Quotient.mk I (a i) * Ideal.Quotient.mk I
        (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) = _
  rw [mul_left_comm, inv_mul_cancel₀ hi, mul_one]

theorem coordinateNormalEquivCotangentDual_mk [PerfectField K]
    [Algebra.EssFiniteType K S] (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))
    (φ : Module.Dual (S ⧸ I) ((S ⧸ I) ⊗[S] Ω[S⁄K])) :
    coordinateNormalEquivCotangentDual I hx
      (Submodule.Quotient.mk (logarithmicAmbientEquiv hx φ)) =
      (conormalDifferential (K := K) I).dualMap φ := by
  simp [coordinateNormalEquivCotangentDual, Submodule.Quotient.equiv_symm]

theorem coordinateNormal_invariant_pairing [PerfectField K]
    [Algebra.EssFiniteType K S] (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))
    (D : Derivation K S S) (a : ι → S)
    (ha : ∀ i, D (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) =
      a i * algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) (x : I) :
    coordinateNormalEquivCotangentDual I hx
      (Submodule.Quotient.mk (fun i => Ideal.Quotient.mk I (a i))) (I.toCotangent x) =
        Ideal.Quotient.mk I (D x) := by
  rw [← logarithmicAmbientEquiv_invariantDerivation I hx D a ha,
    coordinateNormalEquivCotangentDual_mk, derivationAmbientCovector_conormal]

end WeightedTorusJets.Geometry

open Module

namespace WeightedTorusJets.Geometry

theorem exists_basis_ker_dotProduct_algebraMap {K L n ι : Type*}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n] [Fintype ι]
    (c : n → K) (hc : c ≠ 0)
    (b : Basis ι K (LinearMap.ker (dotProductEquiv K n c))) :
    ∃ bL : Basis ι L (LinearMap.ker (dotProductEquiv L n (algebraMap K L ∘ c))),
      ∀ i, (bL i : n → L) = algebraMap K L ∘ (b i : n → K) := by
  let ωK := dotProductEquiv K n c
  let ωL := dotProductEquiv L n (algebraMap K L ∘ c)
  have hcL : algebraMap K L ∘ c ≠ 0 :=
    ((algebraMap K L).injective.comp_left.ne_iff' (by ext; simp)).mpr hc
  have hωK : ωK ≠ 0 := (dotProductEquiv K n).map_ne_zero_iff.mpr hc
  have hωL : ωL ≠ 0 := (dotProductEquiv L n).map_ne_zero_iff.mpr hcL
  have hmem (i : ι) : algebraMap K L ∘ (b i : n → K) ∈ LinearMap.ker ωL := by
    change (algebraMap K L ∘ c) ⬝ᵥ (algebraMap K L ∘ (b i : n → K)) = 0
    rw [← (algebraMap K L).map_dotProduct]
    have hi : c ⬝ᵥ (b i : n → K) = 0 := (b i).property
    rw [hi, map_zero]
  let w (i : ι) : LinearMap.ker ωL := ⟨algebraMap K L ∘ (b i : n → K), hmem i⟩
  have hbK : LinearIndependent K (fun i => (b i : n → K)) :=
    b.linearIndependent.map' (LinearMap.ker ωK).subtype (Submodule.ker_subtype _)
  have hbL : LinearIndependent L (fun i => algebraMap K L ∘ (b i : n → K)) :=
    linearIndependent_algebraMap_comp_iff.mpr hbK
  have hw : LinearIndependent L w :=
    LinearIndependent.of_comp (LinearMap.ker ωL).subtype hbL
  have hdK := Module.Dual.finrank_ker_add_one_of_ne_zero hωK
  have hdL := Module.Dual.finrank_ker_add_one_of_ne_zero hωL
  rw [finrank_pi] at hdK hdL
  have hd : finrank L (LinearMap.ker ωL) = finrank K (LinearMap.ker ωK) :=
    Nat.add_right_cancel (hdL.trans hdK.symm)
  have hcard : Fintype.card ι = finrank L (LinearMap.ker ωL) := by
    rw [hd, finrank_eq_card_basis b]
  let bL := Basis.mk hw (hw.span_eq_top_of_card_eq_finrank' hcard).ge
  refine ⟨bL, fun i => ?_⟩
  change (Basis.mk hw _ i : n → L) = _
  rw [Basis.mk_apply]



theorem finrank_normal_image_at_point
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) :
    Module.finrank K (LinearMap.range ((⊥ : Submodule K V).mkQ.domRestrict W)) =
      Module.finrank K W := by
  apply LinearMap.finrank_range_of_inj
  have hi : Function.Injective (⊥ : Submodule K V).mkQ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]
  exact hi.comp W.injective_subtype

theorem exists_independent_image_finset
    {K U V ι : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K U]
    (b : Module.Basis ι K U) (f : U →ₗ[K] V) :
    ∃ I : Finset ι, I.card = Module.finrank K (LinearMap.range f) ∧
      LinearIndepOn K (fun i => f (b i)) (I : Set ι) := by
  classical
  have hs : Submodule.span K (Set.range (f.rangeRestrict ∘ b)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_rangeRestrict]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (f.rangeRestrict ∘ b)
  have : Finite κ := hli.finite
  let := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Module.finrank K (LinearMap.range f) := by
    rw [← finrank_span_eq_card hli, hspan, hs, finrank_top]
  refine ⟨Finset.univ.map ⟨a, ha⟩, by simpa using hcard, ?_⟩
  have hi := hli.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
  rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
  exact (linearIndepOn_range_iff ha _).mpr hi

theorem finrank_normal_image_eq_min
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ω : V →ₗ[K] K) (hω : ω ≠ 0) (hdim : Module.finrank K V = 4)
    (T : Submodule K V) (hT : T = ⊥ ∨ ¬ T ≤ LinearMap.ker ω) :
    Module.finrank K (LinearMap.range (T.mkQ.domRestrict (LinearMap.ker ω))) =
      min (4 - Module.finrank K T) 3 := by
  have hker : Module.finrank K (LinearMap.ker ω) = 3 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hω
    omega
  rcases hT with rfl | hT
  · rw [finrank_normal_image_at_point, hker]
    simp
  · have hr := finrank_normal_image_of_not_le ω T hT
    rw [hdim] at hr
    have hle := (T.mkQ.domRestrict (LinearMap.ker ω)).finrank_range_le
    rw [hker, hr] at hle
    rw [hr, Nat.min_eq_left hle]

theorem exists_independent_normal_finset
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ω : V →ₗ[K] K) (hω : ω ≠ 0) (hdim : Module.finrank K V = 4)
    (T : Submodule K V) (hT : T = ⊥ ∨ ¬ T ≤ LinearMap.ker ω)
    (b : Module.Basis (Fin 3) K (LinearMap.ker ω)) :
    ∃ I : Finset (Fin 3), I.card = min (4 - Module.finrank K T) 3 ∧
      LinearIndepOn K (fun i => T.mkQ (b i)) (I : Set (Fin 3)) := by
  obtain ⟨I, hI, hind⟩ :=
    exists_independent_image_finset b (T.mkQ.domRestrict (LinearMap.ker ω))
  refine ⟨I, ?_, hind⟩
  rw [hI, finrank_normal_image_eq_min ω hω hdim T hT]

end WeightedTorusJets.Geometry

end
end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_TorusEvalOne
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section OriginalSourceGeometryOverlay
open Module CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators TensorProduct
noncomputable section
noncomputable section
open scoped TensorProduct
open Module
namespace WeightedTorusJets.Geometry

theorem exists_independent_normal_finset_algebraMap {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (c : Fin 4 → K) (hc : c ≠ 0)
    (b : Module.Basis (Fin 3) K (LinearMap.ker (dotProductEquiv K (Fin 4) c)))
    (T : Submodule L (Fin 4 → L))
    (hT : T = ⊥ ∨ ¬ T ≤ LinearMap.ker
      (dotProductEquiv L (Fin 4) (algebraMap K L ∘ c))) :
    ∃ I : Finset (Fin 3), I.card = min (4 - Module.finrank L T) 3 ∧
      LinearIndepOn L (fun i => T.mkQ (algebraMap K L ∘ (b i : Fin 4 → K)))
        (I : Set (Fin 3)) := by
  obtain ⟨bL, hbL⟩ := exists_basis_ker_dotProduct_algebraMap (L := L) c hc b
  let ωL := dotProductEquiv L (Fin 4) (algebraMap K L ∘ c)
  have hd : Module.finrank L (LinearMap.ker ωL) = 3 := by
    simpa using Module.finrank_eq_card_basis bL
  have hωL : ωL ≠ 0 := by
    intro hzero
    rw [hzero, LinearMap.ker_zero, finrank_top, Module.finrank_pi,
      Fintype.card_fin] at hd
    omega
  obtain ⟨I, hI, hind⟩ := exists_independent_normal_finset ωL hωL (by simp) T hT bL
  refine ⟨I, hI, ?_⟩
  simpa only [hbL] using hind

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets.Geometry
attribute [local instance] Ideal.Quotient.field

theorem cotangent_finrank_add_logarithmic_tangent_finrank
    {K S : Type*} [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    (M : Submonoid (MvPolynomial (Fin 4) K)) [IsLocalization M S]
    (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : Fin 4, IsUnit (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))) :
    Module.finrank (S ⧸ I) I.Cotangent +
      Module.finrank (S ⧸ I) (LinearMap.range (logarithmicTangentMap (k := K)
        (fun i : Fin 4 => Ideal.Quotient.mk I
          (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))))) = 4 := by
  have : Algebra.FormallyEtale (MvPolynomial (Fin 4) K) S :=
    Algebra.FormallyEtale.of_isLocalization M
  have : Algebra.EssFiniteType (MvPolynomial (Fin 4) K) S :=
    Algebra.EssFiniteType.of_isLocalization S M
  have : Algebra.EssFiniteType K S := Algebra.EssFiniteType.comp K (MvPolynomial (Fin 4) K) S
  let T := LinearMap.range (logarithmicTangentMap (k := K)
    (fun i : Fin 4 => Ideal.Quotient.mk I
      (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))))
  have he := (coordinateNormalEquivCotangentDual I hx).finrank_eq
  rw [Subspace.dual_finrank_eq] at he
  rw [← he]
  simpa only [Module.finrank_pi, Fintype.card_fin] using T.finrank_quotient_add_finrank

theorem exists_selected_independent_normal_coordinates
    {K S : Type*} [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    (M : Submonoid (MvPolynomial (Fin 4) K)) [IsLocalization M S]
    (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : Fin 4, IsUnit (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)))
    (c : Fin 4 → K) (hc : c ≠ 0)
    (b : Module.Basis (Fin 3) K (LinearMap.ker (dotProductEquiv K (Fin 4) c)))
    (hform : Module.finrank (S ⧸ I) I.Cotangent ≤ 3 →
      logarithmicForm c (fun i : Fin 4 => Ideal.Quotient.mk I
        (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))) ≠ 0) :
    ∃ J : Finset (Fin 3), J.card = min (Module.finrank (S ⧸ I) I.Cotangent) 3 ∧
      LinearIndependent (S ⧸ I) (fun j : J =>
        (LinearMap.range (logarithmicTangentMap (k := K) (fun i : Fin 4 =>
          Ideal.Quotient.mk I (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))))).mkQ
          (algebraMap K (S ⧸ I) ∘ (b j : Fin 4 → K))) := by
  let f (i : Fin 4) := Ideal.Quotient.mk I
    (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))
  let T := LinearMap.range (logarithmicTangentMap (k := K) f)
  have hdim : Module.finrank (S ⧸ I) I.Cotangent + Module.finrank (S ⧸ I) T = 4 :=
    cotangent_finrank_add_logarithmic_tangent_finrank M I hx
  have hω : logarithmicLinearForm (F := S ⧸ I) c =
      dotProductEquiv (S ⧸ I) (Fin 4) (algebraMap K (S ⧸ I) ∘ c) := by
    ext v
    simp [logarithmicLinearForm_apply, dotProduct, Function.comp_def]
  have hT : T = ⊥ ∨ ¬ T ≤ LinearMap.ker
      (dotProductEquiv (S ⧸ I) (Fin 4) (algebraMap K (S ⧸ I) ∘ c)) := by
    by_cases hh : Module.finrank (S ⧸ I) I.Cotangent ≤ 3
    · exact Or.inr (hω ▸ (logarithmicForm_ne_zero_iff_tangent_not_le c f).mp (hform hh))
    · exact Or.inl (Submodule.finrank_eq_zero.mp (by omega))
  obtain ⟨J, hJ, hind⟩ := exists_independent_normal_finset_algebraMap c hc b T hT
  exact ⟨J, hJ.trans (by congr 1; omega), hind⟩

theorem coordinateNormal_invariant_functional_eq
    {K S : Type*} [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    [Algebra.FormallyEtale (MvPolynomial (Fin 4) K) S] [Algebra.EssFiniteType K S]
    (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : Fin 4, IsUnit (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)))
    (D : Derivation K S S) (v : Fin 4 → K)
    (hD : ∀ i, D (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)) =
      algebraMap K S (v i) * algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)) :
    coordinateNormalEquivCotangentDual I hx (Submodule.Quotient.mk (algebraMap K (S ⧸ I) ∘ v)) =
      derivationCotangentResidue D I := by
  ext x
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  exact coordinateNormal_invariant_pairing I hx D (fun i => algebraMap K S (v i)) hD x

theorem exists_selected_independent_conormal_derivations
    {K S : Type*} [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    (M : Submonoid (MvPolynomial (Fin 4) K)) [IsLocalization M S]
    (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : Fin 4, IsUnit (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)))
    (c : Fin 4 → K) (hc : c ≠ 0)
    (b : Module.Basis (Fin 3) K (LinearMap.ker (dotProductEquiv K (Fin 4) c)))
    (hform : Module.finrank (S ⧸ I) I.Cotangent ≤ 3 →
      logarithmicForm c (fun i : Fin 4 => Ideal.Quotient.mk I
        (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))) ≠ 0) :
    ∃ J : Finset (Fin 3), J.card = min (Module.finrank (S ⧸ I) I.Cotangent) 3 ∧
      LinearIndependent (S ⧸ I) (fun j : J => derivationCotangentResidue
        (localizeDerivation M (invariantDerivation (b j : Fin 4 → K))) I) := by
  have : Algebra.FormallyEtale (MvPolynomial (Fin 4) K) S :=
    Algebra.FormallyEtale.of_isLocalization M
  have : Algebra.EssFiniteType (MvPolynomial (Fin 4) K) S :=
    Algebra.EssFiniteType.of_isLocalization S M
  have : Algebra.EssFiniteType K S := Algebra.EssFiniteType.comp K (MvPolynomial (Fin 4) K) S
  obtain ⟨J, hJ, hind⟩ := exists_selected_independent_normal_coordinates M I hx c hc b hform
  refine ⟨J, hJ, ?_⟩
  let e := coordinateNormalEquivCotangentDual I hx
  have he (j : J) : e (Submodule.Quotient.mk (algebraMap K (S ⧸ I) ∘ (b j : Fin 4 → K))) =
      derivationCotangentResidue
        (localizeDerivation M (invariantDerivation (b j : Fin 4 → K))) I :=
    coordinateNormal_invariant_functional_eq I hx
      (localizeDerivation M (invariantDerivation (b j : Fin 4 → K))) (b j : Fin 4 → K)
      (fun i => localize_invariantDerivation_X M (b j : Fin 4 → K) i)
  have hi := hind.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  change LinearIndependent (S ⧸ I) (fun j : J =>
    e (Submodule.Quotient.mk (algebraMap K (S ⧸ I) ∘ (b j : Fin 4 → K)))) at hi
  have hfamily := funext he
  rwa [hfamily] at hi



end WeightedTorusJets.Geometry

end
end
end OriginalSourceGeometryOverlay

section

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

theorem invariantDerivation_commute (c d : ι → R) :
    Function.Commute (invariantDerivation c) (invariantDerivation d) := by
  intro f
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
      simp only [invariantDerivation_monomial, Derivation.map_smul, smul_smul]
      rw [mul_comm]
  | add f g hf hg => simp only [map_add, hf, hg]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

omit [Algebra R S] [IsScalarTower R S T] in
theorem localization_derivation_ext (M : Submonoid S) [IsLocalization M T]
    {D E : Derivation R T T}
    (h : ∀ s : S, D (algebraMap S T s) = E (algebraMap S T s)) : D = E := by
  apply Derivation.ext
  intro t
  obtain ⟨s, m, rfl⟩ := IsLocalization.exists_mk'_eq M t
  have hd := D.leibniz (IsLocalization.mk' T s m) (algebraMap S T m)
  have he := E.leibniz (IsLocalization.mk' T s m) (algebraMap S T m)
  rw [IsLocalization.mk'_spec, h] at hd
  rw [IsLocalization.mk'_spec] at he
  simp only [smul_eq_mul, h] at hd he
  have heq : algebraMap S T (m : S) * D (IsLocalization.mk' T s m) =
      algebraMap S T (m : S) * E (IsLocalization.mk' T s m) := by
    exact add_left_cancel (hd.symm.trans he)
  exact (IsLocalization.map_units T m).mul_left_cancel heq

theorem iterate_localizeDerivation_algebraMap (M : Submonoid S) [IsLocalization M T]
    (D : Derivation R S S) (n : ℕ) (s : S) :
    (localizeDerivation M D)^[n] (algebraMap S T s) = algebraMap S T (D^[n] s) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [Function.iterate_succ_apply', hn, localizeDerivation_algebraMap,
      Function.iterate_succ_apply']

theorem localizeDerivation_commute (M : Submonoid S) [IsLocalization M T]
    (D E : Derivation R S S) (h : Function.Commute D E) :
    Function.Commute (localizeDerivation M D : T → T) (localizeDerivation M E) := by
  have hzero : ⁅localizeDerivation (T := T) M D, localizeDerivation (T := T) M E⁆ =
      (0 : Derivation R T T) := by
    apply localization_derivation_ext M
    intro s
    simp only [Derivation.commutator_apply, localizeDerivation_algebraMap,
      Derivation.zero_apply]
    rw [h s, sub_self]
  intro t
  exact sub_eq_zero.mp (by
    simpa only [Derivation.commutator_apply, Derivation.zero_apply] using
      congrArg (fun F : Derivation R T T => F t) hzero)

theorem mixed_localizeDerivation_algebraMap (M : Submonoid S) [IsLocalization M T]
    (D : Fin 3 → Derivation R S S) (a : Fin 3 → ℕ) (s : S) :
    ((localizeDerivation M (D 0)).toLinearMap ^ a 0)
      (((localizeDerivation M (D 1)).toLinearMap ^ a 1)
        (((localizeDerivation M (D 2)).toLinearMap ^ a 2) (algebraMap S T s))) =
    algebraMap S T (((D 0).toLinearMap ^ a 0)
      (((D 1).toLinearMap ^ a 1) (((D 2).toLinearMap ^ a 2) s))) := by
  simp only [Module.End.pow_apply, Derivation.coeFn_coe,
    iterate_localizeDerivation_algebraMap]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem torus_algebraMap_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin 4) K)
      (Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) := by
  have ht : (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ MvPolynomial.X_ne_zero i
  exact IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors ht)

theorem torus_polynomial_ne_zero {F : MvPolynomial (Fin 4) K} (hF : F ≠ 0) :
    algebraMap (MvPolynomial (Fin 4) K)
      (Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))) F ≠ 0 := by
  exact fun h ↦ hF (torus_algebraMap_injective (h.trans (map_zero _).symm))

theorem torus_coordinate_isUnit (i : Fin 4) :
    IsUnit (algebraMap (MvPolynomial (Fin 4) K)
      (Localization.Away (∏ j : Fin 4, (MvPolynomial.X j : MvPolynomial (Fin 4) K)))
      (MvPolynomial.X i)) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (∏ j : Fin 4, (MvPolynomial.X j : MvPolynomial (Fin 4) K)))
    (∏ j : Fin 4, (MvPolynomial.X j : MvPolynomial (Fin 4) K))
  rw [map_prod] at h
  exact IsUnit.prod_univ_iff.mp h i



end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R] (I p : Ideal R) [p.IsPrime]

theorem component_local_radical (hp : p ∈ I.minimalPrimes) :
    (I.map (algebraMap R (Localization.AtPrime p))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime p) p I hp,
    Localization.AtPrime.map_eq_maximalIdeal]

theorem component_local_primary (hp : p ∈ I.minimalPrimes) :
    (I.map (algebraMap R (Localization.AtPrime p))).IsPrimary := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [component_local_radical I p hp]
  infer_instance

theorem component_local_contains_maximal_pow [IsNoetherianRing R]
    (hp : p ∈ I.minimalPrimes) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ n ≤
      I.map (algebraMap R (Localization.AtPrime p)) := by
  have h := (I.map (algebraMap R (Localization.AtPrime p))).exists_radical_pow_le_of_fg
    (Ideal.fg_of_isNoetherianRing _)
  rwa [component_local_radical I p hp] at h

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry



theorem rectangleJetIdeal_mono {ι R : Type*} [CommRing R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) : Monotone (rectangleJetIdeal jet t) := by
  intro b c hbc
  apply Ideal.span_mono
  exact Set.image_mono fun a ha j ↦ (ha j).trans (Nat.mul_le_mul_right (t j) hbc)

theorem rectangleJetIdeal_zero {ι R : Type*} [CommRing R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) :
    rectangleJetIdeal jet t 0 = Ideal.span {jet 0} := by
  unfold rectangleJetIdeal
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, zero_mul, Nat.le_zero_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact congrArg jet (funext ha)
  · rintro rfl
    exact ⟨0, fun _ ↦ rfl, rfl⟩

theorem rectangleJetZeroLocus_antitone {ι R : Type*} [CommRing R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) :
    Antitone (fun b ↦ PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t b : Set R)) :=
  fun _ _ h ↦ PrimeSpectrum.zeroLocus_anti_mono_ideal (rectangleJetIdeal_mono jet t h)

theorem rectangleJetIdeal_le_ker {ι R S : Type*} [CommRing R] [CommRing S]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) (φ : R →+* S) {b c : ℕ}
    (hbc : b ≤ c) (hvanish : ∀ a, (∀ j, a j ≤ c * t j) → φ (jet a) = 0) :
    rectangleJetIdeal jet t b ≤ RingHom.ker φ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  exact hvanish a fun j ↦ (ha j).trans (Nat.mul_le_mul_right (t j) hbc)

theorem exists_consecutive_eq_of_dimension_bound (d : ℕ → ℕ) (n : ℕ)
    (hd : ∀ b, b ≤ n → d (b + 1) ≤ d b) (hbound : d 0 ≤ n) :
    ∃ b, b ≤ n ∧ d b = d (b + 1) := by
  by_contra! h
  have hdecrease : ∀ b ≤ n, d (b + 1) < d b := by
    intro b hb
    exact lt_of_le_of_ne (hd b hb) (Ne.symm (h b hb))
  have hsteps : ∀ b ≤ n + 1, d b + b ≤ d 0 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      intro hb
      have hi := ih (by omega)
      have hj := hdecrease b (by omega)
      omega
  have := hsteps (n + 1) le_rfl
  omega

theorem local_irreducible_dimension_nat {X : Type*} [TopologicalSpace X]
    (x : X) (Z : Set X) (hx : x ∈ Z) (hZ : IsClosed Z) (n : ℕ)
    (hdim : topologicalKrullDim Z ≤ n) :
    ∃ d ≤ n, Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z} = d := by
  let A := {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z}
  let e : A ↪o {V : TopologicalSpace.IrreducibleCloseds X // (V : Set X) ⊆ Z} :=
    Subtype.orderEmbedding (fun _ hV ↦ hV.2)
  have hb : Order.krullDim A ≤ n :=
    (Order.krullDim_le_of_orderEmbedding (e.trans (irreducibleClosedSubtypeEmbedding Z))).trans hdim
  let : Nonempty A := ⟨⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩,
    subset_closure (Set.mem_singleton x),
    closure_minimal (Set.singleton_subset_iff.mpr hx) hZ⟩⟩
  let : FiniteDimensionalOrder A :=
    Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
      ⟨Order.krullDim_ne_bot_iff.mpr inferInstance,
        ne_top_of_le_ne_top (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n)).ne hb⟩
  have heq := Order.krullDim_eq_length_of_finiteDimensionalOrder (α := A)
  refine ⟨(LTSeries.longestOf A).length, ?_, heq⟩
  rw [heq] at hb
  exact_mod_cast hb

theorem localization_ringKrullDim_le {R S : Type*} [CommRing R] [CommRing S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S] :
    ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso (IsLocalization.primeSpectrumOrderIso M S)]
  exact Order.krullDim_le_of_orderEmbedding (OrderEmbedding.subtype _)

theorem hypersurface_ringKrullDim_le {R : Type*} [CommRing R] [IsDomain R]
    {F : R} (hF : F ≠ 0) {n : ℕ} (hdim : ringKrullDim R ≤ n + 1) :
    ringKrullDim (R ⧸ Ideal.span {F}) ≤ n := by
  exact ENat.WithBot.add_le_add_one_right_iff.mp
    ((ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero hF)).trans hdim)

theorem four_variable_localization_ringKrullDim_le {k S : Type*} [Field k] [CommRing S]
    (M : Submonoid (MvPolynomial (Fin 4) k)) [Algebra (MvPolynomial (Fin 4) k) S]
    [IsLocalization M S] : ringKrullDim S ≤ 4 := by
  have hdim := localization_ringKrullDim_le (S := S) M
  simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field] using hdim

theorem vanishingIdeal_isMinimalPrime_of_maximal {R : Type*} [CommRing R]
    (I : Ideal R) (V : Set (PrimeSpectrum R))
    (hV : Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ PrimeSpectrum.zeroLocus (I : Set R)) V) :
    I.IsMinimalPrime (PrimeSpectrum.vanishingIdeal V) := by
  refine ⟨⟨PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hV.1.1,
    (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal V I).mp hV.1.2⟩, ?_⟩
  intro q hq hqV
  have hVq : V ⊆ PrimeSpectrum.zeroLocus (q : Set R) :=
    (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal V q).mpr hqV
  have hqV' : PrimeSpectrum.zeroLocus (q : Set R) ⊆ V :=
    hV.2 ⟨(PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical q hq.1.isRadical).mpr hq.1,
      PrimeSpectrum.zeroLocus_anti_mono_ideal hq.2⟩ hVq
  have h := PrimeSpectrum.vanishingIdeal_anti_mono hqV'
  simpa only [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hq.1.isRadical.radical] using h

theorem exists_shared_maximal_of_krullDim_eq_with_height {α β : Type*}
    [PartialOrder α] [PartialOrder β] (e : β ↪o α) (n : ℕ)
    (hα : Order.krullDim α = n) (hβ : Order.krullDim β = n) :
    ∃ b : β, IsMax b ∧ IsMax (e b) ∧ Order.height b = n ∧ Order.height (e b) = n := by
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp (le_of_eq hβ.symm)
  let q := p.map e e.strictMono
  have hmax : IsMax (e p.last) := by
    intro a ha
    by_contra hnot
    have hlt : q.last < a := lt_of_le_not_ge ha hnot
    have hlength := Order.LTSeries.length_le_krullDim (q.snoc a hlt)
    have hn : (n + 1 : WithBot ℕ∞) ≤ n := by
      simpa [q, hp, hα] using hlength
    norm_cast at hn
    omega
  refine ⟨p.last, fun b hb ↦ e.le_iff_le.mp (hmax (e.monotone hb)), hmax, ?_, ?_⟩
  · apply le_antisymm
    · have hd := Order.height_le_krullDim p.last
      rw [hβ] at hd
      exact_mod_cast hd
    · simpa [hp] using Order.length_le_height_last (p := p)
  · apply le_antisymm
    · have hd := Order.height_le_krullDim (e p.last)
      rw [hα] at hd
      exact_mod_cast hd
    · simpa [q, hp] using Order.length_le_height_last (p := q)

theorem local_irreducible_dimension_eq_order_height
    {X : Type*} [TopologicalSpace X] (x : X) (Z : Set X)
    (V : {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z}) :
    Order.krullDim
      {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ V.1} =
      (Order.height V : WithBot ℕ∞) := by
  let e : {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ V.1} ≃o
      Set.Iic V :=
    { toFun := fun W ↦ ⟨⟨W.1, W.2.1, W.2.2.trans V.2.2⟩, W.2.2⟩
      invFun := fun W ↦ ⟨W.1.1, W.1.2.1, W.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_rel_iff' := Iff.rfl }
  exact (Order.krullDim_eq_of_orderIso e).trans (Order.height_eq_krullDim_Iic V).symm

theorem exists_shared_component_of_full_local_dimension
    {X : Type*} [TopologicalSpace X] (x : X) (Z₁ Z₂ : Set X)
    (hZ₁ : IsClosed Z₁) (hZ₂Z₁ : Z₂ ⊆ Z₁) (n : ℕ)
    (hd₁ : Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z₁} = n)
    (hd₂ : Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z₂} = n) :
    ∃ V : Set X, x ∈ V ∧ V ⊆ Z₂ ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z₁) V ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z₂) V ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ V} = n := by
  let e : {V : TopologicalSpace.IrreducibleCloseds X //
      x ∈ V ∧ (V : Set X) ⊆ Z₂} ↪o
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z₁} :=
    Subtype.orderEmbedding (fun V hV ↦ ⟨hV.1, hV.2.trans hZ₂Z₁⟩)
  obtain ⟨V, _, hmax, hVheight, _⟩ :=
    exists_shared_maximal_of_krullDim_eq_with_height e n hd₁ hd₂
  have hm : Maximal (fun S : Set X ↦ IsIrreducible S ∧ S ⊆ Z₁) (V.1 : Set X) := by
    refine ⟨⟨V.1.isIrreducible, V.2.2.trans hZ₂Z₁⟩, ?_⟩
    intro S hS hVS
    let W : {W : TopologicalSpace.IrreducibleCloseds X //
        x ∈ W ∧ (W : Set X) ⊆ Z₁} :=
      ⟨⟨closure S, hS.1.closure, isClosed_closure⟩,
        subset_closure (hVS V.2.1), closure_minimal hS.2 hZ₁⟩
    have hVW : e V ≤ W := fun _ hy ↦ subset_closure (hVS hy)
    exact subset_closure.trans (hmax hVW)
  refine ⟨V.1, V.2.1, V.2.2, hm,
    ⟨⟨V.1.isIrreducible, V.2.2⟩,
      fun S hS hVS ↦ hm.2 ⟨hS.1, hS.2.trans hZ₂Z₁⟩ hVS⟩, ?_⟩
  rw [local_irreducible_dimension_eq_order_height x Z₂ V, hVheight]
  rfl

theorem exists_shared_component_of_dimension_three_full
    {X : Type*} [TopologicalSpace X] (x : X) (Z : ℕ → Set X)
    (hclosed : ∀ b ≤ 4, IsClosed (Z b)) (hnested : Antitone Z)
    (hx : x ∈ Z 4) (hdim : topologicalKrullDim (Z 0) ≤ 3) :
    ∃ b ≤ 3, ∃ n : ℕ, n ≤ 3 ∧ ∃ V : Set X,
      x ∈ V ∧ V ⊆ Z (b + 1) ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z b) V ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z (b + 1)) V ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ Z b} = n ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ Z (b + 1)} = n ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ V} = n := by
  have hex : ∀ b, b ≤ 4 → ∃ d : ℕ, d ≤ 3 ∧ Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z b} = d := by
    intro b hb
    apply local_irreducible_dimension_nat x (Z b) (hnested hb hx) (hclosed b hb) 3
    have he := (Topology.IsEmbedding.inclusion (hnested (Nat.zero_le b))).isInducing
    exact he.topologicalKrullDim_le.trans hdim
  let d (b : ℕ) : ℕ := if hb : b ≤ 4 then (hex b hb).choose else 0
  have hd : ∀ b, b ≤ 4 → Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z b} = d b := by
    intro b hb
    simpa only [d, dite_eq_left hb] using (hex b hb).choose_spec.2
  have hdle : ∀ b, b ≤ 4 → d b ≤ 3 := by
    intro b hb
    simpa only [d, dite_eq_left hb] using (hex b hb).choose_spec.1
  have hmono : ∀ b, b ≤ 3 → d (b + 1) ≤ d b := by
    intro b hb
    let e : {V : TopologicalSpace.IrreducibleCloseds X //
        x ∈ V ∧ (V : Set X) ⊆ Z (b + 1)} ↪o
        {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z b} :=
      Subtype.orderEmbedding (fun V hV ↦ ⟨hV.1, hV.2.trans (hnested (Nat.le_succ b))⟩)
    have he := Order.krullDim_le_of_orderEmbedding e
    rw [hd b (by omega), hd (b + 1) (by omega)] at he
    exact_mod_cast he
  obtain ⟨b, hb, heq⟩ := exists_consecutive_eq_of_dimension_bound d 3 hmono (hdle 0 (by omega))
  have hdnext : Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z (b + 1)} = d b := by
    rw [hd (b + 1) (by omega), heq]
  obtain ⟨V, hxV, hVZ, hm₁, hm₂, hVdim⟩ :=
    exists_shared_component_of_full_local_dimension x (Z b) (Z (b + 1))
      (hclosed b (by omega)) (hnested (Nat.le_succ b)) (d b) (hd b (by omega)) hdnext
  exact ⟨b, hb, d b, hdle b (by omega), V, hxV, hVZ, hm₁, hm₂,
    hd b (by omega), hdnext, hVdim⟩

theorem rectangleJets_have_shared_component_full
    {ι R : Type*} [CommRing R] [IsDomain R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) (p : PrimeSpectrum R)
    (hp : rectangleJetIdeal jet t 4 ≤ p.asIdeal) (hjet : jet 0 ≠ 0)
    (hdim : ringKrullDim R ≤ 4) :
    let Z := fun b ↦ PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t b : Set R)
    ∃ b ≤ 3, ∃ n : ℕ, n ≤ 3 ∧ ∃ V : Set (PrimeSpectrum R),
      p ∈ V ∧ V ⊆ Z (b + 1) ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z b) V ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z (b + 1)) V ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ W ∧ (W : Set (PrimeSpectrum R)) ⊆ Z b} = n ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ W ∧ (W : Set (PrimeSpectrum R)) ⊆ Z (b + 1)} = n ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ W ∧ (W : Set (PrimeSpectrum R)) ⊆ V} = n := by
  apply exists_shared_component_of_dimension_three_full p
    (fun b ↦ PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t b : Set R))
    (fun b _ ↦ PrimeSpectrum.isClosed_zeroLocus _)
    (rectangleJetZeroLocus_antitone jet t) hp
  calc
    topologicalKrullDim (PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t 0 : Set R)) =
        Order.krullDim (TopologicalSpace.IrreducibleCloseds
          (PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t 0 : Set R)))ᵒᵈ :=
      Order.krullDim_orderDual.symm
    _ = Order.krullDim (PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t 0 : Set R)) :=
      (Order.krullDim_eq_of_orderIso
        (PrimeSpectrum.zeroLocusEquivIrreducibleCloseds
          (rectangleJetIdeal jet t 0 : Set R))).symm
    _ = ringKrullDim (R ⧸ rectangleJetIdeal jet t 0) := (ringKrullDim_quotient _).symm
    _ ≤ 3 := by
      rw [rectangleJetIdeal_zero]
      exact hypersurface_ringKrullDim_le hjet hdim

theorem rectangleJets_have_shared_minimal_prime {ι R : Type*} [CommRing R] [IsDomain R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) (p : PrimeSpectrum R)
    (hp : rectangleJetIdeal jet t 4 ≤ p.asIdeal) (hjet : jet 0 ≠ 0)
    (hdim : ringKrullDim R ≤ 4) :
    ∃ b ≤ 3, ∃ q : Ideal R, q ≤ p.asIdeal ∧
      (rectangleJetIdeal jet t b).IsMinimalPrime q ∧
      (rectangleJetIdeal jet t (b + 1)).IsMinimalPrime q := by
  obtain ⟨b, hb, _, _, V, hpV, _, hVb, hVb', _⟩ :=
    rectangleJets_have_shared_component_full jet t p hp hjet hdim
  refine ⟨b, hb, PrimeSpectrum.vanishingIdeal V, ?_,
    vanishingIdeal_isMinimalPrime_of_maximal _ V hVb,
    vanishingIdeal_isMinimalPrime_of_maximal _ V hVb'⟩
  simpa only [PrimeSpectrum.vanishingIdeal_singleton] using
    PrimeSpectrum.vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hpV)

end WeightedTorusJets.Geometry

open scoped BigOperators

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_RectangleThreshold
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open scoped BigOperators
namespace WeightedTorusJets.Geometry

lemma rectangleThreshold_pos {H N : ℝ} (hH : 0 < H) (hN : 0 < N) (j : Fin 3) :
    0 < rectangleThreshold H N j := by
  unfold rectangleThreshold
  positivity

lemma short_side_lower {H N : ℝ} (hH : 0 < H) (hHN : H ≤ N) :
    N ≤ H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := by
  have hN : 0 < N := lt_of_lt_of_le hH hHN
  have hp : N ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) = N := by
    rw [← Real.rpow_add hN]
    norm_num
  calc
    N = N ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := hp.symm
    _ ≤ H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hH hHN (by norm_num : (-1 / 3 : ℝ) ≤ 0))
        (Real.rpow_nonneg hN.le _)

lemma short_side_le_threshold {H N : ℝ} (hH : 1 ≤ H) (hN : 0 ≤ N) (j : Fin 3) :
    8 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) ≤ rectangleThreshold H N j / 4 := by
  have he : H ^ (-1 / 3 : ℝ) ≤
      H ^ (if j = 0 then (2 / 3 : ℝ) else (-1 / 3 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hH
    split_ifs <;> norm_num
  have hm := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hN (4 / 3 : ℝ))
  unfold rectangleThreshold
  linarith

theorem rectangle_floor_product_gt_short_power {H N : ℝ} (hH : 1 ≤ H) (hN : 0 < N)
    (I : Finset (Fin 3)) (hI : I.Nonempty) :
    (8 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ)) ^ I.card <
      ∏ j ∈ I, ((⌊rectangleThreshold H N j / 4⌋₊ : ℝ) + 1) := by
  have hp := Finset.prod_lt_prod_of_nonempty
    (s := I) (f := fun _ ↦ 8 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ))
    (g := fun j ↦ ((⌊rectangleThreshold H N j / 4⌋₊ : ℝ) + 1))
    (fun _ _ ↦ by have : 0 < H := lt_of_lt_of_le zero_lt_one hH; positivity)
    (fun j _ ↦ (short_side_le_threshold hH hN.le j).trans_lt (Nat.lt_floor_add_one _)) hI
  simpa using hp

lemma rectangleThreshold_product {H N : ℝ} (hH : 0 < H) (hN : 0 < N) :
    (∏ j : Fin 3, rectangleThreshold H N j / 4) = 8 ^ 3 * N ^ 4 := by
  have hhp : H ^ (2 / 3 : ℝ) * H ^ (-1 / 3 : ℝ) * H ^ (-1 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hH, ← Real.rpow_add hH]
    norm_num
  have hnp : (N ^ (4 / 3 : ℝ)) ^ 3 = N ^ 4 := by
    rw [← Real.rpow_mul_natCast hN.le]
    norm_num
  rw [Fin.prod_univ_three]
  simp only [rectangleThreshold, ↓reduceIte, Fin.isValue, one_ne_zero, show (2 : Fin 3) ≠ 0 by decide]
  calc
    _ = 8 ^ 3 * (H ^ (2 / 3 : ℝ) * H ^ (-1 / 3 : ℝ) * H ^ (-1 / 3 : ℝ)) *
        (N ^ (4 / 3 : ℝ)) ^ 3 := by ring
    _ = 8 ^ 3 * N ^ 4 := by rw [hhp, hnp]; ring

theorem rectangle_floor_product_gt {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N)
    {h : ℕ} (hh : 1 ≤ h) (hh4 : h ≤ 4) (I : Finset (Fin 3))
    (hI : I.card = min h 3) :
    (4 * N) ^ h < ∏ j ∈ I, ((⌊rectangleThreshold H N j / 4⌋₊ : ℝ) + 1) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hNp : 0 < N := lt_of_lt_of_le hHp hHN
  have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hh3 : h ≤ 3
  · have hIc : I.card = h := by omega
    have hprod : (8 * N) ^ h <
        ∏ j ∈ I, ((⌊rectangleThreshold H N j / 4⌋₊ : ℝ) + 1) := by
      have hp := rectangle_floor_product_gt_short_power hH hNp I hIne
      rw [hIc] at hp
      have hs : 8 * N ≤ 8 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := by
        have := short_side_lower hHp hHN
        linarith
      exact (pow_le_pow_left₀ (by positivity) hs h).trans_lt hp
    exact (pow_lt_pow_left₀ (by nlinarith : 4 * N < 8 * N) (by positivity)
      (by omega : h ≠ 0)).trans hprod
  · have heq : h = 4 := by omega
    subst h
    have hIu : I = Finset.univ := I.eq_univ_of_card (by simpa using hI)
    subst I
    have hp := Finset.prod_lt_prod_of_nonempty
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun j ↦ rectangleThreshold H N j / 4)
      (g := fun j ↦ ((⌊rectangleThreshold H N j / 4⌋₊ : ℝ) + 1))
      (fun j _ ↦ div_pos (rectangleThreshold_pos hHp hNp j) (by norm_num))
      (fun _ _ ↦ Nat.lt_floor_add_one _) (by simp)
    rw [rectangleThreshold_product hHp hNp] at hp
    have hn4 : 0 < N ^ 4 := pow_pos hNp _
    nlinarith

theorem rectangle_floor_product_gt_nat {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N)
    {h : ℕ} (hh : 1 ≤ h) (hh4 : h ≤ 4) (I : Finset (Fin 3))
    (hI : I.card = min h 3) :
    (4 * N) ^ h < ∏ j ∈ I, (⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊ + 1) := by
  have hp := rectangle_floor_product_gt
    (H := (H : ℝ)) (N := (N : ℝ)) (by exact_mod_cast hH) (by exact_mod_cast hHN)
    hh hh4 I hI
  exact_mod_cast hp

theorem rectangle_jet_cutoff {H N : ℝ} (hH : 0 < H) (hN : 0 < N)
    (j : Fin 3) {a b : ℕ} (hb : b ≤ 4)
    (ha : a ≤ b * ⌊rectangleThreshold H N j / 4⌋₊) :
    (a : ℝ) ≤ rectangleThreshold H N j := by
  have ht := rectangleThreshold_pos hH hN j
  have hf := Nat.floor_le (le_of_lt (div_pos ht (by norm_num : (0 : ℝ) < 4)))
  have hab : (a : ℝ) ≤ 4 * (⌊rectangleThreshold H N j / 4⌋₊ : ℝ) := by
    exact_mod_cast ha.trans (Nat.mul_le_mul_right _ hb)
  linarith

theorem rectangle_cutoff_lower {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) (j : Fin 3) :
    8 * N + 1 ≤ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊ + 1 := by
  apply Nat.succ_le_succ
  apply Nat.le_floor
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hs := short_side_lower (lt_of_lt_of_le zero_lt_one hHr) hHNr
  have ht := short_side_le_threshold hHr (Nat.cast_nonneg N) j
  push_cast
  linarith

theorem rectangle_cutoff_ge_nine {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) (j : Fin 3) :
    9 ≤ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊ + 1 := by
  have := rectangle_cutoff_lower hH hHN j
  have hN : 1 ≤ N := hH.trans hHN
  omega



section TorusJetAssembly

variable {K : Type*} [Field K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "torusCoordinateProduct" => (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))
local notation "TorusCoordRing" => Localization.Away torusCoordinateProduct

theorem torus_mixed_derivatives_algebraMap (c : Fin 3 → Fin 4 → K)
    (a : Fin 3 → ℕ) (F : PolyRing) :
    ((localizeDerivation (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
      (invariantDerivation (c 0))).toLinearMap ^ a 0)
      (((localizeDerivation (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
        (invariantDerivation (c 1))).toLinearMap ^ a 1)
        (((localizeDerivation (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
          (invariantDerivation (c 2))).toLinearMap ^ a 2) (algebraMap PolyRing TorusCoordRing F))) =
      algebraMap PolyRing TorusCoordRing (invariantJet c a F) := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe, invariantJet] using
    mixed_localizeDerivation_algebraMap (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
      (fun j ↦ invariantDerivation (c j)) a F

theorem torus_rectangleJetIdeal_le_identity {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (c : Fin 3 → Fin 4 → K) (F : PolyRing)
    (hvanish : ∀ a : Fin 3 → ℕ,
      (∀ j, (a j : ℝ) ≤ rectangleThreshold (H : ℝ) (N : ℝ) j) →
        MvPolynomial.eval (fun _ ↦ 1) (invariantJet c a F) = 0)
    {b : ℕ} (hb : b ≤ 4) :
    rectangleJetIdeal (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F))
      (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) b ≤
        (torusIdentityPoint (K := K)).asIdeal := by
  change _ ≤ RingHom.ker (torusEvalOne (K := K))
  apply rectangleJetIdeal_le_ker
    (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F))
    (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊)
    (torusEvalOne (K := K)) hb
  intro a ha
  rw [torusEvalOne_algebraMap]
  apply hvanish a
  intro j
  exact rectangle_jet_cutoff
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hH))
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hH.trans hHN)))
    j le_rfl (ha j)

theorem torus_rectangle_has_shared_minimal_prime {H N : ℕ}
    (hH : 1 ≤ H) (hHN : H ≤ N) (c : Fin 3 → Fin 4 → K) (F : PolyRing) (hF : F ≠ 0)
    (hvanish : ∀ a : Fin 3 → ℕ,
      (∀ j, (a j : ℝ) ≤ rectangleThreshold (H : ℝ) (N : ℝ) j) →
        MvPolynomial.eval (fun _ ↦ 1) (invariantJet c a F) = 0) :
    let jet := fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)
    let t := fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊
    ∃ b ≤ 3, ∃ q : Ideal TorusCoordRing, q ≤ (torusIdentityPoint (K := K)).asIdeal ∧
      (rectangleJetIdeal jet t b).IsMinimalPrime q ∧
      (rectangleJetIdeal jet t (b + 1)).IsMinimalPrime q := by
  have hu : torusCoordinateProduct ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ MvPolynomial.X_ne_zero i
  let : IsDomain TorusCoordRing := IsLocalization.isDomain_of_le_nonZeroDivisors TorusCoordRing
    (powers_le_nonZeroDivisors_of_noZeroDivisors hu)
  apply rectangleJets_have_shared_minimal_prime _ _ (torusIdentityPoint (K := K))
  · exact torus_rectangleJetIdeal_le_identity hH hHN c F hvanish le_rfl
  · simpa only [invariantJet, Pi.zero_apply, Function.iterate_zero, id_eq] using
      (torus_polynomial_ne_zero hF)
  · exact four_variable_localization_ringKrullDim_le (Submonoid.powers torusCoordinateProduct)

theorem torus_rectangle_shared_component_data {H N : ℕ}
    (hH : 1 ≤ H) (hHN : H ≤ N) (c : Fin 3 → Fin 4 → K)
    (F : PolyRing) (hF : F ≠ 0)
    (hvanish : ∀ a : Fin 3 → ℕ,
      (∀ j, (a j : ℝ) ≤ rectangleThreshold (H : ℝ) (N : ℝ) j) →
        MvPolynomial.eval (fun _ ↦ 1) (invariantJet c a F) = 0) :
    let jet := fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)
    let t := fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊
    ∃ b ≤ 3, ∃ q : PrimeSpectrum TorusCoordRing,
      q.asIdeal ≤ (torusIdentityPoint (K := K)).asIdeal ∧
      (rectangleJetIdeal jet t b).IsMinimalPrime q.asIdeal ∧
      (rectangleJetIdeal jet t (b + 1)).IsMinimalPrime q.asIdeal ∧
      1 ≤ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
        (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)) ∧
      Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
        (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)) ≤ 4 := by
  obtain ⟨b, hb, q, hqp, hqb, hqb'⟩ :=
    torus_rectangle_has_shared_minimal_prime hH hHN c F hF hvanish
  have : q.IsPrime := hqb.isPrime
  have hmem : algebraMap PolyRing TorusCoordRing F ∈ q := by
    apply hqb.le
    apply rectangleJetIdeal_mono _ _ (Nat.zero_le b)
    rw [rectangleJetIdeal_zero]
    apply Ideal.subset_span
    simp only [Set.mem_singleton_iff, invariantJet, Pi.zero_apply, Function.iterate_zero, id_eq]
  exact ⟨b, hb, ⟨q, hqb.isPrime⟩, hqp, hqb, hqb',
    localization_component_cotangent_bounds (Submonoid.powers torusCoordinateProduct) q hF hmem⟩

end TorusJetAssembly



end WeightedTorusJets.Geometry

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DerivationJet
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators

namespace WeightedTorusJets.Geometry



noncomputable section

variable {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

theorem derivationJet_map (D : Fin 3 → Derivation ℚ A A)
    (E : Fin 3 → Derivation ℚ B B) (f : A →+* B)
    (h : ∀ i a, f (D i a) = E i (f a)) (β : Fin 3 → ℕ) (a : A) :
    f (derivationJet D β a) = derivationJet E β (f a) := by
  have hp (i : Fin 3) (n : ℕ) (x : A) :
      f (((D i).toLinearMap ^ n) x) = ((E i).toLinearMap ^ n) (f x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [pow_succ', Module.End.mul_apply, Derivation.coeFn_coe, h, ih]
  simp only [derivationJet, hp]

theorem derivativeStageIdeal_map (D : Fin 3 → Derivation ℚ A A)
    (E : Fin 3 → Derivation ℚ B B) (f : A →+* B)
    (h : ∀ i a, f (D i a) = E i (f a)) (t : Fin 3 → ℕ) (b : ℕ) (F : A) :
    Ideal.map f (derivativeStageIdeal D t b F) = derivativeStageIdeal E t b (f F) := by
  unfold derivativeStageIdeal
  rw [Ideal.map_span, Set.image_image]
  simp only [derivationJet_map D E f h]

end

end WeightedTorusJets.Geometry

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_HilbertSeries
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open MvPolynomial
noncomputable section
open scoped BigOperators
open scoped BigOperators

open _root_.Filter

open scoped BigOperators

namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveDegree_pos_iff (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    0 < projectiveDegree I hI ↔ hilbertPolynomial I hI ≠ 0 := by
  constructor
  · intro hpos hzero
    simp [projectiveDegree, hzero] at hpos
  · intro hne
    rw [projectiveDegree, dite_eq_right hne]
    have hz := (exists_pos_integer_factorial_mul_leadingCoeff_hilbertPolynomial I hI hne).choose_spec.1
    omega

end WeightedTorusJets.Geometry.GradedQuotient

end
end

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_FinrankDegreePiecePosPrimeVariableNotMem
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section
namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem finrank_degreePiece_pos_of_prime_variable_not_mem
    (I : Ideal (MvPolynomial σ K)) (hprime : I.IsPrime)
    {i : σ} (hi : X i ∉ I) (n : ℕ) :
    0 < Module.finrank K (degreePiece I n) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨Ideal.Quotient.mk I (X i ^ n), X i ^ n, isHomogeneous_X_pow i n, rfl⟩, ?_⟩
  intro hzero
  exact hi (hprime.mem_of_pow_mem n
    (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hzero)))

theorem hilbertPolynomial_ne_zero_of_prime_variable_not_mem
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hprime : I.IsPrime)
    (hvars : ∃ i : σ, X i ∉ I) : hilbertPolynomial I hI ≠ 0 := by
  obtain ⟨i, hi⟩ := hvars
  obtain ⟨N, hN⟩ := hilbertPolynomial_spec I hI
  intro hzero
  have h := hN (N + 1) (by omega)
  rw [hzero, Polynomial.eval_zero] at h
  have hpos := finrank_degreePiece_pos_of_prime_variable_not_mem I hprime hi (N + 1)
  exact (Nat.ne_of_gt hpos) (by exact_mod_cast h)

theorem projectiveDegree_pos_of_prime_variable_not_mem
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hprime : I.IsPrime)
    (hvars : ∃ i : σ, X i ∉ I) : 0 < projectiveDegree I hI :=
  (projectiveDegree_pos_iff I hI).mpr
    (hilbertPolynomial_ne_zero_of_prime_variable_not_mem I hI hprime hvars)

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets.Geometry.GradedQuotient
open MvPolynomial

theorem cone_projectiveDegree_pos
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    0 < projectiveDegree (coneIdeal p) (coneIdeal_isHomogeneous p) :=
  projectiveDegree_pos_of_prime_variable_not_mem
    (coneIdeal p) (coneIdeal_isHomogeneous p) (coneIdeal_isPrime p)
    ⟨none, X_none_not_mem_coneIdeal p⟩

end WeightedTorusJets.Geometry.GradedQuotient

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_TorusDerivationOverRat
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
noncomputable section

namespace WeightedTorusJets.Geometry


variable {K : Type*} [Field K] [CharZero K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "torusCoordinateProduct" => (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))
local notation "TorusCoordRing" => Localization.Away torusCoordinateProduct

theorem torusDerivationOverRat_commute (c : Fin 3 → Fin 4 → K) (i j : Fin 3) :
    Function.Commute (torusDerivationOverRat c i) (torusDerivationOverRat c j) := by
  simpa only [torusDerivationOverRat, Derivation.coe_restrictScalars] using
    localizeDerivation_commute (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
      (invariantDerivation (c i)) (invariantDerivation (c j))
      (invariantDerivation_commute (c i) (c j))

theorem localTorusDerivationOverRat_commute (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (i j : Fin 3) :
    Function.Commute (localTorusDerivationOverRat c q i) (localTorusDerivationOverRat c q j) :=
  localizeDerivation_commute q.asIdeal.primeCompl
    (torusDerivationOverRat c i) (torusDerivationOverRat c j)
    (torusDerivationOverRat_commute c i j)

theorem torus_derivationJet_eq (c : Fin 3 → Fin 4 → K) (a : Fin 3 → ℕ) (F : PolyRing) :
    derivationJet (torusDerivationOverRat c) a (algebraMap PolyRing TorusCoordRing F) =
      algebraMap PolyRing TorusCoordRing (invariantJet c a F) := by
  simpa only [derivationJet, torusDerivationOverRat, Module.End.pow_apply,
    Derivation.coeFn_coe, Derivation.coe_restrictScalars] using
      torus_mixed_derivatives_algebraMap c a F

theorem torus_derivativeStageIdeal_eq (c : Fin 3 → Fin 4 → K)
    (t : Fin 3 → ℕ) (b : ℕ) (F : PolyRing) :
    derivativeStageIdeal (torusDerivationOverRat c) t b (algebraMap PolyRing TorusCoordRing F) =
      rectangleJetIdeal (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)) t b := by
  simp only [derivativeStageIdeal, rectangleJetIdeal, torus_derivationJet_eq]

theorem local_torus_derivativeStageIdeal_eq (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (t : Fin 3 → ℕ) (b : ℕ) (F : PolyRing) :
    Ideal.map (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal))
      (rectangleJetIdeal (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)) t b) =
    derivativeStageIdeal (localTorusDerivationOverRat c q) t b
      (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal)
        (algebraMap PolyRing TorusCoordRing F)) := by
  rw [← torus_derivativeStageIdeal_eq]
  apply derivativeStageIdeal_map
  intro j f
  exact (localizeDerivation_algebraMap q.asIdeal.primeCompl (torusDerivationOverRat c j) f).symm

theorem local_torus_stage_le_maximal (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (t : Fin 3 → ℕ) (b : ℕ) (F : PolyRing)
    (hq : rectangleJetIdeal
      (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)) t b ≤ q.asIdeal) :
    derivativeStageIdeal (localTorusDerivationOverRat c q) t b
      (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal)
        (algebraMap PolyRing TorusCoordRing F)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
  rw [← local_torus_derivativeStageIdeal_eq]
  exact (Ideal.map_mono hq).trans_eq
    (IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal (Localization.AtPrime q.asIdeal))

theorem local_torus_stage_primary_data (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (t : Fin 3 → ℕ) (b : ℕ) (F : PolyRing)
    (hq : (rectangleJetIdeal
      (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)) t b).IsMinimalPrime q.asIdeal) :
    let J := derivativeStageIdeal (localTorusDerivationOverRat c q) t b
      (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal)
        (algebraMap PolyRing TorusCoordRing F))
    J.radical = IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ∧ J.IsPrimary ∧
      ∃ n : ℕ, IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n ≤ J := by
  dsimp only
  rw [← local_torus_derivativeStageIdeal_eq]
  exact ⟨component_local_radical _ q.asIdeal hq, component_local_primary _ q.asIdeal hq,
    component_local_contains_maximal_pow _ q.asIdeal hq⟩


end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

section ScalarCompatibility

variable {K S L : Type*} [CommRing K] [Algebra ℚ K]
  [CommRing S] [Algebra K S] [Algebra ℚ S] [IsScalarTower ℚ K S]
  [CommRing L] [Algebra K L] [Algebra ℚ L] [IsScalarTower ℚ K L]
  [Algebra S L] [IsScalarTower K S L] [IsScalarTower ℚ S L]

theorem derivationCotangentResidue_restrictScalars (D : Derivation K S S) (I : Ideal S) :
    derivationCotangentResidue (D.restrictScalars ℚ) I = derivationCotangentResidue D I := by
  ext x
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rfl

end ScalarCompatibility


attribute [local instance] Ideal.Quotient.field

variable {K : Type*} [Field K] [CharZero K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "torusCoordinateProduct" => (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))
local notation "TorusCoordRing" => Localization.Away torusCoordinateProduct

theorem localTorusDerivationOverRat_eq_direct (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (M : Submonoid PolyRing)
    [IsLocalization M (Localization.AtPrime q.asIdeal)] (j : Fin 3) :
    localTorusDerivationOverRat c q j =
      (localizeDerivation (T := Localization.AtPrime q.asIdeal) M
        (invariantDerivation (c j))).restrictScalars ℚ := by
  apply localization_derivation_ext M
  intro F
  rw [IsScalarTower.algebraMap_apply PolyRing TorusCoordRing (Localization.AtPrime q.asIdeal)]
  simp only [localTorusDerivationOverRat, localizeDerivation_algebraMap,
    torusDerivationOverRat, Derivation.coe_restrictScalars]
  rw [← IsScalarTower.algebraMap_apply PolyRing TorusCoordRing (Localization.AtPrime q.asIdeal),
    ← IsScalarTower.algebraMap_apply PolyRing TorusCoordRing (Localization.AtPrime q.asIdeal),
    localizeDerivation_algebraMap]

theorem localTorusDerivationOverRat_cotangent_eq_direct (c : Fin 3 → Fin 4 → K)
    (q : PrimeSpectrum TorusCoordRing) (M : Submonoid PolyRing)
    [IsLocalization M (Localization.AtPrime q.asIdeal)] (j : Fin 3) :
    derivationCotangentResidue (localTorusDerivationOverRat c q j)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) =
    derivationCotangentResidue
      (localizeDerivation (T := Localization.AtPrime q.asIdeal) M (invariantDerivation (c j)))
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) := by
  rw [localTorusDerivationOverRat_eq_direct c q M j, derivationCotangentResidue_restrictScalars]


end WeightedTorusJets.Geometry

open scoped TensorProduct


open scoped TensorProduct







open Module




open scoped BigOperators







end
end




open scoped BigOperators


open Module


open MvPolynomial


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_InvariantJetMonomial
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section














open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

theorem invariantJet_monomial (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (m : ι →₀ ℕ) (r : R) :
    invariantJet c a (MvPolynomial.monomial m r) =
      ((∑ i, c 0 i * (m i : R)) ^ a 0 *
        (∑ i, c 1 i * (m i : R)) ^ a 1 *
        (∑ i, c 2 i * (m i : R)) ^ a 2) • MvPolynomial.monomial m r := by
  classical
  ext n
  rw [coeff_invariantJet, MvPolynomial.coeff_smul]
  simp only [MvPolynomial.coeff_monomial, smul_eq_mul]
  split_ifs with h
  · subst n
    rfl
  · simp




end WeightedTorusJets.Geometry



noncomputable section
open scoped BigOperators
open MvPolynomial








namespace WeightedTorusJets.Geometry

section RectangleUpper

universe uSource
variable {K : Type uSource} [Field K] [Infinite K]
local notation "P₄" => MvPolynomial (Fin 4) K
local notation "T₄" => Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P₄))

theorem rectangleJetIdeal_length_le
    (p : Ideal T₄) [p.IsPrime] (c : Fin 3 → Fin 4 → K) (t : Fin 3 → ℕ) (b : ℕ)
    {N : ℕ} (hN : 0 < N) {F : P₄} (hF : F ∈ polynomialBox K N)
    (hp : p ∈ (rectangleJetIdeal (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).minimalPrimes) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⧸
      (rectangleJetIdeal (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).map
        (algebraMap T₄ (Localization.AtPrime p))) ≤
    ((4 * N) ^ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.CotangentSpace (Localization.AtPrime p)) : ℕ∞) := by
  obtain ⟨g, _, _, _, hle, hweighted⟩ :=
    torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247 p c t b hN hF hp
  have : (p.comap (algebraMap P₄ T₄)).IsPrime := Ideal.comap_isPrime _ p
  have hdegree : (1 : ℕ∞) ≤ (GradedQuotient.projectiveDegree
      (coneIdeal (p.comap (algebraMap P₄ T₄)))
      (coneIdeal_isHomogeneous (p.comap (algebraMap P₄ T₄))) : ℕ∞) := by
    exact_mod_cast (Nat.succ_le_iff.mpr
      (GradedQuotient.cone_projectiveDegree_pos (p.comap (algebraMap P₄ T₄))))
  apply hle.trans
  exact (le_mul_of_one_le_right' hdegree).trans (by exact_mod_cast hweighted)

end RectangleUpper

end WeightedTorusJets.Geometry

end
end
end
end


end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_EvalOneInvariantJetMonomial
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

theorem eval_one_invariantJet_monomial (c : Fin 3 → ι → R) (a : Fin 3 → ℕ)
    (m : ι →₀ ℕ) (r : R) :
    MvPolynomial.eval (fun _ => 1) (invariantJet c a (MvPolynomial.monomial m r)) =
      ((∑ i, c 0 i * (m i : R)) ^ a 0 *
        (∑ i, c 1 i * (m i : R)) ^ a 1 *
        (∑ i, c 2 i * (m i : R)) ^ a 2) * r := by
  rw [invariantJet_monomial, MvPolynomial.smul_eval, MvPolynomial.eval_monomial]
  simp

end WeightedTorusJets.Geometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_TorusQuotientDimensionPosCotangentFinrankThree
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace WeightedTorusJets.Geometry

section SourceLocalLengthLower

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "torusCoordinateProduct" => (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))
local notation "TorusCoordRing" => Localization.Away torusCoordinateProduct

theorem source_local_torus_rectangle_graded_length_gt {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c)
    (v : Module.Basis (Fin 3) K (LinearMap.ker (dotProductEquiv K (Fin 4) c)))
    (q : PrimeSpectrum TorusCoordRing) (b : ℕ) (F : PolyRing)
    (hq : (rectangleJetIdeal
      (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet (fun j => (v j : Fin 4 → K)) a F))
      (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) b).IsMinimalPrime q.asIdeal)
    (hnext : rectangleJetIdeal
      (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet (fun j => (v j : Fin 4 → K)) a F))
      (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) (b + 1) ≤ q.asIdeal)
    (hpos : 1 ≤ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)))
    (hdim : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)) ≤ 4) :
    ((4 * N) ^ (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal))) : ℕ) <
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal ⧸
      Ideal.map (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal))
        (rectangleJetIdeal (fun a ↦ algebraMap PolyRing TorusCoordRing
            (invariantJet (fun j => (v j : Fin 4 → K)) a F))
          (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) b)) := by
  let p : Ideal PolyRing := q.asIdeal.comap (algebraMap PolyRing TorusCoordRing)
  have : p.IsPrime := Ideal.comap_isPrime _ q.asIdeal
  have : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers torusCoordinateProduct) (Localization.AtPrime q.asIdeal) q.asIdeal
  have hX (i : Fin 4) : MvPolynomial.X i ∉ p := by
    intro hi
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hi (torus_coordinate_isUnit i))
  have hx (i : Fin 4) : IsUnit
      (algebraMap PolyRing (Localization.AtPrime q.asIdeal) (MvPolynomial.X i)) :=
    IsLocalization.map_units (Localization.AtPrime q.asIdeal)
      (⟨MvPolynomial.X i, hX i⟩ : p.primeCompl)
  have hc0 : c ≠ 0 := by
    intro hzero
    exact hc.ne_zero (0 : Fin 4) (congrFun hzero 0)
  obtain ⟨I, hI, hD⟩ := exists_selected_independent_conormal_derivations
    (S := Localization.AtPrime q.asIdeal) p.primeCompl
    (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) hx c hc0 v
    (fun hsmall => torus_prime_residue_logarithmicForm_ne_zero_jb247 q hsmall c hc)
  change I.card = min (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
    (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal))) 3 at hI
  have hposI : I.Nonempty := Finset.card_pos.mp (by rw [hI]; omega)
  have hprimary := (local_torus_stage_primary_data (fun j => (v j : Fin 4 → K)) q
    (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) b F hq).1
  have hlower := derivativeStageIdeal_graded_length_lower_jb247
    (localTorusDerivationOverRat (fun j => (v j : Fin 4 → K)) q)
    (localTorusDerivationOverRat_commute _ q 0 1)
    (localTorusDerivationOverRat_commute _ q 0 2)
    (localTorusDerivationOverRat_commute _ q 1 2)
    (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) I hposI
    (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊)
    (fun j => (by decide : 2 ≤ 9).trans (rectangle_cutoff_ge_nine hH hHN j)) b
    (algebraMap TorusCoordRing (Localization.AtPrime q.asIdeal)
      (algebraMap PolyRing TorusCoordRing F))
    (local_torus_stage_le_maximal (fun j => (v j : Fin 4 → K)) q _ (b + 1) F hnext)
    (by simpa only [localTorusDerivationOverRat_cotangent_eq_direct (fun j => (v j : Fin 4 → K)) q p.primeCompl] using hD) hprimary
  have hnum := rectangle_floor_product_gt_nat hH hHN hpos hdim I hI
  rw [local_torus_derivativeStageIdeal_eq]
  rw [Finset.prod_coe_sort I (fun j : Fin 3 => ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊ + 1)] at hlower
  exact lt_of_lt_of_le (by exact_mod_cast hnum) hlower

end SourceLocalLengthLower



theorem uniform_rectangular_multiplicity
    {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c)
    (v : Module.Basis (Fin 3) ℂ
      (LinearMap.ker (dotProductEquiv ℂ (Fin 4) c)))
    (F : MvPolynomial (Fin 4) ℂ) (hF : F ∈ polynomialBox ℂ N)
    (hvanish : ∀ a : Fin 3 → ℕ,
      (∀ j, (a j : ℝ) ≤ rectangleThreshold (H : ℝ) (N : ℝ) j) →
        MvPolynomial.eval (fun _ ↦ 1)
          (invariantJet (fun j ↦ (v j : Fin 4 → ℂ)) a F) = 0) :
    F = 0 := by
  by_contra hF0
  obtain ⟨b, _, q, _, hq, hqnext, hpos, hdim⟩ :=
    torus_rectangle_shared_component_data hH hHN (fun j ↦ (v j : Fin 4 → ℂ)) F hF0 hvanish
  have hlength := source_local_torus_rectangle_graded_length_gt hH hHN c hc v q b F
    hq hqnext.le hpos hdim
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (hH.trans hHN)
  have hupper := rectangleJetIdeal_length_le q.asIdeal
    (fun j ↦ (v j : Fin 4 → ℂ))
    (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) b hN hF hq
  exact (not_lt_of_ge hupper) hlength



end WeightedTorusJets.Geometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_InvariantJetLinearMap
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

theorem eval_one_invariantJet_sum_monomials {κ : Type*} [Fintype κ]
    (c : Fin 3 → ι → R) (a : Fin 3 → ℕ) (m : κ → ι →₀ ℕ) (w : κ → R) :
    MvPolynomial.eval (fun _ => 1)
      (invariantJet c a (∑ k, MvPolynomial.monomial (m k) (w k))) =
      ∑ k,
        ((∑ i, c 0 i * (m k i : R)) ^ a 0 *
          (∑ i, c 1 i * (m k i : R)) ^ a 1 *
          (∑ i, c 2 i * (m k i : R)) ^ a 2) * w k := by
  change MvPolynomial.eval (fun _ => 1)
    (invariantJetLinearMap c a (∑ k, MvPolynomial.monomial (m k) (w k))) = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact eval_one_invariantJet_monomial c a (m k) (w k)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry
theorem detects_jet_rows_of_polynomial_detection_set
    {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    (c : Fin 3 → ι → K) (m : κ → ι →₀ ℕ) (hm : Function.Injective m)
    (s : Set (Fin 3 → ℕ))
    (hzero : ∀ f : MvPolynomial ι K,
      f ∈ Submodule.span K (Set.range fun k => MvPolynomial.monomial (m k) (1 : K)) →
      (∀ a ∈ s, MvPolynomial.eval (fun _ => 1) (invariantJet c a f) = 0) → f = 0) :
    ∀ w : κ → K, w ≠ 0 → ∃ a ∈ s,
      ∑ k, ((∑ i, c 0 i * (m k i : K)) ^ a 0 *
        (∑ i, c 1 i * (m k i : K)) ^ a 1 *
        (∑ i, c 2 i * (m k i : K)) ^ a 2) * w k ≠ 0 := by
  classical
  intro w hw
  by_contra! h
  have hmem : (∑ k, MvPolynomial.monomial (m k) (w k)) ∈
      Submodule.span K (Set.range fun k => MvPolynomial.monomial (m k) (1 : K)) := by
    apply Submodule.sum_mem
    intro k _
    have hmono := Submodule.smul_mem
      (Submodule.span K (Set.range fun k => MvPolynomial.monomial (m k) (1 : K)))
      (w k) (Submodule.subset_span ⟨k, rfl⟩)
    simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hmono
  have hF := hzero _ hmem (fun a ha => by
    rw [eval_one_invariantJet_sum_monomials]
    exact h a ha)
  have hlin : LinearIndependent K (fun k => MvPolynomial.monomial (m k) (1 : K)) :=
    (MvPolynomial.basisMonomials ι K).linearIndependent.comp m hm
  apply hw
  funext k
  apply Fintype.linearIndependent_iff.mp hlin w _ k
  simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hF

end WeightedTorusJets.Geometry

namespace WeightedTorusJets
theorem span_rows_eq_top_of_detects_set
    {K ι n : Type*} [Field K] [Fintype n]
    (s : Set ι) (R : ι → n → K)
    (hdetect : ∀ c : n → K, c ≠ 0 → ∃ a ∈ s, ∑ j, R a j * c j ≠ 0) :
    Submodule.span K (R '' s) = ⊤ := by
  classical
  apply (Submodule.map_eq_top_iff (e := dotProductEquiv K n)).mp
  rw [Submodule.map_span]
  apply Submodule.span_eq_top_of_ne_zero
  intro c hc
  obtain ⟨a, ha, hsum⟩ := hdetect c hc
  exact ⟨dotProductEquiv K n (R a),
    Set.mem_image_of_mem _ (Set.mem_image_of_mem R ha), hsum⟩

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

variable {K L ι κ : Type*} [Field K] [Field L] [Fintype ι] [Fintype κ]

theorem span_jet_rows_eq_top_of_polynomial_detection_set_over
    (φ : K →+* L) (c : Fin 3 → ι → K)
    (m : κ → ι →₀ ℕ) (hm : Function.Injective m) (s : Set (Fin 3 → ℕ))
    (hzero : ∀ f : MvPolynomial ι L,
      f ∈ Submodule.span L (Set.range fun k => MvPolynomial.monomial (m k) (1 : L)) →
      (∀ a ∈ s, MvPolynomial.eval (fun _ => 1)
        (invariantJet (fun j i => φ (c j i)) a f) = 0) → f = 0) :
    Submodule.span K ((fun a : Fin 3 → ℕ => fun k =>
      (∑ i, c 0 i * (m k i : K)) ^ a 0 *
        (∑ i, c 1 i * (m k i : K)) ^ a 1 *
        (∑ i, c 2 i * (m k i : K)) ^ a 2) '' s) = ⊤ := by
  apply WeightedTorusJets.span_rows_eq_top_of_detects_set
  intro w hw
  have hfw : (fun k => φ (w k)) ≠ 0 := by
    intro h
    apply hw
    funext k
    exact φ.injective (by simpa only [Pi.zero_apply, map_zero] using congr_fun h k)
  obtain ⟨a, ha, hsum⟩ := detects_jet_rows_of_polynomial_detection_set
    (fun j i => φ (c j i)) m hm s hzero (fun k => φ (w k)) hfw
  refine ⟨a, ha, fun h => hsum ?_⟩
  simpa only [map_sum, map_mul, map_pow, map_natCast, map_zero] using congr_arg φ h

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem source_eigenvalue_row_eq_galois_row {K : Type*} [Field K]
    (u : Fin 4 → K) (σ τ : K →+* K) (n : Fin 4 → ℕ) (a : Fin 3 → ℕ) :
    (∑ i, ![u, (fun i => σ (u i)), (fun i => (σ.comp τ) (u i))] 0 i * (n i : K)) ^ a 0 *
      (∑ i, ![u, (fun i => σ (u i)), (fun i => (σ.comp τ) (u i))] 1 i * (n i : K)) ^ a 1 *
      (∑ i, ![u, (fun i => σ (u i)), (fun i => (σ.comp τ) (u i))] 2 i * (n i : K)) ^ a 2 =
    (∑ i, (n i : K) * u i) ^ a 0 *
      σ (∑ i, (n i : K) * u i) ^ a 1 *
      (σ.comp τ) (∑ i, (n i : K) * u i) ^ a 2 := by
  simp [map_sum, mul_comm]

theorem source_rectangle_span_of_polynomial_zero_test
    {K κ : Type*} [Field K] [Fintype κ]
    (φ : K →+* ℂ) (u : Fin 4 → K) (σ τ : K →+* K)
    (H N : ℕ) (n : κ → Fin 4 → ℕ) (hninj : Function.Injective n)
    (hn : ∀ j i, n j i < N)
    (hzero : ∀ F : MvPolynomial (Fin 4) ℂ, F ∈ polynomialBox ℂ N →
      (∀ a : Fin 3 → ℕ,
        (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) →
        (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) →
        (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) →
        MvPolynomial.eval (fun _ => 1)
          (invariantJet (fun j i => φ (![u, (fun i => σ (u i)),
            (fun i => (σ.comp τ) (u i))] j i)) a F) = 0) → F = 0) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * u i
    Submodule.span K
      ((fun a : Fin 3 → ℕ => fun j => θ j ^ a 0 * σ (θ j) ^ a 1 *
        (σ.comp τ) (θ j) ^ a 2) '' {a : Fin 3 → ℕ |
          (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤ := by
  let m : κ → Fin 4 →₀ ℕ := fun j => Finsupp.equivFunOnFinite.symm (n j)
  let c : Fin 3 → Fin 4 → K := ![u, (fun i => σ (u i)), (fun i => (σ.comp τ) (u i))]
  have hm : Function.Injective m := by
    intro i j h
    apply hninj
    funext k
    exact congrArg (fun d : Fin 4 →₀ ℕ => d k) h
  have hmem : Submodule.span ℂ
      (Set.range fun j => MvPolynomial.monomial (m j) (1 : ℂ)) ≤ polynomialBox ℂ N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨fun i => (⟨n j i, hn j i⟩ : Fin N), rfl⟩
  have hs := span_jet_rows_eq_top_of_polynomial_detection_set_over φ c m hm
    {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}
    (fun F hF hvan => hzero F (hmem hF) (fun a h0 h1 h2 => hvan a ⟨h0, h1, h2⟩))
  simpa only [m, c, Finsupp.coe_equivFunOnFinite_symm,
    source_eigenvalue_row_eq_galois_row] using hs

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

variable {K : Type*} [Field K]

theorem biquadraticCoefficients_linearIndependent [Algebra ℚ K] {a b : K}
    (h : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K)) :
    LinearIndependent ℚ (biquadraticCoefficients a b) := by
  have ha : a ≠ 0 := by simpa using h.ne_zero 1
  have hb : b ≠ 0 := by simpa using h.ne_zero 2
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hscaled : ∑ j, (![ -c 3, -c 2, c 1, c 0] : Fin 4 → ℚ) j •
      (![1, a, b, a * b] : Fin 4 → K) j = 0 := by
    simp [Fin.sum_univ_succ, biquadraticCoefficients, Algebra.smul_def] at hc ⊢
    field_simp at hc
    linear_combination hc
  have hz := Fintype.linearIndependent_iff.mp h _ hscaled
  fin_cases i
  · simpa using hz 3
  · simpa using hz 2
  · simpa using hz 1
  · simpa using hz 0

theorem map_biquadraticCoefficients {L : Type*} [Field L] (f : K →+* L) (a b : K) :
    f ∘ biquadraticCoefficients a b = biquadraticCoefficients (f a) (f b) := by
  ext i
  fin_cases i <;> simp [biquadraticCoefficients]

theorem biquadraticCoefficients_linearIndependent_map [Algebra ℚ K]
    {L : Type*} [Field L] [Algebra ℚ L] (f : K →ₐ[ℚ] L) {a b : K}
    (h : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K)) :
    LinearIndependent ℚ (biquadraticCoefficients (f a) (f b)) := by
  have h' := (biquadraticCoefficients_linearIndependent h).map' f.toLinearMap
    (LinearMap.ker_eq_bot.mpr f.injective)
  exact (map_biquadraticCoefficients f.toRingHom a b) ▸ h'

theorem coe_biquadraticDirectionBasis [CharZero K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 3) :
    (biquadraticDirectionBasis ha hb i : Fin 4 → K) = biquadraticDirections a b i := by
  simp [biquadraticDirectionBasis]

end WeightedTorusJets

namespace WeightedTorusJets

 theorem source_same_witness_hyperplane {K : Type*} [Field K] [CharZero K]
    (a b : K) (φ : K →+* ℂ) (v : Module.Basis (Fin 4) ℚ K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b) (hτa : τ a = a) (hτb : τ b = -b) :
    LinearIndependent ℚ (biquadraticCoefficients (φ a) (φ b)) ∧
    ∃ D : Module.Basis (Fin 3) ℂ (LinearMap.ker (biquadraticForm (φ a) (φ b))),
      ∀ j i, (D j : Fin 4 → ℂ) i =
        φ ((![![1, a, b, a * b], (fun i => σ (![1, a, b, a * b] i)),
          (fun i => (σ * τ) (![1, a, b, a * b] i))] : Fin 3 → Fin 4 → K) j i) := by
  have hbase : LinearIndependent ℚ (![1, a, b, a * b] : Fin 4 → K) :=
    (funext hv) ▸ v.linearIndependent
  have ha : a ≠ 0 := by simpa using hbase.ne_zero 1
  have hb : b ≠ 0 := by simpa using hbase.ne_zero 2
  have hφa : φ a ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr ha
  have hφb : φ b ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr hb
  refine ⟨biquadraticCoefficients_linearIndependent_map φ.toRatAlgHom hbase,
    biquadraticDirectionBasis hφa hφb, ?_⟩
  intro j i
  rw [coe_biquadraticDirectionBasis]
  fin_cases j <;> fin_cases i <;>
    simp [biquadraticDirections, AlgEquiv.mul_apply, hσa, hσb, hτa, hτb]



theorem actual_biquadratic_rectangle_span_jb247_oai
    {K κ : Type*} [Field K] [NumberField K] [Fintype κ]
    (a b : K) (v : Module.Basis (Fin 4) ℚ K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b) (hτa : τ a = a) (hτb : τ b = -b)
    (H N : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (n : κ → Fin 4 → ℕ) (hninj : Function.Injective n) (hn : ∀ j i, n j i < N) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    Submodule.span K
      ((fun α : Fin 3 → ℕ => fun j => θ j ^ α 0 * σ (θ j) ^ α 1 *
        (σ * τ) (θ j) ^ α 2) '' {α : Fin 3 → ℕ |
          (α 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (α 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
          (α 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤ := by
  let φ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  obtain ⟨hc, D, hD⟩ := source_same_witness_hyperplane a b φ.toRingHom v hv σ τ
    hσa hσb hτa hτb
  have hform : biquadraticForm (φ a) (φ b) =
      dotProductEquiv ℂ (Fin 4) (biquadraticCoefficients (φ a) (φ b)) := by
    ext x
    rfl
  let D' := D.map (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hform))
  apply Geometry.source_rectangle_span_of_polynomial_zero_test φ.toRingHom
    ![1, a, b, a * b] σ.toRingHom τ.toRingHom H N n hninj hn
  intro F hF hvan
  apply Geometry.uniform_rectangular_multiplicity (Nat.succ_le_iff.mpr hH) hHN
    (biquadraticCoefficients (φ a) (φ b)) hc D' F hF
  intro α hα
  have h₀ := hα 0
  have h₁ := hα 1
  have h₂ := hα 2
  simp [Geometry.rectangleThreshold] at h₀ h₁ h₂
  have hdirs : (fun j => (D' j : Fin 4 → ℂ)) =
      (fun j i => φ (![![1, a, b, a * b],
        (fun i => σ.toRingHom (![1, a, b, a * b] i)),
        (fun i => (σ.toRingHom.comp τ.toRingHom) (![1, a, b, a * b] i))] j i)) := by
    funext j i
    simpa [D'] using hD j i
  rw [hdirs]
  exact hvan α h₀ (by simpa only [neg_div] using h₁) (by simpa only [neg_div] using h₂)

end WeightedTorusJets

end

end Erdos970

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos970.WeightedTorusJets.actual_biquadratic_rectangle_span_jb247_oai.{u_1, u_2} := @OAI.Erdos970.WeightedTorusJets.actual_biquadratic_rectangle_span_jb247_oai.{u_1, u_2}
