-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.Geometry.derivativeStageIdeal_graded_length_lower_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:53:38.146193+00:00
-- url     : https://prove2.me/submissions/bc72b33b-3727-49fd-a589-f3c77eb53361

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
import Definitions.Def_OAIQ247J009

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_HomogeneousDeformation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.finite_rectangularQuotient _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.WeightedTorusJets.Geometry.rectangularCoefficientDerivation_mk _root_.OAI.Erdos970.WeightedTorusJets.Geometry.rectangularCoefficientDerivation_zero _root_.OAI.Erdos970.WeightedTorusJets.Geometry.rectangularMap_mk _root_.OAI.Erdos970.WeightedTorusJets.Geometry.rectangularTaylorAlong_zero
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

open Module

open MvPolynomial

noncomputable section

noncomputable section

open scoped BigOperators DirectSum
open MvPolynomial

namespace WeightedTorusJets.Geometry

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial
open scoped DirectSum

variable {K σ : Type*} [Field K] [Finite σ]

open MvPolynomial

theorem finrank_rectangularQuotient {σ K : Type*} [Fintype σ] [Field K] (k : σ → ℕ) :
    Module.finrank K (MvPolynomial σ K ⧸ rectangularIdeal k) = ∏ i, k i := by
  classical
  rw [Module.finrank_eq_card_basis (rectangularQuotientBasis k)]
  simp

open MvPolynomial

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

end WeightedTorusJets.Geometry

end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_FiniteTypeFieldModelEquiv
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
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

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

theorem independent_functionals_surjective {k V ι : Type*} [Field k] [AddCommGroup V]
    [Module k V] [Finite ι] (f : ι → V →ₗ[k] k) (hf : LinearIndependent k f) :
    Function.Surjective (LinearMap.pi f) := by
  apply LinearMap.range_eq_top.mp
  rw [← Submodule.span_eq (LinearMap.range (LinearMap.pi f))]
  change Submodule.span k (Set.range (fun x i => f i x)) = ⊤
  apply span_flip_eq_top_iff_linearIndependent.mpr
  exact hf.map' (LinearMap.ltoFun k V k k) (LinearMap.ker_eq_bot.mpr DFunLike.coe_injective)

theorem exists_ideal_element_with_derivatives {ι : Type*} [Finite ι]
    (I : Ideal R) [I.IsMaximal] (D : ι → Derivation K R R)
    (hD : LinearIndependent (R ⧸ I) (fun i => derivationCotangentResidue (D i) I))
    (c : ι → R ⧸ I) :
    ∃ x : I, ∀ i, Ideal.Quotient.mk I (D i x) = c i := by
  let := Ideal.Quotient.field I
  obtain ⟨y, hy⟩ := independent_functionals_surjective
    (fun i => derivationCotangentResidue (D i) I) hD c
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective y
  exact ⟨x, fun i => congrFun hy i⟩



end WeightedTorusJets.Geometry

open scoped TensorProduct

open Module

end
end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_RectangleThreshold
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.finite_rectangularQuotient _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
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



noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem quotientDerivation_pow_mk (D : Derivation ℚ A A) (I : Ideal A)
    (hI : ∀ a ∈ I, D a ∈ I) (n : ℕ) (a : A) :
    ((quotientDerivation D I hI).toLinearMap ^ n) (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I ((D.toLinearMap ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, ih, Derivation.coeFn_coe,
        quotientDerivation_mk]

theorem coefficientDerivation_pow_monomial (σ : Type*) (D : Derivation ℚ A A)
    (n : ℕ) (d : σ →₀ ℕ) (a : A) :
    ((coefficientDerivation σ D).toLinearMap ^ n) (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d ((D.toLinearMap ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, ih, Derivation.coeFn_coe,
        coefficientDerivation_monomial]

theorem rectangularCoefficientDerivation_pow_monomial (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (n : ℕ) (d : σ →₀ ℕ) (a : A) :
    ((rectangularCoefficientDerivation σ k D).toLinearMap ^ n)
      (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial d a)) =
        Ideal.Quotient.mk (rectangularIdeal k)
          (MvPolynomial.monomial d ((D.toLinearMap ^ n) a)) := by
  rw [rectangularCoefficientDerivation, quotientDerivation_pow_mk,
    coefficientDerivation_pow_monomial]

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem rectangularMap_monomial (k : σ → ℕ) (f : R →+* S)
    (d : σ →₀ ℕ) (a : R) :
    rectangularMap k f (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial d a)) =
      Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial d (f a)) := by
  simp

end



noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem nilpotentDerivationExp_apply (D : Derivation ℚ A A)
    {n : ℕ} (hD : D.toLinearMap ^ n = 0) (a : A) :
    nilpotentDerivationExp D ⟨n, hD⟩ a =
      ∑ i ∈ Finset.range n, (i.factorial : ℚ)⁻¹ • ((D.toLinearMap ^ i) a) := by
  simp [nilpotentDerivationExp, IsNilpotent.exp_eq_sum hD]

theorem truncatedTaylor_apply (D : Derivation ℚ A A) (u : A)
    (hu : D u = 0) {n : ℕ} (hn : u ^ n = 0) (a : A) :
    truncatedTaylor D u hu hn a =
      ∑ i ∈ Finset.range n, (i.factorial : ℚ)⁻¹ • (u ^ i * (D.toLinearMap ^ i) a) := by
  rw [truncatedTaylor, nilpotentDerivationExp_apply (u • D)
    (scaledDerivation_pow_eq_zero D u hu hn)]
  simp only [scaledDerivation_pow_apply D u hu]

theorem map_truncatedTaylor {B : Type*} [CommRing B] [Algebra ℚ B]
    (f : A →+* B) (D : Derivation ℚ A A) (u : A) (hu : D u = 0)
    {n : ℕ} (hn : u ^ n = 0) (hnpos : 0 < n) (hfu : f u = 0) (a : A) :
    f (truncatedTaylor D u hu hn a) = f a := by
  rw [truncatedTaylor_apply]
  simp only [map_sum, map_rat_smul, map_mul, map_pow, hfu]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    simp [zero_pow hb0]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hnpos))

end



noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem rectangularTaylorAlong_monomial (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) (d : σ →₀ ℕ) (a : A) :
    rectangularTaylorAlong σ k D i
      (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial d a)) =
      ∑ n ∈ Finset.range (k i), (n.factorial : ℚ)⁻¹ •
        Ideal.Quotient.mk (rectangularIdeal k)
          (MvPolynomial.monomial (Finsupp.single i n + d) ((D.toLinearMap ^ n) a)) := by
  rw [rectangularTaylorAlong, truncatedTaylor_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [rectangularCoefficientDerivation_pow_monomial,
    ← map_pow, ← map_mul, ← MvPolynomial.monomial_single_add]

theorem rectangularTaylorThree_apply {B : Type*} [CommRing B] [Algebra ℚ B]
    (σ : Type*) (k : σ → ℕ) (D₁ D₂ D₃ : Derivation ℚ A A)
    (i₁ i₂ i₃ : σ) (f : A →+* B) (a : A) :
    rectangularTaylorThree σ k D₁ D₂ D₃ i₁ i₂ i₃ f a =
      ∑ n₃ ∈ Finset.range (k i₃), ∑ n₂ ∈ Finset.range (k i₂),
        ∑ n₁ ∈ Finset.range (k i₁),
          (((n₃.factorial : ℚ)⁻¹ * (n₂.factorial : ℚ)⁻¹) * (n₁.factorial : ℚ)⁻¹) •
            Ideal.Quotient.mk (rectangularIdeal k)
              (MvPolynomial.monomial
                (Finsupp.single i₁ n₁ + (Finsupp.single i₂ n₂ + Finsupp.single i₃ n₃))
                (f ((D₁.toLinearMap ^ n₁) ((D₂.toLinearMap ^ n₂) ((D₃.toLinearMap ^ n₃) a))))) := by
  simp only [rectangularTaylorThree, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, MvPolynomial.C_apply]
  simp only [rectangularTaylorAlong_monomial, map_sum, map_rat_smul,
    rectangularMap_monomial, Finset.smul_sum, smul_smul, add_zero, mul_assoc]

theorem rectangularTaylorThree_two_apply {B : Type*} [CommRing B] [Algebra ℚ B]
    (σ : Type*) (k : σ → ℕ) (D₁ D₂ : Derivation ℚ A A)
    (i₁ i₂ : σ) (f : A →+* B) (a : A) :
    rectangularTaylorThree σ k D₁ D₂ 0 i₁ i₂ i₂ f a =
      ∑ n₂ ∈ Finset.range (k i₂), ∑ n₁ ∈ Finset.range (k i₁),
        ((n₂.factorial : ℚ)⁻¹ * (n₁.factorial : ℚ)⁻¹) •
          Ideal.Quotient.mk (rectangularIdeal k)
            (MvPolynomial.monomial (Finsupp.single i₁ n₁ + Finsupp.single i₂ n₂)
              (f ((D₁.toLinearMap ^ n₁) ((D₂.toLinearMap ^ n₂) a)))) := by
  simp only [rectangularTaylorThree, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, rectangularTaylorAlong_zero, AlgHom.id_apply, MvPolynomial.C_apply]
  simp only [rectangularTaylorAlong_monomial, map_sum, map_rat_smul,
    rectangularMap_monomial, Finset.smul_sum, smul_smul, add_zero]

theorem rectangularTaylorThree_one_apply {B : Type*} [CommRing B] [Algebra ℚ B]
    (σ : Type*) (k : σ → ℕ) (D : Derivation ℚ A A) (i : σ)
    (f : A →+* B) (a : A) :
    rectangularTaylorThree σ k D 0 0 i i i f a =
      ∑ n ∈ Finset.range (k i), (n.factorial : ℚ)⁻¹ •
        Ideal.Quotient.mk (rectangularIdeal k)
          (MvPolynomial.monomial (Finsupp.single i n) (f ((D.toLinearMap ^ n) a))) := by
  simp only [rectangularTaylorThree, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, rectangularTaylorAlong_zero, AlgHom.id_apply, MvPolynomial.C_apply]
  simp only [rectangularTaylorAlong_monomial, map_sum, map_rat_smul,
    rectangularMap_monomial, add_zero]

theorem rectangularTaylorThree_residue {B : Type*} [CommRing B] [Algebra ℚ B]
    (σ : Type*) (k : σ → ℕ) (hk : ∀ i, k i ≠ 0)
    (D₁ D₂ D₃ : Derivation ℚ A A) (i₁ i₂ i₃ : σ) (f : A →+* B)
    (ε : (MvPolynomial σ B ⧸ rectangularIdeal k) →+* B)
    (hε : ∀ p, ε (Ideal.Quotient.mk (rectangularIdeal k) p) = MvPolynomial.constantCoeff p)
    (a : A) :
    ε (rectangularTaylorThree σ k D₁ D₂ D₃ i₁ i₂ i₃ f a) = f a := by
  let g := ε.comp (rectangularMap k f)
  have hg (i : σ) : g (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i)) = 0 := by
    simp [g, hε]
  have hstep (D : Derivation ℚ A A) (i : σ) (p) :
      g (rectangularTaylorAlong σ k D i p) = g p := by
    apply map_truncatedTaylor g _ _ _ _ (Nat.pos_of_ne_zero (hk i)) (hg i)
  change g (rectangularTaylorAlong σ k D₁ i₁
    (rectangularTaylorAlong σ k D₂ i₂
      (rectangularTaylorAlong σ k D₃ i₃
        (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C a))))) = f a
  rw [hstep, hstep, hstep]
  simp [g, hε]

end

end WeightedTorusJets.Geometry

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DerivationJet
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

theorem mixed_iterate_add {A : Type*} (D : Fin 3 → A → A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (a b : Fin 3 → ℕ) (x : A) :
    (D 0)^[a 0 + b 0] ((D 1)^[a 1 + b 1] ((D 2)^[a 2 + b 2] x)) =
      (D 0)^[a 0] ((D 1)^[a 1] ((D 2)^[a 2]
        ((D 0)^[b 0] ((D 1)^[b 1] ((D 2)^[b 2] x))))) := by
  simp only [Function.iterate_add_apply]
  rw [(h01.iterate_iterate (b 0) (a 1)).eq,
    (h12.iterate_iterate (b 1) (a 2)).eq,
    (h02.iterate_iterate (b 0) (a 2)).eq]

theorem mixed_derivation_pow_add {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (D : Fin 3 → Derivation R A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (a b : Fin 3 → ℕ) (x : A) :
    ((D 0).toLinearMap ^ (a 0 + b 0))
      (((D 1).toLinearMap ^ (a 1 + b 1)) (((D 2).toLinearMap ^ (a 2 + b 2)) x)) =
      ((D 0).toLinearMap ^ a 0) (((D 1).toLinearMap ^ a 1) (((D 2).toLinearMap ^ a 2)
        (((D 0).toLinearMap ^ b 0) (((D 1).toLinearMap ^ b 1)
          (((D 2).toLinearMap ^ b 2) x))))) := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using mixed_iterate_add
    (fun i => (D i : A → A)) h01 h02 h12 a b x

theorem derivation_pow_mixed_derivation_pow {R A : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A]
    (D : Fin 3 → Derivation R A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (j : Fin 3) (n : ℕ) (b : Fin 3 → ℕ) (x : A) :
    ((D j).toLinearMap ^ n)
      (((D 0).toLinearMap ^ b 0) (((D 1).toLinearMap ^ b 1)
        (((D 2).toLinearMap ^ b 2) x))) =
    ((D 0).toLinearMap ^ ((b + (Pi.single j n : Fin 3 → ℕ)) 0))
      (((D 1).toLinearMap ^ ((b + (Pi.single j n : Fin 3 → ℕ)) 1))
        (((D 2).toLinearMap ^ ((b + (Pi.single j n : Fin 3 → ℕ)) 2)) x)) := by
  have h := mixed_derivation_pow_add D h01 h02 h12 (Pi.single j n) b x
  fin_cases j <;> simpa [Pi.single_apply, add_comm] using h.symm

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets.Geometry

theorem add_jet_indices_le_next_stage {σ : Type*} (a α t : σ → ℕ) (b : ℕ)
    (ha : ∀ j, a j ≤ b * t j) (hα : ∀ j, α j ≤ t j) :
    ∀ j, (a + α) j ≤ (b + 1) * t j := by
  intro j
  simpa [Pi.add_apply, Nat.add_mul] using Nat.add_le_add (ha j) (hα j)



noncomputable section

variable {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

omit [Algebra ℚ B] in
theorem derivativeStageIdeal_le_ker_iff (D : Fin 3 → Derivation ℚ A A)
    (t : Fin 3 → ℕ) (b : ℕ) (F : A) (f : A →+* B) :
    derivativeStageIdeal D t b F ≤ RingHom.ker f ↔
      ∀ β, (∀ j, β j ≤ b * t j) → f (derivationJet D β F) = 0 := by
  rw [derivativeStageIdeal, Ideal.span_le, Set.image_subset_iff]
  rfl

theorem derivationJet_shift (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (j : Fin 3) (n : ℕ) (β : Fin 3 → ℕ) (a : A) :
    ((D j).toLinearMap ^ n) (derivationJet D β a) =
      derivationJet D (β + Pi.single j n) a :=
  derivation_pow_mixed_derivation_pow D h01 h02 h12 j n β a

theorem single_index_le {j : Fin 3} {n : ℕ} (t : Fin 3 → ℕ) (hn : n ≤ t j) :
    ∀ l, (Pi.single j n : Fin 3 → ℕ) l ≤ t l := by
  intro l
  by_cases h : l = j
  · simpa [h] using hn
  · simp [Pi.single_eq_of_ne h]

theorem pair_index_le {i j : Fin 3} (hij : i ≠ j) {m n : ℕ} (t : Fin 3 → ℕ)
    (hm : m ≤ t i) (hn : n ≤ t j) :
    ∀ l, ((Pi.single i m : Fin 3 → ℕ) + (Pi.single j n : Fin 3 → ℕ)) l ≤ t l := by
  intro l
  by_cases hi : l = i
  · subst l
    simpa [Pi.single_apply, hij] using hm
  · by_cases hj : l = j
    · subst l
      simpa [Pi.single_apply, Ne.symm hij] using hn
    · simp [hi, hj]

theorem triple_index_le {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {m n p : ℕ} (t : Fin 3 → ℕ) (hm : m ≤ t i) (hn : n ≤ t j) (hp : p ≤ t k) :
    ∀ l, (((Pi.single i m : Fin 3 → ℕ) + (Pi.single j n : Fin 3 → ℕ)) +
      (Pi.single k p : Fin 3 → ℕ)) l ≤ t l := by
  intro l
  by_cases hi : l = i
  · subst l
    simpa [Pi.single_apply, hij, hik] using hm
  · by_cases hj : l = j
    · subst l
      simpa [Pi.single_apply, Ne.symm hij, hjk] using hn
    · by_cases hk : l = k
      · subst l
        simpa [Pi.single_apply, Ne.symm hik, Ne.symm hjk] using hp
      · simp [hi, hj, hk]

theorem derivativeStageIdeal_le_ker_taylor_one
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i : I) (t : Fin 3 → ℕ) (b : ℕ) (F : A) (f : A →+* B)
    (hvanish : ∀ β, (∀ j, β j ≤ (b + 1) * t j) → f (derivationJet D β F) = 0) :
    derivativeStageIdeal D t b F ≤ RingHom.ker
      (rectangularTaylorThree I (fun j => t j + 1) (D i) 0 0 i i i f) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨β, hβ, rfl⟩
  change rectangularTaylorThree _ _ _ _ _ _ _ _ _ _ = 0
  rw [rectangularTaylorThree_one_apply]
  apply Finset.sum_eq_zero
  intro n hn
  have hbound := add_jet_indices_le_next_stage β (Pi.single (i : Fin 3) n) t b hβ
    (single_index_le t (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))
  rw [derivationJet_shift D h01 h02 h12, hvanish _ hbound]
  simp

theorem derivativeStageIdeal_le_ker_taylor_two
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i j : I) (hij : i ≠ j)
    (t : Fin 3 → ℕ) (b : ℕ) (F : A) (f : A →+* B)
    (hvanish : ∀ β, (∀ l, β l ≤ (b + 1) * t l) → f (derivationJet D β F) = 0) :
    derivativeStageIdeal D t b F ≤ RingHom.ker
      (rectangularTaylorThree I (fun l => t l + 1) (D i) (D j) 0 i j j f) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨β, hβ, rfl⟩
  change rectangularTaylorThree _ _ _ _ _ _ _ _ _ _ = 0
  rw [rectangularTaylorThree_two_apply]
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  have hji : (j : Fin 3) ≠ (i : Fin 3) := fun he => hij (Subtype.ext he.symm)
  have hbound := add_jet_indices_le_next_stage β
    ((Pi.single (j : Fin 3) n : Fin 3 → ℕ) + (Pi.single (i : Fin 3) m : Fin 3 → ℕ)) t b hβ
    (pair_index_le hji t (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
  rw [derivationJet_shift D h01 h02 h12, derivationJet_shift D h01 h02 h12]
  rw [add_assoc, hvanish _ hbound]
  simp

theorem derivativeStageIdeal_le_ker_taylor_three
    (D : Fin 3 → Derivation ℚ A A)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (I : Finset (Fin 3)) (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : Fin 3 → ℕ) (b : ℕ) (F : A) (f : A →+* B)
    (hvanish : ∀ β, (∀ l, β l ≤ (b + 1) * t l) → f (derivationJet D β F) = 0) :
    derivativeStageIdeal D t b F ≤ RingHom.ker
      (rectangularTaylorThree I (fun l => t l + 1) (D i) (D j) (D k) i j k f) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨β, hβ, rfl⟩
  change rectangularTaylorThree _ _ _ _ _ _ _ _ _ _ = 0
  rw [rectangularTaylorThree_apply]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  have hkj : (k : Fin 3) ≠ (j : Fin 3) := fun he => hjk (Subtype.ext he.symm)
  have hki : (k : Fin 3) ≠ (i : Fin 3) := fun he => hik (Subtype.ext he.symm)
  have hji : (j : Fin 3) ≠ (i : Fin 3) := fun he => hij (Subtype.ext he.symm)
  have hbound := add_jet_indices_le_next_stage β
    (((Pi.single (k : Fin 3) p : Fin 3 → ℕ) + (Pi.single (j : Fin 3) n : Fin 3 → ℕ)) +
      (Pi.single (i : Fin 3) m : Fin 3 → ℕ)) t b hβ
    (triple_index_le hkj hki hji t (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
  rw [derivationJet_shift D h01 h02 h12, derivationJet_shift D h01 h02 h12,
    derivationJet_shift D h01 h02 h12]
  simp only [add_assoc] at hbound
  rw [add_assoc, add_assoc, hvanish _ hbound]
  simp

end

end WeightedTorusJets.Geometry

noncomputable section

namespace WeightedTorusJets.Geometry

theorem local_module_length_eq_finrank {K A M : Type*} [Field K] [CommRing A]
    [IsLocalRing A] [Algebra K A] [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [Module.Finite K M]
    (hκ : Function.Surjective (algebraMap K (IsLocalRing.ResidueField A))) :
    Module.length A M = Module.finrank K M := by
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField A) = 1 := by
    rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField A)
      (IsLocalRing.residue_surjective (R := K))]
    rw [Module.length_eq_of_surjective (M := IsLocalRing.ResidueField A) hκ]
    exact Module.length_eq_one _ _
  have h := IsLocalRing.length_restrictScalars K A M
  rw [hres, mul_one, Module.length_eq_finrank K M] at h
  exact h.symm

theorem local_length_eq_finrank {K A : Type*} [Field K] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Module.Finite K A]
    (hκ : Function.Surjective (algebraMap K (IsLocalRing.ResidueField A))) :
    Module.length A A = Module.finrank K A :=
  local_module_length_eq_finrank hκ

theorem isNilpotent_of_mem_nilpotent_ideal {A : Type*} [CommRing A]
    (I : Ideal A) (hI : IsNilpotent I) {a : A} (ha : a ∈ I) : IsNilpotent a := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  have h := Ideal.pow_mem_pow ha n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

theorem isLocalRing_of_nilpotent_augmentation {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (ε : A →ₐ[K] K) (hε : IsNilpotent (RingHom.ker ε)) :
    IsLocalRing A := by
  have : Nontrivial A := ε.toRingHom.domain_nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  by_cases ha : ε a = 0
  · exact Or.inr (isNilpotent_of_mem_nilpotent_ideal _ hε ha).isUnit_one_sub
  · apply Or.inl
    have hn : IsNilpotent (a - algebraMap K A (ε a)) :=
      isNilpotent_of_mem_nilpotent_ideal _ hε (by simp)
    simpa using hn.isUnit_add_left_of_commute
      ((isUnit_iff_ne_zero.mpr ha).map (algebraMap K A)) (Commute.all _ _)

theorem residue_surjective_of_nilpotent_augmentation {K A : Type*} [Field K]
    [CommRing A] [Algebra K A] [IsLocalRing A] (ε : A →ₐ[K] K)
    (hε : IsNilpotent (RingHom.ker ε)) :
    Function.Surjective (algebraMap K (IsLocalRing.ResidueField A)) := by
  intro b
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective b
  refine ⟨ε a, ?_⟩
  have hn : IsNilpotent (a - algebraMap K A (ε a)) :=
    isNilpotent_of_mem_nilpotent_ideal _ hε (by simp)
  have hm : a - algebraMap K A (ε a) ∈ IsLocalRing.maximalIdeal A := hn.not_isUnit
  have he := (IsLocalRing.residue_eq_zero_iff _).mpr hm
  rw [map_sub, sub_eq_zero] at he
  exact he.symm

theorem length_eq_finrank_of_nilpotent_augmentation {K A : Type*} [Field K]
    [CommRing A] [Algebra K A] [Module.Finite K A] (ε : A →ₐ[K] K)
    (hε : IsNilpotent (RingHom.ker ε)) :
    Module.length A A = Module.finrank K A := by
  let := isLocalRing_of_nilpotent_augmentation ε hε
  exact local_length_eq_finrank (residue_surjective_of_nilpotent_augmentation ε hε)

open MvPolynomial

open MvPolynomial

theorem isNilpotent_map_idealOfVars_of_pow_mem
    {σ K : Type*} [Finite σ] [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (k : σ → ℕ)
    (hk : ∀ i, (X i : MvPolynomial σ K) ^ k i ∈ J) :
    IsNilpotent ((idealOfVars σ K).map (Ideal.Quotient.mk J)) := by
  apply ((idealOfVars_fg σ K).map (Ideal.Quotient.mk J)).isNilpotent_iff_le_nilradical.mpr
  rw [Ideal.map_le_iff_le_comap, idealOfVars, Ideal.span_le, Set.range_subset_iff]
  intro i
  change IsNilpotent (Ideal.Quotient.mk J (X i))
  refine ⟨k i, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hk i)

theorem isNilpotent_ker_quotientAugmentation
    {σ K : Type*} [Finite σ] [CommRing K]
    (J : Ideal (MvPolynomial σ K))
    (hJ : J ≤ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K))
    (k : σ → ℕ) (hk : ∀ i, (X i : MvPolynomial σ K) ^ k i ∈ J) :
    IsNilpotent (RingHom.ker (quotientAugmentation J hJ).toRingHom) := by
  rw [ker_quotientAugmentation]
  exact isNilpotent_map_idealOfVars_of_pow_mem J k hk

theorem isNilpotent_ker_rectangularAugmentation
    {σ K : Type*} [Finite σ] [CommRing K] (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) :
    IsNilpotent (RingHom.ker (rectangularAugmentation (K := K) k hk).toRingHom) := by
  apply isNilpotent_ker_quotientAugmentation _ _ k
  intro i
  exact Ideal.subset_span ⟨i, rfl⟩



end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem surjective_of_nilpotent_ideal_lifts {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal B) (hI : IsNilpotent I)
    (h₀ : ∀ b : B, ∃ a : A, b - f a ∈ I)
    (h₁ : ∀ b ∈ I, ∃ a : A, f a ∈ I ∧ b - f a ∈ I ^ 2) :
    Function.Surjective f := by
  have liftPower : ∀ n : ℕ, ∀ b ∈ I ^ n,
      ∃ a : A, f a ∈ I ^ n ∧ b - f a ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        intro b _
        obtain ⟨a, ha⟩ := h₀ b
        exact ⟨a, by simp, by simpa using ha⟩
    | succ n hn =>
        intro b hb
        rw [pow_succ] at hb
        refine Submodule.mul_induction_on hb ?_ ?_
        · intro x hx y hy
          obtain ⟨a, ha, hxa⟩ := hn x hx
          obtain ⟨c, hc, hyc⟩ := h₁ y hy
          refine ⟨a * c, ?_, ?_⟩
          · rw [map_mul, pow_succ]
            exact Ideal.mul_mem_mul ha hc
          · have hleft : (x - f a) * y ∈ I ^ (n + 1 + 1) := by
              rw [pow_succ]
              exact Ideal.mul_mem_mul hxa hy
            have hright : f a * (y - f c) ∈ I ^ (n + 1 + 1) := by
              rw [show n + 1 + 1 = n + 2 by omega, pow_add]
              exact Ideal.mul_mem_mul ha hyc
            convert (I ^ (n + 1 + 1)).add_mem hleft hright using 1
            all_goals try with_reducible_and_instances rfl
            simp only [map_mul]
            ring
        · intro x y hx hy
          obtain ⟨a, ha, hxa⟩ := hx
          obtain ⟨c, hc, hyc⟩ := hy
          refine ⟨a + c, ?_, ?_⟩
          · simpa only [map_add] using (I ^ (n + 1)).add_mem ha hc
          · convert (I ^ (n + 1 + 1)).add_mem hxa hyc using 1
            all_goals try with_reducible_and_instances rfl
            simp only [map_add]
            ring
  have liftAll : ∀ n : ℕ, ∀ b : B, ∃ a : A, b - f a ∈ I ^ n := by
    intro n
    induction n with
    | zero => exact fun b => ⟨0, by simp⟩
    | succ n hn =>
        intro b
        obtain ⟨a, ha⟩ := hn b
        obtain ⟨c, _, hc⟩ := liftPower n (b - f a) ha
        refine ⟨a + c, ?_⟩
        convert hc using 1
        all_goals try with_reducible_and_instances rfl
        simp only [map_add]
        ring
  obtain ⟨n, hn⟩ := hI
  intro b
  obtain ⟨a, ha⟩ := liftAll n b
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at ha
  exact ⟨a, (sub_eq_zero.mp ha).symm⟩

end WeightedTorusJets.Geometry

end
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

theorem rectangularTaylorThree_augmentation {R B σ : Type*}
    [CommRing R] [Algebra ℚ R] [CommRing B] [Algebra ℚ B]
    (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) (D₁ D₂ D₃ : Derivation ℚ R R)
    (i₁ i₂ i₃ : σ) (f : R →+* B) (a : R) :
    rectangularAugmentation k hk (rectangularTaylorThree σ k D₁ D₂ D₃ i₁ i₂ i₃ f a) = f a :=
  rectangularTaylorThree_residue σ k hk D₁ D₂ D₃ i₁ i₂ i₃ f
    (rectangularAugmentation k hk).toRingHom (fun p => quotientAugmentation_mk _ _ p) a

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_PolynomialLinearCoefficients
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
open scoped BigOperators
noncomputable section
noncomputable section

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem rectangularAugmentationCotangentEquiv_toCotangent_mk
    {σ K : Type*} [Fintype σ] [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i) (p : idealOfVars σ K) (i : σ) :
    rectangularAugmentationCotangentEquiv k hk
      ((RingHom.ker (rectangularAugmentation (K := K) k
        (fun j => by have := hk j; omega)).toRingHom).toCotangent
        ⟨Ideal.Quotient.mk _ p, by
          change quotientAugmentation (K := K) _ _
            (Ideal.Quotient.mk _ (p : MvPolynomial σ K)) = 0
          rw [quotientAugmentation_mk]
          exact (congrArg (fun J : Ideal (MvPolynomial σ K) =>
            (p : MvPolynomial σ K) ∈ J) ker_constantCoeff_eq_idealOfVars).mpr p.property⟩) i =
      (p : MvPolynomial σ K).coeff (Finsupp.single i 1) := by
  let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range fun j => X j ^ k j)
  let h₀ : J ≤ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) :=
    rectangularIdeal_le_ker_constantCoeff k (fun j => by have := hk j; omega)
  let n : Ideal (MvPolynomial σ K ⧸ J) := RingHom.ker (quotientAugmentation J h₀).toRingHom
  have hp₀ : constantCoeff (p : MvPolynomial σ K) = 0 :=
    (congrArg (fun I : Ideal (MvPolynomial σ K) =>
      (p : MvPolynomial σ K) ∈ I) ker_constantCoeff_eq_idealOfVars).mpr p.property
  have hqp : Ideal.Quotient.mk J (p : MvPolynomial σ K) ∈ n := by
    change quotientAugmentation J h₀ (Ideal.Quotient.mk J p) = 0
    simpa only [quotientAugmentation_mk] using hp₀
  change polynomialQuotientCotangentEquiv J (rectangularIdeal_le_vars_square k hk)
    (cotangentEquivOfEqOver K n _ (ker_quotientAugmentation J h₀)
      (n.toCotangent ⟨Ideal.Quotient.mk J p, hqp⟩)) i = _
  rw [cotangentEquivOfEqOver_toCotangent]
  exact polynomialQuotientCotangentEquiv_map_toCotangent J _ p i

theorem rectangularAugmentation_linear_representative
    {σ K : Type*} [Fintype σ] [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i)
    (b : RingHom.ker (rectangularAugmentation (K := K) k
      (fun j => by have := hk j; omega)).toRingHom) :
    (b : MvPolynomial σ K ⧸ Ideal.span (Set.range fun j => (X j : MvPolynomial σ K) ^ k j)) -
      ∑ i, (rectangularAugmentationCotangentEquiv k hk
        ((RingHom.ker (rectangularAugmentation (K := K) k
          (fun j => by have := hk j; omega)).toRingHom).toCotangent b)) i •
        Ideal.Quotient.mk _ (X i) ∈
      (RingHom.ker (rectangularAugmentation (K := K) k
        (fun j => by have := hk j; omega)).toRingHom) ^ 2 := by
  classical
  let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range fun j => X j ^ k j)
  let N : Ideal (MvPolynomial σ K ⧸ J) := RingHom.ker
    (rectangularAugmentation (K := K) k (fun j => by have := hk j; omega)).toRingHom
  let e := rectangularAugmentationCotangentEquiv (K := K) k hk
  let c : σ → K := e (N.toCotangent b)
  let p : MvPolynomial σ K := ∑ i, c i • X i
  have hp : p ∈ idealOfVars σ K := by
    apply Ideal.sum_mem
    intro i _
    exact ((idealOfVars σ K).restrictScalars K).smul_mem (c i)
      (Ideal.subset_span ⟨i, rfl⟩)
  have hpn : Ideal.Quotient.mk J p ∈ N := by
    change quotientAugmentation (K := K) _ _ (Ideal.Quotient.mk J p) = 0
    rw [quotientAugmentation_mk]
    exact (congrArg (fun I : Ideal (MvPolynomial σ K) => p ∈ I)
      ker_constantCoeff_eq_idealOfVars).mpr hp
  have hc : e (N.toCotangent ⟨Ideal.Quotient.mk J p, hpn⟩) = c := by
    ext i
    exact (rectangularAugmentationCotangentEquiv_toCotangent_mk k hk ⟨p, hp⟩ i).trans
      (by simp [p, coeff_X, Finsupp.single_left_inj, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul])
  have hq : Ideal.Quotient.mk J p = ∑ i, c i • Ideal.Quotient.mk J (X i) := by
    change (Ideal.Quotient.mkₐ K J) p = _
    simp only [p, map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk]
  have hdiff := N.toCotangent_eq.mp (e.injective hc.symm)
  simpa only [hq] using hdiff



end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem taylor_sum_sub_first_order_mem {A : Type*} [CommRing A] [Algebra ℚ A]
    (D : Derivation ℚ A A) (I : Ideal A) {u : A} (hu : u ∈ I)
    {n : ℕ} (hn : 2 ≤ n) (a : A) :
    (∑ i ∈ Finset.range n, (i.factorial : ℚ)⁻¹ • (u ^ i * (D.toLinearMap ^ i) a)) -
      (a + u * D a) ∈ I ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => simp [Finset.sum_range_succ]
  | succ n hn ih =>
      have hu' : u ^ n ∈ I ^ 2 := Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hu n)
      have hterm : (n.factorial : ℚ)⁻¹ • (u ^ n * (D.toLinearMap ^ n) a) ∈ I ^ 2 := by
        rw [Algebra.smul_def]
        exact (I ^ 2).mul_mem_left _ ((I ^ 2).mul_mem_right _ hu')
      rw [Finset.sum_range_succ]
      convert (I ^ 2).add_mem ih hterm using 1
      all_goals try with_reducible_and_instances rfl
      ring

theorem ringHom_comp_sub_first_order_mem {A : Type*} [CommRing A]
    (I : Ideal A) (f g : A →+* A)
    (hf : ∀ x ∈ I, f x - x ∈ I ^ 2) {a : A} (hg : g a - a ∈ I) :
    f (g a) - (f a + g a - a) ∈ I ^ 2 := by
  have h := hf (g a - a) hg
  rw [map_sub] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring



variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem truncatedTaylor_sub_first_order_mem (D : Derivation ℚ A A) (I : Ideal A)
    (u : A) (hDu : D u = 0) {n : ℕ} (hun : u ^ n = 0) (hn : 2 ≤ n)
    (hu : u ∈ I) (a : A) :
    truncatedTaylor D u hDu hun a - (a + u * D a) ∈ I ^ 2 := by
  rw [truncatedTaylor_apply]
  exact taylor_sum_sub_first_order_mem D I hu hn a

theorem truncatedTaylor_sub_self_mem (D : Derivation ℚ A A) (I : Ideal A)
    (u : A) (hDu : D u = 0) {n : ℕ} (hun : u ^ n = 0) (hn : 2 ≤ n)
    (hu : u ∈ I) (a : A) :
    truncatedTaylor D u hDu hun a - a ∈ I := by
  have h := (Ideal.pow_le_self (by decide : 2 ≠ 0))
    (truncatedTaylor_sub_first_order_mem D I u hDu hun hn hu a)
  convert I.add_mem h (I.mul_mem_right (D a) hu) using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem truncatedTaylor_sub_self_mem_sq (D : Derivation ℚ A A) (I : Ideal A)
    (u : A) (hDu : D u = 0) {n : ℕ} (hun : u ^ n = 0) (hn : 2 ≤ n)
    (hu : u ∈ I) (hDI : ∀ a ∈ I, D a ∈ I) {a : A} (ha : a ∈ I) :
    truncatedTaylor D u hDu hun a - a ∈ I ^ 2 := by
  have h := truncatedTaylor_sub_first_order_mem D I u hDu hun hn hu a
  have hc : u * D a ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hu (hDI a ha)
  convert (I ^ 2).add_mem h hc using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [Algebra ℚ A] in

theorem ringHom_comp3_sub_first_order_mem (I : Ideal A) (f₁ f₂ f₃ : A →+* A)
    (hf₁ : ∀ x ∈ I, f₁ x - x ∈ I ^ 2)
    (hf₂ : ∀ x ∈ I, f₂ x - x ∈ I ^ 2)
    (hg₂ : ∀ x, f₂ x - x ∈ I)
    {a e₁ e₂ e₃ : A} (hg₃ : f₃ a - a ∈ I)
    (h₁ : f₁ a - (a + e₁) ∈ I ^ 2)
    (h₂ : f₂ a - (a + e₂) ∈ I ^ 2)
    (h₃ : f₃ a - (a + e₃) ∈ I ^ 2) :
    f₁ (f₂ (f₃ a)) - (a + e₁ + e₂ + e₃) ∈ I ^ 2 := by
  have h23 : f₂ (f₃ a) - a ∈ I := by
    convert I.add_mem (hg₂ (f₃ a)) hg₃ using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hc₁ := ringHom_comp_sub_first_order_mem I f₁ (f₂.comp f₃) hf₁ h23
  have hc₂ := ringHom_comp_sub_first_order_mem I f₂ f₃ hf₂ hg₃
  have h := (I ^ 2).add_mem ((I ^ 2).add_mem ((I ^ 2).add_mem
    ((I ^ 2).add_mem hc₁ hc₂) h₁) h₂) h₃
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [RingHom.comp_apply]
  ring

theorem rectangularCoefficientDerivation_mem_vars (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) {p : MvPolynomial σ A ⧸ rectangularIdeal k}
    (hp : p ∈ (MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))) :
    rectangularCoefficientDerivation σ k D p ∈
      (MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k)) := by
  have he : (MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k)) =
      Ideal.span (Set.range fun i => Ideal.Quotient.mk (rectangularIdeal k)
        (MvPolynomial.X i : MvPolynomial σ A)) := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [he] at hp ⊢
  apply derivation_mem_span_of_vanishes _ _ _ hp
  rintro _ ⟨i, rfl⟩
  exact rectangularCoefficientDerivation_X σ k D i

theorem rectangularTaylorAlong_sub_first_order_mem (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) (hk : 2 ≤ k i)
    (p : MvPolynomial σ A ⧸ rectangularIdeal k) :
    rectangularTaylorAlong σ k D i p -
      (p + Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) *
        rectangularCoefficientDerivation σ k D p) ∈
      ((MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))) ^ 2 := by
  apply truncatedTaylor_sub_first_order_mem _ _ _ _ _ hk
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

theorem rectangularTaylorAlong_sub_self_mem (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) (hk : 2 ≤ k i)
    (p : MvPolynomial σ A ⧸ rectangularIdeal k) :
    rectangularTaylorAlong σ k D i p - p ∈
      (MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k)) := by
  apply truncatedTaylor_sub_self_mem _ _ _ _ _ hk
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

theorem rectangularTaylorAlong_sub_self_mem_sq (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) (hk : 2 ≤ k i)
    {p : MvPolynomial σ A ⧸ rectangularIdeal k}
    (hp : p ∈ (MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))) :
    rectangularTaylorAlong σ k D i p - p ∈
      ((MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))) ^ 2 := by
  apply truncatedTaylor_sub_self_mem_sq _ _ _ _ _ hk _ _ hp
  · exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
  · exact fun _ => rectangularCoefficientDerivation_mem_vars σ k D

theorem rectangularTaylorComp3_sub_first_order_mem (σ : Type*) (k : σ → ℕ)
    (D₁ D₂ D₃ : Derivation ℚ A A) (i₁ i₂ i₃ : σ)
    (hk₁ : 2 ≤ k i₁) (hk₂ : 2 ≤ k i₂) (hk₃ : 2 ≤ k i₃)
    (p : MvPolynomial σ A ⧸ rectangularIdeal k) :
    rectangularTaylorAlong σ k D₁ i₁
      (rectangularTaylorAlong σ k D₂ i₂ (rectangularTaylorAlong σ k D₃ i₃ p)) -
      (p + Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₁) *
        rectangularCoefficientDerivation σ k D₁ p +
        Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₂) *
        rectangularCoefficientDerivation σ k D₂ p +
        Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₃) *
        rectangularCoefficientDerivation σ k D₃ p) ∈
      ((MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))) ^ 2 := by
  apply ringHom_comp3_sub_first_order_mem _
    (rectangularTaylorAlong σ k D₁ i₁).toRingHom
    (rectangularTaylorAlong σ k D₂ i₂).toRingHom
    (rectangularTaylorAlong σ k D₃ i₃).toRingHom
  · exact fun _ => rectangularTaylorAlong_sub_self_mem_sq σ k D₁ i₁ hk₁
  · exact fun _ => rectangularTaylorAlong_sub_self_mem_sq σ k D₂ i₂ hk₂
  · exact rectangularTaylorAlong_sub_self_mem σ k D₂ i₂ hk₂
  · exact rectangularTaylorAlong_sub_self_mem σ k D₃ i₃ hk₃ p
  · exact rectangularTaylorAlong_sub_first_order_mem σ k D₁ i₁ hk₁ p
  · exact rectangularTaylorAlong_sub_first_order_mem σ k D₂ i₂ hk₂ p
  · exact rectangularTaylorAlong_sub_first_order_mem σ k D₃ i₃ hk₃ p

omit [Algebra ℚ A] in

theorem rectangularMap_vars_le {B : Type*} [CommRing B] (σ : Type*) (k : σ → ℕ)
    (f : A →+* B) :
    ((MvPolynomial.idealOfVars σ A).map (Ideal.Quotient.mk (rectangularIdeal k))).map
      (rectangularMap k f) ≤
        (MvPolynomial.idealOfVars σ B).map (Ideal.Quotient.mk (rectangularIdeal k)) := by
  rw [Ideal.map_map, MvPolynomial.idealOfVars, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨p, ⟨i, rfl⟩, rfl⟩
  change rectangularMap k f (Ideal.Quotient.mk _ (MvPolynomial.X i)) ∈ _
  rw [rectangularMap_mk, MvPolynomial.map_X]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

theorem rectangularTaylorThree_sub_first_order_mem {B : Type*} [CommRing B]
    (σ : Type*) (k : σ → ℕ) (D₁ D₂ D₃ : Derivation ℚ A A)
    (i₁ i₂ i₃ : σ) (hk₁ : 2 ≤ k i₁) (hk₂ : 2 ≤ k i₂) (hk₃ : 2 ≤ k i₃)
    (f : A →+* B) (a : A) :
    rectangularTaylorThree σ k D₁ D₂ D₃ i₁ i₂ i₃ f a -
      (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C (f a)) +
        Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₁) *
          Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C (f (D₁ a))) +
        Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₂) *
          Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C (f (D₂ a))) +
        Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i₃) *
          Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C (f (D₃ a)))) ∈
      ((MvPolynomial.idealOfVars σ B).map (Ideal.Quotient.mk (rectangularIdeal k))) ^ 2 := by
  have h := rectangularTaylorComp3_sub_first_order_mem σ k D₁ D₂ D₃ i₁ i₂ i₃
    hk₁ hk₂ hk₃ (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C a))
  have hm := Ideal.mem_map_of_mem (rectangularMap k f) h
  rw [Ideal.map_pow] at hm
  have ht := pow_le_pow_left' (rectangularMap_vars_le σ k f) 2 hm
  simpa only [map_sub, map_add, map_mul, rectangularCoefficientDerivation_mk,
    coefficientDerivation_C, rectangularMap_mk, MvPolynomial.map_C,
    MvPolynomial.map_X, rectangularTaylorThree, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using ht

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {R B σ : Type*} [CommRing R] [Algebra ℚ R] [CommRing B] [Fintype σ]

omit [Fintype σ] in
theorem quotient_X_mul_C (J : Ideal (MvPolynomial σ B)) (i : σ) (a : B) :
    Ideal.Quotient.mk J (MvPolynomial.X i) * Ideal.Quotient.mk J (MvPolynomial.C a) =
      a • Ideal.Quotient.mk J (MvPolynomial.X i) := by
  rw [← map_mul, mul_comm, MvPolynomial.C_mul']
  exact (Ideal.Quotient.mkₐ B J).toLinearMap.map_smul a (MvPolynomial.X i)

omit [Fintype σ] in
theorem rectangular_augmentation_ker_eq (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) :
    (RingHom.ker (rectangularAugmentation (K := B) k hk).toRingHom :
      Ideal (MvPolynomial σ B ⧸ rectangularIdeal k)) =
      (MvPolynomial.idealOfVars σ B).map (Ideal.Quotient.mk (rectangularIdeal k)) := by
  exact ker_quotientAugmentation (rectangularIdeal k) (rectangularIdeal_le_ker_constantCoeff k hk)

theorem rectangularTaylorThree_one_first_order (k : σ → ℕ) (hk : ∀ j, 2 ≤ k j)
    (D : σ → Derivation ℚ R R) (i : σ) (hi : ∀ j, j = i)
    (f : R →+* B) (a : R) (ha : f a = 0) :
    rectangularTaylorThree σ k (D i) 0 0 i i i f a -
      ∑ j, f (D j a) • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X j) ∈
      (RingHom.ker (rectangularAugmentation (K := B) k
        (fun j => by have := hk j; omega)).toRingHom :
          Ideal (MvPolynomial σ B ⧸ rectangularIdeal k)) ^ 2 := by
  classical
  have h := rectangularTaylorThree_sub_first_order_mem σ k (D i) 0 0 i i i
    (hk i) (hk i) (hk i) f a
  have hs : (∑ j, f (D j a) • Ideal.Quotient.mk (rectangularIdeal k)
      (MvPolynomial.X j : MvPolynomial σ B)) =
      f (D i a) • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      exact False.elim (hji (hi j))
    · simp
  rw [hs]
  rw [rectangular_augmentation_ker_eq]
  simpa [ha, quotient_X_mul_C] using h

theorem rectangularTaylorThree_two_first_order (k : σ → ℕ) (hk : ∀ l, 2 ≤ k l)
    (D : σ → Derivation ℚ R R) (i j : σ) (hij : i ≠ j)
    (hijcover : ∀ l, l = i ∨ l = j) (f : R →+* B) (a : R) (ha : f a = 0) :
    rectangularTaylorThree σ k (D i) (D j) 0 i j j f a -
      ∑ l, f (D l a) • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X l) ∈
      (RingHom.ker (rectangularAugmentation (K := B) k
        (fun l => by have := hk l; omega)).toRingHom :
          Ideal (MvPolynomial σ B ⧸ rectangularIdeal k)) ^ 2 := by
  classical
  have h := rectangularTaylorThree_sub_first_order_mem σ k (D i) (D j) 0 i j j
    (hk i) (hk j) (hk j) f a
  have hu : (Finset.univ : Finset σ) = {i, j} := by
    ext l
    simpa using hijcover l
  rw [hu, Finset.sum_pair hij]
  rw [rectangular_augmentation_ker_eq]
  simpa [ha, quotient_X_mul_C] using h

theorem rectangularTaylorThree_three_first_order (k : σ → ℕ) (hk : ∀ l, 2 ≤ k l)
    (D : σ → Derivation ℚ R R) (i j l : σ) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hcover : ∀ u, u = i ∨ u = j ∨ u = l) (f : R →+* B) (a : R) (ha : f a = 0) :
    rectangularTaylorThree σ k (D i) (D j) (D l) i j l f a -
      ∑ u, f (D u a) • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X u) ∈
      (RingHom.ker (rectangularAugmentation (K := B) k
        (fun u => by have := hk u; omega)).toRingHom :
          Ideal (MvPolynomial σ B ⧸ rectangularIdeal k)) ^ 2 := by
  classical
  have h := rectangularTaylorThree_sub_first_order_mem σ k (D i) (D j) (D l) i j l
    (hk i) (hk j) (hk l) f a
  have hu : (Finset.univ : Finset σ) = {i, j, l} := by
    ext u
    simpa using hcover u
  rw [hu]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, hij, hil, hjl,
    or_self, not_false_eq_true, Finset.sum_singleton]
  rw [rectangular_augmentation_ker_eq]
  simpa [ha, quotient_X_mul_C, add_assoc] using h

end WeightedTorusJets.Geometry

end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_IdealPowLayer
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

namespace WeightedTorusJets.Geometry



theorem surjective_of_rectangular_first_order
    {R σ : Type*} [CommRing R] [Algebra ℚ R] [Fintype σ]
    (m : Ideal R) [m.IsMaximal] (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i)
    (D : σ → Derivation ℚ R R)
    (hD : LinearIndependent (R ⧸ m) (fun i => derivationCotangentResidue (D i) m))
    (φ : R →+* (MvPolynomial σ (R ⧸ m) ⧸ rectangularIdeal k))
    (hres : ∀ a, rectangularAugmentation k (fun i => by have := hk i; omega) (φ a) =
      Ideal.Quotient.mk m a)
    (hfirst : ∀ x : m, φ x -
        ∑ i, Ideal.Quotient.mk m (D i x) •
          Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) ∈
      (RingHom.ker (rectangularAugmentation (K := R ⧸ m) k
        (fun i => by have := hk i; omega)).toRingHom) ^ 2) :
    Function.Surjective φ := by
  classical
  let := Ideal.Quotient.field m
  let ε : (MvPolynomial σ (R ⧸ m) ⧸ rectangularIdeal k) →ₐ[R ⧸ m] R ⧸ m :=
    rectangularAugmentation (K := R ⧸ m) k (fun i => by have := hk i; omega)
  let N := RingHom.ker ε.toRingHom
  have hres' (a : R) : ε (φ a) = Ideal.Quotient.mk m a := hres a
  have hφ : Function.Surjective φ := by
    apply surjective_of_nilpotent_ideal_lifts φ N
      (isNilpotent_ker_rectangularAugmentation k (fun i => by have := hk i; omega))
    · intro z
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ε z)
      refine ⟨a, ?_⟩
      change ε (z - φ a) = 0
      rw [map_sub, hres', ha, sub_self]
    · intro z hz
      let zN : N := ⟨z, hz⟩
      let c : σ → R ⧸ m := rectangularAugmentationCotangentEquiv k hk (N.toCotangent zN)
      obtain ⟨x, hx⟩ := exists_ideal_element_with_derivatives m D hD c
      refine ⟨x, ?_, ?_⟩
      · change ε (φ x) = 0
        rw [hres']
        exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property
      · have hlinear := rectangularAugmentation_linear_representative k hk zN
        have hfirstx := hfirst x
        simp_rw [hx] at hfirstx
        change z - ∑ i, c i • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) ∈
          N ^ 2 at hlinear
        change φ x - ∑ i, c i • Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) ∈
          N ^ 2 at hfirstx
        convert (N ^ 2).sub_mem hlinear hfirstx using 1 <;> first | (with_reducible_and_instances rfl) | (abel)
  exact hφ



theorem idealPowLayer_kernel {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) :
    (LinearMap.ker (Submodule.mkQ (I • ⊤ : Submodule A ↥(I ^ n)))).map
      (I ^ n).subtype = I ^ (n + 1) := by
  rw [Submodule.ker_mkQ, Submodule.map_smul'', Submodule.map_subtype_top,
    Ideal.smul_eq_mul, pow_succ']



theorem length_idealPow_step {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) :
    Module.length A ↥(I ^ n) =
      Module.length A ↥(I ^ (n + 1)) + Module.length A (idealPowLayer I n) := by
  let P := (I • ⊤ : Submodule A ↥(I ^ n))
  have hP : P.map (I ^ n).subtype = I ^ (n + 1) := by
    simpa only [Submodule.ker_mkQ] using idealPowLayer_kernel I n
  have hlen : Module.length A P = Module.length A ↥(I ^ (n + 1)) := by
    exact (((I ^ n).equivSubtypeMap P).trans (LinearEquiv.ofEq _ _ hP)).length_eq
  rw [Module.length_eq_add_of_exact P.subtype P.mkQ (Submodule.subtype_injective P)
    (Submodule.mkQ_surjective P) (LinearMap.exact_subtype_mkQ P), hlen]

theorem length_eq_sum_idealPowLayer {A : Type*} [CommRing A]
    (I : Ideal A) (N : ℕ) (hN : I ^ N = ⊥) :
    Module.length A A = ∑ n ∈ Finset.range N, Module.length A (idealPowLayer I n) := by
  have hsum : ∀ j : ℕ, Module.length A A =
      Module.length A ↥(I ^ j) + ∑ n ∈ Finset.range j, Module.length A (idealPowLayer I n) := by
    intro j
    induction j with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        have htop : I ^ 0 = ⊤ := by simp
        exact (Module.length_top (R := A) (M := A)).symm.trans
          (LinearEquiv.ofEq _ _ htop).length_eq.symm
    | succ j ih =>
        rw [Finset.sum_range_succ]
        calc
          Module.length A A = Module.length A ↥(I ^ j) +
            ∑ n ∈ Finset.range j, Module.length A (idealPowLayer I n) := ih
          _ = Module.length A ↥(I ^ (j + 1)) + Module.length A (idealPowLayer I j) +
            ∑ n ∈ Finset.range j, Module.length A (idealPowLayer I n) := by
              rw [length_idealPow_step I j]
          _ = _ := by ac_rfl
  have hzero : Module.length A ↥(I ^ N) = 0 :=
    (LinearEquiv.ofEq _ _ hN).length_eq.trans (Module.length_bot (R := A) (M := A))
  simpa only [hzero, zero_add] using hsum N

theorem length_idealPowLayer_eq_finrank {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [I.IsMaximal] (n : ℕ) :
    Module.length A (idealPowLayer I n) =
      (Module.finrank (A ⧸ I) (idealPowLayer I n) : ℕ∞) := by
  let := Ideal.Quotient.field I
  let : Module.Finite (A ⧸ I) (idealPowLayer I n) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ I) (idealPowLayer I n)
  rw [Module.length_eq_of_surjective (R := A ⧸ I) (S := A)
    (Ideal.Quotient.mk_surjective)]
  exact Module.length_eq_finrank (A ⧸ I) (idealPowLayer I n)

theorem length_eq_sum_finrank_idealPowLayer {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [I.IsMaximal] (N : ℕ) (hN : I ^ N = ⊥) :
    Module.length A A =
      ∑ n ∈ Finset.range N, (Module.finrank (A ⧸ I) (idealPowLayer I n) : ℕ∞) := by
  rw [length_eq_sum_idealPowLayer I N hN]
  apply Finset.sum_congr rfl
  intro n hn
  exact length_idealPowLayer_eq_finrank I n



theorem quotient_length_eq_sum_finrank_idealPowLayer
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J m : Ideal R) [m.IsMaximal] (hJm : J ≤ m)
    (N : ℕ) (hN : (m.map (Ideal.Quotient.mk J)) ^ N = ⊥) :
    Module.length R (R ⧸ J) =
      ∑ n ∈ Finset.range N,
        let := Module.compHom (idealPowLayer (m.map (Ideal.Quotient.mk J)) n)
          (DoubleQuot.quotQuotEquivQuotOfLE hJm).symm.toRingHom
        (Module.finrank (R ⧸ m) (idealPowLayer (m.map (Ideal.Quotient.mk J)) n) : ℕ∞) := by
  let I := m.map (Ideal.Quotient.mk J)
  let : IsNoetherianRing (R ⧸ J) :=
    isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : I.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hJm)
  calc
    Module.length R (R ⧸ J) = Module.length (R ⧸ J) (R ⧸ J) :=
      Module.length_eq_of_surjective (R := R ⧸ J) (M := R ⧸ J) (S := R)
        Ideal.Quotient.mk_surjective
    _ = ∑ n ∈ Finset.range N,
        (Module.finrank ((R ⧸ J) ⧸ I) (idealPowLayer I n) : ℕ∞) :=
      length_eq_sum_finrank_idealPowLayer I N hN
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      let e := DoubleQuot.quotQuotEquivQuotOfLE hJm
      let := Module.compHom (idealPowLayer I n) e.symm.toRingHom
      have hdim : Module.finrank (R ⧸ m) (idealPowLayer I n) =
          Module.finrank ((R ⧸ J) ⧸ I) (idealPowLayer I n) :=
        congrArg Cardinal.toNat (rank_eq_of_equiv_equiv e.symm
          (AddEquiv.refl (idealPowLayer I n)) e.symm.bijective (fun _ _ => rfl))
      exact congrArg (fun z : ℕ => (z : ℕ∞)) hdim.symm




theorem augmentation_length_eq_sum_finrank_idealPowLayer
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (q : A →ₐ[K] K) (N : ℕ) (hN : (RingHom.ker q) ^ N = ⊥) :
    Module.length A A =
      ∑ n ∈ Finset.range N, (Module.finrank K (idealPowLayer (RingHom.ker q) n) : ℕ∞) := by
  have hnil : IsNilpotent (RingHom.ker q) := ⟨N, by simpa only [Ideal.zero_eq_bot] using hN⟩
  let := isLocalRing_of_nilpotent_augmentation q hnil
  rw [length_eq_sum_idealPowLayer (RingHom.ker q) N hN]
  apply Finset.sum_congr rfl
  intro n hn
  exact local_module_length_eq_finrank (residue_surjective_of_nilpotent_augmentation q hnil)



theorem mapIdealPowLayerQuotientAugmentation_surjective {R B : Type*}
    [CommRing R] [CommRing B] (J m : Ideal R) (hJm : J ≤ m) [Algebra (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (mapIdealPowLayerQuotientAugmentation J m hJm f q hcomp n) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hmap : ((m.map (Ideal.Quotient.mk J)) ^ n).map f = (RingHom.ker q) ^ n := by
    rw [Ideal.map_pow, ← quotientAugmentation_comap_ker_eq J m hJm f q hcomp,
      Ideal.map_comap_of_surjective f hf]
  have hy : (y : B) ∈ ((m.map (Ideal.Quotient.mk J)) ^ n).map f := by
    rw [hmap]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hy
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
  rw [mapIdealPowLayerQuotientAugmentation_mk]
  congr 1
  exact Subtype.ext hxy


theorem finite_quotientIdealPowLayer_over_residue
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J m : Ideal R) [m.IsMaximal] (hJm : J ≤ m) (n : ℕ) :
    let := Module.compHom (idealPowLayer (m.map (Ideal.Quotient.mk J)) n)
      (DoubleQuot.quotQuotEquivQuotOfLE hJm).symm.toRingHom
    Module.Finite (R ⧸ m) (idealPowLayer (m.map (Ideal.Quotient.mk J)) n) := by
  let I := m.map (Ideal.Quotient.mk J)
  let : IsNoetherianRing (R ⧸ J) :=
    isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : I.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hJm)
  let := Ideal.Quotient.field m
  let := Ideal.Quotient.field I
  let : Module.Finite ((R ⧸ J) ⧸ I) (idealPowLayer I n) :=
    Module.Finite.of_restrictScalars_finite (R ⧸ J) ((R ⧸ J) ⧸ I) (idealPowLayer I n)
  let e := DoubleQuot.quotQuotEquivQuotOfLE hJm
  let := Module.compHom (idealPowLayer I n) e.symm.toRingHom
  apply Module.rank_lt_aleph0_iff.mp
  rw [rank_eq_of_equiv_equiv e.symm (AddEquiv.refl (idealPowLayer I n))
    e.symm.bijective (fun _ _ => rfl)]
  exact Module.rank_lt_aleph0 _ _

theorem augmentation_length_le_quotient_length
    {R B : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B]
    (J m : Ideal R) [m.IsMaximal] (hJm : J ≤ m)
    [Algebra (R ⧸ m) B] [Module.Finite (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (hf : Function.Surjective f)
    (N : ℕ) (hN : (m.map (Ideal.Quotient.mk J)) ^ N = ⊥) :
    Module.length B B ≤ Module.length R (R ⧸ J) := by
  let := Ideal.Quotient.field m
  have htarget : (RingHom.ker q) ^ N = ⊥ := by
    rw [← Ideal.map_comap_of_surjective f hf (RingHom.ker q),
      quotientAugmentation_comap_ker_eq J m hJm f q hcomp, ← Ideal.map_pow, hN, Ideal.map_bot]
  rw [augmentation_length_eq_sum_finrank_idealPowLayer q N htarget,
    quotient_length_eq_sum_finrank_idealPowLayer J m hJm N hN]
  apply Finset.sum_le_sum
  intro n hn
  let := Module.compHom (idealPowLayer (m.map (Ideal.Quotient.mk J)) n)
    (DoubleQuot.quotQuotEquivQuotOfLE hJm).symm.toRingHom
  let := finite_quotientIdealPowLayer_over_residue J m hJm n
  change (Module.finrank (R ⧸ m) (idealPowLayer (RingHom.ker q) n) : ℕ∞) ≤
    (Module.finrank (R ⧸ m) (idealPowLayer (m.map (Ideal.Quotient.mk J)) n) : ℕ∞)
  exact_mod_cast LinearMap.finrank_le_finrank_of_surjective
    (mapIdealPowLayerQuotientAugmentation_surjective J m hJm f q hcomp hf n)

theorem augmentation_finrank_le_quotient_length
    {R B : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B]
    (J m : Ideal R) [m.IsMaximal] (hJm : J ≤ m)
    [Algebra (R ⧸ m) B] [Module.Finite (R ⧸ m) B]
    (f : (R ⧸ J) →+* B) (q : B →ₐ[R ⧸ m] R ⧸ m)
    (hcomp : (q.toRingHom.comp f).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m)
    (hf : Function.Surjective f)
    (N : ℕ) (hN : (m.map (Ideal.Quotient.mk J)) ^ N = ⊥) :
    (Module.finrank (R ⧸ m) B : ℕ∞) ≤ Module.length R (R ⧸ J) := by
  let := Ideal.Quotient.field m
  have htarget : (RingHom.ker q) ^ N = ⊥ := by
    rw [← Ideal.map_comap_of_surjective f hf (RingHom.ker q),
      quotientAugmentation_comap_ker_eq J m hJm f q hcomp, ← Ideal.map_pow, hN, Ideal.map_bot]
  have hnil : IsNilpotent (RingHom.ker q) := ⟨N, by simpa only [Ideal.zero_eq_bot] using htarget⟩
  rw [← length_eq_finrank_of_nilpotent_augmentation q hnil]
  exact augmentation_length_le_quotient_length J m hJm f q hcomp hf N hN


theorem local_graded_length_lower_of_rectangular_first_order
    {R σ : Type*} [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] [Fintype σ]
    (m J : Ideal R) [m.IsMaximal] (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i)
    (D : σ → Derivation ℚ R R)
    (hD : LinearIndependent (R ⧸ m) (fun i => derivationCotangentResidue (D i) m))
    (φ : R →+* (MvPolynomial σ (R ⧸ m) ⧸ rectangularIdeal k))
    (hJ : J ≤ RingHom.ker φ)
    (hres : ∀ a, rectangularAugmentation k (fun i => by have := hk i; omega) (φ a) =
      Ideal.Quotient.mk m a)
    (hfirst : ∀ x : m, φ x -
        ∑ i, Ideal.Quotient.mk m (D i x) •
          Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i) ∈
      (RingHom.ker (rectangularAugmentation (K := R ⧸ m) k
        (fun i => by have := hk i; omega)).toRingHom) ^ 2)
    (hprimary : J.radical = m) :
    (∏ i, k i : ℕ) ≤ Module.length R (R ⧸ J) := by
  classical
  let := Ideal.Quotient.field m
  let ε : (MvPolynomial σ (R ⧸ m) ⧸ rectangularIdeal k) →ₐ[R ⧸ m] R ⧸ m :=
    rectangularAugmentation (K := R ⧸ m) k (fun i => by have := hk i; omega)
  have hφ := surjective_of_rectangular_first_order m k hk D hD φ hres hfirst
  let ψ := Ideal.Quotient.lift J φ (fun _ hx => hJ hx)
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨a, rfl⟩ := hφ z
    exact ⟨Ideal.Quotient.mk J a, rfl⟩
  have hJm : J ≤ m := J.le_radical.trans_eq hprimary
  have hcomp : (ε.toRingHom.comp ψ).comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk m := by
    ext a
    exact hres a
  obtain ⟨N, hN⟩ := J.exists_radical_pow_le_of_fg (Ideal.fg_of_isNoetherianRing _)
  rw [hprimary] at hN
  have hpow : (m.map (Ideal.Quotient.mk J)) ^ N = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hN
  have h := augmentation_finrank_le_quotient_length J m hJm ψ ε hcomp hψ N hpow
  simpa only [finrank_rectangularQuotient] using h

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]

theorem derivativeStageIdeal_graded_length_lower_one (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (m : Ideal R) [m.IsMaximal] (I : Finset (Fin 3)) (i : I) (hi : ∀ j : I, j = i)
    (t : Fin 3 → ℕ) (ht : ∀ j : I, 2 ≤ t j + 1) (b : ℕ) (F : R)
    (hnext : derivativeStageIdeal D t (b + 1) F ≤ m)
    (hD : LinearIndependent (R ⧸ m) (fun j : I => derivationCotangentResidue (D j) m))
    (hprimary : (derivativeStageIdeal D t b F).radical = m) :
    (∏ j : I, (t j + 1) : ℕ) ≤ Module.length R (R ⧸ derivativeStageIdeal D t b F) := by
  have hvanish := (derivativeStageIdeal_le_ker_iff D t (b + 1) F (Ideal.Quotient.mk m)).mp
    (by simpa only [Ideal.mk_ker] using hnext)
  refine local_graded_length_lower_of_rectangular_first_order m (derivativeStageIdeal D t b F)
    (fun j : I => t j + 1) ht (fun j : I => D j) hD
    (rectangularTaylorThree I (fun j => t j + 1) (D i) 0 0 i i i (Ideal.Quotient.mk m))
    (derivativeStageIdeal_le_ker_taylor_one D h01 h02 h12 I i t b F _ hvanish) ?_ ?_ hprimary
  · intro a
    exact rectangularTaylorThree_augmentation _ _ _ _ _ _ _ _ _ a
  · intro x
    exact rectangularTaylorThree_one_first_order _ ht (fun j : I => D j) i hi
      (Ideal.Quotient.mk m) x (Ideal.Quotient.eq_zero_iff_mem.mpr x.property)

theorem derivativeStageIdeal_graded_length_lower_two (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (m : Ideal R) [m.IsMaximal] (I : Finset (Fin 3)) (i j : I) (hij : i ≠ j)
    (hcover : ∀ l : I, l = i ∨ l = j)
    (t : Fin 3 → ℕ) (ht : ∀ l : I, 2 ≤ t l + 1) (b : ℕ) (F : R)
    (hnext : derivativeStageIdeal D t (b + 1) F ≤ m)
    (hD : LinearIndependent (R ⧸ m) (fun l : I => derivationCotangentResidue (D l) m))
    (hprimary : (derivativeStageIdeal D t b F).radical = m) :
    (∏ l : I, (t l + 1) : ℕ) ≤ Module.length R (R ⧸ derivativeStageIdeal D t b F) := by
  have hvanish := (derivativeStageIdeal_le_ker_iff D t (b + 1) F (Ideal.Quotient.mk m)).mp
    (by simpa only [Ideal.mk_ker] using hnext)
  refine local_graded_length_lower_of_rectangular_first_order m (derivativeStageIdeal D t b F)
    (fun l : I => t l + 1) ht (fun l : I => D l) hD
    (rectangularTaylorThree I (fun l => t l + 1) (D i) (D j) 0 i j j (Ideal.Quotient.mk m))
    (derivativeStageIdeal_le_ker_taylor_two D h01 h02 h12 I i j hij t b F _ hvanish) ?_ ?_ hprimary
  · intro a
    exact rectangularTaylorThree_augmentation _ _ _ _ _ _ _ _ _ a
  · intro x
    exact rectangularTaylorThree_two_first_order _ ht (fun l : I => D l) i j hij hcover
      (Ideal.Quotient.mk m) x (Ideal.Quotient.eq_zero_iff_mem.mpr x.property)

theorem derivativeStageIdeal_graded_length_lower_three (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (m : Ideal R) [m.IsMaximal] (I : Finset (Fin 3)) (i j l : I)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (hcover : ∀ u : I, u = i ∨ u = j ∨ u = l)
    (t : Fin 3 → ℕ) (ht : ∀ u : I, 2 ≤ t u + 1) (b : ℕ) (F : R)
    (hnext : derivativeStageIdeal D t (b + 1) F ≤ m)
    (hD : LinearIndependent (R ⧸ m) (fun u : I => derivationCotangentResidue (D u) m))
    (hprimary : (derivativeStageIdeal D t b F).radical = m) :
    (∏ u : I, (t u + 1) : ℕ) ≤ Module.length R (R ⧸ derivativeStageIdeal D t b F) := by
  have hvanish := (derivativeStageIdeal_le_ker_iff D t (b + 1) F (Ideal.Quotient.mk m)).mp
    (by simpa only [Ideal.mk_ker] using hnext)
  refine local_graded_length_lower_of_rectangular_first_order m (derivativeStageIdeal D t b F)
    (fun u : I => t u + 1) ht (fun u : I => D u) hD
    (rectangularTaylorThree I (fun u => t u + 1) (D i) (D j) (D l) i j l (Ideal.Quotient.mk m))
    (derivativeStageIdeal_le_ker_taylor_three D h01 h02 h12 I i j l hij hil hjl t b F _ hvanish) ?_ ?_ hprimary
  · intro a
    exact rectangularTaylorThree_augmentation _ _ _ _ _ _ _ _ _ a
  · intro x
    exact rectangularTaylorThree_three_first_order _ ht (fun u : I => D u) i j l hij hil hjl hcover
      (Ideal.Quotient.mk m) x (Ideal.Quotient.eq_zero_iff_mem.mpr x.property)

theorem derivativeStageIdeal_graded_length_lower_jb247_oai (D : Fin 3 → Derivation ℚ R R)
    (h01 : Function.Commute (D 0) (D 1))
    (h02 : Function.Commute (D 0) (D 2))
    (h12 : Function.Commute (D 1) (D 2))
    (m : Ideal R) [m.IsMaximal] (I : Finset (Fin 3)) (hI : I.Nonempty)
    (t : Fin 3 → ℕ) (ht : ∀ i : I, 2 ≤ t i + 1) (b : ℕ) (F : R)
    (hnext : derivativeStageIdeal D t (b + 1) F ≤ m)
    (hD : LinearIndependent (R ⧸ m) (fun i : I => derivationCotangentResidue (D i) m))
    (hprimary : (derivativeStageIdeal D t b F).radical = m) :
    (∏ i : I, (t i + 1) : ℕ) ≤ Module.length R (R ⧸ derivativeStageIdeal D t b F) := by
  classical
  have hpos := Finset.card_pos.mpr hI
  have hmax : I.card ≤ 3 := by simpa using Finset.card_le_univ I
  have hcard : I.card = 1 ∨ I.card = 2 ∨ I.card = 3 := by omega
  rcases hcard with hcard | hcard | hcard
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    exact derivativeStageIdeal_graded_length_lower_one D h01 h02 h12 m {i} ⟨i, by simp⟩
      (fun j => Subtype.ext (Finset.mem_singleton.mp j.property)) t ht b F hnext hD hprimary
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
    let ii : ↥({i, j} : Finset (Fin 3)) := ⟨i, by simp⟩
    let jj : ↥({i, j} : Finset (Fin 3)) := ⟨j, by simp⟩
    refine derivativeStageIdeal_graded_length_lower_two D h01 h02 h12 m {i, j} ii jj
      (fun h => hij (congrArg Subtype.val h)) ?_ t ht b F hnext hD hprimary
    intro u
    rcases Finset.mem_insert.mp u.property with hu | hu
    · exact Or.inl (Subtype.ext hu)
    · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp hu))
  · obtain ⟨i, j, l, hij, hil, hjl, rfl⟩ := Finset.card_eq_three.mp hcard
    let ii : ↥({i, j, l} : Finset (Fin 3)) := ⟨i, by simp⟩
    let jj : ↥({i, j, l} : Finset (Fin 3)) := ⟨j, by simp⟩
    let ll : ↥({i, j, l} : Finset (Fin 3)) := ⟨l, by simp⟩
    refine derivativeStageIdeal_graded_length_lower_three D h01 h02 h12 m {i, j, l} ii jj ll
      (fun h => hij (congrArg Subtype.val h))
      (fun h => hil (congrArg Subtype.val h))
      (fun h => hjl (congrArg Subtype.val h)) ?_ t ht b F hnext hD hprimary
    intro u
    have hu : u.val = i ∨ u.val = j ∨ u.val = l := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using u.property
    rcases hu with hu | hu | hu
    · exact Or.inl (Subtype.ext hu)
    · exact Or.inr (Or.inl (Subtype.ext hu))
    · exact Or.inr (Or.inr (Subtype.ext hu))

end WeightedTorusJets.Geometry


end Erdos970

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos970.WeightedTorusJets.Geometry.derivativeStageIdeal_graded_length_lower_jb247_oai.{u_1} := @OAI.Erdos970.WeightedTorusJets.Geometry.derivativeStageIdeal_graded_length_lower_jb247_oai.{u_1}
